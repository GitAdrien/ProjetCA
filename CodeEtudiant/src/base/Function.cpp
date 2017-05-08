#include <Function.h>

Function::Function(){
  _head = NULL;
  _end = NULL;
  BB_computed = false;
  BB_pred_succ = false;
  dom_computed = false;
}

Function::~Function(){}

void Function::set_head(Line *head){
  _head = head;
}

void Function::set_end(Line *end){
  _end = end;
}

Line* Function::get_head(){
  return _head;
}

Basic_block* Function::get_firstBB(){
   return _myBB.front();
}

Line* Function::get_end(){
  return _end;
}
void Function::display(){
  cout<<"Begin Function"<<endl;
  Line* element = _head;

  if(element == _end)
    cout << _head->get_content() <<endl;

  while(element != _end){
    cout << element->get_content() <<endl;

    if(element->get_next()==_end){
      cout << element->get_next()->get_content() <<endl;
      break;
    }
    else element = element->get_next();

    }
  cout<<"End Function\n\n"<<endl;

}

int Function::size(){
  Line* element = _head;
  int lenght=0;
  while(element != _end)
    {
      lenght++;
      if (element->get_next()==_end)
	break;
      else
	element = element->get_next();
    }
  return lenght;
}


void Function::restitution(string const filename){

  Line* element = _head;
  ofstream monflux(filename.c_str(), ios::app);

  if(monflux){
    monflux<<"Begin"<<endl;
    if(element == _end)
      monflux << _head->get_content() <<endl;
    while(element != _end)
      {
	if(element->isInst() ||
	   element->isDirective())
	  monflux<<"\t";

	monflux << element->get_content() ;

	if(element->get_content().compare("nop"))
	  monflux<<endl;

	if(element->get_next()==_end){
	  if(element->get_next()->isInst() ||
	     element->get_next()->isDirective())
	    monflux<<"\t";
	  monflux << element->get_next()->get_content()<<endl;
	  break;
	}
	else element = element->get_next();

      }
    monflux<<"End\n\n"<<endl;

  }

  else {
    cout<<"Error cannot open the file"<<endl;
  }

  monflux.close();
}

void Function::comput_label(){
  Line* element = _head;

  if(element == _end && element->isLabel())
    _list_lab.push_back(getLabel(element));
  while(element != _end)
    {

      if(element->isLabel())
	_list_lab.push_back(getLabel(element));

      if(element->get_next()==_end){
	if(element->isLabel())
	  _list_lab.push_back(getLabel(element));
	break;
      }
      else element = element->get_next();

    }

}

int Function::nbr_label(){
  return _list_lab.size();

}

Label* Function::get_label(int index){

  list<Label*>::iterator it;
  it=_list_lab.begin();

  int size=(int) _list_lab.size();
  if(index< size){
    for (int i=0; i<index;i++ ) it++;
    return *it;
  }
  else cout<<"Error get_label : index is bigger than the size of the list"<<endl;

  return _list_lab.back();
}

Basic_block *Function::find_label_BB(OPLabel* label){
  //Basic_block *BB = new Basic_block();
   int size=(int)_myBB.size();
   string str;
   for(int i=0; i<size; i++){
      if(get_BB(i)->is_labeled()){

	 str=get_BB(i)->get_head()->get_content();
	 if(!str.compare(0, (str.size()-1),label->get_op())){
	    return get_BB(i);
	 }
      }
  }
  return NULL;
}


/* ajoute nouveau BB � la liste de BB de la fonction en le creant */

void Function::add_BB(Line *debut, Line* fin, Line *br, int index){
   Basic_block *b=new Basic_block();
   b->set_head(debut);
   b->set_end(fin);
   b->set_index(index);
   b->set_branch(br);
   _myBB.push_back(b);
}


//Calcule la liste des blocs de base : il faut d�limiter les BB, en parcourant la liste des lignes/instructions � partir de la premiere, il faut s'arreter � chaque branchement (et prendre en compte le delayed slot qui appartient au meme BB, c'est l'instruction qui suit tout branchement) ou � chaque label (on estime que tout label est utilis� par un saut et donc correspond bien � une entete de BB).

void Function::comput_basic_block(){
    Line *debut, *current, *prev;
    bool verbose = true;
    current=_head;
    debut=_head;
    prev = NULL;
    int ind=0;
    Line *l=NULL;
    Instruction *i=NULL;
    Line * b;
    cout<< "comput BB" <<endl;

   if (verbose){
       cout<<"head :"<<_head->get_content()<<endl;
       cout<<"tail :"<<_end->get_content()<<endl;
   }

   if (BB_computed) return; // NE PAS TOUCHER

    Line* lastlabel = NULL;

    bool hasInst = false;
    bool hasLabel = false;
    while(current != _end->get_next()){ //traiter la derniere ligne donc s'arr�ter � la suivante!
    	cout << "current line : " << current->to_string()<< endl;
        if (!current->isInst()) {
            if (current->isLabel()) {
                if (!hasLabel || !hasInst) { // Premier label rencontré ou aucune inst depsuis le dernier label.
                    cout <<"cas 1"<<endl;
                    debut = current;
                    current = current->get_next();
                    hasLabel = true;
                } else { // Il y avait deja un label.
                	cout <<"cas 2"<<endl;
                    add_BB(debut, current, b, ind);
                    ind++;

                    debut = current;
                    current = current->get_next();
                    lastlabel = false;
                    hasInst = false;
                }
            } else { // est une directive donc skip.
            	cout <<"cas 6"<<endl;
                current = current->get_next();
            }
        } else { // est une instruction.
            hasInst = true;
            i = getInst(current);
            if (i->is_branch()) {
            	cout <<"cas 3"<<endl;
                add_BB(debut, current->get_next(), current, ind);
                current = current->get_next();
                current = current->get_next();
                b = NULL;
                ind++;
                lastlabel = false;
                hasInst = false;
                debut = current;
            } else { // n'est pas un jump.
                if (!hasLabel) {
                	cout <<"cas 4"<<endl;
                    debut = current;
                    hasLabel = true;
                }
                current = current->get_next();
                cout <<"cas 4 bis"<<endl;
            }

            if ((current->get_next() == _end->get_next()) && hasInst) {
            	cout <<"cas 5"<<endl;
                add_BB(debut, current, b, ind);
            }
        }
    }



   if (verbose)
     cout<<"end comput Basic Block"<<endl;

   BB_computed = true;
   return;
}

int Function::nbr_BB(){
   return _myBB.size();
}

Basic_block *Function::get_BB(int index){

  list<Basic_block*>::iterator it;
  it=_myBB.begin();
  int size=(int)_myBB.size();

  if(index< size){
    for (int i=0; i<index;i++ ) it++;
    return *it;
  }
  else
    return NULL;
}

list<Basic_block*>::iterator Function::bb_list_begin(){
   return _myBB.begin();
}

list<Basic_block*>::iterator Function::bb_list_end(){
   return _myBB.end();
}

/* comput_pred_succ calcule les successeurs et pr�d�cesseur des BB, pour cela il faut commencer par les successeurs */
/* et it�rer sur tous les BB d'une fonction */
/* il faut determiner si un BB a un ou deux successeurs : d�pend de la pr�sence d'un saut pr�sent ou non � la fin */
/* pas de saut ou saut incontionnel ou appel de fonction : 1 successeur (lequel ?)*/
/* branchement conditionnel : 2 successeurs */
/* le dernier bloc n'a pas de successeurs - celui qui se termine par jr R31 */
/* les sauts indirects n'ont pas de successeur */

void Function::comput_succ_pred_BB(){
   list<Basic_block*>::iterator it, it2;
   Basic_block *current;
   Instruction *instr;
   Basic_block *succ=NULL, *next;
   int size = _myBB.size();
   if (BB_pred_succ) return;


   OPLabel *nextLabel;
   Label *label;
   Instruction *nextInstr;
   it=_myBB.begin();
   Instruction *branch;
   for(int i=0;i<size;i++) {
       current = get_BB(i);
       current->display();
       branch = (Instruction*)current->get_branch();
       //Successeur direct
       if (i+1<size) {
           next = get_BB(i+1);
           if (branch==NULL||branch->is_cond_branch()||branch->is_call()) {
           		current->set_link_succ_pred(next);
           }
       }
       
       //Successeur indirect
      if (branch != NULL) {
          nextLabel = branch->get_op_label();
          if (nextLabel == NULL) {
          	branch = NULL;
          	continue;
          }

          next = find_label_BB(nextLabel);
          if (next != NULL)
            current->set_link_succ_pred(next);
      }
      branch = NULL;
   }

   // ne pas toucher ci-dessous
   BB_pred_succ = true;
   return;
}
void Function::compute_dom(){
 list<Basic_block*>::iterator it, it2;
  list<Basic_block*> workinglist;
  Basic_block *current, *bb, *pred;
  vector<bool> currDomin;
  bool change = true;
  int size = _myBB.size();
  if (dom_computed) return;
  comput_succ_pred_BB();

  for(it = Function::bb_list_begin(), it2 = Function::bb_list_end(); it!=it2; it++){
  	current = *it;
  	if(current->get_nb_pred()==0){
  		workinglist.push_back(current);
  	}
  }
  while(!workinglist.empty()){
  	change = false;
  	current = workinglist.front();
  	currDomin = current->Domin;
  	workinglist.pop_front();
  	for(int i = 0; i < current->get_nb_pred(); i++){
  		currDomin[current->get_predecessor(i)->get_index()] = true;
  	}
  	currDomin[current->get_index()] = true;
  	for(int i = 0; i < currDomin.size(); i++){
		if(currDomin[i] != current->Domin[i]){
			change = true;
			current->Domin[i]= currDomin[i];	
		}
  	}
  	if(change){
  		for(int i = 0; i<current->get_nb_succ();i++){
  			if(i==0)
  				workinglist.push_back(current->get_successor1());
  			else
  				workinglist.push_back(current->get_successor2());
  		}
  	}
	
  }
	
  /* A REMPLIR */


  // affichage du resultat
  it=_myBB.begin();

  for (int j=0; j< size; j++){
    current = *it;
    cout << "Dominants pour BB" << current -> get_index() << " : ";
    for (int i = 0; i< nbr_BB(); i++){
      if (current->Domin[i]) cout << " BB" << i  ;
    }
    cout << endl;
    it++;
  }
  dom_computed = true;
  return;
}

void Function::compute_live_var(){
  list<Basic_block*>::iterator it, it2;
  list<Basic_block*> workinglist;
  Basic_block *current, *bb, *pred;
  bool change = true;
  int size= (int) _myBB.size();
  int nb_pred;
  it=_myBB.begin();
  for(it = Function::bb_list_end(), it2 = Function::bb_list_begin(); it!=it2; it--){ //du dernier au premier
  	current = *it;
  	if(current->get_nb_succ()==0){//Sans successeur
  		workinglist.push_back(current);
  	}
  }
  while(!workinglist.empty()){
    current = workinglist.front();
    nb_pred = current->get_nb_pred();
    workinglist.pop_front();
    for(int i = 0; i < current->LiveIn.size(); i++){
          if(current->get_successor1()!=NULL&&current->get_successor1()->LiveIn[i]){
            current->LiveOut[i] = true;
          }
           if(current->get_successor2()!=NULL&&current->get_successor2()->LiveIn[i]){
            current->LiveOut[i] = true;
          }

          if((current->LiveOut[i]&&!current->Def[i]) || current->Use[i]){
            current->LiveIn[i] = true;
          }
    }
    if(current->get_branch()!=NULL){
        current->LiveOut[2] = true;
        current->LiveOut[29] = true;  
    }
    for(int j = 0; j < nb_pred; j){
      workinglist.push_back(current->get_predecessor(j));
    }

  }


  /* A REMPLIR avec algo vu en cours et en TD*/
 /* algorithme it�ratif qui part des blocs sans successeur, ne pas oublier que lorsque l'on sort d'une fonction le registre $2 contient le r�sultat (il est donc vivant), le registre pointeur de pile ($29) est aussi vivant ! */


  // Affichage du resultat
  it2=_myBB.begin();
  for (int j=0; j<size; j++){
    bb = *it2;
    cout << "********* bb " << bb->get_index() << "***********" << endl;
    cout << "LIVE_OUT : " ;
    for(int i=0; i<NB_REG; i++){
      if (bb->LiveOut[i]){
	cout << "$"<< i << " ";
      }
    }
    cout << endl;
    cout << "LIVE_IN :  " ;
    for(int i=0; i<NB_REG; i++){
      if (bb->LiveIn[i]){
	cout << "$"<< i << " ";
      }}
    cout << endl;
    it2++;
  }
  return;
}




/* en implementant la fonction test de la classe BB, permet de tester des choses sur tous les blocs de base d'une fonction par exemple l'affichage de tous les BB d'une fonction ou l'affichage des succ/pred des BBs comme c'est le cas -- voir la classe Basic_block et la m�thode test */

void Function::test(){
  int size=(int)_myBB.size();
   for(int i=0;i<size; i++){
    get_BB(i)->test();
  }
   return;
}
