---------------------------------------------------------------------------------

## Data generation  
  
  ### Instruction on how to generate the data for sharp bounds of combinatorial objects
>The data generation phase is performed in this order:
>1. the generation of a set of tables associated with each combinatorial object,  
>2. the generation of some metadata for each generated table associated with each combinatorial object,  
>3. the generation of some meta metadata for the metadata of each combinatorial object.  
  
  A detailed instruction is this:
  
### Generating the data, i.e. the tables, for the combinatorial objets graph, partition, partition0, group, cgroup.  
  
>Make sure that, within the directory containing the bound seeker code files, there is a directory called **data**, and make sure that with this **data** directory there are the directories called **graph**, **partition**, **partition0**, **group**, **cgroup**, **tree**, **forest**, and **forest0**.  
  
>For generating the graph data, i.e. the tables of the graph combinatorial object do:  
>1. Check that within the **/data/graph** directory we have the empty directories **data2, data3, ... , data26.**  
>2. Open a bash shell and position yourself in the directory containing the files of the **bound seeker**,  
>3. Run SICStus Prolog and run the goal `[gen_data].` to load the file `gen_data.pl`,  
>4. Type the goal `top(graph, 26, 1).`,  
>5. Type `halt.` to exit SICStus Prolog.  
  
>Proceed in a similar way to generate the tables of the _partition_, _partition0_, _group_, and _cgroup_ combinatorial objects, by respectively replacing `graph` by `partition`, `partition0`, `group`, and `cgroup`, and  
the constant `26` by `30`, `30`,`30` and `30`.  
  
>Note that for the _tree_, _forest_, and _forest0_ combinatorial objects, a python code generates the corresponding tables.  
  
  
  
### Generating the metadata associated with each table of the combinatorial objects graph, partition, partition0, group, cgroup, tree, forest, and forest0.  
  
>For generating the graph metadata do:  
>1. Open a bash shell and position yourself in the directory containing the files of the bound seeker,  
>2. Run SICStus Prolog and run the goal `[gen_metadata].` to load the file `gen_metadata.pl`,  
>3. Type the goal `top(graph, 26).`,  
>4. Type `halt.` to exit SICStus Prolog.  
  
>Proceed in a similar way to generate the metadata of the _partition_, _partition0_, _group_, _cgroup_, _tree_, _forest_, _forest0_ combinatorial objects, by respectively replacing `graph` by `partition`, `partition0`, `group`, `cgroup`, `tree`, `forest`, `forest0` and the constant `26` by `30`, `30`, `30`, `30`, `22`, `22`, and `22`.  
  
  
  
### Generating the meta metadata associated with each combinatorial objets graph, partition, partition0, group, cgroup, tree, forest, and forest0.  
  
>For generating the graph meta metadata do:  
>1. Open a bash shell and position yourself in the directory containing the files of the bound seeker,  
>2. Run SICStus Prolog and run the goal `[gen_meta_metadata].` to load the file `gen_meta_metadata.pl`,  
>3. Type the goal `top(graph, 26).`,  
>4. Type `halt.` to exit SICStus Prolog.  
  
>Proceed in a similar way to generate the metadata of the _partition_, _partition0_, _group_, _cgroup_, _tree_, _forest_, _forest0_ combinatorial objects, by respectively replacing `graph` by `partition`, `partition0`, `group`, `cgroup`, `tree`, `forest`, `forest0` and the constant `26` by `30`, `30`, `30`, `30`, `22`, `22`, and `22`. 

### How the generate the forest, forest0 and tree objects used in the experiment of decomposition method

> The files insides this directory are used to generate three combinatorials objects, namely :

1.  forest with isolated vertices noted _forest_
2.  forest without isolated vertices noted _forest0_
3.  tree noted _tree_

> The goal of thoses scripts is to generate instances (in SICStus prolog format) for three combinatorial objects where one of their characteristics are optimal acccording to their values. As examples of characteristics, we have the greatest depth of a node noted _maxp_, the number of leaves noted _f_ or the number of nodes noted _v_ and etc…

> The main method used to generate those objects is a dedicated algorithm of [Donald E. Knuth](https://www-cs-faculty.stanford.edu/~knuth/taocp.html) stated Algorithm O (_Oriented forest_) of his book titled _Art of Computer Programming, Volume 4, Fascicle 4, Generating All Trees, History of Combinatorial Generation_

### Command lines to generate the objects forest, forest0 and tree objects used in the experiment of decomposition method

#### Dependencies

> The programs [`python3`](https://www.python.org/downloads/) and SICStus Prolog (version 4.6.0 or a more recent version) should be installed.


#### Preparation for running the files to generate the combinatorials objects.

  

> Upload on your computer the directory  __generate_data_forest_ext_CPAIOR__ and its contains avalaible in git repository.

  

### Running the program to generate the combinatorial objects

  >1.  From the terminal  and inside the  directory __generate_data_forest_ext_CPAIOR__   run SICStus Prolog (version 4.6.0 or a more recent version) with the following command to generate appropriate directories for data:  
    `| ?- [gen_data_directory], gen_directory, halt.`
>2. Then to generate the combinatorial object _forest_, _forest0_, or _tree_, you just need  to respectively run in the Terminal from the repository __generate_data_forest_ext_CPAIOR__ the scripts below:
`python3 gen_forest.py maximum_size_of_the_combinatorial_object`
`python3 gen_forest0.py maximum_size_of_the_combinatorial_object`
`python3 gen_tree.py maximum_size_of_the_combinatorial_object`

### Results of running the scripts above

> After running the scripts above, the generated objects which have extremal values of their caracteristics and no more than `maximum_size_of_the_combinatorial_object` vertices are stored in the directory named __data_object__ where **object** is respectively __forest, forest0__, or __tree__.
> Then you copy those directories **forest, forest0, tree** in the **data** directory of the bound seeker.


### Instruction on how to reproduce the experiments executed on the clusters of  Digital Research Alliance of Canada to learn sharp bounds using Model 1 and Model 2



  

To reproduce the test performed on the clusters of  Digital Research Alliance of Canada perform the following steps:

  

#### Running the 1rst version of the acquisition tool **which  use** __Model 1__

  

>1. First upload on the cluster of Digital Research Alliance of Canada the version of Bound Seeker code files **which  use** __Model 1__. The code is at the archive repository.
>2. Upload the files `run_on_cluster.pl, cmds_for_maps.pl`  in the same directory that contains the file `main.pl` of the version of Bound Seeker code files **which  use** __Model 1__ and that you previously uploaded on the cluster of Digital Research Alliance of Canada.
>3. Then open in edit option the code file `main.pl`  of the version of Bound Seeker code files **which  use** __Model 1__. At line number 608, change the name of the directory inside brackets `'data/',KindCombi,/found_conjectures_',FilesOutSuffix,'.pl'` by the name `'data_test_1_poly_cond/', KindCombi,'/found_conjectures_', FilesOutSuffix,'.pl'`. 
>Then record and close the file.
>4. From the terminal of cluster and inside the same directory of the file `main.pl`   run SICStus Prolog (version 4.6.0 or a more recent version)  with the following command to launch the experiments:
`| ?- [run_on_cluster], gen_tache('_test_1_poly_cond'), submit_job('_test_1_poly_cond'), halt.`

  

After launching the command above, **510  jobs** (a job is to find sharp bounds on a group of data bound table of the same characteristic of the same combinatorial object) to find sharp bounds with  __Model 1__ will be launched where the maximum time of running is **4 days**.

  

>5. After the jobs on clusters are finished, from the terminal of cluster and inside the same directory of the file `main.pl`  run SICStus Prolog (version 4.6.0 or a more recent version)  with the following command to get the results of the experiments:
`| ?- [run_on_cluster], get_results('_test_1_poly_cond'), halt.`



  

When the running of the command above terminates, you can access the results which are the conjectures files in the directory:
>**data_test_1_poly_cond/name_of_the_combinatorial_object_v_test_1_poly_cond/conjectures_name_of_the_combinatorial_object**

And you can access the results which are the formulae of the conjectures in the files
 >**data_test_1_poly_cond/name_of_the_combinatorial_object_v_test_1_poly_cond/results_name_of_the_combinatorial_object.tex**

where **name_of_the_combinatorial_object** is one of the following names of objects : **graph , partition, partition0, group, cgroup, tree, forest, forest0.**

  

  

  

  



#### Running the 2nd version of the acquisition tool which use **which  use** __Model 2__

  

>1. First upload on the cluster of Digital Research Alliance of Canada the version of Bound Seeker code files **which  use** __Model 2__. The code is at the archive repository.
>2. Upload the files `run_on_cluster.pl, cmds_for_maps.pl`  in the same directory that contains the file `main.pl` of the version of Bound Seeker code files **which  use** __Model 2__ and that you previously uploaded on the cluster of Digital Research Alliance of Canada.
>3. Then open in edit option the code file `main.pl`  of the version of Bound Seeker code files **which  use** __Model 2__. At line number 608, change the name of the directory inside brackets `'data/',KindCombi,/found_conjectures_',FilesOutSuffix,'.pl'` by the name `'data_test_1_tous/', KindCombi,'/found_conjectures_', FilesOutSuffix,'.pl'`. Then record and close the file.
>4. From the terminal of cluster and inside the same directory of the file `main.pl`   run SICStus Prolog (version 4.6.0 or a more recent version)  with the following command to launch the experiments:
`| ?- [run_on_cluster], gen_tache('_test_1_tous'), submit_job('_test_1_tous'), halt.`

  

After launching the command above, **510  jobs** (a job is to find sharp bounds on a group of data bound table of the same characteristic of the same combinatorial object) to find sharp bounds with  __Model 2__ will be launched where the maximum time of running is **4 days.**

  

>5. After the jobs on clusters are finished, from the terminal of cluster and inside the same directory of the file `main.pl`  run SICStus Prolog (version 4.6.0 or a more recent version)  with the following command to get the results of the experiments:
`| ?- [run_on_cluster], get_results('_test_1_tous'), halt.`

When the running of the command above terminates, you can access the results which are the conjectures files in the directory:
>**data_test_1_tous/name_of_the_combinatorial_object_v_test_1_tous/conjectures_name_of_the_combinatorial_object**

And you can access the results which are the formulae of the conjectures in the files

>**data_test_1_tous/name_of_the_combinatorial_object_v_test_1_tous/results_name_of_the_combinatorial_object.tex**

where **name_of_the_combinatorial_object** is one of the following names of objects : **graph , partition, partition0, group, cgroup, tree, forest, forest0.**



### Instruction on how to reproduce the tables of the evaluation of the contribution of Boolean-arithmetic equations to learn sharp bounds

>To reproduce the test performed in **Section 8.2** perform the following steps :
>1.  First, to avoid an overwriting in the following steps, make sure to duplicate the **/data/** directory which already exists in the archive and contains the data tables for the lower and upper bounds of each combinatorial object of the Bound Seeker.
>2.  After generating the conjectures files (First launch of the Bound Seeker) using the model acquiring only polynomials or conditionals  (i.e. the **Model 1**), change the name of the directory **/data/** by the name **/data_test_1_poly_cond/**.
>3.  Then change the name of the copy of the duplicated **/data/** directory by the original name **/data/** for the second launch of the Bound Seeker.
>4.  In the same way, after generating the conjectures files (Second launch of the Bound Seeker) using the full version of the model which includes all the contributions of **Sections 4, 5, 6**, and **7** (i.e. **Model 2**) , change the name of the directory **/data/** by the name **/data_test_1_tous/**.
>5.  Then make sur that the **/data_test_1_poly_cond/** directory, the **/data_test_1_tous/’** directory and the **/contribution_test_script.pl/** file are in the same directory. Then open a terminal and stay in that same directory.
>6.  Run SICStus Prolog from the terminal (version 4.6.0 or a more recent version) with the following command to print in the console the **Table 10**:
    `| ?− [contribution_test_script], top(bool), halt.`
>7.  Run SICStus Prolog from the terminal (version 4.6.0 or a more recent version) with the following command to print in the console the **Table 11** : 
>`| ?− [ contribution_test_script ], top(cond_ex), halt . ` 
>8. Run SICStus Prolog from the terminal (version 4.6.0 or a more recent version) with the following command to print in the console the **Table 12**:  
`| ?− [contribution_test_script], top(cases), halt.`

### Instruction on how to reproduce the performance test of the acquisition of Boolean-arithmetic equations

To reproduce the test performed in Section 8.3 perform the following steps:

1. Put the conjecture files in the `existing_maps' directory. Ensure that the conjecture files have the appropriate names.
    Note that the `existing_maps' directory already exists in the archive and contains the lower and upper bounds of the corresponding bounds generated by the Bound Seeker for each combinatorial object.

2. Run SICStus Prolog from a terminal (version 4.6.0 or a more recent version) with the following command to generate examples used in the comparison:
    `| ?- [performance_test_script], create_examples, halt.`

    Afterwards, copy and paste the printed list of tables from the console into the file `tables_list.pl', if necessary, replacing the previous examples.

3. Run SICStus Prolog with the following command:
   ` | ?- [main_test_1_full_model], top(0), halt.`

4. Run SICStus Prolog with the following command:
   ` | ?- [main_test_1_enhanced_model], top(0), halt.`

5. Run SICStus Prolog with the following command:
    `| ?- [main_test_1_core_model], top(0), halt.`

6. Run SICStus Prolog with the following command to print in the console all performance test results of Tables 13 and 14:
    `| ?- [performance_test_script], create_stats, halt.`
