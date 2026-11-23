import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.MultiPhi
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.MultiPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDualEx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sum_ofFn_prod {A ι : Type} [Semiring A] [Fintype ι] (q : ℕ) (T : Fin q → ι → A) :
    ∑ i : Fin q → ι, (List.ofFn fun j => T j (i j)).prod = (List.ofFn fun j => ∑ k, T j k).prod := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.ofFn_succ, List.prod_cons, ← ih (fun j => T j.succ), Finset.sum_mul_sum,
      ← Fintype.sum_prod_type']
    refine (Fintype.sum_equiv (Fin.consEquiv fun _ => ι) _ _ ?_).symm
    intro p
    simp [List.ofFn_succ, Fin.consEquiv]

section

variable {O R V : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup V] [Module R V] {q n : ℕ}
  {Nq : Fin q → ℕ} {act : PU R q n →ₐ[R] Module.End R V} {e : Fin q → Module.End R V} {W : Fin q → Submodule R V}

private theorem emb_C (j : Fin q) (r : O) :
    emb O R j (MvPolynomial.C r : MvPolynomial (Fin n) O) = algebraMap R (PU R q n) (algebraMap O R r) := by
  simp [emb]

private theorem emb_X (j : Fin q) (i : Fin n) :
    emb O R j (MvPolynomial.X i : MvPolynomial (Fin n) O) = (MvPolynomial.X (j, i) : PU R q n) := by
  simp [emb]

private theorem comm_emb (H : HkHyp O Nq act e W) {j j' : Fin q} (h : j ≠ j') (x : MvPolynomial (Fin n) O) :
    Commute (e j) (act (emb O R j' x)) := by
  induction x using MvPolynomial.induction_on with
  | C r => rw [emb_C, AlgHom.commutes]; exact (Algebra.commutes _ _).symm
  | add p p' hp hp' => rw [map_add, map_add]; exact hp.add_right hp'
  | mul_X p i hp => rw [map_mul, map_mul, emb_X]; exact hp.mul_right (H.eX j j' i h)

private theorem mem_emb (H : HkHyp O Nq act e W) {j j' : Fin q} (h : j ≠ j') (x : MvPolynomial (Fin n) O) :
    ∀ v ∈ W j, act (emb O R j' x) v ∈ W j := by
  induction x using MvPolynomial.induction_on with
  | C r => intro v hv; rw [emb_C, AlgHom.commutes]; exact (W j).smul_mem _ hv
  | add p p' hp hp' => intro v hv; rw [map_add, map_add]; exact (W j).add_mem (hp v hv) (hp' v hv)
  | mul_X p i hp => intro v hv; rw [map_mul, map_mul, emb_X]; exact hp _ (H.WX j j' i h v hv)

private theorem comm_list (H : HkHyp O Nq act e W) {j : Fin q} {l : List (Fin q)} (h : j ∉ l)
    (x : MvPolynomial (Fin n) O) : Commute (act (emb O R j x)) (l.map e).prod := by
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
  have haj : a ≠ j := by
    rintro rfl
    exact h ha
  exact (comm_emb H haj x).symm

private theorem comm_list' (H : HkHyp O Nq act e W) {j : Fin q} {l : List (Fin q)} (h : j ∉ l)
    (x : Fin q → MvPolynomial (Fin n) O) : Commute (e j) (act (l.map fun j => emb O R j (x j)).prod) := by
  rw [map_list_prod]
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hz
  have hja : j ≠ a := by
    rintro rfl
    exact h ha
  exact comm_emb H hja (x a)

private theorem mem_list (H : HkHyp O Nq act e W) {j : Fin q} {l : List (Fin q)} (h : j ∉ l)
    (x : Fin q → MvPolynomial (Fin n) O) {v : V} (hv : v ∈ W j) :
    act (l.map fun j => emb O R j (x j)).prod v ∈ W j := by
  induction l with
  | nil => simpa using hv
  | cons j' l ih =>
    rw [List.map_cons, List.prod_cons, map_mul]
    exact mem_emb H (List.ne_of_not_mem_cons h) _ _ (ih fun h' => h (List.mem_cons_of_mem _ h'))

private theorem tr_list (H : HkHyp O Nq act e W) {l : List (Fin q)} (h : l.Nodup)
    (x : Fin q → MvPolynomial (Fin n) O) {v : V} (hv : ∀ j, v ∈ W j) :
    (l.map e).prod (act (l.map fun j => emb O R j (x j)).prod v) =
      act (l.map fun j => emb O R j (Hk.dd (Hk.NN n (Nq j : O) * x j))).prod v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply]
    have hc := (comm_list H h.1 (x a)).eq
    have hw := congrArg (fun f : Module.End R V => f ((act (l.map fun j => emb O R j (x j)).prod) v)) hc
    simp only [Module.End.mul_apply] at hw
    rw [← hw, ih h.2]
    exact H.tr a (x a) _ (mem_list H h.1 _ (hv a))

private theorem sum_list (H : HkHyp O Nq act e W) {l : List (Fin q)} (h : l.Nodup)
    (x y : Fin q → MvPolynomial (Fin n) O) :
    act (l.map fun j => emb O R j (x j)).prod * (l.map e).prod * act (l.map fun j => emb O R j (y j)).prod =
      (l.map fun j => act (emb O R j (x j)) * e j * act (emb O R j (y j))).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.prod_cons, map_mul]
    rw [← ih h.2]
    have h1 : Commute (act (l.map fun j => emb O R j (x j)).prod) (e a) := (comm_list' H h.1 x).symm
    have h2 : Commute (act (emb O R a (y a))) (l.map e).prod := comm_list H h.1 (y a)
    have h3 : Commute (act (emb O R a (y a))) (act (l.map fun j => emb O R j (x j)).prod) :=
      (Commute.all _ _).map act
    set A := act (emb O R a (x a))
    set PA := act (l.map fun j => emb O R j (x j)).prod
    set Pe := (l.map e).prod
    set C := act (emb O R a (y a))
    set PC := act (l.map fun j => emb O R j (y j)).prod
    calc A * PA * (e a * Pe) * (C * PC) = A * (PA * e a) * (Pe * C) * PC := by simp only [mul_assoc]
      _ = A * (e a * PA) * (C * Pe) * PC := by rw [h1.eq, h2.eq]
      _ = A * e a * (PA * C) * Pe * PC := by simp only [mul_assoc]
      _ = A * e a * (C * PA) * Pe * PC := by rw [h3.eq]
      _ = A * e a * C * (PA * Pe * PC) := by simp only [mul_assoc]

private theorem prod_list {A : Type} [CommMonoid A] (f : Fin q → A) : ∏ j, f j = ((List.finRange q).map f).prod := by
  rw [← List.ofFn_eq_map, List.prod_ofFn]

private theorem sum_all (H : HkHyp O Nq act e W) {ι : Type} [Fintype ι] {a c : ι → MvPolynomial (Fin n) O}
    (hd : Hk.IsDual a c) :
    ∑ i : Fin q → ι, act (∏ j, emb O R j (a (i j))) * (List.ofFn e).prod * act (∏ j, emb O R j (c (i j))) =
      act (∏ j, emb O R j (Hk.NN n (Nq j : O))) := by
  have hl := List.nodup_finRange q
  have key : ∀ i : Fin q → ι, act (∏ j, emb O R j (a (i j))) * (List.ofFn e).prod * act (∏ j, emb O R j (c (i j)))
      = (List.ofFn fun j => act (emb O R j (a (i j))) * e j * act (emb O R j (c (i j)))).prod := by
    intro i
    rw [prod_list, prod_list, List.ofFn_eq_map, List.ofFn_eq_map]
    exact sum_list H hl (fun j => a (i j)) (fun j => c (i j))
  simp only [key]
  rw [sum_ofFn_prod q (fun j k => act (emb O R j (a k)) * e j * act (emb O R j (c k)))]
  have hs : ∀ j, ∑ k, act (emb O R j (a k)) * e j * act (emb O R j (c k)) = act (emb O R j (Hk.NN n (Nq j : O))) :=
    fun j => H.sum j ι a c hd
  simp only [hs]
  rw [prod_list, map_list_prod, List.ofFn_eq_map, List.map_map]
  rfl

private theorem comm_sym (H : HkHyp O Nq act e W) (j : Fin q) (z : MvPolynomial (Fin n) O) (hz : z.IsSymmetric) :
    Commute (act (emb O R j z)) (List.ofFn e).prod := by
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨j', rfl⟩ := (List.mem_ofFn' _ _).1 hy
  by_cases h : j' = j
  · subst h; exact (H.esym _ z hz).symm
  · exact (comm_emb H h z).symm

end

private theorem esymm_root {O R B : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing B] {q n : ℕ} (β : R →+* B)
    (P : Fin q → Polynomial B) (j : Fin q) (k : ℕ) (hk : k ≤ n) :
    Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β (emb O R j (MvPolynomial.esymm (Fin n) O k)))
      = algebraMap B (MSplitAlg P n) ((-1) ^ k * (P j).coeff (n - k)) := by
  classical
  have hE : ∀ p : MvPolynomial (Fin n) O, MvPolynomial.map β (emb O R j p) =
      MvPolynomial.rename (fun i => (j, i)) (MvPolynomial.map (β.comp (algebraMap O R)) p) := by
    intro p
    simp [emb, MvPolynomial.map_rename, MvPolynomial.map_map]
  rw [hE, MvPolynomial.map_esymm, MvPolynomial.esymm, map_sum, map_sum]
  simp only [map_prod, MvPolynomial.rename_X]
  have hroot := MSplitAlg.prod_root P n j
  have hc' : ((Finset.univ.val.map (MSplitAlg.root P n j)).map fun t => Polynomial.X - Polynomial.C t).prod.coeff (n - k)
      = algebraMap B (MSplitAlg P n) ((P j).coeff (n - k)) := by
    rw [Multiset.map_map, ← Polynomial.coeff_map, ← hroot]
    rfl
  rw [Multiset.prod_X_sub_C_coeff _ (by simp)] at hc'
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, Nat.sub_sub_self hk,
    Finset.esymm_map_val] at hc'
  rw [map_mul, ← hc', map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  rfl

theorem UpperTheory.V.Pa.Lev.multiTwo :
    ∀ (O R B M V : Type) [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (Nq : Fin q → ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (e : Fin q → Module.End R V) (W : Fin q → Submodule R V) (inc : M →+ V) (tr : V →+ M), HkHyp O Nq act e W → (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) → Function.Injective inc → (∀ (t : R) m, inc (β t • m) = t • inc m) → (∀ v, inc (tr v) = (List.ofFn e).prod v) → (∀ j m, inc m ∈ W j) → (∀ j k, k ≤ n → ∀ m, act (emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ k)) (inc m) = inc (((-1) ^ k * (P j).coeff (n - k)) • m)) → TwoMaps (M := M) β P act (∏ j, emb O R j (Hk.NN n (Nq j : O))) := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n Nq β P act e W inc tr H hmon hdeg hinj hβ htr hW hsym
  classical
  set mkq := Ideal.Quotient.mk (mSplitIdeal P n)
  set f : PU R q n := ∏ j, emb O R j (Hk.NN n (Nq j : O))
  obtain ⟨φ, hφ1, hφ2⟩ := multiPhi R B M V q n β P act inc hmon hdeg hβ hsym
  obtain ⟨ι, hι, a, c, hd⟩ := hkDualEx O n
  have hembZ : ∀ (j : Fin q) (k : ℕ), emb O R j (MvPolynomial.esymm (Fin n) O k) = emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ k) := by
    intro j k
    simp only [emb, RingHom.comp_apply, MvPolynomial.map_esymm]
  have htrS : ∀ (t : R) (v : V), tr (t • v) = β t • tr v := by
    intro t v
    apply hinj
    rw [hβ, htr, htr, map_smul]
  have htrE : ∀ (j : Fin q), ∀ k ≤ n, ∀ v : V,
      tr (act (emb O R j (MvPolynomial.esymm (Fin n) O k)) v) = ((-1) ^ k * (P j).coeff (n - k)) • tr v := by
    intro j k hk v
    apply hinj
    have hc := (comm_sym H j _ (MvPolynomial.esymm_isSymmetric (Fin n) O k)).eq
    have := congrArg (fun g : Module.End R V => g v) hc
    simp only [Module.End.mul_apply] at this
    rw [htr, ← this, ← htr, hembZ, hsym j k hk]
  let ψ : V →+ MSplitAlg P n ⊗[B] M := AddMonoidHom.mk' (fun v => ∑ i : Fin q → ι,
      mkq (MvPolynomial.map β (∏ j, emb O R j (a (i j)))) ⊗ₜ[B] tr (act (∏ j, emb O R j (c (i j))) v))
    (by intro v w; simp [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib])
  have hψv : ∀ v, ψ v = ∑ i : Fin q → ι,
      mkq (MvPolynomial.map β (∏ j, emb O R j (a (i j)))) ⊗ₜ[B] tr (act (∏ j, emb O R j (c (i j))) v) := fun v => rfl
  have hψ := multiPsi O R B M V q n β P act tr ι a c hd hmon hdeg htrS htrE ψ hψv
  have e1 : ∀ (s : MSplitAlg P n) (x : M), s ⊗ₜ[B] x = s • ((1 : MSplitAlg P n) ⊗ₜ[B] x) := by
    intro s x
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hφψ : ∀ v, φ (ψ v) = act f v := by
    intro v
    rw [hψv, map_sum]
    have hterm : ∀ i : Fin q → ι, φ (mkq (MvPolynomial.map β (∏ j, emb O R j (a (i j)))) ⊗ₜ[B]
        tr (act (∏ j, emb O R j (c (i j))) v)) =
        (act (∏ j, emb O R j (a (i j))) * (List.ofFn e).prod * act (∏ j, emb O R j (c (i j)))) v := by
      intro i
      rw [e1, hφ2, hφ1, htr]
      rfl
    simp only [hterm]
    rw [← LinearMap.sum_apply, sum_all H hd]
  let T : PU R q n → Prop := fun x => ∃ b : B, algebraMap B (MSplitAlg P n) b = mkq (MvPolynomial.map β x) ∧
    ∀ m, act x (inc m) = inc (b • m)
  have hT1 : T 1 := ⟨1, by simp, by simp⟩
  have hTmul : ∀ x y, T x → T y → T (x * y) := by
    rintro x y ⟨b1, h1, k1⟩ ⟨b2, h2, k2⟩
    refine ⟨b1 * b2, by rw [map_mul, map_mul, map_mul, h1, h2], fun m => ?_⟩
    rw [map_mul, Module.End.mul_apply, k2, k1, mul_smul]
  have hTadd : ∀ x y, T x → T y → T (x + y) := by
    rintro x y ⟨b1, h1, k1⟩ ⟨b2, h2, k2⟩
    refine ⟨b1 + b2, by rw [map_add, map_add, map_add, h1, h2], fun m => ?_⟩
    rw [map_add, LinearMap.add_apply, k2, k1, ← map_add, add_smul]
  have hTC : ∀ (j : Fin q) (r : O), T (emb O R j (MvPolynomial.C r)) := by
    intro j r
    refine ⟨β (algebraMap O R r), ?_, fun m => ?_⟩
    · rw [emb_C, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
      rfl
    · rw [emb_C, AlgHom.commutes, Module.algebraMap_end_apply, hβ]
  have hTes : ∀ (j : Fin q), ∀ k ≤ n, T (emb O R j (MvPolynomial.esymm (Fin n) O k)) := by
    intro j k hk
    refine ⟨(-1) ^ k * (P j).coeff (n - k), (esymm_root β P j k hk).symm, fun m => ?_⟩
    rw [hembZ, hsym j k hk]
  have hTQ : ∀ (j : Fin q) (Q : MvPolynomial (Fin n) O),
      T (emb O R j ((MvPolynomial.esymmAlgHom (Fin n) O n Q : MvPolynomial (Fin n) O))) := by
    intro j Q
    induction Q using MvPolynomial.induction_on with
    | C r =>
      have : ((MvPolynomial.esymmAlgHom (Fin n) O n (MvPolynomial.C r) : MvPolynomial (Fin n) O)) = MvPolynomial.C r := by
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
        rfl
      rw [this]
      exact hTC j r
    | add p p' hp hp' =>
      rw [map_add, Subalgebra.coe_add, map_add]
      exact hTadd _ _ hp hp'
    | mul_X p i hp =>
      rw [map_mul, Subalgebra.coe_mul, map_mul]
      refine hTmul _ _ hp ?_
      have : ((MvPolynomial.esymmAlgHom (Fin n) O n (MvPolynomial.X i) : MvPolynomial (Fin n) O)) =
          MvPolynomial.esymm (Fin n) O (i + 1) := by
        simp [MvPolynomial.esymmAlgHom]
      rw [this]
      exact hTes j _ i.2
  have hTsym : ∀ (j : Fin q) (z : MvPolynomial (Fin n) O), z.IsSymmetric → T (emb O R j z) := by
    intro j z hz
    obtain ⟨Q, hQ⟩ := MvPolynomial.esymmAlgHom_surjective O (σ := Fin n) (n := n) (by simp) ⟨z, hz⟩
    have : z = (MvPolynomial.esymmAlgHom (Fin n) O n Q : MvPolynomial (Fin n) O) := by rw [hQ]
    rw [this]
    exact hTQ j Q
  have hTprod : ∀ z : Fin q → MvPolynomial (Fin n) O, (∀ j, (z j).IsSymmetric) → T (∏ j, emb O R j (z j)) :=
    fun z hz => Finset.prod_induction _ T hTmul hT1 (fun j _ => hTsym j (z j) (hz j))
  have hpoly : ∑ i : Fin q → ι, (∏ j, emb O R j (Hk.dd (Hk.NN n (Nq j : O) * c (i j)))) * (∏ j, emb O R j (a (i j))) = f := by
    simp only [← Finset.prod_mul_distrib, ← map_mul]
    have hpu := Finset.prod_univ_sum (fun _ : Fin q => (Finset.univ : Finset ι))
      (fun j k => emb O R j (Hk.dd (Hk.NN n (Nq j : O) * c k) * a k))
    rw [Fintype.piFinset_univ] at hpu
    rw [← hpu]
    apply Finset.prod_congr rfl
    intro j _
    rw [← map_sum]
    congr 1
    conv_rhs => rw [← (hkDualExp O n ι a c hd (Hk.NN n (Nq j : O))).1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (Hk.NN n (Nq j : O)) (c k), mul_comm]
  have hψinc : ∀ m : M, ψ (inc m) = mkq (MvPolynomial.map β f) • ((1 : MSplitAlg P n) ⊗ₜ[B] m) := by
    intro m
    have hvW : ∀ j, inc m ∈ W j := fun j => hW j m
    have hb : ∀ i : Fin q → ι, ∃ b : B, algebraMap B (MSplitAlg P n) b =
        mkq (MvPolynomial.map β (∏ j, emb O R j (Hk.dd (Hk.NN n (Nq j : O) * c (i j))))) ∧
        tr (act (∏ j, emb O R j (c (i j))) (inc m)) = b • m := by
      intro i
      obtain ⟨b, hb1, hb2⟩ := hTprod (fun j => Hk.dd (Hk.NN n (Nq j : O) * c (i j)))
        (fun j => (hkDdProps O n).2.2.1 _)
      refine ⟨b, hb1, hinj ?_⟩
      rw [htr, ← hb2, prod_list, prod_list, List.ofFn_eq_map]
      exact tr_list H (List.nodup_finRange q) (fun j => c (i j)) hvW
    choose bb hbb1 hbb2 using hb
    rw [hψv]
    simp only [hbb2, ← TensorProduct.smul_tmul, Algebra.smul_def, hbb1, ← map_mul, ← TensorProduct.sum_tmul,
      ← map_sum]
    rw [hpoly, e1]
  refine ⟨φ, ψ, hφ2, hψ, hφψ, ?_⟩
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | tmul s m =>
    obtain ⟨p, rfl⟩ : ∃ p, mkq p = s := Ideal.Quotient.mk_surjective s
    induction p using MvPolynomial.induction_on' generalizing m with
    | monomial u b =>
      have hs : mkq (MvPolynomial.monomial u b) ⊗ₜ[B] m =
          mkq (MvPolynomial.map β (MvPolynomial.monomial u 1)) • ((1 : MSplitAlg P n) ⊗ₜ[B] (b • m)) := by
        rw [← e1, ← TensorProduct.smul_tmul, MvPolynomial.map_monomial, map_one, Algebra.smul_def]
        congr 1
        rw [show algebraMap B (MSplitAlg P n) b = mkq (MvPolynomial.C b) from rfl, ← map_mul,
          MvPolynomial.C_mul_monomial, mul_one]
      rw [hs, hφ2, hφ1, hψ, hψinc, smul_smul, smul_smul, mul_comm]
    | add p1 p2 h1 h2 =>
      rw [map_add, TensorProduct.add_tmul, map_add, map_add, h1, h2, smul_add]
