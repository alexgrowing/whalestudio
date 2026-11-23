import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymbolCongr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeSingleAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdXEqMonomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UgMemSpanListProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdPLinIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetrisationEquivariant

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible MvPolynomial TensorProduct

noncomputable section

namespace GlobalTheory.InducedPBW.Injective

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def coordP (ab : PIx p q) : Mat p q →ₗ[ℂ] ℂ := Matrix.entryLinearMap ℂ ℂ ab.1.1 ab.1.2

lemma isKC_iff (x : Mat p q) : (∀ j, coordP j x = 0) ↔ IsKC x := by
  constructor
  · intro h a b hab
    exact h ⟨(a, b), hab⟩
  · intro h j
    exact h j.1.1 j.1.2 j.2

private lemma sameBlock_trans_twisted_operators {a b c : Ix p q} (h1 : sameBlock a b) (h2 : sameBlock b c) :
    sameBlock a c := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp_all [sameBlock]

lemma isKC_mul {x y : Mat p q} (hx : IsKC x) (hy : IsKC y) : IsKC (x * y) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : sameBlock a c
  · have hcb : ¬ sameBlock c b := fun hcb => hab (sameBlock_trans_twisted_operators hac hcb)
    rw [hy c b hcb, mul_zero]
  · rw [hx a c hac, zero_mul]

lemma mulLin_tmul (x : Mat p q) (s : MvPolynomial (PIx p q) ℂ) (v : V) :
    mulLin coordP x (s ⊗ₜ[ℂ] v) = (pLin x * s) ⊗ₜ[ℂ] v := by
  rw [mulLin_apply]
  simp only [mulX, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, coordP,
    Matrix.entryLinearMap_apply]
  rw [pLin, Finset.sum_mul, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.smul_tmul', MvPolynomial.smul_eq_C_mul, mul_assoc]

lemma pLin_Eab (ab : PIx p q) : pLin (Eab ab.1.1 ab.1.2) = X ab := by
  unfold pLin
  rw [Finset.sum_eq_single ab]
  · simp [Eab]
  · intro b _ hb
    have : ¬ (ab.1.1 = b.1.1 ∧ ab.1.2 = b.1.2) := fun h =>
      hb (Subtype.ext (Prod.ext h.1.symm h.2.symm))
    simp [Eab, Matrix.single_apply_of_ne (h := this)]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma prod_map_X_eq_monomial' (L : List (PIx p q)) :
    (L.map (X : PIx p q → MvPolynomial (PIx p q) ℂ)).prod =
      monomial (Multiset.toFinsupp (L : Multiset (PIx p q))) 1 := by
  induction L with
  | nil => simp [Multiset.toFinsupp_zero, MvPolynomial.monomial_zero']
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, ← Multiset.cons_coe, ← Multiset.singleton_add,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, MvPolynomial.X,
      MvPolynomial.monomial_mul, one_mul]

lemma exists_list (α : PIx p q →₀ ℕ) : ∃ l : List (Mat p q), l.length = α.degree ∧
    (l.map pLin).prod = monomial α 1 := by
  refine ⟨(Finsupp.toMultiset α).toList.map fun ab => Eab ab.1.1 ab.1.2, ?_, ?_⟩
  · rw [List.length_map, Multiset.length_toList, Finsupp.card_toMultiset, Finsupp.degree_apply]
    rfl
  · rw [List.map_map]
    have hc : (pLin ∘ fun ab : PIx p q => Eab ab.1.1 ab.1.2) = X := funext pLin_Eab
    rw [hc, prod_map_X_eq_monomial', Multiset.coe_toList, Finsupp.toMultiset_toFinsupp]

private lemma coordP_Eab (i j : PIx p q) :
    coordP i (Eab j.1.1 j.1.2) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [coordP, Eab]
  · have hne : ¬ (j.1.1 = i.1.1 ∧ j.1.2 = i.1.2) := fun h' =>
      h (Subtype.ext (Prod.ext h'.1.symm h'.2.symm))
    simp [coordP, Eab, h, Matrix.single_apply_of_ne (h := hne)]

private lemma isKC_sub' {x y : Mat p q} (hx : IsKC x) (hy : IsKC y) : IsKC (x - y) := by
  intro a b hab
  rw [Matrix.sub_apply, hx a b hab, hy a b hab, sub_zero]

lemma exists_rep_gl (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (h : IsKLieAct act) :
    ∃ ρ : Ug p q →ₐ[ℂ] Module.End ℂ (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V),
      (∀ x, IsKC x → ∀ v, ρ (ugι p q x) (zv 0 v) = zv 0 (act x v)) ∧
      ∀ n x, ∀ m ∈ degLt ℂ (PIx p q) V n,
        ρ (ugι p q x) m - mulLin coordP x m ∈ degLt ℂ (PIx p q) V n := by
  let _ : LinearOrder (PIx p q) :=
    LinearOrder.lift' (Fintype.equivFin (PIx p q)) (Fintype.equivFin (PIx p q)).injective
  have hK : ∀ x y : Mat p q, (∀ j, coordP j x = 0) → (∀ j, coordP j y = 0) →
      ∀ j, coordP j ⁅x, y⁆ = 0 := by
    intro x y hx hy
    rw [Ring.lie_def]
    exact (isKC_iff _).mpr (isKC_sub' (isKC_mul ((isKC_iff x).mp hx) ((isKC_iff y).mp hy))
      (isKC_mul ((isKC_iff y).mp hy) ((isKC_iff x).mp hx)))
  have hact : ∀ x y : Mat p q, (∀ j, coordP j x = 0) → (∀ j, coordP j y = 0) →
      act ⁅x, y⁆ = act x * act y - act y * act x := by
    intro x y hx hy
    rw [Ring.lie_def]
    exact h x y ((isKC_iff x).mp hx) ((isKC_iff y).mp hy)
  obtain ⟨ρ, hbr, hk, hdeg⟩ := exists_rep (R := ℂ) (ι := PIx p q) (g := Mat p q) (V := V)
    (fun ab => Eab ab.1.1 ab.1.2) coordP act
    (fun i j => by rw [coordP_Eab]; split_ifs <;> rfl) hK hact
  let f : Mat p q →ₗ⁅ℂ⁆ Module.End ℂ (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V) :=
    { ρ with
      map_lie' := fun {x y} => by
        show ρ ⁅x, y⁆ = ⁅ρ x, ρ y⁆
        rw [hbr, Ring.lie_def] }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ f, fun x hx v => ?_, fun n x m hm => ?_⟩
  · rw [show ugι p q x = UniversalEnvelopingAlgebra.ι ℂ x from rfl,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    exact hk x ((isKC_iff x).mpr hx) v
  · rw [show ugι p q x = UniversalEnvelopingAlgebra.ι ℂ x from rfl,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    exact hdeg n x m hm

lemma prod_tmul_mem (l : List (Mat p q)) (v : V) :
    (l.map pLin).prod ⊗ₜ[ℂ] v ∈ degLt ℂ (PIx p q) V (l.length + 1) := by
  induction l with
  | nil =>
    have h1 : (1 : MvPolynomial (PIx p q) ℂ) ⊗ₜ[ℂ] v = zv 0 v := by
      simp [zv, MvPolynomial.monomial_zero']
    rw [List.map_nil, List.prod_nil, h1]
    exact zv_mem (by simp) v
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, ← mulLin_tmul, List.length_cons]
    exact mulLin_mem coordP x _ ih

lemma exists_symbol (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (h : IsKLieAct act) :
    ∃ φ : Ind act →ₗ[ℂ] (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V), ∀ (l : List (Mat p q)) (v : V),
      φ ((indRel act).mkQ ((l.map (ugι p q)).prod ⊗ₜ[ℂ] v)) - (l.map pLin).prod ⊗ₜ[ℂ] v ∈
        degLt ℂ (PIx p q) V l.length := by
  obtain ⟨ρ, hk, hdeg⟩ := exists_rep_gl act h
  let F : Ug p q →ₗ[ℂ] V →ₗ[ℂ] (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V) :=
    LinearMap.mk₂ ℂ (fun u v => ρ u (zv 0 v)) (fun u u' v => by simp) (fun c u v => by simp)
      (fun u v v' => by simp) (fun c u v => by simp)
  have hΦ : ∀ u v, TensorProduct.lift F (u ⊗ₜ[ℂ] v) = ρ u (zv 0 v) := fun u v => by
    simp [F]
  have hle : indRel act ≤ LinearMap.ker (TensorProduct.lift F) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨u, Y, v, hY, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hΦ, map_mul, Module.End.mul_apply,
      hk Y hY v, sub_self]
  refine ⟨(indRel act).liftQ (TensorProduct.lift F) hle, fun l v => ?_⟩
  simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, hΦ]
  induction l with
  | nil =>
    simp [zv, MvPolynomial.monomial_zero']
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, List.map_cons,
      List.prod_cons, List.length_cons]
    have hA : ρ (l.map (ugι p q)).prod (zv 0 v) ∈ degLt ℂ (PIx p q) V (l.length + 1) := by
      have h2 := Submodule.add_mem _ (degLt_mono (Nat.le_succ _) ih) (prod_tmul_mem l v)
      rwa [sub_add_cancel] at h2
    have e : ρ (ugι p q x) (ρ (l.map (ugι p q)).prod (zv 0 v)) - (pLin x * (l.map pLin).prod) ⊗ₜ[ℂ] v =
        (ρ (ugι p q x) (ρ (l.map (ugι p q)).prod (zv 0 v)) -
          mulLin coordP x (ρ (l.map (ugι p q)).prod (zv 0 v))) +
        mulLin coordP x (ρ (l.map (ugι p q)).prod (zv 0 v) - (l.map pLin).prod ⊗ₜ[ℂ] v) := by
      rw [map_sub, mulLin_tmul]
      abel
    rw [e]
    exact Submodule.add_mem _ (hdeg _ x _ hA) (mulLin_mem coordP x _ ih)

lemma eq_zero_of_mem {k : ℕ} {z : MvPolynomial (PIx p q) ℂ ⊗[ℂ] V} (h1 : z ∈ symTens p q V k)
    (h2 : z ∈ degLt ℂ (PIx p q) V k) : z = 0 := by
  have hfix : LinearMap.rTensor V (homogeneousComponent k) z = z := by
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp h1
    have hc : (homogeneousComponent k).comp (homog (PIx p q) k).subtype =
        (homog (PIx p q) k).subtype := by
      refine LinearMap.ext fun P => ?_
      simp [homogeneousComponent_of_mem P.2]
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hc]
  have hkill : degLt ℂ (PIx p q) V k ≤
      LinearMap.ker (LinearMap.rTensor V (homogeneousComponent (σ := PIx p q) (R := ℂ) k)) := by
    refine Submodule.span_le.mpr ?_
    rintro m ⟨α, v, hα, rfl⟩
    have hm : (monomial α (1 : ℂ)) ∈ homogeneousSubmodule (PIx p q) ℂ α.degree :=
      (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial 1 rfl)
    simp only [SetLike.mem_coe, LinearMap.mem_ker, zv, TensorProduct.mk_apply,
      LinearMap.rTensor_tmul, homogeneousComponent_of_mem hm, if_neg (Nat.ne_of_gt hα),
      TensorProduct.zero_tmul]
  have h3 := hkill h2
  rw [LinearMap.mem_ker, hfix] at h3
  exact h3

theorem symmetrisation_injective (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (h : IsKLieAct act)
    (hs : SymbolCongr act) (k : ℕ) (z) (hz : z ∈ symTens p q V k)
    (hz' : (indRel act).mkQ (LinearMap.rTensor V (symU p q) z) ∈ indFlt act k) : z = 0 := by
  obtain ⟨φ, hφ⟩ := exists_symbol act h
  have hF : ∀ j < k, indF act j ≤ (degLt ℂ (PIx p q) V k).comap φ := by
    intro j hj
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, v, rfl⟩
    let Lv : Ug p q →ₗ[ℂ] (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V) :=
      φ ∘ₗ (indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v
    have hU : UgF p q j ≤ (degLt ℂ (PIx p q) V k).comap Lv := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, hl, rfl⟩
      have h4 := Submodule.add_mem _ (degLt_mono (show l.length ≤ k by omega) (hφ l v))
        (degLt_mono (show l.length + 1 ≤ k by omega) (prod_tmul_mem l v))
      rw [sub_add_cancel] at h4
      exact h4
    exact hU hu
  have hlow : indFlt act k ≤ (degLt ℂ (PIx p q) V k).comap φ := by
    unfold indFlt
    exact iSup_le fun j => iSup_le fun hj => hF j hj
  have hsym : ∀ P : MvPolynomial (PIx p q) ℂ, P.IsHomogeneous k → ∀ v : V,
      φ ((indRel act).mkQ (symU p q P ⊗ₜ[ℂ] v)) - P ⊗ₜ[ℂ] v ∈ degLt ℂ (PIx p q) V k := by
    intro P hP v
    let M : MvPolynomial (PIx p q) ℂ →ₗ[ℂ] (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V) :=
      φ ∘ₗ (indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v ∘ₗ symU p q -
        (TensorProduct.mk ℂ (MvPolynomial (PIx p q) ℂ) V).flip v
    have hM : ∀ Q, M Q = φ ((indRel act).mkQ (symU p q Q ⊗ₜ[ℂ] v)) - Q ⊗ₜ[ℂ] v := fun Q => rfl
    rw [← hM, P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    have hdeg : α.degree = k := by
      rw [Finsupp.degree_eq_weight_one]
      exact hP (mem_support_iff.mp hα)
    have hmon : monomial α (coeff α P) = coeff α P • monomial α (1 : ℂ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [hM]
    obtain ⟨l, hl, hprod⟩ := exists_list α
    have hc := hs l v
    have h1 := hφ l v
    rw [hprod, hl, hdeg] at hc h1
    have h8 : φ ((indRel act).mkQ ((l.map (ugι p q)).prod ⊗ₜ[ℂ] v) -
        (indRel act).mkQ (symU p q (monomial α 1) ⊗ₜ[ℂ] v)) ∈ degLt ℂ (PIx p q) V k := hlow hc
    have key := Submodule.sub_mem _ h1 h8
    rw [map_sub, sub_sub_sub_cancel_left] at key
    exact key
  have hzsym : φ ((indRel act).mkQ (LinearMap.rTensor V (symU p q) z)) - z ∈
      degLt ℂ (PIx p q) V k := by
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hz
    clear hz hz'
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul P v =>
      simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype]
      exact hsym P.1 P.2 v
    | add w w' hw hw' =>
      have h5 := Submodule.add_mem _ hw hw'
      simp only [map_add]
      rw [add_sub_add_comm]
      exact h5
  have hz0 : z ∈ degLt ℂ (PIx p q) V k := by
    have h7 : φ ((indRel act).mkQ (LinearMap.rTensor V (symU p q) z)) ∈ degLt ℂ (PIx p q) V k :=
      hlow hz'
    have h6 := Submodule.sub_mem _ h7 hzsym
    rwa [sub_sub_cancel] at h6
  exact eq_zero_of_mem hz hz0

end GlobalTheory.InducedPBW.Injective

namespace GlobalTheory.InducedPBW

theorem pbw_induced : admQ8 := by
  unfold admQ8
  intro p q V _ _ act h
  have hs := symbolCongr p q V act
  refine ⟨iSup_indF_eq_top p q V act, fun k => ⟨Onto.indF_eq_sup p q V act hs k,
    fun z hz hz' => Injective.symmetrisation_injective act h hs k z hz hz',
    fun Y hY z hz => symmetrisation_equivariant p q V act hs k Y hY z hz⟩⟩

end GlobalTheory.InducedPBW
