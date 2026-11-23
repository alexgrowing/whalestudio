import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp

noncomputable section

open NumberField IsDedekindDomain Polynomial Module
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.TNZ.Isotypic₂

section Avg

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module ℂ V]

def eigSub (R : Γ →* Module.End ℂ V) (χ : Γ →* ℂˣ) : Submodule ℂ V where
  carrier := {v | ∀ g, R g v = (χ g : ℂ) • v}
  add_mem' := by
    intro x y hx hy g
    simp only [Set.mem_setOf_eq] at hx hy
    rw [map_add, hx g, hy g, smul_add]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c x hx g
    simp only [Set.mem_setOf_eq] at hx
    rw [map_smul, hx g, smul_comm]

theorem mem_eigSub {R : Γ →* Module.End ℂ V} {χ : Γ →* ℂˣ} {v : V} :
    v ∈ eigSub R χ ↔ ∀ g, R g v = (χ g : ℂ) • v := Iff.rfl

variable [Fintype Γ]

def proj (R : Γ →* Module.End ℂ V) (χ : Γ →* ℂˣ) : Module.End ℂ V :=
  (Fintype.card Γ : ℂ)⁻¹ • ∑ g, (((χ g)⁻¹ : ℂˣ) : ℂ) • R g

theorem proj_apply (R : Γ →* Module.End ℂ V) (χ : Γ →* ℂˣ) (v : V) :
    proj R χ v = (Fintype.card Γ : ℂ)⁻¹ • ∑ g, (((χ g)⁻¹ : ℂˣ) : ℂ) • R g v := by
  simp [proj, LinearMap.sum_apply]

theorem card_ne_zero' : (Fintype.card Γ : ℂ) ≠ 0 := by
  haveI : Nonempty Γ := ⟨1⟩
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

omit [AddCommGroup V] [Module ℂ V] in
theorem orth_self (χ : Γ →* ℂˣ) : ∑ g, (((χ g)⁻¹ : ℂˣ) : ℂ) * (χ g : ℂ) = (Fintype.card Γ : ℂ) := by
  simp

omit [AddCommGroup V] [Module ℂ V] in
theorem orth_ne {χ χ' : Γ →* ℂˣ} (hc : χ ≠ χ') : ∑ g, (((χ g)⁻¹ : ℂˣ) : ℂ) * (χ' g : ℂ) = 0 := by
  let f : Γ →* ℂ := (Units.coeHom ℂ).comp (χ⁻¹ * χ')
  have hf : f ≠ 1 := by
    intro h1
    apply hc
    refine MonoidHom.ext fun g => ?_
    have h2 : (χ⁻¹ * χ') g = 1 := Units.ext (by simpa [f] using congrArg (fun F : Γ →* ℂ => F g) h1)
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_eq_one] at h2
    exact h2
  have := sum_hom_units_eq_zero f hf
  simpa [f] using this

theorem proj_apply_of_mem (R : Γ →* Module.End ℂ V) (χ χ' : Γ →* ℂˣ) {v : V} (hv : v ∈ eigSub R χ') :
    proj R χ v = ((Fintype.card Γ : ℂ)⁻¹ * ∑ g, (((χ g)⁻¹ : ℂˣ) : ℂ) * (χ' g : ℂ)) • v := by
  rw [proj_apply, mul_smul, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hv g, smul_smul]

theorem proj_self_of_mem (R : Γ →* Module.End ℂ V) (χ : Γ →* ℂˣ) {v : V} (hv : v ∈ eigSub R χ) :
    proj R χ v = v := by
  rw [proj_apply_of_mem R χ χ hv, orth_self, inv_mul_cancel₀ card_ne_zero', one_smul]

theorem proj_ne_of_mem (R : Γ →* Module.End ℂ V) {χ χ' : Γ →* ℂˣ} (hc : χ ≠ χ') {v : V}
    (hv : v ∈ eigSub R χ') : proj R χ v = 0 := by
  rw [proj_apply_of_mem R χ χ' hv, orth_ne hc, mul_zero, zero_smul]

theorem proj_mem (R : Γ →* Module.End ℂ V) (χ : Γ →* ℂˣ) (v : V) : proj R χ v ∈ eigSub R χ := by
  rw [mem_eigSub]
  intro k
  simp only [proj_apply, map_smul, map_sum]
  rw [smul_comm (χ k : ℂ) ((Fintype.card Γ : ℂ)⁻¹)]
  congr 1
  rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulLeft k) (fun g => (χ k : ℂ) • (((χ g)⁻¹ : ℂˣ) : ℂ) • R g v)]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]
  congr 1
  simp only [mul_inv, Units.val_mul]
  rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem isProj (R : Γ →* Module.End ℂ V) (χ : Γ →* ℂˣ) : LinearMap.IsProj (eigSub R χ) (proj R χ) :=
  ⟨proj_mem R χ, fun _ hv => proj_self_of_mem R χ hv⟩

theorem finrank_eigSub [FiniteDimensional ℂ V] (R : Γ →* Module.End ℂ V) (χ : Γ →* ℂˣ) :
    (finrank ℂ (eigSub R χ) : ℂ) = LinearMap.trace ℂ V (proj R χ) :=
  (isProj R χ).trace.symm

theorem trace_proj [FiniteDimensional ℂ V] (R : Γ →* Module.End ℂ V) (χ : Γ →* ℂˣ) :
    LinearMap.trace ℂ V (proj R χ) =
      (Fintype.card Γ : ℂ)⁻¹ * ∑ g, (((χ g)⁻¹ : ℂˣ) : ℂ) * LinearMap.trace ℂ V (R g) := by
  simp [proj, map_sum, map_smul]

theorem decomp [FiniteDimensional ℂ V] {ι : Type*} [Fintype ι] (R : Γ →* Module.End ℂ V)
    (χ : ι → Γ →* ℂˣ) (d : ι → ℕ) (hχ : Function.Injective χ)
    (htr : ∀ g, LinearMap.trace ℂ V (R g) = ∑ b, (d b : ℂ) * (χ b g : ℂ))
    (hdim : ∑ b, d b = finrank ℂ V) :
    (∀ b, finrank ℂ (eigSub R (χ b)) = d b) ∧ ∀ v, v = ∑ b, proj R (χ b) v := by
  have htp : ∀ b, LinearMap.trace ℂ V (proj R (χ b)) = d b := by
    intro b
    rw [trace_proj]
    have h1 : ∑ g, (((χ b g)⁻¹ : ℂˣ) : ℂ) * LinearMap.trace ℂ V (R g) =
        ∑ c, (d c : ℂ) * ∑ g, (((χ b g)⁻¹ : ℂˣ) : ℂ) * (χ c g : ℂ) := by
      simp_rw [htr, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun g _ => by ring
    rw [h1, Finset.sum_eq_single b, orth_self]
    · rw [mul_comm, mul_assoc, mul_inv_cancel₀ card_ne_zero', mul_one]
    · intro c _ hcb
      rw [orth_ne (fun h => hcb (hχ h).symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ b) h
  have hfin : ∀ b, finrank ℂ (eigSub R (χ b)) = d b := fun b => by
    exact_mod_cast (finrank_eigSub R (χ b)).trans (htp b)
  refine ⟨hfin, ?_⟩
  obtain ⟨E, hE⟩ : ∃ E : Module.End ℂ V, E = ∑ b, proj R (χ b) := ⟨_, rfl⟩
  have hEv : ∀ v, E v = ∑ b, proj R (χ b) v := fun v => by
    rw [hE, LinearMap.sum_apply]
  have hPP : ∀ b v, proj R (χ b) (E v) = proj R (χ b) v := by
    intro b v
    rw [hEv, map_sum, Finset.sum_eq_single b]
    · exact proj_self_of_mem R _ (proj_mem R _ _)
    · intro c _ hcb
      exact proj_ne_of_mem R (fun h => hcb (hχ h).symm) (proj_mem R _ _)
    · intro h
      exact absurd (Finset.mem_univ b) h
  have hEE : ∀ v, E (E v) = E v := fun v => by
    rw [hEv (E v)]
    simp_rw [hPP]
    exact (hEv v).symm
  have hproj : LinearMap.IsProj (LinearMap.range E) E :=
    ⟨fun v => LinearMap.mem_range_self E v, fun v hv => by
      obtain ⟨u, rfl⟩ := hv
      exact hEE u⟩
  have htrE : LinearMap.trace ℂ V E = finrank ℂ V := by
    rw [hE, map_sum]
    simp_rw [htp]
    rw [← Nat.cast_sum, hdim]
  have hr : finrank ℂ (LinearMap.range E) = finrank ℂ V := by
    exact_mod_cast hproj.trace.symm.trans htrE
  have htop := Submodule.eq_top_of_finrank_eq hr
  intro v
  have hv : v ∈ LinearMap.range E := htop ▸ Submodule.mem_top
  obtain ⟨u, rfl⟩ := hv
  rw [← hEv (E u), hEE]

end Avg

section Lin

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem trace_of_charpoly {m : ℕ} (f : Module.End ℂ W) (c : Fin m → ℂ) (d : Fin m → ℕ)
    (hf : f.charpoly = ∏ b, (X - C (c b)) ^ d b) : LinearMap.trace ℂ W f = ∑ b, (d b : ℂ) * c b := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _), hf,
    Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr fun b _ => pow_ne_zero _ (X_sub_C_ne_zero _))]
  simp [Multiset.sum_bind, Polynomial.roots_pow, Multiset.sum_nsmul, List.sum_ofFn, nsmul_eq_mul]

theorem charpoly_scalar (f : Module.End ℂ W) (c : ℂ) (hf : ∀ v, f v = c • v) :
    f.charpoly = (X - C c) ^ finrank ℂ W := by
  have : f = c • LinearMap.id := LinearMap.ext fun v => by simp [hf]
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ W), this, map_smul, LinearMap.toMatrix_id,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Lin

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem exists_conj (σ : Weil h) (t : Ine (F := E) A) :
    ∃ t' : Ine (F := E) A, ineIncl h t' = σ⁻¹ * ineIncl h t * σ :=
  ⟨⟨((σ⁻¹ * ineIncl h t * σ : Weil h) : G E Ω), deg_eq_zero_iff.mp (by simp)⟩, Subtype.ext rfl⟩

def Phi (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) : Weil h →* (Fin m → ℂˣ) × (Module.End ℂ V)ˣ :=
  (Pi.monoidHom ψ).prod a.ρ.asGroupHom

theorem isSmooth_Phi (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) (hψ : ∀ b, IsSmooth (ψ b)) :
    IsSmooth (Phi a ψ) := by
  have h1 : IsSmooth (Pi.monoidHom ψ) := by
    have : {σ : Ine (F := E) A | Pi.monoidHom ψ (ineIncl h σ) = 1} = ⋂ b, {σ | ψ b (ineIncl h σ) = 1} := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact funext_iff
    unfold IsSmooth
    rw [this]
    exact isOpen_iInter_of_finite hψ
  have h2 : IsSmooth a.ρ.asGroupHom := a.smooth.of_le fun σ hσ =>
    Units.ext (by rw [Representation.asGroupHom_apply, hσ, Units.val_one])
  exact h1.of_le₂ h2 fun σ h1 h2 => Prod.ext h1 h2

def Gam (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) : Subgroup ((Fin m → ℂˣ) × (Module.End ℂ V)ˣ) :=
  ((Phi a ψ).comp (ineIncl h)).range

theorem finite_Gam (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) (hψ : ∀ b, IsSmooth (ψ b)) :
    Finite (Gam a ψ) := by
  have := (isSmooth_Phi a ψ hψ).finite_range
  have hfin : ((Gam a ψ : Set ((Fin m → ℂˣ) × (Module.End ℂ V)ˣ))).Finite := this.subset (by
    intro x hx
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hx
    exact ⟨t, rfl⟩)
  exact hfin.to_subtype

def Rg (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) : Gam a ψ →* Module.End ℂ V :=
  (Units.coeHom _).comp ((MonoidHom.snd _ _).comp (Gam a ψ).subtype)

def chig (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) (b : Fin m) : Gam a ψ →* ℂˣ :=
  (Pi.evalMonoidHom _ b).comp ((MonoidHom.fst _ _).comp (Gam a ψ).subtype)

def elt (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) (t : Ine (F := E) A) : Gam a ψ :=
  ⟨Phi a ψ (ineIncl h t), MonoidHom.mem_range.mpr ⟨t, rfl⟩⟩

theorem Rg_elt (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) (t : Ine (F := E) A) :
    Rg a ψ (elt a ψ t) = a.ρ (ineIncl h t) := by
  simp [Rg, elt, Phi, Representation.asGroupHom_apply]

theorem chig_elt (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) (b : Fin m) (t : Ine (F := E) A) :
    chig a ψ b (elt a ψ t) = ψ b (ineIncl h t) := rfl

theorem exists_elt (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) (g : Gam a ψ) :
    ∃ t, g = elt a ψ t := by
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp g.2
  exact ⟨t, Subtype.ext ht.symm⟩

theorem mem_eig_iff (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) (b : Fin m) {v : V} :
    v ∈ eigSub (Rg a ψ) (chig a ψ b) ↔ ∀ t : Ine (F := E) A, a.ρ (ineIncl h t) v = (ψ b (ineIncl h t) : ℂ) • v := by
  constructor
  · intro hv t
    have := hv (elt a ψ t)
    rwa [Rg_elt, chig_elt] at this
  · intro hv g
    obtain ⟨t, rfl⟩ := exists_elt a ψ g
    rw [Rg_elt, chig_elt]
    exact hv t

theorem stable (a : WDRep h V) {m : ℕ} (ψ : Fin m → Weil h →* ℂˣ) (b : Fin m) (σ : Weil h) {v : V}
    (hv : v ∈ eigSub (Rg a ψ) (chig a ψ b)) : a.ρ σ v ∈ eigSub (Rg a ψ) (chig a ψ b) := by
  rw [mem_eig_iff] at hv ⊢
  intro t
  obtain ⟨t', ht'⟩ := exists_conj σ t
  have e1 : ineIncl h t * σ = σ * ineIncl h t' := by
    rw [ht']
    group
  have e2 : ψ b (ineIncl h t') = ψ b (ineIncl h t) := by
    rw [ht', map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  calc a.ρ (ineIncl h t) (a.ρ σ v) = a.ρ (ineIncl h t * σ) v := by rw [map_mul, Module.End.mul_apply]
    _ = a.ρ σ (a.ρ (ineIncl h t') v) := by rw [e1, map_mul, Module.End.mul_apply]
    _ = (ψ b (ineIncl h t) : ℂ) • a.ρ σ v := by rw [hv t', map_smul, e2]

def res (a : WDRep h V) (U : Submodule ℂ V) (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) : WDRep h U where
  ρ :=
    { toFun := fun σ => (a.ρ σ).restrict (hU σ)
      map_one' := by
        ext v
        simp
      map_mul' := fun σ τ => by
        ext v
        simp }
  N := 0
  smooth := a.smooth.of_le fun σ hσ => by
    ext v
    simp [hσ]
  semisimple σ := (a.semisimple σ).restrict ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (a.ρ σ)).mpr (hU σ))
  nilpotent := IsNilpotent.zero
  comm σ := by simp

theorem res_ρ_apply (a : WDRep h V) (U : Submodule ℂ V) (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) (σ : Weil h)
    (x : U) : ((res a U hU).ρ σ x : V) = a.ρ σ x := rfl

theorem iso_sum (a : WDRep h V) (hN : a.N = 0) (U W : Submodule ℂ V) (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U)
    (hW : ∀ σ, ∀ v ∈ W, a.ρ σ v ∈ W) (hc : IsCompl U W) : ((res a U hU).sum (res a W hW)).Iso a :=
  ⟨Submodule.prodEquivOfIsCompl U W hc, fun σ x => by
      simp only [Submodule.coe_prodEquivOfIsCompl', WDRep.sum_ρ, LinearMap.prodMap_apply, res_ρ_apply, map_add],
    fun x => by simp [hN, res]⟩

theorem sumList_cons (x : WD h) (l : List (WD h)) : sumList (x :: l) = x.lpSum (sumList l) := rfl

theorem key : ∀ (s : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V),
    a.N = 0 → ∀ (d : Fin s → ℕ) (ψ : Fin s → Weil h →* ℂˣ), (∀ b, IsSmooth (ψ b)) →
    (∀ b c, b ≠ c → ∃ t : Ine (F := E) A, ψ b (ineIncl h t) ≠ ψ c (ineIncl h t)) →
    (∀ t : Ine (F := E) A, (a.ρ (ineIncl h t)).charpoly = ∏ b, (X - C ((ψ b (ineIncl h t) : ℂˣ) : ℂ)) ^ d b) →
    ∃ v : Fin s → WD h, (∀ b, (v b).mono0 ∧ (v b).lpDim = d b ∧
      ∀ t : Ine (F := E) A, (v b).charPol (ineIncl h t) = (X - C ((ψ b (ineIncl h t) : ℂˣ) : ℂ)) ^ d b) ∧
      WD.mk a = sumList (List.ofFn v) := by
  intro s
  induction s with
  | zero =>
    intro V _ _ _ a hN d ψ hψ hdist hchar
    have h0 : finrank ℂ V = 0 := by
      rw [← LinearMap.charpoly_natDegree (a.ρ (ineIncl h 1)), hchar 1]
      simp
    refine ⟨Fin.elim0, fun b => b.elim0, ?_⟩
    rw [List.ofFn_zero]
    exact WD.sound (b := WDRep.diag h (ι := Fin 0) fun i => i.elim0)
      ⟨LinearEquiv.ofFinrankEq _ _ (by simp [h0]), fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | succ s ih =>
    intro V _ _ _ a hN d ψ hψ hdist hchar
    haveI := finite_Gam a ψ hψ
    letI : Fintype (Gam a ψ) := Fintype.ofFinite _
    have hinj : Function.Injective (chig a ψ) := by
      intro b c hbc
      by_contra hne
      obtain ⟨t, ht⟩ := hdist b c hne
      apply ht
      have := congrArg (fun χ : Gam a ψ →* ℂˣ => χ (elt a ψ t)) hbc
      simpa only [chig_elt] using this
    have hdim : ∑ b, d b = finrank ℂ V := by
      rw [← LinearMap.charpoly_natDegree (a.ρ (ineIncl h 1)), hchar 1,
        Polynomial.natDegree_prod_of_monic _ _ fun b _ => (monic_X_sub_C _).pow _]
      simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
    have htr : ∀ g, LinearMap.trace ℂ V (Rg a ψ g) = ∑ b, (d b : ℂ) * (chig a ψ b g : ℂ) := by
      intro g
      obtain ⟨t, rfl⟩ := exists_elt a ψ g
      simp only [Rg_elt, chig_elt]
      exact trace_of_charpoly _ _ _ (hchar t)
    obtain ⟨hfin, hsum⟩ := decomp (Rg a ψ) (chig a ψ) d hinj htr hdim
    have hU : ∀ σ, ∀ v ∈ eigSub (Rg a ψ) (chig a ψ 0), a.ρ σ v ∈ eigSub (Rg a ψ) (chig a ψ 0) :=
      fun σ v hv => stable a ψ 0 σ hv
    have hW : ∀ σ, ∀ v ∈ ⨆ b : Fin s, eigSub (Rg a ψ) (chig a ψ b.succ),
        a.ρ σ v ∈ ⨆ b : Fin s, eigSub (Rg a ψ) (chig a ψ b.succ) := by
      intro σ v hv
      refine Submodule.iSup_induction _ (motive := fun v => a.ρ σ v ∈ ⨆ b : Fin s, eigSub (Rg a ψ) (chig a ψ b.succ))
        hv ?_ ?_ ?_
      · intro b x hx
        exact Submodule.mem_iSup_of_mem b (stable a ψ _ σ hx)
      · simp
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    have hWker : ∀ v ∈ ⨆ b : Fin s, eigSub (Rg a ψ) (chig a ψ b.succ), proj (Rg a ψ) (chig a ψ 0) v = 0 := by
      intro v hv
      refine Submodule.iSup_induction _ (motive := fun v => proj (Rg a ψ) (chig a ψ 0) v = 0) hv ?_ ?_ ?_
      · intro b x hx
        exact proj_ne_of_mem _ (fun h => Fin.succ_ne_zero b (hinj h).symm) hx
      · simp
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
    have hc : IsCompl (eigSub (Rg a ψ) (chig a ψ 0)) (⨆ b : Fin s, eigSub (Rg a ψ) (chig a ψ b.succ)) := by
      constructor
      · rw [Submodule.disjoint_def]
        intro v hvU hvW
        have := proj_self_of_mem _ _ hvU
        rw [hWker v hvW] at this
        exact this.symm
      · rw [codisjoint_iff, Submodule.eq_top_iff']
        intro v
        rw [hsum v, Fin.sum_univ_succ]
        exact Submodule.add_mem_sup (proj_mem _ _ v)
          (Submodule.sum_mem _ fun b _ => Submodule.mem_iSup_of_mem b (proj_mem _ _ v))
    have hUchar : ∀ t, ((res a _ hU).ρ (ineIncl h t)).charpoly = (X - C ((ψ 0 (ineIncl h t) : ℂˣ) : ℂ)) ^ d 0 := by
      intro t
      rw [charpoly_scalar _ _ fun x => Subtype.ext (by
        rw [res_ρ_apply, Submodule.coe_smul]
        exact (mem_eig_iff a ψ 0).mp x.2 t), hfin 0]
    have hiso := iso_sum a hN _ _ hU hW hc
    have hWchar : ∀ t, ((res a _ hW).ρ (ineIncl h t)).charpoly =
        ∏ b : Fin s, (X - C ((ψ b.succ (ineIncl h t) : ℂˣ) : ℂ)) ^ d b.succ := by
      intro t
      have h1 := hiso.charpoly_eq (ineIncl h t)
      rw [hchar t, WDRep.sum_ρ, LinearMap.charpoly_prodMap, hUchar t, Fin.prod_univ_succ] at h1
      exact mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero _)) h1
    obtain ⟨v', hv', hmk⟩ := ih (res a _ hW) rfl (fun b => d b.succ) (fun b => ψ b.succ) (fun b => hψ _)
      (fun b c hbc => hdist _ _ (fun h => hbc (Fin.succ_injective _ h))) hWchar
    refine ⟨Fin.cons (WD.mk (res a _ hU)) v', fun b => ?_, ?_⟩
    · refine Fin.cases ?_ (fun b => ?_) b
      · simp only [Fin.cons_zero]
        exact ⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff _).mpr rfl, by rw [WD.lpDim_mk, hfin 0], fun t => by rw [WD.charPol_mk, hUchar t]⟩
      · simpa only [Fin.cons_succ] using hv' b
    · rw [List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [sumList_cons, ← hmk, WD.lpSum_mk]
      exact (WD.sound hiso).symm

end Isotypic₂

open Isotypic₂ in
theorem step_isotypic : IsotypicComponentProp := by
  intro E Ω _ _ _ _ _ A w h u s d ψ hψ hdist hmono hchar
  obtain ⟨n, a, rfl⟩ := u.exists_rep
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hmono
  simp only [WD.charPol_mk] at hchar
  exact key s a hmono d ψ hψ hdist hchar

end UpperTheory.TNZ
