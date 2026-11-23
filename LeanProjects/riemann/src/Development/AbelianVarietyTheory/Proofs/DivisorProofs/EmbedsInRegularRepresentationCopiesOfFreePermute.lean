import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem embReg_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H = finrank K V := by
  intro K Γ V X _ _ _ _ _ _ _ _ ρ H _ hfree A hA hmap
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have hinv : ∀ (g : Γ) (v : V), ρ g⁻¹ (ρ g v) = v := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let E := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA
  let comp : ∀ x : X, V →ₗ[K] A x := fun x =>
    (DirectSum.component K X (fun y => A y) x) ∘ₗ E.symm.toLinearMap
  have comp_apply : ∀ x v, comp x v = E.symm v x := fun x v => rfl

  have htr : ∀ (h : H) (x : X) (v : V), (comp (h • x) (ρ h v) : V) = ρ h (comp x v) := by
    intro h x v
    obtain ⟨w, rfl⟩ : ∃ w, v = E w := ⟨E.symm v, (E.apply_symm_apply v).symm⟩
    rw [comp_apply, comp_apply, E.symm_apply_apply]
    induction w using DirectSum.induction_on with
    | zero => simp
    | of y a =>
      have hE : E (DirectSum.of (fun y => A y) y a) = (a : V) := DirectSum.coeLinearMap_of A y a
      rw [hE]
      by_cases hxy : y = x
      · subst hxy
        rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem hA (hmap h y a a.2), DirectSum.of_eq_same]
      · have hne : h • y ≠ h • x := fun he => hxy (smul_left_cancel h he)
        rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne hA hne (hmap h y a a.2),
          DirectSum.of_eq_of_ne (β := fun i => A i) y x a (Ne.symm hxy)]
        simp
    | add w₁ w₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, DirectSum.add_apply, Submodule.coe_add, h₁, h₂,
        DirectSum.add_apply, Submodule.coe_add, map_add]
  have hzero : ∀ v : V, (∀ x, comp x v = 0) → v = 0 := by
    intro v hv
    have : E.symm v = 0 := DFinsupp.ext fun x => by rw [← comp_apply, hv]; rfl
    rw [← E.apply_symm_apply v, this, map_zero]

  let d : X → ℕ := fun x => finrank K (A x)
  have hdle : ∀ (h : H) (x : X), d x ≤ d (h • x) := by
    intro h x
    let φ : A x →ₗ[K] A (h • x) :=
      LinearMap.codRestrict (A (h • x)) ((ρ h).comp (A x).subtype) (fun a => hmap h x a a.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) fun a b hab => ?_
    have := congrArg (fun c : A (h • x) => ρ (h : Γ)⁻¹ (c : V)) hab
    have ha : ((φ a : A (h • x)) : V) = ρ h a := rfl
    have hb : ((φ b : A (h • x)) : V) = ρ h b := rfl
    simp only [ha, hb, hinv] at this
    exact Subtype.ext this
  have hdeq : ∀ (h : H) (x : X), d (h • x) = d x := by
    intro h x
    refine le_antisymm ?_ (hdle h x)
    have := hdle h⁻¹ (h • x)
    rwa [inv_smul_smul] at this

  let O := MulAction.orbitRel.Quotient H X
  haveI : Fintype O := Fintype.ofFinite O
  let β : H × O → X := fun p => p.1 • p.2.out
  have hβ : Function.Bijective β := by
    constructor
    · rintro ⟨h, o⟩ ⟨h', o'⟩ he
      simp only [β] at he
      have ho : o = o' := by
        have e1 : (Quotient.mk _ (h • o.out) : O) = o := by
          conv_rhs => rw [← Quotient.out_eq o]
          exact Quotient.sound (MulAction.mem_orbit _ h)
        have e2 : (Quotient.mk _ (h' • o'.out) : O) = o' := by
          conv_rhs => rw [← Quotient.out_eq o']
          exact Quotient.sound (MulAction.mem_orbit _ h')
        rw [← e1, ← e2, he]
      subst ho
      have : (h'⁻¹ * h) • o.out = o.out := by rw [mul_smul, he, inv_smul_smul]
      have := hfree _ _ this
      rw [inv_mul_eq_one] at this
      rw [this]
    · intro x
      let o : O := Quotient.mk _ x
      have hrel : o.out ∈ MulAction.orbit H x := by
        have := Quotient.exact (Quotient.out_eq o)
        exact this
      obtain ⟨g, hg⟩ := hrel
      exact ⟨(g⁻¹, o), by simp only [β, ← hg, inv_smul_smul]⟩

  let n : ℕ := ∑ o : O, d o.out
  have hdimV : finrank K V = ∑ x, d x := by
    rw [Module.finrank_eq_card_basis (hA.collectedBasis fun x => Module.finBasis K (A x)), Fintype.card_sigma]
    simp [d]
  have hcount : n * Nat.card H = finrank K V := by
    rw [hdimV, ← hβ.sum_comp d, Fintype.sum_prod_type_right]
    simp only [β, hdeq, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, n, Finset.sum_mul]
    exact Finset.sum_congr rfl fun o _ => by ring

  let I := Σ o : O, Fin (d o.out)
  have hcard : Fintype.card I = n := by simp [I, Fintype.card_sigma, n]
  let e : Fin n ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  let b : ∀ o : O, Basis (Fin (d o.out)) K (A o.out) := fun o => Module.finBasis K (A o.out)
  let fo : I → V →ₗ[K] K := fun p => (b p.1).coord p.2 ∘ₗ comp p.1.out
  let T : (V →ₗ[K] K) → V →ₗ[K] MonoidAlgebra K H := fun f =>
    ∑ h : H, (f ∘ₗ ρ (h : Γ)⁻¹).smulRight (MonoidAlgebra.single h (1 : K))
  have hT : ∀ f v, T f v = ∑ h : H, f (ρ (h : Γ)⁻¹ v) • MonoidAlgebra.single h (1 : K) := by
    intro f v; simp [T]
  have hTc : ∀ f v (h : H), (T f v).coeff h = f (ρ (h : Γ)⁻¹ v) := by
    intro f v h
    rw [hT, MonoidAlgebra.coeff_sum]
    simp [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hTeq : ∀ f (g : H) v, T f (ρ g v) = MonoidAlgebra.single g 1 * T f v := by
    intro f g v
    rw [hT, hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => ?_
    simp only [Equiv.coe_mulLeft]
    rw [mul_smul_comm, MonoidAlgebra.single_mul_single, one_mul, mul_inv_cancel_left]
    have hc : ρ (h : Γ)⁻¹ (ρ g v) = ρ ((g⁻¹ * h : H) : Γ)⁻¹ v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp [mul_assoc]
    rw [hc]
  let j : V →ₗ[K] (Fin n → MonoidAlgebra K H) := LinearMap.pi fun k => T (fo (e k))
  refine ⟨n, ⟨j, ?_, ?_⟩, hcount⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hzero
    intro x
    obtain ⟨⟨h, o⟩, rfl⟩ := hβ.2 x
    have h1 : comp o.out (ρ (h : Γ)⁻¹ v) = 0 := by
      rw [← (b o).forall_coord_eq_zero_iff]
      intro i
      have hk : e (e.symm ⟨o, i⟩) = ⟨o, i⟩ := e.apply_symm_apply _
      have h5 : T (fo (e (e.symm ⟨o, i⟩))) v = 0 := congrFun hv (e.symm ⟨o, i⟩)
      rw [hk] at h5
      have h6 := congrArg (fun a => MonoidAlgebra.coeff a h) h5
      simp only [hTc] at h6
      simpa [fo] using h6
    have h2 := htr h⁻¹ (h • o.out) v
    rw [inv_smul_smul] at h2
    simp only [Subgroup.coe_inv] at h2
    rw [h1, Submodule.coe_zero] at h2
    have h3 := congrArg (ρ (h : Γ)) h2
    have h4 := hinv ((h : Γ)⁻¹) (comp (h • o.out) v : V)
    rw [inv_inv] at h4
    rw [map_zero, h4] at h3
    exact Subtype.ext h3.symm
  · intro h v i
    simp only [j, LinearMap.pi_apply]
    exact hTeq _ h v

end GlobalTheory.BadCount
