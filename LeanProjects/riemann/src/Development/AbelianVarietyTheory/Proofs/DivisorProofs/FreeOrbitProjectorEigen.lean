import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory

theorem freeOrbit_projector_eigen : ∀ (K V G C : Type) [Field K] [AddCommGroup V] [Module K V] [Group G] [Fintype G] [Fintype C] [MulAction G C] (e : C → V →ₗ[K] V) (ρ : Representation K G V) (χ : G →* Kˣ), (∀ (g : G) (Z : C), g • Z = Z → g = 1) → (∀ Z v, e Z (e Z v) = e Z v) → (∀ Z Z' v, Z ≠ Z' → e Z (e Z' v) = 0) → (∀ v, ∑ Z, e Z v = v) → (∀ g Z v, ρ g (e Z v) = e (g • Z) (ρ g v)) → ∃ O : Finset C, (∀ Z, ∃ g : G, ∃ o ∈ O, Z = g • o) ∧ (∀ F, (∀ g, ρ g F = (χ g : K) • F) → F = ∑ o ∈ O, ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (e o F)) ∧ ∀ f : C → V, (∀ o, e o (f o) = f o) → (∀ h, ρ h (∑ o ∈ O, ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (f o)) = (χ h : K) • ∑ o ∈ O, ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (f o)) ∧ ∀ g, ∀ o ∈ O, e (g • o) (∑ o' ∈ O, ∑ g', ((χ g')⁻¹ : Kˣ) • ρ g' (f o')) = ((χ g)⁻¹ : Kˣ) • ρ g (f o) := by
  intro K V G C _ _ _ _ _ _ _ e ρ χ hfree hidem horth hsum1 hequi
  classical
  let O : Finset C := Finset.univ.image (fun Z : C => (Quotient.mk (MulAction.orbitRel G C) Z).out)
  have hq : ∀ (g : G) (x : C), Quotient.mk (MulAction.orbitRel G C) (g • x) = Quotient.mk (MulAction.orbitRel G C) x :=
    fun g x => Quotient.sound (MulAction.mem_orbit x g)
  have hinj : ∀ (g : G) (o : C) (g' : G) (o' : C), o ∈ O → o' ∈ O → g • o = g' • o' → g = g' ∧ o = o' := by
    intro g o g' o' ho ho' h
    obtain ⟨Z1, -, rfl⟩ := Finset.mem_image.1 ho
    obtain ⟨Z2, -, rfl⟩ := Finset.mem_image.1 ho'
    have hZ : Quotient.mk (MulAction.orbitRel G C) Z1 = Quotient.mk (MulAction.orbitRel G C) Z2 := by
      calc Quotient.mk (MulAction.orbitRel G C) Z1
          = Quotient.mk (MulAction.orbitRel G C) (Quotient.mk (MulAction.orbitRel G C) Z1).out := (Quotient.out_eq _).symm
        _ = Quotient.mk (MulAction.orbitRel G C) (g • (Quotient.mk (MulAction.orbitRel G C) Z1).out) := (hq g _).symm
        _ = Quotient.mk (MulAction.orbitRel G C) (g' • (Quotient.mk (MulAction.orbitRel G C) Z2).out) := by rw [h]
        _ = Quotient.mk (MulAction.orbitRel G C) (Quotient.mk (MulAction.orbitRel G C) Z2).out := hq g' _
        _ = Quotient.mk (MulAction.orbitRel G C) Z2 := Quotient.out_eq _
    rw [hZ] at h ⊢
    refine ⟨?_, rfl⟩
    have h2 : (g'⁻¹ * g) • (Quotient.mk (MulAction.orbitRel G C) Z2).out = (Quotient.mk (MulAction.orbitRel G C) Z2).out := by
      rw [mul_smul, h, inv_smul_smul]
    have := hfree _ _ h2
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hsurj : ∀ Z, ∃ g : G, ∃ o ∈ O, Z = g • o := by
    intro Z
    have hm : (Quotient.mk (MulAction.orbitRel G C) Z).out ∈ MulAction.orbit G Z := @Quotient.mk_out _ (MulAction.orbitRel G C) Z
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hm
    exact ⟨g⁻¹, _, Finset.mem_image_of_mem _ (Finset.mem_univ Z), by rw [← hg, inv_smul_smul]⟩
  have hsum : ∀ φ : C → V, ∑ Z, φ Z = ∑ o ∈ O, ∑ g : G, φ (g • o) := by
    intro φ
    rw [← Finset.sum_product (s := O) (t := Finset.univ) (f := fun x : C × G => φ (x.2 • x.1))]
    symm
    refine Finset.sum_bij (fun x _ => x.2 • x.1) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨o, g⟩ h ⟨o', g'⟩ h' he
      simp only [Finset.mem_product] at h h'
      obtain ⟨h1, h2⟩ := hinj g o g' o' h.1 h'.1 he
      simp [h1, h2]
    · intro Z _
      obtain ⟨g, o, ho, rfl⟩ := hsurj Z
      exact ⟨(o, g), Finset.mem_product.2 ⟨ho, Finset.mem_univ _⟩, rfl⟩
  refine ⟨O, hsurj, ?_, ?_⟩
  · intro F hF
    conv_lhs => rw [← hsum1 F, hsum (fun Z => e Z F)]
    refine Finset.sum_congr rfl (fun o _ => Finset.sum_congr rfl (fun g _ => ?_))
    rw [hequi, hF, LinearMap.map_smul, ← Units.smul_def, inv_smul_smul]
  · intro f hf
    refine ⟨?_, ?_⟩
    · intro h
      simp only [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun o _ => ?_)
      refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
      simp only [Equiv.coe_mulLeft]
      rw [Units.smul_def, Units.smul_def, LinearMap.map_smul, map_mul, map_mul, Module.End.mul_apply, smul_smul]
      congr 1
      rw [← Units.val_mul]
      congr 1
      rw [mul_inv_rev, mul_comm, mul_assoc, inv_mul_cancel, mul_one]
    · intro g o ho
      have key : ∀ o' ∈ O, ∀ g', e (g • o) (((χ g')⁻¹ : Kˣ) • ρ g' (f o')) =
          if g' = g ∧ o' = o then ((χ g)⁻¹ : Kˣ) • ρ g (f o) else 0 := by
        intro o' ho' g'
        have hw : ρ g' (f o') = e (g' • o') (ρ g' (f o')) := by rw [← hequi g' o' (f o'), hf o']
        split_ifs with hc
        · obtain ⟨rfl, rfl⟩ := hc
          rw [Units.smul_def, LinearMap.map_smul]
          congr 1
          rw [hw, hidem]
        · rw [Units.smul_def, LinearMap.map_smul, hw, horth, smul_zero]
          intro hZ
          obtain ⟨h1, h2⟩ := hinj g o g' o' ho ho' hZ
          exact hc ⟨h1.symm, h2.symm⟩
      rw [map_sum, Finset.sum_eq_single_of_mem o ho]
      · rw [map_sum, Fintype.sum_eq_single g]
        · rw [key o ho g, if_pos ⟨rfl, rfl⟩]
        · intro g' hg'
          rw [key o ho g', if_neg (fun h => hg' h.1)]
      · intro o' ho' hne
        rw [map_sum]
        refine Finset.sum_eq_zero (fun g' _ => ?_)
        rw [key o' ho' g', if_neg (fun h => hne h.2)]

end GlobalTheory
