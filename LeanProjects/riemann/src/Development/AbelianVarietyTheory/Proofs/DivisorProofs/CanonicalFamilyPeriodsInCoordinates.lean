import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GensOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLawsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.PerCoord

theorem comp_C_injective {W R σ : Type} [CommRing W] [IsLocalRing W] [CommRing R] [IsLocalRing R]
    (ψ : MvPolynomial σ W →+* R) (hf : ψ.Flat) (hl : IsLocalHom (ψ.comp MvPolynomial.C)) :
    Function.Injective (ψ.comp MvPolynomial.C) := by
  have hC : (MvPolynomial.C : W →+* MvPolynomial σ W).Flat := by
    show (algebraMap W (MvPolynomial σ W)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have h := RingHom.Flat.comp hC hf
  letI := (ψ.comp MvPolynomial.C).toAlgebra
  haveI : Module.Flat W R := h
  haveI : IsLocalHom (algebraMap W R) := hl
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := W) (B := R)
  exact FaithfulSMul.algebraMap_injective W R

theorem prod_zpow_add {K Ix : Type} [Field K] [Fintype Ix] (c : Ix → K) (hc : ∀ k, c k ≠ 0) (A B C D : Ix → ℤ)
    (h : ∀ k, A k = D k + B k + C k) :
    ∏ k, c k ^ A k = (∏ k, c k ^ D k) * (∏ k, c k ^ B k) * ∏ k, c k ^ C k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h k, zpow_add₀ (hc k), zpow_add₀ (hc k)]

end GlobalTheory.UCanon.PerCoord

namespace GlobalTheory.UCanon.PerCoord

theorem second_diff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X Y : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] (e : X ≃ₗ[𝓞 E] Y) {β : LinearMap.BilinForm ℤ Y}
    (hβ : β ∈ balForms H.bar Y) (a b : X) :
    β (e (a + b)) (H.w0 • e (a + b)) = β (e a) (e b) + β (e a) (H.w0 • e a) + β (e b) (H.w0 • e b) := by
  have h1 : β (e b) (H.w0 • e a) = β (e a) (H.bar H.w0 • e b) := (hβ.1 _ _).trans (hβ.2 _ _ _)
  have h2 : β (e a) (H.w0 • e b) + β (e a) (H.bar H.w0 • e b) = β (e a) (e b) := by
    rw [← map_add, ← add_smul, ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one, one_smul]
  simp only [map_add, smul_add, LinearMap.add_apply]
  rw [h1]
  linarith

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∃ (ε' : Module.Basis (Fin C.m ⊕ Fin Cn.N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre), (∀ k, (ε' k : LinearMap.BilinForm ℤ C.P.D.toPre.X) = pull Cn.e.toLinearMap (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) ∧ FromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) ∧ TauIn C.P.D.toPre τ₀ (fun k => Cn.ψ (MvPolynomial.X (finSumFinEquiv.symm k))) (fun k => (l.M' : ℤ) • (ε' (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C Cn
  classical
  obtain ⟨g, hD, hg, -, -⟩ := Cn.data
  have hinj := comp_C_injective Cn.ψ Cn.compl.2.2.1 Cn.ψ_loc
  obtain ⟨-, hb, hU, -⟩ := letI := H.starRing
    GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws Cn.L.W Cn.L.D (𝓞 E) Cn.L.oa H.w0 l.M' Cn.L.even Cn.L.bimult Cn.L.w0 Cn.L.gen
  obtain ⟨τ₁, hτ, hF⟩ := GlobalTheory.UTautData.gens_fromBase _ hinj _ _ hD hb hU
  refine ⟨Cn.ε.map (pullBalEquiv H.bar Cn.e), τ₁, fun k => rfl, hF, fun a b => ?_⟩
  have hs : ∀ k, algebraMap R (FractionRing R) (Cn.ψ (MvPolynomial.X k)) ≠ 0 := by
    intro k
    refine (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 ?_
    rcases k with i | k
    · rw [Cn.bd i]; exact C.s_ne_zero i
    · exact (Cn.tor k).ne_zero
  refine ⟨(hτ a b).1, g a * g b * (g (a + b))⁻¹, ?_, fun z J hJ => ?_⟩
  · have hsplit := prod_zpow_add _ hs
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e (a + b)) (H.w0 • Cn.e (a + b)))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e a) (H.w0 • Cn.e a))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e b) (H.w0 • Cn.e b))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e a) (Cn.e b))
      (fun k => by simp only [second_diff H Cn.e (Cn.ε k).2 a b]; ring)
    have hne : ∀ y, (((g y)⁻¹ : (FractionRing R)ˣ) : FractionRing R) ≠ 0 := fun y => Units.ne_zero _
    have e1 : (((g a * g b * (g (a + b))⁻¹ : (FractionRing R)ˣ)) : FractionRing R) =
        (((g (a + b))⁻¹ : (FractionRing R)ˣ) : FractionRing R) * ((((g a)⁻¹ : (FractionRing R)ˣ) : FractionRing R))⁻¹ *
          ((((g b)⁻¹ : (FractionRing R)ˣ) : FractionRing R))⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, inv_inv]; ring
    have hA := hne a
    have hB := hne b
    rw [hg a] at hA
    rw [hg b] at hB
    rw [e1, hg (a + b), hsplit, hg a, hg b]
    beta_reduce at hA hB ⊢
    have canc : ∀ T x y : FractionRing R, x ≠ 0 → y ≠ 0 → T * x * y * x⁻¹ * y⁻¹ = T := fun T x y hx hy => by
      field_simp
    rw [canc _ _ _ hA hB]
    refine Eq.trans ?_ (Equiv.prod_comp finSumFinEquiv.symm (fun k => algebraMap R (FractionRing R)
      (Cn.ψ (MvPolynomial.X k)) ^ (((l.M' : ℤ) • ((Cn.ε.map (pullBalEquiv H.bar Cn.e)) k :
        LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b))).symm
    exact Finset.prod_congr rfl fun k _ => rfl
  · have h1 := GlobalTheory.TauTwist.val_tau_rescale (D := C.P.D.toPre) g (a := a) (b := b)
      (x := (g a * g b)⁻¹ * g (a + b)) (by group) (𝟙 _) hJ
    have h2 := (hτ a b).2 z J hJ
    have hx : g a * g b * (g (a + b))⁻¹ = ((g a * g b)⁻¹ * g (a + b))⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [hx]
    show _ = GlobalTheory.TauTwist.unitAt (𝟙 _) z _ * _
    rw [map_inv]
    exact eq_inv_mul_of_mul_eq (h1.symm.trans h2)

end GlobalTheory.UCanon.PerCoord
