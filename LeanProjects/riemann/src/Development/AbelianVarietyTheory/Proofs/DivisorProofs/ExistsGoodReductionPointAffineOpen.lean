import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityCriterionNormalModel
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TrueGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase.CentrePt

open GlobalTheory.TrueGeo.HorizPt in

theorem exists_centre_pt : ∀ {F : Type} [Field F] [NumberField F] {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {s : W ⟶ Sp F} {jB : W ⟶ X} {d : ℕ},
    IsArithVar q d → IsPullback jB s q (spMap (algebraMap (𝓞 F) F)) → ∀ (V : X.Opens), IsAffineOpen V → ∀ x₀ ∈ V,
    ∃ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (xg : Sp (AlgebraicClosure F) ⟶ W)
      (xt : Sp ε.O ⟶ X) (ht : ⊤ ≤ xt ⁻¹ᵁ V), xg ≫ s = spMap (algebraMap F (AlgebraicClosure F)) ∧
      spMap ε.O.subtype ≫ xt = xg ≫ jB ∧ ∀ f : Γ(X, V), IsUnit (TangentOrigin.evalPt xt V ht f) → x₀ ∈ X.basicOpen f := by
  intro F _ _ X W q s jB d hq pb U hU z hzU
  have := hq.isIntegral
  have := hq.flat
  have : IsProper q := by
    obtain ⟨n, c, hc, h⟩ := hq.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(X, U) := charZero (q ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(X, U) := (GlobalTheory.TrueGeo.HorizPt.strHom q U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(X, U) :=
    RingHom.FiniteType.comp (q.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, -⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(X, U) 𝔪 h𝔪 1 one_ne_zero
  let yt : Sp e.O ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ q =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := pb.lift_fst _ _ hw
  have ht : ⊤ ≤ yt ⁻¹ᵁ U := fun x _ => (Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩
  have hev : TangentOrigin.evalPt yt U ht = φ := by
    have := TangentOrigin.eq_spec_fromSpec hU yt ht
    simp only [yt] at this
    rw [cancel_mono] at this
    have := Spec.map_injective this
    exact (congrArg CommRingCat.Hom.hom this).symm
  refine ⟨v, e, pb.lift _ _ hw, yt, ht, pb.lift_snd _ _ hw, hy.symm, fun f hf => ?_⟩
  rw [hev] at hf
  have hn : f ∉ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := fun h => by
    have := hle' h
    rw [← h₂] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this hf
  have h₃ : hU.fromSpec (hU.primeIdealOf ⟨z, hzU⟩) ∈ X.basicOpen f := by
    change _ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f
    rw [hU.fromSpec_preimage_basicOpen]
    exact hn
  rwa [hU.fromSpec_primeIdealOf] at h₃

end GlobalTheory.ArLieBase.CentrePt
