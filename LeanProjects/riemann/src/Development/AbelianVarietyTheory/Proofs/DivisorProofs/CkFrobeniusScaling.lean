import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeFinitePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassPullbackFibreDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KillingElementPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassFrobeniusScalingStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

theorem GlobalTheory.MixedLocalChains.ck_frob : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P P' : Pres B) (g : Γ(B.X, ⊤)), IsRootOfP p g p → Kills g P.mod → IsFrob p P.mod P'.mod → ∀ k : ℕ, P'.ck p k = ((p : ℚ) ^ k) • P.ck p k := by
  intro O _ _ _ p _ _ _ B hB P P' g hg hK hF k
  obtain ⟨B', f, hB', hf0, hfl⟩ := GlobalTheory.T.normal_model_trivializing_blowup O p B hB 1 (fun _ => P.r) (fun _ => P.E)
    (fun _ => P.E') (fun _ => haveI := P.iso; Vert.Model.GenIso.ofHom P.ψ) (fun _ => ⟨P.vb, P.vb'⟩)
  have hfl' : (haveI := (P.pull f).iso;
      Nonempty (Vert.Model.FlagPair (Vert.Model.GenIso.ofHom (P.pull f).ψ) (P.pull f).r)) := by
    rw [Pres.ofHom_pull]; exact hfl 0
  have hg' : IsRootOfP p (f.f.appTop g) p := by
    obtain ⟨u, hu⟩ := hg
    exact ⟨Units.map f.f.appTop.hom.toMonoidHom u, by
      rw [← map_pow]
      simp [hu, map_mul, map_natCast]⟩
  have e4 := GlobalTheory.T.chern_class_frobenius_scaling O p B' hB' (P.pull f) (P'.pull f) (f.f.appTop g) hg'
    (GlobalTheory.T.killing_element_pullback O B B' f P g hK) (GlobalTheory.T.frobenius_lift_pullback O p B B' f P P' hF) hfl' k
  have hpos := (GlobalTheory.T.cap_degree_finite_pullback O p B hB B' f hf0).1
  refine LinearMap.ext fun Q => ?_
  have a := GlobalTheory.T.chern_class_pullback_fibre_degree O p B B' hB hB' f hf0 P k Q
  have b := GlobalTheory.T.chern_class_pullback_fibre_degree O p B B' hB hB' f hf0 P' k Q
  rw [e4, LinearMap.smul_apply, a] at b
  have hne : f.fibreDeg 1 ≠ 0 := hpos.ne'
  rw [LinearMap.smul_apply, smul_eq_mul]
  rw [smul_eq_mul] at b
  apply mul_left_cancel₀ hne
  linear_combination -b

end
