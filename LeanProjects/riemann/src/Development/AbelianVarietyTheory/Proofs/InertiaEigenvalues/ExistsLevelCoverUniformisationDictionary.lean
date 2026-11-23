import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryInvariantRationalLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverUnif

set_option maxHeartbeats 1000000 in

theorem exists_unf_dict : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ,
    GoodEmb T.Q.c σ → ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (d : DeltaDat (T.Q.Xo j) c' 0) (σ₂ : d.c₂.F →+* ℂ),
    d.IsLev → d.l₂.A = 1 → σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF T.Q.c c' hle)) = σ →
    ∃ (U₂ : Unf d.Xo₂ d.c₂ σ₂ D.R.r) (dict₂ : GA D (T.V j σ) → Σ k, Frame (U₂.X k).Ψ D.R.r),
      ∀ cc₂, (⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩ : Cover T j σ).IsUnif := by
  intro D T hT j hj σ hσ c' hle d σ₂ hlev hA hinc
  obtain ⟨hr, -⟩ := hT.modelW j hj σ hσ
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj σ hσ _ rfl hr
  have hpq := (exists_iotaOK D T.Q hT.pins j hj).2
  have hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hg₂ : GoodEmb d.c₂ σ₂ := by
    have h1 := hσ
    rw [← hinc] at h1
    exact h1
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D T.Q.H (T.Q.Dw j) d.l₂ d.Xo₂ d.c₂ σ₂ (T.V j σ) D.R.r hr _ hio hpos hA
    hg₂).2.2 (T.x₀ j σ) hx₀
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D (T.V j σ) d.l₂.M).1
  obtain ⟨un, dict, mu, hdict, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1
    ⟨continuous_const, fun _ => rfl⟩ (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, -, hdl⟩ := hP.dictLaws
  have hdom := (dict_invariant D _ _ _ _ _ _ _ _ C hC dict hdict Kf hKf).2.2.1
  refine ⟨C.unf un, dict, fun cc₂ => ⟨hlev, hA, hinc, hP.unf, hdom, hr, g, e, F, ik, φ, th, hP.modelW, hth, ?_⟩⟩
  rw [← hCι, ← hCx]
  exact hdl

end GlobalTheory.CoverUnif
