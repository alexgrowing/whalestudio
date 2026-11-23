import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnitStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStableStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponentStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplitStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroupStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem frame_rmul_lact {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (γ : GL (Fin r) E) (x b : Frame Ψ r) : rmul (lact γ x) b = lact γ (rmul x b) := by
  funext τ
  exact Matrix.mul_assoc (α := ℂ) _ (mat x τ) (mat b τ)

theorem dict_eq_of_mark (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r) (hC : C.OK)
    (dict : GA D V → Σ k, Frame (C.M.X k).Ψ r) (hd : C.IsDict dict) (g : GA D V) (k : Fin C.F.n)
    (γ : GA D V) (hm : C.Mark g k γ) :
    ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
  obtain ⟨γ', hm', he⟩ := hd.1 g
  have hu := GlobalTheory.T.marking_component_unique_frame_unique_arithmeticGroup D H Dw l Xo c σ V r C hC g
  have hk : k = (dict g).1 := hu.1 _ _ _ _ hm hm'
  subst hk
  obtain ⟨δ, hδ, e⟩ := hu.2 _ _ _ hm hm'
  refine ⟨δ, hδ, ?_⟩
  rw [← e, ← he]

theorem dict_real_equivariant_onto : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V C.th C.hr (fun k => C.fr 1 k) h (dict g).1))⟩) ∧ ∀ k, ∀ x ∈ (C.M.X k).dom, ∃ g, ∃ γ ∈ (C.M.X k).Γ, ∃ b ∈ Bor (C.M.X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩ := by
  intro D H Dw l Xo c σ V r C hC dict hd
  refine ⟨fun g h hh => ?_, fun k x hx => ?_⟩
  · obtain ⟨γ, hm, he⟩ := hd.1 g
    have hm2 := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g _ γ hm).2.2.1 h hh
    obtain ⟨δ, hδ, e⟩ := dict_eq_of_mark D H Dw l Xo c σ V r C hC dict hd (g * h) _ γ hm2
    refine ⟨δ, hδ, ?_⟩
    rw [e, ← mul_assoc, (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC (γ * g) _).2.2.2.2.2.1 h, ← he]
  · obtain ⟨x₀, b, hb, ho, hx₀⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E r
      (C.M.X k).p0 (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm).1 x hx
    obtain ⟨u, hu, hux⟩ := (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.2.2.2.2.2 x₀ ho
    obtain ⟨f, hf, hm⟩ := GlobalTheory.T.exists_finiteAdelic_element_marking_component D H Dw l Xo c σ V r C hC k
    have hm2 := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC f k 1 hm).2.2.1 u hu
    obtain ⟨δ, hδ, e⟩ := dict_eq_of_mark D H Dw l Xo c σ V r C hC dict hd (f * u) k 1 hm2
    refine ⟨f * u, δ, hδ, b, hb, ?_⟩
    rw [e, one_mul, ← (GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split D V).2.1 u hu f hf,
      (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC u k).2.2.2.2.1 f hf, hux, hx₀, frame_rmul_lact]

end GlobalTheory.Member
