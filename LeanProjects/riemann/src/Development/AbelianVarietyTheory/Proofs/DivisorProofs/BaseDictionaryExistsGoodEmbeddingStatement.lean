import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseDictionaryExistsGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_dictionary_exists_good_embedding : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ θ : InfFam D, IsInfFam θ → ∃ (hr : (T.V j σ).rank = D.R.r) (x₀ : D.what₂.Tau → Matrix (Fin (T.V j σ).rank) (Fin (T.V j σ).rank) ℂ), BaseDict θ (T.V j σ) hr (T.U j σ).X (T.dict j σ) (T.Kf j σ) x₀ := by
  first | exact @GlobalTheory.HolRead.baseDict_core | exact GlobalTheory.HolRead.baseDict_core | (intros; apply GlobalTheory.HolRead.baseDict_core <;> assumption)
