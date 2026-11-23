import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilTraceEqOfSameWd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_trace_eq_of_same_wd : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r r' : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (x : WD h), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → IsWDOf ι r x → IsWDOf ι r' x → ∀ σ : Weil h, (r (σ : G E Ω)).val.trace = (r' (σ : G E Ω)).val.trace := by
  first | exact @GlobalTheory.WdTrace.trace_eq_of_isWDOf | exact GlobalTheory.WdTrace.trace_eq_of_isWDOf | (intros; apply GlobalTheory.WdTrace.trace_eq_of_isWDOf <;> assumption)
