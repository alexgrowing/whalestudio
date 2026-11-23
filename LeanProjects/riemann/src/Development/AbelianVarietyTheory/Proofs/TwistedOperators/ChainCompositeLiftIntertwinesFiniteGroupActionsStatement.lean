import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainCompositeLift_intertwines_finiteGroupActions : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → (∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j)) → ∀ t g κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ → ∀ y y' : (R.HX t).H, (∀ h, (R.HX t).e y' h = (levChi _ R.βX (flagL (R.datXt t)) κ)⁻¹ • (R.HX t).e y (h * (finHom _).rangeRestrict κ)) → R.Th t y' = R.gE g (R.Th t y) := by
  first | exact @GlobalTheory.ChainLiftEquiv.th_intertwines | exact GlobalTheory.ChainLiftEquiv.th_intertwines | (intros; apply GlobalTheory.ChainLiftEquiv.th_intertwines <;> assumption)
