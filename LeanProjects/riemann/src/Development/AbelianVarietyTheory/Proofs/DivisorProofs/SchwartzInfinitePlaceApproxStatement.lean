import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInfinitePlaceApprox
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_infinite_place_approx : KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ h ∈ UAt σ G.W (evI F), ∀ f : SInf F (Fin a' × Fin (a + a')), ∃ u : SInf F (Fin a' × Fin (a + a')), ∀ g ∈ SB (Fin a' × Fin (a + a') → Af F), om' (1, h) (pureA F f g) = pureA F u g := by
  first | exact @GlobalTheory.ArchFactorFin.arch_factor | exact GlobalTheory.ArchFactorFin.arch_factor | (intros; apply GlobalTheory.ArchFactorFin.arch_factor <;> assumption)
