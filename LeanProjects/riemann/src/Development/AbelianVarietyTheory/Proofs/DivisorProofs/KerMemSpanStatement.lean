import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerMemSpan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUpdate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_data_local_identity_alt : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ χ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁), Rf.p' B.v₁ χ = 0 → χ ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ G.V' (GlobalTheory.AdelicU.evFin F B.v₁), ∃ φ ∈ G.M'.SoLoc B.ψ B.τ₁, ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), Acts (GlobalTheory.AdelicU.evFin F B.v₁) (om' (g, 1)) φ φ₁ ∧ z = φ₁ - φ} := by
  first | exact @GlobalTheory.KerSoLoc.ker_mem_span | exact GlobalTheory.KerSoLoc.ker_mem_span | (intros; apply GlobalTheory.KerSoLoc.ker_mem_span <;> assumption)
