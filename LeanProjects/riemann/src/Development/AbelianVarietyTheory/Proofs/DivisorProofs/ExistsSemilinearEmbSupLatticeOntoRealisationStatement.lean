import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisation
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_emb_supLattice_onto_realisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), ∃ ι : VK fw i →ₛₗ[algebraMap T.Q.c.F D.what₂.LL] (Fin (R.nW i) → D.what₂.LL), (∀ (f : VK fw i), ∃ h : (f : T.R ((i : ℕ) + 1)) ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ι f = ((fw.e i ⟨f, h⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) ∧ (∀ (n : ℕ) (b : Fin n → VK fw i), LinearIndependent T.Q.c.F b → LinearIndependent D.what₂.LL (fun k => ι (b k))) ∧ ι '' (latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) : Set (VK fw i)) = ((R.FW i).MK : Set (Fin (R.nW i) → D.what₂.LL)) := by
  first | exact @GlobalTheory.CovTop.SupImage.exists_emb_image_latW | exact GlobalTheory.CovTop.SupImage.exists_emb_image_latW | (intros; apply GlobalTheory.CovTop.SupImage.exists_emb_image_latW <;> assumption)
