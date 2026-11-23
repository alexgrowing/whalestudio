import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneTupleRowsCuspFormsIsometricThetaLiftsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.RowsTies

theorem isQuotInt_zero {D : D7} (V : HSp D) (hV : V.SigOK) (c : ℝ) {φ : GA D V → ℂ} (h : ∀ g, φ g = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c φ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ, hμ, -⟩ := GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D V hV
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ.1
  have e : φ = fun _ => 0 := funext h
  subst e
  exact ⟨⟨(μ, 𝓕), ⟨hμ, h𝓕⟩⟩, fun m _ => ⟨integrableOn_zero, by simp⟩⟩

theorem rows_of_ties : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) → (∀ μ, (xi μ).TrivOn D.host.F) → (∀ μ ∈ U, R.xiH (tupT μ) = xi μ ∧ (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1)) → (∀ μ, μ ∉ U → ∀ j, j < D.R.m → D.what₂.io μ j = 0) → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs R.C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) := by
  intro hD D G _ _ Pl0 T A Ks _ _ _ R hL hM hC xi U tupT hf ht hU hoff θ hθ ψ hψ Wf
  obtain rfl : θ = R.θ := (GlobalTheory.Mem.InfFamUnique.existsUnique_infFam D).unique hθ hM.inf
  obtain rfl : ψ = R.ψ := (GlobalTheory.StdAdelicChar.existsUnique_isStdChar D (-1) (Or.inr rfl)).unique hψ (hC.ωX A.μ0).std
  obtain ⟨Rc, hR⟩ := RecFun.exists_chrIs R.C xi hf ht R.θ R.ψ
  have hu := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1
  have he : Rc.eta = R.eta := hu _ _ _ hR.eta hL.eta
  have key : ∀ μ, ∃ (row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j)) (Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j)),
      (∀ j, j < D.R.m → Phi j ≠ 0) ∧
      (μ ∈ U → ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j,
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
          (fun h => star ((row j x).1 h) * (row j y).1 h) (inner ℂ x y)) ∧
      ∀ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ,
        (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (Rc.mY μ (j + 1) * Rc.petC (D.sp.Y (j + 1)))
          (fun h => Wf.ker _ _ (Rc.carY μ (j + 1) (j + 1)) (Rc.carY μ (j + 1) j) (Phi j) h g *
            (row (j + 1) y).1 h) (L g)) ∧
        ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
          (fun g => star (L g) * (row j x).1 g) (inner ℂ (D.what₂.io μ j y) x) := fun μ => by
    by_cases hμ : μ ∈ U
    · obtain ⟨hx, hT⟩ := hU μ hμ
      have hc : ∀ j, j < D.R.m → Rc.chr μ (j + 1) = R.toLevCh.mu (tupT μ) (j + 1) := fun j hj =>
        hu _ _ _ (hR.chr μ ⟨j, hj⟩) (hx ▸ GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 ⟨j, hj⟩) (hL.xi (tupT μ)))
      obtain ⟨row, Phi, h1, h2, h3⟩ := GlobalTheory.T.oneTuple_rows_cuspForms_isometric_thetaLifts hD D G Pl0 T A Ks R hL hM hC (tupT μ) μ hT Wf
        (fun j => Rc.mY μ j * Rc.petC (D.sp.Y j)) fun j =>
          mul_pos (Rc.mY_pos _ _) (mul_pos (Rc.petF_pos _) (Finset.prod_pos fun _ _ => Rc.meas.petR_pos _ _))
      refine ⟨row, Phi, h1, fun _ => h2, fun j hj y => ?_⟩
      unfold RecFun.carY
      rw [hc j hj, he]
      exact h3 j hj y
    · refine ⟨0, Rc.Phi μ, Rc.Phi_ne hψ μ, fun h => absurd h hμ, fun j hj y => ⟨0, fun g => ?_, fun x => ?_⟩⟩
      · exact isQuotInt_zero _ (D.sp.Y_sig _) _ fun h => by simp
      · rw [hoff μ hμ j hj]
        simpa using isQuotInt_zero _ (D.sp.Y_sig _) _ fun h => by simp
  choose row Phi h1 h2 h3 using key
  exact ⟨{ Rc with row := row, Phi := Phi, Phi_ne := fun _ => h1 }, ⟨hR.chr, hR.eta⟩, h3, h2⟩

end GlobalTheory.Mem.RowsTies
