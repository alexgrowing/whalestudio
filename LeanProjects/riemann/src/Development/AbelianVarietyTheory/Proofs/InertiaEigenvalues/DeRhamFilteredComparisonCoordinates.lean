import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.DRFilCoord
open Module

theorem deRham_filtered_Ql (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (TT : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) (hdR : IsDR (P.PD K) ρ) (a : ℤ) (y : V ⊗[ℚ_[l]] P.R.BdR)
    (hy : y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a) :
    ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR),
      (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) (k i) ∧
        b i ∈ (P.PD K).Fil (a - k i)) ∧
      y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : ↥LL.1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module ↥LL.1 V := Module.compHom V (e : ↥LL.1 →+* ℚ_[l])
  haveI : IsScalarTower ℚ_[l] ↥LL.1 V := ⟨fun c x v => by
    show e (c • x) • v = c • (e x • v)
    have h1 := e.toLinearEquiv.map_smul c x
    simp only [AlgEquiv.toLinearEquiv_apply] at h1
    rw [h1, smul_eq_mul, mul_smul]⟩
  haveI : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] _ V
  let ρ' : Representation ↥LL.1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := fun u w => (ρ g).map_add u w
          map_smul' := fun c v => (ρ g).map_smul (e c) v }
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp; rfl }
  have hV : finrank ↥LL.1 V = finrank ℚ_[l] V := by
    rw [← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V, IntermediateField.finrank_bot, one_mul]
  have hR : ∀ g x, actVdR (P.PD K) ρ' g x = actVdR (P.PD K) ρ g x := fun g x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [actVdR]; rfl
    | add u w hu hw => simp only [map_add, hu, hw]
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ' ↔ x ∈ DdR (P.PD K) ρ := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hR]
  have hDd : (DdR (P.PD K) ρ').restrictScalars ℚ_[l] = DdR (P.PD K) ρ := by
    ext x
    rw [Submodule.restrictScalars_mem, hD]
  have hDr : finrank ↥LL.1 ↥(DdR (P.PD K) ρ') = finrank ℚ_[l] ↥(DdR (P.PD K) ρ) := by
    rw [← hDd, LinearEquiv.finrank_eq
      ((Submodule.restrictScalarsEquiv ℚ_[l] ↥LL.1 _ (DdR (P.PD K) ρ')).restrictScalars ℚ_[l]),
      ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 ↥(DdR (P.PD K) ρ'), IntermediateField.finrank_bot, one_mul]
  have hDR' : IsDR (P.PD K) ρ' := by
    unfold IsDR at hdR ⊢
    rw [hDr, hV]; exact hdR
  obtain ⟨m, k, b, d, h, hy'⟩ := GlobalTheory.DRFil.deRham_filtered l P AI TT K LL V ρ' hDR' a y hy
  exact ⟨m, k, b, d, fun i => ⟨(hD _).1 (h i).1, (h i).2.1, (h i).2.2⟩, hy'⟩

theorem filtered_coords : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ i, y i ∈ (P.PD K).Fil a) → ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (z : Fin m → Fin d → P.R.BdR), (∀ r, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (z r i)) = z r) ∧ (∀ i, z r i ∈ (P.PD K).Fil (k r)) ∧ b r ∈ (P.PD K).Fil (a - k r)) ∧ y = ∑ r, b r • z r := by
  intro l _ P AI TT K d ρ hdR a y hy
  let f : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin d → P.R.BdR) :=
    (TensorProduct.piScalarRight ℚ_[l] ℚ_[l] P.R.BdR (Fin d)).toLinearMap ∘ₗ
      (TensorProduct.comm ℚ_[l] (Fin d → ℚ_[l]) P.R.BdR).toLinearMap
  have hf : ∀ (v : Fin d → ℚ_[l]) (β : P.R.BdR), f (v ⊗ₜ β) = fun i => v i • β := by
    intro v β; simp [f]
  have hfmul : ∀ (β : P.R.BdR) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      f (AlgebraTensorModule.map (LinearMap.id : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin d → ℚ_[l]))
        (LinearMap.mulLeft ℚ_[l] β) x) = β • f x := by
    intro β x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply, hf]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      ring
    | add u w hu hw => simp only [map_add, hu, hw, smul_add]
  have hfil : ∀ (c : ℤ) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      x ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) c → ∀ i, f x i ∈ (P.PD K).Fil c := by
    intro c x hx i
    refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun x => f x i ∈ (P.PD K).Fil c) ?_ ?_ ?_ hx
    · simp
    · intro v β hβ
      rw [hf]
      exact (((P.PD K).Fil c).restrictScalars ℚ_[l]).smul_mem (v i) hβ
    · intro x x' h h'
      rw [map_add]
      exact Submodule.add_mem _ h h'
  have hact : ∀ (g : ↥(GK K)) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      f (actVdR (P.PD K) (qRep ρ) g x) =
        (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ
          (fun i => P.actQdR (g : GQ l) (f x i)) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]; exact (Matrix.mulVec_zero _).symm
    | tmul v β =>
      have h1 : actVdR (P.PD K) (qRep ρ) g (v ⊗ₜ β) = qRep ρ g v ⊗ₜ P.actQdR (g : GQ l) β := by
        simp [actVdR, P.PD_actdR]
      rw [h1, hf, hf]
      funext i
      have hq : qRep ρ g v = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v := by
        simp [qRep, Matrix.toLin'_apply]
      rw [hq]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
      rfl
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, ← Matrix.mulVec_add]
      congr 1; funext i; simp
  let x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR := ∑ i, Pi.single i (1 : ℚ_[l]) ⊗ₜ y i
  have hx : x ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) a :=
    Submodule.sum_mem _ fun i _ => GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) (LL := ℚ_[l]) _ (hy i)
  have hfx : f x = y := by
    funext j
    simp [x, map_sum, hf, Pi.single_apply]
  obtain ⟨m, k, b, dd, h, e⟩ :=
    deRham_filtered_Ql l P AI TT K (Fin d → ℚ_[l]) (qRep ρ) hdR a x hx
  refine ⟨m, k, b, fun r => f (dd r), fun r => ⟨fun g => ?_, hfil _ _ (h r).2.1, (h r).2.2⟩, ?_⟩
  · have hg : actVdR (P.PD K) (qRep ρ) g (dd r) = dd r :=
      (GlobalTheory.DRFil.mem_DdR (P.PD K) (qRep ρ) _).1 (h r).1 g
    rw [← hact, hg]
  · rw [← hfx, e, map_sum]
    exact Finset.sum_congr rfl fun r _ => hfmul _ _

end GlobalTheory.DRFilCoord
