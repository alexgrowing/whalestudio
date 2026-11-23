import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActEquivSymmApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCuspStab

open GlobalTheory.MixModel GlobalTheory.RallisCusp

variable {D : D7}

theorem inv_fix {n s : ℕ} (A B : Matrix (Fin n) (Fin n) (AE D)) (M : Matrix (Fin n) (Fin s) (AE D))
    (hBA : B * A = 1) (h : A ⬝ M = M) : B ⬝ M = M := by
  calc B ⬝ M = B ⬝ (A ⬝ M) := by rw [h]
    _ = M := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]

theorem inv_sub_one {n : ℕ} (A B : Matrix (Fin n) (Fin n) (AE D)) (hBA : B * A = 1) : B - 1 = -(B * (A - 1)) := by
  rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]

set_option maxHeartbeats 1000000 in

theorem ni_prop (W : HSp D) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E) (g : GA D W) (hg : g ∈ NI W I) :
    Formalism.L2.Theta.mt W g ⬝ I.map (incA D) = I.map (incA D) ∧
    ∀ x : Fin W.rank → D.host.E, (Iᴴ * W.gram) *ᵥ x = 0 →
      ∃ a : Fin s → AE D, (Formalism.L2.Theta.mt W g - 1) *ᵥ (fun i => incA D (x i)) = I.map (incA D) *ᵥ a := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    refine ⟨?_, fun x hx => hg.2.2 x hx⟩
    have h1 : (Formalism.L2.Theta.mt W g - 1) ⬝ I.map (incA D) = 0 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    exact h1
  | one =>
    refine ⟨by rw [GlobalTheory.MixModel.mt_one, Matrix.one_mul], fun x _ => ⟨0, ?_⟩⟩
    rw [GlobalTheory.MixModel.mt_one, sub_self, Matrix.zero_mulVec, Matrix.mulVec_zero]
  | mul x y _ _ hx hy =>
    refine ⟨by rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, hy.1, hx.1], fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hx.2 v hv
    obtain ⟨b, hb⟩ := hy.2 v hv
    refine ⟨b + a, ?_⟩
    have e : Formalism.L2.Theta.mt W (x * y) - 1 =
        Formalism.L2.Theta.mt W x * (Formalism.L2.Theta.mt W y - 1) + (Formalism.L2.Theta.mt W x - 1) := by
      rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
    rw [e, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hb, ha, Matrix.mulVec_mulVec, hx.1, Matrix.mulVec_add]
  | inv x _ hx =>
    obtain ⟨hx1, hx2⟩ := hx
    have hinv := inv_fix _ _ _ (GlobalTheory.MixModel.mt_inv_mul W x) hx1
    refine ⟨hinv, fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hx2 v hv
    refine ⟨-a, ?_⟩
    rw [inv_sub_one _ _ (GlobalTheory.MixModel.mt_inv_mul W x), Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, hinv, Matrix.mulVec_neg]

theorem exists_leftInv {m s : ℕ} (I : Matrix (Fin m) (Fin s) D.host.E) (hI : LinearIndependent D.host.E I.transpose) :
    ∃ L : Matrix (Fin s) (Fin m) D.host.E, L * I = 1 := by
  have hB : Function.Injective I.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    exact hI
  have hker : LinearMap.ker (Matrix.toLin' I) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    exact hB (by simpa [Matrix.toLin'_apply] using h)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' I) hker
  exact ⟨LinearMap.toMatrix' g, by
    rw [← LinearMap.toMatrix'_toLin' I, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]⟩

theorem descend {m s : ℕ} (I : Matrix (Fin m) (Fin s) D.host.E) (hI : LinearIndependent D.host.E I.transpose)
    (v : Fin m → D.host.E) (a : Fin s → AE D) (h : (fun i => incA D (v i)) = I.map (incA D) *ᵥ a) :
    ∃ b : Fin s → D.host.E, v = I *ᵥ b := by
  obtain ⟨L, hL⟩ := exists_leftInv I hI
  refine ⟨L *ᵥ v, ?_⟩
  have ha : a = fun j => incA D ((L *ᵥ v) j) := by
    have h1 : L.map (incA D) *ᵥ (fun i => incA D (v i)) = a := by
      rw [h, Matrix.mulVec_mulVec, ← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rw [← h1]
    funext j
    exact (RingHom.map_mulVec (incA D) L v j).symm
  funext i
  apply incA_injective
  have := congrFun h i
  rw [this, ha]
  exact (RingHom.map_mulVec (incA D) I (L *ᵥ v) i).symm

theorem fst_perp (W : HSp D) (Y : Lag W) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E)
    (hY : Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _))
    (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) (hy : y ∈ Y.1) : (Iᴴ * W.gram) *ᵥ y.1 = 0 := by
  funext a
  have hcol : ((I.transpose a, 0) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ∈ Y.1 := by
    have h : I.transpose a ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := hY ▸ Submodule.subset_span ⟨a, rfl⟩
    exact h
  have hiso := Y.2.2 _ hcol y hy
  simp only [star_zero, zero_dotProduct] at hiso
  rw [← Matrix.mulVec_mulVec]
  show _ = (0 : D.host.E)
  rw [← hiso]
  rfl

theorem lagAct_eq_of_mem_NI : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E),
    IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) →
    ∀ n : GQ W, (n : GA D W) ∈ NI W I → GlobalTheory.RallisCusp.lagAct W n Y = Y := by
  intro D W Y s I hI hY n hn
  have hn' : ((n⁻¹ : GQ W) : GA D W) ∈ NI W I := by
    rw [InvMemClass.coe_inv]
    exact inv_mem hn
  obtain ⟨-, hP⟩ := ni_prop W I _ hn'
  have hc : Formalism.L2.Theta.mt W ((n⁻¹ : GQ W) : GA D W) - 1 = (gqMat W n⁻¹ - 1).map (incA D) := by
    rw [← rat_gqMat, ← rat_one, ← rat_sub]
    rfl
  have hle : Y.1 ≤ (lagAct W n Y).1 := by
    intro y hy
    rw [mem_lagAct]
    obtain ⟨a, ha⟩ := hP y.1 (fst_perp W Y I hY y hy)
    obtain ⟨b, hb⟩ := descend I hI.2.1 ((gqMat W n⁻¹ - 1) *ᵥ y.1) a (by
      rw [← ha, hc]
      funext i
      exact RingHom.map_mulVec (incA D) _ _ i)
    have hIb : ((I *ᵥ b, 0) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ∈ Y.1 := by
      have h : I *ᵥ b ∈ Submodule.span D.host.E (Set.range I.col) := by
        rw [← Matrix.range_mulVecLin]
        exact ⟨b, rfl⟩
      have h' : I *ᵥ b ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := by
        rw [← hY]
        exact h
      exact h'
    have e : ((gqMat W n⁻¹ *ᵥ y.1, y.2) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) =
        y + (I *ᵥ b, 0) := by
      rw [← hb, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact Prod.ext (by simp) (by simp)
    rw [e]
    exact Y.1.add_mem hy hIb
  exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by rw [Y.2.1, (lagAct W n Y).2.1])).symm

end GlobalTheory.RallisCuspStab

end
