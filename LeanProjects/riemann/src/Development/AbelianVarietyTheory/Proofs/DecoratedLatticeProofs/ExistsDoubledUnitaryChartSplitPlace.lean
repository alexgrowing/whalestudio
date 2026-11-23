import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLatticeFrameAtPlaceDirectSumBlockDiagonalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun.DblSplit

section Pure

variable {A : Type} [CommRing A] {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] (e : m ⊕ m ≃ ι)

theorem blkGL_mem_diag (a : GL m A) : blkGL e (a, a) ∈ Formalism.UG.stabGL (diagSub A e) :=
  mem_stabGL_diagSub.2 ((keepsDiag_blkMat _).2 rfl)

theorem keepsDiag_conj_iff (a : GL m A) (x : GL ι A) :
    KeepsDiag e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1 ↔ KeepsDiag e x.1 := by
  rw [← mem_stabGL_diagSub, ← mem_stabGL_diagSub, Subgroup.mul_mem_cancel_right _ (blkGL_mem_diag e a),
    Subgroup.mul_mem_cancel_left _ (inv_mem (blkGL_mem_diag e a))]

theorem det_leviMat_conj (a : GL m A) {x : GL ι A} (hx : KeepsDiag e x.1) :
    (leviMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (leviMat e x.1).det := by
  let p : Formalism.UG.stabGL (diagSub A e) := ⟨_, blkGL_mem_diag e a⟩
  let q : Formalism.UG.stabGL (diagSub A e) := ⟨x, mem_stabGL_diagSub.2 hx⟩
  change (leviGL e (p⁻¹ * q * p)).1.det = (leviGL e q).1.det
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.det_units_conj']

theorem det_quotMat_conj (a : GL m A) {x : GL ι A} (hx : KeepsDiag e x.1) :
    (quotMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (quotMat e x.1).det := by
  have h1 := ((keepsDiag_conj_iff e a x).2 hx).det_eq
  rw [det_leviMat_conj e a hx, Units.val_mul, Units.val_mul, Matrix.det_units_conj', hx.det_eq] at h1
  have hu : IsUnit (leviMat e x.1).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
    rw [hx.det_eq] at this
    exact isUnit_of_mul_isUnit_left this
  exact (hu.mul_left_cancel h1).symm

omit [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] in
theorem quotMat_map {B : Type} [CommRing B] (f : A →+* B) (M : Matrix ι ι A) :
    quotMat e (M.map f) = (quotMat e M).map f := by
  ext i j; simp [quotMat, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]

end Pure

theorem ordL_eq_neg_log {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (x : K) :
    ordL x = -WithZero.log (Valued.v x) := by
  unfold ordL
  split_ifs with h
  · simp [h]
  · conv_rhs => rw [← WithZero.coe_unzero h]
    rfl

theorem isHermND_dbl {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsHermND σ (dblGram finSumFinEquiv J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
    simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;> simp [hJ.1]
  · rw [dblGram, det_blkMat]
    exact mul_ne_zero hJ.2 (by rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by simp)) hJ.2)

theorem exists_dbl_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e → ∃ f : GLoc σ Q v ≃* GL (Fin (n + n)) (w.adicCompletion E), (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ KGL w (n + n)) ∧ (∀ y y', f (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (e y, e y')) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ KeepsDiag finSumFinEquiv (f g).1) ∧ ∀ p : siegelH (Fv F v) σ Q, toCompl h (aH _ σ Q p).1 = (leviMat finSumFinEquiv (f p).1).det ∧ ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ordL (toCompl h' (aH _ σ Q p).1) = -ordL (quotMat finSumFinEquiv (f p).1).det := by
  intro F E _ _ _ _ _ σ hc n J hJ Q hQ L _ v w h hv hL e he
  have hQ' : IsHermND σ Q := hQ ▸ isHermND_dbl σ hJ
  have hLL : Submodule.IsLattice E (sumLat finSumFinEquiv L L) := inferInstance
  obtain ⟨f₀, ⟨⟨b, hb, e0⟩, hK⟩, -⟩ := SplitChart.exists_isSplitChart hc hQ' hLL.fg hLL.span_eq_top h hv
    (isSelfDualAt_dbl hQ hL)
  obtain ⟨⟨a, ha, ea⟩, -⟩ := id he
  have hk := hb.inv_mul_mem (GlobalTheory.T.isLatticeFrameAtPlace_directSum_blockDiagonal E w n L a ha)
  have ef : ∀ g, f₀.trans (MulAut.conj (b⁻¹ * blkGL finSumFinEquiv (a, a))⁻¹) g =
      (blkGL finSumFinEquiv (a, a))⁻¹ * locMat σ Q h g * blkGL finSumFinEquiv (a, a) := fun g => by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, e0]; group
  have hP : ∀ p : siegelH (Fv F v) σ Q, KeepsDiag finSumFinEquiv (locMat σ Q h p).1 := fun p =>
    (mem_siegelOf.1 p.2).map _ (toCompl h)
  refine ⟨f₀.trans (MulAut.conj (b⁻¹ * blkGL finSumFinEquiv (a, a))⁻¹), fun g => ?_, fun y y' => ?_, fun g => ?_,
    fun p => ⟨?_, fun w' h' hne => ?_⟩⟩
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv, Subgroup.mul_mem_cancel_right _ hk,
      Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
    exact hK g
  · have h1 : locMat σ Q h (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (locMat σ J h y, locMat σ J h y') :=
      bc_blkGL finSumFinEquiv (toCompl h) _ _
    rw [ef, h1, ← map_inv, ← map_mul, ← map_mul, ea, ea]
    rfl
  · rw [ef, keepsDiag_conj_iff]
    refine ⟨fun hg => hP ⟨g, hg⟩, fun hg => ?_⟩
    obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc hv h
    refine GlobalTheory.Core.Rk.IwSplit.mem_siegelH_of_split hc hQ hJ.2 τ (mem_stabGL_diagSub.2 ?_)
    rw [ConjPlace.locMat_eq hc h hτ] at hg
    have h2 := hg.map _ ((ConjPlace.complEquiv hc h hτ).symm : w.adicCompletion E →+* Fv F v)
    convert h2 using 1
    exact Matrix.ext fun i j => ((ConjPlace.complEquiv hc h hτ).symm_apply_apply _).symm
  · rw [ef, det_leviMat_conj _ a (hP p)]
    change toCompl h (leviMat finSumFinEquiv (matHom _ σ Q p).1).det =
      (leviMat finSumFinEquiv ((matHom _ σ Q p).1.map (toCompl h))).det
    rw [leviMat_map, RingHom.map_det, RingHom.mapMatrix_apply]
  · obtain ⟨c, hcv, -, hcc, -⟩ := ConjPlace.exists_conj_chart hc hJ hL hne h h' he
    rw [ef, det_quotMat_conj _ a (hP p)]
    have h1 : (quotMat finSumFinEquiv (locMat σ Q h p).1).det =
        toCompl h (quotMat finSumFinEquiv (matHom _ σ Q p).1).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← quotMat_map]
      rfl
    have h2 := congrArg (fun y => Valued.v (toCompl h' y)) (sigR_det_quot_mul_aH hQ hJ.2 p)
    simp only [map_mul, map_one, ← hcc, hcv] at h2
    rw [h1, ordL_eq_neg_log, ordL_eq_neg_log, eq_inv_of_mul_eq_one_right h2, WithZero.log_inv]

end GlobalTheory.LFun.DblSplit
