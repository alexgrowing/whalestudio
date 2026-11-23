import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeStabilizerIffScaledFrameConjStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemUnitaryStandardIffConjSimilitudeStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Conj

theorem baseChangeTensorConjugation_involutive_of_involution {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (e : R ⊗[F] E) : sigR R σ (sigR R σ e) = e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x => simp [sigR, hσ]

theorem infinitePlaceComponent_tensorConjugation {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w (sigR (AF F) σ z) = sigR w.Completion σ (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a x => simp [compInf, sigR]

theorem mul_eq_conj_mul_of_invertible_cancel {R : Type*} [Ring R] {P Pi F X K : R} (h1 : P * Pi = 1)
    (h : Pi * F * X = (Pi * K * P) * (Pi * F)) : F * X = K * F := by
  have := congrArg (P * ·) h
  simp only [← mul_assoc, h1, one_mul] at this
  rw [this, mul_assoc K P Pi, h1, mul_one]

theorem eq_inv_conj_of_intertwine {R : Type*} [Ring R] {Fi F X K : R} (h1 : Fi * F = 1) (h : F * X = K * F) :
    X = Fi * K * F := by
  rw [mul_assoc, ← h, ← mul_assoc, h1, one_mul]

variable {D : D7}

theorem matHom_chart_conj (A : HSp D) (μ : D.host.E) (κ : GA D (dblSp A) ≃* G D A.rank) (hκ : IsChart A μ κ)
    (Fr : GL (Fin (A.rank + A.rank)) (AE D)) (p : GA D (dblSp A))
    (hp : mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = Fr.1) (k : GA D (dblSp A)) :
    GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D A.rank) (κ (p⁻¹ * k * p)) =
      Fr⁻¹ * GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram k * Fr := by
  set P := GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram p
  set Kk := GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram k
  have hmt : ∀ g, mt (dblSp A) g = (GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram g).1 := fun _ => rfl
  have hT : (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = (P⁻¹).1 * Fr.1 := by
    rw [← hp, hmt, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have h := hκ (p⁻¹ * k * p)
  have hm : GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram (p⁻¹ * k * p) = P⁻¹ * Kk * P := by
    rw [map_mul, map_mul, map_inv]
  rw [hmt, hm, hT] at h
  change (P⁻¹).1 * Fr.1 * mat (κ (p⁻¹ * k * p)) = (P⁻¹ * Kk * P).1 * ((P⁻¹).1 * Fr.1) at h
  apply Units.ext
  have h2 : Fr.1 * mat (κ (p⁻¹ * k * p)) = Kk.1 * Fr.1 := by
    rw [Units.val_mul, Units.val_mul] at h
    exact mul_eq_conj_mul_of_invertible_cancel (P := P.1) (Units.mul_inv P) h
  change mat (κ (p⁻¹ * k * p)) = _
  rw [Units.val_mul, Units.val_mul]
  exact eq_inv_conj_of_intertwine (Units.inv_mul Fr) h2

theorem mem_KAd_iff_of_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (Q J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a b : GL (Fin n) (AF F ⊗[F] E)) (hb : IsLatticeFrame L b)
    (hab : ∀ w, Formalism.UG.bc (compInf F E w) b = Formalism.UG.bc (compInf F E w) a)
    (M M' : GL (Fin (n + n)) (AF F ⊗[F] E)) (u r : (AF F ⊗[F] E)ˣ)
    (hM' : ∀ v i j, compFin F E v (M'.1 i j) ∈ intLoc F E v ∧ compFin F E v ((M'⁻¹).1 i j) ∈ intLoc F E v)
    (hMu : M.1 = (u : AF F ⊗[F] E) • M'.1)
    (hMM : ∀ w, (Formalism.UG.cT (sigR (AF F) σ) M.1 * M.1).map (compInf F E w) = compInf F E w r • 1)
    (k : GAd σ Q) (g : GAd σ J)
    (hg : GlobalTheory.AdelicU.matHom _ σ J g = (blkGL finSumFinEquiv (b, b) * M)⁻¹ * GlobalTheory.AdelicU.matHom _ σ Q k *
      (blkGL finSumFinEquiv (b, b) * M)) :
    k ∈ KAd σ Q L a ↔ g ∈ levelAll σ J (stdLattice E (n + n)) 1 := by
  rw [mem_KAd, mem_levelAll]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · rw [GlobalTheory.Doubling.KFin, stabLoc, stabLoc, Subgroup.mem_comap, Subgroup.mem_comap, matHom_proj, matHom_proj, hg,
      map_mul (Formalism.UG.bc (compFin F E v)), map_mul (Formalism.UG.bc (compFin F E v)) _ (GlobalTheory.AdelicU.matHom _ σ Q k), map_inv]
    exact GlobalTheory.T.mem_latticeStabilizer_iff_scaledFrameConj F E (n + n) _ _ M M' u (isLatticeFrame_dbl hb) hM' hMu v _
  · have hc : Formalism.UG.cT (sigR w.Completion σ) (Formalism.UG.bc (compInf F E w) M).1 * (Formalism.UG.bc (compInf F E w) M).1 =
        ((Units.map (compInf F E w : AF F ⊗[F] E →* w.Completion ⊗[F] E) r : (w.Completion ⊗[F] E)ˣ) :
          w.Completion ⊗[F] E) • 1 := by
      have h := hMM w
      rw [Matrix.map_mul] at h
      refine Eq.trans ?_ h
      congr 1
      ext i j
      exact (infinitePlaceComponent_tensorConjugation σ w (M.1 j i)).symm
    rw [KArch, mem_stabArch, mem_stabArch, matHom_projArch, matHom_projArch, hg,
      GlobalTheory.T.mem_unitaryStandard_iff_conj_similitude _ _ (baseChangeTensorConjugation_involutive_of_involution _ σ hσ) _ _ _ _ hc]
    simp only [map_mul, map_inv, map_one, bc_blkGL, hab w, inv_one, one_mul, mul_one, mul_inv_rev, mul_assoc]

theorem isConj_of_frame : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a b : GL (Fin A.rank) (AE D)), IsLatticeFrame (frameLat A) b → (∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a) → ∀ (M M' : GL (Fin (A.rank + A.rank)) (AE D)) (u : (AE D)ˣ), IntGL M' → M.1 = (u : AE D) • M'.1 → (∀ w, (adj M.1 * M.1).map (compInf D.host.F D.host.E w) = compInf D.host.F D.host.E w (2 * u * cA D u) • 1) → ∀ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = (blkGL finSumFinEquiv (b, b) * M).1 → IsConj A a κ p := by
  intro D A μ _ κ hκ a b hb hab M M' u hM' hMu hMM p hp k
  have h2 : IsUnit (2 : AE D) := by
    have := (IsUnit.mk0 (2 : D.host.E) two_ne_zero).map (incA D)
    rwa [map_ofNat] at this
  have hr : IsUnit (2 * (u : AE D) * cA D u) := (h2.mul u.isUnit).mul (u.isUnit.map (cA D))
  have hg := matHom_chart_conj A μ κ hκ (blkGL finSumFinEquiv (b, b) * M) p hp k
  have hMM' : ∀ w, (Formalism.UG.cT (cA D) M.1 * M.1).map (compInf D.host.F D.host.E w) =
      compInf D.host.F D.host.E w hr.unit • 1 := hMM
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have key := mem_KAd_iff_of_conj (n := A.rank) D.sp.cm.sig hσ (dblSp A).gram (Jst D A.rank) (frameLat A) a b hb hab
    M M' u hr.unit (fun v i j => ⟨hM'.1 i j v, hM'.2 i j v⟩) hMu hMM' k (κ ((p : GA D (dblSp A))⁻¹ * k * p)) hg
  have e : K D A.rank = levelAll D.sp.cm.sig (Jst D A.rank) (stdLattice D.host.E (A.rank + A.rank)) 1 := rfl
  rw [e]
  exact key

end GlobalTheory.StdUnn.Conj

end
