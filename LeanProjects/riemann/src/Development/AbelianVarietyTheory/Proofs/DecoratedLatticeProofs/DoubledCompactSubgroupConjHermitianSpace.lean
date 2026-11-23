import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.LatMove

theorem stab_conj_iff {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (M M' : Set (ι → R)) (B X : GL ι R)
    (hB : ∀ Y, Y ∈ M ↔ B.1 *ᵥ Y ∈ M') :
    (∀ Y, Y ∈ M' ↔ X.1 *ᵥ Y ∈ M') ↔ (∀ Y, Y ∈ M ↔ (B⁻¹ * X * B).1 *ᵥ Y ∈ M) := by
  have key : ∀ Y, B.1 *ᵥ ((B⁻¹ * X * B).1 *ᵥ Y) = X.1 *ᵥ (B.1 *ᵥ Y) := fun Y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      show B * (B⁻¹ * X * B) = X * B by group]
  constructor
  · intro h Y
    rw [hB Y, hB, key]
    exact h _
  · intro h Y
    have hY : B.1 *ᵥ ((B⁻¹).1 *ᵥ Y) = Y := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have := h ((B⁻¹).1 *ᵥ Y)
    rw [hB, hB, key, hY] at this
    exact this

theorem map_conj_of_eq_one {G H : Type} [Group G] [Group H] (f : G →* H) {g : G} (hg : f g = 1) (x : G) :
    f (g⁻¹ * x * g) = f x := by
  rw [map_mul, map_mul, map_inv, hg, inv_one, one_mul, mul_one]

theorem map_conj' {G H : Type} [Group G] [Group H] (f : G →* H) (g x : G) :
    f (g⁻¹ * x * g) = (f g)⁻¹ * f x * f g := by
  rw [map_mul, map_mul, map_inv]

section General

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem mem_KFin_conj (h : Q = dblGram finSumFinEquiv J) {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (g : GLoc σ J v)
    (hg : ∀ z, z ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J g).val *ᵥ z ∈ latLoc F L' v) (x : GLoc σ Q v) :
    x ∈ GlobalTheory.Doubling.KFin σ Q L' v ↔ (ioH _ σ h (g, g))⁻¹ * x * ioH _ σ h (g, g) ∈ GlobalTheory.Doubling.KFin σ Q L v := by
  refine mem_stabLoc.trans (Iff.trans ?_ mem_stabLoc.symm)
  rw [map_conj', matHom_ioH, latLoc_sumLat, latLoc_sumLat]
  refine stab_conj_iff (SetLike.coe (sumLat finSumFinEquiv (latLoc F L v) (latLoc F L v)))
    (SetLike.coe (sumLat finSumFinEquiv (latLoc F L' v) (latLoc F L' v))) _ _ fun Y => ?_
  rw [← pairVec_eta finSumFinEquiv Y, val_blkGL, blkMat_mulVec, SetLike.mem_coe, SetLike.mem_coe,
    pairVec_mem_sumLat, pairVec_mem_sumLat]
  exact and_congr (hg _) (hg _)

theorem mem_KAd_conj (h : Q = dblGram finSumFinEquiv J) {L L' : Submodule (𝓞 E) (Fin n → E)} (k : GAd σ J)
    (hk : k ∈ finPts σ J)
    (hL : ∀ (v : HeightOneSpectrum (𝓞 F)) z,
      z ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J (proj σ J v k)).val *ᵥ z ∈ latLoc F L' v)
    (a : GL (Fin n) (AF F ⊗[F] E)) (x : GAd σ Q) :
    x ∈ KAd σ Q L' a ↔ (ioH _ σ h (k, k))⁻¹ * x * ioH _ σ h (k, k) ∈ KAd σ Q L a := by
  refine mem_KAd.trans (Iff.trans (and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)) mem_KAd.symm)
  · rw [map_conj', proj_ioH]
    exact mem_KFin_conj h _ (hL v) _
  · rw [map_conj_of_eq_one _ (by rw [projArch_ioH, mem_finPts_iff_forall.1 hk w, ioH_one])]

end General

theorem mem_KAd_io_conj : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (k : GA D A), k ∈ GfC A →
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Fin A.rank → TensorProduct D.host.F (Fv D.host.F v) D.host.E),
      z ∈ latLoc D.host.F L v ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram (proj D.sp.cm.sig A.gram v k)).val *ᵥ z ∈ latLoc D.host.F L' v) →
    ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)), x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔
      (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a :=
  fun D A _ _ k hk hL a x => mem_KAd_conj (σ := D.sp.cm.sig) (gram_hdbl A) k hk hL a x

end GlobalTheory.LatMove
