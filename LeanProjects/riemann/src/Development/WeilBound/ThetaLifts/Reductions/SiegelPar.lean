import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
import Development.WeilBound.ThetaLifts.Reductions.SiegelParMod
import Development.WeilBound.ThetaLifts.Reductions.SiegelGood
import Development.WeilBound.ThetaLifts.FrameEstimates.LintegralLeOfCover
import Development.WeilBound.ThetaLifts.FrameEstimates.LeHeightOfIsTorusElt

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)
open PositivityTheory.ThKEst PositivityTheory.ThKEst.Sieg

namespace PositivityTheory.ThKR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

variable (σ J X Y) in

structure IsTorus (a : (Fin r → ℝ) → GAd σ J) : Prop where
  add : ∀ s t, a (s + t) = a s * a t
  cont : Continuous a
  tor : ∀ t, IsTorusElt σ J X Y (fun i => Real.exp (t i)) (a t)
  onX : ∀ t, (matHom _ σ J (a t)).1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i)))
  onY : ∀ t, (matHom _ σ J (a t)).1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i)))
  onV : ∀ t, ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
    (matHom _ σ J (a t)).1 *ᵥ incV F z = incV F z

theorem exists_isTorus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ a, IsTorus σ J X Y a := by
  obtain ⟨a, h1, h2, h3, h4⟩ := exists_torus h hJ hW
  exact ⟨a, ⟨h1, h2, h3, fun t => (h4 t).1, fun t => (h4 t).2.1, fun t => (h4 t).2.2⟩⟩

theorem mul_mem_minPar {p q : GAd σ J} (hp : p ∈ minPar σ J X) (hq : q ∈ minPar σ J X) : p * q ∈ minPar σ J X :=
  mul_mem_minimal_parabolic hp hq

theorem inv_mem_minPar (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) : p⁻¹ ∈ minPar σ J X :=
  inv_mem_minimal_parabolic h hJ hW hp

variable (X) in

def minParSub (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : Subgroup (GAd σ J) where
  carrier := minPar σ J X
  one_mem' := one_mem_minPar σ J X
  mul_mem' := mul_mem_minPar
  inv_mem' := inv_mem_minPar h hJ hW

theorem isClosed_minPar (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (minPar σ J X) :=
  isClosed_minimal_parabolic h hJ hW

theorem minParOne_subset : minParOne σ J X ⊆ minPar σ J X := fun _ ⟨B, hB, e, _⟩ => ⟨B, hB, e⟩

theorem IsTorus.mem {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (t : Fin r → ℝ) : a t ∈ minPar σ J X :=
  ⟨_, Matrix.blockTriangular_diagonal _, ha.onX t⟩

def IsTorus.sub {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (t : Fin r → ℝ) : minParSub X h hJ hW :=
  ⟨a t, ha.mem t⟩

theorem exists_tau (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J}
    (ha : IsTorus σ J X Y a) :
    ∃ τ : minParSub X h hJ hW → Fin r → ℝ, Continuous τ ∧ (∀ p q, τ (p * q) = τ p + τ q) ∧
      (∀ t, τ (ha.sub h hJ hW t) = t) ∧ (∀ p (hp : p ∈ minParOne σ J X), τ ⟨p, minParOne_subset hp⟩ = 0) ∧
      ∀ p : minParSub X h hJ hW, p.1 * (a (τ p))⁻¹ ∈ minParOne σ J X :=
  exists_torus_section h hJ hW (minParSub X h hJ hW) (fun _ => Iff.rfl) ha.add ha.onX (ha.sub h hJ hW) (fun _ => rfl)

theorem map_mul_torus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J}
    (ha : IsTorus σ J X Y a) (ν : Measure (minParSub X h hJ hW)) [ν.IsHaarMeasure] (s : Fin r → ℝ) :
    ν.map (· * ha.sub h hJ hW s) = ENNReal.ofReal (Real.exp (2 * (Module.finrank ℚ F : ℝ) * rho2 n s)) • ν :=
  PMod.map_mul_torus_of h hJ hW (minParSub X h hJ hW) (isClosed_minPar h hJ hW) (fun _ hp => hp) (fun _ hp => hp)
    ha.add ha.onX ha.onY ha.onV ha.mem ν s

theorem commute_of_goodPosition (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) {K : Subgroup (GAd σ J)} (hK : IsCompact (K : Set (GAd σ J)))
    (hG : GoodPosition σ J X Y K) {m : GAd σ J} (hm : m ∈ minPar σ J X) (hmK : m ∈ K) (t : Fin r → ℝ) :
    a t * m = m * a t :=
  commute_of_good_position h hJ hW (ha.tor t).1 (ha.onX t) (ha.onY t) (ha.onV t) hK hG hm hmK

end PositivityTheory.ThKR

end
