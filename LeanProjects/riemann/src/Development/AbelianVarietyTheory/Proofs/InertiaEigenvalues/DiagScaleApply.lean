import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds

noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (K a ι) in

def diagScale (s : ZMod a → K) : Module.End K (Vec K a ι) where
  toFun v τ := s τ • v τ
  map_add' v w := by ext1 τ; simp [smul_add]
  map_smul' c v := by
    ext1 τ
    exact smul_comm (s τ) c (v τ)

@[simp] theorem diagScale_apply (s : ZMod a → K) (v : Vec K a ι) (τ : ZMod a) :
    diagScale K a ι s v τ = s τ • v τ := rfl

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

def isoProj {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) : Module.End K (Vec K a ι) :=
  letI := Fintype.ofFinite (rootsOfUnity e K)
  (e : K)⁻¹ • ∑ ζ : rootsOfUnity e K,
    diagScale K a ι (fun τ => ((TameGal.inertia ζ : TameGal K l e a).root τ)⁻¹ ^ c.val) ∘ₗ
      Δ.act (TameGal.inertia ζ)

def Tsub {η H : ℕ} {D₁ : BKDat O K l e a ι η H} {D₂ : BKDat O K l e a κ η H} (F : BKHom D₁ D₂)
    (A' b : ℕ) : Submodule O (Vec K a κ) :=
  (F.imL.restrictScalars O).map ((mulV K a κ (((X : K⟦X⟧) ^ e) ^ A')).restrictScalars O) ⊔
    (D₂.L.restrictScalars O).map ((mulV K a κ ((l : K⟦X⟧) ^ b)).restrictScalars O) ⊔
    GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod

end GlobalTheory.CokerL

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

theorem act_vpow_smul {P : PhiMod O K l e a ι} (Δ : Descent P) (g : TameGal K l e a) (n : ℕ)
    (w : Vec K a ι) : Δ.act g (((X : K⟦X⟧) ^ e) ^ n • w) = ((X : K⟦X⟧) ^ e) ^ n • Δ.act g w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, ih, Δ.act_X_pow_smul, ← mul_smul, ← pow_succ]

theorem diagScale_smul (s : ZMod a → K) (f : K⟦X⟧) (w : Vec K a ι) :
    diagScale K a ι s (f • w) = f • diagScale K a ι s w := by
  ext1 τ
  exact smul_comm (s τ) f (w τ)

theorem isoProj_vpow {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) (n : ℕ) (v : Vec K a ι) :
    isoProj Δ c (((X : K⟦X⟧) ^ e) ^ n • v) = ((X : K⟦X⟧) ^ e) ^ n • isoProj Δ c v := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, act_vpow_smul, diagScale_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  exact smul_comm _ _ _

theorem app_isoProj {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P}
    {Δ₂ : Descent Q} (F : Descent.Hom Δ₁ Δ₂) (c : ZMod e) (v : Vec K a ι) :
    F.app (isoProj Δ₁ c v) = isoProj Δ₂ c (F.app v) := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.map_smul_of_tower, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [← F.app_act]
  ext1 τ
  simp only [diagScale_apply, BK.Hom.app_apply, Matrix.mulVec_smul]

end GlobalTheory.CokerL
