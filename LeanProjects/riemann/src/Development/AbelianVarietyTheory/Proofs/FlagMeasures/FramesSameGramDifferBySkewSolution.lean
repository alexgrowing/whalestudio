import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLatticeStatement

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.FrameDiff

theorem dd_zpow_le (D : D7) (a : Fin D.R.rS) :
    (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      ddS D ^ (-(D.R.rS : ℤ)) := by
  have ha := a.2
  by_cases h0 : ddS D = 0
  · rw [h0, _root_.zero_zpow _ (by omega)]
    exact FractionalIdeal.zero_le _
  · have h1 : (-((D.R.rS : ℤ) - (a : ℕ))) = -(D.R.rS : ℤ) + ((a : ℕ) : ℤ) := by ring
    rw [h1, zpow_add₀ h0, zpow_natCast]
    have h2 : ddS D ^ (a : ℕ) ≤ 1 := by
      unfold ddS
      rw [← FractionalIdeal.coeIdeal_pow]
      exact FractionalIdeal.coeIdeal_le_one
    calc _ ≤ ddS D ^ (-(D.R.rS : ℤ)) * 1 := by gcongr
      _ = _ := mul_one _

theorem coords_of_mem_XS (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (y : (VS D).V)
    (hy : y ∈ XS D F0) :
    ∃ c : Fin D.R.rS → D.host.E,
      (∀ a, c a ∈ (ddS D ^ (-(D.R.rS : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧
      y = ∑ a, c a • F0.e a := by
  unfold XS at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, x, hx, rfl⟩ := hy
    refine ⟨Pi.single a x, fun a' => ?_, ?_⟩
    · by_cases h : a' = a
      · subst h
        rw [Pi.single_eq_same]
        exact dd_zpow_le D a' hx
      · rw [Pi.single_eq_of_ne h]
        exact FractionalIdeal.zero_mem _
    · rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  | zero => exact ⟨0, fun _ => FractionalIdeal.zero_mem _, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨c, hc, rfl⟩ := h
    obtain ⟨c', hc', rfl⟩ := h'
    refine ⟨c + c', fun a => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩
    exact Submodule.add_mem (FractionalIdeal.coeToSubmodule _) (hc a) (hc' a)
  | smul o y _ h =>
    obtain ⟨c, hc, rfl⟩ := h
    refine ⟨o • c, fun a => ?_, by simp [Finset.smul_sum, smul_assoc]⟩
    exact Submodule.smul_mem (FractionalIdeal.coeToSubmodule _) o (hc a)

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem star_hT (x y : S.V) : star (S.hT x y) = S.hT y x := S.herm.eq x y

theorem gram_eq (F F' : FlagG S r T) (b b' : Fin (r + 1)) :
    S.hT (F.fvec b) (F.fvec b') = S.hT (F'.fvec b) (F'.fvec b') := by
  have hz : ∀ (G : FlagG S r T) a, S.hT G.z (G.e a) = 0 := fun G a => by
    rw [← star_hT, G.z_orth, star_zero]
  induction b using Fin.lastCases <;> induction b' using Fin.lastCases <;>
    simp [FlagG.fvec, F.e_iso, F'.e_iso, F.z_orth, F'.z_orth, F.z_norm, F'.z_norm, hz]

theorem mem_orth_iff (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem hT_X_eq_zero (F : FlagG S r T) (v : S.V) (hv : ∀ a, S.hT (F.e a) v = 0) (x : S.V) (hx : x ∈ F.X) :
    S.hT x v = 0 := by
  unfold FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hv a
  | zero => simp
  | add y y' _ _ h h' => simp [h, h']
  | smul c y _ h => simp [h]

theorem frame_mem (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (h : IsLift Λ F) (he : ∀ a, F.fl.e a ∈ Λ)
    (b : Fin (r + 1)) : frame F b ∈ Λ := by
  induction b using Fin.lastCases with
  | last => simpa [FlagG.fvec] using h.1
  | cast a => simpa [FlagG.fvec] using he a

end Gen

theorem mem_perpE_iff (D : D7) (P : LatW D) (w : (D.sp.X 0).V) :
    w ∈ perpE D P ↔ ∀ p ∈ P, (D.sp.X 0).hT p w = 0 := by
  simp [perpE, Submodule.mem_iInf]

theorem frame_diff : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D), (∀ p, φ p ∈ XLam Λ (lf D F0)) → ∀ F₁ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, ∀ F₂ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, (∀ b, ∃ w, IsWcomp D P (frame F₁ b) w ∧ IsWcomp D P (frame F₂ b) w) → ∃ x : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E, (∀ b, frame F₂ b = frame F₁ b + ∑ a, x a b • F0.e a) ∧ (∀ a b, x a b ∈ (ddS D ^ (-(D.R.rS : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ xᴴ * Z.submatrix Fin.castSucc id + (Z.submatrix Fin.castSucc id)ᴴ * x = 0 := by
  intro D u u' F0 Λ hst hb hrow P φ Z hφ F₁ h₁ F₂ h₂ hw
  obtain ⟨hW, -, hpos, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hst hb hrow
  obtain ⟨l₁, e₁, z₁, o₁⟩ := h₁
  obtain ⟨l₂, e₂, z₂, o₂⟩ := h₂
  have hiso : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
    D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)
  have hZ₁ : ∀ a b, (hS D).hT (F0.fvec a) (frame F₁ b) = Z a b := fun a b => by rw [← z₁]; rfl
  have hZ₂ : ∀ a b, (hS D).hT (F0.fvec a) (frame F₂ b) = Z a b := fun a b => by rw [← z₂]; rfl
  have hWX : ∀ (w : (D.sp.X 0).V), ∀ x ∈ F0.X, (hS D).hT (D.sp.iXY 0 w) x = 0 := by
    intro w x hx
    rw [← star_hT, hT_X_eq_zero F0 (D.sp.iXY 0 w) (fun a => ?_) x hx, star_zero]
    rw [← star_hT, hb.1, (D.sp.hyp_orthX a w).1, star_zero]
  have hd : ∀ b, frame F₂ b - frame F₁ b ∈ XS D F0 := by
    intro b
    rw [← hrow.2.2]
    refine ⟨Λ.sub_mem (frame_mem Λ F₂ l₂ e₂ b) (frame_mem Λ F₁ l₁ e₁ b), ?_⟩
    set d := frame F₂ b - frame F₁ b with hdd
    have hf : ∀ a, (hS D).hT (F0.fvec a) d = 0 := fun a => by rw [hdd, map_sub, hZ₁, hZ₂, sub_self]
    have hX : ∀ x ∈ F0.X, (hS D).hT x d = 0 :=
      hT_X_eq_zero F0 d (fun a => by simpa [FlagG.fvec] using hf a.castSucc)
    have hz : (hS D).hT F0.z d = 0 := by simpa [FlagG.fvec] using hf (Fin.last _)
    have hmem : d ∈ Wsp D ⊔ Xsp (lf D F0) := by
      rw [hW.1, mem_orth_iff]
      intro y hy
      obtain ⟨x, hx, y', hy', rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy'
      simp [hX x hx, hz]
    obtain ⟨_, ⟨w, rfl⟩, x, hx, hwx⟩ := Submodule.mem_sup.1 hmem
    have hwd : ∀ σ, (hS D).hT (D.sp.iXY 0 σ) d = (D.sp.X 0).hT σ w := fun σ => by
      rw [← hwx, map_add, hiso, hWX σ x hx, add_zero]
    have hwP : w ∈ perpE D P := by
      rw [mem_perpE_iff]
      intro p hp
      have h1 : (hS D).hT (D.sp.iXY 0 p + φ ⟨p, hp⟩) d = 0 := by
        rw [hdd, map_sub, o₁ ⟨p, hp⟩ b, o₂ ⟨p, hp⟩ b, sub_self]
      rw [map_add, LinearMap.add_apply, hX _ (hφ ⟨p, hp⟩).2, add_zero, hwd] at h1
      exact h1
    obtain ⟨w', c₁, c₂⟩ := hw b
    have hww : (D.sp.X 0).hT w w = 0 := by
      rw [← hwd, hdd, map_sub, c₁.2 w hwP, c₂.2 w hwP, sub_self]
    have hw0 : w = 0 := by
      by_contra hne
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      have := hpos τ w hne
      rw [hww] at this
      simp at this
    rw [hw0, map_zero, zero_add] at hwx
    rw [← hwx]
    exact hx
  choose c hc hcd using fun b => coords_of_mem_XS D F0 _ (hd b)
  have hfr : ∀ b, frame F₂ b = frame F₁ b + ∑ a, c b a • F0.e a := fun b => by
    rw [← hcd]; abel
  refine ⟨Matrix.of fun a b => c b a, hfr, fun a b => hc b a, ?_⟩
  refine Matrix.ext fun b b' => ?_
  have hg : (hS D).hT (frame F₂ b) (frame F₂ b') = (hS D).hT (frame F₁ b) (frame F₁ b') :=
    gram_eq F₂.fl F₁.fl b b'
  have hY : ∀ a b, (hS D).hT (F0.e a) (frame F₁ b) = Z a.castSucc b := fun a b => by
    simpa [FlagG.fvec] using hZ₁ a.castSucc b
  have hY' : ∀ a b, (hS D).hT (frame F₁ b) (F0.e a) = star (Z a.castSucc b) := fun a b => by
    rw [← hY, star_hT]
  rw [hfr b, hfr b'] at hg
  simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, hY, hY', F0.e_iso, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero,
    starRingEnd_apply] at hg
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.submatrix_apply, id, Matrix.zero_apply]
  have : ∑ a, star (Z a.castSucc b) * c b' a = ∑ a, c b' a * star (Z a.castSucc b) :=
    Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [this]
  linear_combination hg

end GlobalTheory.LoopC.FrameDiff
