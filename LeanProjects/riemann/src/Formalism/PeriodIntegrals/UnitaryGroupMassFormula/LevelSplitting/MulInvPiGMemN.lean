import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ToMatrixLin

noncomputable section

namespace PI.LevelKSplit.W.SemiA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem piG_mem_H (g : HA R σ J) (hg : g ∈ Ssub R σ J P) : piG hσσ hJ hP g hg ∈ Hsub R σ J P := by
  have H := datR_hyp (R := R) hσσ hJ hP
  unfold Hsub
  rw [mem_stabT]
  intro b
  rw [lin_piG]
  refine Fin.addCases (fun b => ?_) (fun b => ?_) b
  · rw [tupH, Fin.append_left]
    refine Fin.lastCases ?_ (fun a => ?_) b
    · rw [F0, Fin.snoc_last]
      exact SemiG.Dat.unipotent_proj_fixes_normal H _
    · rw [F0, Fin.snoc_castSucc]
      exact SemiG.Dat.Pi_e H _ a
  · rw [tupH, Fin.append_right]
    exact SemiG.Dat.Pi_f H _ b

theorem piG_of_H {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (hg : h ∈ Ssub R σ J P) :
    piG hσσ hJ hP h hg = h := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  have H := datR_hyp (R := R) hσσ hJ hP
  unfold Hsub at hh
  rw [mem_stabT] at hh
  have he : ∀ a, lin R σ J h (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := fun a => by
    have h1 := hh (Fin.castAdd r (Fin.castSucc a))
    rwa [tupH, Fin.append_left, F0, Fin.snoc_castSucc] at h1
  have hz : lin R σ J h (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
    have h1 := hh (Fin.castAdd r (Fin.last r))
    rwa [tupH, Fin.append_left, F0, Fin.snoc_last] at h1
  have hf : ∀ a, lin R σ J h (ratV (F := F) R (P.f a)) = ratV (F := F) R (P.f a) := fun a => by
    have h1 := hh (Fin.natAdd (r + 1) a)
    rwa [tupH, Fin.append_right] at h1
  refine hext fun x => ?_
  rw [lin_piG]
  exact SemiG.Dat.Pi_of_fix H ⟨he, hz⟩ hf (uni_lin h) x

theorem piG_of_N {n : HA R σ J} (hn : n ∈ Nsub R σ J P) (hg : n ∈ Ssub R σ J P) :
    piG hσσ hJ hP n hg = 1 := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  have H := datR_hyp (R := R) hσσ hJ hP
  obtain ⟨-, hn2⟩ := hn
  refine hext fun x => ?_
  rw [lin_piG, lin_one]
  refine SemiG.Dat.Pi_of_N H (fun v hv => spanR_le Set.univ (hn2 v fun a => ?_)) x
  have h1 := hv a
  rwa [datR_h] at h1

theorem piG_mul {g g' : HA R σ J} (hg : g ∈ Ssub R σ J P) (hg' : g' ∈ Ssub R σ J P) :
    piG hσσ hJ hP (g * g') ((Ssub R σ J P).mul_mem hg hg') =
      piG hσσ hJ hP g hg * piG hσσ hJ hP g' hg' := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  refine hext fun x => ?_
  rw [lin_piG, lin_mul, lin_piG, lin_piG, Pi_lin_mul hσσ hJ hP hg hg']
  rfl

theorem mul_inv_piG_mem_N {s : HA R σ J} (hs : s ∈ Ssub R σ J P) :
    s * (piG hσσ hJ hP s hs)⁻¹ ∈ Nsub R σ J P := by
  have H := datR_hyp (R := R) hσσ hJ hP
  set π := piG hσσ hJ hP s hs with hπ
  have hpe : ∀ b, lin R σ J π (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := fun b => by
    rw [hπ, lin_piG]
    exact SemiG.Dat.Pi_e H _ b
  have hpie : ∀ b, lin R σ J π⁻¹ (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := fun b => by
    conv_lhs => rw [← hpe b]
    rw [lin_inv_lin]
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [lin_mul, hpie]
    exact S_e hs b
  · set u := lin R σ J π⁻¹ v with hu
    have hu' : ∀ a, (datR R σ J P T).h ((datR R σ J P T).e a) u = 0 := fun a => by
      rw [datR_h]
      show hR R σ J (ratV (F := F) R (P.e a)) u = 0
      rw [← hR_lin π, hpe, hu, lin_lin_inv]
      exact hv a
    have hZ : lin R σ J s (datR R σ J P T).z - (datR R σ J P T).z ∈
        Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) :=
      spanR_le Set.univ (stabilizer_fixes_tail_coords hs)
    have h1 := SemiG.Dat.N_part H (mapX_S hs) (mapW_S hs) hZ u hu'
    have h2 : (datR R σ J P T).Pi (lin R σ J s) u = v := by
      rw [← lin_piG hσσ hJ hP s hs, ← hπ, hu, lin_lin_inv]
    rw [h2] at h1
    rw [lin_mul, ← hu]
    exact span_le_spanR h1

end R

end PI.LevelKSplit.W.SemiA
