import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLoc

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx

theorem ne_val {r : ℕ} {i j : Fin r} (h : i.1 ≠ j.1) : i ≠ j := fun e => h (congrArg Fin.val e)

theorem rv_inj {n : ℕ} {a b : Fin n} : rv a = rv b ↔ a = b :=
  ⟨fun h => by rw [← rv_rv a, h, rv_rv], fun h => h ▸ rfl⟩

theorem gram_of {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {u v : VA I} {P Q : Prop} [Decidable P] [Decidable Q]
    (h : hhat I u v - (if P then 1 else 0) ∈ Wq I w) (hPQ : P ↔ Q) :
    hhat I u v - (if Q then 1 else 0) ∈ Wq I w := by
  have e : (if P then (1 : I.E ⊗[I.F] Af I.F) else 0) = if Q then 1 else 0 := by
    by_cases hp : P
    · rw [if_pos hp, if_pos (hPQ.1 hp)]
    · rw [if_neg hp, if_neg (fun hq => hp (hPQ.2 hq))]
  rwa [e] at h

theorem gram_ne {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {u v : VA I} {Q : Prop} [Decidable Q]
    (h : hhat I u v ∈ Wq I w) (hQ : ¬ Q) : hhat I u v - (if Q then 1 else 0) ∈ Wq I w := by
  rwa [if_neg hQ, sub_zero]

variable {D : D7} (X : HidaSetting D)

theorem sg_hA (u v : VA X.B.I) : sg X.B.I (hA X.B.I u v) = hhat X.B.I v u := hhat_conj X.B.I u v

theorem fr_wt (i : Fin D.R.k) : fr X true (wI (hrD D) i) = X.bw i := by rw [fr_w]; rfl
theorem fr_wf (i : Fin D.R.k) : fr X false (wI (hrD D) i) = X.bwd (rv i) := by rw [fr_w]; rfl
theorem frd_wt (i : Fin D.R.k) : frd X true (wI (hrD D) i) = X.bwd i := by rw [frd_w]; rfl
theorem frd_wf (i : Fin D.R.k) : frd X false (wI (hrD D) i) = X.bw (rv i) := by rw [frd_w]; rfl

variable {w : HeightOneSpectrum (𝓞 X.B.I.E)}

theorem wq (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g c) : c ∈ Wq X.B.I w := zmod_Wq hg h

theorem wqs (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g c) : sg X.B.I c ∈ Wq X.B.I w := zmod_Wq hg (zmod_sg h)

theorem xI_inj {a b : Fin D.R.rS} : xI (hrD D) a = xI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa using this), fun h => h ▸ rfl⟩
theorem wI_inj {a b : Fin D.R.k} : wI (hrD D) a = wI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa using this), fun h => h ▸ rfl⟩
theorem yI_inj {a b : Fin D.R.rS} : yI (hrD D) a = yI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa using this), fun h => h ▸ rfl⟩

theorem gram (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w) :
    GramW w (fr X ob) (frd X ob) := by
  intro i j
  have sg_ite : ∀ (P : Prop) [Decidable P],
      sg X.B.I (if P then (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) else 0) = if P then 1 else 0 := by
    intro P _; split_ifs <;> simp
  rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ <;>
  rcases kind_cases (hrD D) j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩
  ·
    rw [dual_frame_isotropic, frame_isotropic]
    have h := wqs X hg ((X.gramIntegral b a).2.2)
    rw [map_sub, sg_hA, sg_ite] at h
    exact gram_of h (by rw [xI_inj]; exact eq_comm)
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    cases ob
    · rw [dual_frame_isotropic, fr_wf]; exact wq X hg ((X.weightVectorsIntegral (rv b)).2.2 a).2.2.2
    · rw [dual_frame_isotropic, fr_wt]; exact wq X hg ((X.weightVectorsIntegral b).2.2 a).2.1
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    rw [dual_frame_isotropic, frame_anisotropic]; exact wq X hg (X.formsAtZero.2 a).2
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    rw [dual_frame_isotropic, fr_y]; exact wq X hg (X.gramIntegral a (rv b)).2.1
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    cases ob
    · rw [frd_wf, frame_isotropic]; have := wqs X hg ((X.weightVectorsIntegral (rv a)).2.2 b).1; rwa [sg_hA] at this
    · rw [frd_wt, frame_isotropic]; have := wqs X hg ((X.weightVectorsIntegral a).2.2 b).2.2.1; rwa [sg_hA] at this
  ·
    cases ob
    · rw [frd_wf, fr_wf]
      simp only [Bool.false_eq_true, if_false] at hsew
      have h := wqs X hg (X.bw_dual (rv b) (rv a))
      rw [map_sub, sg_hA] at h
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl] at h ⊢
        have := add_mem h hsew
        convert this using 1; ring
      · rw [if_neg (fun h' => hab (rv_inj.1 h'.symm)), map_zero, sub_zero] at h
        exact gram_ne h (fun h' => hab (wI_inj.1 h'))
    · rw [frd_wt, fr_wt]
      simp only [if_true] at hew
      have h := wq X hg (X.bw_dual a b)
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl] at h ⊢
        change hhat X.B.I (X.bwd a) (X.bw a) - X.ew ∈ _ at h
        have := add_mem h hew
        convert this using 1; ring
      · rw [if_neg hab, sub_zero] at h
        exact gram_ne h (fun h' => hab (wI_inj.1 h'))
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    cases ob
    · rw [frd_wf, frame_anisotropic]; have := wqs X hg (X.weightVectorsIntegral (rv a)).1; rwa [sg_hA] at this
    · rw [frd_wt, frame_anisotropic]; have := wqs X hg (X.weightVectorsIntegral a).2.1; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    cases ob
    · rw [frd_wf, fr_y]; have := wqs X hg ((X.weightVectorsIntegral (rv a)).2.2 (rv b)).2.1; rwa [sg_hA] at this
    · rw [frd_wt, fr_y]; have := wqs X hg ((X.weightVectorsIntegral a).2.2 (rv b)).2.2.2; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    rw [dual_frame_anisotropic, frame_isotropic, hhat_neg_left]
    refine neg_mem ?_
    have := wqs X hg (X.formsAtZero.2 b).1; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    cases ob
    · rw [dual_frame_anisotropic, fr_wf, hhat_neg_left]; exact neg_mem (wq X hg (X.weightVectorsIntegral (rv b)).2.1)
    · rw [dual_frame_anisotropic, fr_wt, hhat_neg_left]; exact neg_mem (wq X hg (X.weightVectorsIntegral b).1)
  ·
    rw [dual_frame_anisotropic, frame_anisotropic, hhat_neg_left, if_pos rfl]
    have := neg_mem (wq X hg X.formsAtZero.1)
    convert this using 1
    show -hhat X.B.I X.z0 X.z0 - 1 = -(hA X.B.I X.z0 X.z0 + 1)
    rw [show hA X.B.I X.z0 X.z0 = hhat X.B.I X.z0 X.z0 from rfl]; ring
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    rw [dual_frame_anisotropic, fr_y, hhat_neg_left]
    refine neg_mem ?_
    have := wqs X hg (X.formsAtZero.2 (rv b)).2; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    rw [frd_y, frame_isotropic]; exact wq X hg (X.gramIntegral (rv a) b).1
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    cases ob
    · rw [frd_y, fr_wf]; exact wq X hg ((X.weightVectorsIntegral (rv b)).2.2 (rv a)).2.2.1
    · rw [frd_y, fr_wt]; exact wq X hg ((X.weightVectorsIntegral b).2.2 (rv a)).1
  ·
    refine gram_ne ?_ (ne_val (by simp <;> omega))
    rw [frd_y, frame_anisotropic]; exact wq X hg (X.formsAtZero.2 (rv a)).1
  ·
    rw [frd_y, fr_y]
    exact gram_of (wq X hg (X.gramIntegral (rv a) (rv b)).2.2) (by rw [rv_inj, yI_inj])

end Formalism.L2.SG.Pf.KppLoc
