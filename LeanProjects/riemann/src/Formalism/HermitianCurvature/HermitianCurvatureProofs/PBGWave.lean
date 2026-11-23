import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section sesq

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  (Dv : V → Prop) (Dv' : V' → Prop) (f : V → V' → ℂ)

theorem sesq_sum_left (h0 : Dv 0) (hadd : ∀ x y, Dv x → Dv y → Dv (x + y)) (hsmul : ∀ (c : ℂ) x, Dv x → Dv (c • x))
    (hf : ∀ x₁ x₂ y (c : ℂ), Dv x₁ → Dv x₂ → Dv' y → f (x₁ + c • x₂) y = f x₁ y + c * f x₂ y)
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (v : ι → V) (hv : ∀ i, Dv (v i)) (y : V') (hy : Dv' y) :
    f (∑ i ∈ s, a i • v i) y = ∑ i ∈ s, a i * f (v i) y := by
  classical
  have hD : ∀ t : Finset ι, Dv (∑ i ∈ t, a i • v i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using h0
    | insert b t hb ih => rw [Finset.sum_insert hb]; exact hadd _ _ (hsmul _ _ (hv b)) ih
  have hzero : f 0 y = 0 := by
    have := hf 0 0 y 1 h0 h0 hy
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  induction s using Finset.induction_on with
  | empty => simpa using hzero
  | insert b t hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, add_comm (a b • v b), hf _ _ y (a b) (hD t) (hv b) hy, ih]
    ring

theorem sesq_sum_right (h0 : Dv' 0) (hadd : ∀ x y, Dv' x → Dv' y → Dv' (x + y))
    (hsmul : ∀ (c : ℂ) x, Dv' x → Dv' (c • x))
    (hf : ∀ x y₁ y₂ (c : ℂ), Dv x → Dv' y₁ → Dv' y₂ → f x (y₁ + c • y₂) = f x y₁ + conj c * f x y₂)
    (x : V) (hx : Dv x) {ι : Type} (s : Finset ι) (a : ι → ℂ) (v : ι → V') (hv : ∀ i, Dv' (v i)) :
    f x (∑ i ∈ s, a i • v i) = ∑ i ∈ s, conj (a i) * f x (v i) := by
  classical
  have hD : ∀ t : Finset ι, Dv' (∑ i ∈ t, a i • v i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using h0
    | insert b t hb ih => rw [Finset.sum_insert hb]; exact hadd _ _ (hsmul _ _ (hv b)) ih
  have hzero : f x 0 = 0 := by
    have := hf x 0 0 1 hx h0 h0
    simp only [one_smul, add_zero, map_one, one_mul] at this
    linear_combination -this
  induction s using Finset.induction_on with
  | empty => simpa using hzero
  | insert b t hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, add_comm (a b • v b), hf x _ _ (a b) hx (hD t) (hv b), ih]
    ring

end sesq

section dec

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def DecV {S : Type} (x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) : Prop := ∀ a (A : ℝ) (m : ℕ), B.InCC A m (x a)

theorem decV_zero {S : Type} : DecV (0 : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) :=
  fun _ _ _ => ⟨0, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero⟩

theorem decV_add {S : Type} {x y : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : DecV x) (hy : DecV y) :
    DecV (x + y) := by
  intro a A m
  obtain ⟨c, hc⟩ := hx a A m
  obtain ⟨c', hc'⟩ := hy a A m
  exact ⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩

theorem decV_smul {S : Type} (c : ℂ) {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : DecV x) : DecV (c • x) := by
  intro a A m
  obtain ⟨c', hc'⟩ := hx a A m
  exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul c hc'⟩

theorem decV_restrict {n : ℕ} {x : Wd.Ix (Fin (n + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : DecV x) (e : Fin 2) :
    DecV (fun e' : Wd.Ix (Fin n) => x (Fin.cons e e')) := fun _ => hx _

theorem decV_of_nice {S : Type} {Bs : B.RealPlaceData k ρ Wp Wq} {ε : ℝ} {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)}
    (hx : ∀ a, JC.NiceCoef Bs ε (x a)) : DecV x := fun a A m => (hx a).2.1 A m

end dec

section pairJ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  (P0 : M.Par) (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter)

theorem form_sesq_left (x₁ x₂ y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : DecV x₁) (h₂ : DecV x₂) (hy : DecV y) :
    D.formLev T s j w (x₁ + c • x₂) y = D.formLev T s j w x₁ y + c * D.formLev T s j w x₂ y :=
  (Formalism.FourierDecayAlt.P.JCx4.formLev_sesq_core P0 T s j w _ _ le_rfl le_rfl x₁ x₂ y c (fun a => h₁ a _ _)
    (fun a => h₂ a _ _) (fun a => hy a _ _)).1

theorem form_sesq_right (x y₁ y₂ : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : DecV x) (h₁ : DecV y₁) (h₂ : DecV y₂) :
    D.formLev T s j w x (y₁ + c • y₂) = D.formLev T s j w x y₁ + conj c * D.formLev T s j w x y₂ :=
  (Formalism.FourierDecayAlt.P.JCx4.formLev_sesq_core P0 T s j w _ _ le_rfl le_rfl y₁ y₂ x c (fun a => h₁ a _ _)
    (fun a => h₂ a _ _) (fun a => hx a _ _)).2

theorem pairJ_sesq_left : ∀ (ys : List ℝ) (x₁ x₂ : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ),
    DecV x₁ → DecV x₂ → DecV y →
    KB.pairJ (D.formLev T s j w) ys (x₁ + c • x₂) y =
      KB.pairJ (D.formLev T s j w) ys x₁ y + c * KB.pairJ (D.formLev T s j w) ys x₂ y
  | [], x₁, x₂, y, c, h₁, h₂, hy => form_sesq_left P0 T s j w x₁ x₂ y c h₁ h₂ hy
  | _ :: ys, x₁, x₂, y, c, h₁, h₂, hy => by
    simp only [KB.pairJ]
    have e1 := pairJ_sesq_left ys (fun e => x₁ (Fin.cons 1 e)) (fun e => x₂ (Fin.cons 1 e)) (fun e => y (Fin.cons 0 e))
      c (decV_restrict h₁ 1) (decV_restrict h₂ 1) (decV_restrict hy 0)
    have e0 := pairJ_sesq_left ys (fun e => x₁ (Fin.cons 0 e)) (fun e => x₂ (Fin.cons 0 e)) (fun e => y (Fin.cons 1 e))
      c (decV_restrict h₁ 0) (decV_restrict h₂ 0) (decV_restrict hy 1)
    have r1 : (fun e => (x₁ + c • x₂) (Fin.cons 1 e)) = (fun e => x₁ (Fin.cons 1 e)) + c • (fun e => x₂ (Fin.cons 1 e)) := rfl
    have r0 : (fun e => (x₁ + c • x₂) (Fin.cons 0 e)) = (fun e => x₁ (Fin.cons 0 e)) + c • (fun e => x₂ (Fin.cons 0 e)) := rfl
    rw [r1, r0, e1, e0]
    ring

theorem pairJ_sesq_right : ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (y₁ y₂ : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ),
    DecV x → DecV y₁ → DecV y₂ →
    KB.pairJ (D.formLev T s j w) ys x (y₁ + c • y₂) =
      KB.pairJ (D.formLev T s j w) ys x y₁ + conj c * KB.pairJ (D.formLev T s j w) ys x y₂
  | [], x, y₁, y₂, c, hx, h₁, h₂ => form_sesq_right P0 T s j w x y₁ y₂ c hx h₁ h₂
  | _ :: ys, x, y₁, y₂, c, hx, h₁, h₂ => by
    simp only [KB.pairJ]
    have e1 := pairJ_sesq_right ys (fun e => x (Fin.cons 1 e)) (fun e => y₁ (Fin.cons 0 e)) (fun e => y₂ (Fin.cons 0 e))
      c (decV_restrict hx 1) (decV_restrict h₁ 0) (decV_restrict h₂ 0)
    have e0 := pairJ_sesq_right ys (fun e => x (Fin.cons 0 e)) (fun e => y₁ (Fin.cons 1 e)) (fun e => y₂ (Fin.cons 1 e))
      c (decV_restrict hx 0) (decV_restrict h₁ 1) (decV_restrict h₂ 1)
    have r0 : (fun e => (y₁ + c • y₂) (Fin.cons 0 e)) = (fun e => y₁ (Fin.cons 0 e)) + c • (fun e => y₂ (Fin.cons 0 e)) := rfl
    have r1 : (fun e => (y₁ + c • y₂) (Fin.cons 1 e)) = (fun e => y₁ (Fin.cons 1 e)) + c • (fun e => y₂ (Fin.cons 1 e)) := rfl
    rw [r1, r0, e1, e0]
    ring

theorem pairJ_sum_sum (ys : List ℝ) {ι ι' : Type} (S : Finset ι) (S' : Finset ι') (a : ι → ℂ) (b : ι' → ℂ)
    (v : ι → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (u : ι' → Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (hv : ∀ i, DecV (v i)) (hu : ∀ i, DecV (u i)) :
    KB.pairJ (D.formLev T s j w) ys (∑ i ∈ S, a i • v i) (∑ i ∈ S', b i • u i) =
      ∑ i ∈ S, ∑ i' ∈ S', a i * conj (b i') * KB.pairJ (D.formLev T s j w) ys (v i) (u i') := by
  have hU : DecV (∑ i ∈ S', b i • u i) := by
    classical
    induction S' using Finset.induction_on with
    | empty => simpa using (decV_zero (k := P0.k) (ρ := P0.r - j) (Wp := Wp) (Wq := Wq))
    | insert c t hc ih => rw [Finset.sum_insert hc]; exact decV_add (decV_smul _ (hu c)) ih
  rw [sesq_sum_left DecV DecV (fun x y => KB.pairJ (D.formLev T s j w) ys x y) decV_zero
    (fun _ _ => decV_add) (fun c _ => decV_smul c)
    (fun x₁ x₂ y c h₁ h₂ hy => pairJ_sesq_left P0 T s j w ys x₁ x₂ y c h₁ h₂ hy) S a v hv _ hU]
  apply Finset.sum_congr rfl
  intro i _
  rw [sesq_sum_right DecV DecV (fun x y => KB.pairJ (D.formLev T s j w) ys x y) decV_zero
    (fun _ _ => decV_add) (fun c _ => decV_smul c)
    (fun x y₁ y₂ c hx h₁ h₂ => pairJ_sesq_right P0 T s j w ys x y₁ y₂ c hx h₁ h₂) _ (hv i) S' b u hu,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i' _
  ring

end pairJ

section wave

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def EqGV {S : Type} (x y : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) : Prop := ∀ a, ∀ g ∈ B.GV k ρ, x a g = y a g

theorem uInv_add_smul (s : ℂ) : ∀ (w : List C.Letter) (x y : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℂ),
    KB.uInv s w (x + c • y) = KB.uInv s w x + c • KB.uInv s w y
  | [], x, y, c => rfl
  | l :: w, x, y, c => by
    funext e
    have hx := uInv_add_smul s w (fun e' => x (Fin.cons 0 e')) (fun e' => y (Fin.cons 0 e')) c
    have hx1 := uInv_add_smul s w (fun e' => x (Fin.cons 1 e')) (fun e' => y (Fin.cons 1 e')) c
    have r0 : (fun e' => (x + c • y) (Fin.cons 0 e')) = (fun e' => x (Fin.cons 0 e')) + c • (fun e' => y (Fin.cons 0 e')) := rfl
    have r1 : (fun e' => (x + c • y) (Fin.cons 1 e')) = (fun e' => x (Fin.cons 1 e')) + c • (fun e' => y (Fin.cons 1 e')) := rfl
    show KB.uInv s (l :: w) (x + c • y) e = KB.uInv s (l :: w) x e + c • KB.uInv s (l :: w) y e
    simp only [KB.uInv]
    rw [r0, r1, hx, hx1]
    by_cases h0 : e 0 = 0
    · simp only [if_pos h0, Pi.add_apply, Pi.smul_apply]
    · simp only [if_neg h0, Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]
      rw [mul_comm c]
      abel

theorem waveG_add_smul (Bs : B.RealPlaceData k ρ Wp Wq) (s : ℂ) (w : List C.Letter)
    (x y : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℂ) :
    KB.waveG Bs s w (x + c • y) = KB.waveG Bs s w x + c • KB.waveG Bs s w y := by
  funext e g
  simp only [KB.waveG, uInv_add_smul, Pi.add_apply, Pi.smul_apply, smul_add]
  rw [smul_comm c]

theorem uInv_zero (s : ℂ) (w : List C.Letter) :
    KB.uInv s w (0 : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) = 0 := by
  have h := uInv_add_smul s w (0 : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) 0 1
  rw [one_smul, add_zero] at h
  have h2 : KB.uInv s w (0 : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) + 0 =
      KB.uInv s w 0 + KB.uInv s w 0 := by rw [add_zero]; rw [one_smul] at h; exact h
  exact (add_left_cancel h2).symm

theorem waveG_zero (Bs : B.RealPlaceData k ρ Wp Wq) (s : ℂ) (w : List C.Letter) :
    KB.waveG Bs s w 0 = 0 := by
  funext e g
  simp only [KB.waveG, uInv_zero, Pi.zero_apply, smul_zero]

theorem waveG_sum (Bs : B.RealPlaceData k ρ Wp Wq) (s : ℂ) (w : List C.Letter) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (x : ι → Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    KB.waveG Bs s w (∑ i ∈ S, a i • x i) = ∑ i ∈ S, a i • KB.waveG Bs s w (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using waveG_zero Bs s w
  | insert b t hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, add_comm (a b • x b), waveG_add_smul, ih, add_comm]

theorem waveG_cons0 (Bs : B.RealPlaceData k ρ Wp Wq) (s : ℂ) (t : ℝ) (w : List C.Letter)
    (x : Wd.Ix (Fin (w.length + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (e' : Wd.Ix (Fin w.length)) :
    KB.waveG Bs s ((true, t) :: w) x (Fin.cons 0 e') = KB.waveG Bs s w (fun e => x (Fin.cons 0 e)) e' := by
  funext g
  have h1 : (fun a : Fin w.length => (Fin.cons (0 : Fin 2) e' : Wd.Ix (Fin (w.length + 1))) a.succ) = e' := by
    funext a; simp
  simp only [KB.waveG, KB.uInv, Fin.cons_zero, if_true, h1]

theorem waveG_cons1 (Bs : B.RealPlaceData k ρ Wp Wq) (s : ℂ) (t : ℝ) (w : List C.Letter)
    (x : Wd.Ix (Fin (w.length + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (e' : Wd.Ix (Fin w.length)) :
    KB.waveG Bs s ((true, t) :: w) x (Fin.cons 1 e') =
      KB.waveG Bs s w (fun e => x (Fin.cons 1 e)) e' + s • KB.waveG Bs s w (fun e => x (Fin.cons 0 e)) e' := by
  funext g
  have h1 : (fun a : Fin w.length => (Fin.cons (1 : Fin 2) e' : Wd.Ix (Fin (w.length + 1))) a.succ) = e' := by
    funext a; simp
  simp only [KB.waveG, KB.uInv, Fin.cons_zero, h1, Pi.add_apply, Pi.smul_apply, if_true,
    show ((1 : Fin 2) = 0) = False from by decide, if_false, smul_add]
  rw [smul_comm s]

theorem waveG_congrGV (Bs : B.RealPlaceData k ρ Wp Wq) (s : ℂ) :
    ∀ (w : List C.Letter) (x y : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)), EqGV x y →
      EqGV (KB.waveG Bs s w x) (KB.waveG Bs s w y) := by
  have hu : ∀ (w : List C.Letter) (x y : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)), EqGV x y →
      EqGV (KB.uInv s w x) (KB.uInv s w y) := by
    intro w
    induction w with
    | nil => intro x y h; exact h
    | cons l w ih =>
      intro x y h e g hg
      have h0 := ih (fun e' => x (Fin.cons 0 e')) (fun e' => y (Fin.cons 0 e')) (fun a g hg => h _ g hg)
      have h1 := ih (fun e' => x (Fin.cons 1 e')) (fun e' => y (Fin.cons 1 e')) (fun a g hg => h _ g hg)
      simp only [KB.uInv]
      split_ifs
      · exact h0 _ g hg
      all_goals (simp only [Pi.add_apply, Pi.smul_apply]; rw [h0 _ g hg, h1 _ g hg])
  intro w x y h e g hg
  simp only [KB.waveG]
  rw [hu w x y h e g hg]

theorem onOld_add_smul {w : List C.Letter} (Mo : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp))) :
    ∀ (ys : List ℝ) (x y : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℂ),
      KB.onOld (⇑Mo) ys (x + c • y) = KB.onOld (⇑Mo) ys x + c • KB.onOld (⇑Mo) ys y
  | [], x, y, c => (LinearMap.map_add Mo x (c • y)).trans (congrArg (Mo x + ·) (LinearMap.map_smul Mo c y))
  | _ :: ys, x, y, c => by
    funext e
    have h := onOld_add_smul Mo ys (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) (fun e' => y (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) c
    show KB.onOld (⇑Mo) ys (fun e' => (x + c • y) (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) (fun a => e a.succ) = _
    have r : (fun e' => (x + c • y) (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) =
        (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) + c • (fun e' => y (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) := rfl
    rw [r, h]
    rfl

theorem onOld_zero {w : List C.Letter} (Mo : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp))) (ys : List ℝ) :
    KB.onOld (⇑Mo) ys 0 = 0 := by
  have h := onOld_add_smul Mo ys 0 0 1
  rw [one_smul, add_zero, one_smul] at h
  have h2 : KB.onOld (⇑Mo) ys 0 + 0 = KB.onOld (⇑Mo) ys 0 + KB.onOld (⇑Mo) ys 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

theorem onOld_sum {w : List C.Letter} (Mo : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp))) (ys : List ℝ) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (x : ι → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    KB.onOld (⇑Mo) ys (∑ i ∈ S, a i • x i) = ∑ i ∈ S, a i • KB.onOld (⇑Mo) ys (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using onOld_zero Mo ys
  | insert b t hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, add_comm (a b • x b), onOld_add_smul, ih, add_comm]

theorem onOld_congrGV {w : List C.Letter} (M : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →
      Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (hM : ∀ x y, EqGV x y → EqGV (M x) (M y)) :
    ∀ (ys : List ℝ) (x y : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)), EqGV x y →
      EqGV (KB.onOld M ys x) (KB.onOld M ys y)
  | [], x, y, h => hM x y h
  | _ :: ys, x, y, h => by
    intro e g hg
    exact onOld_congrGV M hM ys (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) (fun e' => y (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e'))
      (fun a g hg => h _ g hg) _ g hg

theorem onOld_nice {w : List C.Letter} (Bs : B.RealPlaceData k ρ Wp Wq) (ε : ℝ)
    (M : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) → Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp))
    (hM : ∀ x, (∀ e, JC.NiceCoef Bs ε (x e)) → ∀ e, JC.NiceCoef Bs ε (M x e)) :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
      (∀ e, JC.NiceCoef Bs ε (x e)) → ∀ e, JC.NiceCoef Bs ε (KB.onOld M ys x e)
  | [], x, h => hM x h
  | _ :: ys, x, h => fun e => onOld_nice Bs ε M hM ys (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) (fun _ => h _) _

theorem mo_congrGV {S : Type} (Bs : B.RealPlaceData k ρ Wp Wq)
    (Mo : (Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] (Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)))
    (hMo : ∀ ε x, (∀ e, JC.NiceCoef Bs ε (x e)) → ∀ e, JC.NiceCoef Bs ε (Mo x e)) (x y : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp))
    (h : EqGV x y) : EqGV (Mo x) (Mo y) := by
  intro a g hg
  have hz : ∀ ε, ∀ e, JC.NiceCoef Bs ε ((x - y) e) := by
    intro ε e
    refine Formalism.FourierDecayAlt.P.JCx2.mn_nice_congr (F := fun _ => 0) (fun g hg => ?_) Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
    simp [h e g hg]
  by_contra hne
  have h0 : Mo (x - y) a g ≠ 0 := by
    rw [map_sub]; simp only [Pi.sub_apply]; exact sub_ne_zero.mpr hne
  have := (hMo (|Gf k ρ Bs.z Bs.z' g| + 1) _ (hz _) a).2.2 g hg h0
  have h2 := le_abs_self (Gf k ρ Bs.z Bs.z' g)
  linarith

end wave

end Formalism.FourierDecayAlt.P.PBG
