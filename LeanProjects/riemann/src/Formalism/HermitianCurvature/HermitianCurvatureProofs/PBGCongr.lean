import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pres

variable {k ρ : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def PresGV (T : (B.Mat k ρ → V) → (B.Mat k ρ → V)) : Prop :=
  ∀ f f₂ : B.Mat k ρ → V, (∀ g ∈ B.GV k ρ, f g = f₂ g) → ∀ g ∈ B.GV k ρ, T f g = T f₂ g

theorem presGV_foldr : ∀ (L : List ((B.Mat k ρ → V) → (B.Mat k ρ → V))), (∀ T ∈ L, PresGV T) →
    PresGV (fun f => L.foldr (fun T h => T h) f)
  | [], _ => fun _ _ h g hg => h g hg
  | T :: L, hL => fun f f₂ h g hg => by
      simp only [List.foldr_cons]
      exact hL T (by simp) _ _ (presGV_foldr L (fun T' hT' => hL T' (by simp [hT'])) f f₂ h) g hg

theorem presGV_qminorOp {t : ℕ} (p q : Fin t → Fin (2 * ρ + k + 1)) (u : ℂ) :
    PresGV (qminorOp (Q.EH k ρ) p q u : (B.Mat k ρ → V) → (B.Mat k ρ → V)) := by
  intro f f₂ h g hg
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine presGV_foldr _ ?_ f f₂ h g hg
  intro T hT
  rw [List.mem_ofFn] at hT
  obtain ⟨i, rfl⟩ := hT
  exact fun f f₂ h g hg => JFxB.top_congr (Q.EH k ρ) (fun c d f f₂ h => JFxB.EH_congr c d f f₂ h) _ _ _ h g hg

theorem presGV_chatL {t : ℕ} (pos : Fin t → Fin (2 * ρ + k + 1)) (u : ℂ) (a β : B.Mat k ρ → Fin t → ℂ) :
    PresGV (Q.chatL (Q.EH k ρ) pos u a β : (B.Mat k ρ → V) → (B.Mat k ρ → V)) := by
  intro f f₂ h g hg
  unfold Q.chatL
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [presGV_qminorOp _ _ u f f₂ h g hg]

theorem presGV_chat2L {t : ℕ} (pos : Fin t → Fin (2 * ρ + k + 1)) (u : ℂ) (a a' β β' : B.Mat k ρ → Fin t → ℂ) :
    PresGV (Q.chat2L (Q.EH k ρ) pos u a a' β β' : (B.Mat k ρ → V) → (B.Mat k ρ → V)) := by
  intro f f₂ h g hg
  unfold Q.chat2L
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun j' _ => ?_
  split_ifs
  · rw [presGV_qminorOp _ _ u f f₂ h g hg]
  · rfl

theorem presGV_tL (z z' : Fin (2 * ρ + k + 1) → ℂ) (i : Fin (ρ + 1)) (Y : ℂ) (p q : Fin 2) :
    PresGV (Q.tL k ρ z z' i Y p q : (B.Mat k ρ → V) → (B.Mat k ρ → V)) := by
  intro f f₂ h g hg
  fin_cases p <;> fin_cases q
  · exact presGV_qminorOp _ _ _ f f₂ h g hg
  · show -(Q.chatL _ _ _ _ _ f) g = -(Q.chatL _ _ _ _ _ f₂) g
    rw [presGV_chatL _ _ _ _ f f₂ h g hg]
  · show -(Q.chatL _ _ _ _ _ f) g = -(Q.chatL _ _ _ _ _ f₂) g
    rw [presGV_chatL _ _ _ _ f f₂ h g hg]
  · show -(Q.chat2L _ _ _ _ _ _ _ f) g = -(Q.chat2L _ _ _ _ _ _ _ f₂) g
    rw [presGV_chat2L _ _ _ _ _ _ f f₂ h g hg]

def OpG (T : D.Op (B.Mat k ρ → V)) : Prop := PresGV (T : (B.Mat k ρ → V) → (B.Mat k ρ → V))

theorem opG_zero : OpG (0 : D.Op (B.Mat k ρ → V)) := by
  intro f f₂ h g hg
  rfl

theorem opG_one : OpG (1 : D.Op (B.Mat k ρ → V)) := by
  intro f f₂ h g hg
  exact h g hg

theorem opG_add {T T' : D.Op (B.Mat k ρ → V)} (h : OpG T) (h' : OpG T') : OpG (T + T') := by
  intro f f₂ hf g hg
  show T f g + T' f g = T f₂ g + T' f₂ g
  rw [h f f₂ hf g hg, h' f f₂ hf g hg]

theorem opG_mul {T T' : D.Op (B.Mat k ρ → V)} (h : OpG T) (h' : OpG T') : OpG (T * T') := by
  intro f f₂ hf g hg
  exact h _ _ (h' f f₂ hf) g hg

theorem opG_cOp (c : ℂ) : OpG (D.cOp c : D.Op (B.Mat k ρ → V)) := by
  intro f f₂ hf g hg
  simp [D.cOp, hf g hg]

theorem opG_sum {ι : Type*} (s : Finset ι) (T : ι → D.Op (B.Mat k ρ → V)) (h : ∀ i ∈ s, OpG (T i)) :
    OpG (∑ i ∈ s, T i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact opG_zero
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact opG_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable {S : Type} [Fintype S] [DecidableEq S]

def SlopeTestChoicesGrowth (M : Wd.SlopeTestRemainingChoices S (D.Op (B.Mat k ρ → V))) : Prop := ∀ a b, OpG (M a b)

theorem matrix_good_mul {M N : Wd.SlopeTestRemainingChoices S (D.Op (B.Mat k ρ → V))} (hM : SlopeTestChoicesGrowth M) (hN : SlopeTestChoicesGrowth N) : SlopeTestChoicesGrowth (M * N) := by
  intro a b
  exact opG_sum _ _ fun c _ => opG_mul (hM a c) (hN c b)

theorem matrix_good_one : SlopeTestChoicesGrowth (1 : Wd.SlopeTestRemainingChoices S (D.Op (B.Mat k ρ → V))) := by
  intro a b
  rw [Matrix.one_apply]
  split_ifs
  · exact opG_one
  · exact opG_zero

theorem matrix_good_sum {ι : Type*} (s : Finset ι) (M : ι → Wd.SlopeTestRemainingChoices S (D.Op (B.Mat k ρ → V))) (h : ∀ i ∈ s, SlopeTestChoicesGrowth (M i)) :
    SlopeTestChoicesGrowth (∑ i ∈ s, M i) := by
  intro a b
  rw [Matrix.sum_apply]
  exact opG_sum _ _ fun i hi => h i hi a b

theorem matrix_good_scalar_map (M : Wd.SlopeTestRemainingChoices S ℂ) : SlopeTestChoicesGrowth (M.map D.cOp : Wd.SlopeTestRemainingChoices S (D.Op (B.Mat k ρ → V))) := by
  intro a b
  exact opG_cOp _

theorem matrix_good_diagonal (T : D.Op (B.Mat k ρ → V)) (hT : OpG T) :
    SlopeTestChoicesGrowth (Matrix.diagonal fun _ : Wd.Ix S => T) := by
  intro a b
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hT
  · exact opG_zero

def EntrywiseGood (M : Wd.M2 (Wd.SlopeTestRemainingChoices S (D.Op (B.Mat k ρ → V)))) : Prop := ∀ p q, SlopeTestChoicesGrowth (M p q)

theorem entrywise_good_mul {M N : Wd.M2 (Wd.SlopeTestRemainingChoices S (D.Op (B.Mat k ρ → V)))} (hM : EntrywiseGood M) (hN : EntrywiseGood N) : EntrywiseGood (M * N) := by
  intro p q
  rw [Matrix.mul_apply]
  exact matrix_good_sum _ _ fun r _ => matrix_good_mul (hM p r) (hN r q)

theorem entrywise_good_scalar (M : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) : EntrywiseGood (D.scal M : Wd.M2 (Wd.SlopeTestRemainingChoices S (D.Op (B.Mat k ρ → V)))) := by
  intro p q a b
  exact opG_cOp _

theorem entrywise_good_transpose {M : Wd.M2 (Wd.SlopeTestRemainingChoices S (D.Op (B.Mat k ρ → V)))} (hM : EntrywiseGood M) : EntrywiseGood M.transpose := by
  intro p q
  exact hM q p

theorem entrywise_good_transfer_word (QQ : ℂ → Wd.M2 (D.Op (B.Mat k ρ → V))) (hQ : ∀ Y p q, OpG (QQ Y p q)) :
    ∀ (w : List (Wd.Letter ℂ S)) (Y : ℂ), EntrywiseGood (D.TTop QQ w Y)
  | [], Y => fun p q => by
      unfold D.TTop
      rw [Matrix.map_apply]
      exact matrix_good_diagonal _ (hQ Y p q)
  | l :: w, Y => by
      unfold D.TTop
      split_ifs
      · exact entrywise_good_mul (entrywise_good_transfer_word QQ hQ w Y) (entrywise_good_scalar _)
      · exact entrywise_good_mul (entrywise_good_scalar _) (entrywise_good_transfer_word QQ hQ w Y)

theorem matrix_good_insert (a : S) {M : Wd.M2 (Wd.SlopeTestRemainingChoices S (D.Op (B.Mat k ρ → V)))} (hM : EntrywiseGood M) : SlopeTestChoicesGrowth (D.insOp a M) := by
  simp only [D.insOp]
  exact matrix_good_sum _ _ fun i _ => matrix_good_sum _ _ fun j _ => matrix_good_mul (matrix_good_scalar_map _) (hM i j)

theorem matrix_good_resolvent_word (QQ : ℂ → Wd.M2 (D.Op (B.Mat k ρ → V))) (hQ : ∀ Y p q, OpG (QQ Y p q)) :
    ∀ w : List (Wd.Letter ℂ S), SlopeTestChoicesGrowth (D.RRop QQ w)
  | [] => by unfold D.RRop; exact matrix_good_one
  | l :: w => by
      unfold D.RRop
      refine matrix_good_mul (matrix_good_resolvent_word QQ hQ w) (matrix_good_insert _ ?_)
      split_ifs
      · exact entrywise_good_transfer_word QQ hQ w l.pt
      · exact entrywise_good_transpose (entrywise_good_transfer_word QQ hQ w l.pt)

theorem actOp_congr {M : Wd.SlopeTestRemainingChoices S (D.Op (B.Mat k ρ → V))} (hM : SlopeTestChoicesGrowth M) {x y : Wd.Ix S → B.Mat k ρ → V}
    (h : ∀ a, ∀ g ∈ B.GV k ρ, x a g = y a g) : ∀ a, ∀ g ∈ B.GV k ρ, D.actOp M x a g = D.actOp M y a g := by
  intro a g hg
  simp only [D.actOp, Finset.sum_apply]
  exact Finset.sum_congr rfl fun b _ => hM a b (x b) (y b) (h b) g hg

end pres

section levels

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem opG_QQlev (T : D.LevTower k r Wp Wq) (s : ℂ) (j : Fin (r + 1)) (Y : ℂ) (p q : Fin 2) :
    OpG (D.QQlev T s j Y p q) := by
  intro f f₂ h g hg
  show (s • Q.tL k (r - j) (T.bs j).z (T.bs j).z' 0 Y p q f) g = (s • Q.tL k (r - j) (T.bs j).z (T.bs j).z' 0 Y p q f₂) g
  rw [Pi.smul_apply, Pi.smul_apply, presGV_tL _ _ _ _ p q f f₂ h g hg]

theorem matrix_good_level_resolvent (T : D.LevTower k r Wp Wq) (s : ℂ) (j : Fin (r + 1)) (w : List C.Letter) :
    SlopeTestChoicesGrowth (D.RRlev T s j w) :=
  matrix_good_resolvent_word (D.QQlev T s j) (opG_QQlev T s j) (D.positionted w)

variable [FiniteDimensional ℂ Wq]

theorem beta_congr_right (Bs : B.RealPlaceData k r Wp Wq) {F H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ B.GV k r, H₁ g = H₂ g) : B.beta Bs F H₁ = B.beta Bs F H₂ := by
  unfold B.beta Formalism.QuantumDeterminants.betaBig
  apply MeasureTheory.integral_congr_ae
  filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero Bs] with q hq
  rcases hq with hq | hq
  · have hg := Formalism.FourierDecayAlt.P.B7.gq_mem Bs hq
    have e := Formalism.FourierDecayAlt.P.Qx8.JF_congr Bs (F := H₁) (F' := H₂) (a := 1)
      (fun g hg => by rw [h g hg, one_smul]) hg
    rw [one_smul] at e
    unfold B.gq at e
    rw [e]
  · simp [hq]

theorem beta_congrGV (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : ∀ g ∈ B.GV k r, F₁ g = F₂ g) (hH : ∀ g ∈ B.GV k r, H₁ g = H₂ g) :
    B.beta Bs F₁ H₁ = B.beta Bs F₂ H₂ := by
  rw [Formalism.FourierDecayAlt.P.Dx1.LZ.beta_congr_left Bs hF, beta_congr_right Bs hH]

theorem formLev_congrGV (T : D.LevTower k r Wp Wq) (s : ℂ) (j : Fin (r + 1)) (w : List C.Letter)
    (x x' y y' : Wd.Ix (Fin w.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp))
    (hx : ∀ a, ∀ g ∈ B.GV k (r - j), x a g = y a g) (hx' : ∀ a, ∀ g ∈ B.GV k (r - j), x' a g = y' a g) :
    D.formLev T s j w x x' = D.formLev T s j w y y' := by
  unfold D.formLev
  refine Finset.sum_congr rfl fun a _ => ?_
  exact beta_congrGV (T.bs j) (actOp_congr (matrix_good_level_resolvent T s j w) hx a) (hx' a)

theorem pairJ_congrGV {ρ : ℕ} {X : Type} {w : List C.Letter}
    (Ξ : (Wd.Ix (Fin w.length) → B.Mat k ρ → X) → (Wd.Ix (Fin w.length) → B.Mat k ρ → X) → ℂ)
    (hΞ : ∀ x x' y y', (∀ a, ∀ g ∈ B.GV k ρ, x a g = y a g) → (∀ a, ∀ g ∈ B.GV k ρ, x' a g = y' a g) →
      Ξ x x' = Ξ y y') :
    ∀ (ys : List ℝ) (x y : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → X)
      (x' y' : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat k ρ → X),
      (∀ a, ∀ g ∈ B.GV k ρ, x a g = y a g) → (∀ a, ∀ g ∈ B.GV k ρ, x' a g = y' a g) →
      KB.pairJ Ξ ys x x' = KB.pairJ Ξ ys y y'
  | [], x, y, x', y', hx, hx' => hΞ x x' y y' hx hx'
  | _ :: ys, x, y, x', y', hx, hx' => by
      unfold KB.pairJ
      rw [pairJ_congrGV Ξ hΞ ys _ (fun e => y (Fin.cons (1 : Fin 2) e)) _ (fun e => y' (Fin.cons (0 : Fin 2) e))
          (fun e => hx _) (fun e => hx' _),
        pairJ_congrGV Ξ hΞ ys _ (fun e => y (Fin.cons (0 : Fin 2) e)) _ (fun e => y' (Fin.cons (1 : Fin 2) e))
          (fun e => hx _) (fun e => hx' _)]

theorem pairJ_formLev_congrGV (T : D.LevTower k r Wp Wq) (s : ℂ) (j : Fin (r + 1)) (w : List C.Letter)
    (ys : List ℝ) (x y : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp))
    (x' y' : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp))
    (hx : ∀ a, ∀ g ∈ B.GV k (r - j), x a g = y a g) (hx' : ∀ a, ∀ g ∈ B.GV k (r - j), x' a g = y' a g) :
    KB.pairJ (D.formLev T s j w) ys x x' = KB.pairJ (D.formLev T s j w) ys y y' := by
  exact pairJ_congrGV (D.formLev T s j w) (fun x x' y y' hx hx' => formLev_congrGV T s j w x x' y y' hx hx')
    ys x y x' y' hx hx'

end levels

end Formalism.FourierDecayAlt.P.PBG
