import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdAlg

variable {R : Type*} [Ring R]

def cont (D e : ℕ → R) (a : ℕ) : ℕ → R
  | 0 => 1
  | 1 => D a
  | n + 2 => D (a + n + 1) * cont D e a (n + 1) - e (a + n + 1) * cont D e a n

theorem cont_zero (D e : ℕ → R) (a : ℕ) : cont D e a 0 = 1 := rfl

theorem cont_one (D e : ℕ → R) (a : ℕ) : cont D e a 1 = D a := rfl

theorem cont_two (D e : ℕ → R) (a n : ℕ) :
    cont D e a (n + 2) = D (a + n + 1) * cont D e a (n + 1) - e (a + n + 1) * cont D e a n := rfl

theorem cont_top (D e : ℕ → R) (hDe : ∀ i j, i + 1 ≤ j → D j * e i = e i * D j)
    (hee : ∀ i j, e i * e j = e j * e i) :
    ∀ n a, cont D e a (n + 2) = cont D e (a + 1) (n + 1) * D a - e (a + 1) * cont D e (a + 2) n
  | 0, a => by
    rw [cont_two, cont_one, cont_one, cont_zero, cont_zero, add_zero]
  | 1, a => by
    show cont D e a 3 = cont D e (a + 1) 2 * D a - e (a + 1) * cont D e (a + 2) 1
    have eA : cont D e a 3 = D (a + 2) * (D (a + 1) * D a - e (a + 1) * 1) - e (a + 2) * D a := rfl
    have eB : cont D e (a + 1) 2 = D (a + 2) * D (a + 1) - e (a + 2) * 1 := rfl
    rw [eA, eB, cont_one]
    have hc := hDe (a + 1) (a + 2) (by omega)
    simp only [mul_one, mul_sub, sub_mul, ← mul_assoc, hc]
    abel
  | n + 2, a => by
    have h1 := cont_top D e hDe hee (n + 1) a
    have h0 := cont_top D e hDe hee n a
    have eA : cont D e a (n + 2 + 2) =
        D (a + n + 3) * cont D e a (n + 1 + 2) - e (a + n + 3) * cont D e a (n + 2) := by
      rw [cont_two]; rfl
    have eB : cont D e (a + 1) (n + 2 + 1) =
        D (a + n + 3) * cont D e (a + 1) (n + 2) - e (a + n + 3) * cont D e (a + 1) (n + 1) := by
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, cont_two, show a + 1 + (n + 1) + 1 = a + n + 3 by omega]
    have eC : cont D e (a + 2) (n + 2) =
        D (a + n + 3) * cont D e (a + 2) (n + 1) - e (a + n + 3) * cont D e (a + 2) n := by
      rw [cont_two, show a + 2 + n + 1 = a + n + 3 by omega]
    rw [eA, eB, eC, h1, h0]
    have hc1 := hDe (a + 1) (a + n + 3) (by omega)
    have hc2 := hee (a + n + 3) (a + 1)
    simp only [mul_sub, sub_mul, ← mul_assoc, hc1, hc2]
    abel

def topK (Dt e : ℕ → R) (r : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | m + 1 => ((topK Dt e r m).1 * Dt m - e (r - m) * (topK Dt e r m).2, (topK Dt e r m).1)

theorem topK_eq (D e : ℕ → R) (hDe : ∀ i j, i + 1 ≤ j → D j * e i = e i * D j)
    (hee : ∀ i j, e i * e j = e j * e i) (r : ℕ) (Dt : ℕ → R) (hDt : ∀ m < r, Dt m = D (r - m - 1)) :
    ∀ m, m ≤ r → (topK Dt e r m).1 = cont D e (r - m) m ∧
      (topK Dt e r m).2 = if m = 0 then 0 else cont D e (r - m + 1) (m - 1)
  | 0, _ => by simp [topK, cont_zero]
  | m + 1, hm => by
    obtain ⟨ih1, ih2⟩ := topK_eq D e hDe hee r Dt hDt m (by omega)
    simp only [topK]
    refine ⟨?_, ?_⟩
    · rw [ih1, ih2, hDt m (by omega)]
      rcases m with _ | m
      · simp only [if_true, mul_zero, sub_zero, cont_zero, one_mul, Nat.sub_zero]
        rfl
      · obtain ⟨a, rfl⟩ : ∃ a, r = a + m + 2 := ⟨r - m - 2, by omega⟩
        rw [if_neg (by omega), show a + m + 2 - (m + 1) = a + 1 by omega,
          show a + 1 - 1 = a by omega, show a + 1 + 1 = a + 2 by omega,
          show a + m + 2 - (m + 1 + 1) = a by omega, show m + 1 - 1 = m by omega, cont_top D e hDe hee m a]
    · rw [ih1, if_neg (by omega), show m + 1 - 1 = m by omega, show r - (m + 1) + 1 = r - m by omega]

theorem topK_conj (G : R) (Dw Dy e : ℕ → R) (r : ℕ) (hG : ∀ m < r, G * Dw m = Dy m * G)
    (hGe : ∀ j, G * e j = e j * G) :
    ∀ m, m ≤ r → G * (topK Dw e r m).1 = (topK Dy e r m).1 * G ∧
      G * (topK Dw e r m).2 = (topK Dy e r m).2 * G
  | 0, _ => by simp [topK]
  | m + 1, hm => by
    obtain ⟨ih1, ih2⟩ := topK_conj G Dw Dy e r hG hGe m (by omega)
    simp only [topK]
    refine ⟨?_, ih1⟩
    rw [mul_sub, ← mul_assoc, ih1, mul_assoc, hG m (by omega), ← mul_assoc G (e (r - m)), hGe,
      mul_assoc (e (r - m)) G, ih2, sub_mul, mul_assoc, mul_assoc]

def botA (D Cb Cbi : ℕ → R) (r : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | i + 1 => if i < r then
      (D i * (botA D Cb Cbi r i).1 - Cb i * (botA D Cb Cbi r i).2, Cbi i * (botA D Cb Cbi r i).1)
      else botA D Cb Cbi r i

theorem botA_eq (D Cb Cbi : ℕ → R) (r : ℕ) :
    ∀ i, i ≤ r → (botA D Cb Cbi r i).1 = cont D (fun j => Cb j * Cbi (j - 1)) 0 i ∧
      (botA D Cb Cbi r i).2 =
        if i = 0 then 0 else Cbi (i - 1) * cont D (fun j => Cb j * Cbi (j - 1)) 0 (i - 1)
  | 0, _ => by simp [botA, cont_zero]
  | i + 1, hi => by
    obtain ⟨ih1, ih2⟩ := botA_eq D Cb Cbi r i (by omega)
    simp only [botA, if_pos (show i < r by omega)]
    refine ⟨?_, ?_⟩
    · rw [ih1, ih2]
      rcases i with _ | i
      · simp only [if_true, mul_zero, sub_zero, cont_zero, mul_one]
        rfl
      · rw [if_neg (by omega), cont_two, show 0 + i + 1 = i + 1 by omega, show i + 1 - 1 = i by omega,
          mul_assoc]
    · rw [ih1, if_neg (by omega), show i + 1 - 1 = i by omega]

end Formalism.FourierDecayAlt.P.CutMP.TVCrdAlg
