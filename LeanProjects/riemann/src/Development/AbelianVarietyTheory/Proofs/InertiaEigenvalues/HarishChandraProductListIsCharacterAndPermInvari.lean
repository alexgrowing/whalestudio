import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionExteriorProductAssocCommStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionCharacterRestrictionDecompStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLqPerm

theorem isChar_one {G : Type} [Group G] : IsChar (fun _ : G => (1 : ℂ)) := by
  refine ⟨FDRep.of (Representation.trivial ℂ G ℂ), fun x => ?_⟩
  change LinearMap.trace ℂ ℂ ((Representation.trivial ℂ G ℂ) x) = 1
  simp [Representation.trivial, LinearMap.trace_id]

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

variable {g : ℕ} [Fact g.Prime]

theorem isChar_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsChar (hcL L (degL L)) := by
  induction L with
  | nil => exact isChar_one
  | cons p L ih =>
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    exact ((GlobalTheory.T.harishChandra_induction_character_restriction_decomp g p.1 (degL L) (degL (p :: L)) hdeg).1 p.2 (hcL L (degL L))
      (hL p (by simp)) (ih fun q hq => hL q (by simp [hq])))

theorem degL_perm {L L' : List (Pc g)} (h : L.Perm L') : degL L = degL L' := by
  unfold degL
  exact (h.map _).sum_eq

theorem hc_congr_mid (a : ℕ) (α : Gn g a → ℂ) (F : (m : ℕ) → Gn g m → ℂ) (n m m' : ℕ) (h : m = m') :
    hc a m α (F m) n = hc a m' α (F m') n := by subst h; rfl

theorem hc_congr_left (c : ℕ) (γ : Gn g c → ℂ) (F : (m : ℕ) → Gn g m → ℂ) (n m m' : ℕ) (h : m = m') :
    hc m c (F m) γ n = hc m' c (F m') γ n := by subst h; rfl

theorem hcL_perm {L L' : List (Pc g)} (h : L.Perm L') :
    (∀ p ∈ L, IsChar p.2) → ∀ n, n = degL L → hcL L n = hcL L' n := by
  induction h with
  | nil => intro _ n _; rfl
  | cons x h ih =>
    rename_i L₁ L₂
    intro hc1 n hn
    rw [hcL_cons, hcL_cons, ih (fun q hq => hc1 q (by simp [hq])) _ rfl]
    exact hc_congr_mid x.1 x.2 (hcL L₂) n _ _ (degL_perm h)
  | swap x y L₁ =>
    intro hc1 n hn
    have hx : IsClass x.2 := isClass_of_isChar (hc1 x (by simp))
    have hy : IsClass y.2 := isClass_of_isChar (hc1 y (by simp))
    have hL : IsClass (hcL L₁ (degL L₁)) :=
      isClass_of_isChar (isChar_hcL L₁ fun q hq => hc1 q (by simp [hq]))
    have hn' : n = y.1 + x.1 + degL L₁ := by rw [hn]; simp [degL]; omega
    have hn'' : n = x.1 + y.1 + degL L₁ := by rw [hn']; omega
    have e1 : degL (x :: L₁) = x.1 + degL L₁ := by simp [degL]
    have e2 : degL (y :: L₁) = y.1 + degL L₁ := by simp [degL]
    simp only [hcL_cons]
    rw [hc_congr_mid y.1 y.2 (fun m => hc x.1 (degL L₁) x.2 (hcL L₁ (degL L₁)) m) n _ _ e1,
      hc_congr_mid x.1 x.2 (fun m => hc y.1 (degL L₁) y.2 (hcL L₁ (degL L₁)) m) n _ _ e2]
    rw [← (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g y.1 x.1 (degL L₁) n y.2 x.2 _ hy hx hL).1 hn',
      ← (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g x.1 y.1 (degL L₁) n x.2 y.2 _ hx hy hL).1 hn'',
      (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g y.1 x.1 (degL L₁) (y.1 + x.1) y.2 x.2 _ hy hx hL).2.1 rfl]
    exact hc_congr_left (degL L₁) (hcL L₁ (degL L₁)) (fun m => hc x.1 y.1 x.2 y.2 m) n _ _ (Nat.add_comm _ _)
  | trans h₁ h₂ ih₁ ih₂ =>
    intro hc1 n hn
    rw [ih₁ hc1 n hn, ih₂ (fun q hq => hc1 q (h₁.mem_iff.mpr hq)) n (hn.trans (degL_perm h₁))]

end GlobalTheory.GLqPerm

theorem GlobalTheory.gl_list_product_perm_char : ∀ (g : ℕ) [Fact g.Prime] (L L' : List (Pc g)) (n : ℕ), n = degL L → (∀ p ∈ L, IsChar p.2) → IsChar (hcL L n) ∧ (L.Perm L' → hcL L n = hcL L' n) := by
  intro g _ L L' n hn hL
  subst hn
  exact ⟨GlobalTheory.GLqPerm.isChar_hcL L hL, fun h => GlobalTheory.GLqPerm.hcL_perm h hL _ rfl⟩
