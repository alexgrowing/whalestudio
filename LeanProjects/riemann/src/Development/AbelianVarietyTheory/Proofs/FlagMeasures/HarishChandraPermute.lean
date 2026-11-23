import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandValuesShiftStatement

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.DSSU.Chamber

variable {n : ℕ}

lemma blk_iff {ε : Fin n → Bool} {lam : Fin n → ℝ} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (hanti : StrictAnti (lam ∘ s))
    {x y : Fin n} (h : ε x = ε y) : lam y < lam x ↔ x < y := by
  have h' : ε (s (s.symm x)) = ε (s (s.symm y)) := by simpa using h
  have e1 := hanti.lt_iff_gt (a := s.symm y) (b := s.symm x)
  have e2 := GlobalTheory.DSId.PermK.lt_iff hs h'
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at e1 e2
  exact e1.trans e2.symm

lemma kType_iff {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hb : ∀ x y, ε x = ε y → (lam y < lam x ↔ x < y)) (μ : Fin n → ℝ) (S : Submodule ℂ H) :
    IsKTypeU ε lam σ μ S ↔ IsKTypeOf ε σ μ S := by
  have hA : ∀ ν : Fin n → ℝ, Above (fun a b => lam b < lam a ∧ ε a = ε b) ν μ ↔ CDom ε ν μ := by
    intro ν
    refine exists_congr fun c => and_congr ?_ ?_
    · refine forall_congr' fun a => forall_congr' fun b => imp_congr_right fun _ => ?_
      exact ⟨fun ⟨h1, h2⟩ => ⟨(hb a b h2).1 h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hb a b h2).2 h1, h2⟩⟩
    · exact ⟨fun h => by rw [h]; abel, fun h => by rw [← h]; abel⟩
  simp only [IsKTypeU, IsKTypeOf, Stable, IsKStableOn, hA]

lemma lowCh_comp (ε : Fin n → Bool) {lam : Fin n → ℝ} {s : Equiv.Perm (Fin n)} (hanti : StrictAnti (lam ∘ s)) :
    lowCh ε lam ∘ s = lowK (ε ∘ s) (lam ∘ s) := by
  funext a
  simp only [lowCh, lowK, rhoNh, rhoCh, rhoN, rhoC, Function.comp_apply, Pi.add_apply, Pi.sub_apply]
  have k : ∀ b, lam (s b) < lam (s a) ↔ a < b := fun b => hanti.lt_iff_gt
  have k' : ∀ b, lam (s a) < lam (s b) ↔ b < a := fun b => hanti.lt_iff_gt
  have c1 : (univ.filter fun b => a < b ∧ ε (s b) ≠ ε (s a)).card =
      (univ.filter fun b => lam b < lam (s a) ∧ ε b ≠ ε (s a)).card :=
    Finset.card_equiv s (fun b => by simp [k])
  have c2 : (univ.filter fun b => b < a ∧ ε (s b) ≠ ε (s a)).card =
      (univ.filter fun b => lam (s a) < lam b ∧ ε b ≠ ε (s a)).card :=
    Finset.card_equiv s (fun b => by simp [k'])
  have c3 : (univ.filter fun b => a < b ∧ ε (s b) = ε (s a)).card =
      (univ.filter fun b => lam b < lam (s a) ∧ ε b = ε (s a)).card :=
    Finset.card_equiv s (fun b => by simp [k])
  have c4 : (univ.filter fun b => b < a ∧ ε (s b) = ε (s a)).card =
      (univ.filter fun b => lam (s a) < lam b ∧ ε b = ε (s a)).card :=
    Finset.card_equiv s (fun b => by simp [k'])
  rw [c1, c2, c3, c4]

lemma infChar_comp (ε : Fin n → Bool) (χ : Fin n → ℂ) (s : Equiv.Perm (Fin n)) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    HasInfChar ε (χ ∘ s) σ ↔ HasInfChar ε χ σ := by
  have h := fun k => (GlobalTheory.T.gelfand_values_shift n χ).2.2 s k
  simp only [HasInfChar, IsZEigen, h]

theorem vChamber : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (s : Equiv.Perm (Fin n)), (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) → StrictAnti (lam ∘ s) → IsHCU ε lam σ → IsHCDS (ε ∘ s) (lam ∘ s) (fun g => σ (g.submatrix s.symm s.symm)) := by
  intro n ε H _ _ σ lam s hs hanti hU
  obtain ⟨hI, hC, hE, hAb⟩ := hU
  have hb : ∀ x y, ε x = ε y → (lam y < lam x ↔ x < y) := fun x y h => blk_iff hs hanti h
  have P := GlobalTheory.DSId.PermK.permKType n ε s H σ hs
  have hlow := lowCh_comp ε hanti
  refine ⟨P.2.2.2.1.1 hI, ?_, ?_, ?_⟩
  · have h1 : HasInfChar ε ((fun a => (lam a : ℂ)) ∘ s) σ := (infChar_comp ε _ s σ).2 hC
    exact (P.2.2.2.2 _).2 h1
  · obtain ⟨S, hS, huniq⟩ := hE
    refine ⟨S, ?_, fun T hT => ?_⟩
    · rw [← hlow]
      exact (P.1 _ S).1 ((kType_iff hb _ S).1 hS)
    · rw [← hlow] at hT
      exact huniq T ((kType_iff hb _ T).2 ((P.1 _ T).2 hT))
  · intro μ S hS
    have e : (μ ∘ s.symm) ∘ s = μ := by funext a; simp
    have h1 : IsKTypeOf ε σ (μ ∘ s.symm) S := (P.1 _ S).2 (by rw [e]; exact hS)
    obtain ⟨c, hc, h2⟩ := hAb _ S ((kType_iff hb _ S).2 h1)
    refine ⟨fun a b => c (s a) (s b), fun a b h => hanti.lt_iff_gt.1 (hc _ _ h), ?_⟩
    rw [← hlow]
    funext x
    have h3 := congrFun h2 (s x)
    rw [← Equiv.sum_comp s] at h3
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Pi.add_apply, Finset.sum_apply] at h3 ⊢
    refine h3.trans (congrArg _ (Finset.sum_congr rfl fun a _ => ?_))
    rw [← Equiv.sum_comp s]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [root, Pi.single_apply]

end GlobalTheory.DSSU.Chamber

end
