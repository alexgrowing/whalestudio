import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SymOfMul
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RhoStrict
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DivSupp
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.aux₃ :
    ∀ (n : ℕ) (ν : Wt n), Dom ν → cf (chR n * alt (domC (ν - rhoV n) + rhoV n)) (ν + rhoV n) = 1 := by
  intro n ν hν
  obtain ⟨hR1, hR2, hR3, -, hR5, -⟩ := rearr n
  obtain ⟨hνA, hκD⟩ := hR5 ν hν
  obtain ⟨χ, hχS, hχ⟩ := divEx n (domC (ν - rhoV n)) hκD
  obtain ⟨hκA, ⟨w0, hw0⟩, -, -, hnsq⟩ := hR2 (ν - rhoV n)
  obtain ⟨c1, -, c3⟩ := divSupp n (domC (ν - rhoV n)) χ hκA hχ
  obtain ⟨hD2, -⟩ := chRF n
  obtain ⟨-, -, -, -, -, -, hA, -⟩ := cfBasic n
  have hx : StrictAnti (ν + rhoV n) := hνA.add_strictAnti hR3
  have hm : chR n * alt (domC (ν - rhoV n) + rhoV n) = alt ((2:ℝ) • rhoV n) * χ := by
    rw [← hχ, hD2]
    ring
  rw [hm, hA]
  rw [Finset.sum_eq_single 1]
  · have e1 : ν + rhoV n - ((2:ℝ) • rhoV n) ∘ ⇑(1 : Equiv.Perm (Fin n)) = ν - rhoV n := by
      funext a
      simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, Equiv.Perm.coe_one, id_eq,
        Pi.smul_apply, two_smul]
      ring
    rw [e1, ← hχS w0, ← hw0, c1]
    simp [sg]
  · intro w _ hw
    by_contra h
    have hne := right_ne_zero_of_mul h
    have hle := c3 hχS _ hne
    rw [hnsq] at hle
    obtain ⟨hle2, heq⟩ := hR1 (ν + rhoV n) (rhoV n) hx.antitone hR3.antitone w
    have hlt : ∑ a, (ν + rhoV n) a * rhoV n (w a) < ∑ a, (ν + rhoV n) a * rhoV n a :=
      lt_of_le_of_ne hle2 (fun h' => hw (heq hx hR3 h'))
    have hsum : ∑ a, rhoV n (w a) ^ 2 = ∑ a, rhoV n a ^ 2 := Equiv.sum_comp w (fun a => rhoV n a ^ 2)
    have hdiff : nsq (ν + rhoV n - ((2:ℝ) • rhoV n) ∘ ⇑w) - nsq (ν - rhoV n)
        = 4 * (∑ a, (ν + rhoV n) a * rhoV n a - ∑ a, (ν + rhoV n) a * rhoV n (w a))
          + 4 * (∑ a, rhoV n (w a) ^ 2 - ∑ a, rhoV n a ^ 2) := by
      simp only [nsq, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, Pi.smul_apply, two_smul]
      ring
    rw [hsum] at hdiff
    linarith
  · intro h
    exact absurd (Finset.mem_univ _) h
