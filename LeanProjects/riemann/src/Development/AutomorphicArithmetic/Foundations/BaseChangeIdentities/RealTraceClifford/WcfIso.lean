import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ChSymAnti
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TrOnZero
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.LapForm
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WcfForm
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IsoFacts
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Sl2Core
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.wcfIso :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ B c (ν : Wt n), Cm F S B → IsCh F S B c → (∀ μ, μ ≠ ν → hw F μ ⊓ S = ⊥) →
      alt (rhoV n) * c = trOn (hw F ν ⊓ S) B • alt (ν + rhoV n) := by
  intro n V _ _ F hF S hfin hstb B c ν hcm hch hother
  have cfB := cfBasic n
  by_cases hS : hw F ν ⊓ S = ⊥
  · have hbot : S = ⊥ := by
      by_contra hne
      obtain ⟨x, hxS, hx0, μ, hμ⟩ := Formalism.REAL.kHiExist V n (fun _ => true) F S hfin
        (Formalism.REAL.glRel_kRel _ _ hF.gl) (fun a b _ => hF.unit a b) (fun a b _ => hstb a b) hne
      have hmem : x ∈ hw F μ ⊓ S := ⟨hμ, hxS⟩
      by_cases hμν : μ = ν
      · subst hμν
        rw [hS] at hmem
        exact hx0 ((Submodule.mem_bot ℂ).1 hmem)
      · rw [hother μ hμν] at hmem
        exact hx0 ((Submodule.mem_bot ℂ).1 hmem)
    have hc0 : ∀ μ, cf c μ = 0 := by
      intro μ
      rw [hch μ, hbot, inf_bot_eq, trOn_bot]
    have hz : ∀ x : Wt n, cf (0 : FR n) x = 0 := by
      intro x
      have h := (cfB.2.2.2.1 0 0 0 x).2
      simpa using h
    rw [hS, trOn_bot, zero_smul]
    apply cfB.2.2.1
    intro x
    rw [hz]
    by_contra hne
    obtain ⟨y, _, hy⟩ := cfB.2.2.2.2.2.1 _ _ x hne
    exact hy (hc0 _)
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    have hdom := hwDom n V F hF S hfin hstb ν x hx.2 hx0 hx.1
    have hanti := ((rearr n).2.2.2.2.1 ν hdom).1
    obtain ⟨hcas, hmaj, hweq⟩ := isoFacts n V F hF S hfin hstb ν hother
    obtain ⟨t, ht1, ht2⟩ := chLap n V F hF S hfin hstb B c _ hcm hch hcas
    have key := wcfForm n c ν hanti (chSym n V F hF S hfin hstb B c hcm hch)
      (fun μ hμ => hmaj μ (fun h => hμ (by rw [hch μ, h, trOn_bot])))
      (fun y hy => by
        have h := lapForm n c t _ ht1 ht2 y hy
        have h' : ((nsq y : ℝ) : ℂ) = ((nsq (ν + rhoV n) : ℝ) : ℂ) := by
          rw [h]
          push_cast
          ring
        exact_mod_cast h')
    rw [key, hch ν, hweq]
