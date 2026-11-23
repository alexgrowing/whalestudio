import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WcfIso
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Sl2Core
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TrOnBot
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TraceRestrictSupDisjoint

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.irrCh :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → LocF F → ∀ ν : Wt n, hw F ν ≠ ⊥ → Dom ν ∧ ∃ (S : Submodule ℂ V) (c : FR n) (d : ℂ), FiniteDimensional ℂ S ∧ Stb F S ∧ IsCh F S 1 c ∧ d ≠ 0 ∧
      alt (rhoV n) * c = d • alt (ν + rhoV n) := by
  intro n V _ _ F hU hL ν hν
  obtain ⟨x, hxh, hx0⟩ := (Submodule.ne_bot_iff _).1 hν
  obtain ⟨S0, hS0f, hxS0, hS0⟩ := hL x
  set S : Submodule ℂ V := Formalism.REAL.kSpan (fun _ => true) F x with hSdef
  have hSle : S ≤ S0 := by
    intro y hy
    exact (Submodule.mem_sInf.1 hy) S0 ⟨hxS0, fun a b _ z hz => hS0 a b z hz⟩
  have hxS : x ∈ S := Submodule.mem_sInf.2 (fun T hT => hT.1)
  have hSf : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSle
  have hSs : Stb F S := by
    intro a b y hy
    exact Submodule.mem_sInf.2 (fun T hT => hT.2 a b rfl y (Submodule.mem_sInf.1 hy T hT))
  have hD : Dom ν := hwDom n V F hU S hSf hSs ν x hxS hx0 hxh
  obtain ⟨c, hc⟩ := chEx n V F hU S hSf hSs 1
  have hCm : Cm F S 1 := ⟨fun a b => by rw [one_mul, mul_one], fun y hy => by simpa using hy⟩
  have hKR : Formalism.REAL.KRel (fun _ => true) F := Formalism.REAL.glRel_kRel _ F hU.gl
  have hKU : Formalism.REAL.KUnit (fun _ => true) F := fun a b _ y z => hU.unit a b y z
  have hoth : ∀ μ : Wt n, μ ≠ ν → hw F μ ⊓ S = ⊥ := by
    intro μ hμ
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_bot]
    rcases Formalism.REAL.kHiUniq V n (fun _ => true) F ν μ x y hKR hKU hxh hy.2 hy.1 with h | h
    · exact h
    · exact absurd h.1 hμ
  have key := wcfIso n V F hU S hSf hSs 1 c ν hCm hc hoth
  have hIf : FiniteDimensional ℂ (hw F ν ⊓ S : Submodule ℂ V) :=
    Submodule.finiteDimensional_of_le (inf_le_right : hw F ν ⊓ S ≤ S)
  have htr : trOn (hw F ν ⊓ S) (1 : Module.End ℂ V) = (Module.finrank ℂ (hw F ν ⊓ S : Submodule ℂ V) : ℂ) :=
    (trAdd V (1 : Module.End ℂ V)).2.2.2 _ hIf
  refine ⟨hD, S, c, trOn (hw F ν ⊓ S) 1, hSf, hSs, hc, ?_, key⟩
  rw [htr, Nat.cast_ne_zero]
  intro h0
  rw [Submodule.finrank_eq_zero] at h0
  have : x ∈ hw F ν ⊓ S := ⟨hxh, hxS⟩
  rw [h0, Submodule.mem_bot] at this
  exact hx0 this
