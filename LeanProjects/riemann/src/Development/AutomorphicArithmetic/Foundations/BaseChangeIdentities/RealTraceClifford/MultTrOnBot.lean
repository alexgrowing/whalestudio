import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WcfIso
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IsoSplit
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TraceRestrictSupDisjoint
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TrOnBot
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Sl2Core
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem mult_trOn_bot {V : Type} [AddCommGroup V] [Module ℂ V] (L : V →ₗ[ℂ] V) :
    trOn (⊥ : Submodule ℂ V) L = 0 := by
  exact trOn_bot L

private theorem mult_iso {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hF : UF F) {S₁ : Submodule ℂ V}
    (hS₁ : FiniteDimensional ℂ S₁) (hSt₁ : Stb F S₁) {B : Module.End ℂ V} {c₁ : FR n}
    {ν₁ ν : Wt n} (hB₁ : Cm F S₁ B) (hc₁ : IsCh F S₁ B c₁) (hne : hw F ν₁ ⊓ S₁ ≠ ⊥)
    (hoth : ∀ μ, μ ≠ ν₁ → hw F μ ⊓ S₁ = ⊥) (hν : StrictAnti (ν + rhoV n)) :
    cf (alt (rhoV n) * c₁) (ν + rhoV n) = trOn (hw F ν ⊓ S₁) B := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hdom := hwDom n V F hF S₁ hS₁ hSt₁ ν₁ x hx.2 hx0 hx.1
  have hanti := ((rearr n).2.2.2.2.1 ν₁ hdom).1
  have hsa : StrictAnti (ν₁ + rhoV n) := hanti.add_strictAnti (rearr n).2.2.1
  have hw1 := wcfIso n V F hF S₁ hS₁ hSt₁ B c₁ ν₁ hB₁ hc₁ hoth
  have hone := ((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 (ν₁ + rhoV n) hsa)
  rw [hw1, ((cfBasic n).2.2.2.1 (alt (ν₁ + rhoV n)) (alt (ν₁ + rhoV n)) (trOn (hw F ν₁ ⊓ S₁) B)
    (ν + rhoV n)).2]
  by_cases hνν : ν = ν₁
  · subst hνν
    rw [hone.1, mul_one]
  · have hne' : ν + rhoV n ≠ ν₁ + rhoV n := fun h => hνν (add_right_cancel h)
    rw [hone.2 _ hν hne', mul_zero, hoth ν hνν, mult_trOn_bot]

theorem UpperTheory.RealTr.mult :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ B c, Cm F S B → IsCh F S B c → ∀ ν : Wt n, StrictAnti (ν + rhoV n) →
      cf (alt (rhoV n) * c) (ν + rhoV n) = trOn (hw F ν ⊓ S) B := by
  intro n V _ _ F hF
  have cfB := cfBasic n
  have hwspB : ∀ (B : Module.End ℂ V), (∀ a b, B * F a b = F a b * B) →
      ∀ μ : Wt n, ∀ x ∈ wsp F μ, B x ∈ wsp F μ := by
    intro B hB μ x hx
    have hx' : IsWeight F μ x := hx
    show IsWeight F μ (B x)
    intro a
    have h1 : B (F a a x) = F a a (B x) := LinearMap.congr_fun (hB a a) x
    rw [← h1, hx' a, map_smul]
  have hwB : ∀ (B : Module.End ℂ V), (∀ a b, B * F a b = F a b * B) →
      ∀ μ : Wt n, ∀ x ∈ hw F μ, B x ∈ hw F μ := by
    intro B hB μ x hx
    have hx' : KHighest (fun _ => true) F μ x := hx
    show KHighest (fun _ => true) F μ (B x)
    refine ⟨?_, ?_⟩
    · intro a
      have h1 : B (F a a x) = F a a (B x) := LinearMap.congr_fun (hB a a) x
      rw [← h1, hx'.1 a, map_smul]
    · intro a b hab _
      have h1 : B (F a b x) = F a b (B x) := LinearMap.congr_fun (hB a b) x
      rw [← h1, hx'.2 a b hab rfl, map_zero]
  suffices H : ∀ k (S : Submodule ℂ V), Module.finrank ℂ S = k → FiniteDimensional ℂ S → Stb F S →
      ∀ B c, Cm F S B → IsCh F S B c → ∀ ν : Wt n, StrictAnti (ν + rhoV n) →
        cf (alt (rhoV n) * c) (ν + rhoV n) = trOn (hw F ν ⊓ S) B by
    intro S hfin
    exact H _ S rfl hfin
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hk hfin hstb B c hcm hch ν hν
  by_cases hS0 : S = ⊥
  · subst hS0
    rw [inf_bot_eq, mult_trOn_bot]
    by_contra hne
    obtain ⟨y, _, hy⟩ := cfB.2.2.2.2.2.1 _ _ _ hne
    exact hy (by rw [hch, inf_bot_eq, mult_trOn_bot])
  · obtain ⟨ν₁, S₁, S₂, hS1, hne1, hsup, hdisj, hst1, hst2, hcm12, hoth, hsplit⟩ :=
      isoSplit n V F hF S hfin hstb hS0
    haveI := hfin
    have hf1 : FiniteDimensional ℂ S₁ := Submodule.finiteDimensional_of_le (hsup ▸ le_sup_left)
    have hf2 : FiniteDimensional ℂ S₂ := Submodule.finiteDimensional_of_le (hsup ▸ le_sup_right)
    obtain ⟨hcm1, hcm2⟩ := hcm12 B hcm
    obtain ⟨c₁, hc1⟩ := chEx n V F hF S₁ hf1 hst1 B
    obtain ⟨c₂, hc2⟩ := chEx n V F hF S₂ hf2 hst2 B
    have hadd2 : ∀ (T : Submodule ℂ V), (∀ x ∈ T, B x ∈ T) →
        trOn (T ⊓ S₁ ⊔ T ⊓ S₂) B = trOn (T ⊓ S₁) B + trOn (T ⊓ S₂) B := by
      intro T hT
      haveI := hf1
      haveI := hf2
      exact (trAdd V B).1 _ _ inferInstance inferInstance (hdisj.mono inf_le_right inf_le_right)
        (fun x hx => Submodule.mem_inf.2 ⟨hT x (Submodule.mem_inf.1 hx).1, hcm1.2 x (Submodule.mem_inf.1 hx).2⟩)
        (fun x hx => Submodule.mem_inf.2 ⟨hT x (Submodule.mem_inf.1 hx).1, hcm2.2 x (Submodule.mem_inf.1 hx).2⟩)
    have hc : c = c₁ + c₂ := by
      apply cfB.2.2.1
      intro μ
      rw [(cfB.2.2.2.1 c₁ c₂ 0 μ).1, hch μ, hc1 μ, hc2 μ, (hsplit μ).1, hadd2 _ (hwspB B hcm.1 μ)]
    have hlt : Module.finrank ℂ S₂ < k := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq S₁ S₂
      rw [hsup, disjoint_iff.1 hdisj, finrank_bot, add_zero] at h
      have h1 : Module.finrank ℂ S₁ ≠ 0 := fun h0 => hS1 (Submodule.finrank_eq_zero.1 h0)
      omega
    have h2 := ih _ hlt S₂ rfl hf2 hst2 B c₂ hcm2 hc2 ν hν
    have h1 := mult_iso hF hf1 hst1 hcm1 hc1 hne1 hoth hν
    rw [hc, mul_add, (cfB.2.2.2.1 _ _ 0 _).1, h1, h2, (hsplit ν).2, hadd2 _ (hwB B hcm.1 ν)]
