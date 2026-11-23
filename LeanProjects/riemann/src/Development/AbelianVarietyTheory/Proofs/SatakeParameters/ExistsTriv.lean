import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.IntegralJetsPairing
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProjectiveOfFg

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField
open scoped Matrix

namespace GlobalTheory.RepEqAt

section General

open Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem exists_triv (hur : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)) {n : ℕ} (hn : 0 < n)
    (Λ : GenLat E N) (hU : Λ.Unimod) :
    ∃ γ : Matrix (Fin N) (Fin N) E, IsUnitaryM γ ∧ ∃ k : ℕ, Nat.Coprime k n ∧
      (∀ v ∈ Λ.La, k • (γ *ᵥ v) ∈ Formalism.L2.Pj.stdLat E N) ∧
      ∀ x ∈ Formalism.L2.Pj.stdLat E N, ∃ v ∈ Λ.La, γ *ᵥ v = k • x := by
  have hsub : ∀ a b : 𝓞 E ⧸ Ideal.span {((1 : ℕ) : 𝓞 E)}, a = b := fun a b => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨a - b, by simp⟩)
  have hiso : IsIsomMod Λ 1 0 := by
    refine ⟨fun y => ⟨0, funext fun j => hsub _ _⟩, fun v => ⟨fun _ => ⟨v, v.2, by simp⟩, fun _ => rfl⟩,
      fun v w x y _ _ => ?_⟩
    obtain ⟨a, ha⟩ := (hU w).1 w.2 v v.2
    refine ⟨a - ∑ j, x j * IsCMField.ringOfIntegersComplexConj E (y j), ?_⟩
    have e1 : ∑ j, (v : Fin N → E) j * IsCMField.complexConj E ((w : Fin N → E) j) = (a : E) := by
      refine Eq.trans ?_ ha.symm
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e2 : ∑ j, (x j : E) * IsCMField.complexConj E (y j : E) =
        ((∑ j, x j * IsCMField.ringOfIntegersComplexConj E (y j) : 𝓞 E) : E) := by
      change _ = algebraMap (𝓞 E) E _
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← IsCMField.coe_ringOfIntegersComplexConj]
    rw [e1, e2, Nat.cast_one, one_mul]
    exact (map_sub (algebraMap (𝓞 E) E) _ _).symm
  obtain ⟨γ, hγ, ⟨k, hk, h1, h2⟩, -⟩ :=
    GlobalTheory.RepTrivial.repExists E N hur 1 n one_pos hn Λ 0 hU hiso
  rw [GlobalTheory.GenusLatCompare.span_smul_le_iff] at h1 h2
  exact ⟨γ, hγ, k, hk, fun v hv => h1 _ ⟨v, hv, rfl⟩, fun x hx => h2 x hx⟩

end General

theorem repExS (D : D7) : GL3Theta.repExS D := by
  letI := D.host.cmStar
  intro n hn N L L₀
  have hur := Formalism.L2.Pj.unramBridge D.host.E (Formalism.L2.Pj.cmUnram_conj D)
  have hst : ∀ x : D.host.E, star x = IsCMField.complexConj D.host.E x := fun _ => rfl
  have hU : ∀ M : SDLat D.host.E N, (⟨M.1⟩ : Formalism.L2.Pj.GenLat D.host.E N).Unimod := fun M v => by
    refine (M.2.2.2 v).trans (forall₂_congr fun w _ => ?_)
    have e : ∀ x y : Fin N → D.host.E, IsCMField.complexConj D.host.E (stdH D.host.E N x y) =
        stdH D.host.E N y x := fun x y => by
      rw [← hst]
      simp [stdH, mul_comm]
    have c : ∀ x y : Fin N → D.host.E, stdH D.host.E N x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range →
        stdH D.host.E N y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
      rintro x y ⟨a, ha⟩
      refine ⟨IsCMField.ringOfIntegersComplexConj D.host.E a, ?_⟩
      rw [← e, ← ha]
      exact IsCMField.coe_ringOfIntegersComplexConj D.host.E a
    exact ⟨c w v, c v w⟩
  have hun : ∀ γ : Matrix (Fin N) (Fin N) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ →
      γ ∈ Matrix.unitaryGroup (Fin N) D.host.E := fun γ h => Matrix.mem_unitaryGroup_iff'.2 h
  obtain ⟨γ, hγ, k, hk, h1, h2⟩ := exists_triv hur hn _ (hU L)
  obtain ⟨δ, hδ, l, hl, h3, h4⟩ := exists_triv hur hn _ (hU L₀)
  have hδ1 : star δ * δ = 1 := Matrix.mem_unitaryGroup_iff'.1 (hun δ hδ)
  have hγ1 : star γ * γ = 1 := Matrix.mem_unitaryGroup_iff'.1 (hun γ hγ)
  have hinv : ∀ v, star δ *ᵥ (δ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hδ1, Matrix.one_mulVec]
  refine ⟨⟨star δ * γ, mul_mem (Unitary.star_mem (hun δ hδ)) (hun γ hγ)⟩, k * l,
    Nat.Coprime.mul_left hk hl, ?_, fun x hx => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu, e⟩ := h4 _ (h1 v hv)
    have : ((k * l : ℕ) : D.host.E) • ((star δ * γ) *ᵥ v) = u := by
      rw [← hinv u, e, Nat.cast_smul_eq_nsmul, ← Matrix.mulVec_mulVec, smul_smul, mul_comm l k,
        Matrix.mulVec_smul]
    exact this ▸ hu
  · obtain ⟨u, hu, e⟩ := h2 _ (h3 x hx)
    refine ⟨u, hu, ?_⟩
    change (star δ * γ) *ᵥ u = _
    rw [← Matrix.mulVec_mulVec, e, smul_smul, Matrix.mulVec_smul, hinv, Nat.cast_smul_eq_nsmul]

end GlobalTheory.RepEqAt
