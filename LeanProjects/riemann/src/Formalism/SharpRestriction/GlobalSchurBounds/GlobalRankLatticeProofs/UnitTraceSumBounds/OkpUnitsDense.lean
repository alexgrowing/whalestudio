import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhNormOfUnits
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SplitZeroOf

namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.Ext NumberField

def PhNormOK (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p →
      Simeq (g.phAt (g.mulBy (tauK D g.lam (a : D.host.K)) (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (tauK D g.lam (a : D.host.K) * tauKc D g.lam (a : D.host.K)) * g.phAt (Xv ()))

def OkpUnitsDense (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → ∀ α ∈ OKp D lam, ‖α.1‖ = 1 → ‖α.2‖ = 1 →
    α ∈ closure {x | ∃ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p ∧
      x = (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K))}

def OkpTwoUnits2 (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 →
    ∀ α ∈ OKp D lam, ∃ β ∈ OKp D lam, ∃ γ ∈ OKp D lam,
      ‖β.1‖ = 1 ∧ ‖β.2‖ = 1 ∧ ‖γ.1‖ = 1 ∧ ‖γ.2‖ = 1 ∧ α = β + γ

theorem phNorm_of (H1 : PhNormOfUnits) (H2 : PhNormClosed) (D : D7) (hOK : PhNormOK D) (hd : OkpUnitsDense D)
    (hU : OkpTwoUnits2 D) (ht : OkpTrace D) (hN : OkpNorm D) (he : endInt D) (ha : addInt D) (hB : beBiadd D) :
    phNorm D := by
  have hsqK : D.host.conj D.host.sqd ∈ D.host.K := by
    unfold Formalism.HC.HostRaw.K
    rw [D.host.gal_sqd]
    exact mul_mem (intCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hsq : D.host.conj (D.host.conj D.host.sqd) = D.host.sqd := by
    have hu : ∀ u : ℤˣ, (u : ℤ) * u = 1 := fun u => by
      first
      | exact Int.units_coe_mul_self u
      | (rw [← Units.val_mul, Int.units_mul_self, Units.val_one])
      | (rcases Int.units_eq_one_or u with h | h <;> simp [h])
    rw [D.host.gal_sqd, map_mul, map_intCast, D.host.gal_sqd, ← mul_assoc, ← Int.cast_mul, hu,
      Int.cast_one, one_mul]
  have hmemK : ∀ y : D.host.E, y ∈ D.host.K →
      D.host.conj y ∈ D.host.K ∧ D.host.conj (D.host.conj y) = y := by
    clear H1 H2 hOK hd hU ht hN he ha hB
    unfold Formalism.HC.HostRaw.K at hsqK ⊢
    intro y hy
    induction hy using IntermediateField.adjoin_induction
    all_goals simp_all [Set.mem_singleton_iff, map_add, map_mul, map_inv₀, map_neg, AlgEquiv.commutes,
      add_mem, mul_mem, inv_mem, neg_mem, IntermediateField.algebraMap_mem]
  have hQ : ∀ x : D.host.E, D.host.φ₀ x ∈ Qbar := by
    intro x
    have hx : IsIntegral ℚ (D.host.φ₀ x) :=
      (Algebra.IsIntegral.isIntegral (R := ℚ) x).map D.host.φ₀.toRatAlgHom
    first
    | exact hx
    | exact (mem_algebraicClosure_iff' (F := ℚ)).2 hx
    | exact mem_algebraicClosure_iff.2 hx.isAlgebraic
  have hL : ∀ {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : D.host.E),
      lamC lam (D.host.φ₀ x) = lam ⟨D.host.φ₀ x, hQ x⟩ := by
    intro p _ lam x
    unfold lamC
    rw [dif_pos (hQ x)]
  have key : ∀ {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
      (∀ α ∈ OKp D lam, ∀ β ∈ OKp D lam, α + β ∈ OKp D lam) ∧
      (∀ α ∈ OKp D lam, ∀ β ∈ OKp D lam, α * β ∈ OKp D lam) ∧
      ((2 : ℂ_[p]), (2 : ℂ_[p])) ∈ OKp D lam ∧
      (∀ α ∈ OKp D lam, α.swap ∈ OKp D lam) := by
    intro p _ lam
    let ψ : D.host.E →+* Qbar := D.host.φ₀.codRestrict Qbar hQ
    let ι : 𝓞 D.host.K →+* D.host.E :=
      (algebraMap D.host.K D.host.E).comp (algebraMap (𝓞 D.host.K) D.host.K)
    let F : 𝓞 D.host.K →+* ℂ_[p] × ℂ_[p] :=
      RingHom.prod ((lam.comp ψ).comp ι)
        ((lam.comp ψ).comp ((D.host.conj : D.host.E →+* D.host.E).comp ι))
    have hF : ∀ a : 𝓞 D.host.K, F a = (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K)) := by
      intro a
      unfold tauK tauKc
      rw [hL, hL]
      rfl
    have hR : OKp D lam = closure ((F.range : Subring (ℂ_[p] × ℂ_[p])) : Set (ℂ_[p] × ℂ_[p])) := by
      unfold OKp
      congr 1
      ext x
      simp only [Set.mem_range, SetLike.mem_coe, RingHom.mem_range, hF]
    have hcl : OKp D lam = ((F.range.topologicalClosure : Subring _) : Set (ℂ_[p] × ℂ_[p])) := by
      rw [hR]
      first
      | rfl
      | exact (Subring.coe_topologicalClosure _).symm
      | exact (Subring.topologicalClosure_coe _).symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro α hα β hβ
      rw [hcl] at hα hβ ⊢
      exact add_mem hα hβ
    · intro α hα β hβ
      rw [hcl] at hα hβ ⊢
      exact mul_mem hα hβ
    · have e : ((2 : ℂ_[p]), (2 : ℂ_[p])) = 1 + 1 := by
        ext <;> norm_num
      rw [hcl, e]
      exact add_mem (one_mem _) (one_mem _)
    · intro α hα
      rw [hR] at hα ⊢
      refine map_mem_closure continuous_swap hα ?_
      intro x hx
      rw [SetLike.mem_coe, RingHom.mem_range] at hx ⊢
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨hc, hcc⟩ := hmemK ((a : D.host.K) : D.host.E) (a : D.host.K).2
      let z : D.host.K := ⟨D.host.conj ((a : D.host.K) : D.host.E), hc⟩
      have h1 : IsIntegral ℤ (a : D.host.K) := by
        first
        | exact a.2
        | exact NumberField.RingOfIntegers.isIntegral_coe a
      have h2 := h1.map (((D.host.conj : D.host.E →+* D.host.E).comp
        (algebraMap D.host.K D.host.E)).toIntAlgHom)
      have hz : IsIntegral ℤ z :=
        (isIntegral_algHom_iff (x := z) ((algebraMap D.host.K D.host.E).toIntAlgHom)
          (algebraMap D.host.K D.host.E).injective).1 h2
      refine ⟨⟨z, hz⟩, ?_⟩
      rw [hF a]
      refine (hF _).trans (Prod.ext rfl ?_)
      show lamC lam (D.host.φ₀ (D.host.conj (D.host.conj ((a : D.host.K) : D.host.E)))) =
        lamC lam (D.host.φ₀ ((a : D.host.K) : D.host.E))
      rw [hcc]
  intro p _ cc δ g hAt hp
  obtain ⟨hadd, hmul, htwo, hswap⟩ := key g.lam
  have hOk : g.Ok := hAt.2.2.2.2
  apply H1 p g (OKp D g.lam) hOk hp htwo hswap hadd hmul (he p cc δ g hAt) (ha p cc δ g hAt).1
    (ht p g.lam) (hN p g.lam) (hU p g.lam hp) (hB p cc δ g hAt).1
  intro α hα h1 h2
  have hcl := hd p g.lam hp α hα h1 h2
  refine H2 p g _ hOk ?_ ?_ α hcl
  · rintro _ ⟨a, _, rfl⟩
    apply he p cc δ g hAt
    unfold OKp
    exact subset_closure ⟨a, rfl⟩
  · rintro _ ⟨a, hcop, rfl⟩
    exact hOK p cc δ g hAt hp a hcop

end Formalism.MainNotions.Ext.CutA
