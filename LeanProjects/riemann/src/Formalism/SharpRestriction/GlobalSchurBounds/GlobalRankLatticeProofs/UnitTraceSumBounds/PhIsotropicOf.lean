import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeOfTwoIdentities
import Formalism.SharpRestriction.GlobalSchurBounds.StatementTranslationInvariantSeventh
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TestVectorMemSchwartzBruhat

namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.Ext

def OkpSwap (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ∀ α ∈ OKp D lam, α.swap ∈ OKp D lam

def OkpTrace (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ∀ α ∈ OKp D lam, ∃ n : ℤ_[p], α.1 + α.2 = zc n

def OkpNeg (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((-1 : ℂ_[p]), (-1 : ℂ_[p])) ∈ OKp D lam

def OkpTwo (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((2 : ℂ_[p]), (2 : ℂ_[p])) ∈ OKp D lam

def OkpDiff (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 →
    ∃ α ∈ OKp D lam, ‖α.1 - α.2‖ = if p = D.host.d then ((p : ℝ) ^ ((1 : ℝ) / 2))⁻¹ else 1

theorem okpSwap_holds (D : D7) : OkpSwap D := by
  intro p _ lam α hα
  have hsq : D.host.conj D.host.sqd ∈ D.host.K := by
    rw [Formalism.HC.HostRaw.conj_sqd]
    exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hK : ∀ x ∈ D.host.K, D.host.conj x ∈ D.host.K := by
    intro x hx
    have hle : (D.host.K).map (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) ≤ D.host.K := by
      show (IntermediateField.adjoin ℚ {D.host.sqd}).map
        (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) ≤ D.host.K
      rw [IntermediateField.adjoin_map, Set.image_singleton,
        IntermediateField.adjoin_simple_le_iff]
      exact hsq
    exact hle ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)
  have hint : ∀ a : NumberField.RingOfIntegers D.host.K, IsIntegral ℤ (D.host.conj ((a : D.host.K) : D.host.E)) := by
    intro a
    have h0 : IsIntegral ℤ ((a : D.host.K) : D.host.E) :=
      (NumberField.RingOfIntegers.isIntegral_coe a).map ((D.host.K).val.restrictScalars ℤ)
    exact h0.map ((D.host.conj : D.host.E →ₐ[ℚ] D.host.E).restrictScalars ℤ)
  have key : ∀ a : NumberField.RingOfIntegers D.host.K, ∃ b : NumberField.RingOfIntegers D.host.K,
      ((b : D.host.K) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
    intro a
    have hy : IsIntegral ℤ
        (⟨D.host.conj ((a : D.host.K) : D.host.E), hK _ (a : D.host.K).2⟩ : D.host.K) :=
      (isIntegral_algHom_iff ((D.host.K).val.restrictScalars ℤ)
        (fun x y h => Subtype.ext h)).1 (hint a)
    exact ⟨⟨⟨D.host.conj ((a : D.host.K) : D.host.E), hK _ (a : D.host.K).2⟩, hy⟩, rfl⟩
  have hmaps : Set.MapsTo Prod.swap
      (Set.range fun a : NumberField.RingOfIntegers D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K)))
      (Set.range fun a : NumberField.RingOfIntegers D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K))) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := key a
    refine ⟨b, ?_⟩
    simp only [Prod.swap_prod_mk, tauK, tauKc, hb, Formalism.HC.HostRaw.conj_conj]
  unfold OKp at hα ⊢
  exact map_mem_closure continuous_swap hα hmaps

theorem okpNeg_holds (D : D7) : OkpNeg D := by
  intro p _ lam
  have hQ : (-1 : ℂ) ∈ Qbar := neg_mem (one_mem _)
  have hl : lamC lam (-1 : ℂ) = -1 := by
    unfold lamC
    rw [dif_pos hQ]
    have e : (⟨-1, hQ⟩ : Qbar) = -1 := Subtype.ext (by first | rfl | simp | norm_num)
    rw [e, map_neg, map_one]
  have hc : D.host.conj (-1 : D.host.E) = -1 := by simp
  unfold OKp
  refine subset_closure ⟨-1, ?_⟩
  simp [tauK, tauKc, hc, hl]

theorem okpTwo_holds (D : D7) : OkpTwo D := by
  intro p _ lam
  have hQ : (2 : ℂ) ∈ Qbar := by
    first
      | norm_num
      | simp
      | (have h := add_mem (one_mem Qbar) (one_mem Qbar); rwa [one_add_one_eq_two] at h)
  have hl : lamC lam (2 : ℂ) = 2 := by
    unfold lamC
    rw [dif_pos hQ]
    have e : (⟨2, hQ⟩ : Qbar) = 1 + 1 := Subtype.ext (by
      first
        | (show (2 : ℂ) = ((1 : Qbar) : ℂ) + ((1 : Qbar) : ℂ); norm_num)
        | (push_cast; norm_num)
        | rfl)
    rw [e, map_add, map_one] <;> norm_num
  have hc : D.host.conj (2 : D.host.E) = 2 := by
    first
      | (rw [show (2 : D.host.E) = 1 + 1 by norm_num, map_add, map_one])
      | exact map_ofNat _ 2
  have hz : (((2 : NumberField.RingOfIntegers D.host.K) : D.host.K) : D.host.E) = 2 := by
    rw [show (2 : NumberField.RingOfIntegers D.host.K) = 1 + 1 by norm_num]
    first
      | (push_cast; norm_num)
      | simp
      | norm_num
  have hφ : D.host.φ₀ (2 : D.host.E) = 2 := by
    first
      | (rw [show (2 : D.host.E) = 1 + 1 by norm_num, map_add, map_one]; norm_num)
      | simp
  unfold OKp
  refine subset_closure ⟨2, ?_⟩
  simp only [tauK, tauKc, hz, hc, hφ, hl, Prod.mk.injEq, and_self]

theorem cube_of (H : CubeOfTwoIdentities) (D : D7) (h2 : cube2 D) (h3 : cube3 D) : cube D := by
  intro p _ cc δ g hA
  exact H p g hA.2.2.2.2 (h2 p cc δ g hA) (h3 p cc δ g hA)

theorem phGram_of (H : PhGramG) (D : D7) (he : endInt D) (ha : addInt D) (hn : phNorm D)
    (hb : beConj D) (hB : beBiadd D) : GL3r7.PhGram D := by
  intro p _ cc δ g hA hp
  have key := H p g (OKp D g.lam) hA.2.2.2.2 (fun α hα => okpSwap_holds D p g.lam α hα)
    (he p cc δ g hA) (ha p cc δ g hA).1 (hn p cc δ g hA hp) (hb p cc δ g hA hp)
    (hB p cc δ g hA).1
  intro κ _ k A hA'
  exact key κ k A hA'

theorem phUnitary_of (HU : GramUnitEq) (D : D7) (hG : GL3r7.PhGram D) : PhUnitary D := by
  intro p _ cc δ g hA hp n de hde horth
  have h1 := hG p cc δ g hA hp (Fin n) n de hde
  rwa [HU p g hA.2.2.2.2 n de horth] at h1

theorem phIsotropic_of (HI : GramIsoEq) (D : D7) (hG : GL3r7.PhGram D) : PhIsotropic D := by
  intro p _ cc δ g hA hp n r b hb _ hiso
  have h1 := hG p cc δ g hA hp (Fin n) r b hb
  rwa [HI p g hA.2.2.2.2 (Fin n) r b hiso] at h1

theorem phDual_of (HD : PhDualOfGram) (D : D7) (hG : GL3r7.PhGram D) : PhDual D := by
  intro p _ cc δ g hA hp κ ι _ _ b b' hb hb' hd
  exact HD p g (OKp D g.lam) hA.2.2.2.2
    (by
      intro κ' _ k A hA'
      exact hG p cc δ g hA hp κ' k A hA') κ ι b b' hb hb' hd

theorem jetsPh_of (HH : JetsHigh) (H1 : JetsOne) (H2 : JetsTwo) (D : D7) (hc : cube D) (hn : phNorm D)
    (hb : beConj D) (hdf : OkpDiff D) : jetsPh D := by
  intro p _ cc δ g hA hp
  have hok := hA.2.2.2.2
  obtain ⟨α₀, hα₀, hnorm⟩ := hdf p g.lam hp
  have hprod : ‖(α₀.1 - α₀.2) * g.jetPh 2‖ ≤ 1 :=
    H2 p g α₀.1 α₀.2 hok (hb p cc δ g hA hp α₀ hα₀)
  rw [norm_mul] at hprod
  refine ⟨fun i hi2 => ?_, fun α hα => H2 p g α.1 α.2 hok (hb p cc δ g hA hp α hα),
    fun hpd => ?_, fun hpd => ?_⟩
  · by_cases hi1 : i = 1
    · subst hi1
      have hn1 := hn p cc δ g hA hp ((-1 : ℂ_[p]), (-1 : ℂ_[p])) (okpNeg_holds D p g.lam)
      have hm : ((-1 : ℂ_[p]), (-1 : ℂ_[p])).1 * ((-1 : ℂ_[p]), (-1 : ℂ_[p])).2 = 1 := by
        norm_num
      rw [hm, map_one, one_mul] at hn1
      exact H1 p g hok hp hn1
    · exact HH p g hok (hc p cc δ g hA) i hi1 hi2
  · rw [if_neg hpd] at hnorm
    rw [hnorm, one_mul] at hprod
    exact hprod
  · rw [if_pos hpd] at hnorm
    rw [hnorm] at hprod
    have hpos : (0 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
    have h3 := mul_le_mul_of_nonneg_left hprod hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_one] at h3
    exact h3

set_option maxHeartbeats 400000 in
theorem beDiag_of (H : BeDiagG) (D : D7) (ht : OkpTrace D) (he : endInt D)
    (ha : addInt D) (hn : phNorm D) (hb : beConj D) (hB : beBiadd D) : beDiag D := by
  intro p _ cc δ g hA hp
  have h2 := hn p cc δ g hA hp ((2 : ℂ_[p]), (2 : ℂ_[p])) (okpTwo_holds D p g.lam)
  exact H p g (OKp D g.lam) hA.2.2.2.2 (fun α hα => okpSwap_holds D p g.lam α hα)
    (he p cc δ g hA) (ha p cc δ g hA).1 (fun α hα => ht p g.lam α hα) h2
    (hb p cc δ g hA hp) (hB p cc δ g hA).1

end Formalism.MainNotions.Ext.CutA
