import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechH0SectionsHypothesesLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace CechZerothCohomologySections

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

def pt {i : Fin (N + 1)} (hi : i ∈ support x) : Cech.Idx (support x) 0 :=
  ⟨⟨{i}, Finset.singleton_nonempty i, Finset.singleton_subset_iff.mpr hi⟩, Finset.card_singleton i⟩

theorem idx_ext {U : Finset (Fin (N + 1))} {i : ℕ} {K K' : Cech.Idx U i} (h : K.1.1 = K'.1.1) :
    K = K' :=
  Subtype.ext (Subtype.ext h)

theorem mem_sub_of_mem_secs (F : SubSystem S x E) {z : E} (hz : z ∈ F.secs) (I : Chart x) :
    z ∈ F.sub I :=
  (Submodule.mem_iInf _).mp hz I

theorem cocycle_coe_eq (F : SubSystem S x E) {s : Cech.Cochain (fun I => F.sub I) 0}
    (hs : Cech.d (fun I => F.sub I) F.res 0 s = 0) (K K' : Cech.Idx (support x) 0) :
    (s K : E) = (s K' : E) := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp K.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K'.2
  by_cases hab : a = b
  · subst hab; rw [idx_ext (ha.trans hb.symm)]
  have hsub : ({a, b} : Finset (Fin (N + 1))) ⊆ support x := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact K.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self _)
    · rw [Finset.mem_singleton.mp hz]
      exact K'.1.2.2 (by rw [hb]; exact Finset.mem_singleton_self _)
  let J : Cech.Idx (support x) 1 :=
    ⟨⟨{a, b}, Finset.insert_nonempty _ _, hsub⟩, Finset.card_pair hab⟩
  have ha' : a ∈ J.1.1 := Finset.mem_insert_self _ _
  have hb' : b ∈ J.1.1 := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have fa : Cech.face J ⟨a, ha'⟩ = K' := idx_ext (by
    change ({a, b} : Finset _).erase a = _
    rw [hb]; ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · rintro rfl; exact ⟨Ne.symm hab, Or.inr rfl⟩)
  have fb : Cech.face J ⟨b, hb'⟩ = K := idx_ext (by
    change ({a, b} : Finset _).erase b = _
    rw [ha]; ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · rintro rfl; exact ⟨hab, Or.inl rfl⟩)
  have hval : ∀ L L' : Cech.Idx (support x) 0, L = L' → (s L : E) = (s L' : E) := by
    rintro L L' rfl; rfl
  have h0 := congrArg (F.sub J.1).subtype (congrFun hs J)
  rw [Cech.d_apply, map_sum, Pi.zero_apply, map_zero] at h0
  have huniv : (Finset.univ : Finset J.1.1) = {⟨a, ha'⟩, ⟨b, hb'⟩} := by
    ext ⟨z, hz⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    exact (Finset.mem_insert.mp hz).imp id Finset.mem_singleton.mp
  have hne : (⟨a, ha'⟩ : J.1.1) ≠ ⟨b, hb'⟩ := fun h => hab (congrArg Subtype.val h)
  rw [huniv, Finset.sum_pair hne, map_zsmul, map_zsmul] at h0
  have h1 : Cech.sgn ({a, b} : Finset (Fin (N + 1))) a • (s K' : E) +
      Cech.sgn ({a, b} : Finset (Fin (N + 1))) b • (s K : E) = 0 := by
    rw [← hval _ _ fa, ← hval _ _ fb]; exact h0
  have hsum := Cech.sum_sgn_of_card_two (Finset.card_pair hab)
  rw [Finset.sum_pair hab] at hsum
  have hb2 : Cech.sgn ({a, b} : Finset (Fin (N + 1))) b =
      - Cech.sgn ({a, b} : Finset (Fin (N + 1))) a := by linarith
  rw [hb2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h1
  have hsq : Cech.sgn ({a, b} : Finset (Fin (N + 1))) a *
      Cech.sgn ({a, b} : Finset (Fin (N + 1))) a = 1 := by
    unfold Cech.sgn; rw [← mul_pow]; norm_num
  have h2 : (s K' : E) - (s K : E) = 0 := by
    rw [← one_smul ℤ ((s K' : E) - (s K : E)), ← hsq, mul_smul, h1, smul_zero]
  exact (sub_eq_zero.mp h2).symm

def constC (F : SubSystem S x E) : F.secs →ₗ[S] Cech.Cochain (fun I => F.sub I) 0 where
  toFun z K := ⟨z, mem_sub_of_mem_secs F z.2 K.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem constC_cocycle (F : SubSystem S x E) (z : F.secs) :
    Cech.d (fun I => F.sub I) F.res 0 (constC F z) = 0 :=
  Cech.d_zero_of_compat (v := fun I => (⟨z, mem_sub_of_mem_secs F z.2 I⟩ : F.sub I))
    (fun _ _ _ => rfl)

def toKer (F : SubSystem S x E) :
    F.secs →ₗ[S] LinearMap.ker (Cech.d (fun I => F.sub I) F.res 0) :=
  (constC F).codRestrict _ fun z => LinearMap.mem_ker.mpr (constC_cocycle F z)

theorem exists_mem_support (hx : x ≠ 0) : ∃ i, i ∈ support x := by
  by_contra h
  simp only [not_exists] at h
  exact hx (funext fun i => by_contra fun hi => h i ((mem_support x).mpr hi))

theorem toKer_bijective (F : SubSystem S x E) (hx : x ≠ 0) : Function.Bijective (toKer F) := by
  obtain ⟨i₀, hi₀⟩ := exists_mem_support hx
  refine ⟨fun z₁ z₂ h => ?_, fun s => ?_⟩
  · have := congrArg (fun t => ((t.1 (pt hi₀) : F.sub (pt hi₀).1) : E)) h
    exact Subtype.ext this
  · have hs := LinearMap.mem_ker.mp s.2
    have hz : (s.1 (pt hi₀) : E) ∈ F.secs := by
      refine Submodule.mem_iInf _ |>.mpr fun I => ?_
      obtain ⟨i, hi⟩ := I.2.1
      have hsup : i ∈ support x := I.2.2 hi
      rw [Submodule.restrictScalars_mem, cocycle_coe_eq F hs (pt hi₀) (pt hsup)]
      exact F.mono _ I (Finset.singleton_subset_iff.mpr hi) _ (s.1 (pt hsup)).2
    refine ⟨⟨_, hz⟩, Subtype.ext (funext fun K => Subtype.ext ?_)⟩
    exact cocycle_coe_eq F hs (pt hi₀) K

theorem proof : CechZerothCohomologySections.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F hx
  have hp : (Cech.bdry (fun I => F.sub I) F.res 0).comap
      (LinearMap.ker (Cech.d (fun I => F.sub I) F.res 0)).subtype = ⊥ := by
    rw [show Cech.bdry (fun I => F.sub I) F.res 0 = ⊥ from rfl, Submodule.comap_bot,
      Submodule.ker_subtype]
  exact ⟨(Submodule.quotEquivOfEqBot _ hp).trans
    (LinearEquiv.ofBijective (toKer F) (toKer_bijective F hx)).symm⟩

end CechZerothCohomologySections

end

end GroundTheory.Heights₂.Heights.Kleiman
