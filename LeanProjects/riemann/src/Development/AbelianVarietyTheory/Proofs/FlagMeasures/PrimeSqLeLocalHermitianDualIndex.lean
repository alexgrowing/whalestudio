import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponents

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.IdxLower

theorem prime_le_relIndex {G : Type*} [AddCommGroup G] (H K : AddSubgroup G) (T : ℕ) (hT : T.Prime)
    (h0 : H.relIndex K ≠ 0) (hk : ∃ k ∈ K, k ∉ H) (hkill : ∀ k ∈ K, T • k ∈ H) :
    T ≤ H.relIndex K := by
  classical
  obtain ⟨k, hkK, hkH⟩ := hk
  have hq0 : (((⟨k, hkK⟩ : K) : K ⧸ H.addSubgroupOf K)) ≠ 0 := by
    intro h
    apply hkH
    have := (QuotientAddGroup.eq_zero_iff _).1 h
    simpa [AddSubgroup.mem_addSubgroupOf] using this
  have hqT : T • (((⟨k, hkK⟩ : K) : K ⧸ H.addSubgroupOf K)) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hkill k hkK
  have hord : addOrderOf (((⟨k, hkK⟩ : K) : K ⧸ H.addSubgroupOf K)) = T := by
    rcases hT.eq_one_or_self_of_dvd _ (addOrderOf_dvd_of_nsmul_eq_zero hqT) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) hq0
    · exact h
  have hdvd : T ∣ H.relIndex K := by
    rw [← hord, AddSubgroup.relIndex, AddSubgroup.index_eq_card]
    exact addOrderOf_dvd_natCard _
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd

theorem sq_le_relIndex {G : Type*} [AddCommGroup G] (A B C : AddSubgroup G) (T : ℕ) (hT : T.Prime)
    (h0 : A.relIndex B ≠ 0) (hAC : A ⊓ B ≤ C) (hCB : C ≤ B) (h1 : ∃ k ∈ B, k ∉ C)
    (h2 : ∃ k ∈ C, k ∉ A) (hkill : ∀ k ∈ B, T • k ∈ A) :
    T ^ 2 ≤ A.relIndex B := by
  have hmid : (A ⊓ B).relIndex C = A.relIndex C := by
    rw [← AddSubgroup.inf_relIndex_right (A ⊓ B) C, ← AddSubgroup.inf_relIndex_right A C,
      inf_assoc, inf_eq_right.2 hCB]
  have hAB : A.relIndex B = A.relIndex C * C.relIndex B := by
    rw [← AddSubgroup.inf_relIndex_right A B, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hAC hCB, hmid]
  have hAC0 : A.relIndex C ≠ 0 := by
    intro h; apply h0; rw [hAB, h, zero_mul]
  have hCB0 : C.relIndex B ≠ 0 := by
    intro h; apply h0; rw [hAB, h, mul_zero]
  have hle1 : T ≤ A.relIndex C := prime_le_relIndex A C T hT hAC0 h2 (fun k hk => hkill k (hCB hk))
  have hle2 : T ≤ C.relIndex B := prime_le_relIndex C B T hT hCB0 h1
    (fun k hk => hAC (AddSubgroup.mem_inf.2 ⟨hkill k hk, B.nsmul_mem hk T⟩))
  rw [hAB, sq]
  exact Nat.mul_le_mul hle1 hle2

theorem nsmul_mem_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (L M : Submodule (𝓞 E) (Fin n → E)) (T : ℕ)
    (h : ∀ x ∈ M, T • x ∈ L) : ∀ y ∈ loc v M, T • y ∈ loc v L := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨T • m, h m hm, ?_⟩
    funext i
    simp
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [smul_add]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem nsmul_mem_of_dual {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (T : ℕ)
    (h : ∀ y ∈ dualSet (σ : E →+* E) J L, (T : E) • y ∈ L) : ∀ x ∈ dualL σ J L, T • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => rw [← Nat.cast_smul_eq_nsmul E]; exact h y hy
  | zero => rw [smul_zero]; exact L.zero_mem
  | add x z _ _ hx hz => rw [smul_add]; exact L.add_mem hx hz
  | smul a x _ hx => rw [smul_comm]; exact L.smul_mem a hx

theorem sq_le_local_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup ≠ 0 → T ^ 2 ≤ (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT hsplit hrank hTL v hv sp hsp h1 hiff h0
  classical
  obtain ⟨_, _, hkillT, _, hnt⟩ := hTL
  have hkill : ∀ k ∈ (loc v (dualL cm.sig J L)).toAddSubgroup, T • k ∈ (loc v L).toAddSubgroup :=
    fun k hk => nsmul_mem_loc v L (dualL cm.sig J L) T (nsmul_mem_of_dual cm.sig J L T hkillT) k hk
  obtain ⟨x, hxB, hxA⟩ := hnt v hv
  have hsc := split_components F E cm n J hJ hdet v sp hsp h1
  have hnot1 : ¬ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) := by
    intro hP1
    exact hxA ((hsc.1 L x).2 ⟨hP1 x hxB, hiff.1 hP1 x hxB⟩)
  have hnot2 : ¬ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2) :=
    fun hP2 => hnot1 (hiff.2 hP2)
  push Not at hnot1 hnot2
  obtain ⟨y1, hy1B, hy1⟩ := hnot1
  obtain ⟨y2, hy2B, hy2⟩ := hnot2
  have heV : sp.symm (0, 1) ∈ intV E v := by
    have hI := (split_integral_local F E v sp h1 (sp.symm (0, 1))).2
    rw [RingEquiv.apply_symm_apply] at hI
    exact hI ⟨zero_mem _, one_mem _⟩
  have hcomp : ∀ b, sp (((⟨sp.symm (0, 1), heV⟩ : intV E v) • y2) b) = (0, (sp (y2 b)).2) := by
    intro b
    show sp (sp.symm (0, 1) * y2 b) = _
    rw [map_mul, RingEquiv.apply_symm_apply]
    ext <;> simp
  let C : AddSubgroup (Fin n → E ⊗[F] v.adicCompletion F) :=
    { carrier := {y | y ∈ loc v (dualL cm.sig J L) ∧ ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1}
      add_mem' := by
        intro a c ha hc
        obtain ⟨ha, za, hza, hza'⟩ := ha
        obtain ⟨hc, zc, hzc, hzc'⟩ := hc
        refine ⟨Submodule.add_mem _ ha hc, za + zc, Submodule.add_mem _ hza hzc, fun b => ?_⟩
        simp only [Pi.add_apply, map_add, Prod.fst_add, hza', hzc']
      zero_mem' := by
        refine ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, fun b => rfl⟩
      neg_mem' := by
        intro a ha
        obtain ⟨ha, za, hza, hza'⟩ := ha
        refine ⟨Submodule.neg_mem _ ha, -za, Submodule.neg_mem _ hza, fun b => ?_⟩
        simp only [Pi.neg_apply, map_neg, Prod.fst_neg, hza'] }
  have hAC : (loc v L).toAddSubgroup ⊓ (loc v (dualL cm.sig J L)).toAddSubgroup ≤ C := by
    intro y hy
    obtain ⟨hyA, hyB⟩ := AddSubgroup.mem_inf.1 hy
    exact ⟨hyB, y, hyA, fun b => rfl⟩
  have hCB : C ≤ (loc v (dualL cm.sig J L)).toAddSubgroup := fun y hy => hy.1
  have hBC : ∃ k ∈ (loc v (dualL cm.sig J L)).toAddSubgroup, k ∉ C := by
    refine ⟨y1, hy1B, fun hC => ?_⟩
    obtain ⟨z, hz, hz'⟩ := hC.2
    obtain ⟨b, hb⟩ := hy1 z hz
    exact hb (hz' b)
  have hCA : ∃ k ∈ C, k ∉ (loc v L).toAddSubgroup := by
    refine ⟨(⟨sp.symm (0, 1), heV⟩ : intV E v) • y2,
      ⟨Submodule.smul_mem _ _ hy2B, 0, Submodule.zero_mem _, fun b => ?_⟩, fun hA => ?_⟩
    · rw [hcomp b]; simp
    · obtain ⟨b, hb⟩ := hy2 _ hA
      apply hb
      rw [hcomp b]
  exact sq_le_relIndex _ _ C T hT h0 hAC hCB hBC hCA hkill

end GlobalTheory.St.G.IdxLower
