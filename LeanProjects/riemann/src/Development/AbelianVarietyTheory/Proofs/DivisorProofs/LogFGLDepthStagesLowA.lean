import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypicalCurvesTangentAndBasesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootExtractionLemmaSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedBlocksMulInvIntegralUnitDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootTrickFinsetCurvesBlockInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RebasedTypicalCurvesIsBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanTangentOfTypeStatement

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.DepthStages

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem glue_ne_zero {ι : Type} {lab : Fin d → ι} {S : ι → Finset (Fin d)}
    {x : ι → Matrix (Fin d) (Fin d) C} (hx : ∀ i a b, x i a b ≠ 0 → a ∈ S i ∧ b ∈ S i)
    {a b : Fin d} (h : glue lab S x a b ≠ 0) : b = a ∨ (a ∈ S (lab a) ∧ b ∈ S (lab a)) := by
  simp only [glue, Matrix.of_apply] at h
  by_cases ha : a ∈ S (lab a)
  · rw [if_pos ha] at h
    exact Or.inr (hx _ _ _ h)
  · rw [if_neg ha] at h
    by_cases hab : a = b
    · exact Or.inl hab.symm
    · rw [if_neg hab] at h; exact absurd rfl h

theorem finrank_mod_le {M : Type} [AddCommGroup M] [Module C M] (W : Submodule C M)
    (t : Finset M) (A : Set M) (hA : ∀ w ∈ A, w ∈ W ⊔ Submodule.span C (t : Set M)) :
    Module.finrank C (Submodule.span C (W.mkQ '' A)) ≤ t.card := by
  classical
  have h1 : Submodule.span C (W.mkQ '' A) ≤ Submodule.span C ((t.image W.mkQ : Finset _) : Set (M ⧸ W)) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hA w hw)
    have hy0 : W.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero W).2 hy
    rw [map_add, hy0, zero_add, Finset.coe_image, Submodule.span_image]
    exact Submodule.mem_map_of_mem hz
  have : Module.Finite C (Submodule.span C ((t.image W.mkQ : Finset _) : Set (M ⧸ W))) :=
    Module.Finite.span_of_finite C (Finset.finite_toSet _)
  exact (Submodule.finrank_mono h1).trans
    ((finrank_span_finset_le_card _).trans Finset.card_image_le)

theorem exists_stage [IsAlgClosed C] [CharZero C] {p : ℕ} (hp : p.Prime) (hv : v (p : C) = 1)
    {h : ℕ} {ty : Fin d → ZMod h} {G : LogFGL v d} {γ : Fin d → Fin d → PowerSeries C}
    (hB : IsBasis G p ty γ) (S : ZMod h → Finset (Fin d)) (hS : ∀ i a, a ∈ S i → ty a = i)
    {n : ℕ} (hn : 1 ≤ n) (j : ℕ) (W : ZMod h → Submodule C (Fin d → C))
    (hW : ∀ i, ∃ t : Finset (Fin d → C), t.card ≤ j ∧
      ∀ a ∈ S i, G.lc p (γ a) n ∈ W i ⊔ Submodule.span C (t : Set (Fin d → C))) :
    ∃ (γ' : Fin d → Fin d → PowerSeries C) (D : ZMod h → Finset (Fin d)), IsBasis G p ty γ' ∧
      (∀ i, (D i).card ≤ j) ∧
      (∀ a m (U : Submodule C (Fin d → C)),
        (∀ b, (b = a ∨ (a ∈ S (ty a) ∧ b ∈ S (ty a))) → G.lc p (γ b) m ∈ U) →
          G.lc p (γ' a) m ∈ U) ∧
      (∀ a (U : Submodule C (Fin d → C)),
        (∀ b, (b = a ∨ (a ∈ S (ty a) ∧ b ∈ S (ty a))) → tangent (γ' b) ∈ U) →
          tangent (γ a) ∈ U) ∧
      ∀ a ∈ S (ty a), a ∉ D (ty a) → G.lc p (γ' a) n ∈ W (ty a) := by
  have key := fun i => GlobalTheory.T.root_trick_finset_curves_block_inverse GlobalTheory.T.root_extraction_lemma_sheaf C v p hp hv d h ty i G γ (S i) (fun a _ => hB.1 a)
    (fun a ha => hS i a ha ▸ hB.2.1 a) n j hn ((Fin d → C) ⧸ W i) (W i).mkQ (by
      obtain ⟨t, ht, hta⟩ := hW i
      have := finrank_mod_le (W i) t ((fun a => G.lc p (γ a) n) '' (S i : Set (Fin d)))
        (by rintro _ ⟨a, ha, rfl⟩; exact hta a ha)
      rw [Set.image_image] at this
      exact this.trans ht)
  choose x y D hDS hDj hxi hyi hxs hys hxy hLa using key
  obtain ⟨hXi, hXY, hXd⟩ := GlobalTheory.T.glued_blocks_mul_inv_integral_unit_det C v d (ZMod h) ty S x y hS hxs hys hxi hyi hxy
  obtain ⟨hB', htan, hlc⟩ := GlobalTheory.T.rebased_typical_curves_isBasis C v p hp hv d h ty G γ (glue ty S x) hB hXi hXd (by
    intro a b hab
    rcases glue_ne_zero hxs hab with rfl | ⟨-, hb⟩
    · rfl
    · exact hS _ _ hb)
  refine ⟨_, D, hB', hDj, fun a m U hU => ?_, fun a U hU => ?_, fun a ha haD => ?_⟩
  · rw [hlc]
    refine U.sum_mem fun b _ => ?_
    by_cases hab : glue ty S x a b = 0
    · rw [hab, zero_pow (pow_ne_zero _ hp.ne_zero), zero_smul]; exact U.zero_mem
    · exact U.smul_mem _ (hU b (glue_ne_zero hxs hab))
  · have hYX : glue ty S y * glue ty S x = 1 := mul_eq_one_comm.1 hXY
    have e : tangent (γ a) = ∑ b, glue ty S y a b • tangent (rebase G (glue ty S x) γ b) := by
      simp only [htan, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, ← Matrix.mul_apply, hYX, Matrix.one_apply, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [e]
    refine U.sum_mem fun b _ => ?_
    by_cases hab : glue ty S y a b = 0
    · rw [hab, zero_smul]; exact U.zero_mem
    · exact U.smul_mem _ (hU b (glue_ne_zero hys hab))
  · have := hLa (ty a) a ha haD
    rw [hlc]
    simp only [glue, Matrix.of_apply, if_pos ha]
    exact (Submodule.Quotient.mk_eq_zero _).1 this

end

end GlobalTheory.DepthStages

namespace GlobalTheory.DepthStages

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem odd_val_add_one {h : ℕ} (h0 : 0 < h) (hh : Even h) {i : ZMod h} (hi : Even i.val) :
    Odd (i + 1).val := by
  have : NeZero h := ⟨h0.ne'⟩
  have e : i + 1 = ((i.val + 1 : ℕ) : ZMod h) := by simp
  rw [e, ZMod.val_natCast, Nat.odd_iff, Nat.mod_mod_of_dvd _ hh.two_dvd]
  rw [Nat.even_iff] at hi; omega

theorem even_val_add_two {h : ℕ} (h0 : 0 < h) (hh : Even h) {i : ZMod h} (hi : Even i.val) :
    Even (i + 2).val := by
  have : NeZero h := ⟨h0.ne'⟩
  have e : i + 2 = ((i.val + 2 : ℕ) : ZMod h) := by simp
  rw [e, ZMod.val_natCast, Nat.even_iff, Nat.mod_mod_of_dvd _ hh.two_dvd]
  rw [Nat.even_iff] at hi; omega

def StageInv (G : LogFGL v d) (p : ℕ) {h : ℕ} (ty : Fin d → ZMod h) (j K : ℕ)
    (γ : Fin d → Fin d → PowerSeries C) (dp : Fin d → ℤ) : Prop :=
  IsBasis G p ty γ ∧ (∀ a, -1 ≤ dp a ∧ dp a ≤ K) ∧ (∀ a, Odd (ty a).val → dp a = -1) ∧
    (∀ i : ZMod h, Even i.val → ∀ l : ℤ, l < K →
      (Finset.univ.filter fun a => ty a = i ∧ dp a = l).card ≤ j) ∧
    ∀ a, 0 ≤ dp a → G.lc p (γ a) 1 = 0 ∧
      G.lc p (γ a) 2 ∈ Submodule.span C
        (Set.range fun b : {b // ty b = ty a + 2 ∧ dp a - 1 ≤ dp b} => tangent (γ b.1))

theorem exists_stageInv_zero [IsAlgClosed C] [CharZero C] {p : ℕ} (hp : p.Prime)
    (hv : v (p : C) = 1) {h : ℕ} (h0 : 0 < h) (hh : Even h) {ty : Fin d → ZMod h} {G : LogFGL v d}
    {γ : Fin d → Fin d → PowerSeries C} (hB : IsBasis G p ty γ) {j : ℕ}
    (hj : ∀ i : ZMod h, Odd i.val → (Finset.univ.filter fun a => ty a = i).card ≤ j) :
    ∃ (γ' : Fin d → Fin d → PowerSeries C) (dp : Fin d → ℤ), StageInv G p ty j 0 γ' dp := by
  classical
  obtain ⟨γ', D, hB', hD, -, -, hW⟩ := exists_stage hp hv hB
    (fun i => Finset.univ.filter fun a => ty a = i ∧ Even i.val)
    (fun i a ha => (Finset.mem_filter.1 ha).2.1) (le_refl 1) j (fun _ => ⊥) (by
      intro i
      by_cases hi : Even i.val
      · refine ⟨(Finset.univ.filter fun c => ty c = i + 1).image fun c => Pi.single c (1 : C),
          Finset.card_image_le.trans (hj _ (odd_val_add_one h0 hh hi)), fun a ha => ?_⟩
        have hai : ty a = i := (Finset.mem_filter.1 ha).2.1
        rw [bot_sup_eq, ← Finset.univ_sum_single (G.lc p (γ a) 1)]
        refine Submodule.sum_mem _ fun c _ => ?_
        by_cases hc : ty c = i + 1
        · have e : (Pi.single c (G.lc p (γ a) 1 c) : Fin d → C) =
              G.lc p (γ a) 1 c • (Pi.single c (1 : C) : Fin d → C) := by
            rw [← Pi.single_smul, smul_eq_mul, mul_one]
          rw [e]
          refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
          simp only [Finset.coe_image]
          exact ⟨c, by simpa using hc, rfl⟩
        · rw [(hB.2.1 a).2 1 c (by rw [hai]; simpa using hc), Pi.single_zero]
          exact Submodule.zero_mem _
      · exact ⟨∅, by simp, fun a ha => absurd (Finset.mem_filter.1 ha).2.2 hi⟩)
  refine ⟨γ', fun a => if Even (ty a).val ∧ a ∉ D (ty a) then 0 else -1, hB', fun a => ?_,
    fun a ha => ?_, fun i hi l hl => ?_, fun a ha => ?_⟩
  · dsimp only; split_ifs <;> simp
  · exact if_neg fun hc => (Nat.not_even_iff_odd.2 ha) hc.1
  · refine (Finset.card_le_card fun a ha => ?_).trans (hD i)
    obtain ⟨-, rfl, hal⟩ := Finset.mem_filter.1 ha
    by_contra haD
    dsimp only at hal
    rw [if_pos ⟨hi, haD⟩] at hal
    simp only [Nat.cast_zero] at hl
    omega
  · have hc : Even (ty a).val ∧ a ∉ D (ty a) := by
      by_contra hc
      simp only [if_neg hc] at ha
      omega
    refine ⟨(Submodule.mem_bot C).1 (hW a (by simpa using hc.1) hc.2), ?_⟩
    refine Submodule.span_mono ?_ (GlobalTheory.T.mem_span_tangent_of_type_of_isBasis C v p d h ty G γ' hB' (ty a + 2) _ fun c hc' =>
      (hB'.2.1 a).2 2 c (by simpa using hc'))
    rintro _ ⟨b, rfl⟩
    refine ⟨⟨b.1, b.2, ?_⟩, rfl⟩
    dsimp only
    rw [if_pos hc]
    split_ifs <;> simp

theorem exists_stageInv_succ [IsAlgClosed C] [CharZero C] {p : ℕ} (hp : p.Prime)
    (hv : v (p : C) = 1) {h : ℕ} (h0 : 0 < h) (hh : Even h) {ty : Fin d → ZMod h} {G : LogFGL v d}
    {j K : ℕ} {γ : Fin d → Fin d → PowerSeries C} {dp : Fin d → ℤ}
    (hI : StageInv G p ty j K γ dp) :
    ∃ (γ' : Fin d → Fin d → PowerSeries C) (dp' : Fin d → ℤ), StageInv G p ty j (K + 1) γ' dp' := by
  classical
  obtain ⟨hB, hr, ho, hc, hl⟩ := hI
  have hev : ∀ a, 0 ≤ dp a → Even (ty a).val := fun a ha => by
    by_contra hne
    have := ho a (Nat.not_even_iff_odd.1 hne)
    omega
  obtain ⟨γ', D, hB', hD, hlc, htan, hW⟩ := exists_stage hp hv hB
    (fun i => Finset.univ.filter fun a => ty a = i ∧ dp a = K)
    (fun i a ha => (Finset.mem_filter.1 ha).2.1) (n := 2) (by norm_num) j
    (fun i => Submodule.span C
      (Set.range fun b : {b // ty b = i + 2 ∧ (K : ℤ) ≤ dp b} => tangent (γ b.1))) (by
      intro i
      by_cases hi : Even i.val
      · refine ⟨(Finset.univ.filter fun b => ty b = i + 2 ∧ dp b = K - 1).image
            fun b => tangent (γ b),
          Finset.card_image_le.trans (hc _ (even_val_add_two h0 hh hi) _ (by omega)),
          fun a ha => ?_⟩
        obtain ⟨-, rfl, haK⟩ := Finset.mem_filter.1 ha
        refine Submodule.span_le.2 ?_ (hl a (by omega)).2
        rintro _ ⟨b, rfl⟩
        obtain ⟨b, hb1, hb2⟩ := b
        by_cases hbK : (K : ℤ) ≤ dp b
        · exact Submodule.mem_sup_left (Submodule.subset_span ⟨⟨b, hb1, hbK⟩, rfl⟩)
        · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
          simp only [Finset.coe_image]
          exact ⟨b, by simpa using ⟨hb1, by omega⟩, rfl⟩
      · refine ⟨∅, by simp, fun a ha => ?_⟩
        obtain ⟨-, rfl, haK⟩ := Finset.mem_filter.1 ha
        exact absurd (hev a (by omega)) hi)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlc htan hW
  set dp' : Fin d → ℤ := fun a => if dp a = K ∧ a ∉ D (ty a) then K + 1 else dp a with hdp'
  have hge : ∀ a, dp a ≤ dp' a := fun a => by
    simp only [hdp']; split_ifs with hc' <;> omega
  have hspan : ∀ (t : ZMod h) (l l' : ℤ), l' ≤ l → l' ≤ K →
      Submodule.span C (Set.range fun b : {b // ty b = t ∧ l ≤ dp b} => tangent (γ b.1)) ≤
      Submodule.span C (Set.range fun b : {b // ty b = t ∧ l' ≤ dp' b} => tangent (γ' b.1)) := by
    intro t l l' hll hl'
    rw [Submodule.span_le]
    rintro _ ⟨⟨b, hb1, hb2⟩, rfl⟩
    refine htan b _ fun c hcb => Submodule.subset_span ⟨⟨c, ?_⟩, rfl⟩
    have := hge c
    rcases hcb with rfl | ⟨-, hc1, hc2⟩
    · exact ⟨hb1, by omega⟩
    · exact ⟨hc1.trans hb1, by omega⟩
  refine ⟨γ', dp', hB', fun a => ?_, fun a ha => ?_, fun i hi l hlK => ?_, fun a ha => ?_⟩
  · have := hr a
    simp only [hdp']; push_cast; split_ifs <;> omega
  · have := ho a ha
    simp only [hdp']; rw [if_neg (by omega), this]
  · push_cast at hlK
    by_cases hlK' : l = K
    · refine (Finset.card_le_card fun a ha => ?_).trans (hD i)
      obtain ⟨-, rfl, hal⟩ := Finset.mem_filter.1 ha
      by_contra haD
      simp only [hdp'] at hal
      split_ifs at hal with h1
      · omega
      · exact h1 ⟨by omega, haD⟩
    · refine (Finset.card_le_card fun a ha => ?_).trans (hc i hi l (by omega))
      obtain ⟨-, hai, hal⟩ := Finset.mem_filter.1 ha
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hai, ?_⟩
      simp only [hdp'] at hal
      split_ifs at hal with h1
      · omega
      · exact hal
  · have ha0 : 0 ≤ dp a := by
      simp only [hdp'] at ha
      split_ifs at ha with h1 <;> omega
    refine ⟨(Submodule.mem_bot C).1 (hlc a 1 ⊥ fun b hb => (Submodule.mem_bot C).2
      (hl b ?_).1), ?_⟩
    · rcases hb with rfl | ⟨-, -, hb⟩ <;> omega
    · by_cases h1 : dp a = K ∧ a ∉ D (ty a)
      · have e : dp' a = K + 1 := if_pos h1
        exact hspan _ K _ (by omega) (by omega) (hW a h1.1 h1.2)
      · have e : dp' a = dp a := if_neg h1
        have := hr a
        refine hlc a 2 _ fun b hb => ?_
        rcases hb with rfl | ⟨haK, hb1, hb2⟩
        · exact hspan _ _ _ (by omega) (by omega) (hl b ha0).2
        · have hb := (hl b (by omega)).2
          rw [← hb1]
          exact hspan _ _ _ (by omega) (by omega) hb

end

end GlobalTheory.DepthStages

namespace GlobalTheory.DepthStages

theorem conclusion_of_stageInv {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d h : ℕ}
    {G : LogFGL v d} {p : ℕ} {ty : Fin d → ZMod h} {j K : ℕ} {γ : Fin d → Fin d → PowerSeries C}
    {dp : Fin d → ℤ} (hI : StageInv G p ty j K γ dp) :
    IsBasis G p ty γ ∧ (∀ a, -1 ≤ dp a ∧ dp a ≤ K) ∧ (∀ a, Odd (ty a).val → dp a = -1) ∧
      (∀ i : ZMod h, Even i.val →
        (Finset.univ.filter fun a => ty a = i ∧ dp a < K).card ≤ (K + 1) * j) ∧
      ∀ a, 0 ≤ dp a → G.lc p (γ a) 1 = 0 ∧
        G.lc p (γ a) 2 ∈ Submodule.span C
          (Set.range fun b : {b // dp a - 1 ≤ dp b} => tangent (γ b.1)) := by
  obtain ⟨hB, hr, ho, hc, hl⟩ := hI
  refine ⟨hB, hr, ho, fun i hi => ?_, fun a ha => ?_⟩
  · have hsub : (Finset.univ.filter fun a => ty a = i ∧ dp a < K) ⊆
        (Finset.Icc (-1 : ℤ) (K - 1)).biUnion
          (fun l => Finset.univ.filter fun a => ty a = i ∧ dp a = l) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨dp a, ⟨(hr a).1, by omega⟩, ha.1, rfl⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
    refine (Finset.sum_le_sum (g := fun _ => j) fun l hl' => hc i hi l ?_).trans ?_
    · simp only [Finset.mem_Icc] at hl'; omega
    · rw [Finset.sum_const, smul_eq_mul, Int.card_Icc]
      have : (K - 1 + 1 - -1 : ℤ).toNat = K + 1 := by omega
      rw [this]
  · obtain ⟨h1, h2⟩ := hl a ha
    refine ⟨h1, Submodule.span_mono ?_ h2⟩
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b.1, b.2.2⟩, rfl⟩

end GlobalTheory.DepthStages

namespace GlobalTheory.DepthStages

theorem lowA_statement : LowAStatement := by
  intro C _ _ _ v p hp _ hv d h h0 hh ty G μ j K hj
  obtain ⟨γ₀, hγ₀⟩ := (GlobalTheory.T.typicalCurveEigenspace_and_basisExists.2 C v p hp hv d h h0 ty G μ).1
  have key : ∃ (γ : Fin d → Fin d → PowerSeries C) (dp : Fin d → ℤ), StageInv G p ty j K γ dp := by
    induction K with
    | zero => exact exists_stageInv_zero hp hv h0 hh hγ₀ hj
    | succ K ih =>
      obtain ⟨γ, dp, hI⟩ := ih
      exact exists_stageInv_succ hp hv h0 hh hI
  obtain ⟨γ, dp, hI⟩ := key
  exact ⟨γ, dp, conclusion_of_stageInv hI⟩

end GlobalTheory.DepthStages
