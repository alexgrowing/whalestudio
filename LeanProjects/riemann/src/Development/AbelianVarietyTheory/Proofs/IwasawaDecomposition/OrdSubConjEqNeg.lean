import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdFNonnegOfIsInteger
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.ChiIdeal

open GlobalTheory.Mem.Chr.DetOrd

section General

variable {L : Type} [Field L] [NumberField L]

theorem frac_of_mul_eq_one {A B : Submodule (𝓞 L) L} (h : A * B = 1) :
    IsFractional (𝓞 L)⁰ A ∧ ∃ k : Lˣ, (k : L) ∈ A := by
  refine ⟨FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit (IsUnit.of_mul_eq_one B h)), ?_⟩
  have hA : A ≠ ⊥ := by
    rintro rfl
    rw [Submodule.bot_mul] at h
    have : (1 : L) ∈ (⊥ : Submodule (𝓞 L) L) := h ▸ Submodule.one_le.1 le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).1 this)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff A).1 hA
  exact ⟨Units.mk0 x hx0, hx⟩

theorem ordF_le_iff (w : HeightOneSpectrum (𝓞 L)) (a b : Lˣ) :
    ordF w a ≤ ordF w b ↔ w.valuation L (b : L) ≤ w.valuation L (a : L) := by
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hb : w.valuation L (b : L) ≠ 0 := by simp
  unfold ordF
  rw [neg_le_neg_iff, WithZero.log_le_log hb ha]

theorem exists_gen {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (w : HeightOneSpectrum (𝓞 L)) :
    ∃ a : Lˣ, (a : L) ∈ A ∧ ordF w a = ordSub w A ∧ ∀ x ∈ A, w.valuation L x ≤ w.valuation L (a : L) := by
  obtain ⟨⟨a, ha, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  refine ⟨a, ha, e, fun x hx => ?_⟩
  by_cases h0 : x = 0
  · simp [h0]
  · have h1 := hl ⟨Units.mk0 x h0, hx, rfl⟩
    rw [← e, ordF_le_iff] at h1
    exact h1

theorem ordSub_mul {A B : Submodule (𝓞 L) L} (hA : IsFractional (𝓞 L)⁰ A) (a0 : Lˣ) (ha0 : (a0 : L) ∈ A)
    (hB : IsFractional (𝓞 L)⁰ B) (b0 : Lˣ) (hb0 : (b0 : L) ∈ B) (w : HeightOneSpectrum (𝓞 L)) :
    ordSub w (A * B) = ordSub w A + ordSub w B := by
  obtain ⟨a, ha, ea, hla⟩ := exists_gen hA a0 ha0 w
  obtain ⟨b, hb, eb, hlb⟩ := exists_gen hB b0 hb0 w
  rw [← ea, ← eb, ← ordF_mul']
  refine IsLeast.csInf_eq ⟨⟨a * b, Submodule.mul_mem_mul ha hb, rfl⟩, ?_⟩
  rintro n ⟨k, hk, rfl⟩
  rw [ordF_le_iff]
  refine Submodule.mul_induction_on (C := fun x => w.valuation L x ≤ w.valuation L ((a * b : Lˣ) : L)) hk
    (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [Units.val_mul, map_mul, map_mul]
    exact mul_le_mul' (hla x hx) (hlb y hy)
  · exact Valuation.map_add_le _ hx hy

theorem ordSub_one (w : HeightOneSpectrum (𝓞 L)) : ordSub w (1 : Submodule (𝓞 L) L) = 0 := by
  have h := ordSub_span_singleton w (1 : Lˣ)
  rw [Units.val_one, ← Submodule.one_eq_span] at h
  rw [h]
  simp [ordF]

theorem ordF_conj {c : L ≃+* L} {w w' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c w w') (k k' : Lˣ)
    (e : (k' : L) = c k) : ordF w' k' = ordF w k := by
  unfold ordF
  rw [e, h]

theorem ordSub_conj {c : L ≃+* L} {w w' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c w w') {A B : Submodule (𝓞 L) L}
    (hB : ∀ x, x ∈ B ↔ c x ∈ A) : ordSub w' A = ordSub w B := by
  unfold ordSub
  congr 1
  ext n
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h0 : c.symm k ≠ 0 := by simp
    refine ⟨Units.mk0 _ h0, (hB _).2 (by simpa using hk), (ordF_conj h _ _ (by simp)).symm⟩
  · rintro ⟨k, hk, rfl⟩
    have h0 : c k ≠ 0 := by simp
    exact ⟨Units.mk0 _ h0, (hB _).1 hk, ordF_conj h _ _ rfl⟩

theorem ordSub_conj_eq_neg {c : L ≃+* L} {w w' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c w w')
    {A B : Submodule (𝓞 L) L} (hB : ∀ x, x ∈ B ↔ c x ∈ A) (h1 : A * B = 1) : ordSub w' A = -ordSub w A := by
  obtain ⟨fA, a, ha⟩ := frac_of_mul_eq_one h1
  obtain ⟨fB, b, hb⟩ := frac_of_mul_eq_one ((mul_comm B A).trans h1)
  have h2 := ordSub_mul fA a ha fB b hb w
  rw [h1, ordSub_one, ← ordSub_conj h hB] at h2
  omega

variable {F : Type} [Field F] [NumberField F] [Algebra F L]

theorem prod_val_above (χ : HChar L) (hu : ∀ v, χ.UnrAt v) (ht : χ.TrivOn F)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (v : HeightOneSpectrum (𝓞 F)) : ∏ P ∈ aboveF (L := L) F v, χ.val P = 1 := by
  have h := ht.1 v (unif v)
  rw [HChar.resFin, MonoidHom.finset_prod_apply] at h
  rw [← h]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hP' : P.under (𝓞 F) = v := by simpa [aboveF] using hP
  rw [MonoidHom.comp_apply, GlobalTheory.HeckeProduct.locK_unr χ (hu P), hr, hP', ordF_unif_self, zpow_one]

theorem finprod_val_eq_one (χ : HChar L) (hv : ∀ v, ∏ P ∈ aboveF (L := L) F v, χ.val P = 1)
    (n : HeightOneSpectrum (𝓞 L) → ℤ) (hf : {w | n w ≠ 0}.Finite)
    (hn : ∀ w w', w'.under (𝓞 F) = w.under (𝓞 F) → n w' = n w) : ∏ᶠ w, χ.val w ^ n w = 1 := by
  classical
  have hm : ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L)),
      P ∈ aboveF (L := L) F v ↔ P.under (𝓞 F) = v := fun v P => by simp [aboveF]
  rw [finprod_eq_prod_of_mulSupport_subset _
    (s := (hf.toFinset.image fun w => w.under (𝓞 F)).biUnion (aboveF (L := L) F)), Finset.prod_biUnion]
  · refine Finset.prod_eq_one fun v hv' => ?_
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv'
    rw [Finset.prod_congr rfl (fun P hP => by rw [hn w P ((hm _ _).1 hP)]), Finset.prod_zpow, hv, one_zpow]
  · intro v _ v' _ hne
    refine Finset.disjoint_left.2 fun P h1 h2 => hne (((hm _ _).1 h1).symm.trans ((hm _ _).1 h2))
  · intro w hw
    have : n w ≠ 0 := fun h0 => hw (by simp [h0])
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨_, Finset.mem_image.2 ⟨w, hf.mem_toFinset.2 this, rfl⟩, (hm _ _).2 rfl⟩

theorem finprod_val_add (χ : HChar L) (n m : HeightOneSpectrum (𝓞 L) → ℤ) (hn : {w | n w ≠ 0}.Finite)
    (hm : {w | m w ≠ 0}.Finite) :
    ∏ᶠ w, χ.val w ^ (n w + m w) = (∏ᶠ w, χ.val w ^ n w) * ∏ᶠ w, χ.val w ^ m w := by
  simp only [zpow_add]
  exact finprod_mul_distrib (hn.subset fun w hw h0 => hw (by simp [h0])) (hm.subset fun w hw h0 => hw (by simp [h0]))

theorem finprod_val_congr (χ : HChar L) (hv : ∀ v, ∏ P ∈ aboveF (L := L) F v, χ.val P = 1)
    (n m : HeightOneSpectrum (𝓞 L) → ℤ) (hn : {w | n w ≠ 0}.Finite) (hm : {w | m w ≠ 0}.Finite)
    (h : ∀ w w', w'.under (𝓞 F) = w.under (𝓞 F) → n w' - m w' = n w - m w) :
    ∏ᶠ w, χ.val w ^ n w = ∏ᶠ w, χ.val w ^ m w := by
  have hd : {w | n w - m w ≠ 0}.Finite := (hn.union hm).subset fun w hw => by
    by_contra h0
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h0
    exact hw (by rw [h0.1, h0.2, sub_self])
  have h1 := finprod_val_add χ _ m hd hm
  rw [finprod_val_eq_one χ hv _ hd h, one_mul] at h1
  simpa using h1

theorem finite_toNat {n : HeightOneSpectrum (𝓞 L) → ℤ} (hn : {w | n w ≠ 0}.Finite) :
    {w | ((n w).toNat : ℤ) ≠ 0}.Finite :=
  hn.subset fun w hw h0 => hw (by simp [h0])

end General

theorem phase_sq_eq {a u : ℂ} (ha : a ≠ 0) (h : u * starRingEnd ℂ a = a) :
    (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = u := by
  have hc : starRingEnd ℂ a ≠ 0 := by simpa using ha
  rw [zpow_ofNat, div_pow, ← Complex.mul_conj', div_eq_iff (mul_ne_zero ha hc)]
  linear_combination (-a) * h

theorem exists_mul_conj_eq {L : Type} [Field L] (c : L →+* L) (hc : ∀ x, c (c x) = x) (hne : ∃ a, c a ≠ a)
    (z : L) (hz : z * c z = 1) : ∃ k : Lˣ, z * c (k : L) = k := by
  by_cases h : 1 + z = 0
  · obtain ⟨a, ha⟩ := hne
    refine ⟨Units.mk0 (a - c a) (sub_ne_zero.2 ha.symm), ?_⟩
    have hz1 : z = -1 := by linear_combination h
    rw [Units.val_mk0, map_sub, hc, hz1]
    ring
  · refine ⟨Units.mk0 (1 + z) h, ?_⟩
    rw [Units.val_mk0, map_add, map_one]
    linear_combination hz

theorem isChi_chiId : ∀ (D : D7) (χ : HChar D.host.E), IsChiPsi D.host χ → Formalism.MainNotions.TaylorLogMetric.IsChi D (chiId χ) := by
  intro D χ hχ
  obtain ⟨c, hc, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have hv := prod_val_above χ hχ.unr hχ.triv hr
  have hpl := fun w w' => (under_eq_iff_conjPl c hcm.rank hcm.ne w w').1
  refine ⟨?_, ?_⟩
  · rintro A B ⟨A', hA', hA⟩ ⟨B', hB', hB⟩
    obtain ⟨fA, a, ha⟩ := frac_of_mul_eq_one hA
    obtain ⟨fB, b, hb⟩ := frac_of_mul_eq_one hB
    have nA := ordSub_finite fA a ha
    have nB := ordSub_finite fB b hb
    have nAB : {w | ordSub w A + ordSub w B ≠ 0}.Finite := (nA.union nB).subset fun w hw => by
      by_contra h0
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h0
      exact hw (by rw [h0.1, h0.2, add_zero])
    unfold chiId
    rw [← Units.val_mul]
    congr 1
    simp only [← zpow_natCast, ordSub_mul fA a ha fB b hb]
    rw [← finprod_val_add χ _ _ (finite_toNat nA) (finite_toNat nB)]
    refine finprod_val_congr χ hv _ _ (finite_toNat nAB) ((nA.union nB).subset fun w hw => ?_) fun w w' h => ?_
    · by_contra h0
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h0
      exact hw (by simp [h0.1, h0.2])
    · rcases hpl w w' h with rfl | h
      · rfl
      · rw [ordSub_conj_eq_neg h (fun x => (hA' x).trans (by rw [← hc]; rfl)) hA,
          ordSub_conj_eq_neg h (fun x => (hB' x).trans (by rw [← hc]; rfl)) hB]
        omega
  · letI := D.host.cmStar
    intro z
    have hcmf : IsCMField D.host.E := D.host.isCMField_hostE
    have hcc : ∀ x, IsCMField.complexConj D.host.E x = D.host.conj x := fun x => bridge_star_holds D.R D.host x
    have hinv : ∀ x, c (c x) = x := fun x => by
      rw [hc, hc, ← hcc, ← hcc, IsCMField.complexConj_apply_apply]
    have hz : (z : D.host.E) * c (z : D.host.E) = 1 := by
      rw [hc, ← bridge_star_holds D.R D.host]
      exact z.2.2
    obtain ⟨k, hk⟩ := exists_mul_conj_eq (c : D.host.E →+* D.host.E) hinv
      (by by_contra hn; push Not at hn; exact hcm.ne (AlgEquiv.ext hn)) z hz
    have hk' : (z : D.host.E) * c (k : D.host.E) = k := hk
    have z0 : (z : D.host.E) ≠ 0 := left_ne_zero_of_mul_eq_one hz
    have k0 : c (k : D.host.E) ≠ 0 := by simp
    have hu : Units.mk0 _ z0 * Units.mk0 _ k0 = k := Units.ext hk'
    have e1 := chiId_span_singleton χ (Units.mk0 _ z0)
    rw [Units.val_mk0] at e1
    have e2 : ∏ᶠ w, χ.val w ^ (ordF w (Units.mk0 _ z0)).toNat = ∏ᶠ w, χ.val w ^ ordF w k := by
      simp only [← zpow_natCast]
      refine finprod_val_congr χ hv _ _ (finite_toNat (ordF_finite _)) (ordF_finite _) fun w w' h => ?_
      rcases hpl w w' h with rfl | h
      · rfl
      · have a1 := ordF_mul' w (Units.mk0 _ z0) (Units.mk0 _ k0)
        have a2 := ordF_mul' w' (Units.mk0 _ z0) (Units.mk0 _ k0)
        have a3 := ordF_conj h k (Units.mk0 _ k0) rfl
        have a4 := ordF_conj h (Units.mk0 _ k0) k (hinv _).symm
        rw [hu] at a1 a2
        omega
    have e3 := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hχ.unr v) k
    simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at e3
    rw [mul_comm, mul_eq_one_iff_eq_inv] at e3
    rw [e1, e2, e3, Units.val_inv_eq_inv_val, hχ.inf k, ← Finset.prod_inv_distrib]
    refine (Fintype.prod_equiv D.eTau _ _ fun τ => ?_).symm
    congr 1
    refine (phase_sq_eq ((map_ne_zero _).2 k.ne_zero) ?_).symm
    have hcj : embPsi D.host (D.eTau τ) (D.host.conj (k : D.host.E)) =
        starRingEnd ℂ (embPsi D.host (D.eTau τ) (k : D.host.E)) := Formalism.HC.HostAx.conjE_apply _ _ _
    rw [← hcj, ← hc]
    exact (map_mul (embPsi D.host (D.eTau τ)) _ _).symm.trans (congrArg _ hk')

end GlobalTheory.Mem.ChiIdeal
