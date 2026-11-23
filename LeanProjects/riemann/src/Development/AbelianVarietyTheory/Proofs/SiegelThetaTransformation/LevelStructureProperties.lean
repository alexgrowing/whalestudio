import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (omegaStd)

namespace GlobalTheory.SW.Lev

section Ring

variable {O : Type} [CommRing O] {𝔞 𝔟 : Ideal O} {s t : O}

theorem cop_iff : IsCoprime (Ideal.span {s}) 𝔞 ↔ ∃ a, ∃ m ∈ 𝔞, a * s + m = 1 := by
  rw [Ideal.isCoprime_iff_exists]
  constructor
  · rintro ⟨x, hx, m, hm, h⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact ⟨a, m, hm, h⟩
  · rintro ⟨a, m, hm, h⟩
    exact ⟨_, Ideal.mem_span_singleton'.2 ⟨a, rfl⟩, m, hm, h⟩

theorem cop_one : IsCoprime (Ideal.span {(1 : O)}) 𝔞 := cop_iff.2 ⟨1, 0, zero_mem _, by simp⟩

theorem cop_mul (hs : IsCoprime (Ideal.span {s}) 𝔞) (ht : IsCoprime (Ideal.span {t}) 𝔞) :
    IsCoprime (Ideal.span {s * t}) 𝔞 := by
  rw [← Ideal.span_singleton_mul_span_singleton]; exact hs.mul_left ht

theorem cop_of_sub_one (h : s - 1 ∈ 𝔞) : IsCoprime (Ideal.span {s}) 𝔞 :=
  cop_iff.2 ⟨1, -(s - 1), neg_mem h, by ring⟩

theorem cop_ne_zero (h𝔞 : 𝔞 ≠ ⊤) (hs : IsCoprime (Ideal.span {s}) 𝔞) : s ≠ 0 := by
  rintro rfl
  obtain ⟨a, m, hm, h⟩ := cop_iff.1 hs
  exact h𝔞 ((Ideal.eq_top_iff_one _).2 (by rw [← h]; simpa using hm))

theorem cop_glue (h : IsCoprime 𝔞 𝔟) (hs : IsCoprime (Ideal.span {s}) 𝔞)
    (ht : IsCoprime (Ideal.span {t}) 𝔟) :
    ∃ a b, IsCoprime (Ideal.span {a * s + b * t}) (𝔞 * 𝔟) := by
  obtain ⟨m, hm, m', hm', e⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨a, x, hx, e1⟩ := cop_iff.1 hs
  obtain ⟨b, y, hy, e2⟩ := cop_iff.1 ht
  refine ⟨m' * a, m * b, IsCoprime.mul_right (cop_of_sub_one ?_) (cop_of_sub_one ?_)⟩
  · have : m' * a * s + m * b * t - 1 = (b * t - 1) * m - m' * x := by
      linear_combination m' * e1 + e
    rw [this]; exact sub_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hx)
  · have : m' * a * s + m * b * t - 1 = (a * s - 1) * m' - m * y := by
      linear_combination m * e2 + e
    rw [this]; exact sub_mem (Ideal.mul_mem_left _ _ hm') (Ideal.mul_mem_left _ _ hy)

variable {M : Type} [AddCommGroup M] [Module O M]

def loc (𝔞 : Ideal O) (L : Submodule O M) : Submodule O M where
  carrier := {v | ∃ s, IsCoprime (Ideal.span {s}) 𝔞 ∧ s • v ∈ L}
  add_mem' := by
    rintro u v ⟨s, hs, hu⟩ ⟨t, ht, hv⟩
    refine ⟨s * t, cop_mul hs ht, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hu
    · rw [mul_smul]; exact L.smul_mem _ hv
  zero_mem' := ⟨1, cop_one, by simp⟩
  smul_mem' := by
    rintro c v ⟨s, hs, hv⟩
    exact ⟨s, hs, by rw [smul_comm]; exact L.smul_mem _ hv⟩

theorem le_loc (L : Submodule O M) : L ≤ loc 𝔞 L := fun v hv => ⟨1, cop_one, by simpa using hv⟩

theorem loc_mono {L L' : Submodule O M} (h : L ≤ L') : loc 𝔞 L ≤ loc 𝔞 L' :=
  fun _ ⟨s, hs, hv⟩ => ⟨s, hs, h hv⟩

theorem loc_loc {L : Submodule O M} {v : M} (hs : IsCoprime (Ideal.span {s}) 𝔞)
    (h : s • v ∈ loc 𝔞 L) : v ∈ loc 𝔞 L := by
  obtain ⟨t, ht, hv⟩ := h
  exact ⟨t * s, cop_mul ht hs, by rwa [mul_smul]⟩

theorem exists_mul_of_fg {L L' : Submodule O M} (hL : L.FG) (h : L ≤ loc 𝔞 L') :
    ∃ s, IsCoprime (Ideal.span {s}) 𝔞 ∧ ∀ v ∈ L, s • v ∈ L' := by
  classical
  obtain ⟨S, rfl⟩ := hL
  have hS : ∀ x ∈ S, ∃ s : O, IsCoprime (Ideal.span {s}) 𝔞 ∧ s • x ∈ L' := fun x hx =>
    h (Submodule.subset_span (Finset.mem_coe.2 hx))
  have key : ∀ T : Finset M,
      (∀ x ∈ T, ∃ s : O, IsCoprime (Ideal.span {s}) 𝔞 ∧ s • x ∈ L') →
      ∃ s : O, IsCoprime (Ideal.span {s}) 𝔞 ∧ ∀ x ∈ T, s • x ∈ L' := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, ?_, by simp⟩
      rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]
      exact isCoprime_one_left
    | insert a T _ ih =>
      intro hT
      obtain ⟨s, hs, hsT⟩ := ih fun x hx => hT x (Finset.mem_insert_of_mem hx)
      obtain ⟨t, ht, hta⟩ := hT a (Finset.mem_insert_self a T)
      refine ⟨s * t, ?_, ?_⟩
      · rw [← Ideal.span_singleton_mul_span_singleton]
        exact hs.mul_left ht
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · rw [mul_smul]
          exact L'.smul_mem s hta
        · rw [mul_comm, mul_smul]
          exact L'.smul_mem t (hsT x hx)
  obtain ⟨s, hs, hsS⟩ := key S hS
  refine ⟨s, hs, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem x hx => exact hsS x (Finset.mem_coe.1 hx)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L'.add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact L'.smul_mem c hx

theorem mem_of_loc {L N : Submodule O M} {v : M} (hv : v ∈ L) (hN : 𝔞 • L ≤ N)
    (h : v ∈ loc 𝔞 N) : v ∈ N := by
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨a, m, hm, e⟩ := cop_iff.1 hs
  rw [← one_smul O v, ← e, add_smul, mul_smul]
  exact add_mem (N.smul_mem _ h) (hN (Submodule.smul_mem_smul hm hv))

theorem nakayama {L N : Submodule O M} (hL : L.FG) (h : L ≤ N ⊔ 𝔞 • L) :
    ∃ s, IsCoprime (Ideal.span {s}) 𝔞 ∧ ∀ v ∈ L, s • v ∈ N := by
  obtain ⟨s, hs, hle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := 𝔞) (N := N) (N' := L) (P := L) hL le_rfl h
  exact ⟨s, cop_of_sub_one hs, fun v hv => hle (Submodule.smul_mem_pointwise_smul v s L hv)⟩

theorem smul_map_mem {L L' : Submodule O M} (f : M →ₗ[O] M) (h : ∀ v ∈ L, s • f v ∈ L') {v : M}
    (hv : v ∈ 𝔟 • L) : s • f v ∈ 𝔟 • L' := by
  refine Submodule.smul_induction_on hv (fun m hm x hx => ?_) fun x y hx hy => ?_
  · rw [map_smul, smul_comm]; exact Submodule.smul_mem_smul hm (h x hx)
  · rw [map_add, smul_add]; exact add_mem hx hy

theorem relIndex_eq {A B C : AddSubgroup M} (h : C ≤ A) (h' : A ≤ C ⊔ B ⊓ A) :
    B.relIndex A = B.relIndex C := by
  have e : A = C ⊔ B ⊓ A := le_antisymm h' (sup_le h inf_le_right)
  rw [← AddSubgroup.inf_relIndex_right B A]
  conv_lhs => congr; rfl; rw [e]
  rw [AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right, inf_assoc,
    inf_eq_right.2 h, AddSubgroup.inf_relIndex_right]

theorem exists_gen [IsDedekindDomain O] (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) (h𝔟' : 𝔟 ≠ ⊤) :
    ∃ p ∈ 𝔞, p ≠ 0 ∧ ∃ t, IsCoprime (Ideal.span {t}) 𝔟 ∧ ∀ a ∈ 𝔞, ∃ c, t * a = p * c := by
  obtain ⟨p, hp⟩ := IsDedekindDomain.exists_sup_span_eq (I := 𝔞 * 𝔟) (J := 𝔞) Ideal.mul_le_left
    (mul_ne_zero h𝔞 h𝔟)
  have hle : Ideal.span {p} ≤ 𝔞 := le_sup_right.trans hp.le
  obtain ⟨𝔠, h𝔠⟩ := Ideal.dvd_iff_le.2 hle
  have h1 : 𝔟 ⊔ 𝔠 = ⊤ := by
    apply mul_left_cancel₀ h𝔞
    rw [Ideal.mul_sup, ← h𝔠, hp, Ideal.mul_top]
  obtain ⟨m, hm, t, ht, e⟩ := Submodule.mem_sup.1 (h1 ▸ Submodule.mem_top : (1 : O) ∈ 𝔟 ⊔ 𝔠)
  have hc : IsCoprime (Ideal.span {t}) 𝔟 := cop_iff.2 ⟨1, m, hm, by linear_combination e⟩
  have key : ∀ a ∈ 𝔞, ∃ c, t * a = p * c := fun a ha => by
    have : a * t ∈ Ideal.span {p} := h𝔠 ▸ Ideal.mul_mem_mul ha ht
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨c, by linear_combination -hc⟩
  refine ⟨p, hle (Ideal.mem_span_singleton_self p), ?_, t, hc, key⟩
  rintro rfl
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  obtain ⟨c, hc'⟩ := key a ha
  exact mul_ne_zero (cop_ne_zero h𝔟' hc) ha0 (by simpa using hc')

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

noncomputable def bar : 𝓞 E →+* 𝓞 E := (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)

theorem coe_bar (a : 𝓞 E) : ((bar a : 𝓞 E) : E) = cc (a : E) :=
  IsCMField.coe_ringOfIntegersComplexConj E a

theorem bar_bar (a : 𝓞 E) : bar (bar a) = a := by
  apply RingOfIntegers.ext; rw [coe_bar, coe_bar]; simp [cc]

theorem mem_conjI {P : Ideal (𝓞 E)} {a : 𝓞 E} : a ∈ conjI P ↔ bar a ∈ P := by
  constructor
  · intro h
    have : conjI P ≤ P.comap bar := Ideal.span_le.2 (by
      rintro a ⟨b, hb, e⟩
      obtain rfl : a = bar b := RingOfIntegers.ext (e.trans (coe_bar b).symm)
      change bar (bar b) ∈ P
      rwa [bar_bar])
    exact this h
  · intro h
    exact Ideal.subset_span ⟨_, h, by rw [← coe_bar, bar_bar]⟩

theorem cop_bar {P : Ideal (𝓞 E)} {s : 𝓞 E} (h : IsCoprime (Ideal.span {s}) P) :
    IsCoprime (Ideal.span {bar s}) (conjI P) := by
  obtain ⟨a, m, hm, e⟩ := cop_iff.1 h
  exact cop_iff.2 ⟨bar a, bar m, mem_conjI.2 (by rwa [bar_bar]),
    by rw [← map_mul, ← map_add, e, map_one]⟩

theorem O_smul (a : 𝓞 E) (v : Fin r → E) : a • v = (a : E) • v := rfl

theorem EF_smulE (a : E) (u v : Fin r → E) : EF X (a • u) v = EF X u (cc a • v) := by
  simp only [EF_def, herm, Pi.smul_apply, smul_eq_mul, cc, map_mul, IsCMField.complexConj_apply_apply]
  congr 2
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem EF_smul (a : 𝓞 E) (u v : Fin r → E) : EF X (a • u) v = EF X u (bar a • v) := by
  rw [O_smul, O_smul, coe_bar, EF_smulE]

theorem EF_add_left (u u' v : Fin r → E) : EF X (u + u') v = EF X u v + EF X u' v := by
  simp only [EF_def, ← map_add, herm, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem EF_add_right (u v v' : Fin r → E) : EF X u (v + v') = EF X u v + EF X u v' := by
  simp only [EF_def, herm, cc, Pi.add_apply, map_add, Finset.sum_add_distrib, mul_add]

theorem EF_zsmul (k : ℤ) (u v : Fin r → E) : EF X (k • u) v = k * EF X u v := by
  simp only [EF_def, herm, Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm,
    map_zsmul]
  exact zsmul_eq_mul _ _

theorem selfD_of_sympl {g : ℕ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) :
    SelfD X X.Λ := by
  refine ⟨X.Λ_fg, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩
  · have := hs (bas.symm ⟨x, hx⟩) (bas.symm ⟨y, hy⟩)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
    exact ⟨_, this.trans (Int.cast_neg _).symm⟩
  · obtain ⟨k, hk, hx⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span x
    set m := bas.symm ⟨_, hx⟩ with hm
    have h1 (b) : k ∣ omegaStd m b := by
      have := hs m b
      rw [hm, LinearEquiv.apply_symm_apply] at this
      obtain ⟨l, hl⟩ := h _ (bas b).2
      change EF X (k • x) _ = _ at this
      rw [EF_zsmul, hl] at this
      refine ⟨-l, ?_⟩
      have : k * l = -omegaStd (bas.symm ⟨_, hx⟩) b := by exact_mod_cast this
      linear_combination this
    have h2 (j) : k ∣ m j := by
      rcases j with j | j
      · simpa [omegaStd, Pi.single_apply] using h1 (Pi.single (Sum.inr j) 1)
      · simpa [omegaStd, Pi.single_apply] using h1 (Pi.single (Sum.inl j) 1)
    choose m' hm' using h2
    have h3 : m = k • m' := funext hm'
    have h4 : k • x = k • (bas m' : Fin r → E) := by
      have := congrArg (fun t => (bas t : Fin r → E)) h3
      simpa only [hm, LinearEquiv.apply_symm_apply, map_zsmul, AddSubgroupClass.coe_zsmul] using this
    rw [smul_right_injective _ hk h4]
    exact (bas m').2

noncomputable def lin (γ : GL (Fin r) E) : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) :=
  (Matrix.toLin' (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)

theorem lin_apply (γ : GL (Fin r) E) (v : Fin r → E) :
    lin γ v = (γ : Matrix (Fin r) (Fin r) E) *ᵥ v := rfl

theorem lin_mul (γ δ : GL (Fin r) E) (v : Fin r → E) : lin (γ * δ) v = lin γ (lin δ v) := by
  simp [lin_apply]

theorem lin_inv (γ : GL (Fin r) E) (v : Fin r → E) : lin γ⁻¹ (lin γ v) = v := by
  rw [← lin_mul]; simp [lin_apply]

theorem lin_inv' (γ : GL (Fin r) E) (v : Fin r → E) : lin γ (lin γ⁻¹ v) = v := by
  rw [← lin_mul]; simp [lin_apply]

theorem mem_mapL {γ : GL (Fin r) E} {L : Lt E r} {v : Fin r → E} :
    v ∈ mapL γ L ↔ lin γ⁻¹ v ∈ L :=
  ⟨by rintro ⟨x, hx, rfl⟩; exact (lin_inv γ x).symm ▸ hx, fun h => ⟨_, h, lin_inv' γ v⟩⟩

theorem isUn_inv {γ : GL (Fin r) E} (h : IsUn X γ) : IsUn X γ⁻¹ := fun x y => by
  have := h (lin γ⁻¹ x) (lin γ⁻¹ y)
  rw [← lin_apply, ← lin_apply, lin_inv', lin_inv'] at this
  exact this.symm

theorem isUn_mul {γ δ : GL (Fin r) E} (h : IsUn X γ) (h' : IsUn X δ) : IsUn X (γ * δ) :=
  fun x y => by
    rw [← lin_apply, ← lin_apply, lin_mul, lin_mul]
    exact (h _ _).trans (h' _ _)

theorem EF_lin {γ : GL (Fin r) E} (h : IsUn X γ) (u v : Fin r → E) :
    EF X (lin γ u) v = EF X u (lin γ⁻¹ v) := by
  conv_lhs => rw [← lin_inv' γ v]
  rw [EF_def, EF_def, lin_apply γ, lin_apply γ, h]

theorem selfD_mapL {γ : GL (Fin r) E} (h : IsUn X γ) {L : Lt E r} (hL : SelfD X L) :
    SelfD X (mapL γ L) := by
  refine ⟨hL.1.map _, fun x => ?_⟩
  rw [mem_mapL, hL.2]
  simp only [EF_lin (isUn_inv h), inv_inv]
  exact ⟨fun H y hy => lin_inv' γ y ▸ H _ (mem_mapL.1 hy), fun H y hy => H _ ⟨y, hy, rfl⟩⟩

theorem mem_idq {𝔞 𝔟 : Ideal (𝓞 E)} {L : Lt E r} {v : Fin r → E} :
    v ∈ idq 𝔞 𝔟 L ↔ ∀ b ∈ 𝔟, b • v ∈ 𝔞 • L := Iff.rfl

theorem idq_mapL (𝔞 𝔟 : Ideal (𝓞 E)) (γ : GL (Fin r) E) (L : Lt E r) :
    idq 𝔞 𝔟 (mapL γ L) = mapL γ (idq 𝔞 𝔟 L) := by
  ext v
  have : 𝔞 • mapL γ L = mapL γ (𝔞 • L) := (Submodule.map_smul'' _ _ _).symm
  simp only [mem_mapL, mem_idq, this, map_smul]

theorem smul_le_idq (𝔞 𝔟 : Ideal (𝓞 E)) (L : Lt E r) : 𝔞 • L ≤ idq 𝔞 𝔟 L :=
  fun _ hv b _ => Submodule.smul_mem _ b hv

theorem selfD_idq {P : Ideal (𝓞 E)} (h0 : P ≠ ⊥) (h1 : P ≠ ⊤) (hc : IsCoprime P (conjI P))
    {L : Lt E r} (hL : SelfD X L) : SelfD X (idq P (conjI P) L) := by
  have hb {a : 𝓞 E} (ha : a ∈ P) : bar a ∈ conjI P := mem_conjI.2 (by rwa [bar_bar])
  obtain ⟨p, hp, hp0, t, ht, hgen⟩ := exists_gen h0 h0 h1
  have hp0' : (p : E) ≠ 0 := by simpa using hp0
  refine ⟨?_, fun x => ⟨fun hx y hy => ?_, fun h b hb' => ?_⟩⟩
  · have hq : bar p ≠ 0 := fun e => hp0 (by rw [← bar_bar p, e, map_zero])
    refine Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) _ (bar p))
      (LinearMap.lsmul_injective hq) ?_
    refine Submodule.FG.of_le hL.1 ?_
    rintro _ ⟨v, hv, rfl⟩
    exact Submodule.smul_le_right (hv _ (hb hp))
  · obtain ⟨m, hm, m', hm', e⟩ := Ideal.isCoprime_iff_exists.1 hc
    have k1 : ∀ z ∈ P • L, ∃ k : ℤ, EF X x z = k := fun z hz => by
      refine Submodule.smul_induction_on hz (fun a ha l hl => ?_) ?_
      · rw [← bar_bar a, ← EF_smul]
        exact (hL.2 _).1 (Submodule.smul_le_right (hx _ (hb ha))) l hl
      · rintro u v ⟨k, hk⟩ ⟨l, hl⟩
        exact ⟨k + l, by rw [EF_add_right, hk, hl, Int.cast_add]⟩
    have k2 : ∀ z ∈ P • L, ∃ k : ℤ, EF X z y = k := fun z hz => by
      refine Submodule.smul_induction_on hz (fun a ha l hl => ?_) ?_
      · rw [EF_smul]
        exact (hL.2 _).1 hl _ (Submodule.smul_le_right (hy _ (hb ha)))
      · rintro u v ⟨k, hk⟩ ⟨l, hl⟩
        exact ⟨k + l, by rw [EF_add_left, hk, hl, Int.cast_add]⟩
    obtain ⟨k, hk⟩ := k1 _ (hy _ (hb hm))
    obtain ⟨l, hl⟩ := k2 _ (hx _ hm')
    refine ⟨k + l, ?_⟩
    rw [← one_smul (𝓞 E) x, ← e, add_smul, EF_add_left, EF_smul, hk, hl, Int.cast_add]
  · have hm := mem_conjI.1 hb'
    have hz : b • x ∈ L := (hL.2 _).2 fun l hl => by
      rw [EF_smul]
      exact h _ (smul_le_idq _ _ _ (Submodule.smul_mem_smul hm hl))
    refine mem_of_loc hz le_rfl ⟨t, ht, ?_⟩
    have hw : ((t : E) * b / p) • x ∈ L := (hL.2 _).2 fun l hl => by
      rw [EF_smulE]
      refine h _ fun a ha => ?_
      obtain ⟨c, hc⟩ := hgen _ (mem_conjI.1 ha)
      have : a • cc ((t : E) * b / p) • l = bar b • bar c • l := by
        have e : (t : E) * cc (a : E) = p * c := by
          rw [← coe_bar]; exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hc
        rw [O_smul, O_smul, O_smul, smul_smul, smul_smul, coe_bar, coe_bar]
        congr 1
        have e2 : (c : E) = t * cc (a : E) / p := by rw [e]; field_simp
        rw [e2]
        simp only [cc, map_mul, map_div₀, IsCMField.complexConj_apply_apply]
        ring
      rw [this]
      exact Submodule.smul_mem_smul hm (L.smul_mem _ hl)
    have : t • b • x = p • ((t : E) * b / p) • x := by
      rw [O_smul, O_smul, O_smul, smul_smul, smul_smul]; congr 1; field_simp
    rw [this]
    exact Submodule.smul_mem_smul hp hw

theorem relIndex_idq {P Q : Ideal (𝓞 E)} {L L' : Lt E r} {s : 𝓞 E}
    (hs : IsCoprime (Ideal.span {s}) (P * Q)) (h : ∀ v ∈ L, s • v ∈ L') :
    (idq P Q L').toAddSubgroup.relIndex (idq P Q L).toAddSubgroup =
      L'.toAddSubgroup.relIndex L.toAddSubgroup := by
  obtain ⟨a, m, hm, e⟩ := cop_iff.1 hs.of_mul_right_left
  obtain ⟨a', m', hm', e'⟩ := cop_iff.1 hs.of_mul_right_right
  have h' {v} (hv : v ∈ P • L) : s • v ∈ P • L' := smul_map_mem LinearMap.id h hv
  have d (x : Fin r → E) : x = m • x + a • s • x := by
    rw [← mul_smul, ← add_smul, add_comm, e, one_smul]
  have d' (x : Fin r → E) : x = m' • x + a' • s • x := by
    rw [← mul_smul, ← add_smul, add_comm, e', one_smul]
  rw [relIndex_eq (C := (P • L).toAddSubgroup) (A := (idq P Q L).toAddSubgroup) (smul_le_idq _ _ _),
    relIndex_eq (C := (P • L).toAddSubgroup) (A := L.toAddSubgroup) Submodule.smul_le_right,
    ← AddSubgroup.inf_relIndex_right, ← AddSubgroup.inf_relIndex_right L'.toAddSubgroup]
  · congr 1
    ext x
    refine and_congr_left fun (hx : x ∈ P • L) => ⟨fun (H : x ∈ idq P Q L') => ?_, fun (H : x ∈ L') => ?_⟩
    · change x ∈ L'
      rw [d' x]
      exact Submodule.smul_le_right (add_mem (H _ hm') (Submodule.smul_mem _ _ (h' hx)))
    · refine smul_le_idq P Q L' ?_
      rw [d x]
      exact add_mem (Submodule.smul_mem_smul hm H) (Submodule.smul_mem _ _ (h' hx))
  · intro x (hx : x ∈ L)
    rw [d x]
    exact AddSubgroup.add_mem_sup (Submodule.smul_mem_smul hm hx)
      ⟨L'.smul_mem _ (h x hx), L.smul_mem _ (L.smul_mem _ hx)⟩
  · intro x (hx : x ∈ idq P Q L)
    rw [d' x]
    refine AddSubgroup.add_mem_sup (hx _ hm')
      ⟨(idq P Q L').smul_mem _ fun b hb => ?_, (idq P Q L).smul_mem _ ((idq P Q L).smul_mem _ hx)⟩
    rw [smul_comm]; exact h' (hx b hb)

variable (D : Level X)

theorem cong_iff {𝔪 : Ideal (𝓞 E)} {u v : Fin r → E} :
    Cong X 𝔪 u v ↔ u - v ∈ loc 𝔪 (𝔪 • X.Λ) := Iff.rfl

theorem cong_symm {𝔪 : Ideal (𝓞 E)} {u v : Fin r → E} (h : Cong X 𝔪 u v) : Cong X 𝔪 v u := by
  rw [cong_iff, ← neg_sub]; exact neg_mem (cong_iff.1 h)

theorem cong_trans {𝔪 : Ideal (𝓞 E)} {u v w : Fin r → E} (h : Cong X 𝔪 u v) (h' : Cong X 𝔪 v w) :
    Cong X 𝔪 u w := by
  rw [cong_iff, ← sub_add_sub_cancel u v w]; exact add_mem (cong_iff.1 h) (cong_iff.1 h')

theorem cong_refl {𝔪 : Ideal (𝓞 E)} (u : Fin r → E) : Cong X 𝔪 u u := by
  rw [cong_iff, sub_self]; exact zero_mem _

theorem cong_sum {𝔪 : Ideal (𝓞 E)} {u v : Fin r → Fin r → E} (h : ∀ i, Cong X 𝔪 (u i) (v i))
    (c : Fin r → 𝓞 E) : Cong X 𝔪 (∑ i, c i • u i) (∑ i, c i • v i) := by
  rw [cong_iff, ← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun i _ => smul_sub (c i) (u i) (v i) ▸ Submodule.smul_mem _ _ (cong_iff.1 (h i))

theorem cong_lin {𝔪 : Ideal (𝓞 E)} {γ : GL (Fin r) E} {s : 𝓞 E}
    (hs : IsCoprime (Ideal.span {s}) 𝔪) (h : ∀ v ∈ X.Λ, s • lin γ v ∈ X.Λ) {u v : Fin r → E}
    (H : Cong X 𝔪 u v) : Cong X 𝔪 (lin γ u) (lin γ v) := by
  obtain ⟨t, ht, H⟩ := H
  refine ⟨s * t, cop_mul hs ht, ?_⟩
  rw [← map_sub, mul_smul, ← map_smul]
  exact smul_map_mem _ h H

theorem cong_coeff {c d : Fin r → 𝓞 E} (h : ∀ j, c j - d j ∈ D.𝔪) :
    Cong X D.𝔪 (∑ j, c j • D.β j) (∑ j, d j • D.β j) := by
  rw [cong_iff, ← Finset.sum_sub_distrib]
  exact le_loc _ (Submodule.sum_mem _ fun j _ =>
    sub_smul (c j) (d j) (D.β j) ▸ Submodule.smul_mem_smul (h j) (D.β_mem j))

theorem coeff_cong {c d : Fin r → 𝓞 E} (h : Cong X D.𝔪 (∑ j, c j • D.β j) (∑ j, d j • D.β j)) (j) :
    c j - d j ∈ D.𝔪 := by
  obtain ⟨s, hs, hN⟩ := nakayama X.Λ_fg D.β_span
  have hs0 : (s : E) ≠ 0 := by simpa using cop_ne_zero D.proper hs
  have hli : LinearIndependent E D.β := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
    rw [← X.Λ_span, Submodule.span_le]
    intro v hv
    have := Submodule.span_le_restrictScalars (𝓞 E) E _ (hN v hv)
    exact (Submodule.smul_mem_iff _ hs0).1 this
  obtain ⟨t, ht, h⟩ := h
  have h1 := smul_map_mem LinearMap.id hN h
  obtain ⟨a, ha, e⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ _ _).1 h1
  rw [Finsupp.sum_fintype _ _ (by simp)] at e
  have h2 : (a j : E) = ((s * t * (c j - d j) : 𝓞 E) : E) := by
    refine (Fintype.linearIndependent_iffₛ.1 hli) (fun j => (a j : E))
      (fun j => ((s * t * (c j - d j) : 𝓞 E) : E)) ?_ j
    simp only [← O_smul]
    rw [e]
    simp only [LinearMap.id_apply, mul_smul, sub_smul, ← Finset.smul_sum, Finset.sum_sub_distrib]
  obtain ⟨b, m, hm, e'⟩ := cop_iff.1 (cop_mul hs ht)
  have h3 : c j - d j = b * a j + (c j - d j) * m := by
    rw [RingOfIntegers.ext h2]; linear_combination -(c j - d j) * e'
  rw [h3]
  exact add_mem (Ideal.mul_mem_left _ _ (ha j)) (Ideal.mul_mem_left _ _ hm)

variable {D}

theorem red_unique {u : Fin r → Fin r → E} {k k' : GL (Fin r) (𝓞 E ⧸ D.𝔪)} (h : D.Red u k)
    (h' : D.Red u k') : k = k' := by
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨b, hb, h'⟩ := h'
  ext j i
  rw [← ha, ← hb]
  exact Ideal.Quotient.eq.2 (coeff_cong D (cong_trans (cong_symm (h i)) (h' i)) j)

theorem red_congr {u u' : Fin r → Fin r → E} {k : GL (Fin r) (𝓞 E ⧸ D.𝔪)}
    (H : ∀ i, Cong X D.𝔪 (u' i) (u i)) (h : D.Red u k) : D.Red u' k := by
  obtain ⟨a, ha, h⟩ := h
  exact ⟨a, ha, fun i => cong_trans (H i) (h i)⟩

theorem cong_of_red {u u' : Fin r → Fin r → E} {k : GL (Fin r) (𝓞 E ⧸ D.𝔪)}
    (h : D.Red u k) (h' : D.Red u' k) (i) : Cong X D.𝔪 (u i) (u' i) := by
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨b, hb, h'⟩ := h'
  refine cong_trans (h i) (cong_trans (cong_coeff D fun j => ?_) (cong_symm (h' i)))
  exact Ideal.Quotient.eq.1 (congrFun (congrFun (ha.trans hb.symm) j) i)

theorem red_one : D.Red D.β 1 :=
  ⟨1, by simp, fun i => by simpa [Matrix.one_apply] using cong_refl _⟩

theorem exists_lift (k : GL (Fin r) (𝓞 E ⧸ D.𝔪)) :
    ∃ a : Matrix (Fin r) (Fin r) (𝓞 E), a.map (Ideal.Quotient.mk D.𝔪) = k := by
  choose a ha using fun i j => Ideal.Quotient.mk_surjective (k.1 i j)
  exact ⟨Matrix.of a, by ext i j; exact ha i j⟩

theorem red_comb {u : Fin r → Fin r → E} {k l : GL (Fin r) (𝓞 E ⧸ D.𝔪)} (h : D.Red u k)
    {b : Matrix (Fin r) (Fin r) (𝓞 E)} (hb : b.map (Ideal.Quotient.mk D.𝔪) = l) :
    D.Red (fun i => ∑ j, b j i • u j) (k * l) := by
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a * b, by rw [Matrix.map_mul, ha, hb, Units.val_mul], fun i => ?_⟩
  convert cong_sum h (fun j => b j i) using 1
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul, mul_comm]
  exact Finset.sum_comm

theorem keeps {γ : GL (Fin r) E} {k : GL (Fin r) (𝓞 E ⧸ D.𝔪)}
    (h : D.Red (fun i => lin γ (D.β i)) k) :
    ∃ s, IsCoprime (Ideal.span {s}) D.𝔪 ∧ (∀ v ∈ X.Λ, s • lin γ v ∈ X.Λ) ∧
      ∀ v ∈ X.Λ, s • lin γ⁻¹ v ∈ X.Λ := by
  have h1 : mapL γ X.Λ ≤ loc D.𝔪 X.Λ := by
    obtain ⟨s, hs, hN⟩ := nakayama X.Λ_fg D.β_span
    rintro _ ⟨v, hv, rfl⟩
    refine loc_loc hs ?_
    change s • lin γ v ∈ _
    rw [← map_smul]
    refine (Submodule.span_le (p := (loc D.𝔪 X.Λ).comap (lin γ))).2 ?_ (hN v hv)
    rintro _ ⟨i, rfl⟩
    obtain ⟨a, -, h⟩ := h
    have := add_mem (loc_mono Submodule.smul_le_right (cong_iff.1 (h i)))
      (le_loc _ (X.Λ.sum_mem (t := Finset.univ) fun j _ => X.Λ.smul_mem (a j i) (D.β_mem j)))
    rwa [sub_add_cancel] at this
  have h2 : X.Λ ≤ mapL γ X.Λ ⊔ D.𝔪 • X.Λ := by
    refine D.β_span.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)
    rintro _ ⟨i, rfl⟩
    refine mem_of_loc (D.β_mem i) le_sup_right ?_
    obtain ⟨b, hb⟩ := exists_lift k⁻¹
    have h3 := red_comb h hb
    rw [mul_inv_cancel] at h3
    have := add_mem (loc_mono (le_sup_right (a := mapL γ X.Λ))
      (cong_iff.1 (cong_of_red red_one h3 i)))
      (le_loc _ (Submodule.mem_sup_left ((mapL γ X.Λ).sum_mem (t := Finset.univ) fun j _ =>
        (mapL γ X.Λ).smul_mem (b j i) (x := lin γ (D.β j)) ⟨_, D.β_mem j, rfl⟩)))
    rwa [sub_add_cancel] at this
  obtain ⟨s, hs, h1⟩ := exists_mul_of_fg (X.Λ_fg.map _) h1
  obtain ⟨t, ht, h2⟩ := nakayama X.Λ_fg h2
  refine ⟨s * t, cop_mul hs ht, fun v hv => ?_, fun v hv => ?_⟩
  · rw [mul_comm, mul_smul]; exact X.Λ.smul_mem _ (h1 _ ⟨v, hv, rfl⟩)
  · rw [mul_smul, ← map_smul]; exact X.Λ.smul_mem _ (mem_mapL.1 (h2 v hv))

theorem cong_lin_iff {γ : GL (Fin r) E} {k : GL (Fin r) (𝓞 E ⧸ D.𝔪)}
    (h : D.Red (fun i => lin γ (D.β i)) k) {u v : Fin r → E} :
    Cong X D.𝔪 (lin γ u) (lin γ v) ↔ Cong X D.𝔪 u v := by
  obtain ⟨s, hs, h1, h2⟩ := keeps h
  exact ⟨fun H => by simpa only [lin_inv] using cong_lin hs h2 H, cong_lin hs h1⟩

theorem red_lin_iff {γ : GL (Fin r) E} {k l : GL (Fin r) (𝓞 E ⧸ D.𝔪)}
    (h : D.Red (fun i => lin γ (D.β i)) k) {u : Fin r → Fin r → E} :
    D.Red (fun i => lin γ (u i)) (k * l) ↔ D.Red u l := by
  have key {b : Matrix (Fin r) (Fin r) (𝓞 E)} (hb : b.map (Ideal.Quotient.mk D.𝔪) = l) :
      D.Red (fun i => lin γ (∑ j, b j i • D.β j)) (k * l) := by
    simpa only [map_sum, map_smul] using red_comb h hb
  constructor
  · intro H
    obtain ⟨b, hb⟩ := exists_lift l
    exact ⟨b, hb, fun i => (cong_lin_iff h).1 (cong_of_red H (key hb) i)⟩
  · rintro ⟨b, hb, H⟩
    exact red_congr (fun i => (cong_lin_iff h).2 (H i)) (key hb)

theorem mem_grp (γ : GL (Fin r) E) :
    γ ∈ D.grp ↔ IsUn X γ ∧ ∃ k ∈ D.J, D.Red (fun i => lin γ (D.β i)) k := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => by simp, 1, one_mem _, by simpa [lin_apply] using red_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hx, k, hk, h⟩ := hx
    obtain ⟨hy, l, hl, h'⟩ := hy
    exact ⟨isUn_mul hx hy, k * l, mul_mem hk hl, by
      simpa only [lin_mul] using (red_lin_iff h).2 h'⟩
  | inv x _ hx =>
    obtain ⟨hx, k, hk, h⟩ := hx
    refine ⟨isUn_inv hx, k⁻¹, inv_mem hk, (red_lin_iff h).1 ?_⟩
    simpa only [lin_inv', mul_inv_cancel] using red_one

theorem mapL_mem_lats (hΛ : SelfD X X.Λ) {γ : GL (Fin r) E} (hγ : γ ∈ D.grp) {L : Lt E r}
    (hL : L ∈ D.lats) : mapL γ L ∈ D.lats := by
  obtain ⟨hu, k, -, h⟩ := (mem_grp γ).1 hγ
  obtain ⟨s, hs, h1, h2⟩ := keeps h
  obtain ⟨hL, t, ht, h3, h4⟩ := hL
  have h1' (v) (hv : v ∈ X.Λ) : bar s • lin γ v ∈ X.Λ := (hΛ.2 _).2 fun y hy => by
    rw [EF_smul, bar_bar, EF_lin hu, map_smul]
    exact (hΛ.2 _).1 hv _ (h2 y hy)
  have h2' (v) (hv : v ∈ X.Λ) : bar s • lin γ⁻¹ v ∈ X.Λ := (hΛ.2 _).2 fun y hy => by
    rw [EF_smul, bar_bar, EF_lin (isUn_inv hu), inv_inv, map_smul]
    exact (hΛ.2 _).1 hv _ (h1 y hy)
  obtain ⟨a, b, hab⟩ := cop_glue D.cop hs (cop_bar hs)
  have glue {w : Fin r → E} (H : s • w ∈ X.Λ) (H' : bar s • w ∈ X.Λ) :
      (a * s + b * bar s) • w ∈ X.Λ := by
    rw [add_smul, mul_smul, mul_smul]
    exact add_mem (X.Λ.smul_mem _ H) (X.Λ.smul_mem _ H')
  refine ⟨selfD_mapL hu hL, (a * s + b * bar s) * t, cop_mul hab ht, ?_, fun v hv => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    change _ • lin γ v ∈ _
    rw [mul_smul, ← map_smul]
    exact glue (h1 _ (h3 v hv)) (h1' _ (h3 v hv))
  · rw [mem_mapL, map_smul, mul_comm, mul_smul]
    exact h4 _ (glue (h2 v hv) (h2' v hv))

theorem span_lats {L : Lt E r} (hL : L ∈ D.lats) :
    Submodule.span E (L : Set (Fin r → E)) = ⊤ := by
  obtain ⟨-, t, ht, -, h4⟩ := hL
  have h0 : (t : E) ≠ 0 := by simpa using cop_ne_zero D.proper ht.of_mul_right_left
  rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
  exact fun v hv => (Submodule.smul_mem_iff _ h0).1 (Submodule.subset_span (h4 v hv))

theorem norm_lam (k : D.J) : ‖((D.lam k : ℂˣ) : ℂ)‖ = 1 := by
  haveI : Finite (𝓞 E ⧸ D.𝔪) := Ideal.finiteQuotientOfFreeOfNeBot _ D.ne_bot
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card D.J) ?_ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

variable {n : ℕ} (hn : r ≤ n)

theorem dat_pos {y : Matrix (Fin n) (Fin r) E} {k : D.J}
    (h : D.Red (fun i => y (Fin.castLE hn i)) k)
    (h' : ∀ k : Fin n, r ≤ (k : ℕ) → Cong X D.𝔪 (y k) 0) : D.dat hn y = (D.lam k : ℂˣ) := by
  have H : (∃ k : D.J, D.Red (fun i => y (Fin.castLE hn i)) k) ∧
      ∀ k : Fin n, r ≤ (k : ℕ) → Cong X D.𝔪 (y k) 0 := ⟨⟨k, h⟩, h'⟩
  rw [Level.dat, dif_pos H, Subtype.ext (red_unique H.1.choose_spec h)]

theorem dat_congr {y y' : Matrix (Fin n) (Fin r) E} (h : ∀ k, Cong X D.𝔪 (y k) (y' k)) :
    D.dat hn y = D.dat hn y' := by
  by_cases H : (∃ k : D.J, D.Red (fun i => y' (Fin.castLE hn i)) k) ∧
      ∀ k : Fin n, r ≤ (k : ℕ) → Cong X D.𝔪 (y' k) 0
  · obtain ⟨⟨k, hk⟩, H⟩ := H
    rw [dat_pos hn hk H, dat_pos hn (red_congr (fun i => h _) hk)
      fun j hj => cong_trans (h j) (H j hj)]
  · rw [Level.dat, Level.dat, dif_neg H, dif_neg]
    rintro ⟨⟨k, hk⟩, H'⟩
    exact H ⟨⟨k, red_congr (fun i => cong_symm (h _)) hk⟩,
      fun j hj => cong_trans (cong_symm (h j)) (H' j hj)⟩

theorem dat_lin {γ : GL (Fin r) E} {k : D.J} (h : D.Red (fun i => lin γ (D.β i)) k)
    (y : Matrix (Fin n) (Fin r) E) :
    D.dat hn (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) = (D.lam k : ℂˣ) * D.dat hn y := by
  have e (j) : (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) j = lin γ (y j) := by
    funext i; simp [lin_apply, Matrix.mul_apply, mulVec, dotProduct, mul_comm]
  have e0 (j) : Cong X D.𝔪 (lin γ (y j)) 0 ↔ Cong X D.𝔪 (y j) 0 := by
    rw [← cong_lin_iff h (u := y j), map_zero]
  by_cases H : (∃ k : D.J, D.Red (fun i => y (Fin.castLE hn i)) k) ∧
      ∀ k : Fin n, r ≤ (k : ℕ) → Cong X D.𝔪 (y k) 0
  · obtain ⟨⟨l, hl⟩, H⟩ := H
    rw [dat_pos hn hl H, dat_pos hn (k := k * l), map_mul, Units.val_mul]
    · simp only [e]; exact (red_lin_iff h).2 hl
    · intro j hj; rw [e, e0]; exact H j hj
  · rw [Level.dat, Level.dat, dif_neg H, dif_neg, mul_zero]
    rintro ⟨⟨l, hl⟩, H'⟩
    refine H ⟨⟨k⁻¹ * l, (red_lin_iff h).1 ?_⟩, fun j hj => ?_⟩
    · simpa [e] using hl
    · rw [← e0, ← e]; exact H' j hj

end GlobalTheory.SW.Lev

namespace GlobalTheory.SW

open Lev

theorem level_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n), X.Λ ∈ D.lats ∧ (∀ u k k', D.Red u k → D.Red u k' → k = k') ∧ (∀ γ, γ ∈ D.grp ↔ IsUn X γ ∧ ∃ k ∈ D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k) ∧ (∀ L ∈ D.lats, SelfD X (D.sh L) ∧ Submodule.span E (L : Set (Fin r → E)) = ⊤ ∧ (∀ L' ∈ D.lats, (D.sh L').toAddSubgroup.relIndex (D.sh L).toAddSubgroup = L'.toAddSubgroup.relIndex L.toAddSubgroup) ∧ ∀ γ ∈ D.grp, mapL γ L ∈ D.lats ∧ D.sh (mapL γ L) = mapL γ (D.sh L)) ∧ (∀ k : D.J, ‖((D.lam k : ℂˣ) : ℂ)‖ = 1) ∧ (∀ y y' : Matrix (Fin n) (Fin r) E, (∀ k, Cong X D.𝔪 (y k) (y' k)) → D.dat hn y = D.dat hn y') ∧ ∀ γ ∈ D.grp, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → ∀ y : Matrix (Fin n) (Fin r) E, D.dat hn (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) = (D.lam k : ℂˣ) * D.dat hn y := by
  intro E _ _ _ r X g bas _ n hs _ D hn
  have hΛ := selfD_of_sympl hs
  refine ⟨⟨hΛ, 1, cop_one, fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩,
    fun _ _ _ => red_unique, mem_grp, fun L hL => ⟨selfD_idq D.ne_bot D.proper D.cop hL.1,
      span_lats hL, fun L' hL' => ?_, fun γ hγ => ⟨mapL_mem_lats hΛ hγ hL, idq_mapL _ _ _ _⟩⟩,
    norm_lam, fun _ _ => dat_congr hn, fun γ _ k h => dat_lin hn h⟩
  obtain ⟨-, s, hs, h1, -⟩ := hL
  obtain ⟨-, t, ht, -, h2⟩ := hL'
  exact relIndex_idq (cop_mul ht hs) fun v hv => by rw [mul_smul]; exact h2 _ (h1 v hv)

end GlobalTheory.SW
