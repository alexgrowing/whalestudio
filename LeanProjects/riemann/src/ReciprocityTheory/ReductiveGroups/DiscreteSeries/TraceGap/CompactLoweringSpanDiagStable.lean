import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section Straight

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}

theorem lowerWord_weight (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M}
    (hy : ∀ a, E a a y = (μ a : ℂ) • y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ (a : Fin n),
      E a a (lowWord E y l) = (lowWt μ l a : ℂ) • lowWord E y l
  | [], _, a => by simpa [lowWord, lowWt] using hy a
  | p :: l, hl, a => by
    obtain ⟨c, d⟩ := p
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have h := congrArg (fun X : Module.End ℂ M => X (lowWord E y l)) (hE a a c d rfl hcd.2)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [lowerWord_weight hE hy l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) a, map_smul,
      sub_eq_iff_eq_add] at h
    simp only [lowWord, lowWt]
    rw [h]
    simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases hac : a = c <;> by_cases had : a = d
    · subst hac; subst had; simp
    · subst hac
      simp only [if_neg had, if_neg (Ne.symm had), LinearMap.zero_apply, sub_zero]
      push_cast
      module
    · subst had
      simp only [if_neg hac, LinearMap.zero_apply, zero_sub]
      push_cast
      module
    · simp [hac, had, Ne.symm had]

theorem compactLoweringSpan_diag_stable (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M}
    (hy : ∀ a, E a a y = (μ a : ℂ) • y) (a : Fin n) :
    ∀ x ∈ kLowSpan ε E y, E a a x ∈ kLowSpan ε E y := by
  have : kLowSpan ε E y ≤ (kLowSpan ε E y).comap (E a a) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨l, hl, rfl⟩
    show E a a (lowWord E y l) ∈ kLowSpan ε E y
    rw [lowerWord_weight hE hy l hl a]
    exact Submodule.smul_mem _ _ (lowWord_mem hl)
  exact fun x hx => this hx

theorem lowerWord_mem_span_of_ge (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M}
    (hy : ∀ a, E a a y = (μ a : ℂ) • y)
    {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) {a b : Fin n} (hab : b ≤ a)
    (hε : ε a = ε b) : E a b (lowWord E y l) ∈ kLowSpan ε E y := by
  rcases hab.lt_or_eq with h | rfl
  · exact kLowSpan_low_stable (c := a) (d := b) ⟨h, hε⟩ _ (lowWord_mem hl)
  · exact compactLoweringSpan_diag_stable hE hy b _ (lowWord_mem hl)

theorem lowerWord_raise_mem_span (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M} (hy : IsKHWVec ε E μ y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ a b : Fin n, a < b → ε a = ε b →
      E a b (lowWord E y l) ∈ kLowSpan ε E y
  | [], _, a, b, hab, hε => by
    simp only [lowWord]
    rw [hy.2 a b hab hε]
    exact Submodule.zero_mem _
  | p :: l, hl, a, b, hab, hε => by
    obtain ⟨c, d⟩ := p
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have hl' : ∀ p ∈ l, IsKLow ε p := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have ih := lowerWord_raise_mem_span hE hy l hl'
    have key : ∀ a' b' : Fin n, ε a' = ε b' → E a' b' (lowWord E y l) ∈ kLowSpan ε E y := by
      intro a' b' h'
      rcases lt_or_ge a' b' with h | h
      · exact ih a' b' h h'
      · exact lowerWord_mem_span_of_ge hE hy.1 hl' h h'
    have h := congrArg (fun X : Module.End ℂ M => X (lowWord E y l)) (hE a b c d hε hcd.2)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [sub_eq_iff_eq_add] at h
    simp only [lowWord]
    rw [h]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (kLowSpan_low_stable hcd _ (ih a b hab hε))
    · split_ifs with hbc
      · subst hbc; exact key a d (hε.trans hcd.2)
      · simp
    · split_ifs with hda
      · subst hda; exact key c b (hcd.2.trans hε)
      · simp

theorem compactLoweringSpan_kStable (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M} (hy : IsKHWVec ε E μ y) :
    IsKStableSub ε E (kLowSpan ε E y) := by
  intro a b hab
  rcases lt_or_ge a b with h | h
  · have : kLowSpan ε E y ≤ (kLowSpan ε E y).comap (E a b) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨l, hl, rfl⟩
      exact lowerWord_raise_mem_span hE hy l hl a b h hab
    exact fun x hx => this hx
  · rcases h.lt_or_eq with h | rfl
    · exact kLowSpan_low_stable ⟨h, hab⟩
    · exact compactLoweringSpan_diag_stable hE hy.1 b

end Straight

theorem kLowSpan_kIso {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hR : Formalism.REAL.KRel ε F) (hU : Formalism.REAL.KUnit ε F)
    {γ : Fin n → ℝ} {z : M} (hz : IsKHWVec ε F γ z) (hz0 : z ≠ 0)
    (hfin : FiniteDimensional ℂ (kLowSpan ε F z)) (T : S7.KType ε γ) :
    IsKStableSub ε F (kLowSpan ε F z) ∧
      ∃ φ : kLowSpan ε F z ≃ₗ[ℂ] T.V,
        (∀ a b, ε a = ε b → ∀ v w : kLowSpan ε F z, (w : M) = F a b v →
          φ w = T.dτ (Matrix.single a b 1) (φ v)) ∧
        φ ⟨z, self_mem_kLowSpan (ε := ε) (E := F) z⟩ = T.w := by
  classical
  set S := kLowSpan ε F z with hSdef
  have hS : IsKStableSub ε F S := compactLoweringSpan_kStable hR hz
  refine ⟨hS, ?_⟩
  let G : Fin n → Fin n → Module.End ℂ S := fun a b =>
    if h : ε a = ε b then (F a b).restrict (p := S) (q := S) (hS a b h) else 0
  have hGapp : ∀ a b, ε a = ε b → ∀ v : S, ((G a b v : S) : M) = F a b v := by
    intro a b h v
    simp only [G, dif_pos h]
    rfl
  have hRG : Formalism.REAL.KRel ε G := by
    intro a b c d hab hcd
    refine LinearMap.ext fun v => Subtype.ext ?_
    have h := congrArg (fun X : Module.End ℂ M => X (v : M)) (hR a b c d hab hcd)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h ⊢
    simp only [Submodule.coe_sub, hGapp a b hab, hGapp c d hcd]
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · rw [if_pos h1, if_pos h2] at h ⊢
      simpa only [Submodule.coe_sub, hGapp a d (by rw [hab, h1, hcd]),
        hGapp c b (by rw [hcd, h2, hab])] using h
    · rw [if_pos h1, if_neg h2] at h ⊢
      simpa only [Submodule.coe_sub, LinearMap.zero_apply, Submodule.coe_zero,
        hGapp a d (by rw [hab, h1, hcd])] using h
    · rw [if_neg h1, if_pos h2] at h ⊢
      simpa only [Submodule.coe_sub, LinearMap.zero_apply, Submodule.coe_zero,
        hGapp c b (by rw [hcd, h2, hab])] using h
    · rw [if_neg h1, if_neg h2] at h ⊢
      simpa only [Submodule.coe_sub, LinearMap.zero_apply, Submodule.coe_zero] using h
  have hUG : Formalism.REAL.KUnit ε G := by
    intro a b hab x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hGapp a b hab, hGapp b a hab.symm]
    exact hU a b hab x y
  let e : S ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ S)) := (stdOrthonormalBasis ℂ S).repr
  let G' : Fin n → Fin n → Module.End ℂ (EuclideanSpace ℂ (Fin (Module.finrank ℂ S))) :=
    fun a b => LinearEquiv.conjRingEquiv e.toLinearEquiv (G a b)
  have hG'app : ∀ a b y, G' a b y = e (G a b (e.symm y)) := fun a b y => rfl
  have hRG' : Formalism.REAL.KRel ε G' :=
    HW.uq_kRel_map ε G (LinearEquiv.conjRingEquiv e.toLinearEquiv).toRingHom hRG
  have hUG' : Formalism.REAL.KUnit ε G' := by
    intro a b hab x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    simp only [hG'app, LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]
    exact hUG a b hab x y
  set z0 : S := ⟨z, self_mem_kLowSpan (ε := ε) (E := F) z⟩ with hz0def
  have hGe : ∀ a b, ε a = ε b → ∀ s : S, G' a b (e s) = e (G a b s) := by
    intro a b _ s
    rw [hG'app, LinearIsometryEquiv.symm_apply_apply]
  have hw' : Formalism.REAL.KHighest ε G' γ (e z0) := by
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [hGe a a rfl, ← map_smul]
      congr 1
      exact Subtype.ext ((hGapp a a rfl z0).trans (hz.1 a))
    · rw [hGe a b he, ← map_zero e]
      congr 1
      exact Subtype.ext ((hGapp a b he z0).trans (hz.2 a b hab he))
  have hw0' : e z0 ≠ 0 := by
    intro h
    apply hz0
    exact congrArg Subtype.val (e.injective (h.trans e.map_zero.symm))
  have hTw0 : T.w ≠ 0 := by
    intro h
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have htop : Formalism.REAL.kSpan ε G' (e z0) = ⊤ := by
    set P := Formalism.REAL.kSpan ε G' (e z0) with hP
    let Q : Submodule ℂ M := (P.comap e.toLinearEquiv.toLinearMap).map S.subtype
    have hQ : IsKStableSub ε F Q := by
      rintro a b hab v ⟨s, hs, rfl⟩
      refine ⟨G a b s, ?_, hGapp a b hab s⟩
      show e (G a b s) ∈ P
      rw [← hGe a b hab s]
      exact HW.uq_kSpan_stable ε G' (e z0) a b hab _ hs
    have hzQ : z ∈ Q := ⟨z0, HW.uq_mem_kSpan ε G' (e z0), rfl⟩
    have hle := kLowSpan_le (E := F) hQ hzQ
    have hall : ∀ s : S, e s ∈ P := by
      intro s
      obtain ⟨s', hs', hss⟩ := hle s.2
      have : s' = s := Subtype.ext hss
      subst this
      exact hs'
    rw [eq_top_iff]
    intro y _
    rw [← e.apply_symm_apply y]
    exact hall _
  obtain ⟨φ0, hφ0, hφ0w⟩ := HW.uq_exists_equiv ε (HW.kunits T) G' γ T.w (e z0) (HW.KType.kRel T) hRG'
    (HW.KType.kUnit T) hUG' (HW.uq_kHighest T) hw' hTw0 hw0' (HW.KType.kSpan_eq_top T) htop
  refine ⟨e.toLinearEquiv.trans φ0.symm, ?_, ?_⟩
  · intro a b hab v w hw
    have hw2 : w = G a b v := Subtype.ext (hw.trans (hGapp a b hab v).symm)
    subst hw2
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    show φ0.symm (e (G a b v)) = HW.kunits T a b (φ0.symm (e v))
    rw [← hGe a b hab v, LinearEquiv.symm_apply_eq, hφ0 a b hab, LinearEquiv.apply_symm_apply]
  · rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
    exact hφ0w.symm

end ReciprocityTheory.ChartRestriction.DS.TRGap
