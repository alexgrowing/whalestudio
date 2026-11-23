import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LatModel

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

def frameLat (ξ : Spec (CommRingCat.of Ω) ⟶ X) {r : ℕ} (b : Fin r → E) : Lat ξ E :=
  fun p => Submodule.span (regAt ξ p) (Set.range b)

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isVB_frameLat {r : ℕ} {b : Fin r → E} (hb : LinearIndependent Ω b) :
    (frameLat ξ b).IsVB r (Submodule.span Ω (Set.range b)) :=
  fun _ _ => ⟨⊤, trivial, b, rfl, fun _ _ _ => ⟨hb, rfl⟩⟩

theorem IsVB_finrank {L : Lat ξ E} {r : ℕ} {V : Submodule Ω E} (h : L.IsVB r V) :
    Module.finrank Ω V = r := by
  obtain ⟨U, hU, b, rfl, hb⟩ := h ⟨genPt ξ, specializes_rfl⟩ trivial
  rw [finrank_span_eq_card (hb _ trivial hU).1, Fintype.card_fin]

theorem IsVB_span {L : Lat ξ E} {r : ℕ} {V : Submodule Ω E} (h : L.IsVB r V) (p : Cpt ξ) :
    Submodule.span Ω (L p : Set E) = V := by
  obtain ⟨U, hU, b, rfl, hb⟩ := h p trivial
  rw [(hb _ trivial hU).2, Submodule.span_span_of_tower]

theorem IsVB_dual {L : Lat ξ E} {r : ℕ} (h : L.IsVB r ⊤) : L.dual.IsVB r ⊤ := by
  classical
  intro p _
  obtain ⟨U, hU, b, hs, hb⟩ := h p trivial
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk (hb p trivial hU).1 hs.ge
  have hB : ∀ i, B i = b i := fun i => Module.Basis.mk_apply _ _ i
  refine ⟨U, hU, B.dualBasis, B.dualBasis.span_eq, fun q _ hq => ⟨B.dualBasis.linearIndependent, ?_⟩⟩
  have hL := (hb q trivial hq).2
  apply le_antisymm
  · intro w hw
    have hw' : ∀ e ∈ L q, w e ∈ regAt ξ q := hw
    rw [← B.dualBasis.sum_repr w]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hi : B.dualBasis.repr w i ∈ regAt ξ q := by
      rw [Module.Basis.dualBasis_repr, hB]
      exact hw' _ (hL ▸ Submodule.subset_span ⟨i, rfl⟩)
    exact Submodule.smul_mem _ (⟨_, hi⟩ : regAt ξ q) (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ e he
    rw [hL] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← hB, Module.Basis.dualBasis_apply_self]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      have : B.dualBasis i (c • x) = (c : Ω) * B.dualBasis i x := by
        rw [show c • x = (c : Ω) • x from rfl, map_smul, smul_eq_mul]
      rw [this]; exact mul_mem c.2 hx

section Deg
variable {K : Type} [Fintype K] {ι : K → Type}

def seg (y : (Σ k, ι k) → Ω) : ((k : K) → ι k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩

theorem ratio_mem {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k} {p : Cpt ξ} (h : InChart ξ (seg y) c p)
    (k : K) (i : ι k) : y ⟨k, c k⟩ ≠ 0 ∧ y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h0 : ∀ l, y ⟨l, c l⟩ ≠ 0 := fun l => Finset.prod_ne_zero_iff.1 h.1 l (Finset.mem_univ _)
  refine ⟨h0 k, ?_⟩
  have := h.2 (Function.update c k i)
  have e : seg y (Function.update c k i) / seg y c = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
    unfold seg
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · simp
    · intro l _ hl
      rw [Function.update_of_ne hl, div_self (h0 l)]
    · simp
  rwa [e] at this

theorem span_chart_le {y : (Σ k, ι k) → Ω} {c c' : (k : K) → ι k} {p : Cpt ξ} (h : InChart ξ (seg y) c p)
    (h' : InChart ξ (seg y) c' p) (a : K → ℤ) (e₀ : E) :
    Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c' k⟩ ^ a k) • e₀} ≤
      Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a k) • e₀} := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  have hm : (∏ k, (y ⟨k, c' k⟩ / y ⟨k, c k⟩) ^ a k) ∈ regAt ξ p := by
    refine prod_mem fun k _ => ?_
    rcases Int.eq_nat_or_neg (a k) with ⟨n, hn | hn⟩
    · rw [hn, zpow_natCast]; exact pow_mem (ratio_mem h k _).2 _
    · rw [hn, zpow_neg, zpow_natCast, ← inv_pow, inv_div]; exact pow_mem (ratio_mem h' k _).2 _
  have e : (∏ k, y ⟨k, c' k⟩ ^ a k) • e₀ =
      (⟨_, hm⟩ : regAt ξ p) • ((∏ k, y ⟨k, c k⟩ ^ a k) • e₀) := by
    show _ = (∏ k, (y ⟨k, c' k⟩ / y ⟨k, c k⟩) ^ a k) • ((∏ k, y ⟨k, c k⟩ ^ a k) • e₀)
    rw [smul_smul, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [div_zpow, div_mul_cancel₀ _ (zpow_ne_zero _ (ratio_mem h k (c k)).1)]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem exists_isDegOn (y : (Σ k, ι k) → Ω) (a : K → ℤ) {e₀ : E} (he : e₀ ≠ 0) :
    ∃ L : Lat ξ E, L.IsDegOn Set.univ y a e₀ := by
  classical
  refine ⟨fun p => if h : ∃ c, InChart ξ (seg y) c p then
    Submodule.span (regAt ξ p) {(∏ k, y ⟨k, h.choose k⟩ ^ a k) • e₀} else ⊥, he, fun p _ c hc => ?_⟩
  have h : ∃ c, InChart ξ (seg y) c p := ⟨c, hc⟩
  show (if h : ∃ c, InChart ξ (seg y) c p then _ else _) = _
  rw [dif_pos h]
  exact le_antisymm (span_chart_le hc h.choose_spec a e₀) (span_chart_le h.choose_spec hc a e₀)

theorem isVB_of_isDegOn {o : Type} [CommRing o] [Algebra o Ω] {y : (Σ k, ι k) → Ω}
    (hT : CoordTie o ξ (seg y)) {a : K → ℤ} {e₀ : E} {L : Lat ξ E} (hL : L.IsDegOn Set.univ y a e₀) :
    L.IsVB 1 (Submodule.span Ω {e₀}) := by
  intro p _
  obtain ⟨c, hc⟩ := hT.cover p
  obtain ⟨U, -, hU⟩ := hT.affine c hc.1
  have hne : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (ratio_mem hc k (c k)).1
  refine ⟨U, (hU p.1).2 ⟨p.2, hc⟩, fun _ => (∏ k, y ⟨k, c k⟩ ^ a k) • e₀, ?_, fun q _ hq => ⟨?_, ?_⟩⟩
  · rw [Set.range_const, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hne)]
  · rw [linearIndependent_unique_iff]; exact smul_ne_zero hne hL.1
  · obtain ⟨_, hq'⟩ := (hU q.1).1 hq
    rw [Set.range_const]
    exact hL.2 q trivial c hq'

theorem isChartOf_lineBundle {o : Type} [CommRing o] [Algebra o Ω] {y : (Σ k, ι k) → Ω}
    (hT : CoordTie o ξ (seg y)) (d : ℕ) {L : Lat ξ Ω} (hL : L.IsDegOn Set.univ y (fun _ => d) 1) :
    L.IsChartOf (seg y) (ReciprocityTheory.ChartRestriction.G.Geo.lineBundle o (seg y) d).lat := by
  intro c hc e
  have key : ∀ p : Cpt ξ, InChart ξ (seg y) c p → (e ∈ L p ↔ e / seg y c ^ d ∈ regAt ξ p) := by
    intro p hp
    rw [hL.2 p trivial c hp, Submodule.mem_span_singleton]
    have : (∏ k, y ⟨k, c k⟩ ^ (d : ℤ)) • (1 : Ω) = seg y c ^ d := by
      simp [seg, Finset.prod_pow]
    rw [this]
    constructor
    · rintro ⟨s, rfl⟩
      show (s : Ω) * _ / _ ∈ _
      rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hc)]; exact s.2
    · intro h
      exact ⟨⟨_, h⟩, div_mul_cancel₀ _ (pow_ne_zero _ hc)⟩
  show e ∈ ReciprocityTheory.ChartRestriction.G.Geo.lineLat o (seg y) d c ↔ _
  rw [ReciprocityTheory.ChartRestriction.G.Geo.mem_lineLat]
  constructor
  · rintro ⟨s, hs, rfl⟩ p hp
    rw [key p hp, mul_div_cancel_right₀ _ (pow_ne_zero _ hc)]
    exact (hT.ring c hc s).1 hs p hp
  · intro h
    exact ⟨_, (hT.ring c hc _).2 fun p hp => (key p hp).1 (h p hp), div_mul_cancel₀ _ (pow_ne_zero _ hc)⟩

end Deg

theorem wedge_eq {L : Lat ξ E} {n : ℕ} {b : Fin n → E} {p : Cpt ξ} (h : L.IsFrameAt b p) (k : ℕ) :
    L.wedge k p = Submodule.span (regAt ξ p)
      (Set.range fun σ : Fin k → Fin n => exteriorPower.ιMulti Ω k (b ∘ σ)) := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    have : ∀ i, ∃ c : Fin n → regAt ξ p, ∑ j, c j • b j = v i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun _).1 (h.2 ▸ hv i)
    choose c hc using this
    have e : v = fun i => ∑ j, (c i j : Ω) • b j := funext fun i => (hc i).symm
    have e2 := (exteriorPower.ιMulti Ω k (M := E)).toMultilinearMap.map_sum (fun i j => (c i j : Ω) • b j)
    rw [e]
    refine (show exteriorPower.ιMulti Ω k (fun i => ∑ j, (c i j : Ω) • b j) = _ from e2) ▸ ?_
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [MultilinearMap.map_smul_univ]
    exact Submodule.smul_mem (R := regAt ξ p) _ (⟨∏ i, (c i (σ i) : Ω), prod_mem fun i _ => (c i (σ i)).2⟩ : regAt ξ p)
      (Submodule.subset_span (Set.mem_range_self σ))
  · refine Submodule.span_mono ?_
    rintro _ ⟨σ, rfl⟩
    exact ⟨b ∘ σ, fun i => by rw [h.2]; exact Submodule.subset_span ⟨σ i, rfl⟩, rfl⟩

theorem isDegOn_zero (L : Lat ξ E) (a : Unit → ℤ) {e₀ : E} (he : e₀ ≠ 0) :
    L.IsDegOn Set.univ (K := Unit) (ι := fun _ => Unit) (fun _ => 0) a e₀ :=
  ⟨he, fun _ _ _ hc => absurd (by simp) hc.1⟩

section Pull
variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}

theorem spec_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : X) (hq : genPt ξ ⤳ q) :
    Spec.map (CommRingCat.ofHom (genMap ξ ⟨q, hq⟩) : X.presheaf.stalk q ⟶ _) ≫ X.fromSpecStalk q = ξ := by
  show Spec.map (X.presheaf.stalkSpecializes (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ X.fromSpecStalk q = ξ
  have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) ξ
  refine Eq.trans ?_ h2
  refine Eq.trans ?_ (congrArg (fun g => Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ g) h1)
  exact (congrArg (fun g => g ≫ X.fromSpecStalk q) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)

theorem dominates_spec {f : X' ⟶ X} {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) (p' : Cpt ξ') :
    genPt ξ ⤳ f p'.1 := by
  have e : f (genPt ξ') = genPt ξ := by
    have h1 : (ξ' ≫ f) (IsLocalRing.closedPoint Ω') =
      (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω') := by rw [show ξ' ≫ f = _ from h]
    have h2 : Spec.map (CommRingCat.ofHom i) (IsLocalRing.closedPoint Ω') = IsLocalRing.closedPoint Ω :=
      Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    exact h1.trans (congrArg ξ h2)
  exact e ▸ p'.2.map f.continuous

theorem dominates_regAt {f : X' ⟶ X} {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) (p' : Cpt ξ')
    (hp : genPt ξ ⤳ f p'.1) {a : Ω} (ha : a ∈ regAt ξ ⟨f p'.1, hp⟩) : i a ∈ regAt ξ' p' := by
  obtain ⟨q, hq⟩ := p'
  obtain ⟨s, rfl⟩ := ha
  have e : f.stalkMap q ≫ (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) =
      (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) ≫ CommRingCat.ofHom i := by
    apply Spec.map_injective
    have h1 := spec_genMap ξ' q hq
    have h2 := spec_genMap ξ (f q) hp
    generalize (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) = u at h1 ⊢
    generalize (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) = v at h2 ⊢
    have h3 := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
    refine (cancel_mono (X.fromSpecStalk (f q))).1 ?_
    have l : Spec.map (f.stalkMap q ≫ u) ≫ X.fromSpecStalk (f q) = ξ' ≫ f :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        ((congrArg (fun g => Spec.map u ≫ g) h3).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f) h1)))
    have r : Spec.map (v ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (f q) = Spec.map (CommRingCat.ofHom i) ≫ ξ :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        (congrArg (fun g => Spec.map (CommRingCat.ofHom i) ≫ g) h2)
    exact l.trans (Eq.trans h r.symm)
  exact ⟨f.stalkMap q s, congrArg (fun g => g.hom s) e⟩

theorem isVB_pull {F : Type} [AddCommGroup F] [Module Ω' F] {f : X' ⟶ X} {i : Ω →+* Ω'}
    (h : Dominates ξ' ξ f i) (j : E →+ F) (hj : ∀ (a : Ω) e, j (a • e) = i a • j e)
    (hli : ∀ {r : ℕ} (b : Fin r → E), LinearIndependent Ω b → LinearIndependent Ω' (j ∘ b))
    {L : Lat ξ E} {r : ℕ} {V : Submodule Ω E} (hL : L.IsVB r V) :
    (L.pull ξ' f j).IsVB r (Submodule.span Ω' (j '' V)) := by
  intro p' _
  obtain ⟨U, hU, b, rfl, hb⟩ := hL ⟨f p'.1, dominates_spec h p'⟩ trivial
  refine ⟨f ⁻¹ᵁ U, hU, j ∘ b, ?_, fun q _ hq => ⟨hli b (hb _ trivial hU).1, ?_⟩⟩
  · apply le_antisymm
    · refine Submodule.span_mono ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨b k, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
      rw [map_sum]
      exact Submodule.sum_mem _ fun k _ => by
        rw [hj]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · have hq' := (hb ⟨f q.1, dominates_spec h q⟩ trivial hq).2
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨hs, e, he, rfl⟩
      rw [hq'] at he
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
      rw [map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      have : j (c k • b k) = (⟨i (c k), dominates_regAt h q hs (c k).2⟩ : regAt ξ' q) • j (b k) := hj _ _
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · refine Submodule.span_mono ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨dominates_spec h q, b k, hq' ▸ Submodule.subset_span ⟨k, rfl⟩, rfl⟩

end Pull

section Int

def ξZ : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))

def two : PrimeSpectrum ℤ := ⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2 Int.prime_two⟩

theorem gen_spec (q : PrimeSpectrum ℤ) : genPt ξZ ⤳ (q : Spec (CommRingCat.of ℤ)) := by
  have : PrimeSpectrum.asIdeal (R := ℤ) (genPt ξZ) ≤ q.asIdeal := by
    intro n hn
    have h1 : (n : ℚ) ∈ IsLocalRing.maximalIdeal ℚ := hn
    have : n = 0 := by simpa [IsLocalRing.maximalIdeal_eq_bot] using h1
    rw [this]; exact zero_mem _
  exact (PrimeSpectrum.le_iff_specializes (R := ℤ) _ _).1 this

def pt2 : Cpt ξZ := ⟨two, gen_spec two⟩

theorem half_notMem : (2⁻¹ : ℚ) ∉ regAt ξZ pt2 := by
  rintro ⟨s, hs⟩
  let : Algebra ℤ ((Spec (CommRingCat.of ℤ)).presheaf.stalk pt2.1) := StructureSheaf.stalkAlgebra ℤ two
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of ℤ)).presheaf.stalk pt2.1) two.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk ℤ two
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj two.asIdeal.primeCompl s
  have h := congrArg (genMap ξZ pt2) hab
  rw [map_mul, hs, eq_intCast, eq_intCast, map_intCast, map_intCast] at h
  apply b.2
  have : (b.1 : ℚ) = ((2 * a : ℤ) : ℚ) := by push_cast; simp only at h; linarith
  have hb : b.1 = 2 * a := by exact_mod_cast this
  show b.1 ∈ Ideal.span {2}
  rw [hb]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem top_not_isVB (r : ℕ) (V : Submodule ℚ ℚ) : ¬ Lat.IsVB (ξ := ξZ) (E := ℚ) (fun _ => ⊤) r V := by
  intro h
  obtain ⟨U, hU, b, -, hb⟩ := h pt2 trivial
  obtain ⟨hli, hsp⟩ := hb pt2 trivial hU
  have hr : r ≤ 1 := by simpa using hli.fintype_card_le_finrank
  have h1 : ∀ x : ℚ, x ∈ Submodule.span (regAt ξZ pt2) (Set.range b) := fun x => by
    rw [← hsp]; trivial
  interval_cases r
  · simpa using h1 1
  · have hb0 : b 0 ≠ 0 := hli.ne_zero 0
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (h1 (2⁻¹ * b 0))
    simp only [Finset.univ_unique, Finset.sum_singleton] at hc
    have : (c default : ℚ) = 2⁻¹ := mul_right_cancel₀ hb0 hc
    exact half_notMem (this ▸ (c default).2)

theorem scale_two_ne : (frameLat ξZ (fun _ : Fin 1 => (1 : ℚ))).scale 2 ≠ frameLat ξZ (fun _ : Fin 1 => (1 : ℚ)) := by
  intro h
  have h1 : (1 : ℚ) ∈ (frameLat ξZ (fun _ : Fin 1 => (1 : ℚ))).scale 2 pt2 := by
    rw [h]; exact Submodule.subset_span ⟨0, rfl⟩
  obtain ⟨x, hx, e⟩ := h1
  have e' : 2 * x = 1 := e
  have hx' : x ∈ Submodule.span (regAt ξZ pt2) (Set.range fun _ : Fin 1 => (1 : ℚ)) := hx
  rw [Set.range_const, Submodule.mem_span_singleton] at hx'
  obtain ⟨c, hc⟩ := hx'
  have hc' : (c : ℚ) * 1 = x := hc
  have : (c : ℚ) = 2⁻¹ := by linarith
  exact half_notMem (this ▸ c.2)

theorem dual_bot : Lat.dual (ξ := ξZ) (E := ℚ) (fun _ => ⊥) = fun _ => ⊤ := by
  funext p
  refine eq_top_iff.2 fun w _ e he => ?_
  rw [(Submodule.mem_bot _).1 he, map_zero]; exact zero_mem _

end Int

end GlobalTheory.CompanionTheory.Ar.LatModel
