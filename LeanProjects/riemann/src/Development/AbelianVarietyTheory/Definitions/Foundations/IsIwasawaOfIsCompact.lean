import Mathlib
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace GlobalTheory.Doubling

open scoped NNReal
open MeasureTheory

section Iwasawa

variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G)

theorem hom_pos {H : Type} [Group H] (δ : H →* ℝ≥0) (p : H) : 0 < δ p :=
  pos_iff_ne_zero.2 ((Group.isUnit p).map δ).ne_zero

def IsIwasawa : Prop := (∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) ∧ ∀ p : P, (p : G) ∈ K → δ p = 1

open Classical in

def iwAbs (g : G) : ℝ≥0 := if h : ∃ p : P, ∃ k ∈ K, g = p * k then δ h.choose else 1

theorem iwAbs_pos (g : G) : 0 < iwAbs δ K g := by
  unfold iwAbs; split_ifs
  · exact hom_pos δ _
  · exact one_pos

variable {δ K}

theorem iwAbs_mul_of_triv (h : ∀ p : P, (p : G) ∈ K → δ p = 1) (p : P) {k : G} (hk : k ∈ K) :
    iwAbs δ K (p * k) = δ p := by
  have e : ∃ p' : P, ∃ k' ∈ K, (p : G) * k = p' * k' := ⟨p, k, hk, rfl⟩
  rw [iwAbs, dif_pos e]
  obtain ⟨k', hk', e'⟩ := e.choose_spec
  have h1 := h (p⁻¹ * e.choose) (by
    have : ((p⁻¹ * e.choose : P) : G) = k * k'⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq, mul_assoc, ← e', inv_mul_cancel_left]
    rw [this]; exact mul_mem hk (inv_mem hk'))
  rw [← mul_inv_cancel_left p e.choose, map_mul, h1, mul_one]

namespace IsIwasawa

variable (h : IsIwasawa δ K)
include h

theorem iwAbs_mul (p : P) {k : G} (hk : k ∈ K) : iwAbs δ K (p * k) = δ p := iwAbs_mul_of_triv h.2 p hk

theorem iwAbs_coe (p : P) : iwAbs δ K p = δ p := by simpa using h.iwAbs_mul p (one_mem K)

theorem iwAbs_of_mem {k : G} (hk : k ∈ K) : iwAbs δ K k = 1 := by simpa using h.iwAbs_mul 1 hk

theorem iwAbs_left (p : P) (g : G) : iwAbs δ K (p * g) = δ p * iwAbs δ K g := by
  obtain ⟨p', k, hk, rfl⟩ := h.1 g
  rw [← mul_assoc, ← Subgroup.coe_mul, h.iwAbs_mul _ hk, h.iwAbs_mul _ hk, map_mul]

theorem iwAbs_right (g : G) {k : G} (hk : k ∈ K) : iwAbs δ K (g * k) = iwAbs δ K g := by
  obtain ⟨p', k', hk', rfl⟩ := h.1 g
  rw [mul_assoc, h.iwAbs_mul _ (mul_mem hk' hk), h.iwAbs_mul _ hk']

theorem eq_iwAbs {f : G → ℝ≥0} (h1 : f 1 = 1) (hl : ∀ (p : P) g, f (p * g) = δ p * f g)
    (hr : ∀ g, ∀ k ∈ K, f (g * k) = f g) : f = iwAbs δ K := funext fun g => by
  obtain ⟨p, k, hk, rfl⟩ := h.1 g
  rw [h.iwAbs_mul _ hk, hr _ _ hk, ← mul_one (p : G), hl, h1, mul_one]

end IsIwasawa

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in

theorem triv_of_isCompact (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) (p : P)
    (hp : (p : G) ∈ K) : δ p = 1 := by
  obtain ⟨C, hC⟩ := ((hP.isClosedEmbedding_subtypeVal.isCompact_preimage hK).image hδ).bddAbove
  have key : ∀ q : P, (q : G) ∈ K → δ q ≤ 1 := fun q hq => by
    by_contra hc
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hc)
    exact absurd (hC ⟨q ^ n, pow_mem hq n, map_pow δ q n⟩) (not_le.2 hn)
  refine le_antisymm (key p hp) ?_
  have := key p⁻¹ (inv_mem hp)
  rwa [map_inv, inv_le_one₀ (hom_pos δ p)] at this

omit [IsTopologicalGroup G] in
theorem isIwasawa_of_isCompact (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) : IsIwasawa δ K := ⟨h, triv_of_isCompact hP hδ hK⟩

theorem continuous_of_prod (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) {X : Type} [TopologicalSpace X] {f : G → X}
    (hf : Continuous fun x : P × K => f (x.1 * x.2)) : Continuous f := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let e : G × K ≃ₜ G × K :=
    { toFun := fun x => (x.1 * x.2, x.2), invFun := fun x => (x.1 * (x.2 : G)⁻¹, x.2)
      left_inv := fun x => by simp, right_inv := fun x => by simp
      continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }
  have hc : IsClosedMap fun x : P × K => (x.1 : G) * x.2 :=
    (isClosedMap_fst_of_compactSpace.comp e.isClosedMap).comp
      (hP.isClosedEmbedding_subtypeVal.prodMap (Topology.IsClosedEmbedding.id (X := K))).isClosedMap
  exact (hc.isQuotientMap (by fun_prop) fun g => by
    obtain ⟨p, k, hk, rfl⟩ := h g; exact ⟨(p, ⟨k, hk⟩), rfl⟩).continuous_iff.2 hf

theorem IsIwasawa.continuous_iwAbs (h : IsIwasawa δ K) (hP : IsClosed (P : Set G)) (hδ : Continuous δ)
    (hK : IsCompact (K : Set G)) : Continuous (iwAbs δ K) :=
  continuous_of_prod hP hK h.1 ((hδ.comp continuous_fst).congr fun x => (h.iwAbs_mul x.1 x.2.2).symm)

end Iwasawa

def npow (r : ℝ≥0) (t : ℂ) : ℂ := ((r : ℝ) : ℂ) ^ t

theorem npow_mul (r r' : ℝ≥0) (t : ℂ) : npow (r * r') t = npow r t * npow r' t := by
  rw [npow, NNReal.coe_mul, Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg r.2 r'.2 t

theorem npow_add {r : ℝ≥0} (hr : 0 < r) (t t' : ℂ) : npow r (t + t') = npow r t * npow r t' :=
  Complex.cpow_add _ _ (by exact_mod_cast hr.ne')

@[simp] theorem npow_zero (r : ℝ≥0) : npow r 0 = 1 := Complex.cpow_zero _
@[simp] theorem one_npow (t : ℂ) : npow 1 t = 1 := by simp [npow]

theorem norm_npow {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : ‖npow r t‖ = (r : ℝ) ^ t.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hr t

theorem npow_ne_zero {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r t ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_npow hr]; exact (Real.rpow_pos_of_pos hr _).ne'

theorem npow_eq_exp {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r t = Complex.exp (Real.log r * t) := by
  rw [npow, Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log r.coe_nonneg]

theorem continuous_npow {X : Type} [TopologicalSpace X] {f : X → ℝ≥0} (hf : Continuous f) (h : ∀ x, 0 < f x) (t : ℂ) :
    Continuous fun x => npow (f x) t := by
  simp only [npow_eq_exp (h _)]
  exact ((Complex.continuous_ofReal.comp
    ((NNReal.continuous_coe.comp hf).log fun x => (NNReal.coe_pos.2 (h x)).ne')).mul continuous_const).cexp

section Induced

variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)

def IndLaw (Φ : G → ℂ) : Prop := ∀ (p : P) (g : G), Φ (p * g) = χ p * npow (δ p) t * Φ g

def kSpan (Φ : G → ℂ) : Submodule ℂ (G → ℂ) := Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = fun g => Φ (g * k)}

def IsKFinite (Φ : G → ℂ) : Prop := FiniteDimensional ℂ (kSpan K Φ)

variable {K}

theorem isKFinite_iff {Φ : G → ℂ} : IsKFinite K Φ ↔
    ∃ W : Submodule ℂ (G → ℂ), FiniteDimensional ℂ W ∧ ∀ k ∈ K, (fun g => Φ (g * k)) ∈ W :=
  ⟨fun h => ⟨_, h, fun k hk => Submodule.subset_span ⟨k, hk, rfl⟩⟩, fun ⟨_, _, h⟩ =>
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact h k hk))⟩

theorem IsKFinite.of_invariant {Φ : G → ℂ} (h : ∀ g, ∀ k ∈ K, Φ (g * k) = Φ g) : IsKFinite K Φ :=
  isKFinite_iff.2 ⟨ℂ ∙ Φ, inferInstance, fun k hk => by
    rw [show (fun g => Φ (g * k)) = Φ from funext fun g => h g k hk]; exact Submodule.mem_span_singleton_self _⟩

theorem IsKFinite.add {Φ Ψ : G → ℂ} (h : IsKFinite K Φ) (h' : IsKFinite K Ψ) : IsKFinite K (Φ + Ψ) := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  obtain ⟨W', _, hW'⟩ := isKFinite_iff.1 h'
  exact isKFinite_iff.2 ⟨W ⊔ W', inferInstance, fun k hk => Submodule.add_mem_sup (hW k hk) (hW' k hk)⟩

theorem IsKFinite.mul_invariant {Φ f : G → ℂ} (h : IsKFinite K Φ) (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    IsKFinite K fun g => Φ g * f g := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  refine isKFinite_iff.2 ⟨W.map (LinearMap.mulRight ℂ f), inferInstance, fun k hk => ⟨_, hW k hk, funext fun g => ?_⟩⟩
  simp [hf g k hk]

theorem IsKFinite.translate {Φ : G → ℂ} (h : IsKFinite K Φ) {k : G} (hk : k ∈ K) : IsKFinite K fun g => Φ (g * k) := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  exact isKFinite_iff.2 ⟨W, inferInstance, fun k' hk' => by simpa only [mul_assoc] using hW _ (mul_mem hk' hk)⟩

variable (K)

def indSpace [TopologicalSpace G] : Submodule ℂ (G → ℂ) where
  carrier := {Φ | IndLaw δ χ t Φ ∧ Continuous Φ ∧ IsKFinite K Φ}
  zero_mem' := ⟨fun _ _ => by simp, continuous_zero, .of_invariant fun _ _ _ => rfl⟩
  add_mem' := fun h h' => ⟨fun p g => by simp only [Pi.add_apply, h.1 p g, h'.1 p g, mul_add],
    h.2.1.add h'.2.1, h.2.2.add h'.2.2⟩
  smul_mem' := fun c Φ h => ⟨fun p g => by simp only [Pi.smul_apply, h.1 p g, smul_eq_mul]; ring,
    h.2.1.const_smul c, by
      have := h.2.2.mul_invariant (f := fun _ => c) fun _ _ _ => rfl
      simp only [mul_comm _ c] at this
      exact this⟩

def flatSec (Φ : G → ℂ) (s₀ s : ℂ) : G → ℂ := fun g => Φ g * npow (iwAbs δ K g) (s - s₀)

def IsFlat (Φ : ℂ → G → ℂ) : Prop := ∀ s s', ∀ k ∈ K, Φ s k = Φ s' k

variable {δ K χ t}

theorem mem_indSpace [TopologicalSpace G] {Φ : G → ℂ} :
    Φ ∈ indSpace δ K χ t ↔ IndLaw δ χ t Φ ∧ Continuous Φ ∧ IsKFinite K Φ := Iff.rfl

theorem translate_mem_indSpace [TopologicalSpace G] [ContinuousMul G] {Φ : G → ℂ} (h : Φ ∈ indSpace δ K χ t) {k : G}
    (hk : k ∈ K) : (fun g => Φ (g * k)) ∈ indSpace δ K χ t :=
  ⟨fun p g => by simpa only [mul_assoc] using h.1 p (g * k), h.2.1.comp (continuous_mul_const k), h.2.2.translate hk⟩

@[simp] theorem flatSec_self (Φ : G → ℂ) (s₀ : ℂ) : flatSec δ K Φ s₀ s₀ = Φ := funext fun g => by simp [flatSec]

theorem flatSec_flatSec (Φ : G → ℂ) (s₀ s₁ s : ℂ) : flatSec δ K (flatSec δ K Φ s₀ s₁) s₁ s = flatSec δ K Φ s₀ s :=
  funext fun g => by
    simp only [flatSec, mul_assoc, ← npow_add (iwAbs_pos δ K g)]
    congr 2; ring

theorem norm_flatSec (Φ : G → ℂ) (s₀ s : ℂ) (g : G) :
    ‖flatSec δ K Φ s₀ s g‖ = ‖Φ g‖ * (iwAbs δ K g : ℝ) ^ (s.re - s₀.re) := by
  rw [flatSec, norm_mul, norm_npow (iwAbs_pos δ K g), Complex.sub_re]

theorem IndLaw.ext (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) {Φ Ψ : G → ℂ} (h1 : IndLaw δ χ t Φ) (h2 : IndLaw δ χ t Ψ)
    (e : ∀ k ∈ K, Φ k = Ψ k) : Φ = Ψ := funext fun g => by
  obtain ⟨p, k, hk, rfl⟩ := h g
  rw [h1, h2, e k hk]

namespace IsIwasawa

variable (h : IsIwasawa δ K)
include h

theorem flatSec_of_mem (Φ : G → ℂ) (s₀ s : ℂ) {k : G} (hk : k ∈ K) : flatSec δ K Φ s₀ s k = Φ k := by
  simp [flatSec, h.iwAbs_of_mem hk]

theorem isFlat_flatSec (Φ : G → ℂ) (s₀ : ℂ) : IsFlat K (flatSec δ K Φ s₀) := fun s s' k hk => by
  rw [h.flatSec_of_mem _ _ _ hk, h.flatSec_of_mem _ _ _ hk]

theorem indLaw_flatSec {Φ : G → ℂ} {ρ s₀ : ℂ} (hΦ : IndLaw δ χ (s₀ + ρ) Φ) (s : ℂ) :
    IndLaw δ χ (s + ρ) (flatSec δ K Φ s₀ s) := fun p g => by
  rw [flatSec, flatSec, hΦ, h.iwAbs_left, npow_mul, show s + ρ = (s₀ + ρ) + (s - s₀) by ring,
    npow_add (hom_pos δ p) _ (s - s₀)]
  ring

theorem eq_flatSec {Φ : ℂ → G → ℂ} {ρ : ℂ} (hΦ : ∀ s, IndLaw δ χ (s + ρ) (Φ s)) (hf : IsFlat K Φ) (s₀ s : ℂ) :
    Φ s = flatSec δ K (Φ s₀) s₀ s :=
  IndLaw.ext h.1 (hΦ s) (h.indLaw_flatSec (hΦ s₀) s) fun k hk => by rw [h.flatSec_of_mem _ _ _ hk, hf s s₀ k hk]

theorem norm_le {Φ : G → ℂ} (hΦ : IndLaw δ χ t Φ) {C : ℝ} (hC : ∀ k ∈ K, ‖Φ k‖ ≤ C) (g : G) :
    ‖Φ g‖ ≤ C * (iwAbs δ K g : ℝ) ^ t.re := by
  obtain ⟨p, k, hk, rfl⟩ := h.1 g
  rw [hΦ, h.iwAbs_mul _ hk, norm_mul, norm_mul, Circle.norm_coe, one_mul, norm_npow (hom_pos δ p), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC k hk) (by positivity)

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem flatSec_mem (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) {Φ : G → ℂ}
    {ρ s₀ : ℂ} (hΦ : Φ ∈ indSpace δ K χ (s₀ + ρ)) (s : ℂ) : flatSec δ K Φ s₀ s ∈ indSpace δ K χ (s + ρ) :=
  ⟨h.indLaw_flatSec hΦ.1 s, hΦ.2.1.mul (continuous_npow (h.continuous_iwAbs hP hδ hK) (iwAbs_pos δ K) _),
    hΦ.2.2.mul_invariant (f := fun g => npow (iwAbs δ K g) (s - s₀)) fun g k hk => by rw [h.iwAbs_right g hk]⟩

theorem npow_iwAbs_mem (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) (t : ℂ) :
    (fun g => npow (iwAbs δ K g) t) ∈ indSpace δ K 1 t :=
  ⟨fun p g => by simp [h.iwAbs_left, npow_mul], continuous_npow (h.continuous_iwAbs hP hδ hK) (iwAbs_pos δ K) _,
    .of_invariant fun g k hk => by rw [h.iwAbs_right g hk]⟩

end IsIwasawa

def IsRightSmooth [TopologicalSpace G] (Φ : G → ℂ) : Prop :=
  ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g, ∀ u ∈ U, Φ (g * u) = Φ g

theorem IsRightSmooth.continuous [TopologicalSpace G] [IsTopologicalGroup G] {Φ : G → ℂ} (h : IsRightSmooth Φ) :
    Continuous Φ := by
  obtain ⟨U, hU, h⟩ := h
  refine continuous_iff_continuousAt.2 fun x => (continuousAt_const (y := Φ x)).congr ?_
  filter_upwards [(hU.preimage (continuous_const_mul x⁻¹)).mem_nhds (x := x) (by simp)] with y hy
  rw [← h x _ hy, mul_inv_cancel_left]

theorem IsRightSmooth.isKFinite [TopologicalSpace G] [IsTopologicalGroup G] {Φ : G → ℂ} (h : IsRightSmooth Φ)
    (hK : IsCompact (K : Set G)) : IsKFinite K Φ := by
  obtain ⟨U, hU, h⟩ := h
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun x : G => (fun y => x⁻¹ * y) ⁻¹' (U : Set G))
    (fun x => hU.preimage (continuous_const_mul x⁻¹)) fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩
  refine isKFinite_iff.2 ⟨Submodule.span ℂ ((fun x g => Φ (g * x)) '' (T : Set G)),
    FiniteDimensional.span_of_finite ℂ (T.finite_toSet.image _), fun k hk => ?_⟩
  obtain ⟨x, hx, hu⟩ := Set.mem_iUnion₂.1 (hT hk)
  refine Submodule.subset_span ⟨x, hx, funext fun g => ?_⟩
  change Φ (g * x) = Φ (g * k)
  rw [← h (g * x) _ hu, mul_assoc, mul_inv_cancel_left]

theorem IsRightSmooth.mem_indSpace [TopologicalSpace G] [IsTopologicalGroup G] {Φ : G → ℂ} (h : IsRightSmooth Φ)
    (hK : IsCompact (K : Set G)) (hl : IndLaw δ χ t Φ) : Φ ∈ indSpace δ K χ t := ⟨hl, h.continuous, h.isKFinite hK⟩

end Induced

section ZetaNonvanishing₂

variable {H : Type} {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def coef (π : H → X → X) (x y : X) : H → ℂ := fun g => inner ℂ y (π g x)

theorem conj_coef (π : H → X → X) (x y : X) (g : H) : starRingEnd ℂ (coef π x y g) = inner ℂ (π g x) y :=
  inner_conj_symm _ _

variable [MeasurableSpace H] (m : Measure H)

def pairInt (f c : H → ℂ) : ℂ := ∫ g, f g * starRingEnd ℂ (c g) ∂m

def PairConv (f c : H → ℂ) : Prop := Integrable (fun g => f g * starRingEnd ℂ (c g)) m

end ZetaNonvanishing₂

example {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (x y : X) (c : ℂ) :
    coef (fun _ : Unit => id) (c • x) y () = c * coef (fun _ : Unit => id) x y () := inner_smul_right _ _ _

example {G : Type} [Group G] (δ : (⊤ : Subgroup G) →* ℝ≥0) : IsIwasawa δ ⊥ :=
  ⟨fun g => ⟨⟨g, trivial⟩, 1, one_mem _, (mul_one g).symm⟩, fun p hp => by
    rw [show p = 1 from Subtype.ext hp, map_one]⟩

end GlobalTheory.Doubling

end
