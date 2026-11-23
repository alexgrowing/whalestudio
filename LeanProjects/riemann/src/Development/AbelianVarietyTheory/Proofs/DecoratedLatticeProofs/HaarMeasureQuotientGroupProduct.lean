import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralOneDoubleCosetEqMulValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEqSumIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IterPeel

section Alg

variable {G₁ G₂ : Type} [Group G₁] [MeasurableSpace G₁] [TopologicalSpace G₁] [Group G₂] [MeasurableSpace G₂]
  [TopologicalSpace G₂] {R₁ : Subgroup G₁} {R₂ : Subgroup G₂} {ρ₁ : Measure R₁} {μ₁ : Measure G₁} {ρ₂ : Measure R₂}
  {μ₂ : Measure G₂}

theorem quot_congr {f f' : G₁ → ℂ} {z z' : ℂ} (h : IsQuotIntL1 ρ₁ μ₁ f z) (hf : ∀ x, f x = f' x) (hz : z = z') :
    IsQuotIntL1 ρ₁ μ₁ f' z' := by
  obtain rfl : f = f' := funext hf
  exact hz ▸ h

theorem iterated_integral_congr {f f' : G₁ → G₂ → ℂ} {z z' : ℂ} (h : Iter2 ρ₁ μ₁ ρ₂ μ₂ f z) (hf : ∀ x y, f x y = f' x y)
    (hz : z = z') : Iter2 ρ₁ μ₁ ρ₂ μ₂ f' z' := by
  obtain rfl : f = f' := funext fun x => funext fun y => hf x y
  exact hz ▸ h

theorem iterated_integral_zero : Iter2 ρ₁ μ₁ ρ₂ μ₂ 0 0 :=
  ⟨0, IsQuotIntL1.zero, fun _ => IsQuotIntL1.zero⟩

theorem iterated_integral_add {f f' : G₁ → G₂ → ℂ} {z z' : ℂ} (h : Iter2 ρ₁ μ₁ ρ₂ μ₂ f z) (h' : Iter2 ρ₁ μ₁ ρ₂ μ₂ f' z') :
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (f + f') (z + z') := by
  obtain ⟨g, hg, hq⟩ := h
  obtain ⟨g', hg', hq'⟩ := h'
  exact ⟨g + g', hg.add hg', fun q => (hq q).add (hq' q)⟩

theorem iterated_integral_mul {u : G₁ → ℂ} {v : G₂ → ℂ} {c d : ℂ} (hu : IsQuotIntL1 ρ₁ μ₁ u c) (hv : IsQuotIntL1 ρ₂ μ₂ v d) :
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => u x * v y) (c * d) :=
  ⟨fun x => u x * d, quot_congr (hu.smul d) (fun x => by simp [mul_comm]) (mul_comm _ _),
    fun x => quot_congr (hv.smul (u x)) (fun y => by simp) rfl⟩

end Alg

theorem iterated_integral_unique {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [SecondCountableTopology G₁]
    [LocallyCompactSpace G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂]
    [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [LocallyCompactSpace G₂] [T2Space G₂] [MeasurableSpace G₂]
    [BorelSpace G₂] {R₁ : Subgroup G₁} {R₂ : Subgroup G₂} (hR₁ : IsClosed (R₁ : Set G₁)) (hR₂ : IsClosed (R₂ : Set G₂))
    {ρ₁ : Measure R₁} {μ₁ : Measure G₁} {ρ₂ : Measure R₂} {μ₂ : Measure G₂} [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure]
    [ρ₁.IsHaarMeasure] [ρ₂.IsHaarMeasure] [ρ₁.IsInvInvariant] [ρ₂.IsInvInvariant] {f : G₁ → G₂ → ℂ} {z z' : ℂ}
    (h : Iter2 ρ₁ μ₁ ρ₂ μ₂ f z) (h' : Iter2 ρ₁ μ₁ ρ₂ μ₂ f z') : z = z' := by
  obtain ⟨g, hg, hq⟩ := h
  obtain ⟨g', hg', hq'⟩ := h'
  have e : g = g' := funext fun q => (hq q).unique hR₂ (hq' q)
  subst e
  exact hg.unique hR₁ hg'

section Prod

variable {A B : Type} [Group A] [MeasurableSpace A] [Group B] [MeasurableSpace B] (R : Subgroup A) (S : Subgroup B)

def prodMEquiv : R.prod S ≃ᵐ R × S where
  toEquiv := (R.prodEquiv S).toEquiv
  measurable_toFun := by
    change Measurable fun x : R.prod S => ((⟨x.1.1, x.2.1⟩ : R), (⟨x.1.2, x.2.2⟩ : S))
    exact (measurable_fst.comp measurable_subtype_coe).subtype_mk.prodMk
      (measurable_snd.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := by
    change Measurable fun q : R × S => (⟨((q.1 : A), (q.2 : B)), ⟨q.1.2, q.2.2⟩⟩ : R.prod S)
    exact ((measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)).subtype_mk

theorem quot_prod {r : Measure R} {s : Measure S} {a : Measure A} {b : Measure B} [SFinite r] [SFinite s] [SFinite a]
    [SFinite b] (p : Measure (R.prod S)) (hp : p.map (R.prodEquiv S) = r.prod s) {u : A → ℂ} {v : B → ℂ} {c d : ℂ}
    (hu : IsQuotIntL1 r a u c) (hv : IsQuotIntL1 s b v d) :
    IsQuotIntL1 p (a.prod b) (fun X => u X.1 * v X.2) (c * d) := by
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := hu
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := hv
  have hp' : p.map (prodMEquiv R S) = r.prod s := hp
  refine ⟨fun X => U X.1 * V X.2, hU1.mul_prod hV1, fun X => ?_, fun X => ?_, ?_⟩
  · have := (hU2 X.1).mul_prod (hV2 X.2)
    rw [← hp', integrable_map_equiv] at this
    exact this
  · have e := integral_map_equiv (μ := p) (prodMEquiv R S)
      (fun q : R × S => U ((q.1 : A) * X.1) * V ((q.2 : B) * X.2))
    have e2 := integral_prod_mul (μ := r) (ν := s) (fun q : R => U ((q : A) * X.1)) (fun q : S => V ((q : B) * X.2))
    rw [hp'] at e
    show u X.1 * v X.2 = _
    rw [hU3, hV3, ← e2, e]
    rfl
  · rw [integral_prod_mul, hU4, hV4]

end Prod

end GlobalTheory.IterPeel

namespace GlobalTheory.IterPeel

section Cells

variable {G : Type} [Group G]

def cell (R K : Subgroup G) (t : G) : Set G := {x | ∃ r ∈ R, ∃ κ ∈ K, x = r * t * κ}

def chi (R K : Subgroup G) (t : G) (x : G) : ℂ := (cell R K t).indicator 1 x

theorem mul_mem_cell_left {R K : Subgroup G} {t x s : G} (hs : s ∈ R) : s * x ∈ cell R K t ↔ x ∈ cell R K t := by
  constructor
  · rintro ⟨r, hr, κ, hκ, h⟩
    refine ⟨s⁻¹ * r, R.mul_mem (R.inv_mem hs) hr, κ, hκ, ?_⟩
    calc x = s⁻¹ * (s * x) := by group
      _ = s⁻¹ * (r * t * κ) := by rw [h]
      _ = s⁻¹ * r * t * κ := by group
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    exact ⟨s * r, R.mul_mem hs hr, κ, hκ, by group⟩

theorem mul_mem_cell_right {R K : Subgroup G} {t x k : G} (hk : k ∈ K) : x * k ∈ cell R K t ↔ x ∈ cell R K t := by
  constructor
  · rintro ⟨r, hr, κ, hκ, h⟩
    refine ⟨r, hr, κ * k⁻¹, K.mul_mem hκ (K.inv_mem hk), ?_⟩
    calc x = (x * k) * k⁻¹ := by group
      _ = (r * t * κ) * k⁻¹ := by rw [h]
      _ = r * t * (κ * k⁻¹) := by group
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    exact ⟨r, hr, κ * k, K.mul_mem hκ hk, by group⟩

theorem decomp {M : Type} [AddCommMonoid M] (R K : Subgroup G) (T : Finset G) : ∀ φ : G → M,
    (∀ r ∈ R, ∀ x, φ (r * x) = φ x) → (∀ κ ∈ K, ∀ x, φ (x * κ) = φ x) →
    (∀ x, φ x ≠ 0 → ∃ t ∈ T, x ∈ cell R K t) →
    ∃ c : G → M, (∀ t, c t = 0 ∨ c t = φ t) ∧ ∀ x, φ x = ∑ t ∈ T, (cell R K t).indicator (fun _ => c t) x := by
  first
  | exact @_root_.GlobalTheory.DoubleCosetIndicator.main
  | exact _root_.GlobalTheory.DoubleCosetIndicator.main
  | (apply _root_.GlobalTheory.DoubleCosetIndicator.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DoubleCosetIndicator.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DoubleCosetIndicator.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DoubleCosetIndicator.main ..)

theorem indicator_fun_apply {X Y : Type} (s : Set X) (c : Y → ℂ) (x : X) (y : Y) :
    (s.indicator (fun _ => c) x) y = s.indicator 1 x * c y := by
  classical
  by_cases h : x ∈ s <;> simp [h]

theorem indicator_const_eq {X : Type} (s : Set X) (m : ℂ) (x : X) :
    s.indicator (fun _ => m) x = s.indicator 1 x * m := by
  classical
  by_cases h : x ∈ s <;> simp [h]

end Cells

theorem mem_cell_prod {A B : Type} [Group A] [Group B] (R K : Subgroup A) (S L : Subgroup B) (t X : A × B) :
    X ∈ cell (R.prod S) (K.prod L) t ↔ X.1 ∈ cell R K t.1 ∧ X.2 ∈ cell S L t.2 := by
  constructor
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    rw [Subgroup.mem_prod] at hr hκ
    exact ⟨⟨r.1, hr.1, κ.1, hκ.1, rfl⟩, ⟨r.2, hr.2, κ.2, hκ.2, rfl⟩⟩
  · rintro ⟨⟨r, hr, κ, hκ, h1⟩, ⟨r', hr', κ', hκ', h2⟩⟩
    exact ⟨(r, r'), Subgroup.mem_prod.2 ⟨hr, hr'⟩, (κ, κ'), Subgroup.mem_prod.2 ⟨hκ, hκ'⟩, Prod.ext h1 h2⟩

theorem chi_prod {A B : Type} [Group A] [Group B] (R K : Subgroup A) (S L : Subgroup B) (t X : A × B) :
    chi (R.prod S) (K.prod L) t X = chi R K t.1 X.1 * chi S L t.2 X.2 := by
  classical
  simp only [chi, Set.indicator_apply, mem_cell_prod, Pi.one_apply]
  split_ifs <;> simp_all

theorem quot_chi {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G)
    (hR : IsClosed (R : Set G)) (hK : IsCO K) (ρ : Measure R) (μ : Measure G) [ρ.IsHaarMeasure] [ρ.IsInvInvariant]
    [μ.IsHaarMeasure] (t : G) : ∃ w, IsQuotIntL1 ρ μ (chi R K t) w := by
  classical
  have : ρ.IsMulRightInvariant := by rw [← Measure.inv_eq_self ρ]; infer_instance
  obtain ⟨w, -, hw⟩ := quotientIntegral_oneDoubleCoset_eq_mul_value G R K hR hK.2 hK.1 ρ μ inferInstance inferInstance inferInstance t
  refine ⟨_, hw _ ?_ ?_ ?_⟩
  · intro r hr g; by_cases h : g ∈ cell R K t <;> simp [chi, h, mul_mem_cell_left hr]
  · intro k hk g; by_cases h : g ∈ cell R K t <;> simp [chi, h, mul_mem_cell_right hk]
  · intro g hg
    by_contra h
    have h' : g ∉ cell R K t := h
    exact hg (by unfold chi; exact Set.indicator_of_notMem h' _)

end GlobalTheory.IterPeel

namespace GlobalTheory.IterPeel

theorem iterated_integral_product_groups : ∀ (A₁ : Type) [Group A₁] [TopologicalSpace A₁] [IsTopologicalGroup A₁] [SecondCountableTopology A₁] [LocallyCompactSpace A₁] [T2Space A₁] [MeasurableSpace A₁] [BorelSpace A₁] (B₁ : Type) [Group B₁] [TopologicalSpace B₁] [IsTopologicalGroup B₁] [SecondCountableTopology B₁] [LocallyCompactSpace B₁] [T2Space B₁] [MeasurableSpace B₁] [BorelSpace B₁] (A₂ : Type) [Group A₂] [TopologicalSpace A₂] [IsTopologicalGroup A₂] [SecondCountableTopology A₂] [LocallyCompactSpace A₂] [T2Space A₂] [MeasurableSpace A₂] [BorelSpace A₂] (B₂ : Type) [Group B₂] [TopologicalSpace B₂] [IsTopologicalGroup B₂] [SecondCountableTopology B₂] [LocallyCompactSpace B₂] [T2Space B₂] [MeasurableSpace B₂] [BorelSpace B₂] (R₁ : Subgroup A₁) (S₁ : Subgroup B₁) (R₂ : Subgroup A₂) (S₂ : Subgroup B₂), IsClosed (R₁ : Set A₁) → IsClosed (S₁ : Set B₁) → IsClosed (R₂ : Set A₂) → IsClosed (S₂ : Set B₂) → ∀ (a₁ : Measure A₁) (b₁ : Measure B₁) (a₂ : Measure A₂) (b₂ : Measure B₂) (r₁ : Measure R₁) (s₁ : Measure S₁) (r₂ : Measure R₂) (s₂ : Measure S₂) (p₁ : Measure (R₁.prod S₁)) (p₂ : Measure (R₂.prod S₂)), a₁.IsHaarMeasure → b₁.IsHaarMeasure → a₂.IsHaarMeasure → b₂.IsHaarMeasure → r₁.IsHaarMeasure → s₁.IsHaarMeasure → r₂.IsHaarMeasure → s₂.IsHaarMeasure → r₁.IsInvInvariant → s₁.IsInvInvariant → r₂.IsInvInvariant → s₂.IsInvInvariant → p₁.map (R₁.prodEquiv S₁) = r₁.prod s₁ → p₂.map (R₂.prodEquiv S₂) = r₂.prod s₂ → ∀ (K₁ : Subgroup A₁) (L₁ : Subgroup B₁) (K₂ : Subgroup A₂) (L₂ : Subgroup B₂), IsCO K₁ → IsCO L₁ → IsCO K₂ → IsCO L₂ → ∀ f : A₁ × B₁ → A₂ × B₂ → ℂ, (∀ x y, ∀ r ∈ R₂.prod S₂, ∀ κ ∈ K₂.prod L₂, f x (r * y * κ) = f x y) → (∀ x y, ∀ κ ∈ K₁.prod L₁, f (x * κ) y = f x y) → (∀ x y, ∀ r ∈ R₁.prod S₁, f (r * x) y = f x y) → (∃ T : Finset (A₁ × B₁), ∀ x y, f x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ R₁.prod S₁, ∃ κ ∈ K₁.prod L₁, x = r * t * κ) → (∀ x, ∃ T : Finset (A₂ × B₂), ∀ y, f x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ R₂.prod S₂, ∃ κ ∈ K₂.prod L₂, y = r * t * κ) → ∀ (g : A₁ → A₂ → ℂ) (z : ℂ), (∀ x y, Iter2 s₁ b₁ s₂ b₂ (fun x' y' => f (x, x') (y, y')) (g x y)) → Iter2 r₁ a₁ r₂ a₂ g z → Iter2 p₁ (a₁.prod b₁) p₂ (a₂.prod b₂) f z := by
  intro A₁ _ _ _ _ _ _ _ _ B₁ _ _ _ _ _ _ _ _ A₂ _ _ _ _ _ _ _ _ B₂ _ _ _ _ _ _ _ _ R₁ S₁ R₂ S₂ hR₁ hS₁ hR₂ hS₂
    a₁ b₁ a₂ b₂ r₁ s₁ r₂ s₂ p₁ p₂ ha₁ hb₁ ha₂ hb₂ hr₁ hs₁ hr₂ hs₂ hir₁ his₁ hir₂ his₂ hp₁ hp₂ K₁ L₁ K₂ L₂
    hK₁ hL₁ hK₂ hL₂ f hfy hfx hfl hTx hTy g z hg hz
  classical
  haveI : LocallyCompactSpace R₁ := hR₁.locallyCompactSpace
  haveI : LocallyCompactSpace S₁ := hS₁.locallyCompactSpace
  haveI : LocallyCompactSpace R₂ := hR₂.locallyCompactSpace
  haveI : LocallyCompactSpace S₂ := hS₂.locallyCompactSpace

  let P : (A₁ × B₁ → A₂ × B₂ → ℂ) → Prop := fun F => ∃ (G : A₁ → A₂ → ℂ) (Z : ℂ),
    (∀ x y, Iter2 s₁ b₁ s₂ b₂ (fun x' y' => F (x, x') (y, y')) (G x y)) ∧ Iter2 r₁ a₁ r₂ a₂ G Z ∧
      Iter2 p₁ (a₁.prod b₁) p₂ (a₂.prod b₂) F Z
  have P0 : P 0 := ⟨0, 0, fun x y => iterated_integral_zero, iterated_integral_zero, iterated_integral_zero⟩
  have Padd : ∀ F F', P F → P F' → P (F + F') := by
    rintro F F' ⟨G, Z, h1, h2, h3⟩ ⟨G', Z', h1', h2', h3'⟩
    exact ⟨G + G', Z + Z', fun x y => iterated_integral_add (h1 x y) (h1' x y), iterated_integral_add h2 h2', iterated_integral_add h3 h3'⟩
  have Pel : ∀ (t : A₁ × B₁) (u : A₂ × B₂) (d : ℂ),
      P (fun X Y => d * (chi (R₁.prod S₁) (K₁.prod L₁) t X * chi (R₂.prod S₂) (K₂.prod L₂) u Y)) := by
    intro t u d
    obtain ⟨w₁, hw₁⟩ := quot_chi R₁ K₁ hR₁ hK₁ r₁ a₁ t.1
    obtain ⟨w₁', hw₁'⟩ := quot_chi S₁ L₁ hS₁ hL₁ s₁ b₁ t.2
    obtain ⟨w₂, hw₂⟩ := quot_chi R₂ K₂ hR₂ hK₂ r₂ a₂ u.1
    obtain ⟨w₂', hw₂'⟩ := quot_chi S₂ L₂ hS₂ hL₂ s₂ b₂ u.2
    refine ⟨fun x y => d * w₁' * w₂' * chi R₁ K₁ t.1 x * chi R₂ K₂ u.1 y, d * w₁' * w₂' * w₁ * w₂,
      fun x y => ?_, ?_, ?_⟩
    · refine iterated_integral_congr (iterated_integral_mul (hw₁'.smul (d * chi R₁ K₁ t.1 x * chi R₂ K₂ u.1 y)) hw₂') (fun x' y' => ?_) (by ring)
      simp only [chi_prod, Pi.smul_apply, smul_eq_mul]
      ring
    · refine iterated_integral_congr (iterated_integral_mul (hw₁.smul (d * w₁' * w₂')) hw₂) (fun x y => ?_) (by ring)
      simp only [Pi.smul_apply, smul_eq_mul]
    · refine iterated_integral_congr (iterated_integral_mul ((quot_prod R₁ S₁ p₁ hp₁ hw₁ hw₁').smul d) (quot_prod R₂ S₂ p₂ hp₂ hw₂ hw₂'))
        (fun X Y => ?_) (by ring)
      simp only [chi_prod, Pi.smul_apply, smul_eq_mul]
      ring

  obtain ⟨T, hT⟩ := hTx
  obtain ⟨c, hc, hce⟩ := decomp (M := A₂ × B₂ → ℂ) (R₁.prod S₁) (K₁.prod L₁) T f
    (fun r hr x => funext fun y => hfl x y r hr) (fun κ hκ x => funext fun y => hfx x y κ hκ)
    (fun x hx => by
      obtain ⟨y, hy⟩ : ∃ y, f x y ≠ 0 := by
        by_contra h; push_neg at h; exact hx (funext h)
      obtain ⟨t, ht, r, hr, κ, hκ, e⟩ := hT x y hy
      exact ⟨t, ht, r, hr, κ, hκ, e⟩)
  have hY : ∀ t, ∃ (U : Finset (A₂ × B₂)) (d : A₂ × B₂ → ℂ),
      ∀ y, c t y = ∑ u ∈ U, (cell (R₂.prod S₂) (K₂.prod L₂) u).indicator (fun _ => d u) y := by
    intro t
    rcases hc t with h | h
    · exact ⟨∅, 0, fun y => by simp [h]⟩
    · obtain ⟨U, hU⟩ := hTy t
      obtain ⟨d, -, hd⟩ := decomp (M := ℂ) (R₂.prod S₂) (K₂.prod L₂) U (f t)
        (fun r hr y => by simpa using hfy t y r hr 1 (Subgroup.one_mem _))
        (fun κ hκ y => by simpa using hfy t y 1 (Subgroup.one_mem _) κ hκ)
        (fun y hy => by
          obtain ⟨u, hu, r, hr, κ, hκ, e⟩ := hU y hy
          exact ⟨u, hu, r, hr, κ, hκ, e⟩)
      exact ⟨U, d, fun y => by rw [h, hd y]⟩
  choose U d hd using hY
  have hfe : f = ∑ t ∈ T, ∑ u ∈ U t,
      (fun X Y => d t u * (chi (R₁.prod S₁) (K₁.prod L₁) t X * chi (R₂.prod S₂) (K₂.prod L₂) u Y)) := by
    funext X Y
    rw [hce X, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_apply, Finset.sum_apply, indicator_fun_apply, hd t Y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [indicator_const_eq]
    simp only [chi]
    ring
  have hPf : P f := by
    rw [hfe]
    refine Finset.sum_induction _ P Padd P0 fun t _ => ?_
    exact Finset.sum_induction _ P Padd P0 fun u _ => Pel t u (d t u)
  obtain ⟨G, Z, h1, h2, h3⟩ := hPf
  have hG : G = g := funext fun x => funext fun y => iterated_integral_unique hS₁ hS₂ (h1 x y) (hg x y)
  subst hG
  rw [← iterated_integral_unique hR₁ hR₂ h2 hz]
  exact h3

end GlobalTheory.IterPeel
