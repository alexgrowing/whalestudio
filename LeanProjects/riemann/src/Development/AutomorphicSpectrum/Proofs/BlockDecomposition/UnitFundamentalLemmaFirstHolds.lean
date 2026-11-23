import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open MeasureTheory Polynomial PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.UnitFL

noncomputable section

theorem exists_doubleCoset_reps {G : Type*} [Group G] (H K : Subgroup G) (A : Set G)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, (∃ h ∈ H, ∃ κ ∈ K, a' = h * a * κ) → a = a') :
    ∃ R : Set G, A ⊆ R ∧ (∀ g, ∃ r ∈ R, ∃ h ∈ H, ∃ κ ∈ K, g = h * r * κ) ∧
      (∀ r ∈ R, ∀ r' ∈ R, (∃ h ∈ H, ∃ κ ∈ K, r' = h * r * κ) → r = r') := by
  classical
  let s : Setoid G :=
    { r := fun a b => ∃ h ∈ H, ∃ κ ∈ K, b = h * a * κ
      iseqv := ⟨fun a => ⟨1, H.one_mem, 1, K.one_mem, by simp⟩,
        fun {a b} ⟨h, hh, κ, hκ, e⟩ => ⟨h⁻¹, H.inv_mem hh, κ⁻¹, K.inv_mem hκ, by rw [e]; group⟩,
        fun {a b c} ⟨h, hh, κ, hκ, e⟩ ⟨h', hh', κ', hκ', e'⟩ =>
          ⟨h' * h, H.mul_mem hh' hh, κ * κ', K.mul_mem hκ hκ', by rw [e', e]; group⟩⟩ }
  let f : Quotient s → G := fun q =>
    if hq : ∃ a ∈ A, (Quotient.mk s a) = q then hq.choose else q.out
  have hf : ∀ q, Quotient.mk s (f q) = q := by
    intro q
    by_cases hq : ∃ a ∈ A, (Quotient.mk s a) = q
    · simp only [f, dif_pos hq]; exact hq.choose_spec.2
    · simp only [f, dif_neg hq]; exact Quotient.out_eq q
  refine ⟨Set.range f, ?_, ?_, ?_⟩
  · intro a ha
    have hq : ∃ a' ∈ A, Quotient.mk s a' = Quotient.mk s a := ⟨a, ha, rfl⟩
    refine ⟨Quotient.mk s a, ?_⟩
    simp only [f, dif_pos hq]
    exact hA _ hq.choose_spec.1 _ ha (Quotient.exact hq.choose_spec.2)
  · intro g
    exact ⟨f (Quotient.mk s g), ⟨_, rfl⟩, Quotient.exact (hf (Quotient.mk s g))⟩
  · rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ hr
    have : q = q' := by
      rw [← hf q, ← hf q']
      exact Quotient.sound hr
    rw [this]

theorem tsum_match {α β : Type*} (Rα : Set α) (Rβ : Set β) (T : Set β) (hT : T ⊆ Rβ) (φ : β → α)
    (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) (hφ : Set.InjOn φ T) (hm : ∀ t ∈ T, φ t ∈ Rα)
    (hf : ∀ a ∈ Rα, f a ≠ 0 → a ∈ φ '' T) (hg : ∀ b ∈ Rβ, g b ≠ 0 → b ∈ T)
    (hfg : ∀ t ∈ T, f (φ t) = g t) :
    ∑' a : Rα, f a = ∑' b : Rβ, g b := by
  have h1 : ∑' t : T, f (φ t) = ∑' a : Rα, f a := by
    refine Function.Injective.tsum_eq (g := fun t : T => (⟨φ t, hm t t.2⟩ : Rα))
      (f := fun a : Rα => f a) ?_ ?_
    · intro a b hab
      exact Subtype.ext (hφ a.2 b.2 (congrArg Subtype.val hab))
    · intro a ha
      obtain ⟨t, ht, e⟩ := hf a a.2 ha
      exact ⟨⟨t, ht⟩, Subtype.ext e⟩
  have h2 : ∑' t : T, g t = ∑' b : Rβ, g b := by
    refine Function.Injective.tsum_eq (g := fun t : T => (⟨t, hT t.2⟩ : Rβ))
      (f := fun b : Rβ => g b) ?_ ?_
    · intro a b hab
      exact Subtype.ext (congrArg (fun x : Rβ => (x : β)) hab)
    · intro b hb
      exact ⟨⟨b, hg b b.2 hb⟩, rfl⟩
  rw [← h1, ← h2]
  exact tsum_congr fun t => hfg t t.2

theorem twNorm_mul' {G : Type*} [Group G] (θ : Monoid.End G) (a b : G)
    (hc : ∀ i j : ℕ, Commute ((θ ^ i) a) ((θ ^ j) b)) (m : ℕ) :
    twNorm θ m (a * b) = twNorm θ m a * twNorm θ m b := by
  have hN : ∀ (m j : ℕ), Commute ((θ ^ j) a) (twNorm θ m b) := by
    intro m j
    induction m with
    | zero => simp
    | succ m ih =>
      rw [twNorm_succ]
      exact ih.mul_right (hc j m)
  induction m with
  | zero => simp
  | succ m ih =>
    rw [twNorm_succ, twNorm_succ, twNorm_succ, ih, map_mul, mul_assoc, mul_assoc,
      ← mul_assoc (twNorm θ m b), ← (hN m m).eq, mul_assoc]

theorem twNorm_one' {G : Type*} [Group G] (θ : Monoid.End G) (m : ℕ) : twNorm θ m (1 : G) = 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [twNorm_succ, ih]; simp

theorem twConj_mul' {G : Type*} [Group G] (θ : Monoid.End G) (a b d : G) :
    twConj θ (a * b) d = twConj θ b (twConj θ a d) := by
  simp only [twConj, map_mul]
  group

theorem exists_matching_reps {G₁ G₂ : Type*} [Group G₁] [Group G₂] (ι : G₁ →* G₂)
    (θ : Monoid.End G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (c w δ : G₂)
    (hι : ∀ g, ι g ∈ K₂ ↔ g ∈ K₁) (hθι : ∀ g, θ (ι g) = ι g)
    (hc : twConj θ w δ = c)
    (hL4 : ∀ g, twConj θ g c ∈ K₂ ↔ (g⁻¹ * θ g ∈ K₂ ∧ g⁻¹ * ι γ * g ∈ K₂))
    (hcent : twCent θ c = (Subgroup.centralizer {γ}).map ι)
    (hH3 : ∀ x, x ∈ twCent θ c ↔ w * x * w⁻¹ ∈ twCent θ δ)
    (hL3 : ∀ g, g⁻¹ * θ g ∈ K₂ → ∃ y, (ι y)⁻¹ * g ∈ K₂)
    (R₁ : Set G₁)
    (hR₁c : ∀ g, ∃ r ∈ R₁, ∃ t ∈ Subgroup.centralizer {γ}, ∃ κ ∈ K₁, g = t * r * κ)
    (hR₁i : ∀ r ∈ R₁, ∀ r' ∈ R₁,
      (∃ t ∈ Subgroup.centralizer {γ}, ∃ κ ∈ K₁, r' = t * r * κ) → r = r') :
    ∃ R₂ : Set G₂,
      (∀ g, ∃ r ∈ R₂, ∃ a ∈ twCent θ δ, ∃ κ ∈ K₂, g = a * r * κ) ∧
      (∀ r ∈ R₂, ∀ r' ∈ R₂, (∃ a ∈ twCent θ δ, ∃ κ ∈ K₂, r' = a * r * κ) → r = r') ∧
      (∀ r ∈ R₁, r⁻¹ * γ * r ∈ K₁ → w * ι r ∈ R₂ ∧ twConj θ (w * ι r) δ ∈ K₂) ∧
      (∀ a ∈ R₂, twConj θ a δ ∈ K₂ → ∃ r ∈ R₁, r⁻¹ * γ * r ∈ K₁ ∧ a = w * ι r) := by
  have hA : ∀ a ∈ (fun r => w * ι r) '' {r | r ∈ R₁ ∧ r⁻¹ * γ * r ∈ K₁},
      ∀ a' ∈ (fun r => w * ι r) '' {r | r ∈ R₁ ∧ r⁻¹ * γ * r ∈ K₁},
      (∃ h ∈ twCent θ δ, ∃ κ ∈ K₂, a' = h * a * κ) → a = a' := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩ ⟨a, ha, κ, hκ, e⟩
    have hx : w⁻¹ * a * w ∈ twCent θ c := (hH3 _).2 (by convert ha using 1; group)
    rw [hcent] at hx
    obtain ⟨t, ht, htw⟩ := hx
    have e1 : ι r' = ι t * ι r * κ := by
      apply mul_left_cancel (a := w)
      have e' : w * ι r' = a * (w * ι r) * κ := e
      rw [e', htw]
      group
    have h1 : (t * r)⁻¹ * r' ∈ K₁ := (hι _).1 (by
      rw [map_mul, map_inv, map_mul, e1]
      convert hκ using 1
      group)
    have h2 := hR₁i r hr.1 r' hr'.1 ⟨t, ht, _, h1, by group⟩
    simp only [h2]
  obtain ⟨R₂, hAR, hc2, hi2⟩ := exists_doubleCoset_reps (twCent θ δ) K₂ _ hA
  refine ⟨R₂, hc2, hi2, ?_, ?_⟩
  · intro r hr hrγ
    refine ⟨hAR ⟨r, ⟨hr, hrγ⟩, rfl⟩, ?_⟩
    rw [twConj_mul', hc, hL4]
    constructor
    · rw [hθι]; simp [K₂.one_mem]
    · have := (hι _).2 hrγ
      simpa [map_mul] using this
  · intro a ha hsupp
    have h1 : twConj θ (w⁻¹ * a) c ∈ K₂ := by
      rw [← hc, ← twConj_mul']
      simpa using hsupp
    obtain ⟨h2, h3⟩ := (hL4 _).1 h1
    obtain ⟨y, hy⟩ := hL3 _ h2
    have hy1 : y⁻¹ * γ * y ∈ K₁ := (hι _).1 (by
      have e : ι (y⁻¹ * γ * y) = ((ι y)⁻¹ * (w⁻¹ * a)) * ((w⁻¹ * a)⁻¹ * ι γ * (w⁻¹ * a)) *
          ((ι y)⁻¹ * (w⁻¹ * a))⁻¹ := by
        simp only [map_mul, map_inv]
        group
      rw [e]
      exact K₂.mul_mem (K₂.mul_mem hy h3) (K₂.inv_mem hy))
    obtain ⟨r, hr, t, ht, κ', hκ', ey⟩ := hR₁c y
    have htγ : t⁻¹ * γ * t = γ := by
      have := Subgroup.mem_centralizer_singleton_iff.1 ht
      rw [mul_assoc, ← this]
      group
    have hr1 : r⁻¹ * γ * r ∈ K₁ := by
      have e : r⁻¹ * γ * r = κ' * (y⁻¹ * γ * y) * κ'⁻¹ := by
        calc r⁻¹ * γ * r = r⁻¹ * (t⁻¹ * γ * t) * r := by rw [htγ]
          _ = κ' * ((t * r * κ')⁻¹ * γ * (t * r * κ')) * κ'⁻¹ := by group
          _ = _ := by rw [← ey]
      rw [e]
      exact K₁.mul_mem (K₁.mul_mem hκ' hy1) (K₁.inv_mem hκ')
    have hm : w * ι t * w⁻¹ ∈ twCent θ δ := (hH3 _).1 (by rw [hcent]; exact ⟨t, ht, rfl⟩)
    have hκ2 : ι κ' * ((ι y)⁻¹ * (w⁻¹ * a)) ∈ K₂ := K₂.mul_mem ((hι _).2 hκ') hy
    have hrm : w * ι r ∈ R₂ := hAR ⟨r, ⟨hr, hr1⟩, rfl⟩
    refine ⟨r, hr, hr1, (hi2 _ hrm _ ha ⟨_, hm, _, hκ2, ?_⟩).symm⟩
    have e : ι y = ι t * ι r * ι κ' := by rw [ey]; simp only [map_mul]
    rw [e]
    group

section GLSide

variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E]

theorem sigmaGL_incl' {n : ℕ} (σ : E ≃ₐ[k] E) (y : GL (Fin n) k) :
    sigmaGL σ (incl y : GL (Fin n) E) = incl y := by
  apply Units.ext
  ext i j
  exact σ.commutes _

theorem charpoly_incl' {n : ℕ} (γ : GL (Fin n) k) :
    ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
      ((γ : Matrix (Fin n) (Fin n) k).charpoly).map (algebraMap k E) :=
  Matrix.charpoly_map _ _

theorem sigma_pow_finrank (σ : E ≃ₐ[k] E) : σ ^ Module.finrank k E = 1 := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact pow_card_eq_one'

theorem sigmaGL_pow_finrank {n : ℕ} (σ : E ≃ₐ[k] E) :
    (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
  rw [← sigmaGL_pow, sigma_pow_finrank, sigmaGL_one]

theorem map_aeval_fixed {n : ℕ} (σ : E ≃ₐ[k] E) (Γ : Matrix (Fin n) (Fin n) E)
    (hΓ : Γ.map σ = Γ) (p : E[X]) :
    (aeval Γ p).map σ = aeval Γ (p.map (σ : E →+* E)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Polynomial.map_add, map_add, ← hp, ← hq]
    ext i j
    simp
  | monomial m a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def]
    have h : ((Γ ^ m).map σ) = Γ ^ m := by
      have := (RingHom.mapMatrix (σ : E →+* E)).map_pow Γ m
      have h2 : RingHom.mapMatrix (σ : E →+* E) Γ = Γ := hΓ
      rw [h2] at this
      exact this
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.coe_coe] at this ⊢
    rw [map_mul, this]

def PolyIn {n : ℕ} (Γ : Matrix (Fin n) (Fin n) E) (a : GL (Fin n) E) : Prop :=
  ∃ p : E[X], (a : Matrix (Fin n) (Fin n) E) = aeval Γ p

theorem PolyIn.comm {n : ℕ} {Γ : Matrix (Fin n) (Fin n) E} {a b : GL (Fin n) E}
    (ha : PolyIn Γ a) (hb : PolyIn Γ b) : Commute a b := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  apply Units.ext
  show (a : Matrix (Fin n) (Fin n) E) * b = b * a
  rw [hp, hq, ← map_mul, ← map_mul, mul_comm]

theorem PolyIn.sigma {n : ℕ} (σ : E ≃ₐ[k] E) {Γ : Matrix (Fin n) (Fin n) E} (hΓ : Γ.map σ = Γ)
    {a : GL (Fin n) E} (ha : PolyIn Γ a) : PolyIn Γ (sigmaGL σ a) := by
  obtain ⟨p, hp⟩ := ha
  refine ⟨p.map (σ : E →+* E), ?_⟩
  rw [← map_aeval_fixed σ Γ hΓ, ← hp]
  rfl

theorem PolyIn.sigma_pow {n : ℕ} (σ : E ≃ₐ[k] E) {Γ : Matrix (Fin n) (Fin n) E} (hΓ : Γ.map σ = Γ)
    {a : GL (Fin n) E} (ha : PolyIn Γ a) (i : ℕ) : PolyIn Γ (((sigmaGL σ) ^ i) a) := by
  induction i with
  | zero => simpa using ha
  | succ i ih =>
    rw [pow_succ_apply']
    exact ih.sigma σ hΓ

theorem normGL_mul_polyIn {n : ℕ} (σ : E ≃ₐ[k] E) {Γ : Matrix (Fin n) (Fin n) E} (hΓ : Γ.map σ = Γ)
    {a b : GL (Fin n) E} (ha : PolyIn Γ a) (hb : PolyIn Γ b) :
    normGL σ (a * b) = normGL σ a * normGL σ b :=
  twNorm_mul' _ a b (fun i j => (ha.sigma_pow σ hΓ i).comm (hb.sigma_pow σ hΓ j)) _

theorem exists_twConj_eq (hA2 : A2) (hA3 : A3) (hun : IsUnramifiedLoc k E) (σ : E ≃ₐ[k] E)
    (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {n : ℕ} (δ h c : GL (Fin n) E)
    (γ : GL (Fin n) k) (hγ : IsRegSemisimple γ) (hN : normGL σ δ = h * incl γ * h⁻¹)
    (hc : PolyIn ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) c)
    (hci : PolyIn ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) c⁻¹)
    (hcN : normGL σ c = incl γ) :
    ∃ z : GL (Fin n) E,
      Commute (z : Matrix (Fin n) (Fin n) E) (incl γ : GL (Fin n) E) ∧
        twConj (sigmaGL σ) (h * z) δ = c := by
  have hΓ : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map σ =
      ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) :=
    congrArg Units.val (sigmaGL_incl' σ γ)
  have hN' : normGL σ (twConj (sigmaGL σ) h δ) = incl γ := by
    unfold normGL
    rw [twNorm_twConj_of_pow_eq_one _ (sigmaGL_pow_finrank σ)]
    change h⁻¹ * normGL σ δ * h = _
    rw [hN]
    group
  have hsep : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    rw [charpoly_incl']
    exact (Polynomial.separable_map _).2 hγ
  obtain ⟨-, p', hp'⟩ := hA2 k E hun σ hgen n _ γ hN' hsep
  have hδ' : PolyIn ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
      (twConj (sigmaGL σ) h δ) := ⟨p', hp'⟩
  have hu : PolyIn ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
      (c⁻¹ * twConj (sigmaGL σ) h δ) := by
    obtain ⟨q, hq⟩ := hci
    refine ⟨q * p', ?_⟩
    rw [map_mul, ← hq, ← hp']
    rfl
  have hnorm : normGL σ (c⁻¹ * twConj (sigmaGL σ) h δ) = 1 := by
    rw [normGL_mul_polyIn σ hΓ hci hδ', hN', ← hcN, ← normGL_mul_polyIn σ hΓ hci hc]
    simpa [normGL] using twNorm_one' (sigmaGL σ) (Module.finrank k E)
  obtain ⟨x, hx, hux⟩ := hA3 k E hun σ hgen n γ hγ _ hu hnorm
  have hxc : x * c = c * x := (PolyIn.comm hx hc).eq
  refine ⟨x⁻¹, ?_, ?_⟩
  · have h1 : x * incl γ = incl γ * x :=
      (PolyIn.comm hx (⟨X, by simp⟩ : PolyIn ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) (incl γ))).eq
    have h2 : x⁻¹ * incl γ = incl γ * x⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, h1]
    exact congrArg Units.val h2
  · rw [twConj_mul']
    have e : twConj (sigmaGL σ) h δ = c * (x⁻¹ * sigmaGL σ x) := by
      rw [← hux]; group
    rw [e, twConj, map_inv, inv_inv]
    calc x * (c * (x⁻¹ * sigmaGL σ x)) * (sigmaGL σ x)⁻¹ = (x * c) * x⁻¹ := by group
      _ = c := by rw [hxc]; group

theorem incl_injective' {n : ℕ} :
    Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := by
  intro a b e
  apply Units.ext
  ext i j
  apply (algebraMap k E).injective
  exact congrArg (fun M : GL (Fin n) E => (M : Matrix (Fin n) (Fin n) E) i j) e

theorem isUnitIntegral_of_incl (hO : ∀ a : k, algebraMap k E a ∈ intO E ↔ a ∈ intO k) {n : ℕ}
    (γ : GL (Fin n) k) (h : IsUnitIntegral (incl γ : GL (Fin n) E)) : IsUnitIntegral γ := by
  obtain ⟨h1, h2⟩ := h
  rw [charpoly_incl'] at h1 h2
  simp only [Polynomial.coeff_map] at h1 h2
  refine ⟨fun i => (hO _).1 (h1 i), ?_⟩
  have ha : (γ : Matrix (Fin n) (Fin n) k).charpoly.coeff 0 ∈ intO k := (hO _).1 (h1 0)
  have ha0 : (γ : Matrix (Fin n) (Fin n) k).charpoly.coeff 0 ≠ 0 := by
    intro e
    rw [e, map_zero, map_zero] at h2
    exact zero_ne_one h2
  have hi : ((γ : Matrix (Fin n) (Fin n) k).charpoly.coeff 0)⁻¹ ∈ intO k := (hO _).1 (by
    rw [map_inv₀]
    show ValuativeRel.valuation E _ ≤ 1
    rw [map_inv₀, h2, inv_one])
  have e1 : ValuativeRel.valuation k ((γ : Matrix (Fin n) (Fin n) k).charpoly.coeff 0) ≤ 1 := ha
  have e2 : ValuativeRel.valuation k (((γ : Matrix (Fin n) (Fin n) k).charpoly.coeff 0)⁻¹) ≤ 1 := hi
  rw [map_inv₀] at e2
  have hv0 : ValuativeRel.valuation k ((γ : Matrix (Fin n) (Fin n) k).charpoly.coeff 0) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ha0
  exact le_antisymm e1 ((inv_le_one₀ (zero_lt_iff.2 hv0)).1 e2)

theorem quotLIntegral_zero' {G : Type*} [Group G] [MeasurableSpace G] (μG : Measure G)
    (H : Subgroup G) (μH : Measure H) (F : G → ℝ≥0∞) (hF : ∀ g, F g = 0) :
    quotLIntegral μG H μH F = 0 := by
  unfold quotLIntegral
  split_ifs <;> simp [hF]

theorem unitFn_of_mem' {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} {x : GL (Fin n) F}
    (hx : x ∈ unitGL (n := Fin n) F) : unitFn (n := Fin n) F x = 1 :=
  Set.indicator_of_mem (s := ((unitGL (n := Fin n) F : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)))
    hx _

theorem unitFn_of_notMem' {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} {x : GL (Fin n) F}
    (hx : x ∉ unitGL (n := Fin n) F) : unitFn (n := Fin n) F x = 0 :=
  Set.indicator_of_notMem (s := ((unitGL (n := Fin n) F : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)))
    hx _

theorem unitFn_congr' {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} {x y : GL (Fin n) F}
    (h : x ∈ unitGL (n := Fin n) F ↔ y ∈ unitGL (n := Fin n) F) :
    unitFn (n := Fin n) F x = unitFn (n := Fin n) F y := by
  by_cases hx : x ∈ unitGL (n := Fin n) F
  · rw [unitFn_of_mem' hx, unitFn_of_mem' (h.1 hx)]
  · rw [unitFn_of_notMem' hx, unitFn_of_notMem' (fun hy => hx (h.2 hy))]

theorem isOpen_of_rightInv {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (S : Set G) (hS : ∀ g ∈ S, ∀ κ ∈ K, g * κ ∈ S) :
    IsOpen S := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g * x) '' K, ?_, (isOpenMap_mul_left g) _ hK, ⟨1, K.one_mem, by simp⟩⟩
  rintro _ ⟨κ, hκ, rfl⟩
  exact hS g hg κ hκ

theorem measurable_unitFn_comp {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (f : G → GL (Fin n) F)
    (hf : ∀ g, ∀ κ ∈ K, f g ∈ unitGL (n := Fin n) F → f (g * κ) ∈ unitGL (n := Fin n) F) :
    Measurable (fun g => unitFn (n := Fin n) F (f g)) := by
  have hS : IsOpen (f ⁻¹' ((unitGL (n := Fin n) F : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F))) :=
    isOpen_of_rightInv K hK _ (fun g hg κ hκ => hf g κ hκ hg)
  have e : (fun g => unitFn (n := Fin n) F (f g)) =
      (f ⁻¹' ((unitGL (n := Fin n) F : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F))).indicator 1 := by
    funext g
    by_cases hg : f g ∈ unitGL (n := Fin n) F
    · rw [unitFn_of_mem' hg]
      exact (Set.indicator_of_mem (show g ∈ f ⁻¹' ((unitGL (n := Fin n) F : Subgroup (GL (Fin n) F)) :
        Set (GL (Fin n) F)) from hg) (1 : G → ℝ≥0∞)).symm
    · rw [unitFn_of_notMem' hg]
      exact (Set.indicator_of_notMem (show g ∉ f ⁻¹' ((unitGL (n := Fin n) F : Subgroup (GL (Fin n) F)) :
        Set (GL (Fin n) F)) from hg) (1 : G → ℝ≥0∞)).symm
  rw [e]
  exact measurable_one.indicator hS.measurableSet

theorem centralizer_comm (hA1 : A1) {K : Type} [Field K] {n : ℕ} (γ : GL (Fin n) K)
    (hs : (γ : Matrix (Fin n) (Fin n) K).charpoly.Separable) {a b : GL (Fin n) K}
    (ha : a ∈ Subgroup.centralizer {γ}) (hb : b ∈ Subgroup.centralizer {γ}) : a * b = b * a := by
  have key : ∀ x ∈ Subgroup.centralizer {γ}, ∃ p : K[X],
      (x : Matrix (Fin n) (Fin n) K) = aeval (γ : Matrix (Fin n) (Fin n) K) p := fun x hx =>
    hA1 K n _ hs _ (congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.1 hx))
  obtain ⟨p, hp⟩ := key a ha
  obtain ⟨q, hq⟩ := key b hb
  apply Units.ext
  show (a : Matrix (Fin n) (Fin n) K) * b = b * a
  rw [hp, hq, ← map_mul, ← map_mul, mul_comm]

theorem unit_fundamental_lemma_nonintegral (hD : D0a) (hL2 : L2) (hun : IsUnramifiedLoc k E) (σ : E ≃ₐ[k] E)
    (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {n : ℕ}
    [MeasurableSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)]
    (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k))
    (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
    (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ}))
    (hN : normGL σ δ = h * incl γ * h⁻¹) (hγ : ¬ IsUnitIntegral γ) :
    twOrbIntegral (sigmaGL σ) μE δ μδ (unitFn E) = orbIntegral μk γ μγ (unitFn k) := by
  obtain ⟨-, hO, -⟩ := hD k E hun σ hgen
  have zk : ∀ g : GL (Fin n) k, unitFn (n := Fin n) k (g⁻¹ * γ * g) = 0 := fun g =>
    unitFn_of_notMem' (fun hg => hγ (hL2.1 k n γ ⟨g, hg⟩))
  have zE : ∀ g : GL (Fin n) E, unitFn (n := Fin n) E (twConj (sigmaGL σ) g δ) = 0 := fun g =>
    unitFn_of_notMem' (fun hg => hγ (by
      have h1 := hL2.2 k E hun σ hgen n δ g hg
      rw [hN] at h1
      have h2 : IsUnitIntegral (incl γ : GL (Fin n) E) :=
        hL2.1 E n _ ⟨h⁻¹ * g, by convert h1 using 1; group⟩
      exact isUnitIntegral_of_incl hO γ h2))
  rw [twOrbIntegral, orbIntegral, quotLIntegral_zero' _ _ _ _ zE, quotLIntegral_zero' _ _ _ _ zk]

open ValuativeRel in

theorem t2Space_of_nonarchimedeanLocalField (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : T2Space F := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  letI : (Valued.v (R := F)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := F).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  infer_instance

theorem t2Space_general_linear_group (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) : T2Space (GL (Fin n) F) := by
  haveI := t2Space_of_nonarchimedeanLocalField F
  haveI : T2Space (Matrix (Fin n) (Fin n) F) := inferInstanceAs (T2Space (Fin n → Fin n → F))
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) F)).t2Space

theorem unit_fundamental_lemma_integral (hD : D0a) (hT : T0) (hA1 : A1) (hA2 : A2) (hA3 : A3) (hN4 : N4) (hL3 : L3)
    (hL4 : L4) (hH2 : H2) (hH3 : H3) (hH4 : H4) (hun : IsUnramifiedLoc k E) (σ : E ≃ₐ[k] E)
    (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {n : ℕ}
    [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k))
    (hμE : μE.IsHaarMeasure) (hμk : μk.IsHaarMeasure)
    (hE1 : μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1)
    (hk1 : μk (unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1)
    (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
    (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ}))
    (hreg : IsTwRegSemisimple σ δ) (hN : normGL σ δ = h * incl γ * h⁻¹)
    (hμδ : μδ.IsHaarMeasure) (hμγ : μγ.IsHaarMeasure)
    (hcomp : Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
      Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ)
    (hγ : IsUnitIntegral γ) :
    twOrbIntegral (sigmaGL σ) μE δ μδ (unitFn E) = orbIntegral μk γ μγ (unitFn k) := by
  obtain ⟨-, -, hincl, hσK, -, -⟩ := hD k E hun σ hgen
  have hsepE : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    have h0 : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := hreg
    rw [hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at h0
    exact h0
  have hγreg : IsRegSemisimple γ := by
    rw [charpoly_incl'] at hsepE
    exact (Polynomial.separable_map _).1 hsepE
  obtain ⟨c, ⟨p, hp, hpi⟩, ⟨q, hq, hqi⟩, hcN⟩ := hN4 k E hun σ hgen n γ hγ
  obtain ⟨z, hz, hw⟩ := exists_twConj_eq hA2 hA3 hun σ hgen δ h c γ hγreg hN ⟨p, hp⟩ ⟨q, hq⟩ hcN
  obtain ⟨hL4a, hL4b⟩ := hL4 k E hun σ hgen n γ c hγreg ⟨p, hp, hpi⟩ ⟨q, hq, hqi⟩ hcN
  obtain ⟨Rk, -, hRc, hRi⟩ := exists_doubleCoset_reps (Subgroup.centralizer {γ})
    (unitGL (n := Fin n) k) ∅ (by simp)
  obtain ⟨RE, hEc, hEi, hE3, hE4⟩ := exists_matching_reps incl (sigmaGL σ) (unitGL (n := Fin n) k)
    (unitGL (n := Fin n) E) γ c (h * z) δ (hincl n) (sigmaGL_incl' σ) hw hL4a hL4b
    (fun x => by
      have := hH3 _ (sigmaGL σ) (h * z) δ x
      rwa [hw] at this)
    (hL3 k E hun σ hgen n) Rk hRc hRi
  obtain ⟨hTa, hTb⟩ := hT
  have hKE : ∀ (g κ : GL (Fin n) E), κ ∈ unitGL (n := Fin n) E →
      (twConj (sigmaGL σ) (g * κ) δ ∈ unitGL (n := Fin n) E ↔
        twConj (sigmaGL σ) g δ ∈ unitGL (n := Fin n) E) := by
    intro g κ hκ
    rw [twConj_mul']
    show κ⁻¹ * twConj (sigmaGL σ) g δ * sigmaGL σ κ ∈ _ ↔ _
    rw [Subgroup.mul_mem_cancel_right _ ((hσK σ n κ).2 hκ),
      Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hκ)]
  have hKk : ∀ (g κ : GL (Fin n) k), κ ∈ unitGL (n := Fin n) k →
      ((g * κ)⁻¹ * γ * (g * κ) ∈ unitGL (n := Fin n) k ↔ g⁻¹ * γ * g ∈ unitGL (n := Fin n) k) := by
    intro g κ hκ
    have e : (g * κ)⁻¹ * γ * (g * κ) = κ⁻¹ * (g⁻¹ * γ * g) * κ := by group
    rw [e, Subgroup.mul_mem_cancel_right _ hκ, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hκ)]
  have hclosed : IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) :
      Set (GL (Fin n) k)) := by
    have e : ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) =
        {t | t * γ = γ * t} := by
      ext t
      exact Subgroup.mem_centralizer_singleton_iff
    rw [e]
    haveI := t2Space_general_linear_group k n
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have hcommE : ∀ a ∈ twCent (sigmaGL σ) δ, ∀ b ∈ twCent (sigmaGL σ) δ, a * b = b * a := by
    intro a ha b hb
    have ha' := conj_twCent_mem_centralizer (sigmaGL σ) (sigmaGL_pow_finrank σ) hN ha
    have hb' := conj_twCent_mem_centralizer (sigmaGL σ) (sigmaGL_pow_finrank σ) hN hb
    have e := centralizer_comm hA1 (incl γ) hsepE ha' hb'
    calc a * b = h * ((h⁻¹ * a * h) * (h⁻¹ * b * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * b * h) * (h⁻¹ * a * h)) * h⁻¹ := by rw [e]
      _ = b * a := by group
  have eE := hH2 E n μE (twCent (sigmaGL σ) δ) μδ hμE (hTb k E hun σ hgen n δ) hcommE hμδ
    (fun g => unitFn (n := Fin n) E (twConj (sigmaGL σ) g δ))
    (measurable_unitFn_comp _ (hTa E n).2.2.1 _ (fun g κ hκ hx => (hKE g κ hκ).2 hx))
    (fun a ha g => by
      show unitFn (n := Fin n) E _ = unitFn (n := Fin n) E _
      rw [twConj_mul_left _ _ ha])
    (fun g κ hκ => unitFn_congr' (hKE g κ hκ)) RE hEc hEi
  have ek := hH2 k n μk (Subgroup.centralizer {γ}) μγ hμk hclosed
    (fun a ha b hb => centralizer_comm hA1 γ hγreg ha hb) hμγ
    (fun g => unitFn (n := Fin n) k (g⁻¹ * γ * g))
    (measurable_unitFn_comp _ (hTa k n).2.2.1 _ (fun g κ hκ hx => (hKk g κ hκ).2 hx))
    (fun t ht g => by
      have e : (t * g)⁻¹ * γ * (t * g) = g⁻¹ * γ * g := by
        have := Subgroup.mem_centralizer_singleton_iff.1 ht
        calc (t * g)⁻¹ * γ * (t * g) = g⁻¹ * (t⁻¹ * (γ * t)) * g := by group
          _ = g⁻¹ * (t⁻¹ * (t * γ)) * g := by rw [this]
          _ = _ := by group
      show unitFn (n := Fin n) k _ = unitFn (n := Fin n) k _
      rw [e])
    (fun g κ hκ => unitFn_congr' (hKk g κ hκ)) Rk hRc hRi
  rw [twOrbIntegral, orbIntegral, eE, ek, hE1, hk1]
  refine tsum_match RE Rk {r | r ∈ Rk ∧ r⁻¹ * γ * r ∈ unitGL (n := Fin n) k} (fun r hr => hr.1)
    (fun r => h * z * incl r)
    (fun a => unitFn (n := Fin n) E (twConj (sigmaGL σ) a δ) * 1 /
      μδ {x : twCent (sigmaGL σ) δ | a⁻¹ * (x : GL (Fin n) E) * a ∈ unitGL (n := Fin n) E})
    (fun b => unitFn (n := Fin n) k (b⁻¹ * γ * b) * 1 /
      μγ {t : Subgroup.centralizer {γ} | b⁻¹ * (t : GL (Fin n) k) * b ∈ unitGL (n := Fin n) k})
    ?_ (fun t ht => (hE3 t ht.1 ht.2).1) ?_ ?_ ?_
  · intro a _ b _ e
    exact incl_injective' (mul_left_cancel e)
  · intro a ha hne
    have hs : twConj (sigmaGL σ) a δ ∈ unitGL (n := Fin n) E := by
      by_contra hn
      apply hne
      rw [unitFn_of_notMem' hn]
      simp
    obtain ⟨r, hr, hr1, e⟩ := hE4 a ha hs
    exact ⟨r, ⟨hr, hr1⟩, e.symm⟩
  · intro b hb hne
    refine ⟨hb, ?_⟩
    by_contra hn
    apply hne
    rw [unitFn_of_notMem' hn]
    simp
  · intro t ht
    rw [unitFn_of_mem' (hE3 t ht.1 ht.2).2, unitFn_of_mem' ht.2,
      hH4 k E hun σ hgen n δ γ h μδ μγ hreg hN hcomp t z hz]

end GLSide

theorem unit_fundamental_lemma_first : D0a → T0 → A1 → A2 → A3 → N4 → L2 → L3 → L4 → H2 → H3 → H4 → Z1 := by
  intro hD hT hA1 hA2 hA3 hN4 hL2 hL3 hL4 hH2 hH3 hH4
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n _ _ _ _ μE μk hμE hμk hE1 hk1 δ γ h μδ μγ hreg hN
    hμδ hμγ hcomp
  by_cases hγ : IsUnitIntegral γ
  · exact unit_fundamental_lemma_integral hD hT hA1 hA2 hA3 hN4 hL3 hL4 hH2 hH3 hH4 hun σ hgen μE μk hμE hμk hE1 hk1
      δ γ h μδ μγ hreg hN hμδ hμγ hcomp hγ
  · exact unit_fundamental_lemma_nonintegral hD hL2 hun σ hgen μE μk δ γ h μδ μγ hN hγ

end

end GlobalTheory.CompanionTheory.UnitFL
