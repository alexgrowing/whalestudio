import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GlueLines

open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E]

variable [StarRing E]

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [StarRing E] in
private lemma exists_generator_of_integral_dual {β : E} {N : Submodule (𝓞 E) E} (hN0 : N ≠ ⊥)
    (hβ0 : β ≠ 0) (hNN : ∀ x ∈ N, ∀ y ∈ N, star x * β * y ∈ (algebraMap (𝓞 E) E).range) :
    ∃ u : E, (∀ s ∈ N, star s * β * u ∈ (algebraMap (𝓞 E) E).range) ∧
      ∀ a : E, (∀ s ∈ N, star s * β * a ∈ (algebraMap (𝓞 E) E).range) →
        ∃ c : 𝓞 E, a - c • u ∈ N := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  set d : E := star s * β with hd
  have hd0 : d ≠ 0 := mul_ne_zero (star_ne_zero.2 hs0) hβ0
  let D : Submodule (𝓞 E) E := ⨅ x ∈ N,
    (1 : Submodule (𝓞 E) E).comap (LinearMap.mulLeft (𝓞 E) (star x * β))
  have memD : ∀ a, a ∈ D ↔ ∀ x ∈ N, star x * β * a ∈ (algebraMap (𝓞 E) E).range := by
    intro a
    simp only [D, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply,
      Submodule.mem_one, RingHom.mem_range]
  let f : 𝓞 E →ₗ[𝓞 E] E := LinearMap.mulLeft (𝓞 E) d⁻¹ ∘ₗ Algebra.linearMap (𝓞 E) E
  have hf : ∀ c, f c = d⁻¹ * algebraMap (𝓞 E) E c := fun c => rfl
  let I : Ideal (𝓞 E) := N.comap f
  let J : Ideal (𝓞 E) := D.comap f
  have hIJ : I ≤ J := by
    intro c hc
    simp only [I, J, Submodule.mem_comap] at hc ⊢
    exact (memD _).2 fun x hx => hNN x hx _ hc
  have hI0 : I ≠ 0 := by
    obtain ⟨c₀, hc₀⟩ := hNN s hs s hs
    intro h
    have hmem : c₀ ∈ I := by
      simp only [I, Submodule.mem_comap, hf, hc₀, hd]
      rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]; exact hs
    rw [h] at hmem
    have hz : c₀ = 0 := (Submodule.mem_bot _).1 hmem
    rw [hz, map_zero] at hc₀
    exact (mul_ne_zero hd0 hs0) hc₀.symm
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_sup_span_eq hIJ hI0
  refine ⟨f y, (memD _).1 ?_, fun a ha => ?_⟩
  · have : y ∈ J := hy ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
    exact this
  · obtain ⟨c₀, hc₀⟩ := ha s hs
    have hc₀J : c₀ ∈ J := by
      simp only [J, Submodule.mem_comap, hf, hc₀, hd]
      rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]; exact (memD _).2 ha
    rw [← hy, Submodule.mem_sup] at hc₀J
    obtain ⟨i, hi, z, hz, hiz⟩ := hc₀J
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨c, ?_⟩
    have ha' : a = f c₀ := by
      rw [hf, hc₀, hd, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
    have : a - c • f y = f i := by
      rw [ha', ← hiz, map_add, map_smul, add_sub_cancel_right]
    rw [this]; exact hi

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [StarRing E] in
private lemma star_mem_range_algebraMap_integers {x : E} (hx : x ∈ (algebraMap (𝓞 E) E).range) :
    star x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨r, rfl⟩ := hx
  have h : IsIntegral ℤ (star (algebraMap (𝓞 E) E r)) :=
    (r.isIntegral_coe).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [StarRing E] in
private lemma mem_of_mem_dual_of_dual_le {β : E} {N P : Submodule (𝓞 E) E} (hP : P.FG) (hP0 : P ≠ ⊥)
    (hβ : star β = β) (hβ0 : β ≠ 0)
    (hPN : ∀ t, (∀ p ∈ P, star p * β * t ∈ (algebraMap (𝓞 E) E).range) → t ∈ N) {a : E}
    (ha : ∀ s ∈ N, star s * β * a ∈ (algebraMap (𝓞 E) E).range) : a ∈ P := by
  let F : FractionalIdeal (𝓞 E)⁰ E := ⟨P, FractionalIdeal.isFractional_of_fg hP⟩
  have hF0 : F ≠ 0 := by
    intro h; apply hP0
    have := congrArg (fun I : FractionalIdeal (𝓞 E)⁰ E => (I : Submodule (𝓞 E) E)) h
    simpa [F] using this
  have hmul : F * F⁻¹ = 1 := mul_inv_cancel₀ hF0
  have key : ∀ z ∈ ((F * F⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E), a * z ∈ P := by
    intro z hz
    rw [FractionalIdeal.coe_mul] at hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro p hp q hq
      have hq' := (FractionalIdeal.mem_inv_iff hF0).1 hq
      have ht : star q * β⁻¹ ∈ N := by
        apply hPN
        intro p' hp'
        have h1 : star p' * β * (star q * β⁻¹) = star (q * p') := by
          rw [star_mul']; field_simp
        rw [h1]
        obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 (hq' p' hp')
        exact star_mem_range_algebraMap_integers ⟨c, hc⟩
      have h2 := ha _ ht
      have h3 : star (star q * β⁻¹) * β * a = q * a := by
        rw [star_mul', star_inv₀, hβ, star_star]; field_simp
      rw [h3] at h2
      obtain ⟨c, hc⟩ := h2
      have : a * (p * q) = c • p := by rw [Algebra.smul_def, hc]; ring
      rw [this]; exact P.smul_mem c hp
    · intro x y hx hy; rw [mul_add]; exact P.add_mem hx hy
  have := key 1 (by rw [hmul]; exact FractionalIdeal.one_mem_one _)
  simpa using this

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [StarRing E] in
open Matrix in
variable {β₁ β₂ : E} {N₁ N₂ : Submodule (𝓞 E) E} {M : Submodule (𝓞 E) (Fin 2 → E)} in
omit [NumberField E] in
private lemma star_dotProduct_diagonal_two_mulVec (y x : Fin 2 → E) :
    star y ⬝ᵥ (Matrix.diagonal ![β₁, β₂] *ᵥ x) =
      star (y 0) * β₁ * x 0 + star (y 1) * β₂ * x 1 := by
  simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec_diagonal]; ring

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [StarRing E] in
open Matrix in
variable {β₁ β₂ : E} {N₁ N₂ : Submodule (𝓞 E) E} {M : Submodule (𝓞 E) (Fin 2 → E)} in
private lemma exists_snd_mem_of_integral_dual_fst (hβ₁ : star β₁ = β₁) (hβ₁0 : β₁ ≠ 0) (hfg : M.FG) (hN0 : N₁ ≠ ⊥)
    (hdual : ∀ x, x ∈ M ↔ ∀ y ∈ M, star y ⬝ᵥ ((Matrix.diagonal ![β₁, β₂]) *ᵥ x) ∈
        (algebraMap (𝓞 E) E).range)
    (h1 : ∀ t, t ∈ N₁ ↔ ![t, 0] ∈ M) {a : E}
    (ha : ∀ s ∈ N₁, star s * β₁ * a ∈ (algebraMap (𝓞 E) E).range) :
    ∃ b, ![a, b] ∈ M := by
  have hP0 : M.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 2 => E) 0) ≠ ⊥ := by
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
    intro h
    have : s ∈ M.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 2 => E) 0) :=
      Submodule.mem_map.2 ⟨![s, 0], (h1 s).1 hs, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hs0 this
  have hmem := mem_of_mem_dual_of_dual_le (hfg.map _) hP0 hβ₁ hβ₁0 (N := N₁) (fun t ht => by
    apply (h1 t).2
    apply (hdual _).2
    intro y hy
    have := ht (y 0) (Submodule.mem_map.2 ⟨y, hy, rfl⟩)
    rw [star_dotProduct_diagonal_two_mulVec]
    simpa using this) ha
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hmem
  refine ⟨x 1, ?_⟩
  convert hx using 1
  funext i; fin_cases i <;> rfl

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [StarRing E] in
open Matrix in
variable {β₁ β₂ : E} {N₁ N₂ : Submodule (𝓞 E) E} {M : Submodule (𝓞 E) (Fin 2 → E)} in
private lemma exists_fst_mem_of_integral_dual_snd (hβ₂ : star β₂ = β₂) (hβ₂0 : β₂ ≠ 0) (hfg : M.FG) (hN0 : N₂ ≠ ⊥)
    (hdual : ∀ x, x ∈ M ↔ ∀ y ∈ M, star y ⬝ᵥ ((Matrix.diagonal ![β₁, β₂]) *ᵥ x) ∈
        (algebraMap (𝓞 E) E).range)
    (h2 : ∀ t, t ∈ N₂ ↔ ![0, t] ∈ M) {b : E}
    (hb : ∀ s ∈ N₂, star s * β₂ * b ∈ (algebraMap (𝓞 E) E).range) :
    ∃ a, ![a, b] ∈ M := by
  have hP0 : M.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 2 => E) 1) ≠ ⊥ := by
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
    intro h
    have : s ∈ M.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 2 => E) 1) :=
      Submodule.mem_map.2 ⟨![0, s], (h2 s).1 hs, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hs0 this
  have hmem := mem_of_mem_dual_of_dual_le (hfg.map _) hP0 hβ₂ hβ₂0 (N := N₂) (fun t ht => by
    apply (h2 t).2
    apply (hdual _).2
    intro y hy
    have := ht (y 1) (Submodule.mem_map.2 ⟨y, hy, rfl⟩)
    rw [star_dotProduct_diagonal_two_mulVec]
    simpa using this) hb
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hmem
  refine ⟨x 0, ?_⟩
  convert hx using 1
  funext i; fin_cases i <;> rfl

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [StarRing E] in
open Matrix in
variable {β₁ β₂ : E} {N₁ N₂ : Submodule (𝓞 E) E} {M : Submodule (𝓞 E) (Fin 2 → E)} in
private lemma star_mul_mul_snd_mem_integers_of_mem
    (hdual : ∀ x, x ∈ M ↔ ∀ y ∈ M, star y ⬝ᵥ ((Matrix.diagonal ![β₁, β₂]) *ᵥ x) ∈
        (algebraMap (𝓞 E) E).range)
    (h2 : ∀ t, t ∈ N₂ ↔ ![0, t] ∈ M) {x : Fin 2 → E} (hx : x ∈ M) {s : E} (hs : s ∈ N₂) :
    star s * β₂ * x 1 ∈ (algebraMap (𝓞 E) E).range := by
  have := (hdual x).1 hx _ ((h2 s).1 hs)
  rw [star_dotProduct_diagonal_two_mulVec] at this
  simpa using this

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [StarRing E] in
open Matrix in
variable {β₁ β₂ : E} {N₁ N₂ : Submodule (𝓞 E) E} {M : Submodule (𝓞 E) (Fin 2 → E)} in
private lemma star_mul_mul_fst_mem_integers_of_mem
    (hdual : ∀ x, x ∈ M ↔ ∀ y ∈ M, star y ⬝ᵥ ((Matrix.diagonal ![β₁, β₂]) *ᵥ x) ∈
        (algebraMap (𝓞 E) E).range)
    (h1 : ∀ t, t ∈ N₁ ↔ ![t, 0] ∈ M) {x : Fin 2 → E} (hx : x ∈ M) {s : E} (hs : s ∈ N₁) :
    star s * β₁ * x 0 ∈ (algebraMap (𝓞 E) E).range := by
  have := (hdual x).1 hx _ ((h1 s).1 hs)
  rw [star_dotProduct_diagonal_two_mulVec] at this
  simpa using this

open MeasureTheory NumberField Matrix Finset in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in
variable [StarRing E] in

theorem _root_.GlobalTheory.GlueLines.card_gluings_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E],
    _root_.Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (β₁ β₂ : E) (N₁ N₂ : Submodule (𝓞 E) E) (𝔫 : Ideal (𝓞 E)), star β₁ = β₁ →
    star β₂ = β₂ → β₁ ≠ 0 → β₂ ≠ 0 → Submodule.IsLattice E N₁ → Submodule.IsLattice E N₂ →
    Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} =
      Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 →
    ENat.card {M : Submodule (𝓞 E) (Fin 2 → E) // Submodule.IsLattice E M ∧
      (∀ x, x ∈ M ↔ ∀ y ∈ M, star y ⬝ᵥ ((Matrix.diagonal ![β₁, β₂]) *ᵥ x) ∈
        (algebraMap (𝓞 E) E).range) ∧
      (∀ t, t ∈ N₁ ↔ ![t, 0] ∈ M) ∧ ∀ t, t ∈ N₂ ↔ ![0, t] ∈ M} ≤ (Ideal.absNorm 𝔫 : ENat) := by
  intro E _ _ _ _ β₁ β₂ N₁ N₂ 𝔫 hβ₁ hβ₂ hβ₁0 hβ₂0 hL₁ hL₂ hspan
  classical
  have hne : ∀ {N : Submodule (𝓞 E) E}, Submodule.IsLattice E N → N ≠ ⊥ := by
    intro N hN h
    have := hN.span_eq_top
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at this
    exact bot_ne_top this
  have hNN : ∀ x ∈ N₁, ∀ y ∈ N₁, star x * β₁ * y ∈ (algebraMap (𝓞 E) E).range := by
    intro x hx y hy
    have : star x * β₁ * y ∈
        Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} :=
      Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
    rw [hspan] at this
    obtain ⟨c, -, hc⟩ := Submodule.mem_map.1 this
    exact ⟨c, hc⟩
  have hideal : ∀ u : E, (∀ s ∈ N₁, star s * β₁ * u ∈ (algebraMap (𝓞 E) E).range) →
      ∀ c ∈ 𝔫, c • u ∈ N₁ := by
    intro u hu c hc
    have hc' : algebraMap (𝓞 E) E c ∈
        Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} := by
      rw [hspan]; exact Submodule.mem_map_of_mem hc
    rw [Algebra.smul_def]
    refine Submodule.span_induction (p := fun z _ => z * u ∈ N₁) ?_ ?_ ?_ ?_ hc'
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      obtain ⟨d, hd⟩ := hu x hx
      have : star x * β₁ * y * u = d • y := by rw [Algebra.smul_def, hd]; ring
      rw [this]; exact N₁.smul_mem d hy
    · simp
    · intro a b _ _ ha hb; rw [add_mul]; exact N₁.add_mem ha hb
    · intro r a _ ha; rw [smul_mul_assoc]; exact N₁.smul_mem r ha
  obtain ⟨u, hu, hgen⟩ := exists_generator_of_integral_dual (hne hL₁) hβ₁0 hNN
  let P : Submodule (𝓞 E) (Fin 2 → E) → Prop := fun M => Submodule.IsLattice E M ∧
      (∀ x, x ∈ M ↔ ∀ y ∈ M, star y ⬝ᵥ ((Matrix.diagonal ![β₁, β₂]) *ᵥ x) ∈
        (algebraMap (𝓞 E) E).range) ∧
      (∀ t, t ∈ N₁ ↔ ![t, 0] ∈ M) ∧ ∀ t, t ∈ N₂ ↔ ![0, t] ∈ M
  show ENat.card {M // P M} ≤ _
  obtain ⟨g, hinj⟩ : ∃ g : {M // P M} → 𝓞 E ⧸ 𝔫, Function.Injective g := by
    rcases isEmpty_or_nonempty {M // P M} with hS | hS
    · exact ⟨isEmptyElim, fun a => isEmptyElim a⟩
    obtain ⟨M₀⟩ := hS
    have hv : ∀ M : {M // P M}, ∃ v, ![u, v] ∈ M.1 := fun M =>
      exists_snd_mem_of_integral_dual_fst hβ₁ hβ₁0 M.2.1.fg (hne hL₁) M.2.2.1 M.2.2.2.1 hu
    choose v hv using hv
    have hc : ∀ M : {M // P M}, ∃ c : 𝓞 E, v M - c • v M₀ ∈ N₂ := by
      intro M
      obtain ⟨a, ha⟩ := exists_fst_mem_of_integral_dual_snd hβ₂ hβ₂0 M₀.2.1.fg (hne hL₂) M₀.2.2.1 M₀.2.2.2.2
        (b := v M) (fun s hs => by
          simpa using star_mul_mul_snd_mem_integers_of_mem M.2.2.1 M.2.2.2.2 (hv M) hs)
      obtain ⟨c, hc⟩ := hgen a (fun s hs => by
        simpa using star_mul_mul_fst_mem_integers_of_mem M₀.2.2.1 M₀.2.2.2.1 ha hs)
      refine ⟨c, (M₀.2.2.2.2 _).2 ?_⟩
      have : ![0, v M - c • v M₀] = ![a, v M] - c • ![u, v M₀] - ![a - c • u, 0] := by
        funext i; fin_cases i <;> simp
      rw [this]
      exact M₀.1.sub_mem (M₀.1.sub_mem ha (M₀.1.smul_mem c (hv M₀))) ((M₀.2.2.2.1 _).1 hc)
    choose c hc using hc
    have hle : ∀ M M' : {M // P M}, v M - v M' ∈ N₂ → M.1 ≤ M'.1 := by
      intro M M' hvv x hx
      obtain ⟨d, hd⟩ := hgen (x 0) (fun s hs => star_mul_mul_fst_mem_integers_of_mem M.2.2.1 M.2.2.2.1 hx hs)
      have h0 : x 1 - d • v M ∈ N₂ := by
        apply (M.2.2.2.2 _).2
        have : ![0, x 1 - d • v M] = x - d • ![u, v M] - ![x 0 - d • u, 0] := by
          funext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]
        rw [this]
        exact M.1.sub_mem (M.1.sub_mem hx (M.1.smul_mem d (hv M))) ((M.2.2.2.1 _).1 hd)
      have : x = ![x 0 - d • u, 0] + d • ![u, v M'] + ![0, (x 1 - d • v M) + d • (v M - v M')] := by
        funext i; fin_cases i <;> simp [smul_sub] <;> abel
      rw [this]
      exact M'.1.add_mem (M'.1.add_mem ((M'.2.2.2.1 _).1 hd) (M'.1.smul_mem d (hv M')))
        ((M'.2.2.2.2 _).1 (N₂.add_mem h0 (N₂.smul_mem d hvv)))
    refine ⟨fun M => Ideal.Quotient.mk 𝔫 (c M), ?_⟩
    · intro M M' h
      have hd : c M - c M' ∈ 𝔫 := Ideal.Quotient.eq.1 h
      have h1 : (c M - c M') • u ∈ N₁ := hideal u hu _ hd
      have h2 : (c M - c M') • v M₀ ∈ N₂ := by
        apply (M₀.2.2.2.2 _).2
        have : ![0, (c M - c M') • v M₀] = (c M - c M') • ![u, v M₀] - ![(c M - c M') • u, 0] := by
          funext i; fin_cases i <;> simp
        rw [this]
        exact M₀.1.sub_mem (M₀.1.smul_mem _ (hv M₀)) ((M₀.2.2.2.1 _).1 h1)
      have hvv : v M - v M' ∈ N₂ := by
        have : v M - v M' = (v M - c M • v M₀) - (v M' - c M' • v M₀) + (c M - c M') • v M₀ := by
          rw [sub_smul]; abel
        rw [this]; exact N₂.add_mem (N₂.sub_mem (hc M) (hc M')) h2
      have hvv' : v M' - v M ∈ N₂ := by rw [← neg_sub]; exact N₂.neg_mem hvv
      exact Subtype.ext (le_antisymm (hle M M' hvv) (hle M' M hvv'))
  have h𝔫 : 𝔫 ≠ ⊥ := by
    intro h
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne hL₁)
    have : star s * β₁ * s ∈
        Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} :=
      Submodule.subset_span ⟨s, hs, s, hs, rfl⟩
    rw [hspan, h, Submodule.map_bot, Submodule.mem_bot] at this
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hs0) hβ₁0) hs0 this
  have hfin : Finite (𝓞 E ⧸ 𝔫) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    apply h𝔫
    rw [← Ideal.absNorm_eq_zero_iff, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Nat.card_eq_zero_of_infinite
  calc ENat.card {M // P M} ≤ ENat.card (𝓞 E ⧸ 𝔫) := ENat.card_le_card_of_injective hinj
    _ = (Ideal.absNorm 𝔫 : ENat) := by
      rw [ENat.card_eq_coe_natCard, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.GlueLines
