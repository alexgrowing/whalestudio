import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLineGenOn
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GenModel

open AlgebraicGeometry CategoryTheory

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

private theorem iota_multi_mem_span_of_mem_span {R : Subring Ω} {r : ℕ} {e : Fin r → E} (b : Fin r → E)
    (hb : ∀ i, b i ∈ Submodule.span R (Set.range e)) :
    exteriorPower.ιMulti Ω r b ∈ Submodule.span R {exteriorPower.ιMulti Ω r e} := by
  suffices H : ∀ s : Finset (Fin r), ∀ b : Fin r → E, (∀ i, b i ∈ Submodule.span R (Set.range e)) →
      (∀ i, i ∉ s → b i ∈ Set.range e) →
      exteriorPower.ιMulti Ω r b ∈ Submodule.span R {exteriorPower.ιMulti Ω r e} from
    H Finset.univ b hb (fun i hi => absurd (Finset.mem_univ i) hi)
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro b _ hb'
    choose g hg using fun i => hb' i (Finset.notMem_empty i)
    have hbg : b = e ∘ g := funext fun i => (hg i).symm
    subst hbg
    by_cases hinj : Function.Injective g
    · have hσ := Finite.injective_iff_bijective.1 hinj
      have he : e ∘ g = e ∘ ⇑(Equiv.ofBijective g hσ) := rfl
      rw [he, AlternatingMap.map_perm, Units.smul_def]
      exact zsmul_mem (Submodule.mem_span_singleton_self _) _
    · rw [AlternatingMap.map_eq_zero_of_not_injective _ _ (fun h => hinj h.of_comp)]
      exact Submodule.zero_mem _
  · intro a s ha ih b hb hb'
    have key : ∀ y ∈ Submodule.span R (Set.range e),
        exteriorPower.ιMulti Ω r (Function.update b a y) ∈
          Submodule.span R {exteriorPower.ιMulti Ω r e} := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        apply ih
        · intro i
          rcases eq_or_ne i a with rfl | hi
          · simpa using Submodule.subset_span hy
          · rw [Function.update_of_ne hi]
            exact hb i
        · intro i hi
          rcases eq_or_ne i a with rfl | hia
          · simpa using hy
          · rw [Function.update_of_ne hia]
            exact hb' i (by simp [hia, hi])
      | zero =>
        rw [AlternatingMap.map_update_zero]
        exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        rw [AlternatingMap.map_update_add]
        exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        rw [Subring.smul_def, AlternatingMap.map_update_smul, ← Subring.smul_def]
        exact Submodule.smul_mem _ c hx
    have hk := key (b a) (hb a)
    rwa [Function.update_eq_self] at hk

theorem wedge_of_frame {L : Lat ξ E} {r : ℕ} {e : Fin r → E} {x : Cpt ξ} (h : L.IsFrameAt e x) :
    L.wedge r x = Submodule.span (regAt ξ x) {exteriorPower.ιMulti Ω r e} := by
  obtain ⟨-, hL⟩ := h
  change Submodule.span (regAt ξ x)
    {w | ∃ b : Fin r → E, (∀ i, b i ∈ L x) ∧ w = exteriorPower.ιMulti Ω r b} = _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨b, hb, rfl⟩
    rw [hL] at hb
    exact iota_multi_mem_span_of_mem_span b hb
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.subset_span ⟨e, fun i => ?_, rfl⟩
    rw [hL]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem isCoeffAt_of_frame {A B : Lat ξ E} {p q : ℕ} {e : Fin p → E} {g : Fin q → E} {x : Cpt ξ}
    (he : A.IsFrameAt e x) (hg : B.IsFrameAt g x) {s t : Ω} (hs : s ≠ 0) (ht : t ≠ 0) :
    IsCoeffAt A B p q (s • exteriorPower.ιMulti Ω p e) (t • exteriorPower.ιMulti Ω q g) x (s / t) := by
  refine ⟨s⁻¹, t⁻¹, inv_ne_zero hs, inv_ne_zero ht, ?_, ?_, ?_⟩
  · rw [wedge_of_frame he, smul_smul, inv_mul_cancel₀ hs, one_smul]
  · rw [wedge_of_frame hg, smul_smul, inv_mul_cancel₀ ht, one_smul]
  · field_simp

theorem unit_of_span_eq {F : Type} [AddCommGroup F] [Module Ω F] {x : Cpt ξ} {a : F} (ha : a ≠ 0) {α α' : Ω}
    (h : Submodule.span (regAt ξ x) {α • a} = Submodule.span (regAt ξ x) {α' • a}) :
    ∃ u : regAt ξ x, α = u * α' := by
  have hmem : α • a ∈ Submodule.span (regAt ξ x) {α' • a} := by
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨u, ?_⟩
  rw [Subring.smul_def, smul_smul] at hu
  exact (smul_left_injective Ω ha hu).symm

private theorem div_mem_reg_at_of_is_coeff_at {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {x : Cpt ξ}
    {f f' : Ω} (ha : a ≠ 0) (hb : b ≠ 0) (h : IsCoeffAt A B p q a b x f)
    (h' : IsCoeffAt A B p q a b x f') : f / f' ∈ regAt ξ x := by
  obtain ⟨α, β, hα, hβ, hA, hB, e1⟩ := h
  obtain ⟨α', β', hα', hβ', hA', hB', e2⟩ := h'
  obtain ⟨u', hu'⟩ := unit_of_span_eq ha (hA'.symm.trans hA)
  obtain ⟨v, hv⟩ := unit_of_span_eq hb (hB.symm.trans hB')
  have hf' : f' ≠ 0 := by
    rintro rfl
    exact hβ' (by rw [← e2, zero_mul])
  have key : f = (v : Ω) * u' * f' := by
    apply mul_right_cancel₀ hα
    linear_combination e1 + hv - (v : Ω) * e2 + (v : Ω) * f' * hu'
  rw [key, mul_div_assoc, div_self hf', mul_one]
  exact mul_mem v.2 u'.2

theorem unitAt_div {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {x : Cpt ξ} {f f' : Ω}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : IsCoeffAt A B p q a b x f) (h' : IsCoeffAt A B p q a b x f') :
    unitAt ξ x (f / f') := by
  have hf : f ≠ 0 := by
    obtain ⟨α, β, -, hβ, -, -, e1⟩ := h
    rintro rfl
    exact hβ (by rw [← e1, zero_mul])
  have hf' : f' ≠ 0 := by
    obtain ⟨α, β, -, hβ, -, -, e1⟩ := h'
    rintro rfl
    exact hβ (by rw [← e1, zero_mul])
  refine ⟨div_ne_zero hf hf', div_mem_reg_at_of_is_coeff_at ha hb h h', ?_⟩
  rw [inv_div]
  exact div_mem_reg_at_of_is_coeff_at ha hb h' h

theorem isCoeffAt_smul {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {x : Cpt ξ} {f c d : Ω}
    (hc : c ≠ 0) (hd : d ≠ 0) (h : IsCoeffAt A B p q a b x f) :
    IsCoeffAt A B p q (c • a) (d • b) x (c * f / d) := by
  obtain ⟨α, β, hα, hβ, hA, hB, e1⟩ := h
  refine ⟨α / c, β / d, div_ne_zero hα hc, div_ne_zero hβ hd, ?_, ?_, ?_⟩
  · rw [hA, smul_smul, div_mul_cancel₀ _ hc]
  · rw [hB, smul_smul, div_mul_cancel₀ _ hd]
  · rw [← e1]
    field_simp

theorem unitAt_of_isLineGenOn {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {T : Set (Cpt ξ)}
    {c : Ω} (hc : c ≠ 0) (h : IsLineGenOn A B p q a b T) (h' : IsLineGenOn A B p q (c • a) b T)
    {x : Cpt ξ} (hx : x ∈ T) : unitAt ξ x c := by
  have h1 : IsCoeffAt A B p q (c • a) b x c := by
    have h2 := isCoeffAt_smul hc one_ne_zero (h.2.2 x hx)
    rwa [one_smul, mul_one, div_one] at h2
  have h3 := unitAt_div h'.1 h'.2.1 h1 (h'.2.2 x hx)
  rwa [div_one] at h3

theorem ιMulti_ne_zero {r : ℕ} {e : Fin r → E} (h : LinearIndependent Ω e) :
    exteriorPower.ιMulti Ω r e ≠ 0 := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend h.repr
  let f : Fin r → Module.Dual Ω E := fun j => Finsupp.lapply j ∘ₗ g
  have hfe : ∀ i j, f j (e i) = if i = j then 1 else 0 := by
    intro i j
    have h1 : g (e i) = Finsupp.single i 1 := by
      have h2 := congrArg (fun φ => φ ⟨e i, Submodule.subset_span ⟨i, rfl⟩⟩) hg
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
      rw [h2]
      exact h.repr_eq_single i _ rfl
    simp [f, h1, Finsupp.single_apply]
  intro h0
  have hd := exteriorPower.pairingDual_ιMulti_ιMulti f e
  rw [h0, map_zero] at hd
  have hm : (Matrix.of fun i j => f j (e i)) = 1 := by
    ext i j
    rw [Matrix.of_apply, hfe, Matrix.one_apply]
  rw [hm, Matrix.det_one] at hd
  exact zero_ne_one hd

theorem ne_zero_of_frame {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {x : Cpt ξ} {f : Ω}
    {e : Fin p → E} (he : A.IsFrameAt e x) (h : IsCoeffAt A B p q a b x f) : a ≠ 0 := by
  rintro rfl
  obtain ⟨α, β, hα, -, hA, -, -⟩ := h
  rw [wedge_of_frame he, smul_zero] at hA
  have hmem : exteriorPower.ιMulti Ω p e ∈ Submodule.span (regAt ξ x) {(0 : ⋀[Ω]^p E)} := by
    rw [← hA]
    exact Submodule.mem_span_singleton_self _
  rw [Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hmem
  exact ιMulti_ne_zero he.1 hmem

end General

section Int

open CptModel

def line (v : Fin 2 → ℚ) : Lat (pt (algebraMap ℤ ℚ)) (Fin 2 → ℚ) :=
  fun x => Submodule.span (regAt _ x) (Set.range ![v])

theorem li {v : Fin 2 → ℚ} (hv : v ≠ 0) : LinearIndependent ℚ ![v] := by
  exact linearIndependent_unique_iff.2 (by simpa using hv)

theorem frame {v : Fin 2 → ℚ} (hv : v ≠ 0) (x) : (line v).IsFrameAt ![v] x := by
  exact ⟨li hv, rfl⟩

theorem ne₀ : (![2, 0] : Fin 2 → ℚ) ≠ 0 := by
  intro h
  simpa using congrFun h 0
theorem ne₁ : (![0, 1] : Fin 2 → ℚ) ≠ 0 := by
  intro h
  simpa using congrFun h 1

theorem gen : IsLineGenOn (line ![2, 0]) (line ![0, 1]) 1 1 (exteriorPower.ιMulti ℚ 1 ![![2, 0]])
    (exteriorPower.ιMulti ℚ 1 ![![0, 1]]) Set.univ := by
  refine ⟨ιMulti_ne_zero (li ne₀), ιMulti_ne_zero (li ne₁), fun x _ => ?_⟩
  have h := isCoeffAt_of_frame (frame ne₀ x) (frame ne₁ x) (one_ne_zero) (one_ne_zero)
  rwa [one_smul, one_smul, div_one] at h

theorem coeff_half (x) : IsCoeffAt (line ![2, 0]) (line ![0, 1]) 1 1
    ((2 : ℚ)⁻¹ • exteriorPower.ιMulti ℚ 1 ![![2, 0]]) (exteriorPower.ιMulti ℚ 1 ![![0, 1]]) x 2⁻¹ := by
  have h := isCoeffAt_of_frame (frame ne₀ x) (frame ne₁ x) (inv_ne_zero two_ne_zero) one_ne_zero
  rwa [one_smul, div_one] at h

theorem not_gen : ¬ IsLineGenOn (line ![2, 0]) (line ![0, 1]) 1 1
    ((2 : ℚ)⁻¹ • exteriorPower.ιMulti ℚ 1 ![![2, 0]]) (exteriorPower.ιMulti ℚ 1 ![![0, 1]]) {two} := by
  intro h
  have hg : IsLineGenOn (line ![2, 0]) (line ![0, 1]) 1 1 (exteriorPower.ιMulti ℚ 1 ![![2, 0]])
      (exteriorPower.ιMulti ℚ 1 ![![0, 1]]) {two} := ⟨gen.1, gen.2.1, fun x _ => gen.2.2 x trivial⟩
  exact half_notMem (unitAt_of_isLineGenOn (inv_ne_zero two_ne_zero) hg h (Set.mem_singleton _)).2.1

end Int

end GlobalTheory.CompanionTheory.Ar.Flat.GenModel
