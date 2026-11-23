import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.CvSmulRight
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.NonVan
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.MemSuppMono
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoShape

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem lin_zero {X : Type*} (L : Submodule ℂ (X → ℂ)) (Λ : (X → ℂ) → ℂ)
    (hlin : ∀ x ∈ L, ∀ y ∈ L, ∀ c : ℂ, Λ (c • x + y) = c * Λ x + Λ y) : Λ 0 = 0 := by
  have h := hlin 0 L.zero_mem 0 L.zero_mem 1
  simp only [smul_zero, add_zero, one_mul] at h
  simpa using h

private theorem lin_sum {X ι : Type*} (L : Submodule ℂ (X → ℂ)) (Λ : (X → ℂ) → ℂ)
    (hlin : ∀ x ∈ L, ∀ y ∈ L, ∀ c : ℂ, Λ (c • x + y) = c * Λ x + Λ y)
    (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ) (hf : ∀ i ∈ s, f i ∈ L) :
    Λ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * Λ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lin_zero L Λ hlin
  | insert i s hi ih =>
    have hf' : ∀ j ∈ s, f j ∈ L := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      hlin _ (hf i (Finset.mem_insert_self i s)) _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hf' j hj)),
      ih hf']

private theorem lin_eq_of_sub {X : Type*} (L C : Submodule ℂ (X → ℂ)) (Λ : (X → ℂ) → ℂ)
    (hlin : ∀ x ∈ L, ∀ y ∈ L, ∀ c : ℂ, Λ (c • x + y) = c * Λ x + Λ y)
    (hC : ∀ x ∈ C, Λ x = 0) {u v : X → ℂ} (hu : u ∈ L) (hv : v ∈ L) (huv : u - v ∈ C) : Λ u = Λ v := by
  have h := hlin (u - v) (L.sub_mem hu hv) v hv 1
  rw [one_smul, sub_add_cancel, hC _ huv, one_mul, zero_add] at h
  exact h

private theorem th_mem (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    [MeasurableSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) {a : Fin n → ℤ} (ha : Antitone a) :
    th μ a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
  Submodule.smul_mem _ _ (dcoShape F n a ha).2.2.1

private theorem dom_add {n : ℕ} {r s : LaurentRing n} (hr : Dom r) (hs : Dom s) : Dom (r + s) := by
  classical
  intro a ha
  rw [AddMonoidAlgebra.coeff_add] at ha
  rcases Finset.mem_union.1 (Finsupp.support_add ha) with h | h
  · exact hr a h
  · exact hs a h

private theorem dom_smul {n : ℕ} {r : LaurentRing n} (c : ℂ) (hr : Dom r) : Dom (c • r) := by
  classical
  intro a ha
  rw [AddMonoidAlgebra.coeff_smul] at ha
  exact hr a (Finsupp.support_smul ha)

private theorem sdom_add {n : ℕ} {r s : LaurentRing n} (hr : SDom r) (hs : SDom s) : SDom (r + s) := by
  classical
  intro a ha
  rw [AddMonoidAlgebra.coeff_add] at ha
  rcases Finset.mem_union.1 (Finsupp.support_add ha) with h | h
  · exact hr a h
  · exact hs a h

private theorem sdom_smul {n : ℕ} {r : LaurentRing n} (c : ℂ) (hr : SDom r) : SDom (c • r) := by
  classical
  intro a ha
  rw [AddMonoidAlgebra.coeff_smul] at ha
  exact hr a (Finsupp.support_smul ha)

private theorem clause_span {n l : ℕ} (Y M M' : LaurentRing n) (P : Finset (LaurentRing n))
    (h : ∀ p ∈ P, SDom (Y * p) ∧ (∃ r, Dom r ∧ Y * p = M * r) ∧ ∃ r', Dom r' ∧ bc l (Y * p) = M' * r')
    (p : LaurentRing n) (hp : p ∈ Submodule.span ℂ (P : Set (LaurentRing n))) :
    SDom (Y * p) ∧ (∃ r, Dom r ∧ Y * p = M * r) ∧ ∃ r', Dom r' ∧ bc l (Y * p) = M' * r' := by
  induction hp using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    refine ⟨?_, ⟨0, ?_, by simp⟩, 0, ?_, by simp⟩
    · intro a ha; simp at ha
    · intro a ha; simp at ha
    · intro a ha; simp at ha
  | add x y _ _ hx hy =>
    obtain ⟨h1, ⟨r, hr, e⟩, r', hr', e'⟩ := hx
    obtain ⟨g1, ⟨s, hs, f⟩, s', hs', f'⟩ := hy
    refine ⟨by rw [mul_add]; exact sdom_add h1 g1, ⟨r + s, dom_add hr hs, by rw [mul_add, mul_add, e, f]⟩,
      r' + s', dom_add hr' hs', by rw [mul_add, map_add, mul_add, e', f']⟩
  | smul c x _ hx =>
    obtain ⟨h1, ⟨r, hr, e⟩, r', hr', e'⟩ := hx
    refine ⟨by rw [mul_smul_comm]; exact sdom_smul c h1, ⟨c • r, dom_smul c hr, by rw [mul_smul_comm, mul_smul_comm, e]⟩,
      c • r', dom_smul c hr', by rw [mul_smul_comm, map_smul, mul_smul_comm, e']⟩

private theorem thP_bc {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    [MeasurableSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) (l : ℕ) (y : LaurentRing n) :
    thP μ (bc l y) = ∑ a ∈ y.coeff.support, y.coeff a • th μ ((l : ℤ) • a) := by
  have hc : (bc l y).coeff = Finsupp.mapDomain (fun m : Fin n → ℤ => (l : ℤ) • m) y.coeff := rfl
  unfold thP
  rw [hc, Finsupp.sum_mapDomain_index (h := fun a c => c • th μ a) (fun a => zero_smul _ _) (fun a c d => add_smul _ _ _)]
  rfl

private theorem range_Y {n : ℕ} (t : ℂ) (a : Fin n → ℤ) (ha : ∀ i, 0 ≤ a i) :
    symSum (monomial a * dPol n t) ∈ (polyEmb n).range := by
  have h1 : (monomial a : LaurentRing n) ∈ (polyEmb n).range := by
    refine mem_range_polyEmb fun b hb i => ?_
    rw [AddMonoidAlgebra.coeff_single] at hb
    have : b = a := by simpa using Finsupp.support_single_subset hb
    rw [this]
    exact ha i
  have hv : ∀ i : Fin n, (varL i : LaurentRing n) ∈ (polyEmb n).range := fun i =>
    AlgHom.mem_range _ |>.2 ⟨MvPolynomial.X i, polyEmb_X i⟩
  have h2 : dPol n t ∈ (polyEmb n).range :=
    Subalgebra.prod_mem _ fun p _ => Subalgebra.sub_mem _ (hv _) (Subalgebra.smul_mem _ (hv _) _)
  obtain ⟨Q, hQ⟩ := AlgHom.mem_range _ |>.1 (Subalgebra.mul_mem _ h1 h2)
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [← hQ]
  exact AlgHom.mem_range _ |>.2 ⟨MvPolynomial.rename σ Q, polyEmb_rename σ Q⟩

theorem UpperTheory.ConvolutionTheory.H.deepAbs :
    ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n l : ℕ), 1 ≤ l → (qF E : ℂ) = (qF k : ℂ) ^ l →
      ∀ [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)) [μE.IsHaarMeasure] [μk.IsHaarMeasure],
      μE (integralGL E n : Set (GL (Fin n) E)) = 1 → μk (integralGL k n : Set (GL (Fin n) k)) = 1 →
      ∀ P : Finset (LaurentRing n), (∀ p ∈ P, p ∈ symmetricLaurent n) → ∀ z : Fin n → ℂˣ,
      ∃ g ∈ symmetricLaurent n, g ∈ (polyEmb n).range ∧ evalAt z g ≠ 0 ∧ ∀ p ∈ Submodule.span ℂ (P : Set (LaurentRing n)),
        ∀ (h : SphericalHecke μE (F := E) (n := n)) (f : SphericalHecke μk (F := k) (n := n)),
          satakeTransform μE h = g * p → satakeTransform μk f = bc l (g * p) →
          ∀ (ΛE : (GL (Fin n) E → ℂ) → ℂ) (Λk : (GL (Fin n) k → ℂ) → ℂ),
          (∀ x ∈ locallyConstantCompactSupport (GL (Fin n) E) ℂ ℂ, ∀ y ∈ locallyConstantCompactSupport (GL (Fin n) E) ℂ ℂ, ∀ c : ℂ,
          ΛE (c • x + y) = c * ΛE x + ΛE y) → (∀ x ∈ comm μE, ΛE x = 0) →
          (∀ x ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ, ∀ y ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ, ∀ c : ℂ,
          Λk (c • x + y) = c * Λk x + Λk y) → (∀ x ∈ comm μk, Λk x = 0) →
          (∀ a : Fin n → ℤ, StrictAnti a → ΛE (th μE a) = Λk (th μk ((l : ℤ) • a))) →
          ΛE (fun x => (h : HeckeAlgebra μE) x) = Λk fun x => (f : HeckeAlgebra μk) x := by
  intro k E _ _ _ _ _ _ _ _ n l hl hq _ _ _ _ μE μk _ _ hE hk P hP z
  classical
  obtain ⟨ν, hν⟩ := core E n μE hE
  obtain ⟨ν', hν'⟩ := core k n μk hk
  obtain ⟨t, ht⟩ : ∃ t : ℂ, t = ((qF k : ℂ))⁻¹ := ⟨_, rfl⟩
  have hte : ((qF E : ℂ))⁻¹ = t ^ l := by rw [hq, ht, inv_pow]
  rw [hte] at hν
  rw [← ht] at hν'
  obtain ⟨m, hm⟩ := depth n l hl t P ν ν'
  have hnorm : ‖t ^ l‖ < 1 := by
    rw [← hte, norm_inv, Complex.norm_natCast]
    have h1 : 1 < qF E := Finite.one_lt_card
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast h1)
  obtain ⟨a, hgap, ha0, hne⟩ := nonVan n (t ^ l) hnorm z m
  refine ⟨symSum (monomial a * dPol n (t ^ l)), (symAlg n l _).1, range_Y _ a ha0, hne, ?_⟩
  intro p hp h f hSh hSf ΛE Λk hlE hzE hlk hzk hth
  obtain ⟨hSD, ⟨r, hr, hyr⟩, r', hr', hyr'⟩ := clause_span (l := l) (monomial a * dPol n (t ^ l)) (monomial ν * dPol n (t ^ l))
    (monomial ν' * dPol n t) P (fun p hp => hm a hgap p hp) p hp
  have hps : p ∈ symmetricLaurent n := by
    have : Submodule.span ℂ (P : Set (LaurentRing n)) ≤ Subalgebra.toSubmodule (symmetricLaurent n) :=
      Submodule.span_le.2 fun x hx => hP x hx
    exact this hp
  obtain ⟨-, hb, hmul, -, -⟩ := symAlg n l (monomial a * dPol n (t ^ l))
  have hSy : symSum (monomial a * dPol n (t ^ l) * p) = symSum (monomial a * dPol n (t ^ l)) * p := hmul p hps
  obtain ⟨-, hb', -, -, -⟩ := symAlg n l (monomial a * dPol n (t ^ l) * p)
  set y := monomial a * dPol n (t ^ l) * p with hy
  have hcE := hν r hr h (by rw [hSh, ← hSy, hyr])
  have hck := hν' r' hr' f (by rw [hSf, ← hSy, hb', hyr'])
  rw [← hyr] at hcE
  rw [← hyr'] at hck
  have hanti : ∀ b ∈ y.coeff.support, Antitone b := fun b hb => (hSD b hb).antitone
  have hantl : ∀ b ∈ y.coeff.support, Antitone ((l : ℤ) • b) := fun b hb i j hij => by
    have := hanti b hb hij
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hmE : thP μE y ∈ locallyConstantCompactSupport (GL (Fin n) E) ℂ ℂ :=
    Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (th_mem E μE (hanti b hb))
  have hmk : thP μk (bc l y) ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ := by
    rw [thP_bc]
    exact Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (th_mem k μk (hantl b hb))
  rw [← lin_eq_of_sub _ (comm μE) ΛE hlE hzE hmE (HeckeAlgebra.mem _) hcE,
    ← lin_eq_of_sub _ (comm μk) Λk hlk hzk hmk (HeckeAlgebra.mem _) hck, thP_bc]
  unfold thP Finsupp.sum
  rw [lin_sum _ ΛE hlE _ _ _ fun b hb => th_mem E μE (hanti b hb),
    lin_sum _ Λk hlk _ _ _ fun b hb => th_mem k μk (hantl b hb)]
  exact Finset.sum_congr rfl fun b hb => by rw [hth b (hSD b hb)]
