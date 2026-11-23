import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.HermitianLattices.TraceFormBilinSeparatingLeftIff
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsFiniteUnitaryClassesOfDualEqSmul

namespace GlobalTheory.DatumClasses

section Varying

open Module Submodule NumberField GlobalTheory.HermClass

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_finite_classes_of_forms {V : Type} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {α : Type*}
    (h : α → V →ₗ[E] V →ₗ⋆[E] E) (hs : ∀ a x y, h a y x = star (h a x y))
    (hnd : ∀ a y, (∀ x, h a y x = 0) → y = 0) {N : ℤ} (hN : N ≠ 0)
    (Λ : α → Submodule ℤ V)
    (hfg : ∀ a, (Λ a).FG) (hsp : ∀ a, span E (Λ a : Set V) = ⊤)
    (hO : ∀ a, ∀ c : E, IsIntegral ℤ c → ∀ x ∈ Λ a, c • x ∈ Λ a)
    (hint : ∀ a, ∀ x ∈ Λ a, ∀ y ∈ Λ a, IsIntegral ℤ (h a x y))
    (hdual : ∀ a y, (∀ x ∈ Λ a, IsIntegral ℤ (h a y x)) → (N : E) • y ∈ Λ a) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : V ≃ₗ[E] V, (∀ x y, h s (γ x) (γ y) = h a x y) ∧
      ∀ x, x ∈ Λ a ↔ γ x ∈ Λ s := by
  classical
  set n := finrank E V with hn
  obtain ⟨D, hD, hD0, H⟩ := exists_finite_orthogonal_lengths (E := E) n hN
  obtain ⟨M, hM, hMD⟩ := exists_int_mul_isIntegral E (hD.image fun a => a⁻¹)
  choose v hvΛ hvo hvD using fun a =>
    H V (h a) (Λ a) rfl (hs a) (hnd a) (hfg a) (hsp a) (hO a) (hint a) (hdual a)
  have hv0 : ∀ a i, h a (v a i) (v a i) ≠ 0 := fun a i h0 => hD0 (h0 ▸ hvD a i)
  have hsum : ∀ a (c : Fin n → E) j,
      h a (∑ i, c i • v a i) (v a j) = c j * h a (v a j) (v a j) := by
    intro a c j
    rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hvo a i j hij]
    · simp
  have hli : ∀ a, LinearIndependent E (v a) := fun a => Fintype.linearIndependent_iff.2
    fun c hc j => by
      have := hsum a c j
      rw [hc, map_zero, LinearMap.zero_apply] at this
      exact (mul_eq_zero.1 this.symm).resolve_right (hv0 a j)
  let B : α → Basis (Fin n) E V := fun a =>
    basisOfLinearIndependentOfCardEqFinrank' (v a) (hli a) (by simp [hn])
  have hB : ∀ a i, B a i = v a i := fun a i => by simp [B]
  let φ : α → V ≃ₗ[E] (Fin n → E) := fun a => (B a).equivFun
  have hφ : ∀ a c, (φ a).symm c = ∑ i, c i • v a i := fun a c => by
    simp [φ, Basis.equivFun_symm_apply, hB]
  have hform : ∀ a c c', h a ((φ a).symm c) ((φ a).symm c') =
      ∑ j, star (c' j) * (c j * h a (v a j) (v a j)) := fun a c c' => by
    rw [hφ, hφ, map_sum (h a _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulₛₗ, hsum, starRingEnd_apply, smul_eq_mul]
  let L : α → Submodule ℤ (Fin n → E) := fun a => (Λ a).map ((φ a).toLinearMap.restrictScalars ℤ)
  have hL : ∀ a c, c ∈ L a ↔ (φ a).symm c ∈ Λ a := fun a c =>
    ⟨by rintro ⟨x, hx, rfl⟩; simpa using hx, fun hc => ⟨_, hc, by simp⟩⟩
  let L₀ : Submodule ℤ (Fin n → E) :=
    Submodule.pi Set.univ fun _ => Subalgebra.toSubmodule (integralClosure ℤ E)
  have hL₀ : L₀.FG := Submodule.fg_pi fun _ => fg_integers E
  have hLF : ∀ a, L₀ ≤ L a ∧ ∀ x ∈ L a, (M : E) • x ∈ L₀ := fun a => by
    refine ⟨fun c hc => ?_, fun c hc j _ => ?_⟩
    · rw [hL, hφ]
      exact sum_mem fun i _ => hO a _ (hc i trivial) _ (hvΛ a i)
    · have h1 := hint a _ ((hL a c).1 hc) _ (hvΛ a j)
      rw [hφ, hsum] at h1
      have h2 := (hMD _ ⟨_, hvD a j, rfl⟩).mul h1
      change IsIntegral ℤ ((M : E) * c j)
      rwa [mul_mul_mul_comm, inv_mul_cancel₀ (hv0 a j), mul_one] at h2
  have hF := finite_between (E := E) L₀ hL₀ hM
  obtain ⟨S, hS, hSa⟩ := exists_finite_representatives
    (fun a => ((fun i => h a (v a i) (v a i), L a) :
      (Fin n → E) × Submodule ℤ (Fin n → E))) (by
    refine ((Set.Finite.pi' fun _ : Fin n => hD).prod hF).subset ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨hvD a, hLF a⟩)
  refine ⟨S, hS, fun a => ?_⟩
  obtain ⟨s, hs, he⟩ := hSa a
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2⟩ := he
  refine ⟨s, hs, (φ a).trans (φ s).symm, fun x x' => ?_, fun x => ?_⟩
  · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hform]
    conv_rhs => rw [← (φ a).symm_apply_apply x, ← (φ a).symm_apply_apply x', hform]
    exact Finset.sum_congr rfl fun j _ => by rw [congrFun h1 j]
  · rw [LinearEquiv.trans_apply, ← hL, h2, hL, LinearEquiv.symm_apply_apply]

end Varying

section Matrices

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_finite_classes_of_traceFormDual_eq {α : Type*} {ξ0 : E} (h0 : ξ0 ≠ 0)
    (G : α → Matrix (Fin r) (Fin r) E) (hG : ∀ s a b, cc (G s a b) = G s b a)
    (hdet : ∀ s, (G s).det ≠ 0) (Λ : α → Submodule (𝓞 E) (Fin r → E))
    (hΛ : ∀ s, IsLattice (Λ s)) (hself : ∀ s, traceFormDual ξ0 (G s) (Λ s) = Λ s) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : (Fin r → E) ≃ₗ[E] (Fin r → E),
      (∀ x y, herm (G s) (γ x) (γ y) = herm (G a) x y) ∧ ∀ x, x ∈ Λ a ↔ γ x ∈ Λ s := by
  classical
  have hc : ∀ x : E, cc x = star x := fun _ => rfl
  obtain ⟨D, hD, hDa⟩ := HermClass.exists_int_mul_isIntegral_of_trace E
  obtain ⟨M, hM, hMa⟩ := HermClass.exists_int_mul_isIntegral E (Set.toFinite {-ξ0, (-ξ0)⁻¹})
  have hN : M * D ≠ 0 := mul_ne_zero hM hD
  have hN' : ((M * D : ℤ) : E) ≠ 0 := by exact_mod_cast hN
  choose h hh using fun s => exists_sesquilinear_eq_herm (G s)
  have hs : ∀ s x y, h s y x = star (h s x y) := fun s x y => by
    rw [hh, hh, ← hc, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_conj (G s) (hG s)]
  have hnd : ∀ s y, (∀ x, h s y x = 0) → y = 0 := fun s y hy =>
    ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.eq_zero_of_herm (G s) (hdet s) y fun x => by rw [← hh, hy]
  obtain ⟨S, hS, H⟩ := exists_finite_classes_of_forms (fun s => ((M * D : ℤ) : E) • h s)
    (fun s x y => by simp [hs s x y])
    (fun s y hy => hnd s y fun x => by
      have := hy x
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hN')
    (mul_ne_zero hM hN) (fun a => (Λ a).restrictScalars ℤ)
    (fun a => by
      have : Module.Finite (𝓞 E) (Λ a) := Module.Finite.iff_fg.2 (hΛ a).1
      exact Module.Finite.iff_fg.1 (Module.Finite.trans (R := ℤ) (𝓞 E) (Λ a)))
    (fun a => (hΛ a).2) (fun a c hc x hx => (Λ a).smul_mem (⟨c, hc⟩ : 𝓞 E) hx)
    (fun a x hx y hy => by
      have h1 : IsIntegral ℤ ((D : E) * (-ξ0 * herm (G a) x y)) := hDa _ fun t ht => by
        have h2 : t • x ∈ traceFormDual ξ0 (G a) (Λ a) := by
          rw [hself]; exact (Λ a).smul_mem (⟨t, ht⟩ : 𝓞 E) hx
        obtain ⟨k, hk⟩ := mem_traceFormDual.1 h2 y hy
        exact ⟨k, by rw [← hk, EFf_smul_eq_trace, mul_comm]⟩
      have h3 := (hMa _ (Or.inr rfl)).mul h1
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hh]
      have h4 : ((M * D : ℤ) : E) * herm (G a) x y =
          (M : E) * (-ξ0)⁻¹ * ((D : E) * (-ξ0 * herm (G a) x y)) := by
        push_cast; field_simp
      rw [h4]; exact h3)
    (fun a y hy => by
      change _ ∈ Λ a
      rw [← hself, mem_traceFormDual]
      intro x hx
      have h1 := hy x hx
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hh] at h1
      have h2 := (hMa _ (Or.inl rfl)).mul h1
      have h3 := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) h2
      obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
      refine ⟨k, ?_⟩
      rw [EFf_smul_eq_trace, ← eq_intCast (algebraMap ℤ ℚ), hk]
      congr 1
      push_cast; ring)
  refine ⟨S, hS, fun a => ?_⟩
  obtain ⟨s, hsS, γ, h1, h2⟩ := H a
  refine ⟨s, hsS, γ, fun x y => ?_, h2⟩
  have := h1 x y
  simp only [LinearMap.smul_apply, smul_eq_mul, hh] at this
  exact mul_left_cancel₀ hN' this

end Matrices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem finite_data_of_signature :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ),
      ∃ (n : ℕ) (Di : Fin n → Datum H), (∀ i, (Di i).p = p ∧ (Di i).q = q) ∧
        ∀ D' : Datum H, D'.p = p → D'.q = q →
          ∃ (i : Fin n) (e : D'.La ≃ₗ[𝓞 E] (Di i).La),
            ∀ x y, (Di i).EF (e x) (e y) = D'.EF x y := by
  intro E _ _ _ H p q
  obtain ⟨ξ0, hξ, h0⟩ := FD.exists_imag (E := E)
  let α := {D : Datum H // D.p = p ∧ D.q = q}
  have hemb : ∀ a : α, ∃ φ : a.1.La →ₗ[𝓞 E] (Fin (p + q) → E), IsLatticeEmb φ := by
    rintro ⟨D, rfl, rfl⟩
    exact datum_exists_isLatticeEmb D
  choose φ hφ using hemb
  have spec := fun a : α => datum_gram_spec a.1 (hφ a) h0 hξ
  obtain ⟨S, hS, HS⟩ := exists_finite_classes_of_traceFormDual_eq h0
    (fun a : α => (hφ a).gram ξ0 a.1.EF) (fun a => (spec a).1) (fun a => (spec a).2.1)
    (fun a => LinearMap.range (φ a)) (fun a => (hφ a).2)
    (fun a => (perfect_iff_traceFormDual_eq h0 (spec a).2.1 (hφ a).2).mp (spec a).2.2.2)
  obtain ⟨n, f, hf⟩ := hS.fin_param
  refine ⟨n, fun i => (f i).1, fun i => (f i).2, fun D' hp hq => ?_⟩
  obtain ⟨s, hs, g, h1, h2⟩ := HS ⟨D', hp, hq⟩
  obtain ⟨i, rfl⟩ : s ∈ Set.range f := hf.2 ▸ hs
  set a : α := ⟨D', hp, hq⟩
  have hmap : (LinearMap.range (φ a)).map (g.restrictScalars (𝓞 E)).toLinearMap =
      LinearMap.range (φ (f i)) := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h2 x).1 hx
    · intro hv
      exact ⟨g.symm v, (h2 _).2 (by simpa using hv), by simp⟩
  let e : D'.La ≃ₗ[𝓞 E] (f i).1.La := (LinearEquiv.ofInjective (φ a) (hφ a).1).trans
    (((g.restrictScalars (𝓞 E)).ofSubmodules _ _ hmap).trans
      (LinearEquiv.ofInjective (φ (f i)) (hφ (f i)).1).symm)
  have he : ∀ x, φ (f i) (e x) = g (φ a x) := fun x => by
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.ofInjective_symm_apply]
    rfl
  refine ⟨i, e, fun x y => ?_⟩
  have : (((f i).1.EF (e x) (e y) : ℤ) : ℚ) = D'.EF x y := by
    rw [← (spec (f i)).2.2.1, he, he, FD.EFf, h1, ← FD.EFf, (spec a).2.2.1]
  exact_mod_cast this

end GlobalTheory.DatumClasses
