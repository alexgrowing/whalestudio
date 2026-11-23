import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsLZBasis
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntegerRingSmulMemSubmodule

namespace GlobalTheory.MaxCusp

open NumberField Complex MeasureTheory Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.TorusFourier
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}

def IsIsotropicSub (G : Matrix (Fin r) (Fin r) E) (V : Submodule E (Fin r → E)) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, herm G v w = 0

def IsMaximal (X : Data E r) (u : Fin d → Fin r → E) : Prop :=
  IsIsoFam X.Gm u ∧ (∀ i, u i ∈ X.Λ) ∧
    Maximal (IsIsotropicSub X.Gm) (Submodule.span E (Set.range u))

theorem isIsotropicSub_span {G : Matrix (Fin r) (Fin r) E} {s : Set (Fin r → E)}
    (h : ∀ v ∈ s, ∀ w ∈ s, herm G v w = 0) : IsIsotropicSub G (Submodule.span E s) := by
  intro v hv w hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    induction hw using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp [herm, cc]
    | add y z _ _ hy hz =>
      have : herm G x (y + z) = herm G x y + herm G x z := by
        simp [herm, cc, mul_add, Finset.sum_add_distrib]
      rw [this, hy, hz, add_zero]
    | smul c y _ hy =>
      have : herm G x (c • y) = cc c * herm G x y := by
        simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [this, hy, mul_zero]
  | zero => simp [herm]
  | add x y _ _ hx hy =>
    have : herm G (x + y) w = herm G x w + herm G y w := by
      simp [herm, add_mul, Finset.sum_add_distrib]
    rw [this, hx, hy, add_zero]
  | smul c x _ hx => rw [herm_smul_left', hx, mul_zero]

theorem herm_comb_self {G : Matrix (Fin r) (Fin r) E} {u : Fin d → Fin r → E}
    (hu : ∀ i k, herm G (u i) (u k) = 0) (a : Fin d → E) :
    herm G (∑ i, a i • u i) (∑ i, a i • u i) = 0 := by
  have hm : ∑ i, a i • u i ∈ Submodule.span E (Set.range u) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine isIsotropicSub_span ?_ _ hm _ hm
  rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩
  exact hu i k

theorem exists_smul_mem (X : Data E r) (v : Fin r → E) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ X.Λ := by
  first
  | exact @_root_.GlobalTheory.SubmoduleScalarClosure.main
  | exact _root_.GlobalTheory.SubmoduleScalarClosure.main
  | (apply _root_.GlobalTheory.SubmoduleScalarClosure.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubmoduleScalarClosure.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubmoduleScalarClosure.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubmoduleScalarClosure.main ..)

theorem exists_isMaximal_ge (X : Data E r) {V : Submodule E (Fin r → E)}
    (hV : IsIsotropicSub X.Gm V) :
    ∃ (d : ℕ) (u : Fin d → Fin r → E), IsMaximal X u ∧ V ≤ Submodule.span E (Set.range u) := by
  obtain ⟨J, hVJ, hJ⟩ := exists_maximal_ge_of_wellFoundedGT (IsIsotropicSub X.Gm) V hV
  set e := Module.finBasis E J
  choose n hn0 hn using fun i => exists_smul_mem X (e i : Fin r → E)
  have hn' : ∀ i, (n i : E) ≠ 0 := fun i => Int.cast_ne_zero.2 (hn0 i)
  set e' := e.unitsSMul fun i => Units.mk0 _ (hn' i)
  have he' : ∀ i, (e' i : Fin r → E) = (n i : E) • (e i : Fin r → E) := fun i => by
    simp [e', Basis.unitsSMul_apply, Units.smul_def]
  have hsp : Submodule.span E (Set.range fun i => (e' i : Fin r → E)) = J := by
    have := congrArg (Submodule.map J.subtype) e'.span_eq
    rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at this
  refine ⟨_, fun i => (e' i : Fin r → E), ⟨⟨fun i k => hJ.prop _ (e' i).2 _ (e' k).2,
    e'.linearIndependent.map' J.subtype (Submodule.ker_subtype _)⟩, fun i => ?_, ?_⟩, ?_⟩
  · show (e' i : Fin r → E) ∈ X.Λ
    rw [he']; exact hn i
  · rwa [hsp]
  · rwa [hsp]

theorem exists_isMaximal (X : Data E r) : ∃ (d : ℕ) (u : Fin d → Fin r → E), IsMaximal X u := by
  obtain ⟨d, u, hu, -⟩ := exists_isMaximal_ge X (V := ⊥) (by
    intro v hv w _
    rw [Submodule.mem_bot] at hv
    simp [hv, herm])
  exact ⟨d, u, hu⟩

theorem exists_isMaximal_mem_span (X : Data E r) {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) :
    ∃ (d : ℕ) (u : Fin d → Fin r → E), IsMaximal X u ∧ ξ ∈ Submodule.span E (Set.range u) := by
  obtain ⟨d, u, hu, h⟩ := exists_isMaximal_ge X (V := Submodule.span E {ξ})
    (isIsotropicSub_span (by rintro _ rfl _ rfl; exact hξ))
  exact ⟨d, u, hu, h (Submodule.mem_span_singleton_self ξ)⟩

theorem exists_isMaximal_pos : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E)
    (X : DataX E 2) (d : ℕ) (u : Fin d → Fin 2 → E),
    X.dom.Nonempty ∧ 0 < d ∧ IsMaximal X.toData u := by
  obtain ⟨X, -, -, hX, ⟨ξ, hξ⟩, -⟩ := exists_cuspData_hyperbolic
  obtain ⟨d, u, hu, h⟩ := exists_isMaximal_mem_span X.toData hξ.2.1
  refine ⟨_, _, _, _, X, d, u, hX, Nat.pos_of_ne_zero ?_, hu⟩
  rintro rfl
  rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at h
  exact hξ.2.2 h

section Torus

variable (X : Data E r)

def orb (u : Fin d → Fin r → E) (G : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (b : hermSub X.Ψ d) : ℂ :=
  G (Zb X u b.1 x)

def lineMap (a : X.Ψ → Fin d → ℂ) : (X.Ψ → ℝ) →ₗ[ℝ] hermSub X.Ψ d where
  toFun s := ⟨fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k), fun τ i k => by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]; ring⟩
  map_add' s t := by apply Subtype.ext; funext τ i k; simp; ring
  map_smul' c s := by apply Subtype.ext; funext τ i k; simp; ring

def nuForm (ν : X.Ψ → ℝ) : (X.Ψ → ℝ) →ₗ[ℝ] ℝ where
  toFun s := 2 * ∑ τ, ν τ * s τ
  map_add' s t := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c s := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem nuForm_apply (ν s : X.Ψ → ℝ) : nuForm X ν s = 2 * ∑ τ, ν τ * s τ := rfl

theorem nuForm_injective : Function.Injective (nuForm X) := by
  classical
  intro ν ν' h
  funext τ
  simpa [nuForm_apply, Pi.single_apply] using LinearMap.congr_fun h (Pi.single τ 1)

theorem form_comp_lineMap (χ : X.Ψ → Fin d → Fin d → ℂ) (a : X.Ψ → Fin d → ℂ) :
    form X χ ∘ₗ lineMap X a = nuForm X fun τ => (chiAt X χ a τ).re := by
  refine LinearMap.ext fun s => ?_
  rw [LinearMap.comp_apply, form_apply, nuForm_apply, pairR, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Complex.re_mul_ofReal, chiAt]
  congr 1
  simp only [lineMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem chiAt_re {χ : X.Ψ → Fin d → Fin d → ℂ} (hχ : IsHerm χ) (a : X.Ψ → Fin d → ℂ) (τ : X.Ψ) :
    ((chiAt X χ a τ).re : ℂ) = chiAt X χ a τ := by
  rw [← Complex.conj_eq_iff_re, chiAt]
  simp only [map_sum, map_mul, Complex.conj_conj, ← hχ τ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_comp_eq_iff (χ : X.Ψ → Fin d → Fin d → ℂ) (a : X.Ψ → Fin d → ℂ) (ν : X.Ψ → ℝ) :
    form X χ ∘ₗ lineMap X a = nuForm X ν ↔ ∀ τ, (chiAt X χ a τ).re = ν τ := by
  rw [form_comp_lineMap, (nuForm_injective X).eq_iff, funext_iff]

theorem cubeCoeff_orb {n : ℕ} (e : Fin n → hermSub X.Ψ d) (u : Fin d → Fin r → E)
    (χ : X.Ψ → Fin d → Fin d → ℂ) (G : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    cubeCoeff e (orb X u G x) (form X χ) =
      ∫ t in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        G (Zb X u (∑ j, (t j : ℂ) • (e j).1) x) *
          cexp (-(4 * Real.pi * I) * pairR X χ (∑ j, (t j : ℂ) • (e j).1)) := by
  unfold cubeCoeff
  congr 1
  funext t
  have : (∑ j, t j • e j).1 = ∑ j, (t j : ℂ) • (e j).1 := by
    simp only [Submodule.coe_sum, Submodule.coe_smul, Complex.coe_smul]
  rw [orb, eNeg, form_apply, this]
  congr 2
  push_cast
  ring

theorem exists_fz_eq {g : ℕ} (hg : 0 < g) :
    ∃ e : Basis (Fin (d * d * Fintype.card X.Ψ)) ℝ (hermSub X.Ψ d),
      Submodule.span ℤ (Set.range e) = latZ X d g ∧
      ∀ (u : Fin d → Fin r → E) χ, IsHerm χ → IsFreqZ X g χ → ∀ G x,
        fz X u g χ G x = cubeCoeff e (orb X u G x) (form X χ) := by
  have h := exists_isLZBasis (d := d) X hg
  obtain ⟨e, he, hsp⟩ := h.choose_spec.exists_basis
  refine ⟨e, hsp, fun u χ h1 h2 G x => ?_⟩
  rw [cubeCoeff_orb, fz, if_pos ⟨h1, h2⟩, dif_pos h]
  simp only [he]

theorem fz_of_not {g : ℕ} {χ : X.Ψ → Fin d → Fin d → ℂ} (h : ¬ (IsHerm χ ∧ IsFreqZ X g χ))
    (u : Fin d → Fin r → E) (G : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : fz X u g χ G x = 0 := by
  rw [fz, if_neg h]

theorem orb_add {u : Fin d → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (G : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (b l : hermSub X.Ψ d) :
    orb X u G x (b + l) = G (Zb X u l.1 (Zb X u b.1 x)) := by
  rw [orb, Zb_Zb X u hu, add_comm]; rfl

theorem orb_periodic {u : Fin d → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0) {g : ℕ}
    {G : Frame X.Ψ r → ℂ} (hG : ∀ b ∈ LZ X d g, ∀ x ∈ X.dom, G (Zb X u b x) = G x)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∀ l ∈ latZ X d g, ∀ b, orb X u G x (b + l) = orb X u G x b := fun l hl b => by
  rw [orb_add X hu, hG _ hl _ (Zb_dom X u hu _ b.2 hx)]; rfl

theorem continuous_orb {u : Fin d → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    {G : Frame X.Ψ r → ℂ} (hG : ContinuousOn G X.dom) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Continuous (orb X u G x) :=
  hG.comp_continuous ((continuous_Zb X u x).comp continuous_subtype_val)
    fun b => Zb_dom X u hu _ b.2 hx

theorem fz_eq_of_isLZBasis {u : Fin d → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0) {g : ℕ}
    (hg : 0 < g) {G : Frame X.Ψ r → ℂ} (hG : ∀ b ∈ LZ X d g, ∀ x ∈ X.dom, G (Zb X u b x) = G x)
    {ω : Fin (d * d * Fintype.card X.Ψ) → X.Ψ → Fin d → Fin d → ℂ} (hω : IsLZBasis X g ω)
    {χ : X.Ψ → Fin d → Fin d → ℂ} (h1 : IsHerm χ) (h2 : IsFreqZ X g χ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    fz X u g χ G x =
      ∫ t in Set.pi Set.univ (fun _ : Fin (d * d * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1),
        G (Zb X u (∑ j, (t j : ℂ) • ω j) x) *
          cexp (-(4 * Real.pi * I) * pairR X χ (∑ j, (t j : ℂ) • ω j)) := by
  obtain ⟨e, he, hfz⟩ := exists_fz_eq (d := d) X hg
  obtain ⟨e', he', hsp⟩ := hω.exists_basis
  have hD := ZSpan.isAddFundamentalDomain e (Measure.addHaar : Measure (hermSub X.Ψ d))
  have hp := orb_periodic X hu hG hx
  have hf := (isFreqZ_iff X χ).1 h2
  rw [hfz u χ h1 h2, ← coeff_eq_cubeCoeff e hD (he ▸ hp) (he ▸ hf),
    coeff_eq_cubeCoeff e' (by rw [hsp, ← he]; exact hD) (hsp ▸ hp) (hsp ▸ hf), cubeCoeff_orb]
  simp only [he']

theorem eq_zero_iff_fz {u : Fin d → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0) {g : ℕ}
    (hg : 0 < g) {G : Frame X.Ψ r → ℂ} (hc : ContinuousOn G X.dom)
    (hG : ∀ b ∈ LZ X d g, ∀ x ∈ X.dom, G (Zb X u b x) = G x) :
    (∀ x ∈ X.dom, G x = 0) ↔
      ∀ χ, IsHerm χ → IsFreqZ X g χ → ∀ x ∈ X.dom, fz X u g χ G x = 0 := by
  obtain ⟨e, he, hfz⟩ := exists_fz_eq (d := d) X hg
  constructor
  · intro h χ h1 h2 x hx
    have : orb X u G x = 0 := funext fun b => h _ (Zb_dom X u hu _ b.2 hx)
    simp [hfz u χ h1 h2, this, cubeCoeff]
  · intro h x hx
    have hD := ZSpan.isAddFundamentalDomain e (Measure.addHaar : Measure (hermSub X.Ψ d))
    have hp := orb_periodic X hu hG hx
    rw [← he] at hp
    have := (eq_zero_iff _ hD (continuous_orb X hu hc hx) hp).2 fun φ hφ => by
      obtain ⟨χ, h1, rfl⟩ := exists_form_eq X φ
      have h2 := (isFreqZ_iff X χ).2 (he ▸ hφ)
      rw [coeff_eq_cubeCoeff e hD hp hφ, ← hfz u χ h1 h2, h χ h1 h2 x hx]
    have h0 := congrFun this 0
    rwa [orb, Submodule.coe_zero, Zb_zero] at h0

theorem orb_add_lineMap {u : Fin d → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (G : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (a : Fin d → E) (b : hermSub X.Ψ d) (s : X.Ψ → ℝ) :
    orb X u G x (b + lineMap X (embC X a) s) =
      G (X.flow (∑ i, a i • u i) (fun τ => (s τ : ℂ)) (Zb X u b.1 x)) := by
  rw [orb_add X hu, flow_eq_Zb]; rfl

theorem orb_fj {u : Fin d → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0) (la : Wt X.Ψ r)
    (a : Fin d → E) {ν : X.Ψ → ℝ} (hν : ∀ p ∈ X.periods la, ∃ k : ℤ, nuForm X ν p = k)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    orb X u (X.fj la (∑ i, a i • u i) ν P) x =
      partialCoeff volume (PeriodLatticeCountable.fd_exists X la).choose (lineMap X (embC X a)) (orb X u P x)
        (nuForm X ν) := by
  funext b
  have hν' : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k := hν
  rw [orb, Data.fj, if_pos hν', dif_pos (PeriodLatticeCountable.fd_exists X la), partialCoeff, coeff_eq]
  simp only [orb_add_lineMap X hu, nuForm_apply]
  congr 2
  funext s
  congr 2
  push_cast
  ring

end Torus

section Main

variable (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P)
  (hχ : ∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
    Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1)

include hP hχ

theorem fj_spec {u : Fin d → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (hmem : ∀ i, u i ∈ X.Λ) {a : Fin d → E} (ha : ∑ i, a i • u i ∈ X.Λ) (ν : X.Ψ → ℝ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    (∀ χ, fz X.toData u X.g χ (X.fj la (∑ i, a i • u i) ν P) x =
      if ∀ τ, (chiAt X.toData χ (embC X.toData a) τ).re = ν τ then fz X.toData u X.g χ P x
      else 0) ∧
    ((∀ b, IsHerm b → X.fj la (∑ i, a i • u i) ν P (Zb X.toData u b x) = 0) ↔
      ∀ χ, IsHerm χ → IsFreqZ X.toData X.g χ →
        (∀ τ, (chiAt X.toData χ (embC X.toData a) τ).re = ν τ) → fz X.toData u X.g χ P x = 0) := by
  obtain ⟨e, he, hfz⟩ := exists_fz_eq (d := d) X.toData X.g_pos
  obtain ⟨-, hD, h0, h1⟩ := (PeriodLatticeCountable.fd_exists X.toData la).choose_spec
  have hp := orb_periodic X.toData hu (LZ_periodic X u hu hmem la P hP hχ) hx
  rw [← he] at hp
  obtain ⟨H₁, H₂, -⟩ := partialCoeff_spec_cube e hD h0.ne' h1.ne (lineMap X.toData (embC X.toData a))
    (continuous_orb X.toData hu hP.1.continuousOn hx)
    (fun i => hp _ (Submodule.subset_span ⟨i, rfl⟩)) (fun l hl b => by
      rw [orb_add_lineMap X.toData hu]
      exact TransvectionPeriodicity.sec_periodic X.toData la P hP ha (herm_comb_self hu a) hl _
        (Zb_dom X.toData u hu _ b.2 hx))
  have hfreq : ∀ χ, IsFreqZ X.toData X.g χ ↔ ∀ i, ∃ k : ℤ, form X.toData χ (e i) = k := fun χ => by
    rw [isFreqZ_iff, ← he, integral_span_iff]
  by_cases hν : ∀ p ∈ X.periods la, ∃ k : ℤ, nuForm X.toData ν p = k
  · obtain ⟨-, -, A, B⟩ := H₁ _ hν
    rw [← orb_fj X.toData hu la a hν] at A B
    refine ⟨fun χ => ?_, ?_⟩
    · by_cases h : IsHerm χ ∧ IsFreqZ X.toData X.g χ
      · rw [hfz u χ h.1 h.2, hfz u χ h.1 h.2, A _ ((hfreq χ).1 h.2)]
        simp only [form_comp_eq_iff]
      · simp [fz_of_not X.toData h]
    · have : (∀ b, IsHerm b → X.fj la (∑ i, a i • u i) ν P (Zb X.toData u b x) = 0) ↔
          orb X.toData u (X.fj la (∑ i, a i • u i) ν P) x = 0 :=
        ⟨fun h => funext fun b => h b.1 b.2, fun h b hb => congrFun h ⟨b, hb⟩⟩
      rw [this, B]
      constructor
      · intro h χ h1 h2 h3
        rw [hfz u χ h1 h2]
        exact h _ ((hfreq χ).1 h2) ((form_comp_eq_iff _ _ _ _).2 h3)
      · intro h φ h2 h3
        obtain ⟨χ, h1, rfl⟩ := exists_form_eq X.toData φ
        rw [← hfz u χ h1 ((hfreq χ).2 h2)]
        exact h χ h1 ((hfreq χ).2 h2) ((form_comp_eq_iff _ _ _ _).1 h3)
  · have hfj : X.fj la (∑ i, a i • u i) ν P = fun _ => 0 := funext fun y => by
      have hν' : ¬ ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k := hν
      rw [Data.fj, if_neg hν']
    have hz : ∀ χ, IsHerm χ → IsFreqZ X.toData X.g χ →
        (∀ τ, (chiAt X.toData χ (embC X.toData a) τ).re = ν τ) → fz X.toData u X.g χ P x = 0 := by
      intro χ h1 h2 h3
      rw [hfz u χ h1 h2]
      refine H₂ _ ((hfreq χ).1 h2) fun h => hν fun p hp => ?_
      rw [← (form_comp_eq_iff _ _ _ _).2 h3]
      exact h p hp
    refine ⟨fun χ => ?_, ⟨fun _ => hz, fun _ b _ => by rw [hfj]⟩⟩
    by_cases h : IsHerm χ ∧ IsFreqZ X.toData X.g χ
    · rw [hfj, hfz u χ h.1 h.2]
      have : cubeCoeff e (orb X.toData u (fun _ => 0) x) (form X.toData χ) = 0 := by
        simp [cubeCoeff, orb]
      rw [this]
      split_ifs with h3
      · exact (hz χ h.1 h.2 h3).symm
      · rfl
    · simp [fz_of_not X.toData h]

theorem fj_eq_zero_iff {u : Fin d → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (hmem : ∀ i, u i ∈ X.Λ) {a : Fin d → E} (ha : ∑ i, a i • u i ∈ X.Λ) (ν : X.Ψ → ℝ) :
    (∀ x ∈ X.dom, X.fj la (∑ i, a i • u i) ν P x = 0) ↔
      ∀ χ, IsHerm χ → IsFreqZ X.toData X.g χ →
        (∀ τ, (chiAt X.toData χ (embC X.toData a) τ).re = ν τ) →
          ∀ x ∈ X.dom, fz X.toData u X.g χ P x = 0 := by
  constructor
  · intro h χ h1 h2 h3 x hx
    exact (fj_spec X la P hP hχ hu hmem ha ν hx).2.1
      (fun b hb => h _ (Zb_dom X.toData u hu b hb hx)) χ h1 h2 h3
  · intro h x hx
    have := (fj_spec X la P hP hχ hu hmem ha ν hx).2.2 (fun χ h1 h2 h3 => h χ h1 h2 h3 x hx) 0
      (hermSub X.Ψ d).zero_mem
    rwa [Zb_zero] at this

theorem forall_fj_eq_zero_iff (S : Set (X.Ψ → ℝ)) :
    (∀ ξ, X.IsIso ξ → ∀ ν ∈ S, ∀ x ∈ X.dom, X.fj la ξ ν P x = 0) ↔
      ∀ (d : ℕ) (u : Fin d → Fin r → E), IsMaximal X.toData u →
        ∀ χ, IsHerm χ → IsFreqZ X.toData X.g χ →
          (∃ a : Fin d → E, ∑ i, a i • u i ∈ X.Λ ∧ ∑ i, a i • u i ≠ 0 ∧
            (fun τ => (chiAt X.toData χ (embC X.toData a) τ).re) ∈ S) →
          ∀ x ∈ X.dom, fz X.toData u X.g χ P x = 0 := by
  constructor
  · rintro h d u hu χ h1 h2 ⟨a, ha, ha0, hS⟩
    exact (fj_eq_zero_iff X la P hP hχ hu.1.1 hu.2.1 ha _).1
      (h _ ⟨ha, herm_comb_self hu.1.1 a, ha0⟩ _ hS) χ h1 h2 fun _ => rfl
  · intro h ξ hξ ν hν
    obtain ⟨d, u, hu, hm⟩ := exists_isMaximal_mem_span X.toData hξ.2.1
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hm
    exact (fj_eq_zero_iff X la P hP hχ hu.1.1 hu.2.1 hξ.1 ν).2 fun χ h1 h2 h3 =>
      h d u hu χ h1 h2 ⟨a, hξ.1, hξ.2.2, by rw [funext h3]; exact hν⟩

theorem maximalCusps :
    (∀ ξ, X.IsIso ξ → ∃ (d : ℕ) (u : Fin d → Fin r → E), IsMaximal X.toData u ∧
      ξ ∈ Submodule.span E (Set.range u)) ∧
    (∀ c : ℝ, (∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∑ τ, ν τ ≤ c → ∀ x ∈ X.dom, X.fj la ξ ν P x = 0) ↔
      ∀ (d : ℕ) (u : Fin d → Fin r → E), IsMaximal X.toData u →
        ∀ χ, IsHerm χ → IsFreqZ X.toData X.g χ →
          (∃ a : Fin d → E, ∑ i, a i • u i ∈ X.Λ ∧ ∑ i, a i • u i ≠ 0 ∧
            ∑ τ, (chiAt X.toData χ (embC X.toData a) τ).re ≤ c) →
          ∀ x ∈ X.dom, fz X.toData u X.g χ P x = 0) ∧
    (∃ (d : ℕ) (u : Fin d → Fin r → E), IsMaximal X.toData u) ∧
    ∀ (d : ℕ) (u : Fin d → Fin r → E), IsMaximal X.toData u →
      ((∀ x ∈ X.dom, P x = 0) ↔
        ∀ χ, IsHerm χ → IsFreqZ X.toData X.g χ → ∀ x ∈ X.dom, fz X.toData u X.g χ P x = 0) :=
  ⟨fun _ hξ => exists_isMaximal_mem_span X.toData hξ.2.1,
    fun c => forall_fj_eq_zero_iff X la P hP hχ {ν | ∑ τ, ν τ ≤ c},
    exists_isMaximal X.toData,
    fun _ u hu => eq_zero_iff_fz X.toData hu.1.1 X.g_pos hP.1.continuousOn
      (LZ_periodic X u hu.1.1 hu.2.1 la P hP hχ)⟩

theorem mem_SSgt_iff (c : ℝ) : P ∈ X.SSgt la c ↔ P ∈ X.SS la ∧
    ∀ (d : ℕ) (u : Fin d → Fin r → E), IsMaximal X.toData u →
      ∀ χ, IsHerm χ → IsFreqZ X.toData X.g χ →
        (∃ a : Fin d → E, ∑ i, a i • u i ∈ X.Λ ∧ ∑ i, a i • u i ≠ 0 ∧
          ∑ τ, (chiAt X.toData χ (embC X.toData a) τ).re ≤ c) →
        ∀ x ∈ X.dom, fz X.toData u X.g χ P x = 0 :=
  and_congr_right' ((maximalCusps X la P hP hχ).2.1 c)

end Main

end

end GlobalTheory.MaxCusp
