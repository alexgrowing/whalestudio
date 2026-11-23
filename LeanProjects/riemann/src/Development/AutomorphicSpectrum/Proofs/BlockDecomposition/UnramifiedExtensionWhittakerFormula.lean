import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdEqZeroOfModulusEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantSeparatingSubalgebraStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.InertAsm.Decomp

section Gen

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem exists_scale {S : Set K} (hS : IsCompact S) : ∃ s : Kˣ, ∀ x ∈ S, x * (s : K) ∈ 𝒪[K] := by
  set π : K := (unifUnit K : K) with hπ
  have hm : modulus π < 1 := by
    rw [hπ, modulus_of_ne_zero (unifUnit K).ne_zero, ord_unifUnit, _root_.zpow_neg, zpow_one]
    exact inv_lt_one_of_one_lt₀ (one_lt_residueCard_nnreal (K := K))
  have hπO : π ∈ 𝒪[K] := modulus_le_one_iff.1 hm.le
  have hpow : ∀ n : ℕ, modulus (π ^ n) = modulus π ^ n := by
    intro n
    induction n with
    | zero => simp [modulus_one]
    | succ n ih => rw [pow_succ, modulus_mul, ih, pow_succ]
  let U : ℕ → Set K := fun n => {x | x * π ^ n ∈ 𝒪[K]}
  have ho : IsOpen (𝒪[K] : Set K) := Valuation.isOpen_integer
  have hUo : ∀ n, IsOpen (U n) := fun n => ho.preimage (continuous_mul_right _)
  have hcov : S ⊆ ⋃ n, U n := by
    intro x _
    refine Set.mem_iUnion.2 ?_
    by_cases hx : x = 0
    · exact ⟨0, by simp [U, hx, zero_mem]⟩
    have hmx : 0 < modulus x := pos_iff_ne_zero.2 (modulus_ne_zero hx)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hmx) hm
    refine ⟨n, modulus_le_one_iff.1 ?_⟩
    rw [modulus_mul, hpow]
    calc modulus x * modulus π ^ n ≤ modulus x * (modulus x)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hmx.ne'
  have hmono : Monotone U := monotone_nat_of_le_succ fun n x hx => by
    have h : x * π ^ (n + 1) = (x * π ^ n) * π := by rw [pow_succ, mul_assoc]
    show x * π ^ (n + 1) ∈ 𝒪[K]
    rw [h]
    exact mul_mem hx hπO
  obtain ⟨n, hn⟩ := hS.elim_directed_cover U hUo hcov hmono.directed_le
  refine ⟨unifUnit K ^ n, fun x hx => ?_⟩
  rw [Units.val_pow_eq_pow_val]
  exact hn hx

theorem isLocallyConstant_char {χ : AddChar K Circle} (hχ : IsStd χ) :
    IsLocallyConstant (χ : K → Circle) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun a => ?_
  have h := isTrivialOn_addCharConductor hχ.1 hχ.2.1
  have ho : IsOpen {y : K | y - a ∈ valBall K (addCharConductor χ)} :=
    (isOpen_valBall (addCharConductor χ)).preimage (continuous_id.sub continuous_const)
  filter_upwards [ho.mem_nhds (show a - a ∈ valBall K (addCharConductor χ) by
    rw [sub_self]; exact zero_mem _)] with y hy
  have h1 : χ (y - a) = 1 := h _ hy
  calc χ y = χ ((y - a) + a) := by rw [sub_add_cancel]
    _ = χ a := by rw [AddChar.map_add_eq_mul, h1, one_mul]

end Gen

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)]

open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep (modulus_norm)

theorem eq_of_norm_eq {c : Eˣ →* ℂˣ} (hc : IsUnramifiedChar c) {Φ : E → ℂ}
    (hΦ : Φ ∈ GL2LocalData.SBc F E c) {p q : E} (h : Algebra.norm F p = Algebra.norm F q) : Φ p = Φ q := by
  have hz : ∀ {x : E}, Algebra.norm F x = 0 → x = 0 := fun hx => Algebra.norm_eq_zero_iff.1 hx
  have hz0 : Algebra.norm F (0 : E) = 0 := Algebra.norm_eq_zero_iff.2 rfl
  by_cases hp : p = 0
  · subst hp
    rw [hz (h.symm.trans hz0)]
  have hq : q ≠ 0 := fun hq => hp (hz (by rw [h, hq, hz0]))
  have hNp : Algebra.norm F p ≠ 0 := Algebra.norm_ne_zero_iff.2 hp
  let u : Eˣ := Units.mk0 (q / p) (div_ne_zero hq hp)
  have hu : Algebra.norm F (u : E) = 1 := by
    refine mul_right_cancel₀ hNp ?_
    rw [one_mul, ← map_mul, h]
    simp only [u, Units.val_mk0, div_mul_cancel₀ q hp]
  have hm : modulus (u : E) = 1 := by
    rw [← modulus_norm (K := F), hu, modulus_one]
  have h1 : c u = 1 := by
    have := char_congr c hc (u := u) (v := 1) (by simpa using hm)
    simpa using this
  have h2 := hΦ.2.2 u hu p
  rw [h1, inv_one, Units.val_one, one_mul] at h2
  rw [← h2]
  simp only [u, Units.val_mk0, mul_div_cancel₀ q hp]

theorem sub_eq_neg_smul_add_of_sub_smul_eq (χ : AddChar F Circle) (hχ : IsStd χ) (c : Eˣ →* ℂˣ) (hc : IsUnramifiedChar c)
    (Φ : E → ℂ) (hΦ : Φ ∈ GL2LocalData.SBc F E c) :
    ∃ (s : Eˣ) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → F), ∀ x, Φ x =
      ∑ j, a j * ((χ (y j * Algebra.norm F x) : ℂ) * intInd (x * (s : E))) := by
  obtain ⟨s, hs⟩ := exists_scale (K := E) hΦ.2.1
  let Bs : Set E := {x | x * (s : E) ∈ 𝒪[E]}
  have hO : IsCompact (𝒪[E] : Set E) := IsNonarchimedeanLocalField.isCompact_closedBall E 1
  have hBc : IsCompact Bs :=
    (Homeomorph.mulRight₀ (s : E) s.ne_zero).isCompact_preimage.2 hO
  haveI : CompactSpace Bs := isCompact_iff_compactSpace.1 hBc
  let e : F → Bs → ℂ := fun y x => (χ (y * Algebra.norm F (x : E)) : ℂ)
  let V : Submodule ℂ (Bs → ℂ) := Submodule.span ℂ (Set.range e)
  have hone : (1 : Bs → ℂ) ∈ V := Submodule.subset_span ⟨0, by funext x; simp [e]⟩
  have hemul : ∀ y y', e y * e y' = e (y + y') := fun y y' => by
    funext x
    simp [e, add_mul, AddChar.map_add_eq_mul]
  have hmul : ∀ f ∈ V, ∀ g ∈ V, f * g ∈ V := by
    intro f hf g hg
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨y, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨y', rfl⟩ := hg
        rw [hemul]
        exact Submodule.subset_span ⟨_, rfl⟩
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact V.add_mem ha hb
      | smul t a _ ha => rw [mul_smul_comm]; exact V.smul_mem _ ha
    | zero => simp
    | add a b _ _ ha hb => rw [add_mul]; exact V.add_mem ha hb
    | smul t a _ ha => rw [smul_mul_assoc]; exact V.smul_mem _ ha
  have hNc : Continuous (Algebra.norm F : E → F) := GroundTheory.LocalField.continuous_algebraNorm F E
  have hlc : ∀ f ∈ V, IsLocallyConstant f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨y, rfl⟩ := hf
      have hcont : Continuous fun x : Bs => y * Algebra.norm F (x : E) :=
        continuous_const.mul (hNc.comp continuous_subtype_val)
      exact ((isLocallyConstant_char hχ).comp_continuous hcont).comp (fun z : Circle => (z : ℂ))
    | zero => exact IsLocallyConstant.const 0
    | add a b _ _ ha hb => exact ha.add hb
    | smul t a _ ha => exact (IsLocallyConstant.const t).mul ha
  have hsep : ∀ p q : Bs, Φ p ≠ Φ q → ∃ f ∈ V, f p ≠ f q := by
    intro p q hpq
    have hd : Algebra.norm F (p : E) - Algebra.norm F (q : E) ≠ 0 := fun h =>
      hpq (eq_of_norm_eq hc hΦ (sub_eq_zero.1 h))
    obtain ⟨t, ht⟩ : ∃ t, χ t ≠ 1 := by
      by_contra hall
      push_neg at hall
      exact hχ.2.1 (by ext x; simp [hall x])
    set d := Algebra.norm F (p : E) - Algebra.norm F (q : E) with hdd
    refine ⟨e (t / d), Submodule.subset_span ⟨_, rfl⟩, fun h => ht ?_⟩
    have h1 : χ (t / d * Algebra.norm F (p : E)) = χ (t / d * Algebra.norm F (q : E)) :=
      Circle.coe_injective h
    have h2 : t / d * Algebra.norm F (p : E) = t + t / d * Algebra.norm F (q : E) := by
      have : t = t / d * d := (div_mul_cancel₀ t hd).symm
      rw [hdd] at this ⊢
      linear_combination (-1 : F) * this
    rw [h2, AddChar.map_add_eq_mul] at h1
    exact mul_right_cancel (h1.trans (one_mul _).symm)
  have hmem : (fun x : Bs => Φ x) ∈ V :=
    GlobalTheory.T.locally_constant_separating_subalgebra Bs V hone hmul hlc (fun x : Bs => Φ x)
      (hΦ.1.comp_continuous continuous_subtype_val) hsep
  obtain ⟨w, hw⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  let eq := w.support.equivFin
  refine ⟨s, w.support.card, fun j => w (eq.symm j), fun j => (eq.symm j : F), fun x => ?_⟩
  by_cases hx : x * (s : E) ∈ 𝒪[E]
  · have h1 : Φ x = (w.sum fun i a => a • e i) ⟨x, hx⟩ := by rw [hw]
    have h2 : (intInd (x * (s : E)) : ℂ) = 1 := by simp [intInd, hx]
    rw [h1, Finsupp.sum, Finset.sum_apply, ← Finset.sum_coe_sort w.support,
      ← Equiv.sum_comp eq.symm]
    simp [e, h2]
  · have h0 : Φ x = 0 := by
      by_contra h
      exact hx (hs x (subset_tsupport _ h))
    have h2 : (intInd (x * (s : E)) : ℂ) = 0 := by simp [intInd, hx]
    simp [h0, h2]

end Main

theorem sbc_decomp : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ χ : AddChar F Circle, Ad3.IsStd χ → ∀ c : Eˣ →* ℂˣ, IsUnramifiedChar c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∃ (s : Eˣ) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → F), ∀ x, Φ x = ∑ j, a j * ((χ (y j * Algebra.norm F x) : ℂ) * intInd (x * (s : E))) := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ h2 _ _ χ hχ c hc Φ hΦ
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact sub_eq_neg_smul_add_of_sub_smul_eq χ hχ c hc Φ hΦ

end GlobalTheory.CompanionTheory.SphTheta.InertAsm.Decomp
