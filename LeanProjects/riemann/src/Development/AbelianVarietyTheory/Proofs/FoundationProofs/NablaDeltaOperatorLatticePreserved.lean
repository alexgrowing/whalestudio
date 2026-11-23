import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StdWeylLatticesFgAndSpanCoeffSpaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientSStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsTer
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TransLattice

section General

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem_of_mem_span (T : Submodule (𝓞 K) V) {x : V} (hx : x ∈ Submodule.span K (T : Set V)) :
    ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ T := by
  first
  | exact @_root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span ..)

theorem exists_smul_mem_of_fg (T A : Submodule (𝓞 K) V) (hA : A.FG)
    (hx : ∀ x ∈ A, x ∈ Submodule.span K (T : Set V)) :
    ∃ s : 𝓞 K, s ≠ 0 ∧ ∀ x ∈ A, s • x ∈ T := by
  classical
  obtain ⟨G, rfl⟩ := hA
  have h1 : ∀ x : G, ∃ s : 𝓞 K, s ≠ 0 ∧ s • (x : V) ∈ T := fun x =>
    exists_smul_mem_of_mem_span T (hx x (Submodule.subset_span x.2))
  choose s hs hsT using h1
  refine ⟨∏ x, s x, Finset.prod_ne_zero_iff.mpr fun x _ => hs x, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : G)), mul_smul]
    exact T.smul_mem _ (hsT ⟨x, hx⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact T.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact T.smul_mem _ hx

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem mem_of_forall_mem_locP (T : Submodule (𝓞 K) V) {x : V}
    (hx : ∀ w : HeightOneSpectrum (𝓞 K), x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T) : x ∈ T := by
  let I : Ideal (𝓞 K) := T.comap (LinearMap.toSpanSingleton (𝓞 K) V x)
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
    obtain ⟨s, hs, hsx⟩ := hx ⟨m, hm.isPrime, hm0⟩
    exact hs (hIm (show s ∈ I from hsx))
  have : (1 : 𝓞 K) ∈ I := by rw [hI]; trivial
  simpa [I] using this

omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem locP_le_of_smul_mem (w : HeightOneSpectrum (𝓞 K)) {A B : Submodule (𝓞 K) V} {t : 𝓞 K}
    (ht : t ∉ w.asIdeal) (h : ∀ x ∈ A, t • x ∈ B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B := by
  rintro x ⟨s, hs, hx⟩
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [mul_smul]
  exact h _ hx

omit [NumberField K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem mul_smul_mem (A : Submodule (𝓞 K) V) (a : 𝓞 K) {b : 𝓞 K} {x : V} (h : b • x ∈ A) : (a * b) • x ∈ A := by
  rw [mul_smul]; exact A.smul_mem _ h

omit [NumberField K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem smul_smul_mem_comm (A : Submodule (𝓞 K) V) {a b : 𝓞 K} {x : V} (h : a • b • x ∈ A) : b • a • x ∈ A := by
  rwa [smul_comm]

end General

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem colLat_one_fg : (colLat (1 : GL (Fin n) K)).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem span_colLat_one : Submodule.span K (colLat (1 : GL (Fin n) K) : Set (Fin n → K)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  refine Submodule.subset_span ⟨j, ?_⟩
  funext a
  simp [Matrix.one_apply, Pi.single_apply]

theorem exists_isBasisAt_one (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    ∃ t : 𝓞 K, t ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 K), t ∉ w.asIdeal → ∀ τ, IsBasisAt w (M τ) 1 := by
  classical
  have h1 : ∀ τ, ∃ s : 𝓞 K, s ≠ 0 ∧ ∀ x ∈ M τ, s • x ∈ colLat (1 : GL (Fin n) K) := fun τ =>
    exists_smul_mem_of_fg _ _ (hM τ).fg fun x _ => by rw [span_colLat_one]; trivial
  have h2 : ∀ τ, ∃ s : 𝓞 K, s ≠ 0 ∧ ∀ x ∈ colLat (1 : GL (Fin n) K), s • x ∈ M τ := fun τ =>
    exists_smul_mem_of_fg _ _ colLat_one_fg fun x _ => by rw [(hM τ).span_eq_top]; trivial
  choose s hs hsM using h1
  choose s' hs' hsM' using h2
  refine ⟨∏ τ, (s τ * s' τ), Finset.prod_ne_zero_iff.mpr fun τ _ => mul_ne_zero (hs τ) (hs' τ), ?_⟩
  intro w hw τ
  have hd : s τ * s' τ ∉ w.asIdeal := fun h =>
    hw (w.asIdeal.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ τ)) h)
  exact le_antisymm
    (locP_le_of_smul_mem w (fun h => hd (w.asIdeal.mul_mem_right _ h)) (hsM τ))
    (locP_le_of_smul_mem w (fun h => hd (w.asIdeal.mul_mem_left _ h)) (hsM' τ))

theorem transLat_fg (hB : BasisAtEx) (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n)) (hT : T.FG)
    (hsp : Submodule.span K (T : Set (Pol K ι n)) = VV K lam)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    (transLat lam T M).FG := by
  classical
  obtain ⟨t, ht, htw⟩ := exists_isBasisAt_one M hM
  have hmem : ∀ F ∈ transLat lam T M, ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K),
      (∀ τ, IsBasisAt w (M τ) (B τ)) → actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T := by
    intro F hF w B hB
    simp only [transLat, Submodule.mem_iInf] at hF
    exact hF w B hB
  have hloc : ∀ w : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ≠ 0 ∧
      ∀ F ∈ transLat lam T M, s • F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T := by
    intro w
    choose B hBw using fun τ => hB K n (M τ) (hM τ) w
    obtain ⟨s, hs, hsT⟩ := exists_smul_mem_of_fg T (T.map ((actP lam B).restrictScalars (𝓞 K))) (hT.map _) (by
      rintro _ ⟨x, hx, rfl⟩
      rw [hsp]
      exact polyAction_mem_VV lam B (hsp ▸ Submodule.subset_span hx))
    refine ⟨s, hs, fun F hF => ?_⟩
    obtain ⟨u, hu, huF⟩ := hmem F hF w B hBw
    refine ⟨u, hu, ?_⟩
    have h := hsT _ ⟨_, huF, rfl⟩
    rw [map_smul, LinearMap.restrictScalars_apply, ← polyAction_mul, mul_inv_cancel, polyAction_one₂] at h
    exact smul_smul_mem_comm T h
  choose s hs hsF using hloc
  have hfin : {w : HeightOneSpectrum (𝓞 K) | w.asIdeal ∣ Ideal.span {t}}.Finite :=
    Ideal.finite_factors (by simpa using ht)
  set c : 𝓞 K := ∏ w ∈ hfin.toFinset, s w with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hs w
  have hcT : ∀ F ∈ transLat lam T M, c • F ∈ T := by
    intro F hF
    refine mem_of_forall_mem_locP T fun w => ?_
    by_cases hw : t ∈ w.asIdeal
    · have hw' : w ∈ hfin.toFinset := by
        simpa [Ideal.dvd_span_singleton] using hw
      rw [hc, ← Finset.prod_erase_mul _ _ hw']
      exact mul_smul_mem _ _ (hsF w F hF)
    · have h := hmem F hF w 1 (htw w hw)
      rw [inv_one, polyAction_one₂] at h
      exact Submodule.smul_mem _ _ h
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 K) (Pol K ι n) c) := by
    intro x y hxy
    have h : algebraMap (𝓞 K) K c • x = algebraMap (𝓞 K) K c • y := by
      rw [algebraMap_smul, algebraMap_smul]; exact hxy
    refine smul_right_injective _ ?_ h
    intro h0
    exact hc0 ((IsFractionRing.injective (𝓞 K) K) (by rw [h0, map_zero]))
  refine Submodule.fg_of_fg_map_injective _ hinj (hT.of_le ?_)
  rintro _ ⟨F, hF, rfl⟩
  exact hcT F hF

theorem transLat_isLattice (hB : BasisAtEx) (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n)) (hT : T.FG)
    (hsp : Submodule.span K (T : Set (Pol K ι n)) = VV K lam)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ))
    (hloc : ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (transLat lam T M) =
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T).map ((actP lam B).restrictScalars (𝓞 K))) :
    Submodule.IsLattice K ((transLat lam T M).comap ((VV K lam).subtype.restrictScalars (𝓞 K))) where
  fg := by
    refine Submodule.fg_of_fg_map_injective ((VV K lam).subtype.restrictScalars (𝓞 K)) Subtype.val_injective ?_
    exact (transLat_fg hB lam T hT hsp M hM).of_le (Submodule.map_comap_le _ _)
  span_eq_top := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
    let w : HeightOneSpectrum (𝓞 K) :=
      ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩
    choose B hBw using fun τ => hB K n (M τ) (hM τ) w
    rw [eq_top_iff]
    rintro x -
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem_of_mem_span T (x := actP lam B⁻¹ x.1)
      (by rw [hsp]; exact polyAction_mem_VV lam B⁻¹ x.2)
    have h1 : s • x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (transLat lam T M) := by
      rw [hloc w B hBw]
      refine ⟨_, ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hsx⟩, ?_⟩
      rw [map_smul, LinearMap.restrictScalars_apply, ← polyAction_mul, mul_inv_cancel, polyAction_one₂]
    obtain ⟨u, hu, hux⟩ := h1
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hu w.asIdeal.zero_mem
    have hne : algebraMap (𝓞 K) K (u * s) ≠ 0 := fun h0 =>
      mul_ne_zero hu0 hs ((IsFractionRing.injective (𝓞 K) K) (by rw [h0, map_zero]))
    have h2 : algebraMap (𝓞 K) K (u * s) • x ∈
        (transLat lam T M).comap ((VV K lam).subtype.restrictScalars (𝓞 K)) := by
      show algebraMap (𝓞 K) K (u * s) • x.1 ∈ transLat lam T M
      rw [algebraMap_smul, mul_smul]
      exact hux
    rw [← Submodule.smul_mem_iff _ hne]
    exact Submodule.subset_span h2

theorem nabDelLattice : NabDelLattice := by
  intro K _ _ ι _ n lam M hM
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.stdWeylLattices_fg_and_span_coeffSpace K ι n lam
  exact ⟨transLat_isLattice GlobalTheory.T.lattice_has_basis_at_every_finite_place lam _ h1 h3 M hM
      fun w B hB => (GlobalTheory.T.transportedLattice_localization_free_le_coefficientSpace.1 K ι n lam M hM w B hB).1,
    transLat_isLattice GlobalTheory.T.lattice_has_basis_at_every_finite_place lam _ h2 h4 M hM
      fun w B hB => (GlobalTheory.T.transportedLattice_localization_free_le_coefficientSpace.1 K ι n lam M hM w B hB).2⟩

end GlobalTheory.TransLattice
