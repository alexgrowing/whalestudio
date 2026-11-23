import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Lemmata.GeneralBFactSecondBisAlt.Imports

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.L2.Col

section Basic

variable {K : Type} [Field K] [NumberField K] {W : Type} [AddCommGroup W] [Module (𝓞 K) W]

theorem lc_mem_locP (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ L := Iff.rfl

theorem lc_one_notMem (w : HeightOneSpectrum (𝓞 K)) : (1 : 𝓞 K) ∉ w.asIdeal :=
  fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem lc_mul_notMem (w : HeightOneSpectrum (𝓞 K)) {s t : 𝓞 K} (hs : s ∉ w.asIdeal) (ht : t ∉ w.asIdeal) :
    s * t ∉ w.asIdeal := fun h => (w.isPrime.mem_or_mem h).elim hs ht

theorem lc_ne_zero_of_notMem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) : s ≠ 0 :=
  fun h => hs (h ▸ w.asIdeal.zero_mem)

theorem lc_le_locP (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) W) : L ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L :=
  fun x hx => (lc_mem_locP w L x).2 ⟨1, lc_one_notMem w, by simpa using hx⟩

theorem localized_localized (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) W) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by
  refine le_antisymm ?_ (lc_le_locP w _)
  rintro x ⟨s, hs, t, ht, hx⟩
  exact ⟨t * s, lc_mul_notMem w ht hs, by rwa [mul_smul]⟩

theorem smul_mem_localized_iff (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) W) {s : 𝓞 K} (hs : s ∉ w.asIdeal)
    (x : W) : s • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by
  constructor
  · rintro ⟨t, ht, hx⟩
    exact ⟨t * s, lc_mul_notMem w ht hs, by rwa [mul_smul]⟩
  · exact fun hx => Submodule.smul_mem _ s hx

theorem lc_le_of_le_locP {A B : Submodule (𝓞 K) W}
    (h : ∀ w : HeightOneSpectrum (𝓞 K), A ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) : A ≤ B := by
  intro x hx
  let I : Ideal (𝓞 K) := B.colon {x}
  by_contra hxB
  have hI : I ≠ ⊤ := by
    intro hI
    have h1 : (1 : 𝓞 K) ∈ I := by rw [hI]; trivial
    rw [Submodule.mem_colon_singleton] at h1
    exact hxB (by simpa using h1)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsx⟩ := h ((plEquiv K).symm ⟨m, hm⟩) hx
  exact hs (hIm (Submodule.mem_colon_singleton.2 hsx))

theorem le_of_forall_localized_le {A B : Submodule (𝓞 K) W}
    (h : ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) : A ≤ B :=
  lc_le_of_le_locP fun w => (lc_le_locP w A).trans (h w)

theorem eq_of_forall_localized_eq {A B : Submodule (𝓞 K) W}
    (h : ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) : A = B :=
  le_antisymm (le_of_forall_localized_le fun w => (h w).le) (le_of_forall_localized_le fun w => (h w).ge)

theorem lc_iInf_locP (T : Submodule (𝓞 K) W) :
    ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T = T :=
  le_antisymm (lc_le_of_le_locP fun w => iInf_le _ w) (le_iInf fun w => lc_le_locP w T)

end Basic

section BasisAt

variable {K : Type} [Field K] [NumberField K]

section Gen

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_localized_iff_mem_baseChange (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L ↔ x ∈ atW w L := mem_atW_iff.symm

theorem localized_eq_of_baseChange_eq (w : HeightOneSpectrum (𝓞 K)) {A B : Submodule (𝓞 K) V} (h : atW w A = atW w B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B := by
  rw [← atW_restrictScalars, ← atW_restrictScalars, h]

theorem lc_atW_span (w : HeightOneSpectrum (𝓞 K)) (S : Set V) :
    atW w (Submodule.span (𝓞 K) S) = Submodule.span (Ow w) S :=
  Submodule.span_span_of_tower (𝓞 K) (Ow w) S

theorem lc_exists_basis (w : HeightOneSpectrum (𝓞 K)) {A : Submodule (𝓞 K) V} (hfg : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    ∃ (κ : Type) (_ : Fintype κ) (bK : Module.Basis κ K V),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range bK)) := by
  obtain ⟨κ, hκ, b, bK, hb⟩ := exists_basis_atW w hfg hsp
  refine ⟨κ, hκ, bK, localized_eq_of_baseChange_eq w ?_⟩
  rw [lc_atW_span]
  have h1 : Set.range bK = (atW w A).subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact hb i
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end Gen

theorem latticeBasisExists_holds : BasisAtEx := by
  intro K _ _ n M hM w
  obtain ⟨κ, hκ, bK, hb⟩ := lc_exists_basis w hM.fg hM.span_eq_top
  have hcard : Fintype.card κ = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b' : Module.Basis (Fin n) K (Fin n → K) := bK.reindex e
  let B : GL (Fin n) K :=
    ⟨(Pi.basisFun K (Fin n)).toMatrix b', b'.toMatrix (Pi.basisFun K (Fin n)),
      Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  refine ⟨B, ?_⟩
  unfold IsBasisAt
  rw [hb]
  congr 2
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨e i, ?_⟩
    funext a
    show (Pi.basisFun K (Fin n)).toMatrix b' a (e i) = bK i a
    simp [Module.Basis.toMatrix_apply, b']
  · rintro ⟨j, rfl⟩
    refine ⟨e.symm j, ?_⟩
    funext a
    show bK (e.symm j) a = (Pi.basisFun K (Fin n)).toMatrix b' a j
    simp [Module.Basis.toMatrix_apply, b']

end BasisAt

section PrimeTo

variable {K : Type} [Field K] [NumberField K]

theorem lc_primeTo (d : 𝓞 K) (hd : d ≠ 0) (w : HeightOneSpectrum (𝓞 K)) :
    ∃ t : 𝓞 K, t ∉ w.asIdeal ∧
      ∀ w' : HeightOneSpectrum (𝓞 K), w' ≠ w → ∃ r : 𝓞 K, r ∉ w'.asIdeal ∧ d ∣ r * t := by
  have hfin : FiniteMultiplicity w.asIdeal (Ideal.span {d}) := by
    refine FiniteMultiplicity.of_not_isUnit ?_ ?_
    · rw [Ideal.isUnit_iff]
      exact w.isPrime.ne_top
    · simpa using hd
  obtain ⟨I, hI, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have h1 : ¬ I ≤ w.asIdeal := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htI, htw⟩ := SetLike.not_le_iff_exists.1 h1
  refine ⟨t, htw, fun w' hw' => ?_⟩
  have h2 : ¬ w.asIdeal ^ multiplicity w.asIdeal (Ideal.span {d}) ≤ w'.asIdeal := by
    intro h
    have h3 : w.asIdeal ≤ w'.asIdeal := w'.isPrime.le_of_pow_le h
    exact hw' (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h3).symm)
  obtain ⟨r, hr, hrw⟩ := SetLike.not_le_iff_exists.1 h2
  refine ⟨r, hrw, ?_⟩
  have h4 : r * t ∈ Ideal.span {d} := by
    rw [hI]
    exact Ideal.mul_mem_mul hr htI
  exact Ideal.mem_span_singleton.1 h4

end PrimeTo

section Sandwich

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem lc_mem_one_iff (x : K) : x ∈ (1 : Submodule (𝓞 K) K) ↔ ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = x :=
  Submodule.mem_one

theorem lc_mem_colLat_one (x : Fin n → K) :
    x ∈ colLat (1 : GL (Fin n) K) ↔ ∀ a, x a ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro hx a
    unfold colLat at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs
      · exact Submodule.one_le.1 le_rfl
      · exact zero_mem _
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul r y _ hy => exact Submodule.smul_mem _ r hy
  · intro hx
    choose r hr using fun a => (lc_mem_one_iff (x a)).1 (hx a)
    have e : x = ∑ j : Fin n, r j • (fun a : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j) := by
      funext a
      rw [Finset.sum_apply, Finset.sum_eq_single a]
      · simp [Algebra.smul_def, hr]
      · intro b _ hb
        simp [Matrix.one_apply, Ne.symm hb]
      · simp
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem lc_colLat_eq_gLat (B : GL (Fin n) K) : colLat B = gLat B (colLat 1) := by
  rw [← colLat_mul, mul_one]

theorem lc_mem_gLat (g : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) (x : Fin n → K) :
    x ∈ gLat g M ↔ ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ M := by
  unfold gLat
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨_, hx, by simp⟩

theorem lc_mem_colLat (B : GL (Fin n) K) (x : Fin n → K) :
    x ∈ colLat B ↔ ∀ a, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) a ∈ (1 : Submodule (𝓞 K) K) := by
  rw [lc_colLat_eq_gLat, lc_mem_gLat, lc_mem_colLat_one]

theorem lc_col_mem_colLat (B : GL (Fin n) K) (j : Fin n) :
    (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) ∈ colLat B := Submodule.subset_span ⟨j, rfl⟩

section Gen

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem lc_exists_smul_mem (M : Submodule (𝓞 K) V) {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  first | exact Bl.general_b_fact_second''''''''.goal1 .. | (apply Bl.general_b_fact_second''''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second''''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''''.goal1 <;> first | assumption | infer_instance)

end Gen

theorem lc_sandwich (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ (∀ x ∈ M, d • x ∈ colLat (1 : GL (Fin n) K)) ∧
      (∀ x ∈ colLat (1 : GL (Fin n) K), d • x ∈ M) := by
  classical

  obtain ⟨S, hS⟩ := hM.fg
  obtain ⟨d1, hd1⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (S.biUnion fun x => Finset.univ.image fun a : Fin n => x a)
  have h1 : ∀ x ∈ M, (d1 : 𝓞 K) • x ∈ colLat (1 : GL (Fin n) K) := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rw [lc_mem_colLat_one]
      intro a
      obtain ⟨r, hr⟩ := hd1 (y a) (Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩)
      exact (lc_mem_one_iff _).2 ⟨r, hr⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ r hy

  have h2 : ∀ j : Fin n, ∃ d : 𝓞 K, d ≠ 0 ∧
      d • (fun a : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j) ∈ M := fun j =>
    lc_exists_smul_mem M (by rw [hM.span_eq_top]; trivial)
  choose e he hem using h2
  have h3 : ∀ x ∈ colLat (1 : GL (Fin n) K), (∏ j, e j) • x ∈ M := by
    intro x hx
    unfold colLat at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [← Finset.mul_prod_erase Finset.univ e (Finset.mem_univ j), mul_comm, mul_smul]
      exact M.smul_mem _ (hem j)
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ r hy
  refine ⟨d1 * ∏ j, e j, mul_ne_zero (nonZeroDivisors.ne_zero d1.2) (Finset.prod_ne_zero_iff.2 fun j _ => he j), ?_, ?_⟩
  · intro x hx
    rw [mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (h1 x hx)
  · intro x hx
    rw [mul_smul]
    exact M.smul_mem _ (h3 x hx)

end Sandwich

section Entries

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem mem_localized_one_iff (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) ↔ x ∈ (algebraMap (Ow w) K).range := by
  rw [mem_localized_iff_mem_baseChange, mem_atW_one_iff, mem_range_ow_iff]

theorem mem_localized_columnLattice_iff (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K) (x : Fin n → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) ↔
      ∀ a, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) a ∈
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := by
  classical
  constructor
  · rintro ⟨s, hs, hx⟩ a
    refine ⟨s, hs, ?_⟩
    have := (lc_mem_colLat B _).1 hx a
    rwa [Matrix.mulVec_smul] at this
  · intro h
    choose s hs hx using h
    refine ⟨∏ a, s a, ?_, ?_⟩
    · intro hmem
      obtain ⟨a, _, ha⟩ := (w.isPrime.prod_mem_iff).1 hmem
      exact hs a ha
    · rw [lc_mem_colLat]
      intro a
      rw [Matrix.mulVec_smul, Pi.smul_apply, ← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ a), mul_comm,
        mul_smul]
      exact Submodule.smul_mem _ _ (hx a)

theorem lc_entries (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin n → K)} {B B' : GL (Fin n) K}
    (hB : IsBasisAt w M B) (hB' : IsBasisAt w M' B') (d : 𝓞 K)
    (hd : ∀ x ∈ M, d • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M') (a b : Fin n) :
    algebraMap (𝓞 K) K d * ((B'⁻¹ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := by
  have h1 : (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a b) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
    rw [hB]
    exact lc_le_locP w _ (lc_col_mem_colLat B b)
  obtain ⟨s, hs, h2⟩ := h1
  have h3 := hd _ h2
  rw [hB', smul_comm, smul_mem_localized_iff w _ hs, mem_localized_columnLattice_iff] at h3
  have h4 := h3 a
  rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def] at h4
  have e : (((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a b) a
      = ((B'⁻¹ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b := by
    rw [Units.val_mul, Matrix.mul_apply]
    rfl
  rwa [e] at h4

theorem lc_entries_same (w : HeightOneSpectrum (𝓞 K)) {M : Submodule (𝓞 K) (Fin n → K)} {B B' : GL (Fin n) K}
    (hB : IsBasisAt w M B) (hB' : IsBasisAt w M B') (a b : Fin n) :
    ((B'⁻¹ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := by
  have := lc_entries w hB hB' 1 (fun x hx => by rw [one_smul]; exact lc_le_locP w _ hx) a b
  rwa [map_one, one_mul] at this

theorem lc_liftOw (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K)
    (h : ∀ a b, (g : Matrix (Fin n) (Fin n) K) a b ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K))
    (h' : ∀ a b, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)) :
    ∃ u : GL (Fin n) (Ow w), (u : Matrix (Fin n) (Fin n) (Ow w)).map (algebraMap (Ow w) K) =
      (g : Matrix (Fin n) (Fin n) K) := by
  choose U hU using fun a b => (mem_localized_one_iff w _).1 (h a b)
  choose U' hU' using fun a b => (mem_localized_one_iff w _).1 (h' a b)
  have e1 : (Matrix.of U).map (algebraMap (Ow w) K) = (g : Matrix (Fin n) (Fin n) K) := by
    ext a b
    exact hU a b
  have e2 : (Matrix.of U').map (algebraMap (Ow w) K) = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    ext a b
    exact hU' a b
  have hinj : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ow w) => A.map (algebraMap (Ow w) K) :=
    Matrix.map_injective (algebraMap_ow_injective w)
  refine ⟨⟨Matrix.of U, Matrix.of U', hinj ?_, hinj ?_⟩, e1⟩
  · show (Matrix.of U * Matrix.of U').map (algebraMap (Ow w) K) = (1 : Matrix (Fin n) (Fin n) (Ow w)).map _
    rw [Matrix.map_mul, e1, e2, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  · show (Matrix.of U' * Matrix.of U).map (algebraMap (Ow w) K) = (1 : Matrix (Fin n) (Fin n) (Ow w)).map _
    rw [Matrix.map_mul, e1, e2, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, inv_mul_cancel,
      Units.val_one]

theorem lc_unitOw (w : HeightOneSpectrum (𝓞 K)) {M : Submodule (𝓞 K) (Fin n → K)} {B B' : GL (Fin n) K}
    (hB : IsBasisAt w M B) (hB' : IsBasisAt w M B') :
    ∃ u : GL (Fin n) (Ow w), (u : Matrix (Fin n) (Fin n) (Ow w)).map (algebraMap (Ow w) K) =
      ((B'⁻¹ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  refine lc_liftOw w _ (lc_entries_same w hB hB') ?_
  have e : (B'⁻¹ * B)⁻¹ = B⁻¹ * B' := by rw [mul_inv_rev, inv_inv]
  rw [e]
  exact lc_entries_same w hB' hB

end Entries

section LocalConditions

variable {K : Type} [Field K] [NumberField K] {W : Type} [AddCommGroup W] [Module (𝓞 K) W]

theorem localized_iInf (Λ : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) W) (Λ₀ : Submodule (𝓞 K) W) (d : 𝓞 K) (hd : d ≠ 0)
    (hcl : ∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Λ w) = Λ w)
    (h1 : ∀ w, ∀ x ∈ Λ w, d • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal Λ₀) (h2 : ∀ w, ∀ x ∈ Λ₀, d • x ∈ Λ w)
    (w : HeightOneSpectrum (𝓞 K)) : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (⨅ w', Λ w') = Λ w := by
  apply le_antisymm
  · rw [← hcl w]
    exact localization_mono w.asIdeal (iInf_le _ w)
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := h1 w x hx
    obtain ⟨t, ht, htw⟩ := lc_primeTo (d * d) (mul_ne_zero hd hd) w
    refine ⟨t * s, lc_mul_notMem w ht hs, ?_⟩
    rw [Submodule.mem_iInf]
    intro w'
    by_cases hw : w' = w
    · rw [hw]
      exact (Λ w).smul_mem _ hx
    · obtain ⟨r, hr, c, hc⟩ := htw w' hw
      rw [← hcl w']
      refine ⟨r, hr, ?_⟩
      have e : r • (t * s) • x = c • d • s • d • x := by
        simp only [smul_smul]
        congr 1
        calc r * (t * s) = r * t * s := by ring
          _ = d * d * c * s := by rw [hc]
          _ = c * (d * (s * d)) := by ring
      rw [e]
      exact (Λ w').smul_mem c (h2 w' _ hsx)

end LocalConditions

end Formalism.L2.DIV
