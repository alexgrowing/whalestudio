import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.SizeWindowBrackets.ChainSlopeWindows.WeightedMeanLemmaNeedsDegree

open Module NumberField

noncomputable section

namespace Formalism.LFunctionChainParameters.slopeLatticeData

open Formalism.HN Formalism.HermitianLatticesTheory

section Alg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_comm_integers_field (r : 𝓞 K) (a : K) (x : V) : r • (a • x) = a • (r • x) := by
  rw [← algebraMap_smul K r (a • x), ← algebraMap_smul K r x, smul_smul, smul_smul, mul_comm]

omit [IsScalarTower (𝓞 K) K V] in
theorem mem_idealSmul {I : Submodule (𝓞 K) K} {L : Submodule (𝓞 K) V} {a : K} {x : V}
    (ha : a ∈ I) (hx : x ∈ L) : a • x ∈ idealSmul I L :=
  Submodule.subset_span ⟨a, ha, x, hx, rfl⟩

theorem idealSmul_le_span (I : Submodule (𝓞 K) K) (L : Submodule (𝓞 K) V) :
    idealSmul I L ≤ (Submodule.span K (L : Set V)).restrictScalars (𝓞 K) := by
  refine Submodule.span_le.2 ?_
  rintro z ⟨a, -, x, hx, rfl⟩
  exact Submodule.smul_mem _ a (Submodule.subset_span hx)

omit [IsScalarTower (𝓞 K) K V] in
theorem idealSmul_mono_right (I : Submodule (𝓞 K) K) {L L' : Submodule (𝓞 K) V} (h : L ≤ L') :
    idealSmul I L ≤ idealSmul I L' := by
  refine Submodule.span_mono ?_
  rintro z ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, ha, x, h hx, rfl⟩

theorem smul_mem_idealSmul {I' J : Submodule (𝓞 K) K} {L : Submodule (𝓞 K) V} (a : K)
    (h : ∀ c ∈ J, a * c ∈ I') {y : V} (hy : y ∈ idealSmul J L) : a • y ∈ idealSmul I' L := by
  refine Submodule.span_induction (p := fun y _ => a • y ∈ idealSmul I' L) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨c, hc, x, hx, rfl⟩
    rw [smul_smul]
    exact mem_idealSmul (h c hc) hx
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [smul_add]; exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    rw [← smul_comm_integers_field]; exact Submodule.smul_mem _ r hx

theorem idealSmul_mul (I J : Submodule (𝓞 K) K) (L : Submodule (𝓞 K) V) :
    idealSmul (I * J) L = idealSmul I (idealSmul J L) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨c, hc, x, hx, rfl⟩
    refine Submodule.mul_induction_on hc ?_ ?_
    · intro a ha c hc
      rw [SetLike.mem_coe, mul_smul]
      exact mem_idealSmul ha (mem_idealSmul hc hx)
    · intro c d hc hd
      rw [SetLike.mem_coe] at hc hd ⊢
      rw [add_smul]; exact Submodule.add_mem _ hc hd
  · refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, y, hy, rfl⟩
    exact smul_mem_idealSmul a (fun c hc => Submodule.mul_mem_mul ha hc) hy

theorem idealSmul_one (L : Submodule (𝓞 K) V) : idealSmul 1 L = L := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
    rw [SetLike.mem_coe, algebraMap_smul]
    exact Submodule.smul_mem _ r hx
  · intro x hx
    have := mem_idealSmul (I := (1 : Submodule (𝓞 K) K)) (a := 1)
      (Submodule.mem_one.2 ⟨1, map_one _⟩) hx
    rwa [one_smul] at this

theorem idealSmul_coeIdeal (J : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    idealSmul ((J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) L = J • L := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 (FractionalIdeal.mem_coe.1 ha)
    rw [SetLike.mem_coe, algebraMap_smul]
    exact Submodule.smul_mem_smul hr hx
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    rw [← algebraMap_smul K r x]
    exact mem_idealSmul (FractionalIdeal.mem_coe.2 ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩)) hx

def lsm (c : K) : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V c).restrictScalars (𝓞 K)

theorem idealSmul_spanSingleton (c : K) (L : Submodule (𝓞 K) V) :
    idealSmul ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) L = L.map (lsm c) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 (FractionalIdeal.mem_coe.1 ha)
    refine ⟨r • x, Submodule.smul_mem _ r hx, ?_⟩
    show c • (r • x) = (r • c) • x
    rw [smul_assoc, smul_comm_integers_field]
  · rintro _ ⟨x, hx, rfl⟩
    show c • x ∈ _
    exact mem_idealSmul (FractionalIdeal.mem_coe.2 (FractionalIdeal.mem_spanSingleton_self _ c)) hx

theorem idealSmul_fg (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) {L : Submodule (𝓞 K) V}
    (hL : L.FG) : (idealSmul (I : Submodule (𝓞 K) K) L).FG := by
  obtain ⟨a, J, -, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  rw [hI, FractionalIdeal.coe_mul, idealSmul_mul, idealSmul_coeIdeal, idealSmul_spanSingleton]
  exact (Submodule.FG.smul (IsNoetherian.noetherian J) hL).map _

theorem idealSmul_inv_cancel {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0)
    (L : Submodule (𝓞 K) V) :
    idealSmul ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)
      (idealSmul (I : Submodule (𝓞 K) K) L) = L := by
  rw [← idealSmul_mul, ← FractionalIdeal.coe_mul, inv_mul_cancel₀ hI, FractionalIdeal.coe_one,
    idealSmul_one]

theorem idealSmul_cancel_inv {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0)
    (L : Submodule (𝓞 K) V) :
    idealSmul (I : Submodule (𝓞 K) K)
      (idealSmul ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) L) = L := by
  rw [← idealSmul_mul, ← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI, FractionalIdeal.coe_one,
    idealSmul_one]

theorem span_idealSmul {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0)
    (L : Submodule (𝓞 K) V) :
    Submodule.span K ((idealSmul (I : Submodule (𝓞 K) K) L : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (L : Set V) := by
  apply le_antisymm
  · exact Submodule.span_le.2 (fun x hx => idealSmul_le_span _ _ hx)
  · refine Submodule.span_le.2 (fun x hx => ?_)
    have h := idealSmul_le_span ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) (idealSmul (I : Submodule (𝓞 K) K) L)
    rw [idealSmul_inv_cancel hI] at h
    exact h hx

theorem rkK_idealSmul {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0)
    (L : Submodule (𝓞 K) V) : rkK (idealSmul (I : Submodule (𝓞 K) K) L) = rkK L := by
  unfold rkK
  rw [span_idealSmul hI]

theorem rkK_pos [FiniteDimensional K V] {L : Submodule (𝓞 K) V} (hL : L ≠ ⊥) : 0 < rkK L := by
  unfold rkK
  rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  intro h
  apply hL
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ Submodule.span K (L : Set V) := Submodule.subset_span hx
  rw [h] at this
  exact this

theorem ne_bot_of_rkK_pos {L : Submodule (𝓞 K) V} (h : 0 < rkK L) : L ≠ ⊥ := by
  rintro rfl
  rw [rkK, Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot] at h
  exact lt_irrefl _ h

theorem fg_of_le {N M : Submodule (𝓞 K) V} (hM : M.FG) (h : N ≤ M) : N.FG := by
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM
  exact Submodule.FG.of_le_of_isNoetherian h

end Alg

section Ht

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

theorem ht_pos (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) : 0 < ht b X L :=
  (place_lattice_structure K V ι b X hX L hL).2.2

theorem ht_index (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {M N : Submodule (𝓞 K) V} (hM : M.FG) (hNM : N ≤ M)
    (hrk : rkK N = rkK M) :
    ht b X N = ht b X M * (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hN : N.FG := fg_of_le hM hNM
  obtain ⟨s, hsN, hspan, hli⟩ := exists_linearIndependent K (N : Set V)
  have hfin : s.Finite := hli.setFinite
  let _ : Fintype s := hfin.fintype
  let e : Fin (Fintype.card s) → V := fun i => ((Fintype.equivFin s).symm i : V)
  have he : LinearIndependent K e := hli.comp _ (Fintype.equivFin s).symm.injective
  have hrange : Set.range e = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ((Fintype.equivFin s).symm i).2
    · intro hx; exact ⟨Fintype.equivFin s ⟨x, hx⟩, by simp [e]⟩
  have hEN : Submodule.span (𝓞 K) (Set.range e) ≤ N := by
    rw [hrange]; exact Submodule.span_le.2 hsN
  have hrkN : rkK N = Fintype.card s := by
    have h0 : Submodule.span K (N : Set V) = Submodule.span K (Set.range e) := by
      rw [hrange, hspan]
    unfold rkK
    rw [h0, finrank_span_eq_card he, Fintype.card_fin]
  obtain ⟨-, hG⟩ := height_gram_determinant K V ι b X hX _ e he
  have h1 := hG N hN hEN hrkN
  have h2 := hG M hM (hEN.trans hNM) (hrk ▸ hrkN)
  have hE : 0 < ht b X (Submodule.span (𝓞 K) (Set.range e)) :=
    ht_pos b X hX (Submodule.fg_span (Set.finite_range e))
  have h3 := AddSubgroup.relIndex_mul_relIndex
    (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup N.toAddSubgroup M.toAddSubgroup
    ((Submodule.toAddSubgroup_le _ _).2 hEN) ((Submodule.toAddSubgroup_le _ _).2 hNM)
  rw [← h3, Nat.cast_mul] at h2
  have ha : ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex N.toAddSubgroup : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact hE.ne h1
  have h4 : ht b X N * ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex
      N.toAddSubgroup : ℝ) = (ht b X M * (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ)) *
      ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex N.toAddSubgroup : ℝ) := by
    rw [h1, ← h2]; ring
  exact mul_right_cancel₀ ha h4

theorem muDef_eq_log (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥) :
    muDef b X L = -(2 * Real.log (ht b X L)) / ((Module.finrank ℚ K : ℝ) * (rkK L : ℝ)) := by
  have h := (size_maximal_slope K V ι b X hX L hL hL0).2.1
  rw [h, size, Real.log_rpow (ht_pos b X hX hL), sizeMu_finrank_eq K]
  push_cast
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hj : (rkK L : ℝ) ≠ 0 := by exact_mod_cast (rkK_pos hL0).ne'
  have hf : (nPl K : ℝ) ≠ 0 := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp

theorem finrank_pos' : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
  exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)

theorem muDef_index (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {M N : Submodule (𝓞 K) V} (hM : M.FG) (hNM : N ≤ M)
    (hN0 : N ≠ ⊥) (hrk : rkK N = rkK M) :
    muDef b X N = muDef b X M - 2 * Real.log (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) /
      ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ)) := by
  have hN : N.FG := fg_of_le hM hNM
  have hM0 : M ≠ ⊥ := fun h => hN0 (eq_bot_iff.2 (h ▸ hNM))
  have hi := ht_index b X hX hM hNM hrk
  have hc : (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hi
    exact (ht_pos b X hX hN).ne' hi
  rw [muDef_eq_log b X hX hN hN0, muDef_eq_log b X hX hM hM0, hi, hrk,
    Real.log_mul (ht_pos b X hX hM).ne' hc]
  ring

theorem ht_ideal (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) {J : Ideal (𝓞 K)}
    (hJ : J ≠ ⊥) : ht b X (J • L) = ht b X L * (Ideal.absNorm J : ℝ) ^ rkK L := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hrk : rkK (J • L) = rkK L := by
    unfold rkK; rw [Formalism.HN.DualPolygon.twist_span_smul L J hJ]
  rw [ht_index b X hX hL Submodule.smul_le_right hrk, Formalism.HN.DualPolygon.twist_index L hL J hJ]
  push_cast
  rfl

theorem ht_fractional (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG)
    {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0) :
    ht b X (idealSmul (I : Submodule (𝓞 K) K) L) =
      ht b X L * ((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ rkK L := by
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h0
    exact ha (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
  have hJ : J ≠ ⊥ := by
    rintro rfl
    apply hI
    rw [hIJ]; simp
  have hA : Ideal.span {a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact ha
  have hmul : ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * I =
      (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, hIJ, ← mul_assoc,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ haK,
      FractionalIdeal.spanSingleton_one, one_mul]
  have hlat : Ideal.span {a} • idealSmul (I : Submodule (𝓞 K) K) L = J • L := by
    rw [← idealSmul_coeIdeal, ← idealSmul_mul, ← FractionalIdeal.coe_mul, hmul, idealSmul_coeIdeal]
  have h1 := ht_ideal b X hX (idealSmul_fg I hL) hA
  rw [hlat, ht_ideal b X hX hL hJ, rkK_idealSmul hI] at h1
  have hnorm : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℝ) * ((FractionalIdeal.absNorm I : ℚ) : ℝ) =
      ((Ideal.absNorm J : ℕ) : ℝ) := by
    have := congrArg FractionalIdeal.absNorm hmul
    rw [map_mul, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm] at this
    exact_mod_cast this
  have hA0 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => hA (Ideal.absNorm_eq_zero_iff.1 h)
  rw [← hnorm, mul_pow] at h1
  have h2 : ht b X (idealSmul (I : Submodule (𝓞 K) K) L) *
      ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℝ) ^ rkK L =
      (ht b X L * ((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ rkK L) *
      ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℝ) ^ rkK L := by
    rw [← h1]; ring
  exact mul_right_cancel₀ (pow_ne_zero _ hA0) h2

theorem absNorm_pos {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0) :
    (0 : ℝ) < ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  have h1 : (0 : ℚ) < FractionalIdeal.absNorm I :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I)
      (fun h => hI (FractionalIdeal.absNorm_eq_zero_iff.1 h.symm))
  exact_mod_cast h1

theorem muDef_fractional (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥)
    {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0) :
    muDef b X (idealSmul (I : Submodule (𝓞 K) K) L) = muDef b X L -
      2 * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hj := rkK_pos hL0
  have hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact hj)
  rw [muDef_eq_log b X hX (idealSmul_fg I hL) hIL0, muDef_eq_log b X hX hL hL0,
    ht_fractional b X hX hL hI, rkK_idealSmul hI,
    Real.log_mul (ht_pos b X hX hL).ne' (pow_ne_zero _ (absNorm_pos hI).ne'), Real.log_pow]
  have hj' : (rkK L : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hq : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_pos' (K := K)).ne'
  field_simp
  ring

end Ht

section Max

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

theorem muDef_le_muMaxDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L Q : Submodule (𝓞 K) V} (hL : L.FG) (hQL : Q ≤ L)
    (hQ0 : Q ≠ ⊥) : muDef b X Q ≤ muMaxDef b X L := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hL0 : L ≠ ⊥ := fun h => hQ0 (eq_bot_iff.2 (h ▸ hQL))
  have hlat := (place_lattice_structure K V ι b X hX L hL).1
  have hch := ((slope_characterization (𝓞 K) V _ (realize b X) L hlat hL0).1
    (muMax (realize b X) L)).1 le_rfl Q hQL
  have hrk := (place_lattice_structure K V ι b X hX Q (fg_of_le hL hQL)).2.1
  have hpos : (0 : ℝ) < (rk (realize b X) Q : ℝ) := by
    rw [hrk]
    exact_mod_cast Nat.mul_pos Module.finrank_pos (rkK_pos hQ0)
  have hs : slope (realize b X) Q ≤ muMax (realize b X) L := by
    show deg (realize b X) Q / (rk (realize b X) Q : ℝ) ≤ _
    rwa [div_le_iff₀ hpos]
  unfold muDef muMaxDef
  linarith

theorem muMaxDef_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    {L : Submodule (𝓞 K) V} (hL0 : L ≠ ⊥) {B : ℝ}
    (h : ∀ Q : Submodule (𝓞 K) V, Q ≤ L → Q ≠ ⊥ → muDef b X Q ≤ B) : muMaxDef b X L ≤ B := by
  have h1 : muMax (realize b X) L ≤
      (B + Real.log 2 - logDisc K / (Module.finrank ℚ K : ℝ)) / 2 := by
    unfold muMax
    refine csSup_le ⟨_, L, le_rfl, hL0, rfl⟩ ?_
    rintro t ⟨Q, hQL, hQ0, rfl⟩
    have := h Q hQL hQ0
    unfold muDef at this
    linarith
  unfold muMaxDef
  linarith

theorem muMaxDef_mono (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {M N : Submodule (𝓞 K) V} (hM : M.FG) (hNM : N ≤ M)
    (hN0 : N ≠ ⊥) : muMaxDef b X N ≤ muMaxDef b X M :=
  muMaxDef_le b X hN0 fun _ hQ hQ0 => muDef_le_muMaxDef b X hX hM (hQ.trans hNM) hQ0

theorem muMaxDef_fractional_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥)
    {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0) :
    muMaxDef b X (idealSmul (I : Submodule (𝓞 K) K) L) ≤ muMaxDef b X L -
      2 * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact rkK_pos hL0)
  refine muMaxDef_le b X hIL0 fun Q hQ hQ0 => ?_
  have hQfg : Q.FG := fg_of_le (idealSmul_fg I hL) hQ
  have hI' : I⁻¹ ≠ 0 := inv_ne_zero hI
  set Q' := idealSmul ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) Q
    with hQ'
  have hQ'L : Q' ≤ L := by
    have := idealSmul_mono_right
      ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) hQ
    rwa [idealSmul_inv_cancel hI] at this
  have hQ'0 : Q' ≠ ⊥ := ne_bot_of_rkK_pos (by rw [hQ', rkK_idealSmul hI']; exact rkK_pos hQ0)
  have hQeq : Q = idealSmul (I : Submodule (𝓞 K) K) Q' := (idealSmul_cancel_inv hI Q).symm
  rw [hQeq, muDef_fractional b X hX (fg_of_le hL hQ'L) hQ'0 hI]
  have := muDef_le_muMaxDef b X hX hL hQ'L hQ'0
  linarith

end Max

section Pow

variable {K : Type} [Field K] [NumberField K]

theorem finPl_ne_bot (w : FinPl K) : w.1 ≠ ⊥ := by
  intro h
  have hm := w.2
  rw [h] at hm
  exact NumberField.RingOfIntegers.not_isField K (Ring.isField_iff_maximal_bot.2 hm)

theorem finPl_coe_ne_zero (w : FinPl K) :
    (w.1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 (finPl_ne_bot w)

theorem idealPow_ne_zero (n : FinPl K →₀ ℤ) : idealPow n ≠ 0 := by
  unfold idealPow Finsupp.prod
  exact Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (finPl_coe_ne_zero w)

theorem log_absNorm_idealPow (n : FinPl K →₀ ℤ) (U : Finset (FinPl K)) (hU : n.support ⊆ U) :
    Real.log ((FractionalIdeal.absNorm (idealPow n) : ℚ) : ℝ) =
      ∑ w ∈ U, (n w : ℝ) * Real.log (Ideal.absNorm w.1 : ℝ) := by
  have h1 : ((FractionalIdeal.absNorm (idealPow n) : ℚ) : ℝ) =
      ∏ w ∈ n.support, ((Ideal.absNorm w.1 : ℕ) : ℝ) ^ (n w) := by
    unfold idealPow Finsupp.prod
    rw [map_prod, Rat.cast_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
  have hne : ∀ w : FinPl K, ((Ideal.absNorm w.1 : ℕ) : ℝ) ≠ 0 := fun w => by
    exact_mod_cast fun h => finPl_ne_bot w (Ideal.absNorm_eq_zero_iff.1 h)
  rw [h1, Real.log_prod (fun w _ => zpow_ne_zero _ (hne w))]
  rw [← Finset.sum_subset hU]
  · exact Finset.sum_congr rfl fun w _ => Real.log_zpow _ _
  · intro w _ hw
    rw [Finsupp.notMem_support_iff.1 hw]; simp

theorem sgSum_eq (σ τ : FinPl K →₀ ℤ) :
    sgSum σ τ = -(2 * Real.log ((FractionalIdeal.absNorm (idealPow (-σ)) : ℚ) : ℝ) /
        (Module.finrank ℚ K : ℝ)) -
      2 * Real.log ((FractionalIdeal.absNorm (idealPow τ) : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by
  classical
  rw [log_absNorm_idealPow (-σ) (σ.support ∪ τ.support)
      (by rw [Finsupp.support_neg]; exact Finset.subset_union_left),
    log_absNorm_idealPow τ (σ.support ∪ τ.support) Finset.subset_union_right]
  unfold sgSum ell
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr (by congr) fun w _ => ?_
  rw [Finsupp.neg_apply, Int.cast_neg]
  ring

end Pow

theorem slope_formula : SlopeRelationsIndex := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX σ τ M N hM hM0 hN hrk
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hτ := idealPow_ne_zero τ
  have hσ := idealPow_ne_zero (-σ)
  have hj := rkK_pos hM0
  set M1 := idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) M with hM1
  have hM1fg : M1.FG := idealSmul_fg _ hM
  have hM1rk : rkK M1 = rkK M := rkK_idealSmul hτ M
  have hNfg : N.FG := fg_of_le hM1fg hN
  have hN0 : N ≠ ⊥ := ne_bot_of_rkK_pos (hrk ▸ hj)
  have hN'0 : modLat σ N ≠ ⊥ :=
    ne_bot_of_rkK_pos (by unfold modLat; rw [rkK_idealSmul hσ, hrk]; exact hj)
  constructor
  · have hle : modLat σ N ≤ idealSmul ((idealPow (-σ) * idealPow τ :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M := by
      rw [FractionalIdeal.coe_mul, idealSmul_mul]
      exact idealSmul_mono_right _ hN
    have h1 := muMaxDef_mono b X hX (idealSmul_fg _ hM) hle hN'0
    have h2 := muMaxDef_fractional_le b X hX hM hM0 (mul_ne_zero hσ hτ)
    rw [map_mul, Rat.cast_mul, Real.log_mul (absNorm_pos hσ).ne' (absNorm_pos hτ).ne'] at h2
    rw [sgSum_eq]
    have e : 2 * (Real.log ((FractionalIdeal.absNorm (idealPow (-σ)) : ℚ) : ℝ) +
        Real.log ((FractionalIdeal.absNorm (idealPow τ) : ℚ) : ℝ)) / (Module.finrank ℚ K : ℝ) =
        2 * Real.log ((FractionalIdeal.absNorm (idealPow (-σ)) : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) +
        2 * Real.log ((FractionalIdeal.absNorm (idealPow τ) : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by
      ring
    rw [e] at h2
    linarith
  · unfold modLat
    rw [muDef_fractional b X hX hNfg hN0 hσ, muDef_index b X hX hM1fg hN hN0 (hrk.trans hM1rk.symm),
      hM1rk, hM1, muDef_fractional b X hX hM hM0 hτ, sgSum_eq]
    ring

theorem slope_twisted_lattice {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (σ τ : FinPl K →₀ ℤ) (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hM0 : M ≠ ⊥) :
    muDef b X (modLat σ (idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) M)) = muDef b X M + sgSum σ τ := by
  have h := (slope_formula K V ι b X hX σ τ M _ hM hM0 le_rfl
    (rkK_idealSmul (idealPow_ne_zero τ) M)).2
  rw [h, AddSubgroup.relIndex_self]
  simp

section Loc

variable {R : Type} [CommRing R]

def locLen (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q] : ℕ∞ :=
  Module.length (Localization.AtPrime w) (LocalizedModule w.primeCompl Q)

theorem locLen_exact (w : Ideal R) [w.IsPrime] {N M P : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    locLen w M = locLen w N + locLen w P :=
  Module.length_eq_add_of_exact (LocalizedModule.map w.primeCompl f)
    (LocalizedModule.map w.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)

theorem locLen_congr (w : Ideal R) [w.IsPrime] {M N : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] N) : locLen w M = locLen w N :=
  le_antisymm
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.toLinearMap)
      (LocalizedModule.map_injective _ _ e.injective))
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.symm.toLinearMap)
      (LocalizedModule.map_injective _ _ e.symm.injective))

theorem locLen_subsingleton (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q]
    [Subsingleton Q] : locLen w Q = 0 :=
  Module.length_eq_zero_iff.2 (IsLocalizedModule.subsingleton_of_subsingleton w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl Q))

theorem locLen_quot_ne (w m : Ideal R) [hw : w.IsMaximal] [hm : m.IsMaximal] (h : w ≠ m) :
    locLen w (R ⧸ m) = 0 := by
  refine Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl (R ⧸ m))).2 ?_)
  have hnle : ¬ m ≤ w := fun hle => h (hm.eq_of_le hw.ne_top hle).symm
  obtain ⟨s, hsm, hsw⟩ := SetLike.not_le_iff_exists.1 hnle
  intro x
  refine ⟨s, hsw, ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact m.mul_mem_right _ hsm

theorem locLen_quot_self (m : Ideal R) [hm : m.IsMaximal] : locLen m (R ⧸ m) = 1 := by
  refine Module.length_eq_one_iff.2 (isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨?_, ?_⟩)
  · rw [← not_subsingleton_iff_nontrivial, IsLocalizedModule.subsingleton_iff m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl (R ⧸ m))]
    intro h
    obtain ⟨r, hr, hr0⟩ := h 1
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr hr0
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h a s =>
    induction y using LocalizedModule.induction_on with
    | h c t =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hr : r ∈ m.primeCompl := by
      intro hrm
      apply hx
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hrm, LocalizedModule.zero_mk]
    refine ⟨Localization.mk (r' * s) (⟨r, hr⟩ * t), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Submonoid.coe_mul, Submonoid.coe_one]
    congr 1
    ring

theorem card_eq_prod_locLen : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module R Q] [Finite Q],
    Nat.card Q = n → ∃ k : {p : Ideal R // p.IsMaximal} →₀ ℕ,
      (∀ w : {p : Ideal R // p.IsMaximal}, (haveI := w.2.isPrime; locLen w.1 Q) = (k w : ℕ∞)) ∧
      Nat.card Q = k.prod fun w j => Nat.card (R ⧸ w.1) ^ j := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ hn
  by_cases hQ : Subsingleton Q
  · refine ⟨0, fun w => ?_, ?_⟩
    · have := w.2.isPrime
      rw [locLen_subsingleton]; simp
    · rw [Finsupp.prod_zero_index]; exact Nat.card_of_subsingleton 0
  · rw [not_subsingleton_iff_nontrivial] at hQ
    rcases eq_top_or_exists_le_coatom (⊥ : Submodule R Q) with h | ⟨Q1, hQ1, -⟩
    · exact absurd h bot_ne_top
    · have hsimple : IsSimpleModule R (Q ⧸ Q1) := isSimpleModule_iff_isCoatom.2 hQ1
      obtain ⟨m0, hm0, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hsimple
      have hnt : Nontrivial (Q ⧸ Q1) := IsSimpleModule.nontrivial R _
      have hcard : Nat.card Q = Nat.card Q1 * Nat.card (Q ⧸ Q1) :=
        Submodule.card_eq_card_quotient_mul_card Q1
      have hfq : Finite (Q ⧸ Q1) := Finite.of_surjective _ Q1.mkQ_surjective
      have h1 : 1 < Nat.card (Q ⧸ Q1) := Finite.one_lt_card
      have h2 : 0 < Nat.card Q1 := Nat.card_pos
      have hlt : Nat.card Q1 < n := by
        rw [← hn, hcard]; nlinarith
      obtain ⟨k1, hk1, hk1c⟩ := ih _ hlt Q1 rfl
      refine ⟨k1 + Finsupp.single ⟨m0, hm0⟩ 1, fun w => ?_, ?_⟩
      · have := w.2.isPrime
        have := w.2
        rw [locLen_exact w.1 Q1.subtype Q1.mkQ Q1.injective_subtype Q1.mkQ_surjective
          (LinearMap.exact_subtype_mkQ Q1), hk1 w, locLen_congr w.1 e, Finsupp.add_apply,
          Finsupp.single_apply]
        by_cases hw : (⟨m0, hm0⟩ : {p : Ideal R // p.IsMaximal}) = w
        · subst hw
          rw [if_pos rfl, locLen_quot_self]; simp
        · rw [if_neg hw, locLen_quot_ne w.1 m0 (fun h => hw (Subtype.ext h.symm))]; simp
      · have hz : ∀ w : {p : Ideal R // p.IsMaximal}, Nat.card (R ⧸ w.1) ^ 0 = 1 :=
          fun _ => pow_zero _
        have ha : ∀ (w : {p : Ideal R // p.IsMaximal}) (a c : ℕ), Nat.card (R ⧸ w.1) ^ (a + c) =
            Nat.card (R ⧸ w.1) ^ a * Nat.card (R ⧸ w.1) ^ c := fun _ _ _ => pow_add _ _ _
        rw [Finsupp.prod_add_index'
            (h := fun (w : {p : Ideal R // p.IsMaximal}) (j : ℕ) => Nat.card (R ⧸ w.1) ^ j) hz ha,
          Finsupp.prod_single_index
            (h := fun (w : {p : Ideal R // p.IsMaximal}) (j : ℕ) => Nat.card (R ⧸ w.1) ^ j) (hz _),
          pow_one, hcard, hk1c, Nat.card_congr e.toEquiv]

end Loc

section Len

theorem index_finsupp {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V) (h : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ k : FinPl K →₀ ℕ, (∀ w : FinPl K, lenAt w A B = (k w : ℕ∞)) ∧
      B.toAddSubgroup.relIndex A.toAddSubgroup = k.prod fun w j => Ideal.absNorm w.1 ^ j := by
  have h' : Nat.card (A ⧸ B.comap A.subtype) ≠ 0 := h
  have hfin : Finite (A ⧸ B.comap A.subtype) := Nat.finite_of_card_ne_zero h'
  obtain ⟨k, hk, hc⟩ := card_eq_prod_locLen (R := 𝓞 K) _ (A ⧸ B.comap A.subtype) rfl
  refine ⟨k, hk, ?_⟩
  change Nat.card (A ⧸ B.comap A.subtype) = _
  rw [hc]
  refine Finsupp.prod_congr fun w _ => ?_
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem index_eq_length : IndexLen := by
  intro K V _ _ _ _ A B h
  obtain ⟨k, hk, hc⟩ := index_finsupp A B h
  refine ⟨fun w => by rw [hk]; exact ENat.natCast_ne_top _, ?_, ?_⟩
  · refine k.support.finite_toSet.subset fun w hw => ?_
    rw [Function.mem_support, hk] at hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    exact_mod_cast hw
  · rw [hc, finprod_eq_prod_of_mulSupport_subset (s := k.support)]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [hk, ENat.toNat_natCast]
    · intro w hw
      rw [Function.mem_mulSupport, hk, ENat.toNat_natCast] at hw
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      rw [h0, pow_zero] at hw
      exact hw rfl

theorem relIndex_ne_zero {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {M N : Submodule (𝓞 K) V} (hM : M.FG) (hNM : N ≤ M)
    (hrk : rkK N = rkK M) : N.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
  intro h0
  have hi := ht_index b X hX hM hNM hrk
  rw [h0, Nat.cast_zero, mul_zero] at hi
  exact (ht_pos b X hX (fg_of_le hM hNM)).ne' hi

theorem slope_via_lengths : SlopeRelationsLength := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX σ τ M N β hM hM0 hN hrk hβ
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  obtain ⟨h1, h2⟩ := slope_formula K V ι b X hX σ τ M N hM hM0 hN hrk
  have hτ := idealPow_ne_zero τ
  have hidx := relIndex_ne_zero b X hX (idealSmul_fg (idealPow τ) hM) hN
    (hrk.trans (rkK_idealSmul hτ M).symm)
  obtain ⟨k, hk, hc⟩ := index_finsupp _ N hidx
  have hd : (rkK M : ℝ) ≠ 0 := by exact_mod_cast (rkK_pos hM0).ne'
  have hq : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  have hkβ : ∀ w, (k w : ℝ) = (rkK M : ℝ) * β w := fun w => by
    rw [← hβ w, hk, ENat.toNat_natCast]
  have hsupp : Function.support β ⊆ (k.support : Set (FinPl K)) := by
    intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    have := hkβ w
    rw [h0, Nat.cast_zero] at this
    exact hw ((mul_eq_zero.1 this.symm).resolve_left hd)
  refine ⟨fun w => by rw [hk]; exact ENat.natCast_ne_top _, k.support.finite_toSet.subset hsupp, h1, ?_⟩
  rw [h2, hc]
  congr 1
  have hne : ∀ w : FinPl K, ((Ideal.absNorm w.1 : ℕ) : ℝ) ≠ 0 := fun w => by
    exact_mod_cast fun h => finPl_ne_bot w (Ideal.absNorm_eq_zero_iff.1 h)
  rw [finsum_eq_sum_of_support_subset (s := k.support)]
  · unfold Finsupp.prod ell
    rw [Nat.cast_prod, Real.log_prod (fun w _ => by push_cast; exact pow_ne_zero _ (hne w)),
      Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Nat.cast_pow, Real.log_pow, hkβ w]
    field_simp
  · intro w hw
    apply hsupp
    rw [Function.mem_support] at hw ⊢
    intro h0
    rw [h0, mul_zero] at hw
    exact hw rfl

theorem slope_pair_of_slopes : SlopesHypothesisFinitePlaces := by
  intro K _ _ _ _ J V ι _ _ _ _ _ _ b X hX σ τ M N β Sg0 dr hM hM0 hN hrk hβ hSg
  constructor
  · intro u
    have := (slope_via_lengths K (V u) (ι u) (b u) (X u) (hX u) (σ u) (τ u) (M u) (N u) (β u) (hM u)
      (hM0 u) (hN u) (hrk u) (hβ u)).2.2.1
    rw [hSg u] at this
    exact this
  · intro u
    have := (slope_via_lengths K (V u) (ι u) (b u) (X u) (hX u) (σ u) (τ u) (M u) (N u) (β u) (hM u)
      (hM0 u) (hN u) (hrk u) (hβ u)).2.2.2
    rw [hSg u] at this
    exact this

end Len

section Span

theorem length_at_span_localized {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (w : Ideal R)
    [w.IsPrime] [Module (Localization.AtPrime w) V] [IsScalarTower R (Localization.AtPrime w) V]
    (A B : Submodule R V) (hBA : B ≤ A) (A'' : Submodule (Localization.AtPrime w) V)
    (hA : haveI := isLocalizedModule_id w.primeCompl V (Localization.AtPrime w)
      A.localized' (Localization.AtPrime w) w.primeCompl LinearMap.id = A'') :
    locLen w (A ⧸ B.comap A.subtype) = Module.length (Localization.AtPrime w)
      (A'' ⧸ (Submodule.span (Localization.AtPrime w) (B : Set V)).comap A''.subtype) := by
  have i0 := isLocalizedModule_id w.primeCompl V (Localization.AtPrime w)
  subst hA
  set f1 := A.toLocalized' (Localization.AtPrime w) w.primeCompl LinearMap.id with hf1
  have hf1c : ∀ a : A, ((f1 a : V)) = (a : V) := fun a => rfl
  have hB : (B.comap A.subtype).localized' (Localization.AtPrime w) w.primeCompl f1 =
      (Submodule.span (Localization.AtPrime w) (B : Set V)).comap
        (A.localized' (Localization.AtPrime w) w.primeCompl LinearMap.id).subtype := by
    have hspan : Submodule.span (Localization.AtPrime w) (B : Set V) =
        B.localized' (Localization.AtPrime w) w.primeCompl LinearMap.id := by
      rw [Submodule.localized'_eq_span]; simp
    rw [hspan]
    ext x
    rw [Submodule.mem_localized', Submodule.mem_comap, Submodule.mem_localized']
    constructor
    · rintro ⟨m, hm, s, hx⟩
      refine ⟨(m : V), hm, s, ?_⟩
      rw [IsLocalizedModule.mk'_eq_iff] at hx ⊢
      have := congrArg Subtype.val hx
      simpa [hf1c] using this
    · rintro ⟨m, hm, s, hx⟩
      refine ⟨⟨m, hBA hm⟩, hm, s, ?_⟩
      rw [IsLocalizedModule.mk'_eq_iff] at hx ⊢
      apply Subtype.ext
      simpa [hf1c] using hx
  rw [← hB]
  exact ((IsLocalizedModule.iso w.primeCompl ((B.comap A.subtype).toLocalizedQuotient'
    (Localization.AtPrime w) w.primeCompl f1)).extendScalarsOfIsLocalization w.primeCompl
      (Localization.AtPrime w)).length_eq

theorem length_at_span : LenAtSpan := by
  intro K V _ _ _ _ w _ _ A B hBA
  have := w.2.isPrime
  have i0 := isLocalizedModule_id w.1.primeCompl V (Localization.AtPrime w.1)
  refine length_at_span_localized w.1 A B hBA _ ?_
  rw [Submodule.localized'_eq_span]; simp

end Span

section Tests

theorem slope_via_lengths_ideal {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (τ : FinPl K →₀ ℤ) (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hM0 : M ≠ ⊥) (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    ∑ᶠ w : FinPl K, 2 * ell w * (((lenAt w (idealSmul ((idealPow τ :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M)
      (J • idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
        Submodule (𝓞 K) K) M)).toNat : ℝ) / (rkK M : ℝ)) =
      2 * Real.log (Ideal.absNorm J : ℝ) / (Module.finrank ℚ K : ℝ) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hτ := idealPow_ne_zero τ
  set M1 := idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) M with hM1
  have hM1fg : M1.FG := idealSmul_fg _ hM
  have hM1rk : rkK M1 = rkK M := rkK_idealSmul hτ M
  have hrk : rkK (J • M1) = rkK M := by
    rw [← hM1rk]; unfold rkK; rw [Formalism.HN.DualPolygon.twist_span_smul M1 J hJ]
  have hd : (rkK M : ℝ) ≠ 0 := by exact_mod_cast (rkK_pos hM0).ne'
  have hq : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  have h1 := (slope_formula K V ι b X hX 0 τ M (J • M1) hM hM0 Submodule.smul_le_right hrk).2
  have h2 := (slope_via_lengths K V ι b X hX 0 τ M (J • M1)
    (fun w => ((lenAt w M1 (J • M1)).toNat : ℝ) / (rkK M : ℝ)) hM hM0 Submodule.smul_le_right hrk
    (fun w => by field_simp; rfl)).2.2.2
  rw [← hM1] at h1
  rw [h1, Formalism.HN.DualPolygon.twist_index M1 hM1fg J hJ] at h2
  have h3 : finrank K (Submodule.span K (M1 : Set V)) = rkK M := hM1rk
  rw [h3, Nat.cast_pow, Real.log_pow] at h2
  have h4 : 2 * ((rkK M : ℝ) * Real.log (Ideal.absNorm J : ℝ)) /
      ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ)) =
      2 * Real.log (Ideal.absNorm J : ℝ) / (Module.finrank ℚ K : ℝ) := by
    field_simp
  rw [h4] at h2
  linarith

example : ∃ (K V ι : Type) (_ : Field K) (_ : NumberField K) (_ : StarRing K)
    (_ : IsTotallyComplex K) (_ : AddCommGroup V) (_ : Module K V) (_ : Module (𝓞 K) V)
    (_ : IsScalarTower (𝓞 K) K V) (_ : Fintype ι) (_ : DecidableEq ι) (_ : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (M : Submodule (𝓞 K) V),
    (∀ v, IsUnit (X v).det) ∧ M.FG ∧ M ≠ ⊥ := by
  have hne : NeZero ((5 : ℕ) : ℚ) := ⟨by norm_num⟩
  have hcyc : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  refine ⟨CyclotomicField 5 ℚ, CyclotomicField 5 ℚ, Unit, inferInstance, inferInstance,
    starRingOfComm, IsCyclotomicExtension.Rat.isTotallyComplex (n := 5) _ (by norm_num),
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Basis.singleton Unit _, fun _ => 1, Submodule.span _ {1}, fun v => by simp,
    Submodule.fg_span (Set.finite_singleton _), ?_⟩
  rw [Ne, Submodule.span_singleton_eq_bot]
  exact one_ne_zero

end Tests

section LocPow

variable {K : Type} [Field K] [NumberField K]

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

def HalfUnit (w : Ideal (𝓞 K)) (J : FI) : Prop :=
  ∃ t : 𝓞 K, t ∉ w ∧ ∀ x ∈ J, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * x

def WUnit (w : Ideal (𝓞 K)) (J : FI) : Prop := J ≠ 0 ∧ HalfUnit w J ∧ HalfUnit w J⁻¹

theorem halfUnit_of_le_one (w : Ideal (𝓞 K)) [hw : w.IsPrime] {J : FI} (h : J ≤ 1) :
    HalfUnit w J := by
  refine ⟨1, fun h1 => hw.ne_top ((Ideal.eq_top_iff_one w).2 h1), fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := (FractionalIdeal.mem_one_iff _).1 (h hx)
  exact ⟨y, by rw [hy, map_one, one_mul]⟩

theorem halfUnit_mul (w : Ideal (𝓞 K)) [hw : w.IsPrime] {I J : FI} (hI : HalfUnit w I)
    (hJ : HalfUnit w J) : HalfUnit w (I * J) := by
  obtain ⟨t1, ht1, h1⟩ := hI
  obtain ⟨t2, ht2, h2⟩ := hJ
  refine ⟨t1 * t2, fun h => (hw.mem_or_mem h).elim ht1 ht2, fun x hx => ?_⟩
  refine FractionalIdeal.mul_induction_on hx ?_ ?_
  · intro i hi j hj
    obtain ⟨y1, hy1⟩ := h1 i hi
    obtain ⟨y2, hy2⟩ := h2 j hj
    exact ⟨y1 * y2, by rw [map_mul, map_mul, hy1, hy2]; ring⟩
  · rintro x y ⟨a, ha⟩ ⟨c, hc⟩
    exact ⟨a + c, by rw [map_add, ha, hc]; ring⟩

theorem wUnit_one (w : Ideal (𝓞 K)) [w.IsPrime] : WUnit w (1 : FI) :=
  ⟨one_ne_zero, halfUnit_of_le_one w le_rfl, by rw [inv_one]; exact halfUnit_of_le_one w le_rfl⟩

theorem wUnit_mul (w : Ideal (𝓞 K)) [w.IsPrime] {I J : FI} (hI : WUnit w I) (hJ : WUnit w J) :
    WUnit w (I * J) :=
  ⟨mul_ne_zero hI.1 hJ.1, halfUnit_mul w hI.2.1 hJ.2.1, by
    rw [mul_inv]; exact halfUnit_mul w hI.2.2 hJ.2.2⟩

theorem wUnit_inv (w : Ideal (𝓞 K)) {I : FI} (hI : WUnit w I) : WUnit w I⁻¹ :=
  ⟨inv_ne_zero hI.1, hI.2.2, by rw [inv_inv]; exact hI.2.1⟩

theorem wUnit_pow (w : Ideal (𝓞 K)) [w.IsPrime] {I : FI} (hI : WUnit w I) (k : ℕ) :
    WUnit w (I ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact wUnit_one w
  | succ k ih => rw [pow_succ]; exact wUnit_mul w ih hI

theorem wUnit_zpow (w : Ideal (𝓞 K)) [w.IsPrime] {I : FI} (hI : WUnit w I) (k : ℤ) :
    WUnit w (I ^ k) := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [zpow_natCast]; exact wUnit_pow w hI n
  · rw [zpow_neg, zpow_natCast]; exact wUnit_inv w (wUnit_pow w hI n)

theorem wUnit_other (w w' : FinPl K) (h : w' ≠ w) : WUnit w.1 (w'.1 : FI) := by
  have := w.2.isPrime
  have h0 := finPl_coe_ne_zero w'
  refine ⟨h0, halfUnit_of_le_one w.1 FractionalIdeal.coeIdeal_le_one, ?_⟩
  have hnle : ¬ w'.1 ≤ w.1 := fun hle => h (Subtype.ext (w'.2.eq_of_le w.2.ne_top hle))
  obtain ⟨t, htw', htw⟩ := SetLike.not_le_iff_exists.1 hnle
  refine ⟨t, htw, fun x hx => ?_⟩
  have hmem : algebraMap (𝓞 K) K t * x ∈ (w'.1 : FI) * (w'.1 : FI)⁻¹ :=
    FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨t, htw', rfl⟩) hx
  rw [mul_inv_cancel₀ h0] at hmem
  exact (FractionalIdeal.mem_one_iff _).1 hmem

theorem wUnit_self (w : FinPl K) {ϖ : 𝓞 K} (h1 : ϖ ∈ w.1) (h2 : ϖ ∉ w.1 ^ 2) :
    WUnit w.1 ((w.1 : FI) *
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ))⁻¹) := by
  have := w.2.isPrime
  have hw0 := finPl_coe_ne_zero w
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl; exact h2 (Ideal.zero_mem _)
  have hϖK : algebraMap (𝓞 K) K ϖ ≠ 0 := by
    intro h0
    exact hϖ0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
  set Pw : FI := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ)
    with hPw
  have hPw0 : Pw ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hϖK
  have hPww : Pw ≤ (w.1 : FI) := by
    rw [hPw, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_le_coeIdeal]
    exact (Ideal.span_singleton_le_iff_mem _).2 h1
  have hC1 : Pw * (w.1 : FI)⁻¹ ≤ 1 := by
    calc Pw * (w.1 : FI)⁻¹ ≤ (w.1 : FI) * (w.1 : FI)⁻¹ := mul_le_mul_left hPww _
      _ = 1 := mul_inv_cancel₀ hw0
  refine ⟨mul_ne_zero hw0 (inv_ne_zero hPw0), ?_, ?_⟩
  ·
    have hex : ∃ t : 𝓞 K, algebraMap (𝓞 K) K t ∈ Pw * (w.1 : FI)⁻¹ ∧ t ∉ w.1 := by
      by_contra hcon
      push Not at hcon
      apply h2
      have hle : Pw * (w.1 : FI)⁻¹ * (w.1 : FI) ≤ ((w.1 ^ 2 : Ideal (𝓞 K)) : FI) := by
        intro x hx
        refine FractionalIdeal.mul_induction_on hx ?_ ?_
        · intro i hi j hj
          obtain ⟨t, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 (hC1 hi)
          obtain ⟨s, hs, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
          refine (FractionalIdeal.mem_coeIdeal _).2 ⟨t * s, ?_, map_mul _ _ _⟩
          rw [sq]; exact Ideal.mul_mem_mul (hcon t hi) hs
        · intro x y hx hy
          exact FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 hx)
            (FractionalIdeal.mem_coe.2 hy))
      rw [mul_assoc, inv_mul_cancel₀ hw0, mul_one] at hle
      obtain ⟨z, hz, hzϖ⟩ := (FractionalIdeal.mem_coeIdeal _).1
        (hle (FractionalIdeal.mem_spanSingleton_self _ _))
      rwa [FaithfulSMul.algebraMap_injective (𝓞 K) K hzϖ] at hz
    obtain ⟨t, htC, htw⟩ := hex
    refine ⟨t, htw, fun x hx => ?_⟩
    have hmem := FractionalIdeal.mul_mem_mul htC hx
    have e : Pw * (w.1 : FI)⁻¹ * ((w.1 : FI) * Pw⁻¹) = 1 := by
      rw [mul_assoc, ← mul_assoc (w.1 : FI)⁻¹, inv_mul_cancel₀ hw0, one_mul, mul_inv_cancel₀ hPw0]
    rw [e] at hmem
    exact (FractionalIdeal.mem_one_iff _).1 hmem
  · rw [mul_inv, inv_inv, mul_comm]
    exact halfUnit_of_le_one w.1 hC1

theorem idealPow_add (m n : FinPl K →₀ ℤ) : idealPow (m + n) = idealPow m * idealPow n := by
  unfold idealPow
  exact Finsupp.prod_add_index' (h := fun (w : FinPl K) (k : ℤ) => ((w.1 : FI)) ^ k)
    (fun _ => zpow_zero _) (fun w _ _ => zpow_add₀ (finPl_coe_ne_zero w) _ _)

theorem wUnit_idealPow (w : FinPl K) {ϖ : 𝓞 K} (h1 : ϖ ∈ w.1) (h2 : ϖ ∉ w.1 ^ 2)
    (n : FinPl K →₀ ℤ) : WUnit w.1 (idealPow n *
      ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ) : FI) ^
        (n w))⁻¹) := by
  classical
  have := w.2.isPrime
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl; exact h2 (Ideal.zero_mem _)
  have hϖK : algebraMap (𝓞 K) K ϖ ≠ 0 := by
    intro h0
    exact hϖ0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
  set Pw : FI := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ)
    with hPw
  have hPw0 : Pw ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hϖK
  induction n using Finsupp.induction_linear with
  | zero =>
    have : idealPow (0 : FinPl K →₀ ℤ) = 1 := by unfold idealPow; exact Finsupp.prod_zero_index
    rw [this, Finsupp.zero_apply, zpow_zero, inv_one, mul_one]
    exact wUnit_one w.1
  | add f g hf hg =>
    rw [idealPow_add, Finsupp.add_apply, zpow_add₀ hPw0, mul_inv, mul_mul_mul_comm]
    exact wUnit_mul w.1 hf hg
  | single a k =>
    have : idealPow (Finsupp.single a k) = (a.1 : FI) ^ k := by
      unfold idealPow
      exact Finsupp.prod_single_index (zpow_zero _)
    rw [this, Finsupp.single_apply]
    by_cases ha : a = w
    · subst ha
      rw [if_pos rfl, ← inv_zpow, ← mul_zpow]
      exact wUnit_zpow a.1 (wUnit_self a h1 h2) k
    · rw [if_neg ha, zpow_zero, inv_one, mul_one]
      exact wUnit_zpow w.1 (wUnit_other w a ha) k

theorem spanSingleton_zpow (x : K) (k : ℤ) :
    (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x : FI) ^ k =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x ^ k) := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [zpow_natCast, zpow_natCast, FractionalIdeal.spanSingleton_pow]
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, FractionalIdeal.spanSingleton_pow,
      FractionalIdeal.spanSingleton_inv]

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem idealSmul_le_span_loc (w : Ideal (𝓞 K)) [w.IsPrime] [Module (Localization.AtPrime w) V]
    [IsScalarTower (𝓞 K) (Localization.AtPrime w) V] {J : FI} (hJ : HalfUnit w J)
    (L : Submodule (𝓞 K) V) :
    idealSmul (J : Submodule (𝓞 K) K) L ≤
      (Submodule.span (Localization.AtPrime w) (L : Set V)).restrictScalars (𝓞 K) := by
  obtain ⟨t, ht, h⟩ := hJ
  refine Submodule.span_le.2 ?_
  rintro z ⟨a, ha, x, hx, rfl⟩
  obtain ⟨y, hy⟩ := h a (FractionalIdeal.mem_coe.1 ha)
  have e1 : t • (a • x) = y • x := by
    rw [← algebraMap_smul K t (a • x), smul_smul, ← hy, algebraMap_smul]
  obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime w) (⟨t, ht⟩ : w.primeCompl)
  have e2 : a • x = (↑u⁻¹ : Localization.AtPrime w) • (y • x) := by
    rw [← e1, ← algebraMap_smul (Localization.AtPrime w) t (a • x), smul_smul]
    have : (↑u⁻¹ : Localization.AtPrime w) * algebraMap (𝓞 K) (Localization.AtPrime w) t = 1 := by
      have hu' : (u : Localization.AtPrime w) = algebraMap (𝓞 K) (Localization.AtPrime w) t := hu
      rw [← hu']; exact u.inv_mul
    rw [this, one_smul]
  show a • x ∈ Submodule.span (Localization.AtPrime w) (L : Set V)
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (L.smul_mem y hx))

theorem span_loc_idealSmul (w : Ideal (𝓞 K)) [w.IsPrime] [Module (Localization.AtPrime w) V]
    [IsScalarTower (𝓞 K) (Localization.AtPrime w) V] {J : FI} (hJ : WUnit w J)
    (L : Submodule (𝓞 K) V) :
    Submodule.span (Localization.AtPrime w)
      ((idealSmul (J : Submodule (𝓞 K) K) L : Submodule (𝓞 K) V) : Set V) =
      Submodule.span (Localization.AtPrime w) (L : Set V) := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun x hx => idealSmul_le_span_loc w hJ.2.1 L hx
  · refine Submodule.span_le.2 fun x hx => ?_
    have h := idealSmul_le_span_loc w hJ.2.2 (idealSmul (J : Submodule (𝓞 K) K) L)
    rw [idealSmul_inv_cancel hJ.1] at h
    exact h hx

theorem local_ideal_pow : LocIdealPow := by
  intro K V _ _ _ _ _ _ w _ _ ϖ h1 h2 n M
  have := w.2.isPrime
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl; exact h2 (Ideal.zero_mem _)
  have hϖK : algebraMap (𝓞 K) K ϖ ≠ 0 := by
    intro h0
    exact hϖ0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
  have hU := wUnit_idealPow w h1 h2 n
  have hPw0 : (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (n w) ≠ 0 :=
    zpow_ne_zero _ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hϖK)
  have hfac : idealPow n = idealPow n *
      ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (n w))⁻¹ *
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ ^ n w) := by
    rw [← spanSingleton_zpow, mul_assoc, inv_mul_cancel₀ hPw0, mul_one]
  conv_lhs => rw [hfac, FractionalIdeal.coe_mul, idealSmul_mul, idealSmul_spanSingleton]
  rw [span_loc_idealSmul w.1 hU, Submodule.map_coe]
  rfl

end LocPow

section Local

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem locScal_one (w : FinPl K) [Module (Rloc w) V] (L : Submodule (𝓞 K) V) :
    locScal w 1 L = Submodule.span (Rloc w) (L : Set V) := by
  unfold locScal
  simp

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem le_of_loc [∀ w : FinPl K, Module (Rloc w) V]
    [∀ w : FinPl K, IsScalarTower (𝓞 K) (Rloc w) V] {A B : Submodule (𝓞 K) V}
    (h : ∀ w : FinPl K, Submodule.span (Rloc w) (A : Set V) ≤ Submodule.span (Rloc w) (B : Set V)) :
    A ≤ B := by
  intro x hx
  let I : Ideal (𝓞 K) := B.colon {x}
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    let w : FinPl K := ⟨m, hm⟩
    have := w.2.isPrime
    have i0 := isLocalizedModule_id w.1.primeCompl V (Rloc w)
    have hxB : x ∈ Submodule.span (Rloc w) (B : Set V) := h w (Submodule.subset_span hx)
    have hspan : Submodule.span (Rloc w) (B : Set V) =
        B.localized' (Rloc w) w.1.primeCompl LinearMap.id := by
      rw [Submodule.localized'_eq_span]; simp
    rw [hspan, Submodule.mem_localized'] at hxB
    obtain ⟨y, hy, s, hs⟩ := hxB
    rw [IsLocalizedModule.mk'_eq_iff] at hs
    have hsI : (s : 𝓞 K) ∈ I := by
      rw [Submodule.mem_colon_singleton]
      have : (s : 𝓞 K) • x = y := hs.symm
      rw [this]; exact hy
    exact s.2 (hIm hsI)
  have h1 : (1 : 𝓞 K) ∈ I := by rw [hI]; exact Submodule.mem_top
  rw [Submodule.mem_colon_singleton, one_smul] at h1
  exact h1

theorem length_congr_sub {R : Type} [CommRing R] [Module R V] {A1 A2 : Submodule R V}
    (h : A1 = A2) (B : Submodule R V) :
    Module.length R (A1 ⧸ B.comap A1.subtype) = Module.length R (A2 ⧸ B.comap A2.subtype) := by
  subst h; rfl

end Local

theorem slope_local : SlopeRelationsLocal := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ _ _ b X hX ϖ hϖ σ τ M N N' β hM hM0 hrk hN hN' hβ
  have hloc : ∀ (n : FinPl K →₀ ℤ) (L : Submodule (𝓞 K) V) (w : FinPl K),
      Submodule.span (Rloc w) ((idealSmul ((idealPow n :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) L :
          Submodule (𝓞 K) V) : Set V) = locScal w (algebraMap (𝓞 K) K (ϖ w) ^ n w) L :=
    fun n L w => local_ideal_pow K V w (ϖ w) (hϖ w).1 (hϖ w).2 n L
  have hNle : N ≤ idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) M := by
    refine le_of_loc fun w => ?_
    rw [hloc, ← locScal_one]
    exact hN w
  have hN'eq : N' = modLat σ N := by
    unfold modLat
    apply le_antisymm
    · refine le_of_loc fun w => ?_
      rw [hloc, ← locScal_one, hN' w, Finsupp.neg_apply]
    · refine le_of_loc fun w => ?_
      rw [hloc, ← locScal_one, hN' w, Finsupp.neg_apply]
  have hlen : ∀ w : FinPl K, lenAt w (idealSmul ((idealPow τ :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M) N =
      Module.length (Rloc w) (locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M ⧸
        (locScal w 1 N).comap (locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M).subtype) := by
    intro w
    rw [length_at_span K V w _ N hNle, locScal_one]
    exact length_congr_sub (hloc τ M w) _
  have hmain := slope_via_lengths K V ι b X hX σ τ M N β hM hM0 hNle hrk
    (fun w => by rw [hlen w]; exact hβ w)
  rw [hN'eq]
  exact ⟨fun w => by rw [← hlen w]; exact hmain.1 w, hmain.2⟩

section LocalTest

def rlocToK {K : Type} [Field K] [NumberField K] (w : FinPl K) : Rloc w →+* K :=
  haveI := w.2.isPrime
  IsLocalization.lift (M := w.1.primeCompl) (S := Rloc w) (g := algebraMap (𝓞 K) K) (fun y => by
    refine IsUnit.mk0 _ fun h0 => y.2 ?_
    have : (y : 𝓞 K) = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0)
    rw [this]; exact Ideal.zero_mem _)

theorem slope_local_nonvacuous {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (σ τ : FinPl K →₀ ℤ)
    (M : Submodule (𝓞 K) V) :
    ∃ (_ : ∀ w : FinPl K, Module (Rloc w) V) (_ : ∀ w : FinPl K, IsScalarTower (𝓞 K) (Rloc w) V)
      (ϖ : FinPl K → 𝓞 K) (N N' : Submodule (𝓞 K) V), (∀ w, ϖ w ∈ w.1 ∧ ϖ w ∉ w.1 ^ 2) ∧
      rkK N = rkK M ∧
      (∀ w, locScal w 1 N ≤ locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M) ∧
      (∀ w, locScal w 1 N' = locScal w (algebraMap (𝓞 K) K (ϖ w) ^ (-σ w)) N) := by
  let i1 : ∀ w : FinPl K, Module (Rloc w) V := fun w => Module.compHom V (rlocToK w)
  have i2 : ∀ w : FinPl K, IsScalarTower (𝓞 K) (Rloc w) V := fun w => ⟨fun r s x => by
    have := w.2.isPrime
    show rlocToK w (r • s) • x = r • (rlocToK w s • x)
    have hr : rlocToK w (algebraMap (𝓞 K) (Rloc w) r) = algebraMap (𝓞 K) K r :=
      IsLocalization.lift_eq _ r
    rw [Algebra.smul_def, map_mul, mul_smul, hr, algebraMap_smul]⟩
  have hex : ∀ w : FinPl K, ∃ x : 𝓞 K, x ∈ w.1 ∧ x ∉ w.1 ^ 2 := fun w => by
    obtain ⟨x, hx, hx'⟩ := Ideal.exists_mem_pow_notMem_pow_succ w.1 (finPl_ne_bot w) w.2.ne_top 1
    exact ⟨x, by simpa using hx, hx'⟩
  choose ϖ hϖ using hex
  refine ⟨i1, i2, ϖ, idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) M, modLat σ (idealSmul ((idealPow τ :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M), hϖ,
      rkK_idealSmul (idealPow_ne_zero τ) M, fun w => ?_, fun w => ?_⟩
  · rw [locScal_one]
    exact (local_ideal_pow K V w (ϖ w) (hϖ w).1 (hϖ w).2 τ M).le
  · rw [locScal_one, ← Finsupp.neg_apply]
    exact local_ideal_pow K V w (ϖ w) (hϖ w).1 (hϖ w).2 (-σ) _

end LocalTest

theorem weighted_mean_lemma_of_slopes : LemmaUFinitePlaceFamily := by
  intro K _ _ _ _ J _ _ V ι _ _ _ _ _ _ b X hX σ τ M N β Sg0 dr h hM hM0 hN hrk hβ hSg hdr
  refine Formalism.LFunctionChainParameters.WeightedMeanLemmas.weighted_mean_claimU J _ _ _ _ _ h dr _ Sg0 (fun u => ?_) hdr
    (slope_pair_of_slopes K J V ι b X hX σ τ M N β Sg0 dr hM hM0 hN hrk hβ hSg)
  have hfd : FiniteDimensional K (V u) := Module.Finite.of_basis (b u)
  exact_mod_cast rkK_pos (hM0 u)

end Formalism.LFunctionChainParameters.slopeLatticeData
