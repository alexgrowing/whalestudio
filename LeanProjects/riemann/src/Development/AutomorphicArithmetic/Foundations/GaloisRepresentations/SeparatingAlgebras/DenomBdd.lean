import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound

open GlobalTheory.CongW (IntMat)

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private lemma natCast_int (u : HeightOneSpectrum (𝓞 E)) (l : ℕ) :
    (l : u.adicCompletion E) ∈ u.adicCompletionIntegers E :=
  _root_.natCast_mem (u.adicCompletionIntegers E) l

private lemma v_lt_one (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) :
    Valued.v (l : u.adicCompletion E) < 1 := by
  have h := (u.valuation_lt_one_iff_mem (K := E) ((l : ℕ) : 𝓞 E)).2 hu
  have h2 := u.valuedAdicCompletion_eq_valuation (K := E) ((l : ℕ) : 𝓞 E)
  rw [← h2] at h
  simpa using h

private lemma exists_pow_int (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (y : u.adicCompletion E) : ∃ d : ℕ, (l : u.adicCompletion E) ^ d * y ∈ u.adicCompletionIntegers E := by
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  obtain ⟨d, hd⟩ := exists_pow_lt₀ (v_lt_one u hu) (Units.mk0 _ (inv_ne_zero hv))
  refine ⟨d, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow]
  have h0 : (0 : _) < Valued.v y := zero_lt_iff.2 hv
  have := mul_le_mul_left (le_of_lt hd) (Valued.v y)
  simpa [hv] using this

private lemma intMat_mono (u : HeightOneSpectrum (𝓞 E)) (l : ℕ) (m : Matrix (Fin a) (Fin a) (u.adicCompletion E))
    {d e : ℕ} (hde : d ≤ e) (h : IntMat u ((l : u.adicCompletion E) ^ d • m)) :
    IntMat u ((l : u.adicCompletion E) ^ e • m) := by
  intro i j
  have h1 := h i j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1 ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde
  rw [pow_add, mul_comm (_ ^ d), mul_assoc]
  exact mul_mem (pow_mem (natCast_int u l) k) h1

private lemma exists_intMat (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (m : Matrix (Fin a) (Fin a) (u.adicCompletion E)) :
    ∃ d : ℕ, IntMat u ((l : u.adicCompletion E) ^ d • m) := by
  choose D hD using fun p : Fin a × Fin a => exists_pow_int u hu (m p.1 p.2)
  refine ⟨Finset.univ.sup D, fun i j => ?_⟩
  have hle : D (i, j) ≤ Finset.univ.sup D := Finset.le_sup (Finset.mem_univ _)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [hk, pow_add, mul_comm (_ ^ D (i, j)), mul_assoc]
  exact mul_mem (pow_mem (natCast_int u l) k) (hD (i, j))

private lemma isOpen_intMat {X : Type*} [TopologicalSpace X] (u : HeightOneSpectrum (𝓞 E)) (c : u.adicCompletion E)
    (f : X → Matrix (Fin a) (Fin a) (u.adicCompletion E)) (hf : Continuous f) :
    IsOpen {x | IntMat u (c • f x)} := by
  have e : {x | IntMat u (c • f x)} = ⋂ i, ⋂ j, {x | c * f x i j ∈ u.adicCompletionIntegers E} := by
    ext x
    simp [IntMat]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  have hc : Continuous fun x => c * f x i j :=
    continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp hf))
  exact (GroundTheory.Global.isOpen_adicCompletionIntegers u).preimage hc

end

end UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound

open GlobalTheory.CongW (IntMat) in
open UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound in
theorem UpperTheory.Gal.Gen.denomBdd_pf :
    UpperTheory.Gal.Gen.DenomBdd := by
  intro E _ _ _ l hl n Z hZ
  have hl0 : ((l : ℕ) : 𝓞 E) ≠ 0 := by
    exact_mod_cast hl.ne_zero
  have hS : {u : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ u.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 E)}) ?_).subset ?_
    · simpa using hl0
    · intro u hu
      exact Ideal.dvd_span_singleton.2 hu
  have hopen : ∀ d : ℕ, IsOpen {g : UA E n | DenomLe l d g} := by
    intro d
    have e : {g : UA E n | DenomLe l d g} = ⋂ u ∈ {u : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ u.asIdeal},
        ({g : UA E n | IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E)))} ∩
        {g : UA E n | IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E)))}) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, DenomLe]
    rw [e]
    refine hS.isOpen_biInter fun u _ => ?_
    exact (isOpen_intMat u _ _ (Units.continuous_val.comp (GlobalTheory.BCT.GlobLev.continuous_cLoc u))).inter
      (isOpen_intMat u _ _ (Units.continuous_coe_inv.comp (GlobalTheory.BCT.GlobLev.continuous_cLoc u)))
  have hmono : ∀ {d e : ℕ}, d ≤ e → ∀ g : UA E n, DenomLe l d g → DenomLe l e g :=
    fun hde g h u hu => ⟨intMat_mono u l _ hde (h u hu).1, intMat_mono u l _ hde (h u hu).2⟩
  have hcover : ∀ g : UA E n, ∃ d : ℕ, DenomLe l d g := by
    intro g
    have h1 : ∀ u : HeightOneSpectrum (𝓞 E), ∃ d : ℕ, ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
        IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))) ∧
        IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))) := by
      intro u
      by_cases hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal
      · obtain ⟨d₁, h₁⟩ := exists_intMat u hu ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))
        obtain ⟨d₂, h₂⟩ := exists_intMat u hu (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))
        exact ⟨max d₁ d₂, fun _ => ⟨intMat_mono u l _ (le_max_left _ _) h₁, intMat_mono u l _ (le_max_right _ _) h₂⟩⟩
      · exact ⟨0, fun h => absurd h hu⟩
    choose D hD using h1
    refine ⟨hS.toFinset.sup D, fun u hu => ?_⟩
    have hle : D u ≤ hS.toFinset.sup D := Finset.le_sup (hS.mem_toFinset.2 hu)
    exact ⟨intMat_mono u l _ hle (hD u hu).1, intMat_mono u l _ hle (hD u hu).2⟩
  obtain ⟨d, hd⟩ := hZ.elim_directed_cover (fun d : ℕ => {g : UA E n | DenomLe l d g}) hopen
    (fun g _ => Set.mem_iUnion.2 (hcover g))
    (directed_of_isDirected_le fun _ _ hde g hg => hmono hde g hg)
  exact ⟨d, fun g hg => hd hg⟩
