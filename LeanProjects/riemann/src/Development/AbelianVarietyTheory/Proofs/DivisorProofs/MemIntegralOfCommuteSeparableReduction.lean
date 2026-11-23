import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntMatSep

theorem nilp_eq_zero_of_commute_sep_alg {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  set f := Matrix.toLin' A
  have hcp : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' N) := hc.map Matrix.toLinAlgEquiv'
  have hNl : IsNilpotent (Matrix.toLin' N) := hN.map Matrix.toLinAlgEquiv'
  obtain ⟨k, hk⟩ := hNl
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤ LinearMap.ker (Matrix.toLin' N) := fun μ v hv => by
    have h1 : Module.finrank K (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hcp]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have h2 : Module.finrank K (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨_, Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv⟩
    have hc' : Matrix.toLin' N v = c • v := (congrArg Subtype.val hc).symm
    have hpow : ∀ m : ℕ, (Matrix.toLin' N ^ m) v = c ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc', smul_smul, pow_succ]
    have h5 : c ^ k • v = 0 := by rw [← hpow, hk]; rfl
    have hc0 : c = 0 := by
      rcases smul_eq_zero.1 h5 with h | h
      · exact pow_eq_zero_iff'.1 h |>.1
      · exact absurd h h0
    rw [LinearMap.mem_ker, hc', hc0, zero_smul]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top] at h3
  exact Matrix.toLin'.injective (by rw [h3, map_zero])

theorem nilp_eq_zero_of_commute_sep {K : Type} [Field K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  have h := nilp_eq_zero_of_commute_sep_alg (K := AlgebraicClosure K)
    (A := A.map (algebraMap K (AlgebraicClosure K))) (N := N.map (algebraMap K (AlgebraicClosure K)))
    (by rw [Matrix.charpoly_map]; exact hA.map) (hN.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
    (hc.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

theorem exists_lt_pow (x B : WithZero (Multiplicative ℤ)) (hx : 1 < x) : ∃ m : ℕ, B < x ^ m := by
  obtain ⟨k, hk⟩ := MulArchimedean.arch B hx
  refine ⟨k + 1, hk.trans_lt ?_⟩
  have h0 : x ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hx))
  rw [pow_succ]
  simpa using mul_lt_mul_of_pos_left hx (zero_lt_iff.2 h0)

theorem integral_of_commute_sep : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ) (P₀ : (w.adicCompletionIntegers E)[X]),
    IsCoprime P₀ (derivative P₀) →
    ∀ (A s : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, A i j ∈ w.adicCompletionIntegers E) →
    A.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → Commute s A →
    (∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℕ) (i j : Fin n), Valued.v ((s ^ k) i j) ≤ B) →
    ∀ i j, s i j ∈ w.adicCompletionIntegers E := by
  intro E _ _ w n P₀ hP A s hA hAc hsA hBd i j
  obtain ⟨B, hB⟩ := hBd
  have memO : ∀ x : w.adicCompletion E, x ∈ w.adicCompletionIntegers E ↔ Valued.v x ≤ 1 :=
    fun x => HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w
  by_contra hij
  haveI : Nonempty (Fin n × Fin n) := ⟨(i, j)⟩
  obtain ⟨⟨i₀, j₀⟩, hmax⟩ := Finite.exists_max (fun p : Fin n × Fin n => Valued.v (s p.1 p.2))
  have hc1 : 1 < Valued.v (s i₀ j₀) := by
    have : 1 < Valued.v (s i j) := not_le.1 (fun h => hij ((memO _).2 h))
    exact this.trans_le (hmax (i, j))
  have hvc : Valued.v (s i₀ j₀) ≠ 0 := ne_of_gt (zero_lt_one.trans hc1)
  have hc0 : s i₀ j₀ ≠ 0 := fun h => hvc (by rw [h, map_zero])
  set c := s i₀ j₀ with hcdef
  set u := c⁻¹ • s with hudef
  have hu : ∀ k l, u k l ∈ w.adicCompletionIntegers E := by
    intro k l
    rw [memO]
    simp only [u, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 hvc), mul_one]
    exact hmax (k, l)
  let A₀ : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := fun k l => ⟨A k l, hA k l⟩
  let u₀ : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := fun k l => ⟨u k l, hu k l⟩
  have hinj : Function.Injective (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hA₀ : A₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = A := by
    ext; rfl
  have hu₀ : u₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = u := by
    ext; rfl
  have hcomm : Commute A₀ u₀ := by
    apply Matrix.map_injective hinj
    show (A₀ * u₀).map _ = (u₀ * A₀).map _
    rw [Matrix.map_mul, Matrix.map_mul, hA₀, hu₀]
    exact ((hsA.smul_left c⁻¹).symm).eq
  have hcp : A₀.charpoly = P₀ := by
    apply Polynomial.map_injective _ hinj
    rw [← Matrix.charpoly_map, hA₀, hAc]
  obtain ⟨m, hm⟩ := exists_lt_pow (Valued.v c) B hc1
  have hsmall : ∀ k l, Valued.v ((u ^ m) k l) < 1 := by
    intro k l
    rw [hudef, _root_.smul_pow, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_inv₀, inv_pow,
      inv_mul_lt_iff₀ (pow_pos (zero_lt_iff.2 hvc) _), mul_one]
    exact (hB m k l).trans_lt hm
  have hnil : IsNilpotent (u₀.map (IsLocalRing.residue (w.adicCompletionIntegers E))) := by
    refine ⟨m, ?_⟩
    rw [← Matrix.map_pow]
    ext k l
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨y, hy⟩
    have e : (((u₀ ^ m) k l : w.adicCompletionIntegers E) : w.adicCompletion E) = (u ^ m) k l := by
      rw [← hu₀, ← Matrix.map_pow]; rfl
    have h1 := hsmall k l
    rw [← e, ← hy] at h1
    have h2 : Valued.v (((y : w.adicCompletionIntegers E) : w.adicCompletion E)) *
        Valued.v (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) = 1 := by
      have hy1 : ((y : w.adicCompletionIntegers E) : w.adicCompletion E) *
          (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) = 1 := by
        first
          | exact congrArg Subtype.val y.mul_inv
          | exact_mod_cast congrArg Subtype.val y.mul_inv
          | simp
      rw [← map_mul, hy1, map_one]
    have h3 := (memO _).1 (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E)).2
    have h4 : Valued.v (((y : w.adicCompletionIntegers E) : w.adicCompletion E)) *
        Valued.v (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h3) h1
    rw [h2] at h4
    exact lt_irrefl _ h4
  have hsep : (A₀.map (IsLocalRing.residue (w.adicCompletionIntegers E))).charpoly.Separable := by
    rw [Matrix.charpoly_map, hcp]
    exact Polynomial.Separable.map hP
  have h0 := nilp_eq_zero_of_commute_sep hsep hnil
    (hcomm.map (IsLocalRing.residue (w.adicCompletionIntegers E)).mapMatrix)
  have hone : u₀ i₀ j₀ = 1 := by
    apply Subtype.ext
    show c⁻¹ * c = 1
    exact inv_mul_cancel₀ hc0
  have := congrFun (congrFun h0 i₀) j₀
  simp only [Matrix.map_apply, Matrix.zero_apply, hone, map_one] at this
  exact one_ne_zero this

end GlobalTheory.IntMatSep
