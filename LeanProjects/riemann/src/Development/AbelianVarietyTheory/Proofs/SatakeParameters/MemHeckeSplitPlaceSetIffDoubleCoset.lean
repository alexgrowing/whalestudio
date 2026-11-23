import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfSupportedAtSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceProjMemIntegersOfIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TSetDoubleCoset

theorem trivOutside_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  have e : ((x * y : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [e, Matrix.map_mul, hx v hv, hy v hv, Matrix.mul_one]

theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem loc_mem_GLint {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    {k : GA L n} (hk : k ∈ Umax L n) :
    s.loc n k ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
  apply mem_GLint_of_entries
  · intro a b
    exact GlobalTheory.splitPlace_proj_mem_integers_of_integral s (hk a b)
  · intro a b
    rw [← map_inv]
    exact GlobalTheory.splitPlace_proj_mem_integers_of_integral s ((Umax L n).inv_mem hk a b)

theorem mem_tSet_iff : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (sp : SplitPlace L) (ϖ : (sp.v).adicCompletion (maximalRealSubfield L)) (k : ℕ), ∀ x₀ ∈ Formalism.AUTREP.tSet L n sp ϖ k, ∀ κ, κ ∈ Formalism.AUTREP.tSet L n sp ϖ k ↔ ∃ k₁, (k₁ ∈ Umax L n ∧ TrivOutside {sp.v} k₁) ∧ ∃ k₂, (k₂ ∈ Umax L n ∧ TrivOutside {sp.v} k₂) ∧ κ = k₁ * x₀ * k₂ := by
  intro L _ _ _ n sp ϖ k x₀ hx₀ κ
  obtain ⟨hx₀t, a₀, ha₀, b₀, hb₀, hx₀e⟩ := hx₀
  constructor
  · rintro ⟨hκt, a, ha, b, hb, hκe⟩
    obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n sp
    have hg : a * a₀⁻¹ ∈ Formalism.UG.GLint (Fin n) (sp.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :=
      mul_mem ha (inv_mem ha₀)
    have hg' : b₀⁻¹ * b ∈ Formalism.UG.GLint (Fin n) (sp.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :=
      mul_mem (inv_mem hb₀) hb
    refine ⟨e (a * a₀⁻¹), ⟨GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp _ (he1 _) (by rw [he2]; exact hg), he1 _⟩,
      e (b₀⁻¹ * b), ⟨GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp _ (he1 _) (by rw [he2]; exact hg'), he1 _⟩, ?_⟩
    apply GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n sp
    · exact hκt
    · exact trivOutside_mul (trivOutside_mul (he1 _) hx₀t) (he1 _)
    · rw [map_mul, map_mul, he2, he2]
      apply Units.ext
      simp only [Units.val_mul]
      rw [hκe, hx₀e]
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]
  · rintro ⟨k₁, ⟨hk₁, hk₁t⟩, k₂, ⟨hk₂, hk₂t⟩, rfl⟩
    refine ⟨trivOutside_mul (trivOutside_mul hk₁t hx₀t) hk₂t, sp.loc n k₁ * a₀,
      mul_mem (loc_mem_GLint sp hk₁) ha₀, b₀ * sp.loc n k₂, mul_mem hb₀ (loc_mem_GLint sp hk₂), ?_⟩
    rw [map_mul, map_mul]
    simp only [Units.val_mul]
    rw [hx₀e]
    simp only [Matrix.mul_assoc]

end GlobalTheory.TSetDoubleCoset
