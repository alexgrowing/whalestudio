import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSecGeneric
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsModelAtIntegralIffMemLieLat
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeOfIsLocalModelAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDvrModelLieBasisAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFractionalIdealLocalGenOfValuationStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDetIdealLocalGenFullLatticeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KeyLocAtOfIsLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosKeyArchAtStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_common_denominator_of_valuation_le_one {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (a : Fin n → K) (ha : ∀ m, p.valuation K (a m) ≤ 1) :
    ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ ∀ m, ∃ b : 𝓞 K, s • a m = algebraMap (𝓞 K) K b := by
  choose nn dd hnd using fun m => p.exists_primeCompl_mul_eq_of_integer (a m) (ha m)
  have hs : (∏ m, (dd m : 𝓞 K)) ∈ p.asIdeal.primeCompl := prod_mem fun m _ => (dd m).2
  refine ⟨∏ m, (dd m : 𝓞 K), hs, fun m => ?_⟩
  refine ⟨nn m * ∏ j ∈ Finset.univ.erase m, (dd j : 𝓞 K), ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), Algebra.smul_def]
  simp only [map_mul]
  rw [← hnd m]
  ring

theorem IsModelAt.rows_span_lieLat {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K}
    {φ : x.P.A.left ⟶ A.A.left} (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) {p : HeightOneSpectrum (𝓞 K)}
    {M : Matrix (Fin x.P.g) (Fin x.P.g) K} (hM : IsModelAt A x φ p M) :
    (∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • M i ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat) ∧
      ∀ c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧
        s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i) := by
  have hdet : M.det ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, -, h, -⟩ := hM
    exact h
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have key := isModelAt_integral_iff_mem_lieLat K A x φ hf p M hM
  refine ⟨fun i => (key (M i)).mp fun m => ?_, fun c hc => ?_⟩
  · have h1 : Matrix.vecMul (M i) M⁻¹ m = (1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i m := by
      rw [← Matrix.mul_nonsing_inv (A := M) hu]
      rfl
    rw [h1, Matrix.one_apply]
    split_ifs <;> simp
  · have hone : (1 : 𝓞 K) ∉ p.asIdeal := fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    have hv := (key c).mpr ⟨1, hone, by simpa using hc⟩
    obtain ⟨s, hs, hb⟩ := exists_common_denominator_of_valuation_le_one p (Matrix.vecMul c M⁻¹) hv
    choose b hb using hb
    refine ⟨s, hs, ?_⟩
    have hc' : c = ∑ m, Matrix.vecMul c M⁻¹ m • M m := by
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul (A := M) hu, Matrix.vecMul_one]
    rw [hc', Finset.smul_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [← smul_assoc, hb m, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

theorem exists_keyLines : Out.SecTwistSt → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∃ T abelian₂ : MLine K, T.Good ∧ abelian₂.Good ∧ (∀ p, KeyLocAt x T abelian₂ p) ∧ (∀ σ, KeyArchAt x T abelian₂ σ) ∧ ∀ p, ∃ M, IsModelAt A x φ p M ∧ IsLocGen p M.det abelian₂.I := by
  intro hT hU _hL hH K _ _ A x φ hfib
  have hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).mp hfib
  let F : GenFib A := GenFib.mk x.P φ hf x.v x.basis
  obtain ⟨hFG, hspan⟩ := GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K A F
  obtain ⟨IL, hIL0, hIL⟩ := GlobalTheory.T.exists_detIdeal_localGen_full_lattice K x.P.g F.lieLat hFG hspan
  obtain ⟨δ, oa, nth, hloc, -, hsupp, -⟩ :=
    GlobalTheory.ThetaDegree.exists_isThetaDeg hT hU K A F x.g_pos x.rig x.rig_gen x.th x.6
  obtain ⟨IT, hIT0, hIT⟩ := GlobalTheory.T.exists_fractionalIdeal_localGen_of_valuation K oa hsupp
  choose t n ht hn hArch using fun σ => GlobalTheory.T.exists_pos_keyArchAt' hU K x σ
  refine ⟨⟨IT, t⟩, ⟨IL, n⟩, And.intro hIT0 ht, And.intro hIL0 hn, fun p => ?_,
    fun σ => hArch σ _ _ rfl rfl, fun p => ?_⟩
  · obtain ⟨a, M, hM, hva⟩ := hloc p
    have hrows := GlobalTheory.T.lieLattice_of_isLocalModel_at_prime hH K A F x.g_pos x.rig x.rig_gen x.th x.6 p a M hM
    exact GlobalTheory.T.keyLocAt_of_isLocalModel' K x ⟨IT, t⟩ ⟨IL, n⟩ p a M hM (hIT p a hva) (hIL p M hrows.1 hrows.2)
  · obtain ⟨M, hM⟩ := GlobalTheory.T.exists_dvrModel_lieBasis_at_prime hT K A x φ hfib p
    have hrows := hM.rows_span_lieLat hf
    exact ⟨M, hM, hIL p M hrows.1 hrows.2⟩

end GlobalTheory.LamF
