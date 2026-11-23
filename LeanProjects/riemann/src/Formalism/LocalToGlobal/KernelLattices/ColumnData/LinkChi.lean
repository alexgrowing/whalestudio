import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

private theorem circle_pow_surj' {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Circle => a ^ n) := by
  intro z
  refine ⟨Circle.exp (Complex.arg z / n), ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  change Circle.exp (Complex.arg z / n) ^ n = z
  rw [← Circle.exp_zsmul, zsmul_eq_mul, mul_div_cancel₀ _ hn', Circle.exp_arg]

theorem circle_extend' {M N : Type} [CommGroup M] [CommGroup N] (f : M →* N)
    (hf : Function.Injective f) (g : M →* Circle) : ∃ h : N →* Circle, ∀ x, h (f x) = g x := by
  let _ : DivisibleBy (Additive Circle) ℤ :=
    divisibleByOfSMulRightSurj (Additive Circle) ℤ (fun hn => circle_pow_surj' hn)
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive f) hf (MonoidHom.toAdditive g)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  exact DFunLike.congr_fun hh (Additive.ofMul x)

theorem host_star_emb (D : Car) (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ (@star D.host.E (@InvolutiveStar.toStar _ (@StarMul.toInvolutiveStar _ _
      (@StarRing.toStarMul _ _ D.host.cmStar))) x) = (starRingEnd ℂ) (φ x) := by
  haveI := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ x

open Classical in
theorem character_linkage_holds : LinkChi := by
  intro D _
  letI := D.host.cmStar

  have hnorm : ∀ (φ : D.host.E →+* ℂ) (z : unitary D.host.E), ‖φ (z : D.host.E)‖ = 1 := by
    intro φ z
    have h1 : φ (star (z : D.host.E)) * φ (z : D.host.E) = 1 := by
      rw [← map_mul, z.2.1, map_one]
    rw [host_star_emb D φ] at h1
    have h2 : ((Complex.normSq (φ (z : D.host.E)) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]; exact h1
    have h3 : Complex.normSq (φ (z : D.host.E)) = 1 := by exact_mod_cast h2
    rw [Complex.normSq_eq_norm_sq] at h3
    have := norm_nonneg (φ (z : D.host.E))
    nlinarith

  let s : unitary D.host.E →* Submodule (𝓞 D.host.E) D.host.E :=
    { toFun := fun z => Submodule.span (𝓞 D.host.E) {(z : D.host.E)}
      map_one' := by
        change Submodule.span (𝓞 D.host.E) {(1 : D.host.E)} = 1
        rw [Submodule.one_eq_span]
      map_mul' := fun a b => by
        change Submodule.span (𝓞 D.host.E) {(a : D.host.E) * (b : D.host.E)} =
          Submodule.span (𝓞 D.host.E) {(a : D.host.E)} * Submodule.span (𝓞 D.host.E) {(b : D.host.E)}
        rw [Submodule.span_mul_span, Set.singleton_mul_singleton] }
  let ι : unitary D.host.E →* (Submodule (𝓞 D.host.E) D.host.E)ˣ := s.toHomUnits

  have hK : ∀ z : unitary D.host.E, ι z = 1 → ∃ m : ℕ, 0 < m ∧ (z : D.host.E) ^ m = 1 := by
    intro z hz
    have hs : Submodule.span (𝓞 D.host.E) {(z : D.host.E)} = 1 := by
      have := congrArg Units.val hz
      simpa [ι, s] using this
    have hmem : (z : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      rw [← hs]; exact Submodule.subset_span rfl
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 hmem
    have hint : IsIntegral ℤ (z : D.host.E) := by
      rw [← hy]; exact RingOfIntegers.isIntegral_coe y
    obtain ⟨m, hm, hzm⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one D.host.E ℂ hint
      (fun φ => hnorm φ z)
    exact ⟨m, hm, hzm⟩

  let n : unitary D.host.E →* Circle :=
    { toFun := fun z => ⟨∏ τ : D.what₂.Tau, (embT D τ (z : D.host.E))⁻¹, by
        change _ ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm, norm_prod]
        exact Finset.prod_eq_one fun τ _ => by rw [norm_inv, hnorm _ z, inv_one]⟩
      map_one' := by
        apply Circle.ext
        simp
      map_mul' := fun a b => by
        apply Circle.ext
        change (∏ τ : D.what₂.Tau, (embT D τ ((a * b : unitary D.host.E) : D.host.E))⁻¹) =
          (∏ τ : D.what₂.Tau, (embT D τ (a : D.host.E))⁻¹) * ∏ τ : D.what₂.Tau, (embT D τ (b : D.host.E))⁻¹
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun τ _ => ?_
        rw [Submonoid.coe_mul, map_mul, mul_inv] }
  have hn : ∀ z : unitary D.host.E, ((n z : Circle) : ℂ) = ∏ τ : D.what₂.Tau, (embT D τ (z : D.host.E))⁻¹ :=
    fun z => rfl
  have hker : ι.ker ≤ n.ker := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz ⊢
    apply Circle.ext
    rw [hn]
    exact UpperTheory.Mu.prod_emb_inv D.host D.eTau (hK z hz)
  obtain ⟨h, hh⟩ := circle_extend' (QuotientGroup.kerLift ι) (QuotientGroup.kerLift_injective ι)
    (QuotientGroup.lift ι.ker n hker)
  refine ⟨fun 𝔞 => if hu : IsUnit 𝔞 then ((h hu.unit : Circle) : ℂ) else 0, ?_, ?_⟩
  · intro 𝔞 𝔟 ha hb
    obtain ⟨𝔞', -, ha'⟩ := ha
    obtain ⟨𝔟', -, hb'⟩ := hb
    have hua : IsUnit 𝔞 := isUnit_iff_exists_inv.2 ⟨_, ha'⟩
    have hub : IsUnit 𝔟 := isUnit_iff_exists_inv.2 ⟨_, hb'⟩
    have hu : IsUnit (𝔞 * 𝔟) := hua.mul hub
    have hunit : hu.unit = hua.unit * hub.unit := Units.ext rfl
    simp only [dif_pos hu, dif_pos hua, dif_pos hub, hunit, map_mul, Circle.coe_mul]
  · intro z
    have hu : IsUnit (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}) := (ι z).isUnit
    have hunit : hu.unit = ι z := Units.ext rfl
    simp only [dif_pos hu, hunit]
    have := hh (QuotientGroup.mk z)
    rw [QuotientGroup.kerLift_mk, QuotientGroup.lift_mk] at this
    rw [this, hn]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
