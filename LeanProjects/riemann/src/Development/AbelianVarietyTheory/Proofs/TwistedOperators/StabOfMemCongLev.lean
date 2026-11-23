import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct

variable {D : D7}

theorem exists_F_mem {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D S P) :
    ∃ X : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) X ∈ 𝔪 ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) X ∉ P.asIdeal := by
  classical
  choose! x hx hxP using hP
  have hz : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ v ∈ S, x v) ∈ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪 (le_bot_iff.1 (h ▸ hJ))
    let Q : HeightOneSpectrum (𝓞 D.host.E) := ⟨J, hJp, hJ0⟩
    have hv := hS Q hJ
    have hxv : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (x (Q.under (𝓞 D.host.F))) ∈ J := hx _ hv
    rw [map_prod, ← Finset.prod_erase_mul _ _ hv]
    exact Ideal.mul_mem_left J _ hxv
  obtain ⟨K, hK⟩ := hz
  refine ⟨(∏ v ∈ S, x v) ^ K, by rwa [map_pow], fun h => ?_⟩
  rw [map_pow] at h
  have h1 := P.isPrime.mem_of_pow_mem K h
  rw [map_prod] at h1
  obtain ⟨v, hv, h2⟩ := (P.isPrime.prod_mem_iff).1 h1
  exact hxP v hv _ rfl h2

theorem oToS_smul_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ 𝔪)
    {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    oToS F E a • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine Submodule.subset_span ⟨a • l, Submodule.smul_mem_smul ha hl, ?_⟩
    funext i
    simp [Subring.smul_def, oToS_coe]
    simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ b hx

end GlobalTheory.CongMember

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem comp_sub_one {R : Type} [CommRing R] (u : R) (hu : u * u = u) (A B K : Matrix (Fin n) (Fin n) R)
    (hA : u • (A - 1) = A - 1) (hB : (1 - u) • (B - 1) = B - 1) (hK : K = A * B ∨ K = B * A) : A - 1 = u • (K - 1) := by
  have e1 : u • B = u • 1 := by
    rw [← sub_eq_zero, ← smul_sub, ← hB, smul_smul, mul_sub, mul_one, hu, sub_self, zero_smul]
  have e2 : u • K = u • A := by
    rcases hK with rfl | rfl
    · rw [← Matrix.mul_smul, e1, Matrix.mul_smul, Matrix.mul_one]
    · rw [← Matrix.smul_mul, e1, Matrix.smul_mul, Matrix.one_mul]
  rw [smul_sub, e2, ← smul_sub, hA]

theorem cong_of_eq (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ 𝔪)
    (u : Formalism.L2.Herm.intAf F E) (A K : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (e : A - 1 = ((u * oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) • (K - 1))
    (hK : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, K *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, A *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  intro y hy
  have e1 : A *ᵥ y - y = (A - 1) *ᵥ y := by rw [sub_mulVec, one_mulVec]
  have e2 : K *ᵥ y - y = (K - 1) *ᵥ y := by rw [sub_mulVec, one_mulVec]
  have e' : A *ᵥ y - y = (u * oToS F E a) • (K *ᵥ y - y) := by
    rw [e1, e2, e, Matrix.smul_mulVec, Subring.smul_def]
  rw [e', mul_smul]
  exact Submodule.smul_mem _ u (oToS_smul_mem_hatL Λ ha (Submodule.sub_mem _ (hK y hy) hy))

theorem hatL_smul_le (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) :
    Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) ≤ Formalism.L2.Herm.hatL (F := F) Λ :=
  Submodule.span_mono (Set.image_mono Submodule.smul_le_right)

theorem mem_congLev_of [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (𝔪 : Ideal (𝓞 E)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hU : x ∈ UA hc J)
    (h1 : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ))
    (h2 : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x⁻¹).1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    x ∈ congLev hc J Λ 𝔪 := by
  refine ⟨hU, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, h1⟩
  · have := Submodule.add_mem _ (hatL_smul_le Λ 𝔪 (h1 y hy)) hy
    rwa [sub_add_cancel] at this
  · have := Submodule.add_mem _ (hatL_smul_le Λ 𝔪 (h2 _ hy)) hy
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec, sub_add_cancel] at this

theorem stab_of_mem_congLev [StarRing E] {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {Λ : Submodule (𝓞 E) (Fin n → E)}
    {𝔪 : Ideal (𝓞 E)} {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ congLev hc J Λ 𝔪) :
    (∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ) ∧
      ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
  ⟨fun y hy => (hx.2.1 y).1 hy, fun y hy => ((Subgroup.inv_mem _ hx).2.1 y).1 hy⟩

end General

variable {D : D7}

theorem exists_idem_eq {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D S P) {e f : Formalism.L2.Theta.AE D} (hi : IsPrimeIdem P e f) :
    ∃ a ∈ 𝔪, ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      ((u * oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) = GlobalTheory.LevSplit.finSw D f := by
  obtain ⟨X, hX𝔪, hXP⟩ := exists_F_mem h𝔪 hS hP
  obtain ⟨u, hu⟩ := GlobalTheory.LevSplit.idem_div_int hi _ _ ((D.sp.cm.fixed _).2 ⟨(X : D.host.F), rfl⟩).symm hXP hXP
  exact ⟨_, hX𝔪, u, hu⟩

end GlobalTheory.CongMember
