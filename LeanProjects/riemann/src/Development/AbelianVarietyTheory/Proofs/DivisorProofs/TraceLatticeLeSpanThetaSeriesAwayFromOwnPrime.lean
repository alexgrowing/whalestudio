import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrbitFamilyAdaptedLatticeSplitSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceShortSeriesEqMulAdelicSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulCoeffIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaKernelTameCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorEqTranslateKernelDatumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompareOff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Formalism.HermitianLatticesTheory (localization₂)

theorem mem_localization_iff {Rr W : Type} [CommRing Rr] [AddCommGroup W] [Module Rr W] (p : Ideal Rr) [p.IsPrime]
    (L : Submodule Rr W) (x : W) : x ∈ localization₂ p L ↔ ∃ s : Rr, s ∉ p ∧ s • x ∈ L :=
  ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩⟩

theorem localization_le_of_le_localization' {Rr W : Type} [CommRing Rr] [AddCommGroup W] [Module Rr W] (p : Ideal Rr) [p.IsPrime]
    (L M : Submodule Rr W) (h : L ≤ localization₂ p M) : localization₂ p L ≤ localization₂ p M := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_localization_iff p L x).1 hx
  obtain ⟨t, ht, hy⟩ := (mem_localization_iff p M _).1 (h hx)
  refine (mem_localization_iff p M x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hm with h1 | h1
  · exact ht h1
  · exact hs h1

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] (lam : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime)
    (hne : Formalism.EigenvalueLevelCeiling.plc lam ≠ p) : ((p : 𝓞 K)) ∉ lam.asIdeal := by
  intro hm
  haveI : lam.asIdeal.IsPrime := lam.isPrime
  have h0 : ((p : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  have hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ p := ringChar.dvd h0
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact hne h1

theorem splitOffBad_of_mul {D : D7} {V : HSp D} {a b : ℕ} {h : GA D V} (H : SplitOffBad V (a * b) h) : SplitOffBad V a h := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := H
  refine ⟨h1, e, P, h2, fun PP hPP hm => h3 PP hPP ?_, h4⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hm

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem singleSeries_transl (R : RealDat D A Ks) (i : Fin D.R.m) {ξ χ ξR Q ω φ} (hK : KerDat R i ξ χ ξR Q ω φ)
    {k : GA D (Vc D i)} (hk : k ∈ GfC (Vc D i)) (c : ℂ) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    singleSeries R i ω (c • ω (k, 1) φ) h w v = c • singleSeries R i ω φ (h * k) w v := by
  funext g
  have hθ : IsInfFam R.θ := hK.vec.1.2.inf
  have hth := GlobalTheory.VecTheta.isThetaFunO_thPVec hK.vec
  simp only [singleSeries, Datum.thetaKO, Pi.smul_apply]
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ ω hK.weil R.θ hθ k hk 1
    (one_mem _) _ _ _ _ φ _ hth, map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem compareOffOwn_run : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ), CompareOffOwn hT.p fw i ℓ U ψ 1 v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hPins hβ hLU hIo hRow hPh hCS v hv hmu hQG hFO hVal hξ hMb hRun ℓ hLev hAct U hdetU ψ
  intro lam hlam
  refine localization_le_of_le_localization' _ _ _ (Submodule.span_le.2 ?_)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, s, f', Λ, h, N, x₀, P, x, hs, hsf, hSplit, hLat, hΛlam, hUni, hTriv, hTrivM, hLevN, hAdm, hP, hx⟩ :=
    GlobalTheory.T.exists_orbit_family_adapted_lattice_split_support D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins ℓ U lam f hf
  obtain ⟨y, s', hy, hs', hyLat⟩ := GlobalTheory.HarmInCoef.harm_mem_coefLat D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins Λ h (splitOffBad_of_mul hSplit) hLat lam hΛlam P hP
  obtain ⟨ω, φ, hBase⟩ := GlobalTheory.OnCmp.exists_baseKernel D G Pl0 T0 A T.J.Q.c.F R F hC i v hv hmu
  obtain ⟨χ, ξR, hKer⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel D G Pl0 T0 A T.J.Q.c.F R F hC i v hv hmu ω φ hBase
  have hEx := GlobalTheory.T.trace_shortSeries_eq_mul_adelicSeries D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins hβ hLU hIo hRow hPh hCS v hv hmu
    hQG hFO hVal hξ hMb hRun ℓ hLev hAct U hdetU ψ
  obtain ⟨y₀, c, hy₀, hcInt, hSer⟩ :=
    hEx χ ξR ω φ hKer Λ h hSplit hLat N x₀ P x f' y hUni hTriv hTrivM hLevN hAdm hP hx hy
  obtain ⟨φ', hVec, k, hk, c', m, hφ', hpc, -, hc'0, hLatk⟩ := GlobalTheory.T.freeLowerBlockVector_eq_translate_kernelDatum D G Pl0 T0 A T.J.Q.c.F R F hC i _ χ ξR _ ω φ hKer
    (ownAt D v) (fun PP hPP => by classical exact (Finset.mem_filter.1 hPP).2) hξ hVal y₀ hy₀
  obtain ⟨s'', hs'', hs''c⟩ := hcInt lam hΛlam
  obtain ⟨g', hg'⟩ : ∃ g', g' = ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f' u) := ⟨_, rfl⟩
  rw [← hg'] at hSer
  have hp : (ownAt D v).Prime := by
    rcases hFO.own with e | e <;> rw [e]
    exacts [D.host.pde_prime, D.host.pde'_prime]
  have hpl : ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ∉ lam.asIdeal := natCast_not_mem lam hp hlam
  have hA : ((s : ℕ) : D.what₂.LL) • (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) =
      algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) • g' := by
    classical
    have e1 : ∀ u, ((s : ℕ) : D.what₂.LL) • cuspTo hT.p fw i (f u) =
        algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) • cuspTo hT.p fw i (f' u) := by
      intro u
      have e2 : ((s : ℕ) : T.J.Q.c.F) • (show ↥(cutR T.J.C ((i : ℕ) + 1) (κ i)) from f u) =
          (show T.J.Q.c.F from (a : T.Q.c.F)) • (show ↥(cutR T.J.C ((i : ℕ) + 1) (κ i)) from f' u) :=
        Subtype.ext (hsf u)
      have e3 := congrArg (cutTo fw i) e2
      rw [map_smul, map_smul] at e3
      rw [← algebraMap_smul D.what₂.LL ((s : ℕ) : T.J.Q.c.F), ← algebraMap_smul D.what₂.LL (show T.J.Q.c.F from (a : T.Q.c.F)),
        map_natCast] at e3
      exact e3
    rw [hg', finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_comm, e1 u, smul_comm]
  have hdet : ∀ x : Fin (R.nW i) → D.what₂.LL,
      (∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i x (fun ρ => w ρ) = 0) → x = 0 := by
    intro x hx
    have h4 : (R.FW i).j (sg0 D A) x = 0 := by
      obtain ⟨u, hu, -⟩ := hIo i
      exact GlobalTheory.TraceIncl.eq_of_low (R := R) (i := i) hC.models.HW ⟨u, hu⟩
        (x := (R.FW i).j (sg0 D A) x) (y := 0) fun w => by rw [map_zero]; exact hx w
    by_contra hne
    exact ((hLU i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)).ne_zero 0 h4
  by_cases hc : c = 0
  · have hz : g' = 0 := hdet g' fun w => by rw [hSer φ' hVec w, hc, map_zero, zero_smul]
    refine (mem_localization_iff _ _ _).2 ⟨(s : 𝓞 D.what₂.LL), hs, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.what₂.LL, hA, hz, smul_zero]
    exact zero_mem _
  · have hs'n : s' ≠ 0 := by
      rintro rfl
      exact hs' (by simp)
    have hs'0 : (s' : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hs'n
    have hp0 : ((ownAt D v : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hc0 : c ≠ 0 := hc
    have hce : D.what₂.embLL c ≠ 0 := (map_ne_zero _).2 hc
    have hce' : D.what₂.embLL c' ≠ 0 := (map_ne_zero _).2 hc'0
    obtain ⟨e, he⟩ : ∃ e, e = (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (c * c')⁻¹) • g' := ⟨_, rfl⟩
    have hmem : e ∈ thetaBase R i U ψ 1 v (ownAt D v) := by
      refine Submodule.subset_span ⟨ω, φ, hKer.isKernel, h * k, mul_mem hSplit.1 hk,
        ((ownAt D v : ℂ)) ^ m • ((s' : ℂ) • (O i).c0' y), hLatk h hSplit.1 _ hyLat, fun w => ?_⟩
      rw [he, adForm_smul, MultilinearMap.smul_apply, hSer φ' hVec w, hφ', singleSeries_transl R i hKer hk,
        singleSeries_smul, singleSeries_smul, map_smul, map_smul, map_smul, one_smul, smul_smul, smul_smul, smul_smul]
      congr 1
      simp only [map_mul, map_inv₀, map_pow, map_natCast]
      field_simp
    have hgg : g' = (c * c' * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL))⁻¹) • e := by
      rw [he, smul_smul]
      conv_lhs => rw [← one_smul D.what₂.LL g']
      congr 1
      field_simp
    have hint : IsIntegral ℤ (algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) *
        (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c')) :=
      ((RingOfIntegers.isIntegral_coe a).algebraMap.mul hs''c).mul hpc
    have hpr := lam.isPrime
    have ht : ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal := by
      simp only [Ideal.IsPrime.mul_mem_iff_mem_or_mem hpr, not_or]
      exact ⟨⟨⟨⟨fun h1 => hpl (hpr.mem_of_pow_mem _ h1), fun h1 => hpl (hpr.mem_of_pow_mem _ h1)⟩, hs'⟩, hs''⟩, hs⟩
    refine (mem_localization_iff _ _ _).2 ⟨_, ht, ?_⟩
    have key : (((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL)) •
        (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) =
        (⟨_, hint⟩ : 𝓞 D.what₂.LL) • e := by
      rw [← algebraMap_smul D.what₂.LL, ← algebraMap_smul D.what₂.LL (⟨_, hint⟩ : 𝓞 D.what₂.LL)]
      have et : algebraMap (𝓞 D.what₂.LL) D.what₂.LL
          (((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL)) =
          ((ownAt D v : ℕ) : D.what₂.LL) ^ m * ((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (s'' : D.what₂.LL) *
            (s : D.what₂.LL) := by
        simp
      have hsc : ((ownAt D v : ℕ) : D.what₂.LL) ^ m * ((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (s'' : D.what₂.LL) *
          (algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * (c * c' * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL))⁻¹)) =
          algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c') := by
        field_simp
      rw [et, mul_smul, hA, hgg, smul_smul, smul_smul]
      congr 1
      show _ = algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c')
      rw [← hsc]
      ring
    rw [key]
    exact Submodule.smul_mem _ _ hmem

end GlobalTheory.CompareOff
