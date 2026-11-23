import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedTupleDataOfFixesSmallFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexLinearExtensionCoefficientMapStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaSeriesRationalVectorNeZeroOfCuspFormsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPhaseThetaSeriesExpandsCuspFormsSmallFieStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist GlobalTheory.SeriesTie GlobalTheory.BigOn.Exp
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.NormRatStd

section Steps

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}

theorem fixBase_of_fix (hRF : GlobalTheory.NT.RayField) {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀))
    (hti : TieIn T Rl.toRealDat κ v₀) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (j : Fin D.R.m) (τ : ℂ ≃+* ℂ) (hτ : ∀ z ∈ (embLL0 D).fieldRange, τ z = z) :
    FixBase T Rl.toRealDat j τ :=
  GlobalTheory.T.fixes_untwistedTupleData_of_fixes_smallField D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ hT hcore hfw hti hgal hval hray hroots j τ hτ

theorem exists_extC {G : Type} [Group G] [Fintype G] {T1 : Type} {A : FamIn D.what₂.LL G Pl0 T1 D.R.m} {T : CoreJ D}
    [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {j : Fin D.R.m} {Tp : Type} {tup : Tp → T1}
    (O : OMDat T.toCore R j Tp tup) : ∃ c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W, ExtC R j (inC O.c') O.c0' c :=
  GlobalTheory.T.exists_complexLinear_extension_coefficientMap D G Pl0 T1 A T R j Tp tup O

theorem exists_ser_ne_zero {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀)) (hio : IoExt Rl.toRealDat)
    (j : Fin D.R.m) (hpins : OMPins T Rl.toRealDat κ v₀ O j) (hrow0 : OneMapRow0 T Rl.toRealDat κ v₀ O j)
    (hcusp : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥)
    (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W) (hc : ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c)
    (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ) (hu : ∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) :
    ∃ (v : VsV D j D.what₂.LL) (x : VsV D j ℂ) (h : GA D (Vc D j)) (g : GA D (Wc D j)),
      (∀ m, ∃ q : ℚ, MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) = (q : D.what₂.LL)) ∧
      (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) ∧
      h ∈ GfC (Vc D j) ∧ ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g ≠ 0 :=
  GlobalTheory.T.exists_thetaSeries_rational_vector_ne_zero_of_cuspForms D Γ Pl0 I0 T0 A3 T Rl F κ v₀ O hnV hcore hfw hio j hpins hrow0 hcusp c hc u hu

theorem expands_of_isRatPhase (hRF : GlobalTheory.NT.RayField) {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
    {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    {F : Face D A3.A} {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
    {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F)
    (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀)) (hti : TieIn T Rl.toRealDat κ v₀) (hio : IoExt Rl.toRealDat)
    (hQ : QGuard Rl.toRealDat) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    {j : Fin D.R.m} (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (hpins : OMPins T Rl.toRealDat κ v₀ O j)
    (hfp : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV)
    {gramR c0R c0L} (hft : Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L)
    (hbc : CoefficientBaseChange Rl.toRealDat j (O j).jL (inC (O j).c') (c0L j) (O j).c0')
    {u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ} (hu : ∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) {ph₀ : ℂ}
    (hph : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph₀)
    (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W) (hc : ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c)
    (v : VsV D j D.what₂.LL)
    (hv : ∀ m, ∃ q : ℚ, MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) = (q : D.what₂.LL))
    (x : VsV D j ℂ)
    (hx : (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank))
    (h : GA D (Vc D j)) (hh : h ∈ GfC (Vc D j)) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n),
      Expands (O j) (κ j) (fun g => ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g) e f ∧
        ∀ k, e k ∈ (embLL0 D).fieldRange :=
  GlobalTheory.T.rationalPhaseThetaSeries_expands_cuspForms_smallField D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hnV hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp gramR c0R c0L hft hbc u hu ph₀ hph c hc v hv x hx h hh

theorem fixed_of_expands {G : Type} [Group G] [Fintype G] {T1 : Type} {A : FamIn D.what₂.LL G Pl0 T1 D.R.m} {T : CoreJ D}
    [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {j : Fin D.R.m} {Tp : Type} {tup : Tp → T1}
    (O : OMDat T.toCore R j Tp tup) (κ : WeightFamilies.Wt D ((j : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {Φ Ψ Ψ' : GA D (Wc D j) → ℂ} {a : ℂ}
    (hc : ConjFun O κ τ 1 Ψ Ψ') (hΨ : ∀ g, Ψ g = a * Φ g) (hΨ' : ∀ g, Ψ' g = a * Φ g) {n : ℕ} {e : Fin n → ℂ}
    {f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA κ) κ.n} (he : Expands O κ Φ e f) (hτ : ∀ k, τ (e k) = e k)
    {g₀ : GA D (Wc D j)} (hg₀ : Φ g₀ ≠ 0) : τ a = a := by
  have h1 : Expands O κ Ψ (fun k => a * e k) f := by
    intro g
    rw [hΨ g, he g, Finset.mul_sum]
    simp only [mul_assoc]
  have h2 := hc.2 _ _ _ h1 g₀
  have h3 : a * Φ g₀ = τ a * Φ g₀ := by
    rw [← hΨ' g₀, h2, he g₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show 1 * τ (a * e k) * _ = _
    rw [one_mul, map_mul, hτ, mul_assoc]
  exact (mul_right_cancel₀ hg₀ h3).symm

theorem conjVec_self_of_rat (j : Fin D.R.m) (τ : ℂ ≃+* ℂ) (v : VsV D j D.what₂.LL)
    (hv : ∀ m, ∃ q : ℚ, MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) = (q : D.what₂.LL))
    (x : VsV D j ℂ)
    (hx : (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) :
    ConjVec j τ x x := by
  unfold ConjVec
  rw [hx]
  ext m
  obtain ⟨q, hq⟩ := hv m
  simp [MvPolynomial.coeff_map, hq]

end Steps

theorem exists_isNorm_isRatScalar_std : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS →
    ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j),
    RealPin Rl cG ρ → RatHyp T Rl F κ v₀ O i j hV → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ →
    ∃ ν, IsNorm Rl v₀ (ρ.B i j b) ν ∧ IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν := by
  intro _ hRF row D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin H hcusp
  have hCI : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.chartIndependence_unconditional
  have hcore := H.core
  have hT := H.laws
  have hti := H.tieIn
  have hfw := H.fw
  have hio := H.io
  have hQ := H.guard
  have hfin := H.fin
  have hpins := H.pins
  have hphase := H.phase
  have hfp := H.frame
  have hnV := H.size
  have hgal := H.galois
  have hval := H.small.val
  have hray := H.small.ray
  have hroots := H.small.roots
  have hrow0 : OneMapRow0 T Rl.toRealDat κ v₀ O j :=
    GlobalTheory.OneMapTies.oneMapRow0_of_ties_base_clauses hCI D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hcore.lev hcore.grp hcore.fam
      hcore.models hcore.thP hti hio O j hpins

  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hpins.2.lift.c0
  obtain ⟨u, w₀, hu, -, hw⟩ := FWT.IsChosenExtremalVector.io _ (hti.hv₀ j (sg0 D A3.A)) hio
  obtain ⟨c, hc0, hsc⟩ := Scale.exists_scale hcore.lev hcore.thP (hcore.models.cV j) (hρ.base i j b) (hpin.psi i j b)
    (hpin.inf i j b) (hpin.cartT i j b) (hpin.onbS i j b) (hpin.onbT i j b) (hpin.mu0 i j b) (hpin.eta i j b)
    (hpin.ap i j b) (hpin.am i j b) (c0L j) (hft.mapL j) _ w₀ hw
  obtain ⟨ph₀, hph₀1, hph₀⟩ : ∃ ph : ℂ, ‖ph‖ = 1 ∧ IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph := by
    obtain ⟨ph, h1, h2⟩ := row D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hT hcore.lev hcore.grp hcore.fam hcore.models hcore.thP hti
      j hV hfp H.std gramR c0R c0L hft u hu
    exact ⟨ph, h1, fun C hC _ => h2 C hC⟩
  have hph₀0 : ph₀ ≠ 0 := fun e => by simp [e] at hph₀1

  have hph1 : ‖cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j)‖ = 1 := (hphase hrow0).2.1.2.2.2.2.1
  have hph0 : cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) ≠ 0 := fun e => by rw [e, norm_zero] at hph1; exact zero_ne_one hph1

  obtain ⟨cx, hcx⟩ := exists_extC (O j)
  obtain ⟨ζ, ⟨n, hn, hζn⟩, hζ⟩ := GlobalTheory.ConjRefTup.conjFun_base_root hCI D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O
    (fun j => cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j)) hnV hcore hfin hfw hio hQ j hpins hphase cx hcx
  have hζ1 : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζn hn.ne'
  have hζ0 : ζ ≠ 0 := fun e => by simp [e] at hζ1

  obtain ⟨v, x, h, g₀, hv, hx, hh, hg₀⟩ := exists_ser_ne_zero O hnV hcore hfw hio j hpins hrow0 hcusp cx hcx u hu
  obtain ⟨m, e, f, hexp, heL⟩ := expands_of_isRatPhase hRF YS O hnV hT hcore hfw hti hio hQ hgal hval hray hroots hV hpins hfp
    hft hbc hu hph₀ cx hcx v hv x hx h hh

  obtain ⟨a, ha_def⟩ : ∃ a, a = ζ * cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) * ph₀⁻¹ := ⟨_, rfl⟩
  have hv0 : (fun ρ => ((u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ))) = v₀ j (sg0 D A3.A) := funext hu
  have haL : a ∈ (embLL0 D).fieldRange := by
    refine GlobalTheory.FixedRoots.mem_of_forall_ringEquiv_fixed _ a fun τ hτ => ?_
    have hfix := fixBase_of_fix hRF YS hT hcore hfw hti hgal hval hray hroots j τ hτ
    have hct : ConjTup Rl.toRealDat τ A3.A.μ0 A3.A.μ0 := by
      refine ⟨rfl, fun z => ?_⟩
      have h1 := hcore.lev.xi A3.A.μ0
      rw [hcore.lev.xi_base] at h1
      rw [GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 z]
      simp
    obtain ⟨y, y', hyy, hy⟩ := GlobalTheory.T.exists_conjugateForms_thetaLift_eq_thetaSeries D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hcore hfw j Unit (fun _ => A3.A.μ0) (O j)
      hpins.2 cx hcx τ A3.A.μ0 A3.A.μ0 hfix hct h hh x x (conjVec_self_of_rat j τ v hv x hx)
    have hcf := hζ τ hfix y y' hyy
    have hy1 : ∀ g, (Rl.thF j A3.A.μ0) y (v₀ j (sg0 D A3.A)) g = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (cx x) g :=
      fun g => by have e := (hy u g).1; rwa [hv0] at e
    have hy2 : ∀ g, (Rl.thF j A3.A.μ0) y' (v₀ j (sg0 D A3.A)) g = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (cx x) g :=
      fun g => by have e := (hy u g).2; rwa [hv0] at e
    refine fixed_of_expands (O j) (κ j) τ hcf (fun g => ?_) (fun g => ?_) hexp (fun k => hτ _ (heL k)) (g₀ := g₀)
      (mul_ne_zero hph₀0 hg₀)
    · rw [hy1 g, ha_def, mul_assoc (ζ * _) ph₀⁻¹, inv_mul_cancel_left₀ hph₀0]
    · rw [hy2 g, ha_def, mul_assoc (ζ * _) ph₀⁻¹, inv_mul_cancel_left₀ hph₀0]
  have ha1 : ‖a‖ = 1 := by rw [ha_def, norm_mul, norm_mul, norm_inv, hζ1, hph1, hph₀1]; norm_num

  have hν : a * (ph₀ * c) = ζ * cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) * c := by
    rw [ha_def, ← mul_assoc, mul_assoc (ζ * _) ph₀⁻¹, inv_mul_cancel₀ hph₀0, mul_one]
  refine ⟨a * (ph₀ * c), ⟨?_, c, ⟨gramR, c0R, c0L, hft, u, hu, hsc⟩, n, hn.ne', ?_⟩, ?_⟩
  · rw [hν]; exact mul_ne_zero (mul_ne_zero hζ0 hph0) hc0
  · rw [hν, mul_assoc, mul_pow, hζn, one_mul]
  · exact (IsRatScalar.intro hft hu hc0 hph₀1 hsc hph₀).mul haL ha1

end GlobalTheory.SeriesTie.NormRatStd

end
