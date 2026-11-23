import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayFieldAny
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverSmall

abbrev smallF (D : D7) : IntermediateField ℚ ℂ := (embLL0 D).toRatAlgHom.fieldRange

theorem smallF_toSubfield (D : D7) : (smallF D).toSubfield = (embLL0 D).fieldRange := by
  ext x; rfl

def smallEquiv (D : D7) : D.LL0 ≃ₐ[ℚ] smallF D := AlgEquiv.ofInjectiveField (embLL0 D).toRatAlgHom

instance smallF_fin (D : D7) : FiniteDimensional ℚ (smallF D) :=
  (smallEquiv D).toLinearEquiv.finiteDimensional

theorem smallF_normal (D : D7) (hgal : IsGalois ℚ D.LL0) : Normal ℚ (smallF D) :=
  (IsGalois.of_algEquiv (smallEquiv D)).to_normal

theorem rayIn_of_dvd (hRF : GlobalTheory.NT.RayField) (D : D7) {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hd : M ∣ N)
    {k : Subfield ℂ} (h : RayIn D N k) : RayIn D M k := by
  obtain ⟨L, i1, i2, i3, i4, hL, j, hj, hk⟩ := h
  have hMb : Ideal.span {((M : ℕ) : 𝓞 D.host.K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hM
  have hNb : Ideal.span {((N : ℕ) : 𝓞 D.host.K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN
  obtain ⟨L', f1, f2, f3, f4, hL'⟩ := hRF D.host.K _ hMb
  have hdv : Ideal.span {((M : ℕ) : 𝓞 D.host.K)} ∣ Ideal.span {((N : ℕ) : 𝓞 D.host.K)} :=
    Ideal.dvd_iff_le.2 (Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hd))
  obtain ⟨f⟩ := GlobalTheory.Published.nonempty_algHom_of_isRay_of_dvd (L := L) (L' := L') hNb hdv hL hL'
  refine ⟨L', f1, f2, f3, f4, hL', j.comp f.toRingHom, ?_, fun x => hk (f x)⟩
  rw [← hj]; ext x; simp

theorem core_le_small {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL]
    (Rl : RealDat3 D A3 ↥T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S)
    (hLaws : LawsJ T) (ha : AlgTie T) (j : Fin D.R.m) : T.Q.c.F ≤ smallF D := by
  intro a ha'
  refine ⟨S.kKs ((YS.fi j).eK.symm ⟨a, ha'⟩), ?_⟩
  have h1 : res T D.what₂.embLL = T.σ₀ := res_embLL T ha hLaws.pins.2.2.1
  change D.what₂.embLL ((S.kKs ((YS.fi j).eK.symm ⟨a, ha'⟩) : ↥D.LL0) : D.what₂.LL) = a
  rw [S.kKs_spec, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun h1 ⟨a, ha'⟩

theorem exists_goodCover_small : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ n : ℕ, ∃ C : GlobalTheory.CoverRead.Cover T ((j : ℕ) + 1) T.σ₀, C.d.pd = 1 ∧ C.σ₂.fieldRange = (embLL0 D).fieldRange ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.GoodCover T Rl.toRealDat j C n := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hLaws hCore hFW hTie hIo hQG hgal hVal hRay hroots j hV hOM hFP n
  haveI : Normal ℚ (smallF D) := smallF_normal D hgal
  have hle : T.Q.c.F ≤ smallF D := core_le_small T Rl cG S YS hLaws hTie.alg j
  have hnum := GlobalTheory.T.numerical_consequences_of_pins D T.Q hLaws.toLawsM.pins
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hLaws.toLawsM.pins.2.1.1
  have hz : ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (T.Q.l.M * 1) ∈ smallF D := by
    rw [mul_one, ← hnum.2.2.1]; exact hle T.Q.c.zeta_mem
  have hsm : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SmallIn Rl.toRealDat j ((smallF D).val : smallF D →+* ℂ) := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨y, hy⟩ := hVal.mu0 j v hv
      exact ⟨⟨embLL0 D y, y, rfl⟩, hy⟩
    · obtain ⟨y, hy⟩ := hVal.eta v hv
      exact ⟨⟨embLL0 D y, y, rfl⟩, hy⟩
  have hM0 : T.Q.l.M ≠ 0 := by have := T.Q.l.three_le; omega
  have hN0 : D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' ≠ 0 := by
    have h0 := (D.host.g_prime 0).ne_zero
    have h1 := (D.host.g_prime 1).ne_zero
    have h2 := D.host.pde_prime.ne_zero
    have h3 := D.host.pde'_prime.ne_zero
    positivity
  have hray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * 1) (smallF D).toSubfield := by
    rw [mul_one, smallF_toSubfield]
    refine rayIn_of_dvd hRF D hM0 hN0 ?_ hRay
    rw [hMg, mul_assoc _ D.host.pde]; exact dvd_mul_right _ _
  have hj : InR D ((j : ℕ) + 1) := ⟨by omega, j.2⟩
  have hK : (⊤ : Ideal (𝓞 D.host.E)) = Ideal.span {x | x ∈ (⊤ : Ideal (𝓞 D.host.E)) ∧ x ∈ Algebra.adjoin ℤ {T.Q.H.w0}} := by
    symm; rw [Ideal.eq_top_iff_one]; exact Ideal.subset_span ⟨Submodule.mem_top, Subalgebra.one_mem _⟩
  have hprod : (⊤ : Ideal (𝓞 D.host.E)) * (⊤ : Ideal (𝓞 D.host.E)).map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
      Ideal.span {((1 : ℕ) : 𝓞 D.host.E)} := by
    rw [Ideal.map_top, Ideal.top_mul, Nat.cast_one, Ideal.span_singleton_one]
  have hsup : (⊤ : Ideal (𝓞 D.host.E)) ⊔ (⊤ : Ideal (𝓞 D.host.E)).map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ :=
    top_sup_eq _
  obtain ⟨C, hpd, -, hfr, hG⟩ := GlobalTheory.CoverGalois.exists_goodCover_galois D T Rl.toRealDat hLaws j hj n 1 ⊤
    (GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.auxiliarySplitSquarefreeLevel_one _) hK hprod hsup (smallF D) hle hz hsm hray
  exact ⟨C, hpd, hfr.trans (smallF_toSubfield D), hG⟩

end GlobalTheory.CoverSmall
