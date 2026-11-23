import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartB
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCompactEmbedded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionTransitionPolynomial
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCoverAndCone
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionLocalChartPolynomial
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStandardSmoothLocalization
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.SmoothMan

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo TensorProduct KaehlerDifferential

theorem finrank_fibre_kaehler (A L C : Type) [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
    [Field L] [Algebra A L] [IsFractionRing A L] [Algebra ℚ L] [IsScalarTower ℚ A L]
    [Field C] [Algebra A C] (e : ℕ) (he : Algebra.trdeg ℚ L = e) :
    Module.finrank C (C ⊗[A] Ω[A⁄ℚ]) = e := by
  have : Algebra.FormallySmooth ℚ A := inferInstance
  have : Module.Projective A Ω[A⁄ℚ] := Algebra.FormallySmooth.projective_kaehlerDifferential
  have : Algebra.FinitePresentation ℚ A := inferInstance
  have : Module.FinitePresentation A Ω[A⁄ℚ] := inferInstance
  have hconst := (Module.isLocallyConstant_rankAtStalk (R := A) (M := Ω[A⁄ℚ]))
  have hC : Module.finrank C (C ⊗[A] Ω[A⁄ℚ]) = Module.rankAtStalk (R := A) Ω[A⁄ℚ]
      (PrimeSpectrum.comap (algebraMap A C) ⊥) := by
    have h := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := C) (M := C ⊗[A] Ω[A⁄ℚ])) ⊥
    rw [Module.rankAtStalk_baseChange] at h
    exact h.symm
  have hL : Module.finrank L (L ⊗[A] Ω[A⁄ℚ]) = Module.rankAtStalk (R := A) Ω[A⁄ℚ]
      (PrimeSpectrum.comap (algebraMap A L) ⊥) := by
    have h := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := L) (M := L ⊗[A] Ω[A⁄ℚ])) ⊥
    rw [Module.rankAtStalk_baseChange] at h
    exact h.symm
  have : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  have : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors A)
  have : Algebra.EssFiniteType ℚ L := .comp ℚ A L
  have hrank : Module.finrank L (L ⊗[A] Ω[A⁄ℚ]) = e := by
    rw [(tensorKaehlerEquivOfFormallyEtale ℚ A L).finrank_eq, Module.finrank, GlobalTheory.rank_kaehler_eq_trdeg, he]
    simp
  rw [hC, hconst.apply_eq_of_preconnectedSpace _ (PrimeSpectrum.comap (algebraMap A L) ⊥), ← hL, hrank]

theorem exists_span_of_fibre (A : Type) [CommRing A] [Algebra ℚ A] [Algebra A ℂ] [IsScalarTower ℚ A ℂ]
    [Module.Finite A Ω[A⁄ℚ]] (σ : Type) (u : σ → A) (e : ℕ)
    (hf : Module.finrank ℂ (ℂ ⊗[A] Ω[A⁄ℚ]) = e) :
    ∃ b : Fin e → σ → ℂ, ∀ Φ : A →ₐ[ℚ] TrivSqZeroExt ℂ ℂ, (∀ a, (Φ a).fst = algebraMap A ℂ a) →
      (fun q => (Φ (u q)).snd) ∈ Submodule.span ℂ (Set.range b) := by
  classical
  let B := Module.finBasisOfFinrankEq ℂ (ℂ ⊗[A] Ω[A⁄ℚ]) hf
  refine ⟨fun i q => B.repr ((1 : ℂ) ⊗ₜ[A] KaehlerDifferential.D ℚ A (u q)) i, fun Φ hΦ => ?_⟩
  have hsm : ∀ (s : A) (x : ℂ), s • x = algebraMap A ℂ s * x := fun s x => Algebra.smul_def s x
  let d : Derivation ℚ A ℂ := Derivation.mk'
    (((TrivSqZeroExt.sndHom ℂ ℂ).restrictScalars ℚ).comp Φ.toLinearMap) (fun a b => by
      show (Φ (a * b)).snd = a • (Φ b).snd + b • (Φ a).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, hΦ, hΦ, hsm, hsm]
      simp [mul_comm])
  have hd : ∀ s, d s = (Φ s).snd := fun _ => rfl
  let l : ℂ ⊗[A] Ω[A⁄ℚ] →ₗ[ℂ] ℂ := LinearMap.liftBaseChange ℂ d.liftKaehlerDifferential
  have hl : ∀ s, l ((1 : ℂ) ⊗ₜ[A] KaehlerDifferential.D ℚ A s) = (Φ s).snd := by
    intro s
    simp [l, LinearMap.liftBaseChange_tmul, hd]
  have key : ∀ q, (Φ (u q)).snd =
      ∑ i, B.repr ((1 : ℂ) ⊗ₜ[A] KaehlerDifferential.D ℚ A (u q)) i * l (B i) := by
    intro q
    rw [← hl]
    have h := congrArg l (B.sum_repr ((1 : ℂ) ⊗ₜ[A] KaehlerDifferential.D ℚ A (u q)))
    rw [map_sum] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have he : (fun q => (Φ (u q)).snd) =
      ∑ i, l (B i) • (fun q => B.repr ((1 : ℂ) ⊗ₜ[A] KaehlerDifferential.D ℚ A (u q)) i) := by
    funext q
    rw [key, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem card_le_of_smooth (σ : Type) [Fintype σ] (Ω : Type) [Field Ω] [CharZero Ω] (u : σ → Ω)
    (V : Submodule ℂ (σ → ℂ)) (w : σ → ℂ)
    (hker : ∀ g : MvPolynomial σ ℚ, aeval u g = 0 → eval w (map (algebraMap ℚ ℂ) g) = 0)
    (hV : ∀ g : MvPolynomial σ ℚ, aeval u g = 0 →
      (fun q => eval w (pderiv q (map (algebraMap ℚ ℂ) g))) ∈ V)
    (hsm : Algebra.Smooth ℚ (Algebra.adjoin ℚ (Set.range u))) (e : ℕ)
    (he : Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range u)) = e) :
    Fintype.card σ ≤ Module.finrank ℂ V + e := by
  classical
  have huS : ∀ q, u q ∈ Algebra.adjoin ℚ (Set.range u) := fun q => Algebra.subset_adjoin ⟨q, rfl⟩
  have haw : ∀ g : MvPolynomial σ ℚ, (aeval w g : ℂ) = eval w (map (algebraMap ℚ ℂ) g) := fun g => by
    rw [eval_map, aeval_def]
  have hS1 : Algebra.adjoin ℚ (Set.range u) =
      Algebra.adjoin ℚ (insert (aeval u (1 : MvPolynomial σ ℚ))⁻¹ (Set.range u)) := by
    simp only [map_one, inv_one]
    apply le_antisymm (Algebra.adjoin_mono (Set.subset_insert _ _))
    rw [Algebra.adjoin_le_iff]
    rintro x (rfl | hx)
    · exact Subalgebra.one_mem _
    · exact Algebra.subset_adjoin hx
  obtain ⟨ψ, hψ, hψu⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_unique_lift σ Ω ℂ u w
    (fun g hg => by rw [haw]; exact hker g hg) 1 (by simp) (by simp) _ hS1 huS
  letI : Algebra (Algebra.adjoin ℚ (Set.range u)) ℂ := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (Algebra.adjoin ℚ (Set.range u)) ℂ :=
    .of_algebraMap_eq fun r => (ψ.commutes r).symm
  have hfin := finrank_fibre_kaehler (Algebra.adjoin ℚ (Set.range u))
    (IntermediateField.adjoin ℚ (Set.range u)) ℂ e he
  obtain ⟨b, hb⟩ := exists_span_of_fibre (Algebra.adjoin ℚ (Set.range u)) σ
    (fun q => ⟨u q, huS q⟩) e hfin
  refine GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.card_le_finrank_add _ _ e b fun v hv => ?_
  let t : σ → TrivSqZeroExt ℂ ℂ := fun q => TrivSqZeroExt.inl (w q) + TrivSqZeroExt.inr (v q)
  obtain ⟨Φ, hΦ, -⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_unique_lift σ Ω (TrivSqZeroExt ℂ ℂ) u t
    (fun g hg => by
      obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.aeval_dual σ w v g
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [h1, hker g hg]; rfl
      · rw [h2]
        have := hv _ (hV g hg)
        exact this)
    1 (by simp) (by simp) _ hS1 huS
  have hfst : (TrivSqZeroExt.fstHom ℚ ℂ ℂ).comp Φ = ψ := hψu _ fun q => by
    simp [hΦ, t]
  have := hb Φ (fun a => DFunLike.congr_fun hfst a)
  have hv' : (fun q => (Φ ⟨u q, huS q⟩).snd) = v := by
    funext q
    simp [hΦ, t]
  rwa [hv'] at this

theorem card_le_finrank_jacSpanAt (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (hP : IsArithVar (mCoordIdeal y) (e + 1))
    (hsm : SmoothGenericFibreM y)
    (p : (k : K) → ι k) (hp : ∀ k, y ⟨k, p k⟩ ≠ 0) (w : (Σ k, ι k) → ℂ)
    (hw : ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p, eval w h = 0) :
    Fintype.card (Σ k, ι k) ≤
      Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p) w) + e := by
  have hkerC := GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.ker_le_chart K ι Ω y p hp
  have hF : GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y p = ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField y :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.ratioField_eq y p hp
  have htr := GlobalTheory.CompanionTheory.Ar.SegreChart.trdeg_blockFnField hP p hp
  rw [← hF] at htr
  exact card_le_of_smooth (Σ k, ι k) Ω _ (ReciprocityTheory.AnForm.R.jacSpanAt _ w) w (fun g hg => hw _ (hkerC g hg))
    (fun g hg => Submodule.subset_span ⟨_, hkerC g hg, rfl⟩) (hsm p hp) e htr

open ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt in

theorem exists_params_of_regular {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hI : ∀ h ∈ I, eval t h = 0) (e : ℕ) (hreg : IsRegularLocalRing (locRing I t))
    (hd : ringKrullDim (locRing I t) = e) :
    ∃ r : Fin e → MvPolynomial (Fin m) ℂ,
      Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
        Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) := by
  classical
  have hK : I ≤ ptI t := fun h hh => mem_ptIdeal.mpr (hI h hh)
  haveI : IsLocalRing (locR I t) := hreg.toIsLocalRing
  have hmax : IsLocalRing.maximalIdeal (locRing I t) =
      Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) := max_eq_map I hK
  have hfg : (IsLocalRing.maximalIdeal (locRing I t)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  have hcard' : s.card = e := by
    have h1 := hreg.spanFinrank_maximalIdeal
    rw [hd] at h1
    have h2 : (IsLocalRing.maximalIdeal (locRing I t)).spanFinrank = e := by exact_mod_cast h1
    omega
  let E := s.equivFinOfCardEq hcard'
  have hex : ∀ g : locRing I t, ∃ a c : MvPolynomial (Fin m) ℂ, eval t c ≠ 0 ∧
      g * algebraMap _ (locRing I t) c = algebraMap _ (locRing I t) a := by
    intro g
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective g
    obtain ⟨⟨a, c⟩, h⟩ := IsLocalization.surj (ptIdeal t).primeCompl x
    refine ⟨a, c, fun h0 => c.2 (RingHom.mem_ker.2 h0), ?_⟩
    exact congrArg (Ideal.Quotient.mk _) h
  choose a c hc hac using fun l : Fin e => hex (E.symm l : s)
  have hu : ∀ l, IsUnit (algebraMap _ (locRing I t) (c l)) := fun l => by
    have := (IsLocalization.map_units (locPt t)
      (⟨c l, fun h => hc l (RingHom.mem_ker.mp h)⟩ : (ptIdeal t).primeCompl)).map
      (algebraMap (locPt t) (locRing I t))
    rwa [← IsScalarTower.algebraMap_apply] at this
  refine ⟨a, ?_⟩
  rw [← hmax, ← hspan]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    show algebraMap _ (locRing I t) (a l) ∈ Ideal.span (s : Set (locRing I t))
    rw [← hac l]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (E.symm l).2)
  · show Ideal.span (s : Set (locRing I t)) ≤ _
    rw [Ideal.span_le]
    intro g hg
    obtain ⟨v, hv⟩ := (hu (E ⟨g, hg⟩)).exists_right_inv
    have h1 := hac (E ⟨g, hg⟩)
    simp only [Equiv.symm_apply_apply] at h1
    have h2 : g = algebraMap _ (locRing I t) (a (E ⟨g, hg⟩)) * v := by
      rw [← h1, mul_assoc, hv, mul_one]
    rw [h2]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, rfl⟩)

theorem isRegularLocalRing_chart (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (hP : IsArithVar (mCoordIdeal y) (e + 1))
    (hsm : SmoothGenericFibreM y) (p : (k : K) → ι k) (x)
    (hx : x ∈ GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.src (pC (mCoordIdeal y)) p) :
    IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ideal (pC (mCoordIdeal y)) p)
      (GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.coord (pC (mCoordIdeal y)) p x)) ∧
    ringKrullDim (ReciprocityTheory.AnForm.R.locRing (GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ideal (pC (mCoordIdeal y)) p)
      (GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.coord (pC (mCoordIdeal y)) p x)) = e := by
  classical
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hP.2.1.2.1
  have hz := GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.rep_mem x
  have hw := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh p (GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.rep x) hx).1 hz
  have hy : ∀ k, y ⟨k, p k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, p k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0]
      simp
    have h1 := hz.2 _ (Ideal.subset_span ⟨_, hX, rfl⟩)
    rw [map_X, eval_X] at h1
    exact hx k h1
  obtain ⟨hloc, hnoeth⟩ := ReciprocityTheory.AnForm.R.locAt_isLocalRing_isNoetherian _ _ hw
  have hd := ReciprocityTheory.AnForm.R.ringKrullDim_locAt_chart _ hPh e (pcEquidim K ι _ e hP) p _ hw
  have hcot := ReciprocityTheory.AnForm.R.finrank_cotangentSpace_locAt
    (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p) (ReciprocityTheory.AnForm.R.affCoord p (GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.rep x))
  have hrank := card_le_finrank_jacSpanAt K ι Ω y e hP hsm p hy _ hw
  have hreg : IsRegularLocalRing (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p)
      (ReciprocityTheory.AnForm.R.affCoord p (GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.rep x))) := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hd]
    have : Module.finrank (IsLocalRing.ResidueField (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p)
        (ReciprocityTheory.AnForm.R.affCoord p (GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.rep x)))) (IsLocalRing.CotangentSpace (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p)
        (ReciprocityTheory.AnForm.R.affCoord p (GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.rep x)))) ≤ e := by omega
    exact_mod_cast this
  exact ⟨IsRegularLocalRing.of_ringEquiv (ReciprocityTheory.AnForm.R.locAtEquiv _ _),
    (ringKrullDim_eq_of_ringEquiv (ReciprocityTheory.AnForm.R.locAtEquiv _ _)).symm.trans hd⟩

theorem not_mem_conePts_top' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ ReciprocityTheory.AnForm.R.conePts (⊤ : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :=
  fun hz => by simpa using hz.2 1 Submodule.mem_top

theorem isUnit_algebraMap_locRing' {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (pt : Fin n → ℂ)
    (g : MvPolynomial (Fin n) ℂ) (hg : eval pt g ≠ 0) :
    IsUnit (algebraMap _ (ReciprocityTheory.AnForm.R.locRing I pt) g) := by
  have := (IsLocalization.map_units (ReciprocityTheory.AnForm.R.locPt pt)
    (⟨g, fun h => hg (RingHom.mem_ker.mp h)⟩ : (ReciprocityTheory.AnForm.R.ptIdeal pt).primeCompl)).map
    (algebraMap (ReciprocityTheory.AnForm.R.locPt pt) (ReciprocityTheory.AnForm.R.locRing I pt))
  rwa [← IsScalarTower.algebraMap_apply] at this

open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes in

theorem nonempty_algRes (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (hP : IsArithVar (mCoordIdeal y) (e + 1))
    (hsm : SmoothGenericFibreM y) :
    Nonempty (ReciprocityTheory.AnForm.R.AlgRes ι (pC (mCoordIdeal y)) ⊤ e) := by
  classical
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hP.2.1.2.1
  obtain ⟨hcpt, hsrc⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.compact_open_embedding K ι _ hPh
  obtain ⟨himage, htrans⟩ := chart_image_and_trans K ι _ hPh
  obtain ⟨hcover, hliftmem, hcompat, hsurj, hinj, -⟩ := chart_lifts_package K ι _ _ hPh hPh
  have hinv := ChartInv.chart_coord_ratio K ι _ hPh
  have hreg := isRegularLocalRing_chart K ι Ω y e hP hsm
  have hdata : ∀ (p : (k : K) → ι k) (x) (hx : x ∈ src (pC (mCoordIdeal y)) p), _ :=
    fun p x hx => exists_params_of_regular (ideal (pC (mCoordIdeal y)) p) (coord (pC (mCoordIdeal y)) p x)
      (by
        have h : coord (pC (mCoordIdeal y)) p x ∈ coord (pC (mCoordIdeal y)) p '' src (pC (mCoordIdeal y)) p :=
          ⟨x, hx, rfl⟩
        rw [himage p] at h
        exact h) e (hreg p x hx).1 (hreg p x hx).2
  let E := Fintype.equivFin ((k : K) → ι k)
  exact ⟨
    { M := Pts (pC (mCoordIdeal y))
      compact := hcpt
      n := Fintype.card ((k : K) → ι k)
      amb := fun _ => Fintype.card (Σ k, ι k)
      ideal := fun i => ideal _ (E.symm i)
      src := fun i => src _ (E.symm i)
      isOpen_alt_bis := fun i => (hsrc _).1
      cover := fun x => by
        obtain ⟨p, hp⟩ := hcover x
        obtain ⟨i, rfl⟩ := E.symm.surjective p
        exact ⟨i, hp⟩
      coord := fun i => coord _ (E.symm i)
      isEmbedding := fun i => (hsrc _).2
      image := fun i => himage _
      trans := fun i j => htrans _ _
      regular := fun i x hx => (hreg _ x hx).1
      dim := fun i x hx => (hreg _ x hx).2
      lift := fun i => GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.lift (E.symm i)
      lift_one := fun i => ⟨E.symm i, fun k => by simp [GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.lift]⟩
      lift_mem := fun i => hliftmem _
      compat := fun i j => hcompat _ _
      surj := fun z hz _ => by
        obtain ⟨p, x, hx, h⟩ := hsurj z hz
        obtain ⟨i, rfl⟩ := E.symm.surjective p
        exact ⟨i, x, hx, h⟩
      inj := fun i j x hx x' hx' _ h => hinj _ _ x hx x' hx' h
      inv := fun i x hx _ p' hp' => hinv _ x hx p' hp'
      bd := fun _ => ⊤
      le_bd := fun _ => le_top
      zero_bd := fun i x hx =>
        ⟨fun h => absurd (h 1 Submodule.mem_top) (by simp), fun h => absurd h (not_mem_conePts_top' _)⟩
      rc := 0
      comp := Fin.elim0
      sncAt := fun i x hx =>
        { r := (hdata _ x hx).choose
          J := ∅
          h := 1
          σ := fun _ => none
          σ_injOn := by simp
          σ_eq_none := by simp
          span_eq := (hdata _ x hx).choose_spec
          eval_h := by simp
          mem_bd := Submodule.mem_top
          le_span := fun g _ => by simp }
      comp_eq := fun i x hx => ⟨src _ (E.symm i), (hsrc _).1, hx, subset_rfl, fun k => k.elim0⟩
      mult := fun f a hf hfP hz => ⟨Fin.elim0, fun i x hx =>
        ⟨_, isUnit_algebraMap_locRing' _ _ _ (by
          rw [ReciprocityTheory.AnForm.R.eval_bind_one]
          intro h0
          exact not_mem_conePts_top' _ (hz _ (hliftmem _ x hx) h0)), by simp⟩⟩ }⟩

end GlobalTheory.CompanionTheory.Ar.PB.SmoothMan

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem nonempty_anLogRes_of_smoothGenericFibre : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → SmoothGenericFibreM y → Nonempty (AnLogRes (mCoordIdeal y) ⊤ D) := by
  intro K _ ι _ Ω _ inst y D hP hsm
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hJ : IsMultiHomogIdeal (⊤ : Ideal (MRing ι)) :=
    ⟨{1}, by
      rintro f rfl
      refine ⟨0, fun m hm k => ?_⟩
      have : m = 0 := by
        by_contra h
        simp [MvPolynomial.coeff_one, MvPolynomial.mem_support_iff, Ne.symm h] at hm
        exact h hm
      simp [this], by simp⟩
  have hJP : ¬ (⊤ : Ideal (MRing ι)) ≤ mCoordIdeal y := fun h =>
    hP.2.1.1.ne_top (top_le_iff.mp h)
  have hT : pC (⊤ : Ideal (MRing ι)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨1, Submodule.mem_top, map_one _⟩
  obtain ⟨R⟩ := SmoothMan.nonempty_algRes K ι Ω y D hP hsm
  exact nonempty_anLogRes_of_algRes _ _ D hJ hJP (pcContract K ι _ D hP) (hT ▸ R)

end GlobalTheory.CompanionTheory.Ar.PB
