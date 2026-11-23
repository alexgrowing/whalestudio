import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrability
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARPartsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.IoLift
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.PointAtPlaceHom
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.KFinOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'}

theorem span_eq_top
    {aS aT : D.what₂.Tau → ℚ} {a : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)}
    {a' : ∀ τ, Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)} (ha : ∀ τ, IsKAct M τ (a τ))
    (hirr : ∀ τ, AbsIrr fun X : lieAt V τ => a τ X) (hker : ∀ τ, LocKer M M' τ (aS τ) (aT τ) (a' τ))
    (I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M)
    (h0 : I ≠ 0) (hIs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y, I (srcOp M M' τ (aT τ) X φ) y = intersection_update_fsHerm_neg_one τ (a τ X) (I φ y))
    (hIt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ y, I (tgtOp M M' τ (aS τ) Y φ) y + I φ (intersection_update_fsHerm_neg_one τ (a' τ Y) y) = 0) :
    Submodule.span ℂ {x | ∃ φ y, I φ y = x} = ⊤ := by
  classical

  have hne : ∃ p y, multi I p y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (span_multi I fun p y => by rw [← multi_apply]; exact hc p y)

  have hsrc : ∀ τ (X : lieAt V τ) (q : D.what₂.Tau → LPol W.rank V.rank) (w : KVec M'),
      multi I (Function.update q τ (sOp M M' τ (aT τ) X (q τ))) w = intersection_update_fsHerm_neg_one τ (a τ X) (multi I q w) := by
    intro τ X q w
    rw [multi_apply, multi_apply, ← srcOp_glue]
    exact hIs τ X X.2 (glue q) (PiTensorProduct.tprod ℂ w)

  have hpair : ∀ τ (L : KT M →ₗ[ℂ] kFin M τ), IsContr τ L → ∀ (p : D.what₂.Tau → LPol W.rank V.rank) (y : KVec M'),
      IsLocPair M M' τ (aS τ) (aT τ) (a' τ) ((slice (multi I) τ p y).compr₂ L) := by
    intro τ L hL p y
    have hmove : ∀ X (hX : X ∈ lieAt V τ) (P : LPol W.rank V.rank) (z : kFin M' τ),
        (slice (multi I) τ p y).compr₂ L (sOp M M' τ (aT τ) X P) z =
          a τ X ((slice (multi I) τ p y).compr₂ L P z) := by
      intro X hX P z
      simp only [LinearMap.compr₂_apply, slice_apply]
      have hq : Function.update p τ (sOp M M' τ (aT τ) X P) =
          Function.update (Function.update p τ P) τ
            (sOp M M' τ (aT τ) X ((Function.update p τ P) τ)) := by simp
      rw [hq, hsrc τ ⟨X, hX⟩]
      exact LinearMap.congr_fun (hL (a τ X)) _
    refine ⟨fun X hX P P' z z' => ?_, fun Y hY P z => ?_⟩
    · rw [hmove X hX, hmove X hX]
      exact (ha τ).skew X hX _ _
    · simp only [LinearMap.compr₂_apply, slice_apply]
      have hq : Function.update p τ (tOp M M' τ (aS τ) Y P) =
          Function.update (Function.update p τ P) τ
            (tOp M M' τ (aS τ) Y ((Function.update p τ P) τ)) := by simp
      have hz : PiTensorProduct.tprod ℂ (Function.update y τ (a' τ Y z)) =
          intersection_update_fsHerm_neg_one τ (a' τ Y) (PiTensorProduct.tprod ℂ (Function.update y τ z)) := by
        rw [position_tprod]; simp
      rw [hq, multi_apply, multi_apply, ← tgtOp_glue, hz, ← map_add, hIt τ Y hY, map_zero]
  have key := (exists_factor (P := fun _ : D.what₂.Tau => LPol W.rank V.rank) (Y := fun τ => kFin M' τ)
    (K := fun τ => kFin M τ) (Z := ℂ) (G := fun τ => lieAt V τ)
    (fun τ X => sOp M M' τ (aT τ) X) (fun τ X => a τ X) hirr (multi I) 0 hne
    (fun τ X p y => hsrc τ X p y)
    (fun τ L hL p y hL0 => ⟨fun L' hL' p' y' => hker τ _ _ _ _ (hpair τ L hL p y) (hpair τ L' hL' p' y') hL0,
      fun p' y' n x z _ => by simp [slice_apply]⟩)).2
  rw [eq_top_iff, ← key]
  apply Submodule.span_mono
  rintro x ⟨p, y, rfl⟩
  exact ⟨glue p, PiTensorProduct.tprod ℂ y, (multi_apply I p y).symm⟩

end GlobalTheory.Chain.KFinOnto

namespace GlobalTheory.Chain.KFinOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem itW_onto_kFin : ∀ (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) (D : D7)
    (k : Fin D.R.m) (a b : ℕ),
    a = k → b = (k : ℕ) + 1 → ∀ (V W : HSp D) (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ), IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f →
    ∀ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (ptOf ψ θ M M' f) It →
    ∃ (h : KSm M) (h' : KSm M'), LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, It φ (inclK h' y) = x} := by
  intro hD hH D k a b hab hb V W M M' θ ψ hθ hC ω f hω hf It hIt
  subst hab hb
  obtain ⟨X, hX, -, -, -, -, h3, -⟩ := GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hD hH
  have hB := GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hD hH D

  have hloc : ∀ τ, (kFin M τ ≤ M.sm τ ∧ kFin M' τ ≤ M'.sm τ) ∧ ∃ a a', IsKAct M τ a ∧ IsKAct M' τ a' ∧
      AbsIrr (fun X : lieAt V τ => a X) ∧ LocKer M M' τ (expS D k τ) (expT D k τ) a' := by
    intro τ
    obtain ⟨al, be, ga, de, hd, -, hA, hA'⟩ := hC τ
    refine exists_local hX h3 hH hB M M' τ hd ?_ ?_
    · show dualPar (parA (Ptw D) k τ) = _
      rw [hA]
    · show dualPar (parA (Ptw D) (k + 1) τ) = _
      rw [hA']
  choose hsm a a' ha ha' hirr hker using hloc
  have h : KSm M := fun τ => (hsm τ).1
  have h' : KSm M' := fun τ => (hsm τ).2
  refine ⟨h, h', ?_⟩

  obtain ⟨χS, χT, hW, hexp⟩ := hω
  have hvc : ∀ τ, _ := fun τ => GlobalTheory.T.thetaVacuumCharacters_realPlaces D V W _ _ M M' θ ψ χS χT ω f τ (expS D k τ) (expT D k τ) hθ hW
    (hexp τ).1 (hexp τ).2 hf
  have hinj : Function.Injective (ptOf ψ θ M M' f) :=
    (GlobalTheory.VacuumFockLaws.vacuumFock_onObjects D V W _ _ M M' ψ θ hW.std hθ f hf).2.2.2.2

  have h0K : ∃ φ y, It φ (inclK h' y) ≠ 0 := by
    have hs : ∀ τ φ (v : M'.Vec), ∃ (n : ℕ) (φs : Fin n → PolF D W.rank V.rank) (u : Fin n → M'.sm τ),
        (∀ i, (u i : M'.H τ) ∈ kFin M' τ) ∧
          It φ (PiTensorProduct.tprod ℂ v) = ∑ i, It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ (u i))) := by
      intro τ φ v
      obtain ⟨n, φs, c, hc, hωc⟩ := FockOrbit.fock_orbit_coefFam D V W _ _ M M' θ ψ ω f τ (expS D k τ) (expT D k τ)
        hθ hinj (hvc τ).2.1 φ
      refine ⟨n, φs, fun i => ⟨kMean M' τ (c i) (v τ),
        (GlobalTheory.SmoothAverage.kMean_smooth D W _ M' τ (c i) (hc.1 i) (v τ) (v τ).2).1⟩,
        fun i => kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (v τ) i, ?_⟩
      exact it_eq_sum_kMean D V W _ _ M M' θ ω (ptOf ψ θ M M' f) It hIt τ n c φ φs v _ hc.1 hωc fun i => rfl
    by_contra hc
    push_neg at hc
    have hspan : Submodule.span ℂ {z | ∃ φ y, It φ (inclK h' y) = z} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨φ, y, rfl⟩
      exact hc φ y
    refine hIt.ne (LinearMap.ext fun φ => LinearMap.ext fun x => ?_)
    have hx := mem_span_of_average It h' hs φ x
    rw [hspan, Submodule.mem_bot] at hx
    simpa using hx

  have hK : ∀ φ y, It φ (inclK h' y) ∈ LinearMap.range (inclK h) := by
    intro φ y
    apply mem_range_inclK h
    intro τ
    refine ⟨Submodule.map ((inclT M) ∘ₗ It.flip (inclK h' y))
      (MvPolynomial.restrictTotalDegree (FVar D W.rank V.rank) ℂ φ.totalDegree), inferInstance, fun g hg => ?_⟩
    have hκ : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := hg
    have hFu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
    have hg' : g = (M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hFu, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hFu, Matrix.one_mul]

    have hUH : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      obtain ⟨hu, hJ⟩ := hκ
      have e3 : (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * (M.fr τ * g * (M.fr τ)⁻¹) = 1 := by
        have := (Matrix.mem_unitaryGroup_iff').mp hu
        rwa [Matrix.star_eq_conjTranspose] at this
      have e1 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Z) = Z := fun Z => by
        rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hFu, Matrix.conjTranspose_one,
          Matrix.one_mul]
      have e2 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * Z) = Z := fun Z => by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hFu, Matrix.one_mul]
      show gᴴ * gramAt D V τ * g = gramAt D V τ
      generalize hk : M.fr τ * g * (M.fr τ)⁻¹ = κ at e3 hJ hg'
      rw [← M.fr_gram τ, hg']
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, e2]
      rw [← Matrix.mul_assoc (Formalism.REAL.Jm (M.ε τ)) κ, ← hJ, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ κ, e3,
        Matrix.one_mul]
    have helt : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M τ (M.fr τ * g * (M.fr τ)⁻¹) = atTau θ V τ g := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt]
      rw [← hg']
    have h1 : (1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) ∈ Formalism.REAL.Kset (M'.ε τ) :=
      ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
    obtain ⟨xx, yy, -, -, hcf⟩ := (hvc τ).2.1
    have hcf1 := hcf _ hκ 1 h1 φ
    rw [elt_one hθ, helt] at hcf1
    obtain ⟨c, Q, hQ, hcQ⟩ : ∃ (c : ℂ) (Q : PolF D W.rank V.rank), Q.totalDegree ≤ φ.totalDegree ∧
        ω (atTau θ V τ g, 1) (ptOf ψ θ M M' f φ) = c • ptOf ψ θ M M' f Q :=
      ⟨_, _, GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ φ, hcf1⟩
    have hpt : ptOf ψ θ M M' f (c • Q) = ω (atTau θ V τ g, 1) (ptOf ψ θ M M' f φ) := by
      rw [hcQ]
      simp only [ptOf, map_smul]
    rw [← hIt.eqK τ g hUH φ (c • Q) hpt (inclK h' y)]
    exact Submodule.mem_map_of_mem ((MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      ((MvPolynomial.totalDegree_smul_le _ _).trans hQ))

  obtain ⟨I, hI⟩ : ∃ I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M,
      ∀ φ y, inclK h (I φ y) = It φ (inclK h' y) := by
    let e := LinearEquiv.ofInjective (inclK h) (inclK_injective h)
    have he : ∀ z : LinearMap.range (inclK h), inclK h (e.symm z) = z := fun z => by
      have := congrArg Subtype.val (e.apply_symm_apply z)
      rw [LinearEquiv.ofInjective_apply] at this
      exact this
    refine ⟨LinearMap.mk₂ ℂ (fun φ y => e.symm ⟨It φ (inclK h' y), hK φ y⟩) ?_ ?_ ?_ ?_, fun φ y => he _⟩
    · intro φ₁ φ₂ y
      apply inclK_injective h
      simp only [map_add, he, LinearMap.add_apply]
    · intro c φ y
      apply inclK_injective h
      simp only [map_smul, he, LinearMap.smul_apply]
    · intro φ y₁ y₂
      apply inclK_injective h
      simp only [map_add, he]
    · intro c φ y
      apply inclK_injective h
      simp only [map_smul, he]
  have hI0 : I ≠ 0 := by
    obtain ⟨φ, y, hne⟩ := h0K
    intro h0
    apply hne
    rw [← hI, h0]
    simp
  have hIs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y,
      I (srcOp M M' τ (expT D k τ) X φ) y = intersection_update_fsHerm_neg_one τ (a τ X) (I φ y) := by
    intro τ X hX φ y
    apply inclK_injective h
    have e1 : ptOf ψ θ M M' f (srcOp M M' τ (expT D k τ) X φ) =
        ptOf ψ θ M M' f (fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) φ -
          ((expT D k τ : ℂ) * X.trace) • φ) := by
      congr 1
      simp only [srcOp, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, Module.End.one_apply, neg_smul,
        sub_eq_add_neg]
    have d1 := hIt.eqg τ X hX φ (srcOp M M' τ (expT D k τ) X φ)
      (fun z => by rw [e1]; exact (hvc τ).2.2.1 X hX φ z) (inclK h' y)
    have d2 := FinTensor.derT_mapFactor h τ (a τ) (ha τ) X hX (I φ y)
    rw [hI] at d2
    rw [hI]
    exact derT_unique d1 d2
  have hIt' : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ y,
      I (tgtOp M M' τ (expS D k τ) Y φ) y + I φ (intersection_update_fsHerm_neg_one τ (a' τ Y) y) = 0 := by
    intro τ Y hY φ y
    apply inclK_injective h
    have e1 : ptOf ψ θ M M' f (tgtOp M M' τ (expS D k τ) Y φ) =
        ptOf ψ θ M M' f (fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ +
          ((expS D k τ : ℂ) * Y.trace) • φ) := by
      rfl
    have hd : ∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptOf ψ θ M M' f φ) z)
        (ptOf ψ θ M M' f (tgtOp M M' τ (expS D k τ) Y φ) z) 0 := fun z => by
      rw [e1]
      exact (hvc τ).2.2.2 Y hY φ z
    have hd2 := FinTensor.derT_mapFactor h' τ (a' τ) (ha' τ) Y hY y
    have hsum := hIt.invg τ Y hY φ _ _ _ hd hd2
    rw [LinearMap.map_add (inclK h), hI, hI, LinearMap.map_zero]
    exact hsum
  have hspanI := span_eq_top (aS := fun τ => expS D k τ) (aT := fun τ => expT D k τ) ha hirr hker I hI0 hIs hIt'
  rintro _ ⟨t, rfl⟩
  have ht : t ∈ Submodule.span ℂ {x | ∃ φ y, I φ y = x} := by rw [hspanI]; exact Submodule.mem_top
  have hmap := Submodule.mem_map_of_mem (f := inclK h) ht
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨φ, y, rfl⟩, rfl⟩
  exact ⟨φ, y, (hI φ y).symm⟩

end GlobalTheory.Chain.KFinOnto

end
