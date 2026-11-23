import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContractionIsometricDiscreteSeriesFock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealItLarge

open GlobalTheory.Chain GlobalTheory.Chain.RealIt

theorem exists_isCoverIt_swap (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q)
    (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H)
    (hI : ∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y')
    (hE : ∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) :
    ∃ B : Pol r s p q →ₗ[ℂ] R₁.U.H →ₛₗ[starRingEnd ℂ] R₂.U.H, IsCoverIt R₂ R₁ B := by
  let A : R₁.U.H → F.H →L[ℂ] R₂.U.H := fun x => ContinuousLinearMap.adjoint (Tm x)
  have hC : ∀ x φ y, inner ℂ y (A x φ) = inner ℂ (Tm x y) φ := fun x φ y => by
    simp only [A]
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hn : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hI x x y y
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hall : ∀ g h φ x, A (R₁.U.π g x) (F.π (g, h) φ) = R₂.U.π h (A x φ) := by
    intro g h φ x
    apply ext_inner_left ℂ
    intro y
    obtain ⟨y, rfl⟩ : ∃ y', R₂.U.π h y' = y := ⟨R₂.U.π h⁻¹ y, by
      change (R₂.U.π h * R₂.U.π h⁻¹) y = y
      rw [← map_mul]; simp⟩
    rw [hC, ← hE, GlobalTheory.Chain.CoverContr.inner_map_of_norm _ (R₂.U.isom h), hC]
    exact GlobalTheory.Chain.CoverContr.inner_map_of_norm _ (F.isom _) _ _
  have he : ∀ h φ x, A x (F.π (1, h) φ) = R₂.U.π h (A x φ) := fun h φ x => by
    simpa using hall 1 h φ x
  have hi : ∀ g φ x, A (R₁.U.π g x) (F.π (g, 1) φ) = A x φ := fun g φ x => by
    simpa using hall g 1 φ x
  let sw : Pol r s p q →ₗ[ℂ] Pol p q r s := (MvPolynomial.rename Prod.swap).toLinearMap
  have hsw : ∀ P, sw P = MvPolynomial.rename Prod.swap P := fun _ => rfl
  let B : Pol r s p q →ₗ[ℂ] R₁.U.H →ₛₗ[starRingEnd ℂ] R₂.U.H :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P x => A x (F.ι (sw P)))
      (fun P Q x => by simp only [map_add])
      (fun c P x => by simp only [map_smul, RingHom.id_apply])
      (fun P x x' => by simp only [A, map_add, ContinuousLinearMap.add_apply])
      (fun c P x => by simp only [A, map_smul, map_smulₛₗ, ContinuousLinearMap.smul_apply])
  have hB : ∀ P x, B P x = A x (F.ι (sw P)) := fun _ _ => rfl
  obtain ⟨-, hd1, hd2⟩ := GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F
  have hsym := GlobalTheory.FockSwap.swap_symmetry r s p q
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · intro P
    refine ⟨‖F.ι (sw P)‖, fun x => ?_⟩
    rw [hB]
    set φ := F.ι (sw P)
    have h := hC x φ (A x φ)
    have h1 : ‖A x φ‖ * ‖A x φ‖ ≤ ‖A x φ‖ * (‖φ‖ * ‖x‖) := by
      have := norm_inner_le_norm (𝕜 := ℂ) (Tm x (A x φ)) φ
      rw [← h, hn, inner_self_eq_norm_sq_to_K] at this
      simp at this
      nlinarith
    rcases (norm_nonneg (A x φ)).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_left h1 h0
  · intro P x
    rw [R₂.ι_range, hB]
    have hf := (GlobalTheory.FockKFin.kfin_fock p q r s T₀ T₁ T₂ F
      (GlobalTheory.FockDegree.Om_Kset_homog p q r s T₀ T₁ T₂ F) (sw P)).2
    unfold KFin at *
    have : (Set.range fun k : T₂.Kset => R₂.U.π k (A x (F.ι (sw P)))) =
        (A x).toLinearMap '' Set.range fun k : T₂.Kset => F.π (1, k) (F.ι (sw P)) := by
      rw [← Set.range_comp]; congr 1; funext k; simp [he]
    rw [this, ← Submodule.map_span]
    infer_instance
  · intro x hx
    by_contra hcon
    push_neg at hcon
    have hcon' : ∀ P : Pol p q r s, A x (F.ι P) = 0 := fun P => by
      have := hcon (MvPolynomial.rename Prod.swap P)
      rwa [hB, hsw, MvPolynomial.rename_rename, Prod.swap_swap_eq, MvPolynomial.rename_id_apply] at this
    have h0 : ∀ φ, A x φ = 0 := fun φ =>
      congrFun (Continuous.ext_on F.dense (A x).continuous (continuous_const (y := (0 : R₂.U.H)))
        (by rintro _ ⟨P, rfl⟩; exact hcon' P)) φ
    have := R₂.nontriv
    obtain ⟨y, hy⟩ := exists_ne (0 : R₂.U.H)
    have h := hC x (Tm x y) y
    rw [h0, inner_zero_right, eq_comm, inner_self_eq_zero, ← norm_eq_zero, hn, mul_eq_zero,
      norm_eq_zero, norm_eq_zero] at h
    tauto
  · intro Z hZ P x
    have := (((A x).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hd2 Z hZ (sw P))
    have e1 : sw (fockAct1 r s p q Z P) = fockAct2 p q r s Z (sw P) := hsym.1 Z P
    simpa [hB, Function.comp_def, he, e1] using this
  · intro Z hZ P x
    have h1 := (((A x).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hd1 Z hZ (sw P))
    have h2 := h1.scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)
    have e2 : sw (fockAct2 r s p q Z P) = fockAct1 p q r s Z (sw P) := hsym.2.1 Z P
    have h3 : (fun t : ℝ => B P (R₁.U.π (T₁.expt (t • Z)) x)) =
        fun t : ℝ => A x (F.π (T₁.expt ((-t) • Z), 1) (F.ι (sw P))) := by
      funext t
      rw [hB, ← hi (T₁.expt (t • Z)) (F.π (T₁.expt ((-t) • Z), 1) (F.ι (sw P))) x]
      congr 1
      change _ = (F.π (T₁.expt (t • Z), 1) * F.π (T₁.expt ((-t) • Z), 1)) _
      rw [← map_mul, Prod.mk_mul_mk, ← T₁.expt_add Z hZ, add_neg_cancel, zero_smul, T₁.expt_zero,
        mul_one, Prod.mk_one_one, map_one, ContinuousLinearMap.one_apply]
    rw [h3, hB, e2]
    simpa [Function.comp_def] using h2

end GlobalTheory.Chain.RealItLarge

namespace GlobalTheory.Chain.RealItLarge

open GlobalTheory.Chain GlobalTheory.Chain.RealIt Formalism.MainNotions.SchurIrreducible

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem isParam_lamM' {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de) : IsParam (lamM' t al be ga de) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have mem : ∀ e, e ∈ ga ++ de ++ al ++ be → e ∈ al ++ be ++ ga ++ de := fun e he => by
    simp only [List.mem_append] at he ⊢
    tauto
  have h' : HypA t ga de al be := by
    refine ⟨h1, by omega, h5, h6, h3, h4, ?_, fun e he => h8 e ?_, fun e he => h9 e ?_, fun e he => h10 e (mem e he),
      fun e he => h11 e (mem e he)⟩
    · refine (List.Perm.nodup_iff ?_).1 h7
      rw [List.append_assoc (al ++ be), List.append_assoc (ga ++ de)]
      exact List.perm_append_comm
    · simp only [List.mem_append] at he ⊢
      tauto
    · simp only [List.mem_append] at he ⊢
      tauto
  obtain ⟨-, -, ⟨p1, p2, p3, p4⟩, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t ga de al be h'
  let σ : Ix (al.length + de.length) (ga.length + be.length + t) → Ix (ga.length + be.length + t) (al.length + de.length) :=
    Sum.swap
  have e : ∀ a, lamM' t al be ga de a = lamA' t ga de al be (σ a) := fun a => by rcases a with a | a <;> rfl
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [e, e] at hab
    exact Sum.swap_leftInverse.injective (p1 hab)
  · rw [e, e]
    refine p2 _ _ ?_
    rcases a with a | a <;> rcases b with b | b <;> exact hab
  · rw [e]; exact p3 _
  · rw [e, e]; exact p4 _ _

theorem exists_locIt_large {X : ProvA} (hX : ChosenSeries X) (h1 : ArchimedeanRallisFirst X) (h2 : ArchimedeanRallisSecond X)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {t : ℕ}
    {al be ga de : List ℚ} (hd : DataARm t al be ga de) {aS aT : ℚ}
    (hS : S τ = dualPar (signed (al ++ de) (ga ++ block t ++ be) aT))
    (hS' : S' τ = dualPar (signed (al ++ be) (ga ++ de) aS)) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨-, p1, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hd.1
  have p2 := isParam_lamM' hd.1
  have ht := hd.1.1
  have hn := hd.1.2.1
  obtain ⟨⟨e, he⟩, m, hm, hU⟩ := hB.1 X V S M τ (al.length + de.length) (ga.length + be.length + t) _ _ aT
    ⟨by omega, by simp, by simp [block]; omega, p2, hX _ _ _ p2, hS⟩
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hB.2 X W S' M' τ (al.length + be.length) (ga.length + de.length) _ _ aS
    ⟨by omega, by simp, by simp, p1, hX _ _ _ p1, hS'⟩
  obtain ⟨U, hU⟩ := hU e he
  obtain ⟨U', hU'⟩ := hU' e' he'
  obtain ⟨Φ, hΦ⟩ := (h1.2 t al be ga de hd).1
  obtain ⟨Tm, hi, hq, -⟩ := h2.2 t al be ga de hd Φ hΦ
  obtain ⟨B, hB⟩ := exists_isCoverIt_swap _ _ _ _ _ _ _ _ _ _ Tm hi hq
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ _ _ e e' he he'
  obtain ⟨v, hv, -⟩ := (hX _ _ _ p1).1
  have c1 := Fintype.card_congr e
  have c2 := Fintype.card_congr e'
  simp only [Fintype.card_sum, Fintype.card_fin] at c1 c2
  exact ⟨⟨by omega, by omega⟩,
    GlobalTheory.T.exists_localFockIntertwiner_realPlace_of_coverContraction D V W S S' M M' τ _ _ _ _ _ _ _ _ e e' m m' aS aT U U' κ B hm hm' hU hU' ⟨v, 0, hv⟩ hκ hB⟩

end GlobalTheory.Chain.RealItLarge

theorem GlobalTheory.Chain.RealItLarge.itLarge : ∀ {D : D7} (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (t : ℕ) (aS aT : D.what₂.Tau → ℚ), GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → IsInfFam θ → (∀ τ, ∃ be de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataARm t [] be [] de ∧ S τ = dualPar (GlobalTheory.Chain.signed de (Formalism.BasicNotions.TH.block t ++ be) (aT τ)) ∧ S' τ = dualPar (GlobalTheory.Chain.signed be de (aS τ))) → ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → (∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ)) → ∀ f, GlobalTheory.Chain.IsVacVec ψ θ M M' f → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It := by
  intro D V W S S' M M' θ ψ t aS aT hD hH hθ hP χS χT ω hω hexp f hf
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have hB := GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, GlobalTheory.Chain.RealIt.LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨be, de, hd, e1, e2⟩ := hP τ
    exact GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M M' τ (al := []) (ga := []) hd e1 e2
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  have hc := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (hexp τ).1 (hexp τ).2 hf
  exact ⟨It, GlobalTheory.Chain.RealIt.isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2
    (fun τ => (hc τ).2.1) fun τ => (hc τ).2.2⟩

end
