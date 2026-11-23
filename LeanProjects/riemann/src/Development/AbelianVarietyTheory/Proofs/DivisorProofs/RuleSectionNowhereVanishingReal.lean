import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryExtensionIndependentOfModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisOfIntegralFramedPointStatement
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraTer

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.BdryUnitVal

theorem pt_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (y : letI := io.toAlgebra; FrPt Xo c T.Fr), (letI := io.toAlgebra; ∀ s, GlobalTheory.AllWt.ptF y s ∈ (V : Set (Xo.XF c))) → ∃ χ : Sp T.V ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.genFibre Y, χ ≫ pullback.snd _ _ = spMap φ ∧ (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y ≫ Y.jQ = spMap (algebraMap T.V T.Fr) ≫ χ) ∧ Set.range χ ⊆ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.compactification Y V := by
  intro E _ _ _ H Dw l Xo c Y V T io φ hφ y hy
  letI := io.toAlgebra
  obtain ⟨χ, h1, h2⟩ := GlobalTheory.CuspFrom.exists_genPt (K := T.Fr) Y φ hφ y
  refine ⟨χ, h1, h2, ?_⟩
  rintro _ ⟨p, rfl⟩
  let η : Sp T.Fr := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr)
  have hη : χ (spMap (algebraMap T.V T.Fr) η) ∈ Y.jQ '' (V : Set (Xo.XF c)) := by
    rw [← Scheme.Hom.comp_apply, ← h2, Scheme.Hom.comp_apply]
    exact ⟨_, hy η, rfl⟩
  have hp : p ∈ closure {spMap (algebraMap T.V T.Fr) η} := by
    apply (PrimeSpectrum.le_iff_mem_closure _ _).1
    show Ideal.comap (algebraMap T.V T.Fr) (⊥ : Ideal T.Fr) ≤ (p : PrimeSpectrum T.V).asIdeal
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective T.V T.Fr)]
    exact bot_le
  exact map_mem_closure χ.continuous hp (fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hη)

end GlobalTheory.BdryUnitVal

namespace GlobalTheory.BdryUnitVal

theorem vV_unit (T : CDVR) (u : T.V) (hu : IsUnit u) : vV T.V (algebraMap T.V T.Fr u) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    refine le_antisymm (HeightOneSpectrum.intValuation_le_one _ _) (not_lt.1 fun h => ?_)
    exact (IsDiscreteValuationRing.maximalIdeal T.V).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).1 h) hu)
  rw [vV, h1, WithZero.log_one, neg_zero]

theorem nval_unit (T : CDVR) (u : T.V) (hu : IsUnit u) : nval T.V 1 (algebraMap T.V T.Fr u) = 0 := by
  have hne : algebraMap T.V T.Fr u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hu.ne_zero
  rw [nval_of_ne hne, vV_unit T u hu]
  simp

theorem exists_factor (T : CDVR) {F : Type} [Field F] (io : F →+* T.Fr) (hio : ∀ a, a ≠ 0 → vV T.V (io a) = 0) :
    ∃ φ : F →+* T.V, (algebraMap T.V T.Fr).comp φ = io := by
  first
  | exact @_root_.GlobalTheory.LiftAndFactorization.exists_factor
  | exact _root_.GlobalTheory.LiftAndFactorization.exists_factor
  | (apply _root_.GlobalTheory.LiftAndFactorization.exists_factor <;> assumption)
  | (intros; apply _root_.GlobalTheory.LiftAndFactorization.exists_factor <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LiftAndFactorization.exists_factor <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LiftAndFactorization.exists_factor ..)

end GlobalTheory.BdryUnitVal

namespace GlobalTheory.BdryUnitVal

theorem conj_ne {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (τ : Psi H) :
    conjEmb τ.1 (H.rt : E) ≠ H.rt0 := fun h3 => by
  have h3' : starRingEnd ℂ (τ.1 (H.rt : E)) = H.rt0 := h3
  rw [τ.2] at h3'
  have h4 := H.sqrt_neg_disc_sq
  have h5 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h3'
  have h6 := congrArg Complex.re h4
  have h7 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  simp [pow_two, h5] at h6
  nlinarith [mul_self_nonneg H.rt0.re]

theorem unit_at_integral : GlobalTheory.CovTop.Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (V : (Xo.XF c).Opens) (τ : Psi H) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → Reads Y V τ sig f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ f) = 0 := by
  intro _ E _ _ _ H Dw l Xo c Y Z V τ sig f hVZ hsig hvn hrd T io y₀ hio hlies
  letI := io.toAlgebra
  obtain ⟨φ, hφ⟩ := exists_factor T io hio
  have hy : ∀ s, GlobalTheory.AllWt.ptF y₀.1 s ∈ (V : Set (Xo.XF c)) := fun s => hVZ ▸ hlies s
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := pt_ext E H Dw l Xo c Y V T io φ hφ y₀.1 hy
  have hp : Dw.mult τ.1 = Dw.p := by rw [Datum.mult, if_pos τ.2]
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := by rw [Datum.mult, if_neg (conj_ne τ)]
  obtain ⟨v, hv, hsv⟩ := GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 τ.1 Dw.p hp
  obtain ⟨w, hw, hsw⟩ := GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 (conjEmb τ.1) Dw.q hq
  let aT : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.V φ := ⟨χ, hχ1, hχ3, v, w, hv, hw⟩
  have hx : (spMap (algebraMap T.V T.Fr) ≫ χ) ≫ pullback.fst _ _ =
      spMap (algebraMap T.V T.Fr) ≫ (χ ≫ pullback.fst _ _) := Category.assoc _ _ _
  obtain ⟨v', hv', ev⟩ := GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hv
  obtain ⟨w', hw', ew⟩ := GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hw
  rw [hφ] at hv' hw'
  let aK : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.Fr io :=
    ⟨spMap (algebraMap T.V T.Fr) ≫ χ, by rw [Category.assoc, hχ1, ← GlobalTheory.DetExtendZero.spMap_comp, hφ], by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hχ3 ⟨_, rfl⟩, v', w', hv', hw'⟩
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsChange aT aK (algebraMap T.V T.Fr) 1 1 := by
    refine ⟨hφ, rfl, fun i => ?_, fun i => ?_⟩
    · have := GlobalTheory.DetExtendZero.comb_one (fun k => (aK.v_basis.1 k).1) i
      convert this using 2 with k
      exact (ev k).symm
    · have := GlobalTheory.DetExtendZero.comb_one (fun k => (aK.w_basis.1 k).1) i
      convert this using 2 with k
      exact (ew k).symm
  have e := hsig T.V T.Fr φ io aT aK (algebraMap T.V T.Fr) 1 1 hc
  simp only [Matrix.det_one, mul_one] at e
  have hm : Matches Y V τ y₀.1 aK :=
    ⟨hχ2.symm, fun i => ⟨Fin.cast hp.symm i, rfl, by
      change SameVec Y y₀.1 _ (v' i).left
      rw [ev]; exact hsv i⟩, fun i => ⟨Fin.cast hq.symm i, rfl, by
      change SameVec Y y₀.1 _ (w' i).left
      rw [ew]; exact hsw i⟩⟩
  have hr := hrd T.Fr y₀.1 y₀.2.1 aK hm
  change nval T.V 1 (evR Xo c f y₀.1) = 0
  rw [hr]
  change nval T.V 1 (sig T.Fr io aK) = 0
  rw [e]
  exact nval_unit T _ (hvn T.V φ aT)

end GlobalTheory.BdryUnitVal
