import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNLowerBoundBaseChange
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem exists_addValuation_mul_log {C : Type} [Field C] (v : Valuation C NNReal) (r : ℝ) (hr : r < 0) :
    ∃ w : AddValuation C (WithTop ℝ), ∀ x, x ≠ 0 → w x = ((r * Real.log (v x : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  have hpos : ∀ x : C, x ≠ 0 → (0 : ℝ) < (v x : ℝ) := fun x hx => by
    have : v x ≠ 0 := by simpa using hx
    exact_mod_cast pos_iff_ne_zero.2 this
  have hmono : ∀ x y : C, x ≠ 0 → y ≠ 0 → v x ≤ v y →
      ((r * Real.log (v y : ℝ) : ℝ) : WithTop ℝ) ≤ ((r * Real.log (v x : ℝ) : ℝ) : WithTop ℝ) := by
    intro x y hx hy h
    rw [WithTop.coe_le_coe]
    exact mul_le_mul_of_nonpos_left (Real.log_le_log (hpos x hx) (by exact_mod_cast h)) hr.le
  refine ⟨AddValuation.of (fun x => if x = 0 then ⊤ else ((r * Real.log (v x : ℝ) : ℝ) : WithTop ℝ))
    (by simp) (by simp) ?_ ?_, fun x hx => by simp [hx]⟩
  · intro x y
    by_cases hxy : x + y = 0
    · simp [hxy]
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp only [if_neg hx, if_neg hy, if_neg hxy]
    rcases le_max_iff.1 (v.map_add x y) with h | h
    · exact min_le_of_left_le (hmono _ _ hxy hx h)
    · exact min_le_of_right_le (hmono _ _ hxy hy h)
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp only [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [map_mul, NNReal.coe_mul, Real.log_mul (hpos x hx).ne' (hpos y hy).ne', mul_add, WithTop.coe_add]

theorem ValExt.exists_addValuation {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (e : ℕ) (he : 0 < e) :
    ∃ w : AddValuation X.C (WithTop ℝ),
      (∀ x : X.O, ((0 : ℝ) : WithTop ℝ) ≤ w (algebraMap X.O X.C x)) ∧
      (∀ x : T.Fr, nval T.V e x = (WithBot.some (w (X.ιF x)) : WithBot (WithTop ℝ))) ∧
      ∀ (x : X.C) (A : ℝ), (X.v (p : X.C) : ℝ) ^ A ≤ (X.v x : ℝ) →
        w x ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * A : ℝ) : WithTop ℝ) := by
  have hp0 : (p : X.C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpos : ∀ x : X.C, x ≠ 0 → (0 : ℝ) < (X.v x : ℝ) := fun x hx => by
    have : X.v x ≠ 0 := by simpa using hx
    exact_mod_cast pos_iff_ne_zero.2 this
  have hle : X.v (p : X.C) ≤ 1 := by
    have := X.ints.map_le_one (p : X.O)
    rwa [map_natCast] at this
  have hne : X.v (p : X.C) ≠ 1 := fun h =>
    X.nonunit.out (X.ints.isUnit_of_one' (by rwa [map_natCast]))
  have hlt : (X.v (p : X.C) : ℝ) < 1 := by exact_mod_cast lt_of_le_of_ne hle hne
  have hlog : Real.log (X.v (p : X.C) : ℝ) < 0 := Real.log_neg (hpos _ hp0) hlt
  have hpT : (p : T.Fr) ≠ 0 := fun h => hp0 (by rw [← map_natCast X.ιF, h, map_zero])
  have he0 : (0 : ℝ) < (vV T.V (p : T.Fr) : ℝ) := by
    have h1 : 0 ≤ vV T.V (p : T.Fr) := by
      have := GlobalTheory.vV_algebraMap_nonneg_dvr T (p : T.V)
      rwa [map_natCast] at this
    refine lt_of_le_of_ne (by exact_mod_cast h1) fun h => ?_
    have h2 := X.val _ hpT
    rw [← h, div_zero, Real.rpow_zero, map_natCast] at h2
    exact hlt.ne h2
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hc : 0 < (vV T.V (p : T.Fr) : ℝ) / (e : ℝ) := div_pos he0 heR
  have hr : (vV T.V (p : T.Fr) : ℝ) / (e : ℝ) / Real.log (X.v (p : X.C) : ℝ) < 0 := div_neg_of_pos_of_neg hc hlog
  obtain ⟨w, hw⟩ := exists_addValuation_mul_log X.v _ hr
  refine ⟨w, fun x => ?_, fun x => ?_, fun x A hA => ?_⟩
  · by_cases hx : algebraMap X.O X.C x = 0
    · rw [hx, AddValuation.map_zero]; exact le_top
    rw [hw _ hx, WithTop.coe_le_coe]
    exact mul_nonneg_of_nonpos_of_nonpos hr.le
      (Real.log_nonpos (hpos _ hx).le (by exact_mod_cast X.ints.map_le_one x))
  · by_cases hx : x = 0
    · rw [hx, nval_zero, map_zero, AddValuation.map_zero]; rfl
    rw [nval_of_ne hx, hw _ ((map_ne_zero X.ιF).2 hx), X.val x hx, Real.log_rpow (hpos _ hp0)]
    have : (vV T.V (p : T.Fr) : ℝ) / (e : ℝ) / Real.log (X.v (p : X.C) : ℝ) *
        ((vV T.V x : ℝ) / (vV T.V (p : T.Fr) : ℝ) * Real.log (X.v (p : X.C) : ℝ)) = (vV T.V x : ℝ) / e := by
      have := hlog.ne
      field_simp
    rw [this]; rfl
  · have hA0 : 0 < (X.v (p : X.C) : ℝ) ^ A := Real.rpow_pos_of_pos (hpos _ hp0) A
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hA
      exact absurd (hA0.trans_le hA) (by simp)
    rw [hw _ hx, WithTop.coe_le_coe]
    have h1 := Real.log_le_log hA0 hA
    rw [Real.log_rpow (hpos _ hp0)] at h1
    refine (mul_le_mul_of_nonpos_left h1 hr.le).trans (le_of_eq ?_)
    have := hlog.ne
    field_simp

theorem nuLocC_le_of_value_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (B : FB X.O (chD Ch.ch) (𝓞 E)), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) → (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → ∀ (P : MvPolynomial (LtN Dw n) X.O), MvPolynomial.map (algebraMap X.O X.C) P ∈ HHa Dw.mult n X.C ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (f : PS X.O n (chD Ch.ch)) (A : ℝ), (X.v (p : X.C) : ℝ) ^ A ≤ (X.v (nabValN B X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k (MvPowerSeries.map (algebraMap X.O X.C) f) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap X.O X.C (X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ i))) (MvPolynomial.map (algebraMap X.O X.C) P)) : ℝ) → nuLocC Ch e k a n ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * A : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X B hF hA e k n a he P hP f A hv
  letI := io.toAlgebra
  obtain ⟨w, hO, hT, hw⟩ := X.exists_addValuation e he
  have hh : MvPowerSeries.constantCoeff Ch.ch.h = 0 :=
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis _ Ch.ch.gauge.ax0 0 fun _ => rfl
  have hcomp : X.ιF.comp (algebraMap T.V T.Fr) = (algebraMap X.O X.C).comp X.ι := RingHom.ext X.comp
  have hmm : ∀ {m : ℕ} (g : PS T.V m (chD Ch.ch)),
      MvPowerSeries.map (algebraMap X.O X.C) (MvPowerSeries.map X.ι g) =
        MvPowerSeries.map X.ιF (MvPowerSeries.map (algebraMap T.V T.Fr) g) := fun g => by
    ext μ
    simp only [MvPowerSeries.coeff_map, X.comp]
  let R : Subring X.C :=
    { carrier := {x | ((0 : ℝ) : WithTop ℝ) ≤ w x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, WithTop.coe_zero] at *
        rw [w.map_mul]; exact add_nonneg ha hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => w.map_le_add ha hb
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rwa [w.map_neg] }
  have key := GlobalTheory.nabValN_lower_bound_baseChange T X.C w X.ιF R (fun x => Iff.rfl)
    (fun x => by rw [X.comp]; exact hO _) _ (𝓞 E) Ch.ch.B (GlobalTheory.FBMap.mapFB (algebraMap X.O X.C) B)
    (fun i => by
      rw [Ch.gen.1.1 i, ← hmm]
      change MvPowerSeries.map _ (B.G.F i) = _
      rw [hF])
    (fun b i => by
      rw [Ch.gen.1.2.1 b i, ← hmm]
      change MvPowerSeries.map _ (B.A.act b i) = _
      rw [hA])
    Ch.ch.h hh H.w0 k (E →+* ℂ) Dw.mult n ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
    (fun ℓ => ℓ.2.2) (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (nuLocC Ch e k a n)
    (by
      intro Q hQ g hg
      rw [← hT]
      unfold nuLocC
      exact iInf_le_of_le Q (iInf_le_of_le hQ (iInf_le_of_le g (iInf_le_of_le hg le_rfl))))
    (MvPolynomial.map (algebraMap X.O X.C) P)
    ⟨hP, fun m => by rw [MvPolynomial.coeff_map]; exact hO _⟩
    (MvPowerSeries.map (algebraMap X.O X.C) f)
    (fun μ => by rw [MvPowerSeries.coeff_map]; exact hO _)
  refine key.trans (WithBot.coe_le_coe.2 (le_trans (le_of_eq (congrArg w ?_)) (hw _ A hv)))
  have hu : (fun (ℓ : LtN Dw n) j => X.ιF (Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ j)) =
      fun (ℓ : LtN Dw n) i => algebraMap X.O X.C (X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ i)) := by
    funext ℓ j
    rw [Ch.gen.1.2.2.2.2.2.2, X.comp]
  have h1 : (GlobalTheory.FBMap.mapFB (algebraMap X.O X.C) B).FK X.C = B.FK X.C := by
    funext i
    ext μ
    simp [FB.FK, FGLaw.mapF, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapLaw, GlobalTheory.FBMap.mapPt]
  have h2 : ∀ b, (GlobalTheory.FBMap.mapFB (algebraMap X.O X.C) B).actK X.C b = B.actK X.C b := by
    intro b
    funext i
    ext μ
    simp [FB.actK, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapAct, GlobalTheory.FBMap.mapPt]
  rw [hu]
  unfold nabValN FB.hL
  rw [h1, h2]

end GlobalTheory.CharDepth
