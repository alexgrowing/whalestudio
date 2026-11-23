import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.AdjointCanonicalGauge
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.LogExpAdaptedGauge
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BetaHSumSmulRight
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalCompApplyEqMvPowerSeriesSubst
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.GermDerivativeLinearMaps

section Calc

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_pderiv (f : PS k 1 d) (i : Fin d) :
    constantCoeff (pderiv k ((0 : Fin 1), i) f) = coeff (Finsupp.single ((0 : Fin 1), i) 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
  simp

theorem dLin_comp (φ ψ : Pt k 1 d) (hψ : GP ψ) : dLin (comp1 φ ψ) = dLin φ * dLin ψ := by
  ext i j
  refine (FormalCalc.coeff_single_subst (a := fun p : Fin 1 × Fin d => (![ψ] : Fin 1 → Pt k 1 d) p.1 p.2)
    (fun p => single_point_zero_constant hψ p.1 p.2) (φ i) _).trans ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.mul_apply]
  rfl

theorem germComp_matrixLinearMap_apply {n : ℕ} (U : Matrix (Fin d) (Fin d) k) (a : Pt k n d) (ha : GP a) (i : Fin d) :
    comp1 (LogExpAdaptedGauge.linMap U) a i = ∑ j, C (U i j) * a j := by
  have hz : FormalLog.CZ (![a] : Fin 1 → Pt k n d) := fun j l => single_point_zero_constant ha j l
  show ev ![a] (∑ j : Fin d, MvPowerSeries.C (U i j) * X ((0 : Fin 1), j)) = _
  rw [FormalLog.ev_sum hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FormalLog.ev_mul hz, FormalLog.ev_C hz, FormalLog.ev_X hz]
  rfl

theorem gp_linMap (U : Matrix (Fin d) (Fin d) k) : GP (LogExpAdaptedGauge.linMap U) := fun i => by
  simp [LogExpAdaptedGauge.linMap]

theorem dLin_linMap (U : Matrix (Fin d) (Fin d) k) : dLin (LogExpAdaptedGauge.linMap U) = U := by
  classical
  ext i j
  simp [dLin, LogExpAdaptedGauge.linMap, coeff_C_mul, coeff_X, Finsupp.single_left_inj]

theorem linMap_one {n : ℕ} (a : Pt k n d) (ha : GP a) : comp1 (LogExpAdaptedGauge.linMap (1 : Matrix (Fin d) (Fin d) k)) a = a := by
  classical
  funext i
  rw [germComp_matrixLinearMap_apply _ _ ha, Finset.sum_eq_single i] <;> simp +contextual [Matrix.one_apply, eq_comm]

end Calc

section Log

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

theorem additive_at {n : ℕ} (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (ψ : Pt k 1 d)
    (hψ : comp1 ψ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1))
    (a b : Pt k n d) (ha : GP a) (hb : GP b) : comp1 ψ (addOf F a b) = comp1 ψ a + comp1 ψ b := by
  have hV := pair_points_zero_constant ha hb
  have e := congrArg (evP ![a, b]) hψ
  have e2 : ∀ u v : Pt k 2 d, evP ![a, b] (u + v) = evP ![a, b] u + evP ![a, b] v := fun u v =>
    funext fun i => gt_ev_add _ hV _ _
  rw [e2, evP_comp1 _ hV _ _ (gp_addOf F hF _ _ (gp_pt 0) (gp_pt 1)),
    evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1), evP_comp1 _ hV _ _ (gp_pt 0),
    evP_comp1 _ hV _ _ (gp_pt 1), evP_pt _ hV, evP_pt _ hV] at e
  exact e

theorem germLinearPart_coordinatePoint_zero : dLin (pt k (n := 1) d 0) = 1 := by
  rw [← linMap_one (pt k (n := 1) d 0) (gp_pt 0), gt_comp1_pt_right, dLin_linMap]

theorem additive_eq_lin (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (ℓ ε ψ : Pt k 1 d)
    (h1 : dLin ℓ = 1) (hℓ : comp1 ℓ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1)) (hi : IsInvPair ℓ ε) (h0 : GP ψ)
    (hψ : comp1 ψ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1)) :
    ψ = comp1 (LogExpAdaptedGauge.linMap (dLin ψ)) ℓ := by
  classical
  have hε : GP ε := hi.2.1
  have hℓ0 : GP ℓ := hi.1
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 := gp_comp1 _ _ hε p0
  have q1 := gp_comp1 _ _ hε p1
  have ps : GP (pt k (n := 2) d 0 + pt k (n := 2) d 1) := fun i => by simp [pt]
  have e1 : comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      addOf F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) := by
    rw [← gt_comp_inv' hi _ (gp_addOf F hF _ _ q0 q1), additive_at F hF ℓ hℓ _ _ q0 q1,
      gt_comp_inv hi _ p0, gt_comp_inv hi _ p1]
  have e2 : comp1 (comp1 ψ ε) (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      comp1 (comp1 ψ ε) (pt k (n := 2) d 0) + comp1 (comp1 ψ ε) (pt k (n := 2) d 1) := by
    rw [gt_comp1_comp1 _ _ hε _ ps, gt_comp1_comp1 _ _ hε _ p0, gt_comp1_comp1 _ _ hε _ p1, e1,
      additive_at F hF ψ hψ _ _ q0 q1]
  have hdε : dLin ε = 1 := by
    have := dLin_comp ℓ ε hε
    rwa [hi.2.2.1, germLinearPart_coordinatePoint_zero, h1, one_mul, eq_comm] at this
  have e3 : comp1 ψ ε = LogExpAdaptedGauge.linMap (dLin ψ) := by
    have hd : dLin (comp1 ψ ε) = dLin (LogExpAdaptedGauge.linMap (dLin ψ)) := by
      rw [dLin_comp _ _ hε, hdε, mul_one, dLin_linMap]
    funext i
    ext e
    by_cases he : e.degree = 1
    · obtain ⟨⟨s, j⟩, rfl⟩ : ∃ s, e = Finsupp.single s 1 := by
        exact (Finsupp.sum_eq_one_iff e).1 he
      obtain rfl : s = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun hd i) j
    · rw [addition_linear k d _ (congrFun e2 i) e he]
      simp only [LogExpAdaptedGauge.linMap, map_sum, coeff_C_mul, coeff_X]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [if_neg, mul_zero]
      rintro rfl
      simp at he
  rw [← e3, gt_comp1_comp1 _ _ hε _ hℓ0, hi.2.2.2, gt_comp1_pt_right]

theorem exists_isLogExp {R : Type} [CommRing R] [Algebra R k] (G : FGLaw R d) :
    ∃ ℓ ε : Pt k 1 d, LogExpAdaptedGauge.IsLogExp k G ℓ ε := by
  obtain ⟨ℓ, h0, h1, h2⟩ := FormalLog.logSt k d (FBMap.mapLaw (algebraMap R k) G)
  obtain ⟨ε, hε⟩ := ChartInv.exists_isInvPair k d ℓ h0 (by rw [h1, Matrix.det_one]; exact isUnit_one)
  exact ⟨ℓ, ε, h1, h2, hε⟩

end Log

section Predicates

variable {C : Type} [NormedField C] [IsUltrametricDist C] {d : ℕ}

end Predicates

section Predicates2

variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
  {O : Type} [CommRing O] [StarRing O]

def comap {O' : Type} [CommRing O'] [StarRing O'] (f : O' →+* O) (hf : ∀ a, f (star a) = star (f a))
    (B : FB R d O) : FB R d O' :=
  { B with
    A :=
      { act := fun a => B.A.act (f a)
        const := fun a => B.A.const (f a)
        hom := fun a => B.A.hom (f a)
        add_act := fun a b => by rw [map_add, B.A.add_act]
        mul_act := fun a b => by rw [map_mul, B.A.mul_act]
        one_act := by rw [map_one, B.A.one_act] }
    ad := fun a => B.ad (f a)
    adjoint_zero_fst := fun a => B.adjoint_zero_fst (f a)
    adjoint_zero_snd := fun a => B.adjoint_zero_snd (f a)
    adjoint_compat_left := fun a => by simpa only [hf] using B.adjoint_compat_left (f a)
    adjoint_compat_right := fun a => by simpa only [hf] using B.adjoint_compat_right (f a)
    ad_one := by simpa only [map_one] using B.ad_one
    ad_mul := fun a b => by simpa only [hf, map_mul] using B.ad_mul (f a) (f b)
    ad_add := fun a b => by simpa only [hf, map_add] using B.ad_add (f a) (f b)
    ad_sy := fun a => by simpa only [hf] using B.ad_sy (f a) }

end Predicates2

section Letters

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

end Letters

section Frame

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

def ColumnBody (g : ℕ) (B : FB (LogExpAdaptedGauge.Ints C) d (𝓞 E)) (ε : Pt C 1 d) (h : PS C 2 d) (w0 : 𝓞 E)
    (u : PS (LogExpAdaptedGauge.Ints C) 2 d) : Prop :=
    ∀ n : ℕ, IsUnit (LogExpAdaptedGauge.colProd B u w0 n) ∧ ∃ hL : PS C n d, constantCoeff hL = 0 ∧
      FB.toK C (LogExpAdaptedGauge.colProd B u w0 n) * FB.expS C (LogExpAdaptedGauge.colSum C B h w0 n) = FB.expS C hL ∧
      ∀ (U : Matrix (Fin d) (Fin d) (LogExpAdaptedGauge.Ints C)) (ty : Fin d → (E →+* C)), LogExpAdaptedGauge.IsAdapted B U ty →
        LogExpAdaptedGauge.IntBelow g (LogExpAdaptedGauge.inChart (LogExpAdaptedGauge.letterChart ε U) hL) ∧
        ∀ m : Fin n × Fin d →₀ ℕ, coeff m (LogExpAdaptedGauge.inChart (LogExpAdaptedGauge.letterChart ε U) hL) ≠ 0 →
          3 ≤ LogExpAdaptedGauge.degTot m ∧
          ∃ (i : Fin n) (a b : Fin d), (∀ p, m p ≠ 0 → p.1 = i ∧ (ty p.2 = ty a ∨ ty p.2 = ty b)) ∧
            m (i, a) ≠ 0 ∧ m (i, b) ≠ 0 ∧ ty b = LogExpAdaptedGauge.conjType (ty a)

def ColumnFrameFor (g : ℕ) (B : FB (LogExpAdaptedGauge.Ints C) d (𝓞 E)) (ε : Pt C 1 d) (h : PS C 2 d) (w0 : 𝓞 E) : Prop :=
  ∃ u : PS (LogExpAdaptedGauge.Ints C) 2 d,
    ev (n := 1) ![0, pt (LogExpAdaptedGauge.Ints C) d 0] u = 1 ∧ ev (n := 1) ![pt (LogExpAdaptedGauge.Ints C) d 0, 0] u = 1 ∧
    ColumnBody g B ε h w0 u

def TwoPoint (B : FB (LogExpAdaptedGauge.Ints C) d (𝓞 E)) (ε : Pt C 1 d) (h : PS C 2 d) (u : PS (LogExpAdaptedGauge.Ints C) 2 d) : Prop :=
  ∃ h₂ : PS C 2 d, ev (n := 1) ![0, pt C d 0] h₂ = 0 ∧ ev (n := 1) ![pt C d 0, 0] h₂ = 0 ∧
    FB.toK C u * FB.expS C h = FB.expS C h₂ ∧
    ∀ (U : Matrix (Fin d) (Fin d) (LogExpAdaptedGauge.Ints C)) (ty : Fin d → (E →+* C)), LogExpAdaptedGauge.IsAdapted B U ty →
      bilinPart C (LogExpAdaptedGauge.inChart (LogExpAdaptedGauge.letterChart ε U) h₂) = 0 ∧
      ∀ m : Fin 2 × Fin d →₀ ℕ, coeff m (LogExpAdaptedGauge.inChart (LogExpAdaptedGauge.letterChart ε U) h₂) ≠ 0 →
        ∃ τ : E →+* C, (∀ i, m (0, i) ≠ 0 → ty i = τ) ∧ (∀ j, m (1, j) ≠ 0 → ty j = LogExpAdaptedGauge.conjType τ)

end Frame

def ColumnFrame : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → LogExpAdaptedGauge.SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (LogExpAdaptedGauge.Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), LogExpAdaptedGauge.IsLogExp C B.G ℓ ε →
  ∀ w0 : 𝓞 E, w0 + star w0 = 1 → ∃ h : PS C 2 d, LogExpAdaptedGauge.IsAdjGauge C B h ∧ ColumnFrameFor g B ε h w0

def UniformFrame : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → LogExpAdaptedGauge.SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (LogExpAdaptedGauge.Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), LogExpAdaptedGauge.IsLogExp C B.G ℓ ε →
  ∃ h : PS C 2 d, LogExpAdaptedGauge.IsAdjGauge C B h ∧ ∃ u : PS (LogExpAdaptedGauge.Ints C) 2 d,
    ev (n := 1) ![0, pt (LogExpAdaptedGauge.Ints C) d 0] u = 1 ∧ ev (n := 1) ![pt (LogExpAdaptedGauge.Ints C) d 0, 0] u = 1 ∧
    TwoPoint B ε h u ∧ ∀ w0 : 𝓞 E, w0 + star w0 = 1 → ColumnBody g B ε h w0 u

end GlobalTheory.GermDerivativeLinearMaps
