import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FormalGroupLawPointMaps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpLaw
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharAtOfMultiplicativeSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLeadingMinorsGeOfLeRank
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNnrealValuationOfAddValuation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotIsUnitNatCastOfIsLocalHom
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsUniversalChartOfFormalGroupChart
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvSelfTwo
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ChartCharacter

section Series

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {d : ℕ}

theorem cz_pt (j : Fin 2) : CZ (![pt k (n := 2) d j] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt j) CZ.nil

theorem cz_add (G : FGLaw k d) :
    CZ (![addOf G.F (pt k (n := 2) d 0) (pt k (n := 2) d 1)] : Fin 1 → Pt k 2 d) :=
  CZ.cons (fun i => constantCoeff_ev (CZ.cons (cc_pt 0) (CZ.cons (cc_pt 1) CZ.nil)) (G.const i)) CZ.nil

theorem isCh_one (F : Fin d → PS k 2 d) : IsCh F 1 := ⟨map_one _, by simp⟩

theorem isCh_mul (G : FGLaw k d) {u u' : PS k 1 d} (h : IsCh G.F u) (h' : IsCh G.F u') : IsCh G.F (u * u') := by
  refine ⟨by rw [map_mul, h.1, h'.1, mul_one], ?_⟩
  rw [LogPf.ev_mul (cz_add G), LogPf.ev_mul (cz_pt 0), LogPf.ev_mul (cz_pt 1), h.2, h'.2]
  ring

theorem ev_ev_one {n : ℕ} {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) {a : Pt k n d}
    (ha : ∀ i, constantCoeff (a i) = 0) (u : PS k 1 d) : ev ![a] (ev ![φ] u) = ev ![comp1 φ a] u := by
  rw [LogPf.ev_ev (CZ.cons ha CZ.nil) (CZ.cons hφ CZ.nil)]
  congr 1
  funext j i
  fin_cases j
  rfl

theorem isCh_pull (G : FGLaw k d) {Λ : Type} [CommRing Λ] (A : OAct Λ G) (a : Λ) {u : PS k 1 d} (h : IsCh G.F u) :
    IsCh G.F (ev ![A.act a] u) := by
  refine ⟨by rw [WickVanishing.gt_const_ev_eq _ (CZ.cons (A.const a) CZ.nil), h.1], ?_⟩
  have hc : ∀ (j : Fin 2) i, constantCoeff (comp1 (A.act a) (pt k (n := 2) d j) i) = 0 := fun j i =>
    constantCoeff_ev (cz_pt j) (A.const a i)
  have hb : CZ (![comp1 (A.act a) (pt k (n := 2) d 0), comp1 (A.act a) (pt k (n := 2) d 1)] : Fin 2 → Pt k 2 d) :=
    CZ.cons (hc 0) (CZ.cons (hc 1) CZ.nil)
  have h2 := congrArg (ev (![comp1 (A.act a) (pt k (n := 2) d 0), comp1 (A.act a) (pt k (n := 2) d 1)] :
    Fin 2 → Pt k 2 d)) h.2
  have hadd : addOf G.F (pt k (n := 2) d 0) (pt k d 1) = G.F :=
    funext fun j => MultiplicativeSeries.ev_self_two _
  rw [LogPf.ev_mul hb, LogPf.ev_ev hb (cz_add G), LogPf.ev_ev hb (cz_pt 0), LogPf.ev_ev hb (cz_pt 1), hadd] at h2
  rw [ev_ev_one (A.const a) (a := addOf G.F (pt k (n := 2) d 0) (pt k d 1)) (cz_add G 0), ev_ev_one (A.const a) (cc_pt 0), ev_ev_one (A.const a) (cc_pt 1),
    A.hom a]
  refine Eq.trans ?_ (h2.trans ?_)
  · congr 1
    funext j i
    fin_cases j
    rfl
  · congr 2
    · funext j i
      fin_cases j
      exact ev_X hb 0 i
    · funext j i
      fin_cases j
      exact ev_X hb 1 i

theorem dl_eq (u : PS k 1 d) (j : Fin d) : dl u j = constantCoeff (pderiv k ((0 : Fin 1), j) u) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
  simp [dl]

theorem dl_one (j : Fin d) : dl (1 : PS k 1 d) j = 0 := by
  rw [dl_eq]
  simp

theorem dl_mul {u u' : PS k 1 d} (h : constantCoeff u = 1) (h' : constantCoeff u' = 1) (j : Fin d) :
    dl (u * u') j = dl u j + dl u' j := by
  rw [dl_eq, dl_eq, dl_eq, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, h, h']
  ring

theorem dl_pull {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (u : PS k 1 d) (j : Fin d) :
    dl (ev ![φ] u) j = ∑ i, dl u i * dLin φ i j := by
  rw [dl_eq, pderiv_ev (CZ.cons hφ CZ.nil), map_sum, Fintype.sum_prod_type, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, WickVanishing.gt_const_ev_eq _ (CZ.cons hφ CZ.nil), ← dl_eq, ← dl_eq]
  rfl

end Series

section Jets

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_isChartJ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] {d : ℕ} (x : JetSer.Fam G (Fin d))
    (hx : Chart.IsUnivChart G d x) (F : FGLaw R d) (hF : JetSer.IsLawOf x F.F) : ∃ x', IsChartJ G F x' := by
  refine ⟨_, (TorsionCompare.isOriginChart_iff G F x).1 ⟨hx.1, hx.2.1, fun κ m y hy => ?_, fun m => ?_⟩⟩
  · have hy' : Chart.spMap (Chart.jetZeroR R κ m) ≫ y = 1 := hy
    have := hx.2.2 (Chart.JetR R κ m) (Chart.jetAug R κ m) m (Chart.ker_jetAug_pow κ m) y (by
      rw [ChartUniv.jetAug_eq, ← Chart.spMap_comp, Category.assoc, hy', MonObj.comp_one])
    simp only [ChartUniv.aug_comp_iff] at this
    exact this
  · have hrep : ∀ i : Fin 2, JetSer.Rep x (pt R (n := 2) d i)
        (fun m => Chart.spMap (ChartUniv.jetRen (fun j => (i, j)) m) ≫ x m) := fun i =>
      ⟨TB.LogPf.cc_pt i, fun m => ⟨_, fun j => (ChartUniv.jetRen_zR _ m j).trans (JetSer.toJet_X m _).symm, rfl⟩⟩
    obtain ⟨ψ, hψ, hψ'⟩ := (hF.2 2 _ _ _ _ (hrep 0) (hrep 1)).2 m
    have hadd : addOf F.F (pt R (n := 2) d 0) (pt R d 1) = F.F :=
      funext fun j => MultiplicativeSeries.ev_self_two _
    rw [hadd] at hψ
    exact ⟨ChartUniv.jetRen (fun j => (0, j)) m, ChartUniv.jetRen (fun j => (1, j)) m, ψ,
      ChartUniv.jetRen_zR _ m, ChartUniv.jetRen_zR _ m, hψ, hψ'⟩

end Jets

section Choice

theorem exists_columns {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) {T : Type} [Fintype T] [DecidableEq T] {r : T → ℕ} (Has : ((Σ t, Fin (r t)) → O) → Prop)
    (h0 : Has 0) (hadd : ∀ z z', Has z → Has z' → Has (z + z')) {N : Type} (f : N → (Σ t, Fin (r t)) → O)
    (hf : ∀ i t, Has fun l => (if t = l.1 then 1 else 0) * f i l) {c : O} (hc : c ≠ 0)
    (hspan : ∀ t (x : Fin (r t) → O), c • x ∈ Submodule.span O (Set.range fun i a => f i ⟨t, a⟩))
    (n : ℕ) (col : ∀ t, Fin (r t) → Fin n) (hcol : ∀ t, Function.Injective (col t)) :
    ∃ y : (Σ t, Fin (r t)) × Fin n → O, (∀ b, Has fun l => y (l, b)) ∧ ∀ t (s : Fin (r t)),
      v (algebraMap O C c) ^ (s.val + 1) ≤ v (algebraMap O C (Matrix.of fun a i : Fin (s.val + 1) =>
        y (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det) := by
  choose u hu hmin using fun t => exists_leading_minors_ge C v O hv (r t) _ c hc (hspan t)
  choose g hg using hu
  let Y : Fin n → (Σ t, Fin (r t)) → (Σ t, Fin (r t)) → O := fun b σ =>
    if col σ.1 σ.2 = b then fun l => (if σ.1 = l.1 then 1 else 0) * f (g σ.1 σ.2) l else 0
  have hY : ∀ b σ, Has (Y b σ) := fun b σ => by
    by_cases hb : col σ.1 σ.2 = b
    · simp only [Y, if_pos hb]
      exact hf _ _
    · simp only [Y, if_neg hb]
      exact h0
  refine ⟨fun q => (∑ σ, Y q.2 σ) q.1, fun b => Finset.sum_induction _ Has hadd h0 fun σ _ => hY b σ, ?_⟩
  have key : ∀ t (a i : Fin (r t)), (∑ σ, Y (col t i) σ) ⟨t, a⟩ = u t i a := by
    intro t a i
    rw [Finset.sum_apply, Finset.sum_eq_single (⟨t, i⟩ : Σ t, Fin (r t))]
    · rw [← hg t i]
      simp [Y]
    · rintro ⟨t', i'⟩ _ hne
      by_cases ht : t' = t
      · subst ht
        have : col t' i' ≠ col t' i := fun h => hne (by rw [hcol t' h])
        simp [Y, this]
      · by_cases hb : col t' i' = col t i <;> simp [Y, hb, ht]
    · intro h
      exact absurd (Finset.mem_univ _) h
  intro t s
  simp only [key]
  exact hmin t s

theorem smul_mem_span_pairing {O N : Type} [CommRing O] {d r : ℕ} {c : O} (w : N → Fin d → O)
    (hw : ∀ g : Fin d → O, c • g ∈ Submodule.span O (Set.range w)) (e lam : Fin r → Fin d → O)
    (hlam : ∀ i i', ∑ s, lam i s * e i' s = if i = i' then 1 else 0) (x : Fin r → O) :
    c • x ∈ Submodule.span O (Set.range fun i a => ∑ j, e a j * w i j) := by
  have h := Submodule.mem_map_of_mem (f := Matrix.mulVecLin (Matrix.of e)) (hw (∑ i, x i • lam i))
  rw [Submodule.map_span, map_smul, ← Set.range_comp] at h
  have e1 : Matrix.mulVecLin (Matrix.of e) (∑ i, x i • lam i) = x := by
    funext a
    have : ∀ i, Matrix.mulVecLin (Matrix.of e) (lam i) a = if i = a then 1 else 0 := fun i => by
      rw [← hlam]
      show ∑ s, e a s * lam i s = _
      exact Finset.sum_congr rfl fun s _ => mul_comm _ _
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, this]
    simp
  rw [e1] at h
  exact h

end Choice

section Dlog

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {V O F Λ L : Type} [CommRing V] [CommRing O] [CommRing F] [Algebra ℚ F] [Algebra V F] [Algebra O F]
  [CommRing Λ] [StarRing Λ] {d : ℕ}

def HasDlog (F : Type) [CommRing F] [Algebra ℚ F] [Algebra V F] [Algebra O F] (B : FB V d Λ) (I : Ideal O)
    (e : L → Fin d → O) (yy : L → O) : Prop :=
  ∃ (u : PS O 1 d) (z : L → O), IsCh (B.FK F) (MvPowerSeries.map (algebraMap O F) u) ∧
    (∀ l, algebraMap O F (z l) = ∑ j, algebraMap O F (e l j) * dl (MvPowerSeries.map (algebraMap O F) u) j) ∧
    ∀ l, yy l - z l ∈ I

theorem hasDlog_zero (B : FB V d Λ) (I : Ideal O) (e : L → Fin d → O) : HasDlog F B I e 0 :=
  ⟨1, 0, by rw [map_one]; exact isCh_one _, fun l => by simp [dl_one], fun l => by simp⟩

theorem HasDlog.add {B : FB V d Λ} {I : Ideal O} {e : L → Fin d → O} {y y' : L → O} (h : HasDlog F B I e y)
    (h' : HasDlog F B I e y') : HasDlog F B I e (y + y') := by
  obtain ⟨u, z, h1, h2, h3⟩ := h
  obtain ⟨u', z', h1', h2', h3'⟩ := h'
  refine ⟨u * u', z + z', by rw [map_mul]; exact isCh_mul (WickVanishing.Nab.lawK F B) h1 h1', fun l => ?_, fun l => ?_⟩
  · rw [Pi.add_apply, map_add, h2, h2', map_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [dl_mul h1.1 h1'.1, mul_add]
  · have := I.add_mem (h3 l) (h3' l)
    simp only [Pi.add_apply]
    convert this using 1
    ring

theorem isCh_map (f : V →+* O) (hf : ∀ r, algebraMap O F (f r) = algebraMap V F r) (B : FB V d Λ) {u : PS O 1 d}
    (hu : IsCh (B.G.mapF f) u) : IsCh (B.FK F) (MvPowerSeries.map (algebraMap O F) u) := by
  refine ⟨by rw [constantCoeff_map, hu.1, map_one], ?_⟩
  have h := congrArg (MvPowerSeries.map (algebraMap O F)) hu.2
  have a1 : addOf (B.G.mapF f) (pt O (n := 2) d 0) (pt O d 1) = B.G.mapF f :=
    funext fun j => MultiplicativeSeries.ev_self_two _
  have a2 : addOf (B.FK F) (pt F (n := 2) d 0) (pt F d 1) = B.FK F :=
    funext fun j => MultiplicativeSeries.ev_self_two _
  have cz : CZ (![B.G.mapF f] : Fin 1 → Pt O 2 d) := CZ.cons (fun i => by
    show constantCoeff (MvPowerSeries.map f _) = 0
    rw [constantCoeff_map, B.G.const, map_zero]) CZ.nil
  rw [a1, map_mul, WickVanishing.Nab.map_ev _ cz, WickVanishing.Nab.map_ev _ (cz_pt 0), WickVanishing.Nab.map_ev _ (cz_pt 1)] at h
  rw [a2]
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    funext j i
    fin_cases j
    ext mo
    exact (hf _).symm
  · congr 2
    · funext j i
      fin_cases j
      exact WickVanishing.Nab.map_pt F 0 i
    · funext j i
      fin_cases j
      exact WickVanishing.Nab.map_pt F 1 i

theorem hasDlog_pull (f : V →+* O) (hf : ∀ r, algebraMap O F (f r) = algebraMap V F r) (B : FB V d Λ) (I : Ideal O)
    (e : L → Fin d → O) (a : Λ) (s δ : L → O)
    (he : ∀ l, (dAct F B a).mulVec (fun i => algebraMap O F (e l i)) =
      algebraMap O F (s l) • fun i => algebraMap O F (e l i))
    (hs : ∀ l, s l - δ l ∈ I) {u : PS O 1 d} (hu : IsCh (B.G.mapF f) u) :
    HasDlog F B I e fun l => δ l * ∑ j, e l j * dl u j := by
  have cz : CZ (![fun i => MvPowerSeries.map f (B.A.act a i)] : Fin 1 → Pt O 1 d) := CZ.cons (fun i => by
    rw [constantCoeff_map, B.A.const, map_zero]) CZ.nil
  have hm : MvPowerSeries.map (algebraMap O F) (ev ![fun i => MvPowerSeries.map f (B.A.act a i)] u) =
      ev ![B.actK F a] (MvPowerSeries.map (algebraMap O F) u) := by
    rw [WickVanishing.Nab.map_ev _ cz]
    congr 1
    funext j i
    fin_cases j
    ext mo
    exact hf _
  refine ⟨ev ![fun i => MvPowerSeries.map f (B.A.act a i)] u, fun l => s l * ∑ j, e l j * dl u j, ?_, fun l => ?_,
    fun l => ?_⟩
  · rw [hm]
    exact isCh_pull (WickVanishing.Nab.lawK F B) (PointMapComposition.actKO F B) a (isCh_map f hf B hu)
  · rw [hm]
    have hc : ∀ i, constantCoeff (B.actK F a i) = 0 := (PointMapComposition.actKO F B).const a
    simp only [dl_pull hc, Finset.mul_sum, map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := congrFun (he l) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [← mul_assoc, ← h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (dAct F B a i j), mul_assoc, mul_comm (dAct F B a i j)]
    rfl
  · rw [← sub_mul, ← neg_sub]
    exact I.mul_mem_right _ (I.neg_mem (hs l))

end Dlog

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

theorem charAt_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
    [IsDomain V] [IsDiscreteValuationRing V] {F : Type} [Field F] [Algebra (FractionRing V) F]
    (y : FamGerm.Pt1 E H V F) {a : 𝓞 E} {p : ℕ} {L : Type} {e : L → Fin y.d → TWO.Ov y.v} {z yy : L → TWO.Ov y.v}
    (h : y.CharAt a p e z) (hz : ∀ l, yy l - z l ∈ Ideal.span {(p : TWO.Ov y.v)}) : y.CharAt a p e yy := by
  obtain ⟨κ, Z, jZ, k, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨κ, Z, jZ, k, h1, h2, h3, h4, h5, h6, h7, fun l => ?_⟩
  rw [Ideal.Quotient.eq.2 (hz l)]
  exact h8 l

theorem characters_exist_of_chartBound : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F) := by
  intro hHT p _ E _ _ _ H V _ _ _ F _ _ _ _ _ _ y
  let _ := H.starRing
  intro hcomp hp a ha huu T _ _ rk τ e heig hτa hlam ⟨ε, hε⟩ c hc n col hcol
  have := y.complete
  have hpp : p.Prime := Fact.out
  have hpF : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  let f := TWO.fO y.v y.hϖ y.hv
  have hloc : IsLocalHom f := TWO.isLocalHom_fO _ _ _
  have hf : ∀ r, algebraMap (TWO.Ov y.v) F (f r) = algebraMap V F r := fun r =>
    (IsScalarTower.algebraMap_apply V (FractionRing V) F r).symm
  have : CharZero V := RingHom.charZero (algebraMap V F)
  obtain ⟨v', hv', hint⟩ := exists_nnreal_valuation_of_addValuation F y.v
  have : Fact ¬IsUnit (p : TWO.Ov y.v) := ⟨hp⟩
  obtain ⟨x', hx'⟩ := exists_isChartJ y.t.G y.x y.hx y.B.G y.hB.law
  obtain ⟨N, u, hu, hspan⟩ := hHT p V (fun h => hp (by simpa using h.map f)) y.t.G y.P.D y.P.A y.P.U.toUnifPre y.d
    y.B.G x' hx' F v' (TWO.Ov y.v) hint f hloc
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 : p - 1 ≠ 0 := by have := hpp.two_le; omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h1
    rw [hm, ZeroMemClass.coe_zero, AddValuation.map_zero, succ_nsmul, add_top] at hc
    exact (AddValuation.ne_top_iff y.v).2 hpF hc.symm
  have hspan' := hspan c (by
    rw [← map_pow, hv', AddValuation.map_pow, map_natCast]
    exact hc.ge)
  obtain ⟨yy, hyy, hmin⟩ := exists_columns v' hint (HasDlog F y.B (Ideal.span {(p : TWO.Ov y.v)}) e)
    (hasDlog_zero _ _ _) (fun _ _ h h' => h.add h') (fun i l => ∑ j, e l j * Pdiv.ChartF.dl (u i) j)
    (fun i t => hasDlog_pull f hf y.B _ e (ε t) (fun l => τ l.1 (ε t)) (fun l => if t = l.1 then 1 else 0)
      (heig (ε t)) (fun l => hε t l.1) (hu i)) hc0
    (fun t x => by
      obtain ⟨lam, hlam⟩ := hlam t
      exact smul_mem_span_pairing _ hspan' (fun i => e ⟨t, i⟩) lam hlam x) n col hcol
  refine ⟨yy, fun b => ?_, fun t s => ?_⟩
  · obtain ⟨w, z, h1, h2, h3⟩ := hyy b
    have hadd : addOf (y.B.FK F) (pt F (n := 2) y.d 0) (pt F y.d 1) = y.B.FK F :=
      funext fun j => MultiplicativeSeries.ev_self_two _
    refine charAt_congr y (SeriesCharacter.charAt_of_multiplicative_series firstFiveLaws.1 firstFiveLaws.2.1
      firstFiveLaws.2.2.2.1 twistBaseChange_and_valuation_statements.1 p hpp E H V F y hcomp hp a ha huu _ e
      (fun l => τ l.1 a) (fun l => hτa l.1) (heig a) _ (fun mo => (MvPowerSeries.coeff mo w).2) h1.1
      (hadd ▸ h1.2) z fun l => ?_) h3
    have h4 := MultiplicativeSeries.main F y.d (TB.WickVanishing.Nab.lawK F y.B) _ h1.2 (fun i => (e l i : F))
    have h5 := congrArg MvPowerSeries.constantCoeff h4
    rw [map_mul, h1.1, _root_.mul_one, MvPowerSeries.constantCoeff_C] at h5
    exact (h2 l).trans h5.symm
  · have h1 := hmin t s
    rw [← map_pow, hv', AddValuation.map_pow] at h1
    exact h1

end GlobalTheory.ChartCharacter
