import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ScaledBilinearLog
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdSy
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.IntegralFamilyPointZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameTwistCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf CZ)
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledBilinearLog

attribute [local instance] Over.cartesianMonoidalCategory

section Series

open MvPowerSeries

variable {S : Type} [CommRing S]

def lin {σ : Type} (v : σ) (f : MvPowerSeries σ S) : S := constantCoeff (pderiv S v f)

def quad {σ : Type} (v w : σ) (f : MvPowerSeries σ S) : S := constantCoeff (pderiv S v (pderiv S w f))

theorem lin_eq_coeff {σ : Type} (v : σ) (f : MvPowerSeries σ S) : lin v f = coeff (Finsupp.single v 1) f := by
  rw [lin, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

variable {n d : ℕ}

def bil (c : Fin d → Fin d → S) (P Q : Pt S n d) : PS S n d := ∑ i, ∑ l, c i l • (P i * Q l)

variable {c : Fin d → Fin d → S} {P Q : Pt S n d}

theorem cc_bil (hP : ∀ i, constantCoeff (P i) = 0) : constantCoeff (bil c P Q) = 0 := by
  simp [bil, hP]

theorem lin_bil (hP : ∀ i, constantCoeff (P i) = 0) (hQ : ∀ i, constantCoeff (Q i) = 0) (v : Fin n × Fin d) :
    lin v (bil c P Q) = 0 := by
  simp [bil, lin, Derivation.leibniz, hP, hQ]

theorem quad_bil (hP : ∀ i, constantCoeff (P i) = 0) (hQ : ∀ i, constantCoeff (Q i) = 0) (v w : Fin n × Fin d) :
    quad v w (bil c P Q) =
      ∑ i, ∑ l, c i l * (lin v (P i) * lin w (Q l) + lin w (P i) * lin v (Q l)) := by
  simp only [bil, lin, quad, map_sum, Derivation.map_smul, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    constantCoeff_smul, hP, hQ]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable [Algebra ℚ S]

theorem cc_exp {g : PS S n d} (h0 : constantCoeff g = 0) : constantCoeff (expP g) = 1 :=
  TB.WickVanishing.constantCoeff_exp h0

theorem lin_exp {g : PS S n d} (h0 : constantCoeff g = 0) (v : Fin n × Fin d) : lin v (expP g) = lin v g := by
  have h := TB.WickVanishing.Nab.pderiv_expS h0 v
  have h1 := cc_exp h0
  change pderiv S v (expP g) = expP g * _ at h
  simp [lin, h, h1]

theorem quad_exp {g : PS S n d} (h0 : constantCoeff g = 0) (v w : Fin n × Fin d) (h1 : lin w g = 0) :
    quad v w (expP g) = quad v w g := by
  have h := TB.WickVanishing.Nab.pderiv_expS h0 w
  have h2 := cc_exp h0
  change pderiv S w (expP g) = expP g * _ at h
  unfold lin at h1
  simp [quad, h, h1, h2, Derivation.leibniz]

omit [Algebra ℚ S] in
theorem lin_comp1 (φ : Pt S 1 d) {a : Pt S n d} (ha : ∀ i, constantCoeff (a i) = 0) (v : Fin n × Fin d) (i : Fin d) :
    lin v (comp1 φ a i) = ∑ j, dLin φ i j * lin v (a j) := by
  have hz : CZ (![a] : Fin 1 → Pt S n d) := fun j i => by fin_cases j; exact ha i
  unfold comp1
  rw [lin, TB.LogPf.pderiv_ev hz, Fintype.sum_prod_type, Fin.sum_univ_one, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, TB.LogPf.cc_ev hz]
  congr 1
  exact lin_eq_coeff _ _

omit [Algebra ℚ S] in
theorem lin_pt (j : Fin n) (i : Fin d) (v : Fin n × Fin d) : lin v (pt S d j i) = if v = (j, i) then 1 else 0 := by
  rw [lin, TB.LogPf.pderiv_pt]
  split_ifs <;> simp_all

theorem isLog_logOf (G : FGLaw S d) : IsLog G (logOf G) := by
  refine ⟨fun i => TB.LogPf.constantCoeff_prim _, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    have h := congrArg constantCoeff (TB.LogPf.pderiv_logOf G i j)
    have h2 := congrFun (congrFun (TB.LogPf.cc_om G) i) j
    simp only [Matrix.map_apply] at h2
    rw [h2] at h
    exact (lin_eq_coeff _ _).symm.trans h
  · funext i
    show ev (n := 2) ![G.add (pt S d 0) (pt S d 1)] (logOf G i) =
      ev (n := 2) ![pt S d 0] (logOf G i) + ev (n := 2) ![pt S d 1] (logOf G i)
    rw [TB.LogPf.addPt]
    exact TB.LogPf.logOf_add G i

theorem lg_eq (G : FGLaw S d) (j : Fin n) : lg G j = comp1 (logOf G) (pt S d j) := rfl

theorem bilLog_eq_bil (ℓ : Pt S 1 d) (c : Fin d → Fin d → S) (P Q : Pt S n d) :
    bilLog ℓ (Matrix.of c) P Q = bil c (comp1 ℓ P) (comp1 ℓ Q) := by
  simp only [bilLog, bil, Matrix.of_apply, smul_eq_C_mul, _root_.mul_assoc]

omit [Algebra ℚ S] in
theorem cc_pt (j : Fin n) (i : Fin d) : constantCoeff (pt S d j i) = 0 := by
  simp [pt]

omit [Algebra ℚ S] in
theorem ev_comp1_pt {k : ℕ} {a : Fin k → Pt S n d} (ha : CZ a) (φ : Pt S 1 d) (j : Fin k) (i : Fin d) :
    ev a (comp1 φ (pt S d j) i) = comp1 φ (a j) i := by
  have hb : CZ (![pt S d j] : Fin 1 → Pt S k d) := fun j' i => by fin_cases j'; exact cc_pt j i
  rw [comp1, comp1, TB.LogPf.ev_ev ha hb]
  congr 1
  funext j' i
  fin_cases j'
  exact TB.LogPf.ev_X ha j i

theorem ev_bilL_eq (G : FGLaw S d) (c : Fin d → Fin d → S) {a : Fin 2 → Pt S n d} (ha : CZ a) :
    ev a (bilL G c) = bilLog (logOf G) (Matrix.of c) (a 0) (a 1) := by
  simp only [bilL, bilLog, lg_eq, smul_eq_C_mul, TB.LogPf.ev_sum ha, TB.LogPf.ev_mul ha, TB.LogPf.ev_C ha,
    ev_comp1_pt ha, Matrix.of_apply, _root_.mul_assoc]

theorem bilL_eq (G : FGLaw S d) (c : Fin d → Fin d → S) :
    bilL G c = bilLog (logOf G) (Matrix.of c) (pt S (n := 2) d 0) (pt S (n := 2) d 1) := by
  rw [bilLog_eq_bil]
  rfl

theorem cc_comp1_log (G : FGLaw S d) {a : Pt S n d} (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) :
    constantCoeff (comp1 (logOf G) a i) = 0 :=
  TB.WickVanishing.cc_comp1 _ _ (isLog_logOf G).1 ha i

theorem lin_comp1_log (G : FGLaw S d) {a : Pt S n d} (ha : ∀ i, constantCoeff (a i) = 0) (v : Fin n × Fin d)
    (i : Fin d) : lin v (comp1 (logOf G) a i) = lin v (a i) := by
  rw [lin_comp1 _ ha, (isLog_logOf G).2.1]
  simp [Matrix.one_apply]

theorem cc_bilL (G : FGLaw S d) (c : Fin d → Fin d → S) : constantCoeff (bilL G c) = 0 := by
  rw [bilL_eq, bilLog_eq_bil, cc_bil (cc_comp1_log G (cc_pt 0))]

theorem ev_expP (G : FGLaw S d) (c : Fin d → Fin d → S) {a : Fin 2 → Pt S n d} (ha : CZ a) :
    ev a (expP (-bilL G c)) = expP (-ev a (bilL G c)) := by
  have hg : constantCoeff (-bilL G c) = 0 := by rw [map_neg, cc_bilL, neg_zero]
  rw [← TB.LogPf.ev_neg ha]
  exact TB.WickVanishing.subst_exp (fun p : Fin 2 × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) hg

theorem cc_ev_twist (G : FGLaw S d) (c : Fin d → Fin d → S) {a : Fin 2 → Pt S n d} (ha : CZ a) :
    constantCoeff (ev a (expP (-bilL G c))) = 1 := by
  rw [TB.LogPf.cc_ev ha, cc_exp]
  rw [map_neg, cc_bilL, neg_zero]

theorem quad_ev_twist (G : FGLaw S d) (c : Fin d → Fin d → S) {a : Fin 2 → Pt S n d} (ha : CZ a)
    (v w : Fin n × Fin d) :
    quad v w (ev a (expP (-bilL G c))) =
      -∑ i, ∑ l, c i l * (lin v (a 0 i) * lin w (a 1 l) + lin w (a 0 i) * lin v (a 1 l)) := by
  have h0 := cc_comp1_log G (ha 0)
  have h1 := cc_comp1_log G (ha 1)
  rw [ev_expP G c ha, ev_bilL_eq G c ha, bilLog_eq_bil, quad_exp]
  · have := quad_bil (c := c) h0 h1 v w
    simp only [lin_comp1_log G (ha 0), lin_comp1_log G (ha 1)] at this
    rw [← this]
    simp [quad]
  · rw [map_neg, cc_bil h0, neg_zero]
  · have := lin_bil (c := c) h0 h1 w
    unfold lin at this ⊢
    rw [map_neg, map_neg, this, neg_zero]

end Series

section Jets

open MvPolynomial

variable {S : Type} [CommRing S] {d : ℕ}

theorem jetSubstP_psJet {n n' : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    {a : Fin n → Pt S n' d} (ha : CZ a) (hφ : ∀ p, constantCoeff (φ p) = 0)
    (hmk : ∀ p : Fin n × Fin d,
      Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (φ p) = psJet m (a p.1 p.2))
    (f : PS S n d) : jetSubstP m φ (psJet m f) = psJet m (ev a f) := by
  rw [ev, FBIdJet.psJet_subst m _ (fun p => ha p.1 p.2) f]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [GermD.jetMap_mk, aeval_X]
  simp only [jetSubstP, GermD.jetMap_mk, aeval_X, hφ p, map_zero, sub_zero]
  rw [hmk p]
  rfl

theorem mk_psIn_psJet {n' : ℕ} (m : ℕ) (k : Fin n') (f : PS S 1 d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (psIn d m ![k] f) =
      psJet m (ev ![pt S d k] f) := by
  have e : (![pt S d k] : Fin 1 → Pt S n' d) = fun i => pt S d ((![k] : Fin 1 → Fin n') i) := by
    funext i; fin_cases i; rfl
  rw [e, FBIdPh.psJet_ev_rel, psIn, FBIdPh.mk_rename]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [GermD.jetMap_mk, aeval_X]
  simp only [jetSubstP, GermD.jetMap_mk, aeval_X, FBIdPh.rel, constantCoeff_X, map_zero, sub_zero]

theorem cz_left {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    CZ (![comp1 φ (pt S d 0), pt S d 1] : Fin 2 → Pt S 2 d) := by
  intro j i
  fin_cases j
  · exact (TB.LogPf.cc_ev TB.LogPf.czX _).trans (hφ i)
  · exact cc_pt _ i

theorem cz_right {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    CZ (![pt S d 0, comp1 φ (pt S d 1)] : Fin 2 → Pt S 2 d) := by
  intro j i
  fin_cases j
  · exact cc_pt _ i
  · exact (TB.LogPf.cc_ev TB.LogPf.czY _).trans (hφ i)

theorem jetSubstP_left (m : ℕ) {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (f : PS S 2 d) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (φ j), fun j => X ((1 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m f) =
      psJet m (ev (n := 2) ![comp1 φ (pt S d 0), pt S d 1] f) := by
  refine jetSubstP_psJet m _ (cz_left hφ) ?_ ?_ f
  · rintro ⟨i, j⟩
    fin_cases i
    · exact (FBIdPh.cc_psIn d m _ _).trans (hφ j)
    · simp
  · rintro ⟨i, j⟩
    fin_cases i
    · exact mk_psIn_psJet m 0 (φ j)
    · exact (FBIdSy.mk_psTrunc_X m _).symm

theorem jetSubstP_right (m : ℕ) {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (f : PS S 2 d) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (φ j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m f) =
      psJet m (ev (n := 2) ![pt S d 0, comp1 φ (pt S d 1)] f) := by
  refine jetSubstP_psJet m _ (cz_right hφ) ?_ ?_ f
  · rintro ⟨i, j⟩
    fin_cases i
    · simp
    · exact (FBIdPh.cc_psIn d m _ _).trans (hφ j)
  · rintro ⟨i, j⟩
    fin_cases i
    · exact (FBIdSy.mk_psTrunc_X m _).symm
    · exact mk_psIn_psJet m 1 (φ j)

variable [Algebra ℚ S]

end Jets

section Frames

open MvPolynomial (X)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} {d : ℕ}
variable {x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G}

variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
  {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} {e e' : ∀ m, FrTy y d x m}

end Frames

section Clauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]
variable (y : FrPt Xo c S) (C : ChartAt Xo c y)

def cut {d : ℕ} (cc : ℕ → Fin d → Fin d → S) (m : ℕ) : Fin d → Fin d → S := if m ≤ 1 then 0 else cc m

end Clauses

end GlobalTheory.FrameTwistCompare
