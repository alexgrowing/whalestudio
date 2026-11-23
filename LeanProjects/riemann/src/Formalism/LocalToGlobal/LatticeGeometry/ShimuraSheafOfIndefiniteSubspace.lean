import Formalism.LocalToGlobal.LatticeGeometry.CompNe
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Geo

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)}
  {ng : NgPkg}

private theorem permExp_degree_eq_dimFl {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) :
    (Formalism.DegreeFormula.permExp σ).degree = Formalism.DegreeFormula.dimFl ι N := by
  rw [Finsupp.degree_eq_sum]
  simp only [Formalism.DegreeFormula.permExp, Finsupp.coe_equivFunOnFinite_symm]
  rw [Fintype.sum_prod_type]
  have h1 : ∀ τ : ι, ∑ i : Fin N, (N - 1 - ((σ τ i : Fin N) : ℕ)) = N * (N - 1) / 2 := by
    intro τ
    rw [Equiv.sum_comp (σ τ) (fun i : Fin N => N - 1 - (i : ℕ))]
    rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
    rw [Finset.sum_range_reflect (fun i => i) N]
    exact Finset.sum_range_id N
  simp only [h1, Finset.sum_const, Finset.card_univ, smul_eq_mul, Formalism.DegreeFormula.dimFl]

theorem chernOf_homog (Tau : Type) [Fintype Tau] (N : ℕ) (vol : ℝ) (P : MvPolynomial (DV.Rt Tau N) ℝ)
    (d : ℕ) (hd : d ≠ Formalism.DegreeFormula.dimFl Tau N) (hP : P.IsHomogeneous d) : chernOf Tau N vol P = 0 := by
  have hc : ∀ σ : Tau → Equiv.Perm (Fin N), P.coeff (Formalism.DegreeFormula.permExp σ) = 0 := fun σ =>
    hP.coeff_eq_zero (by rw [permExp_degree_eq_dimFl]; exact fun h => hd h.symm)
  simp [chernOf, degFlL, LinearMap.sum_apply, MvPolynomial.lcoeff_apply, hc]

def toShimX {w : Dat D Lev} (U : ShimU D G jC ng w) (h : w.Indef) (lev : Finset ℕ)
    (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX D.what₂.Tau where
  N := w.N
  j := w.j
  j_pos := h.1
  j_lt := h.2
  lev := lev
  lev_prime := hlev
  Comp := U.Comp
  vol := U.cx.vol
  chern := U.cx.chern
  chern_homog := fun P d hd hP => chernOf_homog D.what₂.Tau w.N U.cx.vol P d hd hP
  arDeg := U.pad.arDeg
  arDeg_homog := U.pad.arDeg_homog
  arMix := U.pad.arMix
  arMix_HT := U.pad.arMix_HT
  arMix_DR := U.pad.arMix_DR
  CurveHT := U.pad.CurveHT
  degHT := U.pad.degHT
  CurveDR := U.pad.CurveDR
  degDR := U.pad.degDR
  FibComp := U.pad.FibComp
  fibInBd := U.pad.fibInBd
  Pt := U.pad.Pt
  phiDR := U.pad.phiDR
  phiMod := U.pad.phiMod
  phiFr := U.pad.phiFr
  XC := U.cx.XC
  rfn := U.cx.rfn
  rfn_ge := U.cx.rfn_ge
  hLo := U.cx.hLo
  hUp := U.cx.hUp
  hLo_le := U.cx.hLo_le
  connN := U.cx.connN
  curvN := U.cx.curvN
  compOf := U.cx.compOf
  normDetInf := U.cx.normDetInf
  compPt := U.pad.compPt
  normDetT := U.pad.normDetT
  normDetH := U.pad.normDetH
  htDetT := U.pad.htDetT
  ALB := U.alg.ALB
  arSelf := fun L => ∑ c, U.alg.arSelfC L c
  arSelfC := U.alg.arSelfC
  arSelf_sum := fun _ => rfl
  geo := fun L => ∑ c, U.alg.geoC L c
  geoC := U.alg.geoC
  geo_sum := fun _ => rfl
  arVol := U.alg.arVol
  semipos := U.alg.semipos
  nefFib := U.alg.nefFib
  arNef := U.alg.arNef
  Mbar := U.alg.Mbar

structure CompatibleLevelPrimes (X : DivX D) (levPr : X.Lev → Finset ℕ) (hlev : ∀ κ, ∀ p ∈ levPr κ, p.Prime)
    (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w) : Prop where
  lev : X.levPr = levPr
  shv : ∀ (w : Dat D X.Lev) (h : w.Indef), X.shv w.S w.κ = toShimX (U w) h (levPr w.κ) (hlev w.κ)

structure CompatiblePlaces' (X : DivX D) (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p)
    (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w) : Prop where
  wt : ∀ (p : ℕ) [Fact p.Prime] (la : X.PlP p), X.wtP p la = wtL D p (ePl p la)
  jc : ∀ (p : ℕ) [Fact p.Prime] (la : X.PlP p), X.jC p la = jC p (ePl p la)
  mp : ∀ (w : Dat D X.Lev), w.Indef → ∀ (p : ℕ) [Fact p.Prime] (la : X.PlP p),
    X.Mp w.S w.κ p la = (U w).pad.Mp p (ePl p la)
  md : ∀ (w : Dat D X.Lev), w.Indef → ∀ (p : ℕ) [Fact p.Prime] (la : X.PlP p),
    HEq (X.md w.S w.κ p la) ((U w).pad.md p (ePl p la))
  curveM : ∀ (w : Dat D X.Lev), w.Indef → ∀ (p : ℕ) [Fact p.Prime] (la : X.PlP p),
    HEq (X.CurveM w.S w.κ p la) ((U w).pad.CurveM p (ePl p la))
  degM : ∀ (w : Dat D X.Lev), w.Indef → ∀ (p : ℕ) [Fact p.Prime] (la : X.PlP p),
    HEq (X.degM w.S w.κ p la) ((U w).pad.degM p (ePl p la))
  htMdl : ∀ (w : Dat D X.Lev), w.Indef → ∀ (p : ℕ) [Fact p.Prime] (la : X.PlP p),
    HEq (X.htMdl w.S w.κ p la) ((U w).pad.htMdl p (ePl p la))

  htCurve : ∀ (w : Dat D X.Lev), w.Indef → ∀ (p : ℕ) [Fact p.Prime] (c : (X.shv w.S w.κ).CurveHT p)
    (c' : (U w).pad.CurveHT p), HEq c c' →
      ePl p (X.htCurve w.S w.κ p c).1 = c'.1 ∧ HEq (X.htCurve w.S w.κ p c).2 c'.2

structure CompatibleGeometry (X : DivX D) (κg : X.Lev) (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (U (datW D κg j)).Comp) : Prop where
  yv : ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) c, X.Yv j c = (U (datW D κg j)).alg.Yv (eC j h1 h2 c)
  ybd : ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) c, HEq (X.Ybd j c) ((U (datW D κg j)).alg.Ybd (eC j h1 h2 c))
  lw : ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) c (la : D.what₂.Tau → Fin D.R.r → ℤ),
    HEq (X.Lw j c la) ((U (datW D κg j)).alg.Lw (eC j h1 h2 c)
      (fun τ i => la τ (Fin.cast (datW_N D κg j) i)))

structure TiedX (X : DivX D) (levPr : X.Lev → Finset ℕ) (hlev : ∀ κ, ∀ p ∈ levPr κ, p.Prime) (κg : X.Lev)
    (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p) (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (U (datW D κg j)).Comp) : Prop where
  shv : CompatibleLevelPrimes X levPr hlev U
  pl : CompatiblePlaces' X ePl U
  geo : CompatibleGeometry X κg U eC

  lev_κg : levPr κg = Finset.univ.image D.host.g

theorem comp_nonempty (X : DivX D) (κg : X.Lev) (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (U (datW D κg j)).Comp) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) : Nonempty (X.Comp j) :=
  (eC j h1 h2).nonempty_congr.mpr (U (datW D κg j)).compNe

def MumfordU {w : Dat D Lev} (U : ShimU D G jC ng w) : Prop :=
  ∀ (c : U.Comp) (la : D.what₂.Tau → Fin w.N → ℤ),
    ((G.inter (U.alg.Yv c) (fun _ => U.alg.Lw c la) : ℤ) : ℝ) =
      U.cx.volC c * (by classical exact Formalism.DegreeFormula.flagDeg D.what₂.Tau w.N (fun τ i => (la τ i : ℝ)))

theorem chern_linRoot_pow {w : Dat D Lev} (U : ShimU D G jC ng w) (hM : MumfordU U)
    (la : D.what₂.Tau → Fin w.N → ℤ) :
    U.cx.chern (Formalism.DegreeFormula.linRoot (fun τ i => (la τ i : ℝ)) ^ Formalism.DegreeFormula.dimFl D.what₂.Tau w.N) =
      ∑ c, ((G.inter (U.alg.Yv c) (fun _ => U.alg.Lw c la) : ℤ) : ℝ) := by
  have h1 : U.cx.chern (Formalism.DegreeFormula.linRoot (fun τ i => (la τ i : ℝ)) ^ Formalism.DegreeFormula.dimFl D.what₂.Tau w.N) =
      U.cx.vol * (by classical exact Formalism.DegreeFormula.flagDeg D.what₂.Tau w.N (fun τ i => (la τ i : ℝ))) := by
    simp only [CxPkg.chern, chernOf, degFlL, Formalism.DegreeFormula.flagDeg, Formalism.DegreeFormula.degFl, LinearMap.smul_apply,
      LinearMap.sum_apply, MvPolynomial.lcoeff_apply, smul_eq_mul]
  rw [h1, CxPkg.vol, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun c _ => (hM c la).symm)

theorem psiOf_cm (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ) (τ : DV.Emb D p) :
    τ ∈ DV.PsiOf D jc ↔ DV.cEmb D τ ∉ DV.PsiOf D jc := by
  exact cm_type_meets_conjugate_pair p jc τ

def CurveHTDom {w : Dat D Lev} (U : ShimU D G jC ng w) : Prop :=
  ∀ (p : ℕ) (n : ℕ) (Z' : (U.pad.loc p).Mdl), p.Prime → 3 ≤ n →
    (U.pad.loc p).IsHTBlowup Z' ((U.pad.loc p).Xn n) → ∀ c : U.pad.CurveHT p,
      ∃ (C : (U.pad.ex p).CrvS Z') (m : ℕ), 0 < m ∧ ∀ (τ : D.what₂.Tau) (i : Fin w.N),
        (m : ℝ) * U.pad.degHT p c (τ, i) = ((U.pad.ex p).degGr C (D.eTau τ) ((i : ℕ) + 1) : ℝ)

theorem shimura_sheaf_of_indefinite_subspace (X : DivX D) (levPr : X.Lev → Finset ℕ) (hlev : ∀ κ, ∀ p ∈ levPr κ, p.Prime)
    (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w) (hT : CompatibleLevelPrimes X levPr hlev U) (κg : X.Lev) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j < D.R.m) :
    X.shv (letI := D.host.cmStar; D.sp.W j) κg =
      toShimX (U (datW D κg j)) (datW_indef D κg h1 h2) (levPr κg) (hlev κg) := by
  have hj : jcl D j = j := by
    unfold jcl
    rw [min_eq_left h2.le, max_eq_right h1]
  have hS : (datW D κg j).S = (letI := D.host.cmStar; D.sp.W j) := by
    dsimp only [datW]
    rw [hj]
  have h := hT.shv (datW D κg j) (datW_indef D κg h1 h2)
  rw [hS] at h
  exact h

theorem chern_toShimX {w : Dat D Lev} (U : ShimU D G jC ng w) (h : w.Indef) (lev : Finset ℕ)
    (hlev : ∀ p ∈ lev, p.Prime) (Q : MvPolynomial (DV.Rt D.what₂.Tau w.N) ℝ) :
    (toShimX U h lev hlev).chern Q =
      (toShimX U h lev hlev).vol * (by classical exact Formalism.DegreeFormula.degFl D.what₂.Tau w.N Q) := by
  show U.cx.chern Q = U.cx.vol * _
  simp only [CxPkg.chern, chernOf, degFlL, Formalism.DegreeFormula.degFl, LinearMap.smul_apply,
    LinearMap.sum_apply, MvPolynomial.lcoeff_apply, smul_eq_mul]

theorem compNe_of (X : DivX D) (κg : X.Lev) (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (U (datW D κg j)).Comp) : Formalism.MainNotions.placeRankTwoOne.CompNe D X :=
  fun j h1 h2 => comp_nonempty X κg U eC j h1 h2

theorem dim_Yv (X : DivX D) (κg : X.Lev) (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (U (datW D κg j)).Comp) (hG : CompatibleGeometry X κg U eC) {j : ℕ} (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (c : X.Comp j) : X.geo.dim (X.Yv j c) = Formalism.DegreeFormula.dimFl D.what₂.Tau D.R.r := by
  rw [hG.yv j h1 h2 c, (U (datW D κg j)).alg.dim_eq, datW_N]

theorem inter_congr (G : DV.Geo D.what₂.LL) {Y Y' : G.Var} (h : Y = Y') (a : G.Dv Y) (a' : G.Dv Y')
    (ha : HEq a a') : G.inter Y (fun _ => a) = G.inter Y' (fun _ => a') := by
  subst h
  rw [eq_of_heq ha]

theorem chern_record (X : DivX D) (κg : X.Lev) (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (U (datW D κg j)).Comp) (hG : CompatibleGeometry X κg U eC) {j : ℕ} (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (hM : MumfordU (U (datW D κg j))) (la : D.what₂.Tau → Fin D.R.r → ℤ) :
    (U (datW D κg j)).cx.chern (Formalism.DegreeFormula.linRoot (fun τ i => ((la τ (Fin.cast (datW_N D κg j) i) : ℤ) : ℝ)) ^
        Formalism.DegreeFormula.dimFl D.what₂.Tau (datW D κg j).N) =
      ∑ c, ((X.geo.inter (X.Yv j c) (fun _ => X.Lw j c la) : ℤ) : ℝ) := by
  rw [chern_linRoot_pow (U (datW D κg j)) hM (fun τ i => la τ (Fin.cast (datW_N D κg j) i))]
  symm
  refine Fintype.sum_equiv (eC j h1 h2) _ _ (fun c => ?_)
  exact congrArg (fun n : ℤ => (n : ℝ)) (inter_congr X.geo (hG.yv j h1 h2 c) _ _ (hG.lw j h1 h2 c la))

end Formalism.L2.Geo
