import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetVal

open AlgebraicGeometry CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

section Pt

variable {K : Type} [Field K] {σ : Type} {m : ℕ}

theorem jet_pt_eq (p : PrimeSpectrum (Jet K σ m)) : p = IsLocalRing.closedPoint (Jet K σ m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_jetAug _ (by rwa [jetAug_mk]))
    have := jet_nilpotent_of_orig K σ m (sub_const_mem_orig (R := K) q)
    rwa [h0, map_zero, sub_zero] at this
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)

end Pt

theorem gs_appLE_top {Y X : Scheme.{0}} (φ : Y ⟶ X) (y : Y) (U : X.Opens) (h : ⊤ ≤ φ ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs φ y U a = gs (𝟙 Y) y ⊤ ((φ.appLE U ⊤ h).hom a) := by
  have hy : φ y ∈ U := h trivial
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, gs_res (𝟙 Y) y h trivial, gs_pull (𝟙 Y) φ y U hy, Category.id_comp]

section PullSec

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A)
  (hh : h ≫ snd T A = snd T' A)

def pullSecF (s : LB.Sec (LPow A L a T)) (j : Fin 1 → L.ι) : Γ((T' ⊗ A).left, (LPow A L a T').U j) :=
  ((T' ⊗ A).left.presheaf.map (homOfLE (chart_le_res A L h hh a j)).op).hom ((h.left.app _).hom (s.f j))

def pullSecLP (s : LB.Sec (LPow A L a T)) : LB.Sec (LPow A L a T') where
  f := pullSecF A L a h hh s
  compat i j := fn_ext fun y hy => by
    have hi : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) i := chart_le_res A L h hh a i hy.1
    have hj : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) j := chart_le_res A L h hh a j hy.2
    have v : ∀ j', y ∈ (LPow A L a T').U j' → gs (𝟙 _) y _ (pullSecF A L a h hh s j') =
        gs (𝟙 _ ≫ h.left) y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j') (s.f j') := fun j' hj' =>
      (gs_res _ y _ hj' _).trans (gs_pull _ h.left y _ (chart_le_res A L h hh a j' hj') _)
    refine ((gs_res (𝟙 _) y _ hy _).trans ((v i hy.1).trans (sec_trans s (𝟙 _ ≫ h.left) y hi hj))).trans ?_
    refine Eq.trans ?_ (gs_mul (𝟙 _) y _ hy _ _).symm
    refine congrArg₂ (· * ·) ?_ ((v j hy.2).symm.trans (gs_res (𝟙 _) y _ hy _).symm)
    refine Eq.trans ?_ (gs_unit (𝟙 _) y _ hy _).symm
    refine congrArg Units.val (Eq.trans ?_
      (gm_linComb L (fun _ : Fin 1 => (snd T' A).left) (fun _ => a) (𝟙 _) y i j hy.1 hy.2).symm)
    simp only [trF, Category.assoc, ← Over.comp_left, hh]

theorem isPullSec_pullSecLP (s : LB.Sec (LPow A L a T)) : IsPullSec A L a h hh s (pullSecLP A L a h hh s) :=
  fun _ => rfl

end PullSec

section Fam

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] (L : LB G.left) {x0 : Sp ℂ ⟶ X} {g : ℕ}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (hol : IsHolFam e) (he : ∀ z, e z ≫ G.hom = x0)

def jB (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ Over.mk x0 :=
  Over.homMk (spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m))) rfl

def xJ (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ G :=
  Over.homMk (jetPt e hol m) (jetPt_over e hol G.hom x0 he m)

def ePt (z : Fin g → ℂ) : Over.mk x0 ⟶ G := Over.homMk (e z) (he z)

def lftJ (z : Fin g → ℂ) : Sp ℂ ⟶ (Over.mk x0 ⊗ G).left := (ptSecT G (ePt e he z)).left

theorem lftJ_snd (z : Fin g → ℂ) : lftJ e he z ≫ (snd (Over.mk x0) G).left = e z := by
  rw [lftJ, ← Over.comp_left, ptSecT, lift_snd]
  rfl

theorem lftJ_fst (z : Fin g → ℂ) : lftJ e he z ≫ (fst (Over.mk x0) G).left = 𝟙 _ := by
  rw [lftJ, ← Over.comp_left, ptSecT, lift_fst]
  rfl

theorem lftJ_eq (holP : IsHolFam (lftJ e he)) (m : ℕ) :
    (ptSecT G (xJ e hol he m)).left ≫ (jB (x0 := x0) (g := g) m ▷ G).left = jetPt (lftJ e he) holP m := by
  have h1 : jetPt (lftJ e he) holP m ≫ (Over.mk x0 ⊗ G).hom =
      spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫ x0 :=
    jetPt_over (lftJ e he) holP _ x0 (fun z => Over.w (ptSecT G (ePt e he z))) m
  let φ : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ Over.mk x0 ⊗ G := Over.homMk (jetPt (lftJ e he) holP m) h1
  suffices hs : ptSecT G (xJ e hol he m) ≫ jB m ▷ G = φ by
    rw [← Over.comp_left, hs]
    rfl
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, whiskerRight_fst, ptSecT, lift_fst_assoc, Category.id_comp]
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    show spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) = jetPt (lftJ e he) holP m ≫ (fst (Over.mk x0) G).left
    rw [jetPt_comp (lftJ e he) holP _ (fun _ => 𝟙 (Sp ℂ)) (isHolFam_const _) (lftJ_fst e he) m, ← jetPt_const,
      Category.comp_id]
  · rw [Category.assoc, whiskerRight_snd, ptSecT, lift_snd]
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    show jetPt e hol m = jetPt (lftJ e he) holP m ≫ (snd (Over.mk x0) G).left
    rw [jetPt_comp (lftJ e he) holP _ e hol (lftJ_snd e he) m]

theorem isValueAt_jet (holP : IsHolFam (lftJ e he)) (m k : ℕ)
    (F : LB.Sec (LPow G L (k : ℤ) (Over.mk x0)))
    (F' : LB.Sec (LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))))
    (hF' : IsPullSec G L (k : ℤ) (jB m ▷ G) (whiskerRight_snd _ _) F F')
    (θF : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ)
    (hfr : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j})
    (hfr0 : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (hrd : ∀ j z (pt : Sp ℂ ⟶ (Over.mk x0 ⊗ G).left), pt ≫ (snd (Over.mk x0) G).left = e z →
      pt ≫ (fst (Over.mk x0) G).left = 𝟙 (Sp ℂ) → ⊤ ≤ e z ⁻¹ᵁ L.U j →
      valAt' pt ((LPow G L (k : ℤ) (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θF z * fr j z ^ (k : ℤ))
    (τ : LB.Gen (LB.LinComb L (Y := (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) (K := Fin 1)
      (fun _ => (xJ e hol he m).left) (fun _ => (k : ℤ))))
    (hτ : ∀ (j : Fin 1 → L.ι) (h : ⊤ ≤ LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) j),
      ((overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left.presheaf.map (homOfLE h).op).hom (τ.s j).val =
        toΓ _ (jetOf m (fun z => fr (j 0) z ^ k))) :
    IsValueAt G L (k : ℤ) F' (xJ e hol he m) τ (toΓ _ (jetOf m θF)) := by
  intro j
  obtain ⟨j0, rfl⟩ : ∃ j0, j = fun _ => j0 := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine fn_ext fun x hx => ?_
  let Φ := (ptSecT G (xJ e hol he m)).left
  let Ψ := (jB (x0 := x0) (g := g) m ▷ G).left
  let U := (LPow G L (k : ℤ) (Over.mk x0)).U (fun _ => j0)
  have key : Φ ≫ Ψ = jetPt (lftJ e he) holP m := lftJ_eq e hol he holP m
  have hW : ⊤ ≤ LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) (fun _ => j0) := fun p _ => by
    have e1 := jet_pt_eq (K := ℂ) (σ := Fin 1 × Fin g) (m := m) p
    have e2 := jet_pt_eq (K := ℂ) (σ := Fin 1 × Fin g) (m := m) x
    rw [e1, ← e2]
    exact hx
  have hmem1 : ∀ p, Φ p ∈ (LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))).U (fun _ => j0) := fun p =>
    val_le G L (xJ e hol he m) (fun _ => j0) (hW (show p ∈ (⊤ : (Sp (Jet ℂ (Fin 1 × Fin g) m)).Opens) from trivial))
  have hmem : ∀ p, Ψ (Φ p) ∈ U := fun p =>
    chart_le_res G L (T := Over.mk x0) (T' := overAt x0 (Jet ℂ (Fin 1 × Fin g) m)) (jB (x0 := x0) (g := g) m ▷ G)
      (whiskerRight_snd _ _) (k : ℤ) (fun _ => j0) (hmem1 p)
  have hU' : ⊤ ≤ jetPt (lftJ e he) holP m ⁻¹ᵁ U := fun p _ => by
    have h2 := hmem p
    rw [← Scheme.Hom.comp_apply, key] at h2
    exact h2
  have hU : lftJ e he 0 cpt ∈ U := by
    have h3 : jetPt (lftJ e he) holP m (IsLocalRing.closedPoint _) ∈ U := hU' trivial
    rwa [jetPt_closedPoint] at h3
  have hU0 : e 0 cpt ∈ L.U j0 := by
    have h4 : (snd (Over.mk x0) G).left (lftJ e he 0 cpt) ∈ L.U j0 := Set.mem_iInter.1 hU 0
    rwa [← Scheme.Hom.comp_apply, lftJ_snd] at h4

  have heq : ∀ᶠ z in nhds 0, valAt' (lftJ e he z) U (F.f (fun _ => j0)) = θF z * fr j0 z ^ k :=
    (eventually_mem e hol hU0).mono fun z hz => by
      rw [hrd j0 z (lftJ e he z) (lftJ_snd e he z) (lftJ_fst e he z) hz, zpow_natCast]
  have hval : ContDiffAt ℂ ω (fun z => valAt' (lftJ e he z) U (F.f (fun _ => j0))) 0 :=
    contDiffAt_val (lftJ e he) holP hU _
  have hfrA : ContDiffAt ℂ ω (fr j0) 0 :=
    (ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ e z ⁻¹ᵁ L.U j0} (fr j0) (hol (L.U j0) 0).1 (hfr j0) 0
      (top_le_of_mem hU0)).contDiffAt
  have hfrk : ContDiffAt ℂ ω (fun z => fr j0 z ^ k) 0 := hfrA.pow k
  have hθ : ContDiffAt ℂ ω θF 0 := by
    refine (hval.div hfrk (pow_ne_zero _ (hfr0 j0 0 (top_le_of_mem hU0)))).congr_of_eventuallyEq ?_
    filter_upwards [heq, eventually_mem e hol hU0] with z hz hz'
    exact eq_div_of_mul_eq (pow_ne_zero _ (hfr0 j0 z hz')) hz.symm
  have hjet : jetOf m (fun z => valAt' (lftJ e he z) U (F.f (fun _ => j0))) =
      jetOf m θF * jetOf m (fun z => fr j0 z ^ k) := by
    rw [jetOf_congr m heq]
    exact jetOf_mul m hθ hfrk

  have s1 : gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x
      (LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) (fun _ => j0))
      ((((overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left).presheaf.map
        (homOfLE (val_le G L (xJ e hol he m) (fun _ => j0))).op).hom
          (((ptSecT G (xJ e hol he m)).left.app _).hom (F'.f (fun _ => j0)))) =
      gs Φ x ((LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))).U (fun _ => j0)) (F'.f (fun _ => j0)) :=
    (gs_res (𝟙 _) x (val_le G L (xJ e hol he m) (fun _ => j0)) hx _).trans
      ((gs_pull (𝟙 _) Φ x _ (hmem1 x) _).trans (by rw [Category.id_comp]))
  have s2 : gs Φ x ((LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))).U (fun _ => j0)) (F'.f (fun _ => j0)) =
      gs (Φ ≫ Ψ) x U (F.f (fun _ => j0)) := by
    rw [hF' (fun _ => j0)]
    exact (gs_res Φ x (chart_le_res G L (T := Over.mk x0) (T' := overAt x0 (Jet ℂ (Fin 1 × Fin g) m))
        (jB (x0 := x0) (g := g) m ▷ G) (whiskerRight_snd _ _) (k : ℤ) (fun _ => j0)) (hmem1 x) _).trans
      (gs_pull Φ Ψ x U (hmem x) _)
  have s3 : gs (Φ ≫ Ψ) x U (F.f (fun _ => j0)) = gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x ⊤
      (toΓ _ (jetOf m θF * jetOf m (fun z => fr j0 z ^ k))) := by
    rw [key, gs_appLE_top _ x U hU', jetPt_appLE (lftJ e he) holP m U hU hU', CommRingCat.comp_apply, jetψ_apply,
      ← hjet]
    rfl

  have r1 : gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x
      (LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) (fun _ => j0))
      ((((overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left).presheaf.map (homOfLE le_top).op).hom
          (toΓ _ (jetOf m θF)) * (τ.s (fun _ => j0)).val) =
      gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x ⊤
        (toΓ _ (jetOf m θF * jetOf m (fun z => fr j0 z ^ k))) := by
    refine (gs_mul (𝟙 _) x _ hx _ _).trans ?_
    refine (congrArg₂ (· * ·) (gs_res (𝟙 _) x le_top hx _)
      ((gs_res (𝟙 _) x hW trivial (τ.s (fun _ => j0)).val).symm.trans
        (congrArg (gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x ⊤) (hτ _ hW)))).trans ?_
    rw [← gs_mul (𝟙 _) x ⊤ trivial, ← map_mul]
  exact (s1.trans (s2.trans s3)).trans r1.symm

theorem isHolFam_lftJ (hol : IsHolFam e) : IsHolFam (lftJ e he) := by
  have hl : lftJ e he = fun z => Limits.pullback.lift (f := x0) (g := G.hom) (𝟙 (Sp ℂ)) (e z)
      ((Category.id_comp x0).trans (he z).symm) := by
    funext z
    rw [lftJ, ptSecT, Over.lift_left]
    rfl
  rw [hl]
  exact GlobalTheory.AnVal.isHolFam_pullback_lift X (Sp ℂ) G.left x0 G.hom g (fun _ => 𝟙 (Sp ℂ)) e x0 (fun _ => Category.id_comp x0) he
    (isHolFam_const _) hol

end Fam

def onePr (g : ℕ) : (Fin (1 * g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (1 * g) => ℂ)
    (finProdFinEquiv ((0 : Fin 1), j))

theorem onePr_apply {g : ℕ} (v : Fin (1 * g) → ℂ) (j : Fin g) : onePr g v j = v (finProdFinEquiv ((0 : Fin 1), j)) :=
  rfl

theorem anLin_onePr {g : ℕ} (p : Fin 1 × Fin g) :
    anLin (onePr g) p = MvPolynomial.X ((0 : Fin 1), finProdFinEquiv ((0 : Fin 1), p.2)) := by
  rw [anLin, Finset.sum_eq_single (finProdFinEquiv ((0 : Fin 1), p.2))]
  · rw [onePr_apply, Pi.single_eq_same, map_one]
    exact _root_.one_mul _
  · intro k _ hk
    rw [onePr_apply, Pi.single_eq_of_ne (Ne.symm hk), map_zero, zero_mul]
  · simp

theorem jetN_one {g : ℕ} (m : ℕ) {f : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) :
    jetN (n := 1) m (fun w => f (w 0)) = jetOf m f := by
  have h1 : (fun v => (fun w : Fin 1 → Fin g → ℂ => f (w 0)) (colsOf 1 g v)) = f ∘ onePr g := rfl
  rw [jetN, h1, jetOf_comp_anLin m hf, renN,
    anJetMap_comp _ _ _ _ (fun p => MvPolynomial.X p) (fun _ => X_mem_orig _) (fun p => by
      obtain ⟨a, j⟩ := p
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      simp only [anLin_onePr, MvPolynomial.aeval_X, Equiv.symm_apply_apply])]
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (jetOf m f)
  rw [← hp]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval MvPolynomial.X p) = _
  rw [MvPolynomial.aeval_X_left_apply]

theorem isValueAt_jetPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (m k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.Rd k F θ → Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → ∃ F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y g m 1)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y g m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧ IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (Φ.jx m) τ (toΓ _ (jetOf m θ)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ m k F θ τ hF hτ
  have he : ∀ z, (Φ.e z).left ≫ Xo.univ.t.G.hom = y.x := fun z => Over.w (Φ.e z)
  refine ⟨pullSecLP _ _ _ _ (whiskerRight_snd _ _) F, isPullSec_pullSecLP _ _ _ _ _ F, ?_⟩
  refine isValueAt_jet Xo.univ.t.PP.L (fun z => (Φ.e z).left) Φ.hol he (isHolFam_lftJ _ he Φ.hol) m k F _
    (isPullSec_pullSecLP _ _ _ _ _ F) θ Φ.fr Φ.fr_hol Φ.fr_ne hF τ fun j h => ?_
  have hmem : jetPt (fun z => (Φ.e z).left) Φ.hol m (IsLocalRing.closedPoint _) ∈ Xo.univ.t.PP.L.U (j 0) :=
    Set.mem_iInter.1 (h trivial) 0
  rw [jetPt_closedPoint] at hmem
  have hA : ContDiffAt ℂ ω (Φ.fr (j 0)) 0 :=
    (ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j 0)} (Φ.fr (j 0))
      (Φ.hol (Xo.univ.t.PP.L.U (j 0)) 0).1 (Φ.fr_hol (j 0)) 0 (top_le_of_mem hmem)).contDiffAt
  refine (hτ.2 j h).trans (congrArg _ ?_)
  rw [← jetN_one m (hA.pow k)]
  congr 1
  funext w
  simp

end GlobalTheory.JetVal
