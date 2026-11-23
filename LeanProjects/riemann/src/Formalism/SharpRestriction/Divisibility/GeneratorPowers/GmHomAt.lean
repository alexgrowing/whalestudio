import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartActionPoint

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

abbrev σL (C : ChartAt Xo c y) (m : ℕ) : Fin 2 × Fin C.d → MvPolynomial (Fin 1 × Fin C.d) S :=
  fun p => (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn C.d m ![0] (C.B.A.act H.w0 j)] :
    Fin 2 → Fin C.d → MvPolynomial (Fin 1 × Fin C.d) S) p.1 p.2

theorem cc_σL (C : ChartAt Xo c y) (m : ℕ) (p : Fin 2 × Fin C.d) : MvPolynomial.constantCoeff (σL C m p) = 0 := by
  rcases p with ⟨i, j⟩
  fin_cases i <;> simp [σL, psIn, MvPolynomial.constantCoeff_rename, Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.cc_psTrunc', C.B.A.const]

theorem ptm_one_φa (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (m : ℕ) (k : 𝓞 E) :
    homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c k)) ≫ homAt y.x (jφ φ m) = ptm C ![φa c φ k] m := by
  rw [jφ_eq, sA_ptm C ![φ] (fun i j => by rw [Fin.fin_one_eq_zero i]; exact hφ j) m k]
  refine congrArg (fun P => ptm C P m) (funext fun i => funext fun j => ?_)
  rw [Fin.fin_one_eq_zero i]
  rfl

theorem ptm_σL (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)) (m : ℕ) (k : 𝓞 E) :
    ptm C ![φa c φ k] m ≫ homAt y.x (jetSubstP m (σL C m)) = ptm C ![φa c φ k, φa c φ (H.w0 * k)] m := by
  have hP0 : ∀ j, MvPowerSeries.constantCoeff (φa c φ k j) = 0 := const_φa c φ hφ k
  have hP : ∀ i j, MvPowerSeries.constantCoeff ((![φa c φ k] : Fin 1 → _) i j) = 0 := by
    intro i j
    rw [Fin.fin_one_eq_zero i]
    exact hP0 j
  rw [ptm_subst C _ hP m _ (cc_σL C m)]
  set Q : Fin 1 × Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
    fun p => (![φa c φ k] : Fin 1 → _) p.1 p.2 with hQdef
  have hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0 := fun p => hP p.1 p.2
  have hQe : Q = fun p => φa c φ k p.2 := by
    funext p
    obtain ⟨p1, p2⟩ := p
    rw [hQdef, Fin.fin_one_eq_zero p1]
    rfl
  refine ptm_congr C (fun i j => const_substPS Q hQ _ ?_) ?_ m ?_
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    exact cc_σL C m (i, j)
  · rw [Fin.forall_fin_two]
    exact ⟨fun j => hP0 j, fun j => const_φa c φ hφ _ j⟩
  · rw [Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · simp only [σL, Matrix.cons_val_zero]
      rw [MvPolynomial.coe_X, MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ), hQe]
    · simp only [σL, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [power_series_in_fin_one, psJet_subst_trunc m Q hQ, hQe, act_φa c hφ hact]

theorem gm_top {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (v : Γ(Y, ⊤)ˣ) :
    gm r z ⊤ v = gm (𝟙 Z) z ⊤ (Units.map r.appTop.hom.toMonoidHom v) := by
  first
  | rfl
  | (simp only [gm, pullU]; rfl)
  | (ext; simp [gm, pullU]; rfl)

theorem gm_homAt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B)
    (z : (overAt y.x B).left) (w : Aˣ) :
    gm (homAt y.x f).left z ⊤ (unitΓ w) = gm (𝟙 _) z ⊤ (unitΓ (Units.map f.toMonoidHom w)) := by
  rw [gm_top, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB.unitΓ_homAt]

theorem val_eG (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jO y (dL Dw) m 1).left) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (ExpGA.eG C φ τ u m) r z J = gm r z ⊤ (unitΓ (u m)) * val (τ m) (r ≫ (homAt y.x (jφ φ m)).left) z J := by
  show val (scaleGen (fun _ : Fin 1 => (homAt y.x (jφ φ m)).left ≫ (C.x m).left) (fun _ => (1 : ℤ)) (unitΓ (u m))
    (LB.pullGen Xo.univ.t.PP.L _ _ (τ m) (homAt y.x (jφ φ m)).left)) r z J = _
  rw [ExpGD.val_scale' _ _ _ _ _ z J hJ, val_pull hJ]

theorem val_eAt (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j))
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (m : ℕ) (k : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
    (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (eAt y (xExp y C φ) (ExpGA.eG C φ τ u) m k) (𝟙 _) z J =
      gm (𝟙 _) z ⊤ (unitΓ (Units.map (jetSubstP m (actP (Dw := Dw) (S := S) c k)).toMonoidHom (u m))) *
        (val C.wP ((ptm C ![φa c φ k] m).left ≫ (C.x m).left) z J *
          val (C.e m) (ptm C ![φa c φ k, φa c φ (H.w0 * k)] m).left z J) := by
  have hm1 : (𝟙 _ ≫ (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c k))).left) ≫ (homAt y.x (jφ φ m)).left =
      (ptm C ![φa c φ k] m).left := by
    rw [Category.id_comp, ← Over.comp_left, ptm_one_φa C φ hφ m k]
  have hm2 : (ptm C ![φa c φ k] m).left ≫ (homAt y.x (jetSubstP m (σL C m))).left =
      (ptm C ![φa c φ k, φa c φ (H.w0 * k)] m).left := by
    rw [← Over.comp_left, ptm_σL C φ hφ hact m k]
  unfold eAt
  rw [val_pull hJ, val_eG C φ τ u m _ z J hJ, val_corr hJ (hτc m), hm1, Category.id_comp, gm_homAt]
  unfold eL
  rw [val_mul hJ, val_pull hJ,
    show val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn C.d m ![0] (C.B.A.act H.w0 j)])
        (ptm C ![φa c φ k] m).left z J =
      val (C.e m) ((ptm C ![φa c φ k] m).left ≫ (homAt y.x (jetSubstP m (σL C m))).left) z J from val_pull hJ _ _ _,
    hm2]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
