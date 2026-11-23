import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhOneValSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

abbrev P3 (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (u0 u1 u2 : 𝓞 E) :
    Fin 3 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  fun k => φa c φ (![u0, u1, u2] k)

private theorem subst_rename_lemma {σ τ υ R : Type} [CommRing R] [Finite σ] [Finite τ]
    (a : σ → MvPowerSeries υ R) (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ρ : τ → σ)
    (q : MvPolynomial τ R) :
    MvPowerSeries.subst a ((MvPolynomial.rename ρ q : MvPolynomial σ R) : MvPowerSeries σ R) =
      MvPowerSeries.subst (fun t => a (ρ t)) (q : MvPowerSeries τ R) := by
  have h1 : MvPowerSeries.HasSubst a := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  have h2 : MvPowerSeries.HasSubst (fun t => a (ρ t)) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => ha (ρ t))
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [(fun t => ha (ρ t)) s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [(fun t => ha (ρ t)) s]; exact IsNilpotent.zero)
  rw [← MvPowerSeries.coe_substAlgHom h1, ← MvPowerSeries.coe_substAlgHom h2]
  erw [MvPowerSeries.substAlgHom_coe, MvPowerSeries.substAlgHom_coe, MvPolynomial.aeval_rename]
  rfl

theorem subst_psIn {d n n' : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (r : Fin n → Fin n')
    (Q : Fin n' × Fin d → MvPowerSeries κ S) (hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0)
    (f : MvPowerSeries (Fin n × Fin d) S) :
    psJet m (MvPowerSeries.subst Q ((psIn d m r f : MvPolynomial _ S) : MvPowerSeries _ S)) =
      psJet m (MvPowerSeries.subst (fun p : Fin n × Fin d => Q (r p.1, p.2)) f) := by
  simp only [psIn]
  rw [subst_rename_lemma Q hQ, ExpGF.psJet_subst_trunc m _ (fun _ => hQ _) f]

abbrev σ2 (C : ChartAt Xo c y) (a b : Fin 3) : Fin 2 × Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S :=
  fun p => (![fun j => MvPolynomial.X (a, j), fun j => MvPolynomial.X (b, j)] :
    Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2

abbrev σS (C : ChartAt Xo c y) (m : ℕ) : Fin 2 × Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S :=
  fun p => (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn C.d m ![1, 2] (C.B.G.F j)] :
    Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2

set_option maxHeartbeats 1000000 in

theorem ptm_pair (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (m : ℕ) (u0 u1 u2 : 𝓞 E) (a b : Fin 3) :
    ptm C (P3 C φ u0 u1 u2) m ≫ homAt y.x (jetSubstP m (σ2 C a b)) =
      ptm C ![φa c φ (![u0, u1, u2] a), φa c φ (![u0, u1, u2] b)] m := by
  have hP : ∀ i j, MvPowerSeries.constantCoeff (P3 C φ u0 u1 u2 i j) = 0 :=
    fun i j => ExpGG.const_φa c φ hφ _ j
  have hσ : ∀ k, MvPolynomial.constantCoeff (σ2 C a b k) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [σ2]
  rw [ptm_subst C _ hP m (σ2 C a b) hσ]
  have hs : MvPowerSeries.HasSubst (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hP p.1 p.2]; exact IsNilpotent.zero)
  congr 1
  funext i j
  fin_cases i <;> simp [σ2, MvPolynomial.coe_X, MvPowerSeries.subst_X hs]

set_option maxHeartbeats 1000000 in

theorem ptm_sum (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hexp : IsExpOf C.B.G.F C.uvec φ) (m : ℕ) (u0 u1 u2 : 𝓞 E) :
    ptm C (P3 C φ u0 u1 u2) m ≫ homAt y.x (jetSubstP m (σS C m)) =
      ptm C ![φa c φ u0, φa c φ (u1 + u2)] m := by
  have hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0 := hexp.const
  have hP : ∀ i j, MvPowerSeries.constantCoeff (P3 C φ u0 u1 u2 i j) = 0 := fun i j => const_φa c φ hφ _ j
  have hσ : ∀ p : Fin 2 × Fin C.d, MvPolynomial.constantCoeff (σS C m p) = 0 := by
    rintro ⟨i, j⟩
    rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h | h <;> subst h
    · simp
    · show MvPolynomial.constantCoeff (psIn C.d m ![1, 2] (C.B.G.F j)) = 0
      rw [psIn, MvPolynomial.constantCoeff_rename, ExpGB.cc_psTrunc', C.B.G.const]
  rw [ptm_subst C (P3 C φ u0 u1 u2) hP m (σS C m) hσ]
  refine ptm_congr C (P := fun i j => MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
      ((σS C m (i, j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S))
    (P' := ![φa c φ u0, φa c φ (u1 + u2)])
    (fun i j => const_substPS (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
      (fun p : Fin 3 × Fin C.d => hP p.1 p.2) _ ?_)
    ?_ m ?_
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    exact hσ (i, j)
  · rw [Fin.forall_fin_two]
    exact ⟨fun j => const_φa c φ hφ _ j, fun j => const_φa c φ hφ _ j⟩
  · rw [Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
          ((MvPolynomial.X ((0 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries _ S)) = _
      rw [MvPolynomial.coe_X, MvPowerSeries.subst_X (a := fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
        (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p : Fin 3 × Fin C.d => hP p.1 p.2))]
      rfl
    · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
          ((psIn C.d m (![1, 2] : Fin 2 → Fin 3) (C.B.G.F j) : MvPolynomial (Fin 3 × Fin C.d) S) :
            MvPowerSeries (Fin 3 × Fin C.d) S)) = _
      rw [subst_psIn m ![1, 2] (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)
        (fun p : Fin 3 × Fin C.d => hP p.1 p.2) (C.B.G.F j)]
      have hfun : (fun p : Fin 2 × Fin C.d => (fun q : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 q.1 q.2)
          ((![1, 2] : Fin 2 → Fin 3) p.1, p.2)) = fun p : Fin 2 × Fin C.d => φa c φ (![u1, u2] p.1) p.2 := by
        funext p
        obtain ⟨i, k⟩ := p
        rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h | h <;> subst h <;> rfl
      refine (congrArg (fun Q => psJet m (MvPowerSeries.subst Q (C.B.G.F j))) hfun).trans ?_
      rw [law_φa c hexp u1 u2 j]
      rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem phTwoVal_holds : PhTwoValSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C φ hexp hx m u0 u1 u2 z J hJ
  have hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0 := hexp.const
  obtain ⟨u, hu, hc⟩ := C.frame.ph2 m
  have hP : ∀ i j, MvPowerSeries.constantCoeff (P3 C φ u0 u1 u2 i j) = 0 := fun i j => const_φa c φ hφ _ j
  have hPe : (P3 C φ u0 u1 u2) = ![φa c φ u0, φa c φ u1, φa c φ u2] := by
    funext k
    fin_cases k <;> rfl
  refine ⟨Units.map (jetSubstPS (m := m) (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)).toMonoidHom u,
    ?_, ?_⟩
  · show jetSubstPS (m := m) (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2) (u : Jet S (Fin 3 × Fin C.d) m) = _
    rw [hu, jetSubstPS_psJet m (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2) (fun p => hP p.1 p.2), ← hPe]
    rfl
  · have h1 := val_corr hJ (DVR.corr_pullGen hc (ptm C (P3 C φ u0 u1 u2) m).left) (𝟙 _)
    have h2 := (val_pull hJ _ _ _).symm.trans (h1.trans (val_pull hJ _ _ _))
    have h3 := (val_pull hJ _ _ _).symm.trans h2
    simp only [Category.id_comp] at h3
    have hmor : (ptm C (P3 C φ u0 u1 u2) m).left ≫
        (lift (jpt y C.d C.x m (1 : Fin 3)) (lift (jpt y C.d C.x m (2 : Fin 3)) (jpt y C.d C.x m (0 : Fin 3)))).left =
        (xExp y C φ m).left ≫
          (lift (Xo.univ.t.act.act u1) (lift (Xo.univ.t.act.act u2) (Xo.univ.t.act.act u0))).left := by
      rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, comp_lift, comp_lift,
        ptm_jpt C φ hφ hx m ![u0, u1, u2] 1, ptm_jpt C φ hφ hx m ![u0, u1, u2] 2,
        ptm_jpt C φ hφ hx m ![u0, u1, u2] 0]
      rfl
    rw [hmor, ExpGD.val_scale' _ _ _ _ _ z J hJ] at h3
    rw [show val (ExpGC.cubAt (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2) (Xo.univ.t.act.act u0))
        (xExp y C φ m).left z J = _ from val_pull hJ _ _ _, h3]
    have hg : gm (ptm C (P3 C φ u0 u1 u2) m).left z ⊤ (unitΓ u) =
        gm (𝟙 _) z ⊤ (unitΓ (Units.map (jetSubstPS (m := m)
          (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)).toMonoidHom u)) := gm_homAt _ z u
    rw [hg, val_mul hJ, val_mul hJ, val_inv, val_inv]
    rw [show val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 3), j),
          fun j => psIn C.d m ![1, 2] (C.B.G.F j)]) (ptm C (P3 C φ u0 u1 u2) m).left z J =
        val (C.e m) ((ptm C (P3 C φ u0 u1 u2) m).left ≫ (homAt y.x (jetSubstP m fun p : Fin 2 × Fin C.d =>
          (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn C.d m ![1, 2] (C.B.G.F j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2)).left) z J from val_pull hJ _ _ _,
      show val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 3), j),
          fun j => MvPolynomial.X ((1 : Fin 3), j)]) (ptm C (P3 C φ u0 u1 u2) m).left z J =
        val (C.e m) ((ptm C (P3 C φ u0 u1 u2) m).left ≫ (homAt y.x (jetSubstP m fun p : Fin 2 × Fin C.d =>
          (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2)).left) z J from val_pull hJ _ _ _,
      show val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 3), j),
          fun j => MvPolynomial.X ((2 : Fin 3), j)]) (ptm C (P3 C φ u0 u1 u2) m).left z J =
        val (C.e m) ((ptm C (P3 C φ u0 u1 u2) m).left ≫ (homAt y.x (jetSubstP m fun p : Fin 2 × Fin C.d =>
          (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2)).left) z J from val_pull hJ _ _ _]
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ptm_sum C φ hexp m u0 u1 u2,
      ptm_pair C φ hφ m u0 u1 u2 0 1, ptm_pair C φ hφ m u0 u1 u2 0 2]
    rw [mul_assoc (val (C.e m) (ptm C ![φa c φ u0, φa c φ (u1 + u2)] m).left z J)]
    rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
