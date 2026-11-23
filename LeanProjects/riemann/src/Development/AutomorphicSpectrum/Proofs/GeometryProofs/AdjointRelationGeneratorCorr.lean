import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdSy
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Alg

variable {S : Type} [CommRing S] {d : ℕ}

theorem aeval_psIn_zero (m : ℕ) (i : Fin 2) (ψ : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S)
    (h : ∀ l, ψ (i, l) = 0) (f : PS S 1 d) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPolynomial.aeval ψ (psIn d m ![i] f) = 0 := by
  have e : (ψ ∘ fun p : Fin 1 × Fin d => ((![i] : Fin 1 → Fin 2) p.1, p.2)) = 0 := by
    funext p
    obtain ⟨k, l⟩ := p
    simpa using h l
  rw [psIn, MvPolynomial.aeval_rename, e, MvPolynomial.aeval_zero, FBIdPh.cc_psTrunc, hf, map_zero]

theorem aeval_psIn_X (m : ℕ) (i : Fin 2) (ψ : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S)
    (h : ∀ l, ψ (i, l) = MvPolynomial.X ((0 : Fin 1), l)) (f : PS S 1 d) :
    MvPolynomial.aeval ψ (psIn d m ![i] f) = psTrunc m f := by
  have e : (ψ ∘ fun p : Fin 1 × Fin d => ((![i] : Fin 1 → Fin 2) p.1, p.2)) = MvPolynomial.X := by
    funext p
    obtain ⟨k, l⟩ := p
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    simpa using h l
  rw [psIn, MvPolynomial.aeval_rename, e, MvPolynomial.aeval_X_left_apply]

abbrev axP (d : ℕ) (S : Type) [CommRing S] (b : Bool) : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S :=
  fun p => (if b then ![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)]
    else ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

theorem constantCoeff₂ (b : Bool) (p : Fin 2 × Fin d) : MvPolynomial.constantCoeff (axP d S b p) = 0 := by
  obtain ⟨k, j⟩ := p
  cases b <;> fin_cases k <;> simp [axP]

abbrev fstP (f : Fin d → PS S 1 d) (m : ℕ) : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S :=
  fun p => (![fun j => psIn d m ![0] (f j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
    Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2

abbrev sndP (f : Fin d → PS S 1 d) (m : ℕ) : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S :=
  fun p => (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (f j)] :
    Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2

abbrev actJ (f : Fin d → PS S 1 d) (m : ℕ) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (f p.2)

theorem fstP_cc (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ)
    (p : Fin 2 × Fin d) : MvPolynomial.constantCoeff (fstP f m p) = 0 := by
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simpa [fstP] using (FBIdPh.cc_psIn d m ![0] (f j)).trans (hf j)
  · simp [fstP]

theorem sndP_cc (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ)
    (p : Fin 2 × Fin d) : MvPolynomial.constantCoeff (sndP f m p) = 0 := by
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simp [sndP]
  · simpa [sndP] using (FBIdPh.cc_psIn d m ![1] (f j)).trans (hf j)

theorem trunc_cc (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ)
    (p : Fin 1 × Fin d) : MvPolynomial.constantCoeff (psTrunc m (f p.2)) = 0 :=
  (FBIdPh.cc_psTrunc m _).trans (hf _)

theorem ax_fst_true (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m true).comp (jetSubstP m (fstP f m)) = axJ d m true := by
  refine (FBIdPh.jetSubstP_comp m (fstP f m) (axP d S true) (fstP_cc f hf m) (constantCoeff₂ true)).trans ?_
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · exact aeval_psIn_zero m 0 _ (fun _ => rfl) _ (hf j)
  · simp [fstP, axP]

theorem ax_snd_true (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m true).comp (jetSubstP m (sndP f m)) = (actJ f m).comp (axJ d m true) := by
  refine (FBIdPh.jetSubstP_comp m (sndP f m) (axP d S true) (sndP_cc f hf m) (constantCoeff₂ true)).trans ?_
  refine Eq.trans ?_ (FBIdPh.jetSubstP_comp m (axP d S true) _ (constantCoeff₂ true) (trunc_cc f hf m)).symm
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simp [sndP, axP]
  · refine (aeval_psIn_X m 1 _ (fun _ => rfl) _).trans ?_
    simp [axP]

theorem ax_fst_false (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m false).comp (jetSubstP m (fstP f m)) = (actJ f m).comp (axJ d m false) := by
  refine (FBIdPh.jetSubstP_comp m (fstP f m) (axP d S false) (fstP_cc f hf m) (constantCoeff₂ false)).trans ?_
  refine Eq.trans ?_ (FBIdPh.jetSubstP_comp m (axP d S false) _ (constantCoeff₂ false) (trunc_cc f hf m)).symm
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · refine (aeval_psIn_X m 0 _ (fun _ => rfl) _).trans ?_
    simp [axP]
  · simp [fstP, axP]

theorem ax_snd_false (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m false).comp (jetSubstP m (sndP f m)) = axJ d m false := by
  refine (FBIdPh.jetSubstP_comp m (sndP f m) (axP d S false) (sndP_cc f hf m) (constantCoeff₂ false)).trans ?_
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simp [sndP, axP]
  · exact aeval_psIn_zero m 1 _ (fun _ => rfl) _ (hf j)

theorem ax_copy_zero (m : ℕ) (b : Bool) (i : Fin 2) (hi : (i = 1) ≠ b) :
    (axJ (S := S) d m b).comp (jetCopy d m i) =
      (Algebra.ofId S (Jet S (Fin 1 × Fin d) m)).comp jetAug := by
  refine jet_hom_ext fun p => ?_
  obtain ⟨k, j⟩ := p
  have h0 : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X (k, j))) = 0 := by
    simp [jetAug, liftJet]
  rw [AlgHom.comp_apply, AlgHom.comp_apply, h0, map_zero, jetCopy, jetMap_mk, MvPolynomial.aeval_X, axJ_X]
  simp [axV, hi]

theorem ax_copy_id (m : ℕ) (b : Bool) (i : Fin 2) (hi : (i = 1) = b) :
    (axJ (S := S) d m b).comp (jetCopy d m i) = AlgHom.id S _ := by
  refine jet_hom_ext fun p => ?_
  obtain ⟨k, j⟩ := p
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  rw [AlgHom.comp_apply, jetCopy, jetMap_mk, MvPolynomial.aeval_X, axJ_X, AlgHom.id_apply]
  simp [axV, hi]

end Alg

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem pt_killed (hz : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) (m : ℕ) (b : Bool)
    (i : Fin 2) (hi : (i = 1) ≠ b) : homAt x0 (axJ (S := S) d m b) ≫ jptG t x0 d x m i = 1 := by
  rw [jptG, ← Category.assoc, homAt_comp, ax_copy_zero m b i hi, ← homAt_comp, Category.assoc, hz m]
  exact MonObj.comp_one _

theorem pt_kept (m : ℕ) (b : Bool) (i : Fin 2) (hi : (i = 1) = b) :
    homAt x0 (axJ (S := S) d m b) ≫ jptG t x0 d x m i = x m := by
  rw [jptG, ← Category.assoc, homAt_comp, ax_copy_id m b i hi, homAt_id, Category.id_comp]

theorem val_axis (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) (hax : FrAxes t x0 d x e) (a : 𝓞 E) (wL : FrGauge.AdTy t a)
    (hrel : FrGauge.AdRel t x0 d x act ad e a wL) (m : ℕ) (b : Bool)
    (hb : ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) (ad a) = 1)
    (r₁ r₂ : (jOG x0 d m 1).left ⟶ (jOG x0 d m 1).left)
    (h₁ : (homAt x0 (axJ (S := S) d m b)).left ≫ (homAt x0 (jetSubstP m (fstP (act a) m))).left =
      r₁ ≫ (homAt x0 (axJ (S := S) d m b)).left)
    (h₂ : (homAt x0 (axJ (S := S) d m b)).left ≫ (homAt x0 (jetSubstP m (sndP (act (H.bar a)) m))).left =
      r₂ ≫ (homAt x0 (axJ (S := S) d m b)).left)
    (y : (jOG x0 d m 1).left) (J : ((jOG x0 d m 1).left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L y J) :
    val wL ((homAt x0 (axJ (S := S) d m b)).left ≫
      (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) y J = 1 := by
  obtain ⟨u, hu, hc⟩ := hrel m
  have hA : LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (axJ (S := S) d m b)).left) (LB.oneGen t.PP.L) := by
    cases b
    · exact (hax m).2
    · exact (hax m).1
  have hv : ∀ r : (jOG x0 d m 1).left ⟶ (jOG x0 d m 1).left,
      val (e m) (r ≫ (homAt x0 (axJ (S := S) d m b)).left) y J = 1 := fun r =>
    (val_pull hJ _ _ _).symm.trans ((val_corr hJ hA r).trans (val_one _))
  have E := val_corr hJ hc (homAt x0 (axJ (S := S) d m b)).left
  rw [val_mul hJ, val_pull hJ, GermB.val_scale t _ _ _ _ _ y J hJ] at E
  have p₁ : val (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (homAt x0 (axJ (S := S) d m b)).left y J = 1 :=
    (val_pull hJ _ _ _).trans ((congrArg (fun r => val (e m) r y J) h₁).trans (hv r₁))
  have p₂ : val (peG t x0 d x e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])
      (homAt x0 (axJ (S := S) d m b)).left y J = 1 :=
    (val_pull hJ _ _ _).trans ((congrArg (fun r => val (e m) r y J) h₂).trans (hv r₂))
  have hU : Units.map ((axJ (S := S) d m b : _ →ₐ[S] _) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 1 × Fin d) m) u = 1 :=
    Units.ext (by
      rw [Units.coe_map, hu]
      exact (psJet_ev_ax d m (ad a) b).symm.trans ((congrArg (psJet m) hb).trans (psJet_one m)))
  have p₃ : gm (homAt x0 (axJ (S := S) d m b)).left y ⊤ (unitΓ u) = 1 := by
    rw [FrRatio.gm_map, hU, unitΓ_one, map_one]
  rw [p₁, p₂, p₃, _root_.mul_one, _root_.mul_one] at E
  exact E

theorem lift_true (hz : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) (m : ℕ) :
    (homAt x0 (axJ (S := S) d m true)).left ≫
        (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left =
      (lift (1 : jOG x0 d m 1 ⟶ t.G) (x m)).left := by
  rw [← Over.comp_left, comp_lift, pt_killed t x0 d x hz m true 0 (by simp),
    pt_kept t x0 d x m true 1 (by simp)]

theorem lift_false (hz : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) (m : ℕ) :
    (homAt x0 (axJ (S := S) d m false)).left ≫
        (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left =
      (lift (x m) (1 : jOG x0 d m 1 ⟶ t.G)).left := by
  rw [← Over.comp_left, comp_lift, pt_kept t x0 d x m false 0 (by simp),
    pt_killed t x0 d x hz m false 1 (by simp)]

end Frame

theorem adAxes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x : Sp S ⟶ X) (d : ℕ)
    (g : GermAt t x d) (a : 𝓞 E) (wL : FrGauge.AdTy t a), wL.IsGen →
    FrGauge.AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → ∀ m,
    LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (1 : jOG x d m 1 ⟶ t.G) (g.x m)).left)
      (LB.oneGen t.PP.L) ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (g.x m) (1 : jOG x d m 1 ⟶ t.G)).left)
      (LB.oneGen t.PP.L) := by
  intro E _ _ _ H _ _ X t S _ x d g a wL _ hrel m
  have hL := t.PP.isLB
  have hc : ∀ c j, MvPowerSeries.constantCoeff (g.B.A.act c j) = 0 := g.B.A.const
  refine ⟨corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => ?_⟩
  · rw [val_pull hJ, val_one, Category.id_comp, ← lift_true t x d g.x g.chart.zero m]
    refine val_axis t x d g.x g.B.A.act g.B.ad g.e g.axes a wL hrel m true (g.B.adjoint_zero_fst a) (𝟙 _)
      (homAt x (actJ (g.B.A.act (H.bar a)) m)).left ?_ ?_ y J hJ
    · rw [← Over.comp_left, homAt_comp, ax_fst_true _ (hc a) m, Category.id_comp]
    · rw [← Over.comp_left, homAt_comp, ax_snd_true _ (hc _) m, ← homAt_comp, Over.comp_left]
  · rw [val_pull hJ, val_one, Category.id_comp, ← lift_false t x d g.x g.chart.zero m]
    refine val_axis t x d g.x g.B.A.act g.B.ad g.e g.axes a wL hrel m false (g.B.adjoint_zero_snd a)
      (homAt x (actJ (g.B.A.act a) m)).left (𝟙 _) ?_ ?_ y J hJ
    · rw [← Over.comp_left, homAt_comp, ax_fst_false _ (hc _) m, ← homAt_comp, Over.comp_left]
    · rw [← Over.comp_left, homAt_comp, ax_snd_false _ (hc _) m, Category.id_comp]

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis
