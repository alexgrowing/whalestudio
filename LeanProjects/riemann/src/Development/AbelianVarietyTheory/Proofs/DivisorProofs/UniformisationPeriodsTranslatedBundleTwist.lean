import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateIntegralThetaExpansionByTwoTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiTwistedEqPsiMulCharacterOfPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

theorem GlobalTheory.MumCmp.psi_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  intro R _ _ _ hB D A G _ _ hsa U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw h0
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hS : SecBaseChangeSt := GlobalTheory.allSixLaws.1.secBaseChange
  obtain ⟨σ, f, hσ0, hE⟩ : ∃ (σ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α),
      (¬ ∀ j, σ.f j = 0) ∧ ∀ e : ℕ, U.ExpandsAt e 1 σ f := by
    obtain ⟨b, -, hb⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hS R _ D A G U.toUnifPre 1 le_rfl
    let i₀ : Fin (1 ^ A.g) := ⟨0, by rw [one_pow]; exact Nat.one_pos⟩
    have hs : ¬ ∀ j, (b i₀).f j = 0 := fun h0 => by
      obtain ⟨c, -, hc⟩ := hb SecOps.secZero
      have e₁ := hc 0 (fun j => by simp [scal]; rfl)
      have e₂ := hc 1 (fun j => by
        refine (Finset.sum_eq_zero fun i _ => ?_).symm
        obtain rfl : i = i₀ := Fin.ext (by have := i.2; simp only [one_pow] at this; show i.1 = 0; omega)
        rw [h0 j, MulZeroClass.mul_zero])
      exact one_ne_zero (congrFun (e₂.trans e₁.symm) i₀)
    obtain ⟨E, ⟨r, hr, σ, f, hσ, -, hE⟩, -⟩ := (U.expand 1 le_rfl).1 (b i₀)
    refine ⟨σ, f, fun hz0 => hs ?_, hE⟩
    refine GlobalTheory.ThetaScalar.eq_zero_of_sval U.LG.isLB _ fun y J hJ => ?_
    have e₁ := GlobalTheory.PullIntegral.sval_of_secScal hσ (𝟙 _) y hJ
    rw [GlobalTheory.ThetaScalar.sval_eq_zero σ hz0 _ y hJ] at e₁
    have e₃ : gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK R) ≫ jK R) r) =
        cst (pullback.snd G.hom (jK R) ≫ jK R) y r :=
      (gs_pull (𝟙 _) (pullback.snd G.hom (jK R) ≫ jK R) y ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
    rw [e₃] at e₁
    exact (GlobalTheory.IntegralExpansionLocal.isUnit_cst_of_ne_zero _ y hr).mul_right_eq_zero.1 e₁.symm
  obtain ⟨σ₂, f₂, ν, hν, hE₂, h0σ, hrel⟩ :=
    GlobalTheory.T.translate_integral_thetaExpansion_by_twoTorsion R hB D A G hsa U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw σ f hE
  have hne : ¬ ∀ mu j, (f₂ mu).f j = 0 := fun h0' => hσ0 (h0σ (by
    have H := (GlobalTheory.comb_eq_zero_iff_expansion_comb_eq_zero R _ hR D₂ A₂ G U₂.toUnifPre 1 1 ![1] ![σ₂] ![f₂]
      (fun i => by fin_cases i; exact hE₂)).2 hsa.geomConnected (fun α j => by
        simpa [scal] using h0' α j)
    exact fun j => by simpa [scal] using H j))
  exact GlobalTheory.T.psi_twisted_eq_psi_mul_character_of_point R hB D D₂ g β hβm xe hc w hw h0 f f₂ ν hν
    (GlobalTheory.PsiCompare.levelOneEq_of_expandsAt hG hR U.toUnifPre (U.expand 1 le_rfl) σ f hE)
    (GlobalTheory.PsiCompare.levelOneEq_of_expandsAt hG hR U₂.toUnifPre (U₂.expand 1 le_rfl) σ₂ f₂ hE₂) hne hrel
