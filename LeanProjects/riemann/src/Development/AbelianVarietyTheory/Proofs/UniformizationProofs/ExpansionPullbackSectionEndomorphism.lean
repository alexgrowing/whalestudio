import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescentPowerIsoEndomorphismAbelianPartUniformizaStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionEndomorphismExpansionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistThroughIsoStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PullExp
open GlobalTheory.FieldBaseChange

section Uniq

theorem comb_eq_zero {R K F : Type} [CommRing R] [IsDomain R] [Field K] [Field F] [Algebra K F] [Algebra R K]
    [IsFractionRing R K] {V₀ V V' : Type} [AddCommGroup V₀] [Module R V₀] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module F V'] {J : Type} {P₀ : J → Type} [∀ j, AddCommGroup (P₀ j)] [∀ j, Module R (P₀ j)]
    {P P' : Type} [AddCommGroup P] [Module K P] [AddCommGroup P'] [Module F P'] (X : Submodule R (V₀ × ∀ j, P₀ j))
    (j : J) (ρ : V₀ →ₛₗ[algebraMap R K] V) (ρ' : P₀ j →ₛₗ[algebraMap R K] P)
    (a : V →ₛₗ[algebraMap K F] V') (ha : IsExtension a) (b : P →ₛₗ[algebraMap K F] P') (hb : IsExtension b)
    (hX : ∀ x ∈ X, ρ x.1 = 0 → x.2 j = 0) {T : Type} [Fintype T] (c : T → F) (x : T → V₀ × ∀ j, P₀ j)
    (hx : ∀ i, x i ∈ X) (h : ∑ i, c i • a (ρ (x i).1) = 0) : ∑ i, c i • b (ρ' ((x i).2 j)) = 0 := by
  refine hb.eq_of_coord fun ℓ Λ' hΛ' => ?_
  obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
  obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun i => ℓ (c i))
  choose m hm using hr
  have hr : algebraMap R K r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.coe_ne_zero r)
  have e₁ : ρ (∑ i, m i • x i).1 = algebraMap R K r • Λ (∑ i, c i • a (ρ (x i).1)) := by
    rw [map_sum, Finset.smul_sum, Prod.fst_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΛ, Prod.smul_fst, map_smulₛₗ, hm, smul_smul, Algebra.smul_def]
  have e₂ : ρ' ((∑ i, m i • x i).2 j) = algebraMap R K r • Λ' (∑ i, c i • b (ρ' ((x i).2 j))) := by
    rw [map_sum, Finset.smul_sum, Prod.snd_sum, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΛ', Prod.smul_snd, Pi.smul_apply, map_smulₛₗ, hm, smul_smul, Algebra.smul_def]
  rw [h, map_zero, smul_zero] at e₁
  rw [hX _ (Submodule.sum_mem _ fun i _ => X.smul_mem _ (hx i)) e₁, map_zero] at e₂
  rw [map_zero]
  exact (smul_eq_zero.1 e₂.symm).resolve_left hr

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem term_eq_zero [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (k : ℕ) (α : D.toPre.X)
    (x : IntSec U k × ∀ α, IntTerm D k α) (hx : x ∈ expansionPairs U k) (h : genericSec U k x.1 = 0) :
    x.2 α = 0 := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hd := GlobalTheory.ExtUnique.spec_fractionRing R (FractionRing R)
  have : IsSchemeTheoreticallyDominant (jK R) := hd.2
  have : QuasiCompact (jK R) := hd.1
  have h₀ : ∀ j, x.1.f j = 0 := fun j => by
    refine (pullback.fst G.hom (jK R)).app_injective _ (fn_ext fun y hy => ?_)
    have hy' : y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j :=
      mem_wchart.2 fun i => mem_wchart.1 hy i
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ ((congrArg _ (map_zero _)).trans (gs_zero' _ y _ hy)).symm)
    exact (gs_pullFn pullback.condition _ _ (𝟙 _) y hy').symm.trans
      ((congrArg (fun s : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))) =>
        gs (𝟙 _) y (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j) (LB.Sec.f s j)) h).trans (gs_zero' _ y _ hy'))
  have := D.toPre.P.isAb.smooth
  have : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  refine SecOver.ext _ _ ((sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
    (linComb_isLB _ D.toPre.P.isLB _ _) (x.2 α) fun e j => ?_)
  exact (GlobalTheory.ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1 (WeightPf.weightIndep R I D A G U e k x.1 x.2
    (fun j => (congrArg _ (h₀ j)).trans (map_zero _)) (hx e) α j)

theorem secLin_of_expandsG [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (v : GroupSec U F k) (s : Fam D.toPre F k) (hs : U.ExpandsG F k v s)
    (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k) (f : Fin n → ∀ α : D.toPre.X, IntTerm D k α)
    (hf : ∀ i e, U.ExpandsAt e k (σ i) (f i))
    (hv : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) v (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i))) (α : D.toPre.X) :
    GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k)
      (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i)) := by
  obtain ⟨n', c', x', hx', e₁, e₂⟩ := (expandsG_iff U F k v s).1 hs
  have d₁ := (secLin_iff U.LG.isLB v σ
    (UnifPre.gFK (G := G) F) c (fun i => extendSec U F k (genericSec U k (σ i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))).1 hv
  refine (secLin_iff D.toPre.P.isLB
    (famProj D.toPre F k α s) (fun i => f i α) (DegPre.prB D.toPre F).left c
    (fun i => termPull D.toPre (FractionRing R) F k α (genericTerm D k α (f i α))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (f i α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing R) F)))))))).2 ?_
  have : TopologicalSpace.NoetherianSpace ((Over.pullback (jK R)).obj G).left := noetherianSpace_generic U
  have H := comb_eq_zero (expansionPairs U k) α (genericSec U k) (genericTerm D k α) (extendSec U F k)
    (isExtension_pullOver (isPullback_groupBase F) U.LG.isLB _ _) (termPull D.toPre (FractionRing R) F k α)
    (isExtension_termPull D.toPre _ F k α) (term_eq_zero U hI k α) (Sum.elim c' fun i => -c i)
    (Sum.elim x' fun i => (σ i, f i)) (by rintro (i | i); exacts [hx' i, hf i]) (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib]
      rw [← e₁, ← d₁, add_neg_cancel])
  rw [Fintype.sum_sum_type] at H
  simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib] at H
  rw [← e₂ α] at H
  exact add_neg_eq_zero.1 H

end Uniq

section Norm
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem eSec_comp_one : eSec G ≫ (1 : G ⟶ G).left = eSec G :=
  congrArg (fun q => q.left) ((MonObj.comp_one (M := G) η[G]).trans (by
    show toUnit _ ≫ η[G] = η[G]
    rw [toUnit_unit, Category.id_comp]))

theorem exists_normalised (hL : L.IsLB) (a : G ⟶ G) [IsMonHom a] (k' k : ℤ)
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 _, a.left] ![k', -k])) (hβ : β.IsGen) :
    ∃ ν : LB.Gen (LB.LinComb L (K := Fin 3) ![𝟙 _, a.left, (1 : G ⟶ G).left] ![k', -k, k - k']), ν.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ ν (eSec G)) (LB.oneGen L) := by
  have e : (1 : G ⟶ G).left ≫ a.left = (1 : G ⟶ G).left :=
    congrArg (fun q : G ⟶ G => q.left) (MonObj.one_comp a)
  obtain ⟨ν, hν, hv⟩ := exists_gen hL (K' := Fin 3) (φ' := ![𝟙 _, a.left, (1 : G ⟶ G).left]) (ε' := ![k', -k, k - k'])
    (fun V _ h => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_three]
      show h (𝟙 _) ^ k' * h a.left ^ (-k) * (h ((1 : G ⟶ G).left ≫ 𝟙 _) ^ (-k') * h ((1 : G ⟶ G).left ≫ a.left) ^ (- -k)) =
        h (𝟙 _) ^ k' * h a.left ^ (-k) * h (1 : G ⟶ G).left ^ (k - k')
      rw [e, Category.comp_id, ← zpow_add, neg_neg, neg_add_eq_sub])
    (LB.mulGen L _ _ _ _ β (LB.invGen L _ _ (LB.pullGen L _ _ β (1 : G ⟶ G).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hβ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hβ _)))
  refine ⟨ν, hν, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.id_comp, eSec_comp_one,
    mul_inv_cancel]

end Norm

variable {R : Type} [CommRing R] [IsDomain R]

theorem normd_val_eq (hG : GlobalFnsSt) {D : DegPre R} {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb D.P.L φ ε)} (hu : Normd u) (hu' : Normd u') {Z : Scheme.{0}}
    (r : Z ⟶ D.P.A.left) (z : Z) (J) (hJ : Good D.P.L z J) : val u r z J = val u' r z J := by
  refine gen_unique D.P.isLB D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu.1 hu'.1
    (fun y J hJ => ?_) Z r z J hJ
  have a := val_corr hJ hu.2 (𝟙 _)
  have a' := val_corr hJ hu'.2 (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at a a'
  exact a.trans a'.symm

theorem sval_comb {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k n : ℕ} {c : Fin n → F}
    {χ : D.X} {s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε k))} {f : Fin n → D.SecB k χ}
    (h : GeneratorPullback.SecLin D.P.L (DegPre.famφ D F χ) (DegPre.famε k) s (D.famφB χ) (DegPre.famε k) f (DegPre.prB D F).left
      (fun i => scal (fst (TF (R := R) F) D.P.A).left (c i))) (b : TF (R := R) F ⟶ D.P.A) (z) {J}
    (hJ : Good D.P.L z J) :
    sval s (lift (𝟙 (TF (R := R) F)) b).left z J = ∑ i, cst F z (c i) * sval (f i) b.left z J := by
  refine (GlobalTheory.BoxExpansion.secLin_val h _ z hJ).trans (Finset.sum_congr rfl fun i _ => ?_)
  have e₁ : (lift (𝟙 (TF (R := R) F)) b).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    by
    rw [← Over.comp_left, lift_fst]; rfl
  have e₂ : (lift (𝟙 (TF (R := R) F)) b).left ≫ (DegPre.prB D F).left = b.left :=
    by
    rw [← Over.comp_left, lift_snd]
  rw [e₂]
  exact congrArg (· * _) ((gs_scal _ _ z (c i)).trans (congrArg (fun q => constVal q z (c i)) e₁))

theorem main : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ E hh k' k hk hk' ⟨β₀, hβ₀⟩
  have hGF := hL.1.globalFns
  have := hI.1
  have := hI.2.2.2
  have := E.homG
  obtain ⟨β, hβ, hβ'⟩ := exists_normalised U.LG.isLB E.aG k' k β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL R I hI D A G hG U E k' k β hβ hβ'
  refine ⟨⟨κ₀, hκ₀⟩, ?_⟩
  intro w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' s s' ⟨v, hv, n, c, σ, f, h₁, h₂, h₃⟩ ⟨v', hv', hs'⟩ htw κ hκ g g' hg w' w hw' hw₁ hww
  choose σ' f' p₁ p₂ p₃ p₄ using fun i => GlobalTheory.T.pullback_section_endomorphism_expansion R I D A G U.toUnifPre E hh k' k β hβ κ₀ hκ₀.1 hrel (σ i) (f i) (h₁ i)
  have tw := GlobalTheory.T.endU_twist_of_iso hGF R I D A G U.toUnifPre E F k' k β hβ hβ' w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' v v' hv hv' htw
  have H := secLin_of_expandsG U.toUnifPre (IsAdicComplete.le_jacobson_bot I) F k' v' s' hs' n c σ' f' p₁
    ((secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => by
      rw [tw y J hJ, GlobalTheory.BoxExpansion.secLin_val h₂ _ y hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e₁ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
        rw [← Over.comp_left, whiskerLeft_fst]
      have e₂ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫ UnifPre.gFK (G := G) F =
          UnifPre.gFK (G := G) F ≫ E.aG.left := by
        rw [UnifPre.gFK, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc,
          Category.assoc]
        exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)
      rw [p₂ i _ _ y J hJ, gs_scal, gs_scal, e₁, e₂, Category.id_comp, Category.id_comp, _root_.mul_assoc])
  refine ⟨fun χ => CoefBasic.coef_eq fun z J hJ => ?_, fun b hb => CoefBasic.coef_eq fun z J hJ => ?_⟩
  · have a := CoefBasic.isCoef_coef g' hw₁ χ s z J hJ
    have e : g.b.left ≫ D.toPre.P.A.hom = (TF (R := R) F).hom := Over.w g.b
    have e' : g'.b.left = g.b.left ≫ E.aB.left := congrArg (fun q => q.left) hg.1
    rw [sval_comb (h₃ χ) _ z hJ, hg.2 χ z J hJ, ← hww z J hJ, e', normd_val_eq hGF hκ hκ₀ _ z J hJ] at a
    rw [sval_comb (H (E.h χ)) _ z hJ]
    simp only [p₃ _ χ _ _ z J hJ, e, ← _root_.mul_assoc, ← Finset.sum_mul]
    have e₃ : (rigV D.toPre (TF (R := R) F).hom z J).val ^ k' =
        (rigV D.toPre (TF (R := R) F).hom z J).val ^ k * (rigV D.toPre (TF (R := R) F).hom z J ^ ((k' : ℤ) - k)).val := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast,
        ← zpow_add, add_sub_cancel]
    rw [e₃, ← _root_.mul_assoc, a]
    simp only [Units.val_mul]
    ring
  · rw [sval_comb (H b) _ z hJ, CoefBasic.cst_eq, map_zero, zero_mul, Finset.sum_eq_zero, zero_mul, zero_mul]
    intro i _
    exact (congrArg _ ((congrArg (gs _ z _) (p₄ i b hb _)).trans (gs_zero' _ z _ (hJ.mem _ _)))).trans (mul_zero _)

end GlobalTheory.UT.PullExp
end
