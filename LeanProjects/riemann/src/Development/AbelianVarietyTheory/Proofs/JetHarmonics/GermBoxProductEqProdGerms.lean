import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImportsBis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm.BoxGerm
open GlobalTheory.BoxFamily GlobalTheory.PowGerm.FrameN

section General

variable {X X' Y Y₀ Y₁ Z : Scheme.{0}} {M : LB X}

theorem gs_stalkMap (r : Z ⟶ X') (β : X' ⟶ X) (z : Z) (U : X.Opens) (h : β (r z) ∈ U) (a : Γ(X, U)) :
    (r.stalkMap z).hom (gs β (r z) U a) = gs (r ≫ β) z U a := by
  rw [← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]
  exact Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _

theorem sval_along (hM : M.IsLB) (g : Y₁ ⟶ X) (z : Y ⟶ Y₁) (x : Y₀ ⟶ X) (s : Y ⟶ Y₀) (hzg : z ≫ g = s ≫ x) (q : ℕ)
    (σ : LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => g) (fun _ => (q : ℤ))))
    (τ : LB.Gen (LB.LinComb M (K := Fin 1) (fun _ => x) (fun _ => (1 : ℤ)))) (a : Γ(Y, ⊤))
    (H : ∀ y J, Good M y J → sval σ z y J = gs (𝟙 Y) y ⊤ a * (val τ s y J ^ q).val)
    (r : Z ⟶ Y) (y : Z) (J) (hJ : Good M y J) :
    sval σ (r ≫ z) y J = gs r y ⊤ a * (val τ (r ≫ s) y J ^ q).val := by
  have m₀ : (z ≫ g) (r y) ∈ M.U (J (r ≫ z ≫ g)) := hJ (r ≫ z ≫ g)
  obtain ⟨J₀, hJ₀, e⟩ := exists_good M hM (r y) (fun _ : PUnit => z ≫ g) (fun _ => J (r ≫ z ≫ g)) (fun _ _ _ => rfl)
    (fun _ => m₀)
  have e' : J₀ (z ≫ g) = J (r ≫ z ≫ g) := e PUnit.unit
  have h := congrArg (r.stalkMap y).hom (H (r y) J₀ hJ₀)
  have m₁ : z (r y) ∈ LB.wchart M (fun _ : Fin 1 => g) (fun _ => J (r ≫ z ≫ g)) := Set.mem_iInter.2 fun _ => m₀
  have m₂ : s (r y) ∈ LB.wchart M (fun _ : Fin 1 => x) (fun _ => J (r ≫ z ≫ g)) :=
    Set.mem_iInter.2 fun _ => (show (s ≫ x) (r y) ∈ M.U (J (r ≫ z ≫ g)) from hzg ▸ m₀)
  rw [sval_of σ z _ J₀ (fun _ => J (r ≫ z ≫ g)) (fun _ => e'),
    val_of τ s _ J₀ (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [← hzg]; exact e'), map_mul,
    gs_stalkMap r (𝟙 Y) y ⊤ trivial, Category.comp_id, Units.val_pow_eq_pow_val, map_pow] at h
  rw [sval_of σ (r ≫ z) y J (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [Category.assoc]),
    val_of τ (r ≫ s) y J (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [Category.assoc, ← hzg]),
    Units.val_pow_eq_pow_val]
  refine (gs_stalkMap r z y _ m₁ _).symm.trans (h.trans (congrArg (fun u => gs r y ⊤ a * u ^ q) ?_))
  exact (congrArg (r.stalkMap y).hom (gs_unit s _ _ m₂ _).symm).trans
    ((gs_stalkMap r s y _ m₂ _).trans (gs_unit (r ≫ s) y _ m₂ _))

theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (y : Sp B) (a : A) :
    gs (spMap φ) y ⊤ (toΓ A a) = gs (𝟙 (Sp B)) y ⊤ (toΓ B (φ a)) := by
  have e : (spMap φ).appTop.hom (toΓ A a) = toΓ B (φ a) :=
    (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm
  rw [← e]
  exact ((gs_pull (𝟙 _) (spMap φ) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm

end General

theorem psJet_boxSer {F : Type} [CommRing F] {n d : ℕ} (m : ℕ) (f : Fin n → PS F 1 d) :
    psJet m (boxSer f) = ∏ i, jetCopy (S := F) d m i (psJet m (f i)) := by
  have hp : ∀ (S : Finset (Fin n)) (g : Fin n → PS F n d), psJet m (∏ i ∈ S, g i) = ∏ i ∈ S, psJet m (g i) := by
    intro S g
    induction S using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.prod_empty, FBIdJet.psJet_one]
    | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, FBIdJet.psJet_mul, ih]
  rw [boxSer, hp]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [MvPowerSeries.rename_eq_subst, FBIdJet.psJet_subst m _ (fun p => by simp)]
  refine DFunLike.congr_fun (GermD.jet_hom_ext fun p => ?_) _
  rw [jetCopy, GermD.jetMap_mk, GermD.jetMap_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Function.comp_apply,
    ← MvPolynomial.coe_X, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem exists_lift {V : Type} [CommRing V] [IsDomain V] (G : Over (Sp V)) (F : Type) [Field F]
    [Algebra (FractionRing V) F] {Y : Scheme.{0}} (a : Y ⟶ (TFK (R := V) F).left) (b : Y ⟶ G.left)
    (h : b ≫ G.hom = a ≫ (TFK (R := V) F).hom ≫ jK V) :
    ∃ z : Y ⟶ (UnifPre.GF (R := V) (G := G) F).left,
      z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = a ∧
      z ≫ UnifPre.gFK (R := V) (G := G) F = b := by
  let T : Over (TK V).left := Over.mk (a ≫ (TFK (R := V) F).hom)
  let u : T ⟶ TFK (R := V) F := Over.homMk a rfl
  let w : T ⟶ (Over.pullback (jK V)).obj G :=
    Over.homMk (pullback.lift b (a ≫ (TFK (R := V) F).hom) (by rw [h, Category.assoc])) (pullback.lift_snd _ _ _)
  refine ⟨(lift u w).left, congrArg (fun q => q.left) (lift_fst u w), ?_⟩
  have e : (lift u w).left ≫ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = w.left :=
    congrArg (fun q => q.left) (lift_snd u w)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans (pullback.lift_fst _ _ _))

end GlobalTheory.PowGerm.BoxGerm

namespace GlobalTheory.PowGerm
open GlobalTheory.BoxFamily FrameN BoxGerm

set_option maxHeartbeats 1000000 in

theorem boxGermSt_holds : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxGermSt := by
  intro h₁ h₂ h₄ hT E _ _ _ H V _ _ _ _ t P d FT act ph1 ph2 sy ad tg xT eT wPT hch hfr hpr τ₁ g₁ el n D' A' G' _ _
    pD pA pG U' PU F _ _ _ _ q hq σ s f σ' S hσ hS hE' m
  have hM : P.U.LG.L.IsLB := P.U.LG.isLB
  have hM' : U'.LG.L.IsLB := U'.LG.isLB
  obtain ⟨τ, hτ, hv₀⟩ := exists_boxPull_gen (pr := fun i => (pG.pr i).left) PU.wL PU.wL_gen hM hM' (K := Fin 1)
      (φ' := fun _ => (zV pG xT m).left) (φ := fun _ _ => (xT m).left) (ε := fun _ => 1) (cpy V n d m)
      (fun i _ => zV_pr pG xT m i) (fun _ => τ₁ m) (fun _ => g₁ m)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V (Fin n × Fin d) m)) (y : Z) (J J'), Good P.U.LG.L y J →
      Good U'.LG.L y J' →
      om PU.wL y J J' (r ≫ (zV pG xT m).left) * val τ r y J' = ∏ i, val (τ₁ m) (r ≫ cpy V n d m i) y J := by
    intro Z r y J J' hJ hJ'
    have := hv₀ Z r y J J' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_one] at this
  obtain ⟨z, h₀, hzg⟩ := exists_lift G' F (spMap (algebraMap F (Jet F (Fin n × Fin d) m)))
    (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m) ≫ (zV pG xT m).left) (by
      rw [Category.assoc _ (zV pG xT m).left, Over.w (zV pG xT m)]
      symm
      show spMap _ ≫ spMap (algebraMap (FractionRing V) F) ≫ spMap (algebraMap V (FractionRing V)) =
        spMap _ ≫ spMap (algebraMap V (Jet V (Fin n × Fin d) m)) ≫ 𝟙 _
      simp only [spMap, Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [JetTr.jetCoef_alg, ← IsScalarTower.algebraMap_eq])
  have hp : ∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i := fun i => by
    rw [← Category.assoc, hzg, Category.assoc, zV_pr, ← Category.assoc, coef_cpy, jptN]
  choose zi hz₀ hz₁ hz₂ using fun i => (hσ i).2 m
  have hc : ∀ i, cpy F n d m i ≫ spMap (jetCoef (algebraMap V F) (Fin 1 × Fin d) m) = jcN V F d n m i := fun i => by
    rw [jcN]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have main := GlobalTheory.BoxSectionValues.main h₁ h₂ h₄ hT V n P.D D' P.A A' t.G G' pD pA pG U' P.U PU F q hq σ s σ' S
    (fun i => (hσ i).1) hS hE' _ z (fun i => cpy F n d m i ≫ zi i)
    (fun i => by rw [hp, Category.assoc, hz₁, ← Category.assoc, hc, jptN])
    (fun i => by
      rw [h₀, Category.assoc, hz₀]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [AlgHom.comp_algebraMap])
  have core := core_iff (pr := fun i => (pG.pr i).left) hM hM' PU.wL PU.wL_gen (τ₁ m) (g₁ m) (cpy V n d m)
      (zV_pr pG xT m) τ hτ hv (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m))
      (UnifPre.gFK (R := V) (G := G') F) z hzg q
      (genCast (congrArg RigLB.L P.bundle).symm _ _ (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
        LB.pullGen t.PP.L _ _ (genPowG t _ _ (eLG t (𝟙 (Sp V)) d xT act eT wPT m) q) (jcN V F d n m i)))
      (fun y J hJ => (val_cast_prod t _ _ _ _ _ q _ y J hJ).trans (Finset.prod_congr rfl fun i _ => by
        rw [coef_cpy]
        have := val_along hM _ _ _ _ (el m) (jcN V F d n m i) y J hJ
        rw [Category.comp_id] at this
        exact congrArg (· ^ q) this.symm)) σ' (toΓ _ (psJet m (boxSer f)))
  obtain ⟨a, b, k₂, k₃, k₄⟩ := core.2 fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at hM y
    have e₁ : (om PU.wL y J J' (z ≫ UnifPre.gFK (R := V) (G := G') F) ^ q).val * sval σ' z y J' =
        ∏ i, sval (σ i) (cpy F n d m i ≫ zi i) y J := main y J J' hJ hJ'
    have e₂ : ∀ i, sval (σ i) (cpy F n d m i ≫ zi i) y J =
        gs (𝟙 _) y ⊤ (toΓ _ (jetCopy (S := F) d m i (psJet m (f i)))) *
          (val (τ₁ m) (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m) ≫ cpy V n d m i) y J ^ q).val := fun i => by
      rw [sval_along hM _ (zi i) _ _ (hz₁ i) q (σ i) (τ₁ m) _ (hz₂ i) (cpy F n d m i) y J hJ, hc, coef_cpy, gs_spMap]
      rfl
    have e₃ := hv _ (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m)) y J J' hJ hJ'
    rw [← hzg] at e₃
    rw [Finset.prod_congr rfl fun i _ => e₂ i, Finset.prod_mul_distrib, ← Units.coe_prod, Finset.prod_pow, ← e₃,
      mul_pow, Units.val_mul, mul_left_comm, ← gs_prod _ y ⊤ trivial, ← map_prod, ← psJet_boxSer] at e₁
    exact (Units.mul_right_inj _).1 e₁
  exact ⟨z, a, b, h₀, hp, k₂, (corr_genCast _ _ _).2 k₃, k₄⟩

end GlobalTheory.PowGerm
