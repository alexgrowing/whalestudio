import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnifPolarizationSquareIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibrePullbackSiegelTraitModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleTraitFibreEqUniversalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitUniq

theorem form_of_assoc {V V' W : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [CommRing W] [IsDomain W]
    {Dg : DegPre V} {Dg' : DegPre V'} {ϖ : V} {ϖ' : V'} {β : LinearMap.BilinForm ℤ Dg.X}
    {β' : LinearMap.BilinForm ℤ Dg'.X} (hβ : ∀ a b, β a b = β b a) (hβ' : ∀ a b, β' a b = β' b a)
    (hm : IsMonomial Dg ![ϖ] ![β]) (hm' : IsMonomial Dg' ![ϖ'] ![β']) (f : V →+* W) (f' : V' →+* W)
    (ε : Dg.X ≃+ Dg'.X) {w : W} (hw : Irreducible w) {m m' : ℕ} (h : Associated (f ϖ) (w ^ m))
    (h' : Associated (f' ϖ') (w ^ m'))
    (hε : ∀ y r r', PsiCoord Dg y r → PsiCoord Dg' (ε y) r' → Associated (f r ^ 2) (f' r' ^ 2)) :
    ∀ a b, (m : ℤ) * β a b = m' * β' (ε a) (ε b) := by
  have key : ∀ a, (m : ℤ) * β a a = m' * β' (ε a) (ε a) := by
    intro a
    obtain ⟨u₁, n₁, hn₁, c₁⟩ := hm a
    obtain ⟨u₂, n₂, hn₂, c₂⟩ := hm' (ε a)
    have a₁ : Associated (f (u₁ * ∏ i, ![ϖ] i ^ n₁ i)) (w ^ (m * n₁ 0)) := by
      rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow, pow_mul]
      exact (associated_unit_mul_left _ _ (u₁.isUnit.map f)).trans h.pow_pow
    have a₂ : Associated (f' (u₂ * ∏ i, ![ϖ'] i ^ n₂ i)) (w ^ (m' * n₂ 0)) := by
      rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow, pow_mul]
      exact (associated_unit_mul_left _ _ (u₂.isUnit.map f')).trans h'.pow_pow
    have a₃ := (a₁.pow_pow (n := 2)).symm.trans ((hε a _ _ c₁ c₂).trans (a₂.pow_pow (n := 2)))
    rw [← pow_mul, ← pow_mul] at a₃
    have e := GlobalTheory.SiegLoc.TraitOrd.eq_of_associated_pow hw a₃
    have h₀ : β a a = 2 * n₁ 0 := by simpa using hn₁ 0
    have h₀' : β' (ε a) (ε a) = 2 * n₂ 0 := by simpa using hn₂ 0
    rw [h₀, h₀']
    have e' := congrArg (fun x : ℕ => (x : ℤ)) e
    push_cast at e'
    linarith
  intro a b
  have k := key (a + b)
  have ka := key a
  have kb := key b
  simp only [map_add, LinearMap.add_apply] at k
  rw [hβ b a, hβ' (ε b) (ε a)] at k
  simp only [mul_add] at k
  linarith

theorem extIso {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {G₁ G₂ : Over (Sp W)} [GrpObj G₁]
    [GrpObj G₂] (h₁ : IsSemiAbelian G₁) (h₂ : IsSemiAbelian G₂)
    (e : (Over.pullback (jK W)).obj G₁ ≅ (Over.pullback (jK W)).obj G₂) (he : IsMonHom e.hom) :
    ∃ E : G₁ ≅ G₂, IsMonHom E.hom ∧ (Over.pullback (jK W)).map E.hom = e.hom := by
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₁ G₂ h₁ h₂ e.hom he
  obtain ⟨F₁, ⟨hF₁, hF₁'⟩, -⟩ :=
    GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₂ G₁ h₂ h₁ e.inv inferInstance
  refine ⟨⟨F, F₁, ?_, ?_⟩, hF, hF'⟩
  · exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₁ G₁ h₁ h₁ (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, hF', hF₁', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₂ G₂ h₂ h₂ (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, hF₁', hF', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem genFib (T : Trait F) {W : Type} [CommRing W] [IsDomain W] (f : T.V →+* W)
    (fK : FractionRing T.V →+* FractionRing W) (hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) :
    ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left,
      IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧
      κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) =
        pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) :=
  GlobalTheory.T.exists_genericFibre_pullback_siegelTrait_model g n o ζ F T W f fK hfK

theorem lamPull (T : Trait F) {W : Type} [CommRing W] [IsDomain W] (fK : FractionRing T.V →+* FractionRing W)
    (G'' : Over (Sp W)) [GrpObj G''] (β : G''.left ⟶ T.G.left)
    (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left)
    (hκ : IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ)
    (hκβ : κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β)
    (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left) (hα₂ : IsSquare (κ ≫ T.α) α₂) :
    LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β)))
      (F.univ.P.pull α₂) :=
  GlobalTheory.T.mumfordBundle_trait_fibre_eq_universal g n o ζ F T W fK G'' β κ hκ hκβ α₂ hα₂

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem isCN (T : Trait F) : GlobalTheory.TorRef.IsCN T.V := ⟨inferInstance, inferInstance, T.complete, T.char⟩

theorem isCN_of_base {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (h : GlobalTheory.Mum.Base W) : GlobalTheory.TorRef.IsCN W :=
  ⟨h.1.1, h.1.2.2.1, h.1.2.2.2, h.2⟩

theorem pull (T : Trait F) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.TorRef.IsCN W) (f : T.V →+* W)
    (hf : Function.Injective f) (hl : IsLocalHom f) (fK : FractionRing T.V →+* FractionRing W)
    (G'' : Over (Sp W)) [GrpObj G''] [IsCommMonObj G''] (β : G''.left ⟶ T.G.left)
    (hβ : IsGrpPullback G'' T.G (spMap f) β) (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left)
    (hκ : IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ)
    (hκβ : κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β)
    (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left) (hα₂ : IsSquare (κ ≫ T.α) α₂) :
    ∃ (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'')
      (ε : D'.toPre.X ≃+ T.D.toPre.X) (L : LB ((Over.pullback (jK W)).obj G'').left), L.IsLB ∧
      LBIso L (U'.LG.L.pull (pullback.fst G''.hom (jK W))) ∧
      LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') L) (F.univ.P.pull α₂) ∧
      ∀ y r, PsiCoord T.D.toPre (ε y) r → ∃ u : Wˣ, PsiCoord D'.toPre y (u * f r) := by
  have hΛ := lamPull T fK G'' β κ hκ hκβ α₂ hα₂
  have gB := (isGrpPullback_pullback G'' (jK W)).comp hβ
  obtain ⟨hr, hs⟩ := GlobalTheory.T.rigidified_symmetric_lineBundle_groupPullback _ _ _ T.G _ _ gB T.U.LG T.U.symG T.U.symG_gen
  have hα := hκ.comp T.cart
  obtain ⟨ha, hamp, hkt⟩ := GlobalTheory.T.principalPolarization_of_mumfordBundle_siegelFibre o ζ g n F _ (spMap fK ≫ T.y) _ (κ ≫ T.α) α₂ hα hα₂ _
    (pull_isLB T.U.LG.isLB _) hr hs hΛ
  have hϖ : f T.ϖ ≠ 0 := fun h => T.irr.ne_zero (hf (h.trans (map_zero f).symm))
  obtain ⟨D', A', U', ε, hL, hc⟩ := GlobalTheory.T.exists_uniformisation_baseChange_with_coordinates T.V W (isCN T) hW f hl T.G T.semi T.D T.A T.U
    {p | T.ϖ ∉ p.asIdeal} (PrimeSpectrum.isOpen_basicOpen (a := T.ϖ))
    (fun y => T.mono.psiUnitOn y fun p hp => by simpa using hp) (fun h => hϖ (RingHom.mem_ker.1 h)) G'' β hβ ha hr hs
    hamp hkt
  exact ⟨D', A', U', ε, _, pull_isLB T.U.LG.isLB _, hL, hΛ, hc⟩

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

theorem traitUniq : TraitUniqSt := by
  intro g n o _ ζ F T T' W _ _ _ f f' fK fK' hW hdvr hf hf' hl hl' hK hK' hy w m m' hw hm hm'
  haveI := hdvr
  have hWC := isCN_of_base hW
  have hs₁ : IsSemiAbelian ((Over.pullback (spMap f)).obj T.G) := IsSemiAbelian.pullback (spMap f) T.G T.semi
  have hs₂ : IsSemiAbelian ((Over.pullback (spMap f')).obj T'.G) := IsSemiAbelian.pullback (spMap f') T'.G T'.semi
  obtain ⟨κ₁, hκ₁, hκβ₁⟩ := genFib T f fK hK
  obtain ⟨κ₂, hκ₂, hκβ₂⟩ := genFib T' f' fK' hK'
  have hα₁ := hκ₁.comp T.cart
  have hα₂ := (hκ₂.comp T'.cart).congr hy.symm rfl
  obtain ⟨e, he, heα⟩ := grpPullback_iso hα₁ hα₂
  obtain ⟨E, hE, hEe⟩ := extIso hs₁ hs₂ e he
  have w₁ := hα₁.1.w
  let α₂ := pullback.map ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).hom
    ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).hom F.univ.A.hom F.univ.A.hom
    (κ₁ ≫ T.α) (κ₁ ≫ T.α) (spMap fK ≫ T.y) w₁.symm w₁.symm
  have hsq : IsSquare (κ₁ ≫ T.α) α₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hβ' : IsGrpPullback ((Over.pullback (spMap f)).obj T.G) T'.G (spMap f')
      (E.hom.left ≫ pullback.fst T'.G.hom (spMap f')) :=
    ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback T'.G (spMap f'))).congr (Category.id_comp _) rfl
  have hκ' := ((isGrpPullback_of_iso e).comp hκ₂).congr (Category.id_comp _) rfl
  have hκβ' : (e.hom.left ≫ κ₂) ≫ T'.U.gen.inv.left ≫ pullback.fst T'.G.hom (jK T'.V) =
      pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ E.hom.left ≫ pullback.fst T'.G.hom (spMap f') := by
    rw [Category.assoc, hκβ₂, ← Category.assoc, ← Category.assoc, ← hEe]
    congr 1
    exact pullback.lift_fst _ _ _
  have hsq' : IsSquare ((e.hom.left ≫ κ₂) ≫ T'.α) α₂ := by rw [Category.assoc, heα]; exact hsq
  obtain ⟨E₁, A₁, U₁, ε₁, L₁, l₁, i₁, m₁, c₁⟩ := pull T hWC f hf hl fK _ _ (isGrpPullback_pullback T.G (spMap f))
    κ₁ hκ₁ hκβ₁ α₂ hsq
  obtain ⟨E₂, A₂, U₂, ε₂, L₂, l₂, i₂, m₂, c₂⟩ := pull T' hWC f' hf' hl' fK' _ _ hβ' _ hκ' hκβ' α₂ hsq'
  have hΛ : LBIso (abelian₂ _ L₂) (abelian₂ _ L₁) :=
    LBIso.trans (DVR.linComb_isLB _ l₂ _ _) (pull_isLB F.univ.isLB _) (DVR.linComb_isLB _ l₁ _ _) m₂ m₁.symm
  obtain ⟨ε, hε⟩ := GlobalTheory.SqUnifCoord.main W hWC _ hs₁ E₂ E₁ A₂ A₁ U₂ U₁
    (GlobalTheory.squares_iso_of_lam_generic W hWC _ hs₁ E₂ E₁ A₂ A₁ U₂ U₁ L₂ L₁ l₂ l₁ i₂ i₁ hΛ)
  let ε₀ : T.D.toPre.X ≃+ T'.D.toPre.X := (ε₁.symm.trans ε).trans ε₂
  have hε₀ : ∀ z r₁ r₂, PsiCoord T.D.toPre z r₁ → PsiCoord T'.D.toPre (ε₀ z) r₂ →
      Associated (f r₁ ^ 2) (f' r₂ ^ 2) := by
    intro z r₁ r₂ h₁ h₂
    obtain ⟨u₁, k₁⟩ := c₁ (ε₁.symm z) r₁ (by rwa [AddEquiv.apply_symm_apply])
    obtain ⟨u₂, k₂⟩ := c₂ (ε (ε₁.symm z)) r₂ h₂
    have := hε _ _ _ k₂ k₁
    rw [mul_pow, mul_pow] at this
    exact ((associated_unit_mul_left _ _ (u₁.isUnit.pow 2)).symm.trans this.symm).trans
      (associated_unit_mul_left _ _ (u₂.isUnit.pow 2))
  exact ⟨ε₀, form_of_assoc T.symm T'.symm T.mono T'.mono f f' ε₀ hw hm hm' hε₀⟩

end GlobalTheory.Poinc.TraitUniq
