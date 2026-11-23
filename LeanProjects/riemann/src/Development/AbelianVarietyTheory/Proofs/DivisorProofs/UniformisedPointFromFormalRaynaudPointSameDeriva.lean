import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.FormalDer

open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)

theorem isLocalRing_dual (Ω : Type) [CommRing Ω] [IsLocalRing Ω] : IsLocalRing (DualNumber Ω) := by
  have : Nontrivial (DualNumber Ω) := (TrivSqZeroExt.inl_injective (R := Ω) (M := Ω)).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun y => ?_
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self y.fst

theorem mem_pow_map {Ω : Type} [CommRing Ω] (K : Ideal Ω) (n : ℕ) (y : DualNumber Ω)
    (hy : y ∈ (K.map (algebraMap Ω (DualNumber Ω))) ^ n) : y.fst ∈ K ^ n ∧ y.snd ∈ K ^ n := by
  rw [← Ideal.map_pow] at hy
  let S : Ideal (DualNumber Ω) :=
    { carrier := {y | y.fst ∈ K ^ n ∧ y.snd ∈ K ^ n}
      add_mem' := fun ha hb => ⟨by simpa using add_mem ha.1 hb.1, by simpa using add_mem ha.2 hb.2⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := fun c y hy => ⟨by simpa using Ideal.mul_mem_left _ c.fst hy.1, by
        simpa [TrivSqZeroExt.snd_mul, smul_eq_mul, _root_.mul_comm] using
          add_mem (Ideal.mul_mem_left _ c.fst hy.2) (Ideal.mul_mem_left _ c.snd hy.1)⟩ }
  have : (K ^ n).map (algebraMap Ω (DualNumber Ω)) ≤ S :=
    Ideal.map_le_iff_le_comap.2 fun r hr => ⟨by simpa [TrivSqZeroExt.algebraMap_eq_inl] using hr, by
      simp [TrivSqZeroExt.algebraMap_eq_inl]⟩
  exact this hy

theorem isHausdorff_dual {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) (I : Ideal R)
    [h : IsHausdorff (I.map φ) Ω] :
    IsHausdorff (I.map ((algebraMap Ω (DualNumber Ω)).comp φ)) (DualNumber Ω) := by
  rw [← Ideal.map_map]
  refine ⟨fun y hy => ?_⟩
  have h' : ∀ n, y.fst ∈ (I.map φ) ^ n ∧ y.snd ∈ (I.map φ) ^ n := fun n => mem_pow_map _ n y (by
    have := hy n
    rwa [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this)
  ext
  · exact h.haus y.fst fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact (h' n).1
  · exact h.haus y.snd fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact (h' n).2

theorem exists_tangent_lift {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) : ∃ u : epsR R ⟶ G, u.left = (tv v).left ∧ IsTangent u := by
  have h := CoeffWt.isGrpPullback_self G
  obtain ⟨u, e⟩ := PullbackSections.push_surj h (tv v)
  exact ⟨u, (Category.comp_id _).symm.trans (congrArg (fun q => q.left) e),
    (PullbackSections.isTangent_iff h _).2 (by rw [e]; exact PullbackSections.tv_mem _)⟩

theorem epsHom_comp {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) (δ : Derivation ℤ Ω Ω)
    (hδφ : ∀ r, δ (φ r) = 0) :
    letI : Algebra R Ω := φ.toAlgebra
    (epsHom δ).comp φ = algebraMap R (DualNumber Ω) := by
  letI : Algebra R Ω := φ.toAlgebra
  refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
  · show (epsHom δ (φ r)).fst = (algebraMap R (DualNumber Ω) r).fst
    simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl']
    rfl
  · show (epsHom δ (φ r)).snd = (algebraMap R (DualNumber Ω) r).snd
    simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl', hδφ]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ), GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH dd hdd v' hv' dd' hdd' Ω _ _ _ φ x δ hcomp hx hδφ hδ x' hx' hxx' a O f hO
  letI : Algebra R Ω := φ.toAlgebra
  have hε : (inr 1 : DualNumber Ω) * inr 1 = 0 := TrivSqZeroExt.inr_mul_inr _ _ _
  haveI := isLocalRing_dual Ω
  haveI : IsHausdorff ((maximalIdeal R).map (algebraMap R (DualNumber Ω))) (DualNumber Ω) :=
    isHausdorff_dual φ (maximalIdeal R)
  let jη : epsR R ⟶ overAt (𝟙 (Sp R)) (DualNumber R) := Over.homMk (𝟙 _) (by simp)
  obtain ⟨u₀, hu₀, hut₀⟩ := exists_tangent_lift Y.H (vH a)
  obtain ⟨u₁, hu₁, hut₁⟩ := exists_tangent_lift t.G (v' a)
  have eu₀ : u₀ = jη ≫ tv (vH a) := Over.OverMorphism.ext (hu₀.trans (Category.id_comp _).symm)
  have eu₁ : u₁ = jη ≫ tv (v' a) := Over.OverMorphism.ext (hu₁.trans (Category.id_comp _).symm)
  let T : Over (Sp R) := Over.mk (spMap φ)
  let xt : T ⟶ Y.H := Over.homMk x hx
  let xt' : T ⟶ t.G := Over.homMk x' hx'
  let kz : sp (R₀ := R) (DualNumber Ω) ⟶ T := Over.homMk (spMap (algebraMap Ω (DualNumber Ω))) (by
    show spMap _ ≫ spMap φ = Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber Ω)))
    rw [spMap, spMap, ← Spec.map_comp]
    rfl)
  let kε : sp (R₀ := R) (DualNumber Ω) ⟶ T := Over.homMk (spMap (epsHom (δ a))) (by
    show spMap _ ≫ spMap φ = Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber Ω)))
    rw [spMap, spMap, ← Spec.map_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (epsHom_comp φ (δ a) (hδφ a)))
  let kk := Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη
  let z : sp (R₀ := R) (DualNumber Ω) ⟶ Y.H := kz ≫ xt
  let z' : sp (R₀ := R) (DualNumber Ω) ⟶ t.G := kz ≫ xt'
  let yH := (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ u₀) * z
  let yG := (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ u₁) * z'

  have e₁ : yH = kε ≫ xt := by
    refine CoeffWt.eq_of_valR Y yH (kε ≫ xt) ⊤ (x (closedPoint Ω)) trivial fun V' _ hp => ?_
    have m : ⊤ ≤ x ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V') := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of Ω) x hp).ge
    obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω (DualNumber Ω)) x _ m
    obtain ⟨b₁, b₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (epsHom (δ a)) x _ m
    obtain ⟨c₁, c₂⟩ := CoeffWt.valR_translate hu₀ hut₀ (hdd a) (inr 1 : DualNumber Ω) hε z _ a₁
    refine ⟨c₁, b₁, fun α g _ => ?_⟩
    refine (c₂ g).trans (Eq.trans ?_ (b₂ g).symm)
    show valR (spMap (algebraMap Ω (DualNumber Ω)) ≫ x) _ g +
      inr 1 * valR (spMap (algebraMap Ω (DualNumber Ω)) ≫ x) _ (dd a _ g) = _
    rw [a₂, a₂, hδ a _ g m]
    ext <;> simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl']
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have pz := hxx'.pull kz (Y.rep.1 _ _ kz xt)
  have pu := (hv' a).pull (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη)
    (Y.rep.1 _ _ (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη) (tv (vH a)))
  rw [Category.assoc, Category.assoc, ← eu₀, ← eu₁] at pu
  have pm := FormalPoint.IsPointOf.mul hG pu pz (Y.rep.2 _ _ _)
  have pε := hxx'.pull kε (Y.rep.1 _ _ kε xt)
  have e₂ : yG = kε ≫ xt' := by
    have pm' : FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (kε ≫ xt)) yG := by
      rw [← e₁]; exact pm
    exact FormalPoint.IsPointOf.unique pm' pε
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω (DualNumber Ω)) x' O hO
  obtain ⟨b₁, b₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (epsHom (δ a)) x' O hO
  obtain ⟨c₁, c₂⟩ := CoeffWt.valR_translate hu₁ hut₁ (hdd' a) (inr 1 : DualNumber Ω) hε z' O a₁
  have hz : ∀ g, valR z'.left O g = algebraMap Ω (DualNumber Ω) (valR x' O g) := a₂
  have k : valR yG.left O f = valR (spMap (epsHom (δ a)) ≫ x') O f := by
    rw [e₂]
    rfl
  have k2 : algebraMap Ω (DualNumber Ω) (valR x' O f) +
      inr 1 * algebraMap Ω (DualNumber Ω) (valR x' O (dd' a O f)) = epsHom (δ a) (valR x' O f) := by
    rw [← hz, ← hz, ← c₂, k, b₂]
  have k3 := congrArg TrivSqZeroExt.snd k2
  simpa [epsHom, TrivSqZeroExt.algebraMap_eq_inl'] using k3

end GlobalTheory.Heat.FormalDer
