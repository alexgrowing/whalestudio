import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GaIsHTFormOver

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CmpBundlesModel

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_diff {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {V : Type}
    [AddCommGroup V] [Module R V] (M : LieModel G x V) (f : G ⟶ G) [IsMonHom f] : ∃ A, M.IsDiffOf f A := by
  have ht : ∀ e, IsTanAt G x (M.pt e ≫ f) := fun e => by
    have h := M.tan e
    unfold IsTanAt at h ⊢
    rw [Over.comp_left, ← Category.assoc, h, ← Over.comp_left, MonObj.one_comp]
  choose A hA using fun e => M.onto _ (ht e)
  refine ⟨⟨⟨A, fun e e' => M.inj ?_⟩, fun c e => M.inj (Over.OverMorphism.ext ?_)⟩, hA⟩
  · rw [M.add, hA, hA, hA, M.add, MonObj.mul_comp]
  · dsimp only [RingHom.id_apply]
    rw [M.smul, hA, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc]

theorem exists_act {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {V : Type}
    [AddCommGroup V] [Module R V] (M : LieModel G x V) {O : Type} [CommRing O] (a : OAct O G) :
    ∃ ρ : O →+* Module.End R V, M.IsActOf a.act ρ := by
  choose ρ hρ using fun o => haveI := a.hom o; exists_diff M (a.act o)
  have uniq : ∀ (g : G ⟶ G) (A B : V →ₗ[R] V), M.IsDiffOf g A → M.IsDiffOf g B → A = B :=
    fun g A B hA hB => LinearMap.ext fun e => M.inj ((hA e).trans (hB e).symm)
  have hone : ρ 1 = 1 := uniq _ _ _ (hρ 1) (fun e => by
    rw [a.one, Category.comp_id]
    rfl)
  have hmul : ∀ p q, ρ (p * q) = ρ p * ρ q := fun p q => uniq _ _ _ (hρ (p * q)) (fun e => by
    rw [mul_comm p q, a.mul, Module.End.mul_apply, hρ p (ρ q e), hρ q e, Category.assoc])
  have hadd : ∀ p q, ρ (p + q) = ρ p + ρ q := fun p q => uniq _ _ _ (hρ (p + q)) (fun e => by
    rw [LinearMap.add_apply, M.add, hρ p e, hρ q e, a.add, MonObj.comp_mul])
  have hzero : ρ 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  exact ⟨{ toFun := ρ, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := hadd }, hρ⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def Hyps (g : HostAut H) {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (t t' : SAB H X)
    {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ V)
    (ρ ρ' : 𝓞 E →+* Module.End Ω V) : Prop :=
  ∃ (tΩ : SAB H (Sp Ω)) (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ),
    (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, v.left ≫ m.φ = (M.pt e).left ∧ v.left ≫ m'.φ = (M'.pt e).left) ∧
      M.IsActOf t.act.act ρ ∧ M'.IsActOf t'.act.act ρ'

theorem hyps_twist (g : HostAut H) {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (t : SAB H X)
    {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) :
    ∃ ρ : 𝓞 E →+* Module.End Ω V, Hyps g t (twistSAB t g) M M ρ (ρ.comp g.s.toRingHom) := by
  obtain ⟨ρ, hρ⟩ := exists_act M t.act
  obtain ⟨tΩ, ⟨m⟩⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sab ξ t
  refine ⟨ρ, tΩ, m, twistMap m g, fun e => ?_, hρ, fun a => hρ (g.s a)⟩
  have hw : (M.pt e).left ≫ t.G.hom = (epsAt (𝟙 (Sp Ω))).hom ≫ ξ := by
    rw [Over.w]; simp
  exact ⟨Over.homMk (m.cart.1.lift _ _ hw) (m.cart.1.lift_snd _ _ hw), m.cart.1.lift_fst _ _ hw,
    m.cart.1.lift_fst _ _ hw⟩

theorem eigSp_comp {Ω V O : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [CommRing O] (s : O ≃+* O)
    (ρ : O →+* Module.End Ω V) (τ : O →+* Ω) : eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ :=
  s.toEquiv.iInf_congr fun _ => rfl

theorem normal_int : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp ℤ) := by
  intro p
  letI : Algebra ℤ ((Sp ℤ).presheaf.stalk p) := StructureSheaf.stalkAlgebra ℤ p
  have : IsLocalization.AtPrime ((Sp ℤ).presheaf.stalk p) p.asIdeal := StructureSheaf.IsLocalization.to_stalk ℤ p
  exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization (R := ℤ) _ p.asIdeal.primeCompl
    p.asIdeal.primeCompl_le_nonZeroDivisors⟩

section HT

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {A : Type} [AddCommGroup A]

def ev (R : Type) [CommRing R] (a : A) : Module.Dual R (A →+ R) where
  toFun δ := δ a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem gen_comp (p : Cpt ξ) : spMap (genMap ξ p) ≫ X.fromSpecStalk p.1 = ξ := by
  change Spec.map (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ _ = _
  rw [Spec.map_comp_assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ

theorem pt_comp {R : Type} [CommRing R] (x : Sp R ⟶ X) (k : R →+* Ω) (hk : spMap k ≫ x = ξ) (δ : A →+ R) :
    ((TorusModel.lieModel ξ).pt (k.toAddMonoidHom.comp δ)).left =
      Spec.map (CommRingCat.ofHom (dualMap k)) ≫ ((TorusModel.lieModel x).pt δ).left := by
  refine TorusModel.left_eq_of_charVal (dualMap k) ?_ (TorusModel.tanPt x δ) (TorusModel.tanPt ξ _) fun χ => ?_
  · rw [← hk, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [TorusModel.charVal_tanPt, TorusModel.charVal_tanPt]
    ext <;> simp [dualMap]

theorem ev_isHT {R : Type} [CommRing R] [IsDomain R] (x : Sp R ⟶ X) (k : R →+* Ω) (hk : spMap k ≫ x = ξ) (a : A) :
    (TorusModel.lieModel ξ).IsHTFormOver 1 x k (ev Ω a) := by
  have hs : Subsingleton (R ⧸ Ideal.span {((1 : ℕ) : R)}) :=
    Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 (by simp))
  have hs' : Subsingleton (DualNumber (R ⧸ Ideal.span {((1 : ℕ) : R)})) :=
    ⟨fun a b => TrivSqZeroExt.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  have he : IsEmpty (Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {((1 : ℕ) : R)})))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum _))
  refine ⟨inferInstance, Unit, inferInstance, HtLatModel.triv R, _, A →+ R, inferInstance, inferInstance,
    TorusModel.lieModel x, fun δ => k.toAddMonoidHom.comp δ, 1, ev R a,
    HtLatModel.triv_torsion x 1 (fun _ g hg => by rwa [pow_one] at hg), pt_comp ξ x k hk,
    ⟨1, fun t => ?_, fun e => ?_⟩, fun _ => rfl⟩
  · simp [BT.valAt]
  · exact ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _,
      Subsingleton.elim _ _⟩

theorem htLat_one [IsIntegral X] {r : ℕ} (b : Module.Basis (Fin r) ℤ A) :
    ((TorusModel.lieModel ξ : LieModel (splitTorus X A) ξ (A →+ Ω)).htLat 1).IsVB r ⊤ := by
  let d : ∀ (R : Type) [CommRing R], Fin r → (A →+ R) := fun R _ i =>
    (Int.castAddHom R).comp (b.coord i).toAddMonoidHom
  have hd : ∀ i j, ev Ω (b j) (d Ω i) = if j = i then 1 else 0 := fun i j => by
    simp [ev, d, Finsupp.single_apply]
  have hsum : ∀ δ : A →+ Ω, δ = ∑ i, δ (b i) • d Ω i := fun δ => by
    ext a
    have h : δ a = ∑ i, δ (b.repr a i • b i) := by rw [← map_sum, b.sum_repr]
    simp [h, d, _root_.mul_comm]
  have hw : ∀ w : Module.Dual Ω (A →+ Ω), w = ∑ i, w (d Ω i) • ev Ω (b i) := fun w => by
    ext δ
    conv_lhs => rw [hsum δ]
    simp [ev, _root_.mul_comm]
  intro p _
  refine ⟨⊤, trivial, fun i => ev Ω (b i), ?_, fun q _ _ => ⟨?_, le_antisymm ?_ ?_⟩⟩
  · refine top_le_iff.1 fun w _ => ?_
    rw [hw w]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have := LinearMap.congr_fun hc (d Ω i)
    simpa [hd] using this
  · refine (HtLatModel.htLat_le_omLat _ 1 q).trans fun w h => ?_
    rw [hw w]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hi : w (d Ω i) ∈ regAt ξ q := h _ (Submodule.subset_span ⟨_, (TorusModel.lieModel _).tan (d _ i), by
      rw [← pt_comp ξ _ _ (gen_comp ξ q)]
      congr 2
      ext a
      simp [d]⟩)
    exact Submodule.smul_mem _ (⟨_, hi⟩ : regAt ξ q) (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (ev_isHT ξ (R := X.presheaf.stalk q.1) _ _ (gen_comp ξ q) _)

end HT

theorem hyps_inhabited (g : HostAut H) : ∃ (ξ : Sp ℚ ⟶ Sp ℤ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp ℤ) ∧ IsCptGen ξ ∧
    ∃ (t t' : SAB H (Sp ℤ)) (V : Type) (_ : AddCommGroup V) (_ : Module ℚ V) (M : LieModel t.G ξ V)
      (M' : LieModel t'.G ξ V) (ρ ρ' : 𝓞 E →+* Module.End ℚ V), Nontrivial V ∧ Hyps g t t' M M' ρ ρ' ∧
      ∃ r, (M.htLat 1).IsVB r ⊤ ∧ (M'.htLat 1).IsVB r ⊤ := by
  let t : SAB H (Sp ℤ) := GlobalTheory.Models.Inhab.trivTriple H (splitTorus (Sp ℤ) (𝓞 E)) (GlobalTheory.Diag.isSemiAbelian _ _)
    (GlobalTheory.Diag.diagAct _ _ _)
  let ξ : Sp ℚ ⟶ Sp ℤ := CptModel.pt (algebraMap ℤ ℚ)
  let M : LieModel t.G ξ (𝓞 E →+ ℚ) := TorusModel.lieModel ξ
  obtain ⟨ρ, h⟩ := hyps_twist g t M
  refine ⟨ξ, normal_int, CptModel.isCptGen_fractionRing, t, twistSAB t g, _, inferInstance, inferInstance, M, M, ρ, _, ?_, h,
    _, htLat_one ξ (Module.finBasis ℤ (𝓞 E)), htLat_one ξ (Module.finBasis ℤ (𝓞 E))⟩
  refine ⟨0, (Int.castAddHom ℚ).comp (Algebra.trace ℤ (𝓞 E)).toAddMonoidHom, fun h0 => ?_⟩
  have h1 := DFunLike.congr_fun h0 1
  have h2 : Algebra.trace ℤ (𝓞 E) 1 = (Module.finrank ℤ (𝓞 E) : ℤ) := by
    simpa using Algebra.trace_algebraMap (S := 𝓞 E) (1 : ℤ)
  simp [h2] at h1
  exact (Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne' (by exact_mod_cast h1.symm)

end GlobalTheory.CompanionTheory.Ar.CmpBundlesModel
