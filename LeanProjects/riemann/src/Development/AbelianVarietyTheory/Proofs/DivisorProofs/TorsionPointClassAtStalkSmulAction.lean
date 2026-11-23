import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem exists_geomPt_range_eq_singleton (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X), Set.range z = {g} := by
  refine ⟨AlgebraicClosure (X.residueField g), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) _)) ≫ X.fromSpecResidueField g, ?_⟩
  ext y
  have h := fun t => X.fromSpecResidueField_apply g
    (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) (AlgebraicClosure (X.residueField g)))) t)
  simp only [Set.mem_range, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
  exact ⟨fun ⟨t, e⟩ => e.symm.trans (h t),
    fun e => ⟨IsLocalRing.closedPoint _, (h _).trans e.symm⟩⟩

theorem exists_geomPt_stalk_over {X' : Scheme.{0}} [IsIntegral X'] {T : Scheme.{0}} (f : T ⟶ X') [Flat f]
    {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X') [IsOpenImmersion ℓ] (p : T) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ Spec (T.presheaf.stalk p)) (z : Sp Ω ⟶ V),
      y ≫ T.fromSpecStalk p ≫ f = z ≫ ℓ := by
  obtain ⟨p', hp', hfp'⟩ := Flat.generalizingMap f (genericPoint_specializes (f p))
  have hmem : p' ∈ Set.range (T.fromSpecStalk p) := by rw [Scheme.range_fromSpecStalk]; exact hp'
  obtain ⟨d, hd⟩ := hmem
  obtain ⟨Ω, hF, hA, y, hy⟩ := exists_geomPt_range_eq_singleton _ d
  have hgen : genericPoint X' ∈ Set.range ℓ := by
    refine ((genericPoint_spec X').mem_open_set_iff (IsOpenImmersion.isOpen_range ℓ)).mpr ?_
    exact ⟨ℓ (Classical.arbitrary V), trivial, _, rfl⟩
  have hr : Set.range (y ≫ T.fromSpecStalk p ≫ f) ⊆ Set.range ℓ := by
    rintro _ ⟨t, rfl⟩
    have ht : y t = d := by
      have : y t ∈ Set.range y := ⟨t, rfl⟩
      rw [hy] at this
      exact this
    simp only [Scheme.Hom.comp_apply, ht, hd, hfp']
    exact hgen
  exact ⟨Ω, hF, hA, y, IsOpenImmersion.lift ℓ _ hr, (IsOpenImmersion.lift_fac _ _ _).symm⟩

end GlobalTheory.TorsSpec

namespace GlobalTheory.TorsSpec

theorem valAt_comp {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) (τ : torsion G n ⟶ torsion G n) (p q : (torsion G n).left) (hq : τ.left p = q) (c : M)
    (h : ValAt G n ℓ w q c) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (y : Sp Ω ⟶ Spec ((torsion G n).left.presheaf.stalk p)) (z : Sp Ω ⟶ V)
    (hyz : y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom = z ≫ ℓ) :
    y ≫ (torsion G n).left.fromSpecStalk p ≫ τ.left ≫ (torsion.ι G n).left = z ≫ w c := by
  subst hq
  have key := Scheme.SpecMap_stalkMap_fromSpecStalk τ.left (x := p)
  have hw : τ.left ≫ (torsion G n).hom = (torsion G n).hom := Over.w τ
  have h1 := h Ω (y ≫ Spec.map (τ.left.stalkMap p)) z (by
    simpa only [Category.assoc, reassoc_of% key, hw] using hyz)
  simpa only [Category.assoc, reassoc_of% key] using h1

theorem class_act : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    (hlin : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a : M) (r : 𝓞 E) (A B : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w (r • a) → B = A ≫ act.act r)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P : Over.mk t ⟶ G) (r : 𝓞 E)
    (PT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hRT : RT ≫ (torsion.ι G n).left = (P ≫ act.act r).left) (x : Sp K) (cP cR : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = r • cP := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ _ hun act hlin K _ _ t P r PT RT hPT hRT x cP cR hcP hcR
  haveI := GrpTangent.etale_torsion G hn
  haveI := mono_torsion_ι G n
  have hι : torsion.ι G n ≫ mulN G n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G)) (CartesianMonoidalCategory.toUnit_unique _ _))
  have hτ : (torsion.ι G n ≫ act.act r) ≫ mulN G n = 1 := by
    haveI := act.hom r
    rw [← act_natCast act n, Category.assoc, ← act.mul, mul_comm, act.mul, ← Category.assoc,
      act_natCast act n, hι, Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]
  obtain ⟨τ, hτι⟩ := exists_lift_torsion n _ hτ
  have hτl : τ.left ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ (act.act r).left := by
    rw [← Over.comp_left, hτι, Over.comp_left]
  have hPR : PT ≫ τ.left = RT := by
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτl, reassoc_of% hPT, hRT, Over.comp_left]
  have hq : τ.left (PT x) = RT x := by rw [← hPR, Scheme.Hom.comp_apply]
  obtain ⟨Ω, hF, hA, y, z, hyz⟩ := exists_geomPt_stalk_over (torsion G n).hom ℓ (PT x)
  have h1 := hcP Ω y z hyz
  have h2 := valAt_comp G n ℓ w τ (PT x) (RT x) hq cR hcR Ω y z hyz
  rw [hτl, reassoc_of% h1] at h2
  let A : Over.mk (z ≫ ℓ) ⟶ G := Over.homMk (z ≫ w cP) (by rw [Category.assoc, hw]; rfl)
  let B : Over.mk (z ≫ ℓ) ⟶ G := Over.homMk (z ≫ w (r • cP)) (by rw [Category.assoc, hw]; rfl)
  have h3 := congrArg (fun q => q.left) (hlin Ω z cP r A B rfl rfl)
  simp only [A, B, Over.homMk_left, Over.comp_left] at h3
  exact (hun Ω z _ _ (h3.trans ((Category.assoc _ _ _).trans h2))).symm

end GlobalTheory.TorsSpec
