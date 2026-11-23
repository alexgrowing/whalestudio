import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecFracExt
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan

open MonObj
open GlobalTheory.CompanionTheory.Ar.LieTangent (epsBase epsScale isTanAt_iff isTanAt_scale spec_dual_eps spec_eps_alg)

section Push

variable (T : CDVR) {X : Scheme.{0}} (zV : Spec (CommRingCat.of T.V) ⟶ X) {A : CategoryTheory.Over X} [GrpObj A]
  {B : CategoryTheory.Over (Spec (CommRingCat.of T.V))} [GrpObj B] {Ψ : B.left ⟶ A.left}

theorem epsOver_hom :
    (epsOver T.V T.V).hom = Spec.map (CommRingCat.ofHom (algebraMap T.V (DualNumber T.V))) :=
  rfl

def idU : epsAt zV ⟶ CategoryTheory.Over.mk ((epsOver T.V T.V).hom ≫ zV) :=
  CategoryTheory.Over.homMk (𝟙 _) (by rw [Category.id_comp]; rfl)

def pushAt (h : IsGrpPullback B A zV Ψ) : (epsOver T.V T.V ⟶ B) →* (epsAt zV ⟶ A) :=
  (preHom (idU T zV)).comp (pushHom h (epsOver T.V T.V))

def pushGen (h : IsGrpPullback B A zV Ψ) : (epsOver T.V T.V ⟶ B) →* (epsAt (gen T zV) ⟶ A) :=
  (preHom (epsBase (algebraMap T.V T.Fr) rfl)).comp (pushAt T zV h)

variable {T zV}

theorem pushAt_left (h : IsGrpPullback B A zV Ψ) (v : epsOver T.V T.V ⟶ B) :
    (pushAt T zV h v).left = v.left ≫ Ψ := by
  simp [pushAt, preHom, pushHom, pushPt, idU]

theorem pushGen_left (h : IsGrpPullback B A zV Ψ) (v : epsOver T.V T.V ⟶ B) :
    (pushGen T zV h v).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  simp [pushGen, preHom, pushAt_left, GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase]
private theorem key_lemma' {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {Y : Scheme.{0}} (zV : Y ⟶ X)
    {f : Y ⟶ X} (hf : f = zV) :
    (1 : CategoryTheory.Over.mk f ⟶ A).left = (1 : CategoryTheory.Over.mk zV ⟶ A).left := by
  subst hf
  rfl

private theorem one_left_comp_of_isGrpPullback_over {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {Tb : CDVR}
    {zV : Spec (CommRingCat.of Tb.V) ⟶ X} {B : CategoryTheory.Over (Spec (CommRingCat.of Tb.V))} [GrpObj B]
    {Ψ : B.left ⟶ A.left} (h : IsGrpPullback B A zV Ψ) (T' : CategoryTheory.Over (Spec (CommRingCat.of Tb.V))) :
    (1 : T' ⟶ B).left ≫ Ψ = (1 : CategoryTheory.Over.mk (T'.hom ≫ zV) ⟶ A).left := by
  have := congrArg CategoryTheory.Over.Hom.left (map_one (pushHom h T'))
  simpa [pushHom, pushPt] using this

theorem one_left (h : IsGrpPullback B A zV Ψ) :
    (1 : ptOver T.V T.V ⟶ B).left ≫ Ψ = (1 : CategoryTheory.Over.mk zV ⟶ A).left := by
  have hf : (ptOver T.V T.V).hom ≫ zV = zV := by
    simp [ptOver, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
  rw [← key_lemma' zV hf]
  exact one_left_comp_of_isGrpPullback_over h (ptOver T.V T.V)

theorem isTanAt_push (h : IsGrpPullback B A zV Ψ) {v : epsOver T.V T.V ⟶ B} (hv : IsTan v) :
    IsTanAt A zV (pushAt T zV h v) := by
  have e : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
      (1 : ptOver T.V T.V ⟶ B).left := hv
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ (pushAt T zV h v).left =
    (1 : CategoryTheory.Over.mk zV ⟶ A).left
  rw [pushAt_left, ← Category.assoc, e]
  exact one_left h

theorem isTan_of_push (h : IsGrpPullback B A zV Ψ) {v : epsOver T.V T.V ⟶ B}
    (hv : IsTanAt A zV (pushAt T zV h v)) : IsTan v := by
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
    (1 : ptOver T.V T.V ⟶ B).left
  have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ (pushAt T zV h v).left =
      (1 : CategoryTheory.Over.mk zV ⟶ A).left := hv
  rw [pushAt_left, ← Category.assoc, ← one_left h] at hv'
  refine h.1.hom_ext hv' ?_
  rw [Category.assoc, CategoryTheory.Over.w v, CategoryTheory.Over.w (1 : ptOver T.V T.V ⟶ B), epsOver_hom,
    GlobalTheory.CompanionTheory.Ar.LieTangent.spec_comp]
  simp [ptOver, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]

theorem pushAt_surj (h : IsGrpPullback B A zV Ψ) (v : epsAt zV ⟶ A) :
    ∃ v' : epsOver T.V T.V ⟶ B, pushAt T zV h v' = v := by
  have hw : v.left ≫ A.hom = (epsOver T.V T.V).hom ≫ zV := by
    rw [CategoryTheory.Over.w v, epsOver_hom]
    rfl
  refine ⟨CategoryTheory.Over.homMk (h.1.lift v.left (epsOver T.V T.V).hom hw) (h.1.lift_snd _ _ _), ?_⟩
  apply CategoryTheory.Over.OverMorphism.ext
  rw [pushAt_left]
  exact h.1.lift_fst _ _ _

end Push

section Model

variable {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {R : Type} [CommRing R]
  {x : Spec (CommRingCat.of R) ⟶ X} {EC : Type} [AddCommGroup EC] [Module R EC]

theorem pt_list_sum (MC : LieModel A x EC) (l : List EC) : MC.pt l.sum = (l.map MC.pt).prod := by
  induction l with
  | nil =>
    simp only [List.sum_nil, List.map_nil, List.prod_nil]
    exact MC.pt_zero
  | cons a l ih => rw [List.sum_cons, MC.add, ih, List.map_cons, List.prod_cons]

theorem pt_sum (MC : LieModel A x EC) {r : ℕ} (f : Fin r → EC) :
    MC.pt (∑ i, f i) = (List.ofFn fun i => MC.pt (f i)).prod := by
  rw [← List.sum_ofFn, pt_list_sum, List.map_ofFn]
  rfl

theorem mem_eigSp_iff {O : Type} [CommRing O] (ρ : O →+* Module.End R EC) (σ : O →+* R) (w : EC) :
    w ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ↔ ∀ a, ρ a w = σ a • w := by
  simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

end Model

section Main

variable (T : CDVR) {X : Scheme.{0}} (zV : Spec (CommRingCat.of T.V) ⟶ X) {A : CategoryTheory.Over X} [GrpObj A]
  {B : CategoryTheory.Over (Spec (CommRingCat.of T.V))} [GrpObj B] {Ψ : B.left ⟶ A.left}

theorem eigen_span_lie_basis (h : IsGrpPullback B A zV Ψ) {O : Type} [CommRing O] (aA : O → (A ⟶ A))
    (hA : ∀ a, IsMonHom (aA a)) (aB : O → (B ⟶ B)) (hc : ∀ a, (aB a).left ≫ Ψ = Ψ ≫ (aA a).left)
    {EC : Type} [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC]
    (MC : LieModel A (FinRd.Roots.gen T zV) EC) (ρC : O →+* Module.End T.Fr EC) (hρ : MC.IsActOf aA ρC)
    (σ : O →+* T.V) {r : ℕ} (ub : Fin r → (epsOver T.V T.V ⟶ B)) (hut : ∀ i, IsTan (ub i))
    (hue : ∀ i a, (ub i ≫ aB a).left =
      Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ (ub i).left)
    (hub : ∀ w : epsOver T.V T.V ⟶ B, IsTan w →
      (∀ a, (w ≫ aB a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ w.left) →
      ∃ cf : Fin r → T.V, IsComb ub cf w)
    (yb : Fin r → EC)
    (hyb : ∀ i, (MC.pt (yb i)).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (ub i).left ≫ Ψ)
    (L : Submodule T.V EC)
    (hL : ∀ w, w ∈ L ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zV ⟶ A, GlobalTheory.CompanionTheory.Ar.IsTanAt A zV v ∧
      (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left) :
    L ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V =
      Submodule.span T.V (Set.range yb) := by
  have hue' : ∀ i a, (ub i ≫ aB a).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (σ a))) ≫ (ub i).left := hue
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V (FractionRing T.V)
  apply le_antisymm
  · rintro w ⟨hwL, hwE⟩
    obtain ⟨v, hvt, hvl⟩ := (hL w).1 hwL
    obtain ⟨v', rfl⟩ := pushAt_surj h v
    have hv't := isTan_of_push h hvt
    have hwE' : ∀ a, ρC a w = ((algebraMap T.V T.Fr).comp σ) a • w := (mem_eigSp_iff _ _ _).1 hwE
    have hpw : MC.pt w = pushGen T zV h v' := by
      apply CategoryTheory.Over.OverMorphism.ext
      rw [pushGen_left, hvl, pushAt_left]
    have hv'e : ∀ a, (v' ≫ aB a).left =
        Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ v'.left := by
      intro a
      have hp := isTanAt_push h hv't
      have ht1 : GlobalTheory.CompanionTheory.Ar.IsTanAt A zV (pushAt T zV h v' ≫ aA a) := by
        have hp' := hp
        unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at hp' ⊢
        rw [CategoryTheory.Over.comp_left, ← Category.assoc, hp', ← CategoryTheory.Over.comp_left]
        have := hA a
        simp
      have ht2 : GlobalTheory.CompanionTheory.Ar.IsTanAt A zV (GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale zV (σ a) ≫ pushAt T zV h v') :=
        isTanAt_scale (σ a) hp
      have eq1 : pushAt T zV h v' ≫ aA a = GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale zV (σ a) ≫ pushAt T zV h v' := by
        refine GlobalTheory.CompanionTheory.Ar.LieTangent.tan_ext hinj ht1 ht2 ?_
        have e1 := congrArg CategoryTheory.Over.Hom.left (hρ a w)
        rw [hwE' a, MC.smul, hpw, CategoryTheory.Over.comp_left, pushGen_left] at e1
        simp only [CategoryTheory.Over.comp_left, pushAt_left, Category.assoc] at e1 ⊢
        rw [← e1]
        simp only [GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale, CategoryTheory.Over.homMk_left]
        simp only [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]
      refine h.1.hom_ext ?_ ?_
      · rw [CategoryTheory.Over.comp_left, Category.assoc, hc a, ← Category.assoc, ← pushAt_left h v',
          ← CategoryTheory.Over.comp_left, eq1, CategoryTheory.Over.comp_left, pushAt_left]
        simp only [GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale, CategoryTheory.Over.homMk_left, Category.assoc]
        rfl
      · rw [CategoryTheory.Over.w (v' ≫ aB a), Category.assoc, CategoryTheory.Over.w v', epsOver_hom]
        exact (GlobalTheory.CompanionTheory.Ar.LieTangent.spec_eps_alg (σ a)).symm
    obtain ⟨cf, hcf⟩ := hub v' hv't hv'e
    obtain ⟨u, hu, hv'u⟩ := hcf
    have hw : w = ∑ i, cf i • yb i := by
      apply MC.inj
      rw [hpw, pt_sum, hv'u, map_list_prod, List.map_ofFn]
      congr 1
      apply congrArg List.ofFn
      funext i
      apply CategoryTheory.Over.OverMorphism.ext
      rw [Function.comp_apply, pushGen_left, hu i, ← algebraMap_smul T.Fr (cf i) (yb i), MC.smul, hyb i]
      simp only [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
      rw [show Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (cf i))) =
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (cf i))) from rfl, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]
    rw [hw]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨(hL _).2 ⟨pushAt T zV h (ub i), isTanAt_push h (hut i), by rw [hyb i, pushAt_left]⟩, ?_⟩
    show yb i ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)
    rw [mem_eigSp_iff]
    intro a
    apply MC.inj
    apply CategoryTheory.Over.OverMorphism.ext
    rw [hρ a (yb i), MC.smul, CategoryTheory.Over.comp_left, hyb i]
    simp only [Category.assoc]
    rw [← hc a, ← Category.assoc (ub i).left, ← CategoryTheory.Over.comp_left, hue' i a]
    simp only [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]

end Main

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan

theorem GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan.eig_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → (∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left) → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf tX.act.act ρC → ∀ (σ : 𝓞 E →+* T.V) (r : ℕ) (ub : Fin r → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i a, (ub i ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ (ub i).left) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → (∀ a, (w ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ w.left) → ∃ cf : Fin r → T.V, IsComb ub cf w) → ∀ yb : Fin r → EC, (∀ i, (MC.pt (yb i)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (ub i).left ≫ Ψ) → ∀ L : Submodule T.V EC, (∀ w, w ∈ L ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zV ⟶ tX.G, GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G zV v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left) → L ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V = Submodule.span T.V (Set.range yb) := by
  intro E _ _ _ H X tX T zV G Ψ h hc EC _ _ _ _ MC ρC hρ σ r ub hut hue hub yb hyb L hL
  exact eigen_span_lie_basis T zV h tX.act.act tX.act.hom G.act.act hc MC ρC hρ σ ub hut hue hub yb hyb L hL
