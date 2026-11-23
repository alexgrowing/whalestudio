import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSMulRegularCokerDualMapOfExactFibres
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CyclicIdeal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPerfectFreeFiniteComplexStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocalizationOfIsStandardSmooth

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.StabFlat
open GlobalTheory.CechPic

theorem isProjBy_baseChange {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (hf : IsProjBy f) {φ : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (h : IsPullback φ f' f t) : IsProjBy f' := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective t
  obtain ⟨H, hH, n, s, hs⟩ := hf
  have hH' : (H.pull φ).IsLB := DVR.linComb_isLB _ hH _ _
  obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl hH'
  choose s' hs' using fun j => (GlobalTheory.SecPullIso.section_pull X X' φ H _ w hH hH' hw (s j)).1.exists
  refine ⟨_, hH', n, s', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R' g.hom X' f' φ h.w ?_
    _ w s' hH' hw hs'⟩
  have e : pullback.lift φ f' h.w = h.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  have : IsClosedImmersion (pullback.lift φ f' h.w) := by rw [e]; infer_instance
  exact this

theorem pull_iso_eq_zero {X Y : Scheme.{0}} (e : Y ⟶ X) [IsIso e] (c : CechPic.Pic X) :
    CechPic.pull e c = 0 ↔ c = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  rw [← pull_id c, ← IsIso.inv_hom_id e, pull_comp, h, map_zero]

theorem loc_triv_iff {R : Type} [CommRing R] [IsLocalRing R] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of R))
    {M : LB Y} (hM : M.IsLB) :
    (∀ p : Spec (CommRingCat.of R), ∃ U : (Spec (CommRingCat.of R)).Opens, p ∈ U ∧ Triv (M.pull (q ⁻¹ᵁ U).ι)) ↔
      cls M hM = 0 := by
  have key : ∀ U : (Spec (CommRingCat.of R)).Opens, Triv (M.pull (q ⁻¹ᵁ U).ι) ↔
      CechPic.pull (q ⁻¹ᵁ U).ι (cls M hM) = 0 := fun U => (cls_eq_zero_iff (pull_isLB hM _)).symm
  constructor
  · intro h
    obtain ⟨U, hU, ht⟩ := h (IsLocalRing.closedPoint R)
    obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
    have : IsIso (q ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso Y.topIso.hom)
    exact (pull_iso_eq_zero _ _).1 ((key _).1 ht)
  · intro h p
    exact ⟨⊤, trivial, (key _).2 (by rw [h, map_zero])⟩

section Classes

variable {S : Scheme.{0}} {B T T' : Over S} [GrpObj B]

def dcl (l o : CechPic.Pic B.left) (x b : T ⟶ B) : CechPic.Pic T.left :=
  CechPic.pull (x * b).left l - CechPic.pull b.left l - CechPic.pull b.left o

theorem pull_dcl (l o : CechPic.Pic B.left) (h : T' ⟶ T) (x b : T ⟶ B) :
    CechPic.pull h.left (dcl l o x b) = dcl l o (h ≫ x) (h ≫ b) := by
  simp only [dcl, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_mul]

theorem cls_eq_dcl {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) (x : T ⟶ B)
    (h : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB) :
    cls _ h = dcl (cls L hL) (cls O hO) (fst T B ≫ x) (snd T B) := by
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have e₁ : cls _ h₁ = CechPic.pull (lift (fst T B ≫ x) (snd T B) ≫ μ[B]).left (cls L hL) -
      CechPic.pull (snd T B).left (cls L hL) := by
    refine (cls_linComb hL _ _ h₁).trans ?_
    rw [Fin.sum_univ_two, sub_eq_add_neg]
    exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)
  rw [cls_div h₁ (pull_isLB hO _), e₁, cls_pull hO]
  rfl

theorem gen_lam_iff {O : LB B.left} (hO : O.IsLB) :
    (∃ u : LB.Gen (abelian₂ B O), u.IsGen) ↔ lam (cls O hO) (fst B B) (snd B B) = 0 := by
  rw [← cls_cube_two hO (fst B B) (snd B B) (LB.isLB_linComb hO _ _)]
  exact (cls_eq_zero_iff (N := abelian₂ B O) (LB.isLB_linComb hO _ _)).symm

theorem dcl_primitive [IsCommMonObj B] {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen) (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) (x b b' : T ⟶ B) :
    dcl (cls L hL) (cls O hO) x (b * b') - dcl (cls L hL) (cls O hO) x b - dcl (cls L hL) (cls O hO) x b' +
      dcl (cls L hL) (cls O hO) x 1 = 0 := by
  have h₁ := congrArg (CechPic.pull (lift b b').left) ((gen_lam_iff hO).1 hu)
  rw [pull_lam, lift_fst, lift_snd, map_zero] at h₁
  have h₂ := lam_mul_left hL hΘ x b b'
  simp only [lam, dcl, _root_.mul_one, _root_.mul_assoc] at h₁ h₂ ⊢
  linear_combination (norm := abel) h₂ - h₁

end Classes

section Family

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L O : LB B.left}

theorem exists_family (hL : L.IsLB) (hO : O.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) {S' : Scheme.{0}} (t : S' ⟶ S) (a : Over.mk t ⟶ B) :
    ∃ (F : LB ((Over.pullback t).obj B).left) (hF : F.IsLB),
      (∃ u : LB.Gen (abelian₂ ((Over.pullback t).obj B) F), u.IsGen) ∧
      ∀ (W : Over S) (π : W.left ⟶ ((Over.pullback t).obj B).left) (x b : W ⟶ B),
        x.left = π ≫ pullback.snd B.hom t ≫ a.left → b.left = π ≫ pullback.fst B.hom t →
        CechPic.pull π (cls F hF) = dcl (cls L hL) (cls O hO) x b := by
  let T₀ : Over S := Over.mk (pullback.snd B.hom t ≫ t)
  let X : T₀ ⟶ B := Over.homMk (pullback.snd B.hom t ≫ a.left) (by
    rw [Category.assoc, Over.w a]; rfl)
  let P : T₀ ⟶ B := Over.homMk (pullback.fst B.hom t) pullback.condition
  obtain ⟨F, hF, e⟩ := cls_surj (dcl (cls L hL) (cls O hO) X P)
  have key : ∀ (W : Over S) (π : W.left ⟶ ((Over.pullback t).obj B).left) (x b : W ⟶ B),
      x.left = π ≫ pullback.snd B.hom t ≫ a.left → b.left = π ≫ pullback.fst B.hom t →
      CechPic.pull π (cls F hF) = dcl (cls L hL) (cls O hO) x b := by
    intro W π x b hx hb
    let h : W ⟶ T₀ := Over.homMk π (by
      rw [← Over.w b, hb, Category.assoc]
      exact congrArg (π ≫ ·) pullback.condition.symm)
    have e₁ : h ≫ X = x := Over.OverMorphism.ext hx.symm
    have e₂ : h ≫ P = b := Over.OverMorphism.ext hb.symm
    exact (congrArg (CechPic.pull π) e).trans ((pull_dcl _ _ h X P).trans (by rw [e₁, e₂]))
  refine ⟨F, hF, ?_, key⟩
  let B' := (Over.pullback t).obj B
  refine (gen_lam_iff (B := B') hF).2 ?_
  let ρ := pushHom (isGrpPullback_pullback B t) (B' ⊗ B')
  let x : Over.mk ((B' ⊗ B').hom ≫ t) ⟶ B := Over.homMk ((B' ⊗ B').hom ≫ a.left) (by
    rw [Category.assoc, Over.w a]; rfl)
  have k : ∀ u : B' ⊗ B' ⟶ B', CechPic.pull u.left (cls F hF) = dcl (cls L hL) (cls O hO) x (ρ u) := fun u =>
    key (Over.mk ((B' ⊗ B').hom ≫ t)) u.left x (ρ u) (by
      rw [← Category.assoc]
      exact congrArg (· ≫ a.left) (Over.w u).symm) rfl
  have z := dcl_primitive hL hO hΘ hu x (ρ (fst B' B')) (ρ (snd B' B'))
  rw [← map_mul ρ, ← map_one ρ, ← k, ← k, ← k, ← k] at z
  exact z

end Family

theorem exists_ideal (hG : GlobalFnsSt) {V : Type} [CommRing V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) {H : Over (Spec (CommRingCat.of V))} (j : H ⟶ B)
    (hH : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x)
    (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (a : Spec (CommRingCat.of A) ⟶ B.left)
    (ϖ : A) (h₁ : ϖ ∈ nonZeroDivisors A) (h₂ : IsRegularLocalRing (A ⧸ Ideal.span {ϖ}))
    (h₃ : ringKrullDim (A ⧸ Ideal.span {ϖ}) = g)
    (K₀ : Type) [Field K₀] (g₀ : A →+* K₀) (hg₀ : IsLocalHom g₀)
    (h₀ : ∃ y : Spec (CommRingCat.of K₀) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom g₀) ≫ a)
    (hE : ∀ (K : Type) [Field K] (φ : A →+* K), φ ϖ = 0 →
      (∃ y : Spec (CommRingCat.of K) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) →
      RingHom.ker φ = IsLocalRing.maximalIdeal A) :
    ∃ I : Ideal A, IsSMulRegular (A ⧸ I) ϖ ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) ↔
        I ≤ RingHom.ker φ := by
  let t := a ≫ B.hom
  obtain ⟨F, hF, hΛ, hcl⟩ := exists_family hL hO hΘ hu t (Over.homMk a rfl)
  let B' := (Over.pullback t).obj B
  have hB' : IsAbelianScheme B' := TLinPf.isAb_pullback t B hB
  have hpb : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
  have hp' : IsProjBy B'.hom := isProjBy_baseChange hp hpb
  have hg' : SmoothOfRelativeDimension g B'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hpb hg
  have test : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ B'.left)
      (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) →
      (Triv (F.pull π) ↔
        ∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) := by
    intro R _ _ φ X' π f' h
    let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ t)
    let x : T ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ a) (Category.assoc _ _ _)
    have hM : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
      LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
    have q : IsPullback f' (π ≫ pullback.fst B.hom t) T.hom B.hom := (h.paste_horiz hpb).flip
    let W : Over (Spec (CommRingCat.of V)) := Over.mk (f' ≫ T.hom)
    let e : W ⟶ T ⊗ B := Over.homMk q.isoPullback.hom (by
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ T.hom = f' ≫ T.hom
      rw [IsPullback.isoPullback_hom_fst_assoc])
    have : IsIso e.left := inferInstanceAs (IsIso q.isoPullback.hom)
    have c₁ : CechPic.pull π (cls F hF) = CechPic.pull e.left (cls _ hM) := by
      rw [cls_eq_dcl hL hO, pull_dcl]
      refine hcl W π _ _ ?_ q.isoPullback_hom_snd
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ a =
        π ≫ B'.hom ≫ a
      rw [IsPullback.isoPullback_hom_fst_assoc, h.w_assoc]
    refine (cls_eq_zero_iff (pull_isLB hF π)).symm.trans ?_
    rw [cls_pull hF, c₁, pull_iso_eq_zero]
    refine ((loc_triv_iff (R := R) (fst T B).left hM).symm.trans (hH T x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (·.left) hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
      rw [← Over.w j, ← Category.assoc, hy]
      exact Category.assoc _ _ _
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj A _ B'.hom hB'.smooth hp' F hF
  have := hB'.proper
  have := hB'.geomConnected
  have q₀ := IsPullback.of_hasPullback B'.hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨I, ⟨eI⟩, hI⟩ := GlobalTheory.UU.SecCyclic.cyclic_ideal A _ B'.hom F hF P inferInstance inferInstance K₀ g₀ hg₀ _ _ _
    q₀ (CubeOpen.bijective_appTop hG B' hB' q₀) ((test K₀ g₀ _ _ _ q₀).2 h₀)
  obtain ⟨C, c₁, c₂, ⟨eC⟩, c₃⟩ := GlobalTheory.T.exists_perfect_free_finite_complex A B' hB' hp' g hg' F hF hΛ P
  refine ⟨I, ?_, fun R _ _ φ => (test R φ _ _ _ (IsPullback.of_hasPullback _ _)).symm.trans
    (hI R φ _ _ _ (IsPullback.of_hasPullback _ _))⟩
  refine ((eC.trans eI).isSMulRegular_congr ϖ).1
    (GlobalTheory.isSMulRegular_coker_dualMap_of_exact_fibres A ϖ g h₁ h₂ h₃ C c₁ c₂ fun p hϖ => ?_)
  let K := AlgebraicClosure p.asIdeal.ResidueField
  let φ : A →+* K := (algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField)
  have hk : RingHom.ker φ = p.asIdeal := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap p.asIdeal.ResidueField K).injective,
      Ideal.ker_algebraMap_residueField]
  refine ⟨K, inferInstance, φ, hk, fun i hi => c₃ K φ _ _ _ (IsPullback.of_hasPullback _ _) i ?_⟩
  rcases hi with hi | hi
  · refine Or.inr fun ht => hi (hk.symm.trans (hE K φ ?_ ((test K φ _ _ _ (IsPullback.of_hasPullback _ _)).1 ht)))
    exact (RingHom.mem_ker).1 (hk.ge hϖ)
  · exact Or.inl hi

theorem isClosed_of_isFinite {V : Type} [CommRing V] [IsLocalRing V] {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of V)) [IsFinite f] (z : H) (hz : f z = IsLocalRing.closedPoint V) :
    IsClosed ({z} : Set H) := by
  have hc : IsClosed (f ⁻¹' {IsLocalRing.closedPoint V}) :=
    (IsLocalRing.isClosed_singleton_closedPoint V).preimage f.continuous
  have hd := (f.isDiscrete_preimage_singleton (IsLocalRing.closedPoint V)).to_subtype
  have := hc.isClosedEmbedding_subtypeVal.isClosedMap {⟨z, hz⟩} (isClosed_discrete _)
  rwa [Set.image_singleton] at this

theorem flat_of_isFinite : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ (L : RigLB B) (_ : CubicalStr B L) (O : LB B.left), O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∀ (H : Over (Spec (CommRingCat.of V))) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L.L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T ⟶ H, y ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  intro hG V _ _ _ B _ _ hB hp L c O hO hu H j hj hH hf
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim V B hB
  rw [← Over.w j]
  refine flat_of_ideals V ϖ hϖ B.left H.left B.hom j.left hj fun h σ hσ hn => ?_
  have cl : ∀ (z : H.left) (p : Spec (B.left.presheaf.stalk (j.left h))), σ ϖ ∈ p.asIdeal →
      j.left z = B.left.fromSpecStalk (j.left h) p → IsClosed ({j.left z} : Set B.left) := by
    intro z p hp e
    have hz : H.hom z = IsLocalRing.closedPoint V := by
      rw [← Over.w j, Scheme.Hom.comp_apply, e, ← Scheme.Hom.comp_apply, hσ]
      refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top ?_))
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
      exact hp
    have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom z hz)
    rwa [Set.image_singleton] at this
  obtain ⟨h₀, h₁, h₂, h₃⟩ := stalk_of_smooth V ϖ hϖ B.left B.hom g hg (j.left h)
    (cl h (IsLocalRing.closedPoint _) hn Scheme.fromSpecStalk_closedPoint.symm) σ hσ hn
  refine @exists_ideal hG V _ B _ _ hB hp g hg L.L O L.isLB hO ⟨c.t, c.isGen⟩ hu H j hH
    (B.left.presheaf.stalk (j.left h)) _ h₀ _
    (B.left.fromSpecStalk (j.left h)) (σ ϖ) h₁ h₂ h₃ (H.left.residueField h) _
    (j.left.stalkMap h ≫ H.left.residue h).hom
    (RingHom.isLocalHom_comp (IsLocalRing.residue (H.left.presheaf.stalk h)) (j.left.stalkMap h).hom) ⟨H.left.fromSpecResidueField h, ?_⟩ ?_
  · rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    rfl
  · rintro K _ φ hφ ⟨y, hy⟩
    let p := Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K)
    have hk : p.asIdeal = RingHom.ker φ := by
      show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K)) = B.left.fromSpecStalk (j.left h) p :=
      congrArg (fun q => q (IsLocalRing.closedPoint K)) hy
    have hc := cl _ p (hk.ge hφ) e
    have hs : B.left.fromSpecStalk (j.left h) p ⤳ j.left h := by
      have : B.left.fromSpecStalk (j.left h) p ∈ Set.range (B.left.fromSpecStalk (j.left h)) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : j.left h = B.left.fromSpecStalk (j.left h) p := (hs.mem_closed hc e.symm).trans e
    have hp' : p = IsLocalRing.closedPoint _ := (B.left.fromSpecStalk (j.left h)).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, hp']
    rfl

end GlobalTheory.StabFlat
