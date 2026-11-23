import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfThickeningPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.AlgGroup

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

section Connected

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := by
  refine ⟨fun U W hU hW hc ⟨u, _, hu⟩ ⟨w, _, hw⟩ => ?_⟩
  by_contra hne
  let O : Bool → Y.Opens := fun i => bif i then ⟨U, hU⟩ else ⟨W, hW⟩
  have hd : O true ⊓ O false = ⊥ := le_bot_iff.1 fun y hy => hne ⟨y, trivial, hy⟩
  have hcov : ⨆ i, O i = ⊤ := top_unique fun y _ => by
    rcases hc (Set.mem_univ y) with h | h
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨true, h⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨false, h⟩
  obtain ⟨s, hs⟩ := TLinPf.glue O hcov (fun i => bif i then 1 else 0) (fun i j => by
    have sub : ∀ T : Y.Opens, T = ⊥ → Subsingleton Γ(Y, T) := fun T hT => by
      subst hT; infer_instance
    cases i <;> cases j
    · exact (map_zero _).trans (map_zero _).symm
    · exact (sub _ ((inf_comm _ _).trans hd)).elim _ _
    · exact (sub _ hd).elim _ _
    · exact (map_one _).trans (map_one _).symm)
  rcases H s with h | h
  · have h₁ : u ∈ Y.basicOpen s := (mem_basicOpen_rs (le_top : O true ≤ ⊤) s hu).1 (by
      rw [show rs Y (le_top : O true ≤ ⊤) s = 1 from hs true]
      exact mem_of_isUnit isUnit_one hu)
    rw [h] at h₁
    exact h₁
  · have h₁ := (mem_basicOpen_rs (le_top : O false ≤ ⊤) s hw).2 (h.ge (Set.mem_univ w))
    rw [show rs Y (le_top : O false ≤ ⊤) s = 0 from hs false, Scheme.basicOpen_zero] at h₁
    exact h₁

theorem surjective_appTop {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed p] :
    Function.Surjective p.appTop.hom := by
  let F := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  algebraize [F.hom]
  have h : Function.Surjective F.hom :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))).2
  intro s
  obtain ⟨c, hc⟩ := h s
  exact ⟨_, hc⟩

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

theorem triv_pull (π : X' ⟶ X) : Triv ((Inh.trivLB X).pull π) :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    erw [Inh.linComb_triv_g, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem preconnectedSpace_of_line {R F : Type} [CommRing R] [Field F]
    {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (Inh.trivLB X)) {g : R →+* F} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of F)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (v : Fin P.a → F) (hv : ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : F, w = c • v) :
    PreconnectedSpace X' := by
  obtain ⟨E, hE⟩ := P.sec F g X' π f' h
  have key : ∀ s : Γ(X', ⊤), ∃ c : F, ∀ i,
      rs X' (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s = AbLaw.cst f' _ c * loc P π f' v i := fun s => by
    obtain ⟨w, hw⟩ := E.surjective (fnSec π s)
    obtain ⟨c, hc⟩ := hv w.1 w.2
    refine ⟨c, fun i => ?_⟩
    have e := hE w i
    rw [hw] at e
    refine ((rs_rs _ _ s).symm.trans e).trans ?_
    rw [← loc_smul, ← hc]
    rfl
  obtain ⟨c₁, h₁⟩ := key 1
  have hu : ∀ i, IsUnit (loc P π f' v i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [← h₁ i, map_one]; exact isUnit_one)
  refine preconnectedSpace_of_functions X' fun s => ?_
  obtain ⟨c, hc⟩ := key s
  by_cases h0 : c = 0
  · refine Or.inl (le_bot_iff.1 fun y hy => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have := (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).2 hy
    rwa [hc, h0, map_zero, zero_mul, Scheme.basicOpen_zero] at this
  · refine Or.inr (top_unique fun y _ => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    refine (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).1 ?_
    rw [hc]
    exact mem_of_isUnit (((IsUnit.mk0 c h0).map _).mul (hu i)) hi

end Connected

theorem map_lift {κ G H : Type} [Group G] [Group H] (φ : G →* H) (x : κ → G) (w : FreeGroup κ) :
    φ (FreeGroup.lift x w) = FreeGroup.lift (fun i => φ (x i)) w := by
  have : φ.comp (FreeGroup.lift x) = FreeGroup.lift (fun i => φ (x i)) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  exact DFunLike.congr_fun this w

theorem geometricallyConnected_of_quotient (V : Type) [CommRing V] [IsLocalRing V] (J : Ideal V) (hJ : J ≠ ⊤)
    (B : Over (Spec (CommRingCat.of V))) (hs : Smooth B.hom) (hp : IsProjBy B.hom)
    (Y₀ : Over (Spec (CommRingCat.of (V ⧸ J)))) (b : Y₀.left ⟶ B.left)
    (hb : IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (hc : GeometricallyConnected Y₀.hom) : GeometricallyConnected B.hom := by
  obtain ⟨P⟩ := nonempty_perf_of_smooth_isProjBy V B.left B.hom hs hp _ (Inh.trivLB_isLB _)
  have hpr : IsProper B.hom := isProper_of_isProjBy V B.left B.hom hp
  let L := AlgebraicClosure (IsLocalRing.ResidueField V)
  let g₀ : V →+* L := (algebraMap (IsLocalRing.ResidueField V) L).comp (IsLocalRing.residue V)
  have hg₀ : ∀ a, g₀ a = 0 ↔ a ∈ IsLocalRing.maximalIdeal V := fun a =>
    (map_eq_zero (algebraMap (IsLocalRing.ResidueField V) L)).trans (IsLocalRing.residue_eq_zero_iff a)
  let q : V ⧸ J →+* L :=
    Ideal.Quotient.lift _ g₀ fun a ha => (hg₀ a).2 (IsLocalRing.le_maximalIdeal hJ ha)
  let y₀ : Spec (CommRingCat.of L) ⟶ _ := Spec.map (CommRingCat.ofHom q)
  have h₀ : IsPullback (pullback.fst Y₀.hom y₀ ≫ b) (pullback.snd Y₀.hom y₀) B.hom
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback Y₀.hom y₀).paste_horiz hb
    rwa [← Spec.map_comp] at this
  have hs₀ : Smooth Y₀.hom := MorphismProperty.of_isPullback hb hs
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ Y₀.hom hs₀ hc
  have hint : IsIntegral (pullback Y₀.hom y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback Y₀.hom y₀)
  have hpr₀ : IsProper (pullback.snd Y₀.hom y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback Y₀.hom y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst Y₀.hom y₀ ≫ b) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  have hδ' : IsUnit δ := by
    by_contra hn
    exact hδ ((hg₀ δ).2 hn)
  have hsurj : Surjective B.hom := by
    let O : (Spec (CommRingCat.of V)).Opens := ⟨Set.range B.hom, B.hom.isOpenMap.isOpen_range⟩
    have hO : O = ⊤ := by
      refine (IsLocalRing.closedPoint_mem_iff O).1 ⟨(pullback.fst Y₀.hom y₀ ≫ b) x₀, ?_⟩
      have e : B.hom ((pullback.fst Y₀.hom y₀ ≫ b) x₀) =
          Spec.map (CommRingCat.ofHom g₀) (pullback.snd Y₀.hom y₀ x₀) := congrArg (fun t => t x₀) h₀.w
      refine e.trans (PrimeSpectrum.ext ?_)
      refine ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le (PrimeSpectrum.isPrime _).ne_top
        fun a ha => ?_).symm
      change g₀ a ∈ (pullback.snd Y₀.hom y₀ x₀).asIdeal
      rw [(hg₀ a).2 ha]
      exact zero_mem _
    exact ⟨fun z => hO.ge (Set.mem_univ z)⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Z fst snd h => ?_⟩
  have : Surjective snd := MorphismProperty.of_isPullback h hsurj
  obtain ⟨z, -⟩ := snd.surjective (⊥ : PrimeSpectrum F)
  have := preconnectedSpace_of_line P h _ (hker F _ (hδ'.map _))
  exact ⟨⟨z⟩⟩

theorem comp_word {κ : Type} {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (U : T' ⟶ T) (x : κ → (T ⟶ G))
    (x' : κ → (T' ⟶ G)) (hx : ∀ i, U ≫ x i = x' i) (w : FreeGroup κ) :
    U.left ≫ (FreeGroup.lift x w).left = (FreeGroup.lift x' w).left := by
  have h : preHom U (FreeGroup.lift x w) = FreeGroup.lift x' w := by
    rw [map_lift]
    exact congrArg (fun z => FreeGroup.lift z w) (funext hx)
  generalize FreeGroup.lift x w = a at h
  generalize FreeGroup.lift x' w = a' at h
  subst h
  rfl

theorem push_word {κ : Type} {S S' : Scheme.{0}} {G T : Over S} {G' T' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (U : Over.mk (T'.hom ≫ f) ⟶ T)
    (x : κ → (T ⟶ G)) (x' : κ → (T' ⟶ G')) (hx : ∀ i, U.left ≫ (x i).left = (x' i).left ≫ φ)
    (w : FreeGroup κ) : U.left ≫ (FreeGroup.lift x w).left = (FreeGroup.lift x' w).left ≫ φ := by
  rw [comp_word U x (fun i => pushHom h T' (x' i)) (fun i => Over.OverMorphism.ext (hx i)), ← map_lift]
  generalize FreeGroup.lift x' w = a'
  rfl

variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {B : Over (Spec (CommRingCat.of R))}
  {b : ∀ e, (Y e).left ⟶ B.left}

theorem exists_point (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) (e : ℕ)
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x₀ : Over.mk (T.hom ≫ thick R I e) ⟶ B) :
    ∃ x : T ⟶ Y e, x₀.left = x.left ≫ b e :=
  ⟨Over.homMk ((hb e).lift x₀.left T.hom (Over.w x₀)) ((hb e).lift_snd _ _ _),
    ((hb e).lift_fst _ _ _).symm⟩

theorem exists_hom [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (hM : MorAlgSt) (hI : I ≠ ⊤)
    (hc : IsAdicComplete I R) (hc' : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} (hB : IsProjBy B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    (Z : Over (Spec (CommRingCat.of R))) (hZ : IsProjBy Z.hom) (hZs : Smooth Z.hom)
    (φ : ∀ e, thickObj R I e Z ⟶ Y e) (hφ : ∀ e, thickMap R I e Z ≫ (φ (e + 1)).left = (φ e).left ≫ β e) :
    ∃ g : Z ⟶ B, ∀ e, pullback.fst Z.hom (thick R I e) ≫ g.left = (φ e).left ≫ b e := by
  obtain ⟨g, hg, -⟩ := hM R I hI hc hc' Z B hZ hB hZs (fun e => (φ e).left ≫ b e)
    (fun e => by
      rw [Category.assoc, (hb e).w, Over.w_assoc]
      exact pullback.condition.symm)
    (fun e => by rw [← Category.assoc, hφ, Category.assoc, hβb])
  exact ⟨g, hg⟩

theorem word_compat {κ : Type} {S S₁ S₂ : Scheme.{0}} {B Z : Over S} {G₁ T₁ : Over S₁} {G₂ T₂ : Over S₂}
    [GrpObj G₁] [GrpObj G₂] {f₂ : S₂ ⟶ S} {t : S₁ ⟶ S₂} {β : G₁.left ⟶ G₂.left}
    (hβ : IsGrpPullback G₁ G₂ t β) {b₂ : G₂.left ⟶ B.left} {b₁ : G₁.left ⟶ B.left}
    (hb : IsPullback b₂ G₂.hom B.hom f₂) (hβb : β ≫ b₂ = b₁) {π₁ : T₁.left ⟶ Z.left} {π₂ : T₂.left ⟶ Z.left}
    {m : T₁.left ⟶ T₂.left} (h₁ : m ≫ π₂ = π₁) (h₂ : m ≫ T₂.hom = T₁.hom ≫ t) (p : κ → (Z ⟶ B))
    (x₁ : κ → (T₁ ⟶ G₁)) (x₂ : κ → (T₂ ⟶ G₂)) (hx₁ : ∀ i, π₁ ≫ (p i).left = (x₁ i).left ≫ b₁)
    (hx₂ : ∀ i, π₂ ≫ (p i).left = (x₂ i).left ≫ b₂) (w : FreeGroup κ) :
    m ≫ (FreeGroup.lift x₂ w).left = (FreeGroup.lift x₁ w).left ≫ β := by
  refine push_word hβ (Over.homMk m h₂) _ _ (fun i => hb.hom_ext ?_ ?_) w
  · change (m ≫ (x₂ i).left) ≫ b₂ = ((x₁ i).left ≫ β) ≫ b₂
    rw [Category.assoc, Category.assoc, hβb, ← hx₁, ← hx₂, ← h₁, Category.assoc]
  · rw [Category.assoc, Category.assoc, hβ.1.w, Over.w, Over.w, Over.w_assoc]
    rfl

theorem word_points {κ : Type} {S S₁ : Scheme.{0}} {B Z : Over S} {G₁ T₁ : Over S₁} [GrpObj G₁] {f : S₁ ⟶ S}
    {b₁ : G₁.left ⟶ B.left} (hb : IsPullback b₁ G₁.hom B.hom f) {π : T₁.left ⟶ Z.left}
    (hπ : IsPullback π T₁.hom Z.hom f) (p : κ → (Z ⟶ B)) (X : κ → (T₁ ⟶ G₁))
    (hX : ∀ i, π ≫ (p i).left = (X i).left ≫ b₁) (w : FreeGroup κ) (g : Z ⟶ B)
    (hg : π ≫ g.left = (FreeGroup.lift X w).left ≫ b₁) (T : Over S₁) (k : Over.mk (T.hom ≫ f) ⟶ Z)
    (x : κ → (T ⟶ G₁)) (hx : ∀ i, (k ≫ p i).left = (x i).left ≫ b₁) :
    (k ≫ g).left = (FreeGroup.lift x w).left ≫ b₁ := by
  let k' : T ⟶ T₁ := Over.homMk (hπ.lift k.left T.hom (Over.w k)) (hπ.lift_snd _ _ _)
  have hk : k'.left ≫ π = k.left := hπ.lift_fst _ _ _
  have h₁ : ∀ i, k' ≫ X i = x i := fun i => by
    refine Over.OverMorphism.ext (hb.hom_ext ?_ ?_)
    · rw [Over.comp_left, Category.assoc, ← hX, ← Category.assoc, hk, ← hx, Over.comp_left]
    · rw [Over.w, Over.w]
  rw [← comp_word k' _ _ h₁, Over.comp_left, ← hk, Category.assoc, Category.assoc, hg]

theorem exists_word [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (hM : MorAlgSt) (hI : I ≠ ⊤)
    (hc : IsAdicComplete I R) (hc' : IsAdicComplete (IsLocalRing.maximalIdeal R) R) [∀ e, GrpObj (Y e)]
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left}
    (hβ : ∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e)) (hB : IsProjBy B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    {κ : Type} (w : FreeGroup κ) (Z : Over (Spec (CommRingCat.of R))) (hZ : IsProjBy Z.hom)
    (hZs : Smooth Z.hom) (p : κ → (Z ⟶ B)) :
    ∃ g : Z ⟶ B, ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (k : Over.mk (T.hom ≫ thick R I e) ⟶ Z) (x : κ → (T ⟶ Y e)),
      (∀ i, (k ≫ p i).left = (x i).left ≫ b e) → (k ≫ g).left = (FreeGroup.lift x w).left ≫ b e := by
  have ex : ∀ e i, ∃ x : thickObj R I e Z ⟶ Y e,
      pullback.fst Z.hom (thick R I e) ≫ (p i).left = x.left ≫ b e := fun e i =>
    ⟨Over.homMk ((hb e).lift (pullback.fst Z.hom (thick R I e) ≫ (p i).left) (pullback.snd _ _)
      (by rw [Category.assoc, Over.w, pullback.condition])) ((hb e).lift_snd _ _ _),
      ((hb e).lift_fst _ _ _).symm⟩
  choose X hX using ex
  obtain ⟨g, hg⟩ := exists_hom hM hI hc hc' hB hb hβb Z hZ hZs (fun e => FreeGroup.lift (X e) w) fun e =>
    word_compat (hβ e) (hb (e + 1)) (hβb e) ((pullback.lift_fst _ _ _).trans (Category.comp_id _))
      (pullback.lift_snd _ _ _) p (X e) (X (e + 1)) (hX e) (hX (e + 1)) w
  exact ⟨g, fun e T k x hx =>
    word_points (hb e) (IsPullback.of_hasPullback _ _) p (X e) (hX e) w g (hg e) T k x hx⟩

theorem hom_eq_of_points [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (hI : I ≠ ⊤)
    {Z : Over (Spec (CommRingCat.of R))} (hZ : IsProper Z.hom) [IsProper B.hom] {f g : Z ⟶ B}
    (h : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (k : Over.mk (T.hom ≫ thick R I e) ⟶ Z), (k ≫ f).left = (k ≫ g).left) : f = g := by
  refine hom_eq_of_thickenings_of_isProper R I
    ((IsLocalRing.le_maximalIdeal hI).trans (IsLocalRing.maximalIdeal_le_jacobson _)) Z B f g fun e ↦ ?_
  exact h e (thickObj R _ e Z) (Over.homMk (pullback.fst Z.hom (thick R _ e)) pullback.condition)

theorem exists_grpObj [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (hI : I ≠ ⊤) [∀ e, GrpObj (Y e)]
    (hc : ∀ e, IsCommMonObj (Y e)) (hB : IsProper B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e))
    (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B)
    (hm : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y : T ⟶ Y e)
      (x₀ y₀ : Over.mk (T.hom ≫ thick R I e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e →
      (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e)
    (hi : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : T ⟶ Y e)
      (x₀ : Over.mk (T.hom ≫ thick R I e) ⟶ B), x₀.left = x.left ≫ b e →
      (x₀ ≫ io).left = (x⁻¹).left ≫ b e)
    (hu : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))),
      (toUnit (Over.mk (T.hom ≫ thick R I e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) :
    ∃ _ : GrpObj B, IsCommMonObj B ∧ ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e) := by
  have ex := exists_point hb
  have h2 := isProper_tensorObj_over hB hB
  have h3 := isProper_tensorObj_over h2 hB
  have one_mul' : lift (toUnit B ≫ un) (𝟙 B) ≫ mu = 𝟙 B := by
    refine hom_eq_of_points hI hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T 1 x _ _ (hu e T) hx, _root_.one_mul, hx]
  have mul_one' : lift (𝟙 B) (toUnit B ≫ un) ≫ mu = 𝟙 B := by
    refine hom_eq_of_points hI hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T x 1 _ _ hx (hu e T), _root_.mul_one, hx]
  have linv : lift io (𝟙 B) ≫ mu = toUnit B ≫ un := by
    refine hom_eq_of_points hI hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T _ x _ _ (hi e T x k hx) hx, inv_mul_cancel, hu e T]
  have rinv : lift (𝟙 B) io ≫ mu = toUnit B ≫ un := by
    refine hom_eq_of_points hI hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T x _ _ _ hx (hi e T x k hx), mul_inv_cancel, hu e T]
  have assoc' : (mu ▷ B) ≫ mu = (α_ B B B).hom ≫ (B ◁ mu) ≫ mu := by
    refine hom_eq_of_points hI h3 fun e T k ↦ ?_
    obtain ⟨p, q, r, rfl⟩ : ∃ p q r, k = lift (lift p q) r :=
      ⟨k ≫ fst _ _ ≫ fst _ _, k ≫ fst _ _ ≫ snd _ _, k ≫ snd _ _, by ext1 <;> [ext1; skip] <;> simp⟩
    obtain ⟨x, hx⟩ := ex e T p
    obtain ⟨y, hy⟩ := ex e T q
    obtain ⟨z, hz⟩ := ex e T r
    rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
      hm e T _ z _ _ (hm e T x y _ _ hx hy) hz, hm e T x _ _ _ hx (hm e T y z _ _ hy hz),
      _root_.mul_assoc]
  let G : GrpObj B :=
    { one := un
      mul := mu
      inv := io
      one_mul := by
        rw [← cancel_epi (λ_ B).inv, Iso.inv_hom_id, ← one_mul', ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_one := by
        rw [← cancel_epi (ρ_ B).inv, Iso.inv_hom_id, ← mul_one', ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_assoc := assoc'
      left_inv := linv
      right_inv := rinv }
  refine ⟨G, ⟨?_⟩, fun e ↦ ⟨hb e, fun T x y x₀ y₀ hx hy ↦ hm e T x y x₀ y₀ hx hy⟩⟩
  change (β_ B B).hom ≫ mu = mu
  refine hom_eq_of_points hI h2 fun e T k ↦ ?_
  obtain ⟨p, q, rfl⟩ : ∃ p q, k = lift p q := ⟨k ≫ fst _ _, k ≫ snd _ _, by ext1 <;> simp⟩
  obtain ⟨x, hx⟩ := ex e T p
  obtain ⟨y, hy⟩ := ex e T q
  have := hc e
  rw [lift_braiding_hom_assoc, hm e T x y _ _ hx hy, hm e T y x _ _ hy hx, _root_.mul_comm]

theorem isAbelianScheme_of_thickenings : Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsAbelianScheme (Y e)) → (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), GlobalTheory.AbLaw.IsProjBy B.hom → Smooth B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ _ : GrpObj B, IsAbelianScheme B ∧ ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e) := by
  intro hE R _ _ _ I hA Y _ β hY hβ B b hB hs hb hβb
  obtain ⟨⟨hN, -, -, hc⟩, hc', -, hP, -⟩ := hA
  have hI : I ≠ ⊤ := hP.ne_top
  have hpr : IsProper B.hom := isProper_of_isProjBy R B.left B.hom hB
  have hs₂ : Smooth (B ⊗ B).hom := by
    change Smooth (pullback.fst B.hom B.hom ≫ B.hom)
    infer_instance
  obtain ⟨mu, hm⟩ := exists_word hE.2.1 hI hc hc' hβ hB hb hβb
    (FreeGroup.of true * FreeGroup.of false) (B ⊗ B) (isProjBy_tensor R B B hB hB) hs₂
    (fun i => bif i then fst B B else snd B B)
  obtain ⟨io, hi⟩ := exists_word hE.2.1 hI hc hc' hβ hB hb hβb
    (FreeGroup.of ())⁻¹ B hB hs (fun _ => 𝟙 B)
  obtain ⟨un, hu⟩ := exists_word hE.2.1 hI hc hc' hβ hB hb hβb
    (1 : FreeGroup Empty) (𝟙_ _) (isProjBy_id R) (inferInstanceAs (Smooth (𝟙 _))) Empty.elim
  obtain ⟨G, hG, hG'⟩ := exists_grpObj hI (fun e => (hY e).comm) hpr hb mu io un
    (fun e T x y x₀ y₀ hx hy => by
      have := hm e T (lift x₀ y₀) (fun i => bif i then x else y) (fun i => by
        cases i
        · simpa using hy
        · simpa using hx)
      rwa [map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of] at this)
    (fun e T x x₀ hx => by
      have := hi e T x₀ (fun _ => x) (fun _ => by rwa [Category.comp_id])
      rwa [map_inv, FreeGroup.lift_apply_of] at this)
    (fun e T => by
      have := hu e T (toUnit _) Empty.elim (fun i => i.elim)
      rwa [map_one] at this)
  refine ⟨G, ⟨hG, hs, hpr, ?_⟩, hG'⟩
  exact geometricallyConnected_of_quotient R (I ^ (0 + 1)) (by simpa using hI) B hs hB (Y 0) (b 0) (hb 0)
    (hY 0).geomConnected

end GlobalTheory.AlgGroup
end
