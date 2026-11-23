import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.EigenLatticeRankLie

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace GlobalTheory.LieLatCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeRankLie
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (OAct Host Datum SAB SABMap DetCond LieMult IsLieEigen epsPt epsScale Sp)

attribute [local instance] Over.cartesianMonoidalCategory

section Lattice

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}

section SqZero

variable {M : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

theorem ker_fst_sq : (RingHom.ker (TrivSqZeroExt.fstHom R R M)) ^ (1 + 1) = ⊥ := by
  rw [← le_bot_iff, pow_two, Ideal.mul_le]
  intro a ha b hb
  have ha0 : a.fst = 0 := ha
  have hb0 : b.fst = 0 := hb
  rw [Ideal.mem_bot, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha0 rfl,
    show b = TrivSqZeroExt.inr b.snd from TrivSqZeroExt.ext hb0 rfl, TrivSqZeroExt.inr_mul_inr]

def modLift (c : Fin n → M) : JetR R (Fin n) 1 →ₐ[R] TrivSqZeroExt R M :=
  jetLift R (RingHom.ker (TrivSqZeroExt.fstHom R R M)) ker_fst_sq (fun j => TrivSqZeroExt.inr (c j))
    (fun j => TrivSqZeroExt.fst_inr R (c j))

theorem modLift_zR (c : Fin n → M) (j : Fin n) : modLift (R := R) c (zR 1 j) = TrivSqZeroExt.inr (c j) :=
  jetLift_zR _ _ _ _ j

theorem fst_comp_modLift (c : Fin n → M) :
    (TrivSqZeroExt.fstHom R R M).comp (modLift c) = jetAug R (Fin n) 1 :=
  jet_ext fun j => by rw [AlgHom.comp_apply, modLift_zR, jetAug_zR]; exact TrivSqZeroExt.fst_inr R (c j)

theorem fst_modPt (hx : IsUnivChart G n x) (c : Fin n → M) :
    spMap (TrivSqZeroExt.fstHom R R M) ≫ spMap (modLift (R := R) c) ≫ x 1 = 1 := by
  have t : spMap (TrivSqZeroExt.fstHom R R M) ≫ spMap (modLift (R := R) c) =
      spMap ((TrivSqZeroExt.fstHom R R M).comp (modLift c)) := spMap_comp _ _
  rw [← Category.assoc, t, fst_comp_modLift, spMap_jetAug_alt hx]

theorem univ_mod (hx : IsUnivChart G n x) (y : sp (R₀ := R) (TrivSqZeroExt R M) ⟶ G)
    (hy : spMap (TrivSqZeroExt.fstHom R R M) ≫ y = 1) :
    ∃! ψ : JetR R (Fin n) 1 →ₐ[R] TrivSqZeroExt R M,
      (TrivSqZeroExt.fstHom R R M).comp ψ = jetAug R (Fin n) 1 ∧ y = spMap ψ ≫ x 1 :=
  hx.2.2 (TrivSqZeroExt R M) (TrivSqZeroExt.fstHom R R M) 1 ker_fst_sq y hy

theorem modPt_inj (hx : IsUnivChart G n x) {c c' : Fin n → M}
    (h : spMap (modLift (R := R) c) ≫ x 1 = spMap (modLift c') ≫ x 1) : c = c' := by
  have h0 := fst_modPt hx c
  have e := (univ_mod hx _ h0).unique (y₁ := modLift c) (y₂ := modLift c') ⟨fst_comp_modLift c, rfl⟩
    ⟨fst_comp_modLift c', h⟩
  funext j
  have := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun e (zR 1 j))
  rwa [modLift_zR, modLift_zR, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_inr] at this

theorem map_modPt {N : Type} [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N] (l : M →ₗ[R] N)
    (c : Fin n → M) : spMap (TrivSqZeroExt.map l) ≫ spMap (modLift (R := R) c) ≫ x 1 =
      spMap (modLift (l ∘ c)) ≫ x 1 := by
  rw [← Category.assoc, spMap_comp]
  congr 2
  exact jet_ext fun j => by rw [AlgHom.comp_apply, modLift_zR, modLift_zR, TrivSqZeroExt.map_inr]; rfl

theorem modPt_zero (hx : IsUnivChart G n x) : spMap (modLift (R := R) (0 : Fin n → M)) ≫ x 1 = 1 := by
  have : modLift (R := R) (0 : Fin n → M) = (Algebra.ofId R _).comp (jetAug R (Fin n) 1) :=
    jet_ext fun j => by
      rw [modLift_zR, AlgHom.comp_apply, jetAug_zR, map_zero, Pi.zero_apply, TrivSqZeroExt.inr_zero]
  rw [this, ← spMap_comp, Category.assoc, spMap_jetAug_alt hx, comp_one']

theorem modPt_add (hx : IsUnivChart G n x) (c c' : Fin n → M) :
    spMap (modLift (R := R) (c + c')) ≫ x 1 = (spMap (modLift c) ≫ x 1) * (spMap (modLift c') ≫ x 1) := by
  let P : sp (R₀ := R) (TrivSqZeroExt R (M × M)) ⟶ G :=
    (spMap (modLift (LinearMap.inl R M M ∘ c)) ≫ x 1) * (spMap (modLift (LinearMap.inr R M M ∘ c')) ≫ x 1)
  have hP : spMap (TrivSqZeroExt.fstHom R R (M × M)) ≫ P = 1 := by
    refine (MonObj.comp_mul _ _ _).trans ?_
    rw [fst_modPt hx, fst_modPt hx, _root_.mul_one]
  obtain ⟨ψ, ⟨h1, h2⟩, -⟩ := univ_mod hx P hP
  obtain ⟨a, rfl⟩ : ∃ a : Fin n → M × M, ψ = modLift a :=
    ⟨fun j => (ψ (zR 1 j)).snd, jet_ext fun j => by
      rw [modLift_zR]
      refine TrivSqZeroExt.ext ?_ rfl
      have := AlgHom.congr_fun h1 (zR 1 j)
      rw [AlgHom.comp_apply, jetAug_zR] at this
      exact this⟩
  have key : ∀ l : M × M →ₗ[R] M, spMap (modLift (l ∘ a)) ≫ x 1 =
      (spMap (modLift (l ∘ LinearMap.inl R M M ∘ c)) ≫ x 1) *
        (spMap (modLift (l ∘ LinearMap.inr R M M ∘ c')) ≫ x 1) := fun l => by
    rw [← map_modPt, ← h2, MonObj.comp_mul, map_modPt, map_modPt]
  have k1 := key (LinearMap.fst R M M)
  have k2 := key (LinearMap.snd R M M)
  have k3 := key (LinearMap.fst R M M + LinearMap.snd R M M)
  rw [show (LinearMap.fst R M M) ∘ LinearMap.inr R M M ∘ c' = 0 from rfl, modPt_zero hx, _root_.mul_one] at k1
  rw [show (LinearMap.snd R M M) ∘ LinearMap.inl R M M ∘ c = 0 from rfl, modPt_zero hx, _root_.one_mul] at k2
  have e1 := modPt_inj hx k1
  have e2 := modPt_inj hx k2
  have f1 : (LinearMap.fst R M M + LinearMap.snd R M M) ∘ LinearMap.inl R M M ∘ c = c := by funext j; simp
  have f2 : (LinearMap.fst R M M + LinearMap.snd R M M) ∘ LinearMap.inr R M M ∘ c' = c' := by funext j; simp
  have f3 : (LinearMap.fst R M M + LinearMap.snd R M M) ∘ a = c + c' := by
    funext j
    exact congrArg₂ (· + ·) (congrFun e1 j) (congrFun e2 j)
  rwa [f1, f2, f3] at k3

end SqZero

variable {S : Type} [CommRing S] [Algebra R S]

theorem dualLiftOver_zR (c : Fin n → S) (j : Fin n) :
    dualLiftOver (R := R) c (zR 1 j) = TrivSqZeroExt.inr (c j) := jetLift_zR _ _ _ _ j

theorem tvecOver_add (hx : IsUnivChart G n x) (c c' : Fin n → S) :
    tvecOver x (c + c') = tvecOver x c * tvecOver x c' := by
  let _ : Module Rᵐᵒᵖ S := Module.compHom S ((RingHom.id R).fromOpposite mul_comm)
  have _ : IsCentralScalar R S := ⟨fun _ _ => rfl⟩
  let g : TrivSqZeroExt R S →ₐ[R] DualNumber S := TrivSqZeroExt.liftEquivOfComm
    ⟨(TrivSqZeroExt.inrHom S S).restrictScalars R, fun a b => TrivSqZeroExt.inr_mul_inr S a b⟩
  have h : ∀ c : Fin n → S, tvecOver x c = spMap g ≫ spMap (modLift (R := R) c) ≫ x 1 := fun c => by
    rw [← Category.assoc, spMap_comp, tvecOver]
    congr 2
    exact jet_ext fun j => by
      rw [AlgHom.comp_apply, modLift_zR, dualLiftOver_zR]
      simp [g, TrivSqZeroExt.liftEquivOfComm]
  rw [h, h, h, modPt_add hx, MonObj.comp_mul]

theorem tvecOver_smul (s : S) (c : Fin n → S) :
    tvecOver x (s • c) = spMap (scaleOver R s) ≫ tvecOver x c := by
  rw [tvecOver, tvecOver, ← Category.assoc, spMap_comp]
  congr 2
  exact jet_ext fun j => by
    rw [AlgHom.comp_apply, dualLiftOver_zR, dualLiftOver_zR]
    exact (TrivSqZeroExt.map_inr (s • LinearMap.id : S →ₗ[S] S) (c j)).symm

variable (R S) in

def dualAlg : DualNumber R →ₐ[R] DualNumber S :=
  { dualMapR (algebraMap R S) with
    commutes' := fun r => by ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl'] }

theorem dualAlg_tvec (c : Fin n → R) :
    spMap (dualAlg R S) ≫ tvec (x := x) c = tvecOver x (algebraMap R S ∘ c) := by
  rw [tvec, tvecOver, ← Category.assoc, spMap_comp]
  congr 2
  exact jet_ext fun j => by
    rw [AlgHom.comp_apply, dualLift_zR, dualLiftOver_zR]
    ext <;> simp [dualAlg, dualMapR]

theorem dualMapR_tvec (c : Fin n → R) :
    Spec.map (CommRingCat.ofHom (dualMapR (algebraMap R S))) ≫ (tvec (x := x) c).left =
      (tvecOver x (algebraMap R S ∘ c)).left :=
  congrArg (fun q : sp (R₀ := R) (DualNumber S) ⟶ G => q.left) (dualAlg_tvec (x := x) c)

theorem family_ext {F F' : (Fin n → S) → (sp (R₀ := R) (DualNumber S) ⟶ G)}
    (a : ∀ c c', F (c + c') = F c * F c') (a' : ∀ c c', F' (c + c') = F' c * F' c')
    (s : ∀ (r : S) c, F (r • c) = spMap (scaleOver R r) ≫ F c)
    (s' : ∀ (r : S) c, F' (r • c) = spMap (scaleOver R r) ≫ F' c)
    (h : ∀ c : Fin n → R, F (algebraMap R S ∘ c) = F' (algebraMap R S ∘ c)) (c : Fin n → S) : F c = F' c := by
  classical
  have h0 : F 0 = F' 0 := by
    have := h 0
    rwa [show algebraMap R S ∘ (0 : Fin n → R) = 0 from funext fun _ => map_zero _] at this
  induction c using Pi.single_induction with
  | zero => exact h0
  | add c c' hc hc' => rw [a, a', hc, hc']
  | single i r =>
    have e : (Pi.single i r : Fin n → S) = r • (algebraMap R S ∘ (Pi.single i 1 : Fin n → R)) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    rw [e, s, s', h]

theorem extendLin_comp (T : (Fin n → R) →ₗ[R] (Fin n → R)) (c : Fin n → R) :
    extendLin S T (algebraMap R S ∘ c) = algebraMap R S ∘ T c := by
  funext i
  rw [extendLin, Matrix.toLin'_apply, ← RingHom.map_mulVec, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

end Lattice

section Tangent

def ChartBC {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G) : Prop :=
  ∃ x' : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj G,
    IsUnivChart _ n x' ∧ ∀ c : Fin n → R,
      (tvec (x := x') (φ ∘ c)).left ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (dualMapR φ)) ≫ (tvec (x := x) c).left

def IsTangentChart {R : Type} [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G) : Prop :=
  (∀ c, IsTan (tvec (x := x) c)) ∧ (∀ w, IsTan w → ∃! c, w = tvec (x := x) c) ∧
    ∀ c c', tvec (x := x) (c + c') = tvec (x := x) c * tvec (x := x) c'

def ChartBCOne {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G) : Prop :=
  ∃ x' : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj G,
    IsTangentChart _ n x' ∧ ∀ c : Fin n → R,
      (tvec (x := x') (φ ∘ c)).left ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (dualMapR φ)) ≫ (tvec (x := x) c).left

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}

def CoordBC (hx : IsUnivChart G n x) (S : Type) [CommRing S] [Algebra R S] : Prop :=
  (∀ c : Fin n → S, spMap (fstOver R S) ≫ tvecOver x c = 1) ∧
  (∀ w : sp (R₀ := R) (DualNumber S) ⟶ G, spMap (fstOver R S) ≫ w = 1 → ∃! c : Fin n → S, w = tvecOver x c) ∧
  (∀ c c' : Fin n → S, tvecOver x (c + c') = tvecOver x c * tvecOver x c') ∧
  (∀ (s : S) (c : Fin n → S), tvecOver x (s • c) = spMap (scaleOver R s) ≫ tvecOver x c) ∧
  ∀ (f : G ⟶ G) [IsMonHom f] (c : Fin n → S), tvecOver x c ≫ f = tvecOver x (extendLin S (tmap hx f) c)

theorem isTangentChart_of_isUnivChart (hx : IsUnivChart G n x) : IsTangentChart G n x :=
  ⟨isTan_tvec hx, exists_coord hx, tvec_add hx⟩

theorem chartBCOne_of_chartBC {S : Type} [CommRing S] {φ : R →+* S} (h : ChartBC φ G n x) : ChartBCOne φ G n x :=
  h.imp fun _ h => ⟨isTangentChart_of_isUnivChart h.1, h.2⟩

variable {S : Type} [CommRing S] [Algebra R S]

variable (G S) in
theorem exists_push (P : Type) [CommRing P] [Algebra S P] [Algebra R P] [IsScalarTower R S P] :
    ∃ e : (sp (R₀ := S) P ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj G) ≃*
        (sp (R₀ := R) P ⟶ G), ∀ y, (e y).left = y.left ≫ pullback.fst _ _ :=
  exists_mulEquiv_of_isGrpPullback (Geo.Tor.isGrpPullback_pullback G _) _ _ (by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

variable (G S) in

def push (P : Type) [CommRing P] [Algebra S P] [Algebra R P] [IsScalarTower R S P] :
    (sp (R₀ := S) P ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj G) ≃*
      (sp (R₀ := R) P ⟶ G) := (exists_push G S P).choose

theorem push_left {P : Type} [CommRing P] [Algebra S P] [Algebra R P] [IsScalarTower R S P] (y) :
    (push G S P y).left = y.left ≫ pullback.fst _ _ := (exists_push G S P).choose_spec y

theorem push_spMap {P P' : Type} [CommRing P] [Algebra S P] [Algebra R P] [IsScalarTower R S P]
    [CommRing P'] [Algebra S P'] [Algebra R P'] [IsScalarTower R S P'] (g : P →ₐ[S] P') (y) :
    push G S P' (spMap g ≫ y) = spMap (g.restrictScalars R) ≫ push G S P y := by
  apply Over.OverMorphism.ext
  rw [push_left, Over.comp_left, Over.comp_left, push_left, Category.assoc]
  rfl

theorem isTan_iff_push (w) : IsTan w ↔ spMap (fstOver R S) ≫ push G S (DualNumber S) w = 1 := by
  rw [IsTan, ← push_spMap, map_eq_one_iff _ (push G S S).injective]

theorem tvecOver_comp (hx : IsUnivChart G n x) (f : G ⟶ G) [IsMonHom f] (c : Fin n → S) :
    tvecOver x c ≫ f = tvecOver x (extendLin S (tmap hx f) c) := by
  refine family_ext (F := fun c => tvecOver x c ≫ f) (F' := fun c => tvecOver x (extendLin S (tmap hx f) c))
    (fun c c' => ?_) (fun c c' => ?_) (fun r c => ?_) (fun r c => ?_) (fun c => ?_) c
  · rw [tvecOver_add hx, Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]
  · rw [map_add, tvecOver_add hx]
  · rw [tvecOver_smul, Category.assoc]
  · rw [map_smul, tvecOver_smul]
  · rw [extendLin_comp, ← dualAlg_tvec, ← dualAlg_tvec, tvec_tmap, Category.assoc]

theorem coordBC_iff (hx : IsUnivChart G n x) : CoordBC hx S ↔ ChartBCOne (algebraMap R S) G n x := by
  constructor
  · rintro ⟨h1, h2, h3, -, -⟩
    let jm : ∀ m, JetR R (Fin n) m →ₐ[R] JetR S (Fin n) m := fun m =>
      jetLift R (RingHom.ker (jetAug S (Fin n) m)) (ker_jetAug_pow (Fin n) m) (fun j => zR m j)
        (fun j => zR_mem_ker m j)
    let x' := fun m => (push G S (JetR S (Fin n) m)).symm (spMap (jm m) ≫ x m)
    have key : ∀ c, push G S _ (tvec (x := x') c) = tvecOver x c := fun c => by
      rw [tvec, push_spMap, MulEquiv.apply_symm_apply, ← Category.assoc, spMap_comp, tvecOver]
      congr 2
      exact jet_ext fun j => by
        rw [AlgHom.comp_apply, jetLift_zR, dualLiftOver_zR]
        exact dualLift_zR c j
    refine ⟨x', ⟨fun c => ?_, fun w hw => ?_, fun c c' => ?_⟩, fun c => ?_⟩
    · rw [isTan_iff_push, key, h1]
    · refine (existsUnique_congr fun c => ?_).1 (h2 _ ((isTan_iff_push w).1 hw))
      rw [← key, (push G S _).injective.eq_iff]
    · apply (push G S _).injective
      rw [map_mul, key, key, key, h3]
    · rw [← push_left, key, dualMapR_tvec]
  · rintro ⟨x', ⟨h1, h2, h3⟩, h4⟩
    have key : ∀ c, push G S _ (tvec (x := x') c) = tvecOver x c :=
      family_ext (fun c c' => by rw [h3, map_mul]) (tvecOver_add hx)
        (fun r c => by
          rw [show tvec (x := x') (r • c) = spMap (scaleOver S r) ≫ tvec (x := x') c from tvecOver_smul (x := x') r c,
            push_spMap]
          rfl) tvecOver_smul
        (fun c => Over.OverMorphism.ext (by rw [push_left, h4, dualMapR_tvec]))
    refine ⟨fun c => ?_, fun w hw => ?_, tvecOver_add hx, tvecOver_smul, tvecOver_comp hx⟩
    · rw [← key, ← isTan_iff_push]
      exact h1 c
    · obtain ⟨w, rfl⟩ := (push G S _).surjective w
      refine (existsUnique_congr fun c => ?_).1 (h2 _ ((isTan_iff_push w).2 hw))
      rw [← key, (push G S _).injective.eq_iff]

def TanBCOne : Prop :=
  ∀ (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] (φ : R →+* S)
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G),
    IsUnivChart G n x → ChartBCOne φ G n x

theorem tangentBaseChange_iff_one : TangentBaseChange ↔ TanBCOne :=
  ⟨fun h R S _ _ _ φ G _ n x hx => by
    let _ := φ.toAlgebra
    exact (coordBC_iff hx).1 (h R G n x hx S),
  fun h R _ _ G _ n x hx S _ _ => (coordBC_iff hx).2 (h R S _ G n x hx)⟩

theorem tanBCOne_of_tanBCSt (h : TanBCSt) : TanBCOne :=
  fun R S _ _ _ φ G _ n x hx => chartBCOne_of_chartBC (h R S φ G n x hx)

end Tangent

section Rank

theorem basis_iff_finrank {k A : Type} [Field k] [Group A] {n : ℕ} (T : (Fin n → k) → A) (hT : Function.Injective T)
    (ha : ∀ c c', T (c + c') = T c * T c') (W : Submodule k (Fin n → k)) {P : A → Prop} {Q : k → A → A → Prop}
    (hP : ∀ w, P w ↔ ∃ c ∈ W, w = T c) (hQ : ∀ d u c, Q d u (T c) ↔ u = T (d • c)) (N : ℕ) :
    (∃ v : Fin N → A, (∀ i, P (v i)) ∧ ∀ w, P w →
      ∃! d : Fin N → k, ∃ u : Fin N → A, (∀ i, Q (d i) (u i) (v i)) ∧ w = (List.ofFn u).prod) ↔
      Module.finrank k W = N := by
  let T' : Multiplicative (Fin n → k) →* A := MonoidHom.mk' (fun c => T c.toAdd) fun c c' => ha _ _
  have pr : ∀ c : Fin N → Fin n → k, (List.ofFn fun i => T (c i)).prod = T (∑ i, c i) := fun c => by
    have := map_list_prod T' (List.ofFn fun i => Multiplicative.ofAdd (c i))
    rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum] at this
    exact this.symm
  have comb : ∀ (b : Fin N → W) (c : W) (d : Fin N → k),
      (∃ u : Fin N → A, (∀ i, Q (d i) (u i) (T (b i))) ∧ T c = (List.ofFn u).prod) ↔
        Fintype.linearCombination k b d = c := fun b c d => by
    simp only [hQ, ← funext_iff, exists_eq_left]
    rw [pr, hT.eq_iff, Subtype.ext_iff, Fintype.linearCombination_apply]
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    exact eq_comm
  constructor
  · rintro ⟨v, hv, H⟩
    choose b hb hb' using fun i => (hP _).1 (hv i)
    obtain rfl : v = fun i => T (b i) := funext hb'
    rw [← (LinearEquiv.ofBijective (Fintype.linearCombination k fun i => (⟨b i, hb i⟩ : W))
      ((Function.bijective_iff_existsUnique _).2 fun c => (existsUnique_congr (comb (fun i => ⟨b i, hb i⟩) c)).1
        (H _ ((hP _).2 ⟨c, c.2, rfl⟩)))).finrank_eq, Module.finrank_fin_fun]
  · intro h
    let b := Module.finBasisOfFinrankEq _ _ h
    refine ⟨fun i => T (b i), fun i => (hP _).2 ⟨_, (b i).2, rfl⟩, fun w hw => ?_⟩
    obtain ⟨c, hc, rfl⟩ := (hP _).1 hw
    refine (existsUnique_congr (comb b ⟨c, hc⟩)).2 ((Function.bijective_iff_existsUnique _).1 ?_ _)
    convert b.equivFun.symm.bijective using 1
    ext r
    simp [Fintype.linearCombination_apply]

def under {S X : Scheme.{0}} {G : Over S} {a : X ⟶ S} (y : Over.mk a ⟶ G) : X ⟶ G.left := y.left

theorem under_inj {S X : Scheme.{0}} {G : Over S} {a : X ⟶ S} {y y' : Over.mk a ⟶ G} :
    y = y' ↔ under y = under y' := Over.OverMorphism.ext_iff

theorem under_comp {S X : Scheme.{0}} {G : Over S} {a : X ⟶ S} (y : Over.mk a ⟶ G) (f : G ⟶ G) :
    under (y ≫ f) = under y ≫ f.left := rfl

theorem exists_mulEquiv_of_eq {S X : Scheme.{0}} (G : Over S) [GrpObj G] {a b : X ⟶ S} (h : a = b) :
    ∃ e : (Over.mk a ⟶ G) ≃* (Over.mk b ⟶ G), ∀ y, under (e y) = under y := by
  subst h
  exact ⟨MulEquiv.refl _, fun _ => rfl⟩

theorem isLieEigen_under {S : Scheme.{0}} {G : Over S} [GrpObj G] {k : Type} [Field k] {O : Type} [CommRing O]
    (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (v : epsPt t ⟶ G) :
    IsLieEigen act t τ v ↔
      Geo.Tor.spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ under v = under (1 : Over.mk t ⟶ G) ∧
        ∀ a, under v ≫ (act.act a).left = Geo.Tor.spMap (epsScale (τ a)) ≫ under v := Iff.rfl

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}

theorem under_scale {k : Type} [Field k] [Algebra R k] (d : k) (w : sp (R₀ := R) (DualNumber k) ⟶ G) :
    under (spMap (scaleOver R d) ≫ w) = Geo.Tor.spMap (epsScale d) ≫ under w := rfl

theorem under_fst {k : Type} [Field k] [Algebra R k] (w : sp (R₀ := R) (DualNumber k) ⟶ G) :
    under (spMap (fstOver R k) ≫ w) = Geo.Tor.spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ under w := rfl

theorem exists_eps {k : Type} [Field k] [Algebra R k] :
    ∃ e : (sp (R₀ := R) (DualNumber k) ⟶ G) ≃* (epsPt (Geo.Tor.spMap (algebraMap R k)) ⟶ G),
      ∀ y, under (e y) = under y :=
  exists_mulEquiv_of_eq G (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

theorem isLieEigen_iff {k : Type} [Field k] [Algebra R k] {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* k)
    (w : sp (R₀ := R) (DualNumber k) ⟶ G) (w' : epsPt (Geo.Tor.spMap (algebraMap R k)) ⟶ G)
    (he : under w' = under w) :
    IsLieEigen act _ τ w' ↔ spMap (fstOver R k) ≫ w = 1 ∧
      ∀ a, w ≫ act.act a = spMap (scaleOver R (τ a)) ≫ w := by
  rw [isLieEigen_under, he]
  refine and_congr ?_ (forall_congr' fun a => ?_)
  · rw [under_inj, under_fst]
  · rw [under_inj, under_comp, under_scale]

theorem mem_eig_iff (hx : IsUnivChart G n x) {k : Type} [Field k] [Algebra R k] (hB : CoordBC hx k) {O : Type}
    [CommRing O] (act : OAct O G) (τ : O →+* k) (c : Fin n → k) :
    c ∈ (⨅ a, LinearMap.ker (extendLin k (lieAct hx act a) - τ a • LinearMap.id) : Submodule k (Fin n → k)) ↔
      ∀ a, tvecOver x c ≫ act.act a = spMap (scaleOver R (τ a)) ≫ tvecOver x c := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hB
  have inj : Function.Injective (tvecOver x : (Fin n → k) → _) := fun c c' h => (h2 _ (h1 c)).unique rfl h
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun a => ?_
  have := act.hom a
  rw [h5, ← h4, inj.eq_iff, lieAct]

theorem lieMult_iff (hx : IsUnivChart G n x) {k : Type} [Field k] [Algebra R k] (hB : CoordBC hx k) {O : Type}
    [CommRing O] (act : OAct O G) (τ : O →+* k) (N : ℕ) :
    LieMult act (Geo.Tor.spMap (algebraMap R k)) τ N ↔ Module.finrank k
      (⨅ a, LinearMap.ker (extendLin k (lieAct hx act a) - τ a • LinearMap.id) : Submodule k (Fin n → k)) = N := by
  have m := mem_eig_iff hx hB act τ
  obtain ⟨h1, h2, h3, h4, -⟩ := hB
  obtain ⟨e, he⟩ := exists_eps (G := G) (k := k)
  have inj : Function.Injective (tvecOver x : (Fin n → k) → _) := fun c c' h => (h2 _ (h1 c)).unique rfl h
  refine basis_iff_finrank (fun c => e (tvecOver x c)) (e.injective.comp inj) (fun c c' => by rw [h3, map_mul]) _
    (P := IsLieEigen act _ τ) (Q := fun d u v => under u = Geo.Tor.spMap (epsScale d) ≫ under v)
    (fun w => ?_) (fun d u c => ?_) N
  · obtain ⟨w, rfl⟩ := e.surjective w
    rw [isLieEigen_iff act τ w _ (he w)]
    constructor
    · rintro ⟨t1, t2⟩
      obtain ⟨c, rfl, -⟩ := h2 w t1
      exact ⟨c, (m c).2 t2, rfl⟩
    · rintro ⟨c, hc, hw⟩
      obtain rfl := e.injective hw
      exact ⟨h1 c, (m c).1 hc⟩
  · rw [under_inj, he, he, h4, under_scale]

theorem exists_factor {O K k : Type} [CommRing O] [Algebra.IsIntegral ℤ O] [Field K] [IsAlgClosed K] [Field k]
    (i : K →+* k) (τ : O →+* k) : ∃ χ : O →+* K, i.comp χ = τ := by
  let _ := i.toAlgebra
  have h : ∀ a, ∃ z : K, i z = τ a := fun a => by
    have hi : IsIntegral K (τ a) := ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map τ.toIntAlgHom).tower_top
    exact minpoly.mem_range_of_degree_eq_one K _
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi))
  choose f hf using h
  have inj := i.injective
  exact ⟨⟨⟨⟨f, inj (by simp [hf])⟩, fun a b => inj (by simp [hf])⟩, inj (by simp [hf]),
    fun a b => inj (by simp [hf])⟩, RingHom.ext hf⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

variable {V : Type} [CommRing V] [IsDomain V]

def GenericDet (t' : SAB H (Spec (CommRingCat.of (FractionRing V)))) (ρ : V) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (FractionRing V) k],
    DetCond D t'.act (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) k)))
      (algebraMap (FractionRing V) k (algebraMap V (FractionRing V) ρ))

variable {t : SAB H (Spec (CommRingCat.of V))} {t' : SAB H (Spec (CommRingCat.of (FractionRing V)))}

def RankWhen (C : ∀ (V : Type) [CommRing V], ℕ → V → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (G : SAB H (Spec (CommRingCat.of V))) (t' : SAB H (Spec (CommRingCat.of (FractionRing V))))
    (_m : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))))
    (n : ℕ) (xc : ∀ m : ℕ, sp (R₀ := V) (JetR V (Fin n) m) ⟶ G.G) (hx : IsUnivChart G.G n xc) (χ : 𝓞 E →+* V) (ρ : V),
    C V H.d ρ → GenericDet D t' ρ →
    letI : ∀ a, IsMonHom (G.act.act a) := G.act.hom
    (χ H.rt = ρ → Module.finrank V (eigLat hx G.act.act χ) = D.p) ∧
      (χ H.rt ≠ ρ → Module.finrank V (eigLat hx G.act.act χ) = D.q)

def RankRoot : Prop := RankWhen fun V _ d ρ => ρ ^ 2 = -(d : V)

def RankOffRoot : Prop := RankWhen fun V _ d ρ => ρ ^ 2 ≠ -(d : V)

end Rank

end GlobalTheory.LieLatCompare
