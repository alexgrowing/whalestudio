import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace BoxIndep

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_tensor_pow (F O : Type) [Field F] [CommRing O] [Algebra F O] {m : ℕ} (β : Fin m → O)
    (hβ : LinearIndependent F β) (j : ℕ) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (em : Fin j → (O →ₐ[F] B)),
      LinearIndependent F (fun a : Fin j → Fin m => ∏ i, em i (β (a i))) := by
  induction j with
  | zero =>
    refine ⟨F, inferInstance, inferInstance, fun i => i.elim0, ?_⟩
    rw [linearIndependent_unique_iff]
    simp
  | succ j ih =>
    obtain ⟨B, _, _, em, h⟩ := ih
    refine ⟨TensorProduct F O B, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (em i)), ?_⟩
    have h2 := (hβ.tmul_of_isDomain h).comp (Fin.consEquiv (fun _ : Fin (j+1) => Fin m)).symm
      (Equiv.injective _)
    refine (congrArg (fun v : (Fin (j + 1) → Fin m) → TensorProduct F O B => LinearIndependent F v) (funext fun a => ?_)).mpr h2
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, AlgHom.comp_apply, Function.comp_apply]
    rw [← map_prod, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rfl

variable {X Z : Scheme.{0}}

noncomputable def germOf {B : CommRingCat.{0}} (r : Z ⟶ Spec B) (z : Z) : B →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp ((r.app ⊤).hom.comp (Scheme.ΓSpecIso B).inv.hom)

theorem germOf_apply {B : CommRingCat.{0}} (r : Z ⟶ Spec B) (z : Z) (a : B) :
    germOf r z a = gs r z ⊤ ((Scheme.ΓSpecIso B).inv.hom a) := (gs_eq r z ⊤ trivial _).symm

theorem germOf_map {B C : CommRingCat.{0}} (r : Z ⟶ Spec C) (φ : B ⟶ C) (z : Z) (a : B) :
    germOf (r ≫ Spec.map φ) z a = germOf r z (φ.hom a) := by
  rw [germOf_apply, germOf_apply, ← gs_pull r (Spec.map φ) z ⊤ trivial]
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality φ)
  exact congrArg (gs r z ⊤) e.symm

theorem eq_zero_of_germOf {B : CommRingCat.{0}} (a : B) (h : ∀ z, germOf (𝟙 (Spec B)) z a = 0) : a = 0 := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).1
  refine fn_ext fun z hz => ?_
  rw [map_zero, gs_zero _ _ _ hz]
  exact (germOf_apply _ _ _).symm.trans (h z)

theorem fromSpecStalk_mem (x : X) {U : X.Opens} (hx : x ∈ U) (y : Spec (X.presheaf.stalk x)) :
    X.fromSpecStalk x y ∈ U := by
  have : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact Specializes.mem_open this U.isOpen hx

theorem gs_fromSpecStalk (x : X) {U : X.Opens} (hx : x ∈ U) (r : Z ⟶ Spec (X.presheaf.stalk x)) (z : Z)
    (a : Γ(X, U)) : gs (r ≫ X.fromSpecStalk x) z U a = germOf r z (gs (𝟙 X) x U a) := by
  have hm := fromSpecStalk_mem x hx (r z)
  rw [← gs_pull r _ z U hm, Scheme.fromSpecStalk_app hx, germOf_apply, gs_eq (𝟙 X) x U hx]
  exact gs_res r z le_top hm _

theorem fromSpecStalk_comp {B : CommRingCat.{0}} (p : X ⟶ Spec B) (x : X) :
    X.fromSpecStalk x ≫ p = Spec.map (CommRingCat.ofHom (germOf p x)) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  ext a
  have e : CommRingCat.ofHom (germOf p x) =
      (Scheme.ΓSpecIso B).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial := rfl
  simp [e]

theorem exists_test {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F)) (x : X) {U : X.Opens} (hx : x ∈ U) {m : ℕ}
    (s : Fin m → Γ(X, U))
    (hs : ∀ c : Fin m → F, ∑ l, germOf p x (c l) * gs (𝟙 X) x U (s l) = 0 → c = 0) (j : ℕ) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Fin j → (Z ⟶ X)), (∀ i, r i ≫ p = q) ∧
      (∀ i z, r i z ∈ U) ∧ ∀ c : (Fin j → Fin m) → F,
        (∀ z, ∑ a, germOf q z (c a) * ∏ i, gs (r i) z U (s (a i)) = 0) → c = 0 := by
  let : Algebra F (X.presheaf.stalk x) := (germOf p x).toAlgebra
  have hβ : LinearIndependent F (fun l => gs (𝟙 X) x U (s l)) :=
    Fintype.linearIndependent_iff.2 fun c hc => congrFun (hs c (by simp only [Algebra.smul_def] at hc; exact hc))
  obtain ⟨B, _, _, em, h⟩ := exists_tensor_pow F _ _ hβ j
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    fun i => (Spec.map (CommRingCat.ofHom (em i).toRingHom) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x,
    fun i => ?_, fun i z => fromSpecStalk_mem x hx _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact (em i).commutes a
  · funext a
    refine Fintype.linearIndependent_iff.1 h c (eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_) a
    rw [← hc z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    congr 1
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gs_fromSpecStalk x hx]
      exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom (em i).toRingHom) z _).symm

theorem gs_liftFun {S : Scheme.{0}} (A : Over S) {B : CommRingCat.{0}} (t : Spec B ⟶ S)
    (W : (Over.mk t ⊗ A).left.Opens) (r : Z ⟶ (Over.mk t ⊗ A).left) (z : Z) (hz : r z ∈ W) (a : B) :
    gs r z W (liftFun A (T := Over.mk t) W ((Scheme.ΓSpecIso B).inv.hom a)) =
      germOf (B := B) (r ≫ (fst (Over.mk t) A).left) z a :=
  (gs_res r z le_top hz _).trans ((gs_pull r (fst (Over.mk t) A).left z ⊤ trivial _).trans (germOf_apply _ _ _).symm)

theorem gs_comb {S : Scheme.{0}} (A : Over S) {B : CommRingCat.{0}} (t : Spec B ⟶ S)
    (W : (Over.mk t ⊗ A).left.Opens) (r : Z ⟶ (Over.mk t ⊗ A).left) (z : Z) (hz : r z ∈ W) {K : Type} [Fintype K]
    (c : K → B) (f : K → Γ((Over.mk t ⊗ A).left, W)) :
    gs r z W (∑ l, liftFun A (T := Over.mk t) W ((Scheme.ΓSpecIso B).inv.hom (c l)) * f l) =
      ∑ l, germOf (B := B) (r ≫ (fst (Over.mk t) A).left) z (c l) * gs r z W (f l) := by
  rw [gs_fsum r z W hz]
  exact Finset.sum_congr rfl fun l _ => by rw [gs_mul r z W hz, gs_liftFun A t W r z hz]

theorem box_indep {S : Scheme.{0}} (j : ℕ) (A A' : PolAV S) (pA : IsPowPolAV A' A j) (F : Type) [Field F]
    (t : Spec (CommRingCat.of F) ⟶ S) (k m : ℕ)
    (b : Fin m → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (Over.mk t) A.A).left) (fun _ => (k : ℤ))))
    (hb : ∀ c : Fin m → F,
      (∀ jj, ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (b l).f jj = 0) → c = 0)
    (t' : (Fin j → Fin m) →
      LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (Over.mk t) A'.A).left) (fun _ => (k : ℤ))))
    (ht : ∀ a, (∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.mk t) ⊗ A'.A).left) (z : Z) (J J'), Good A.L z J → Good A'.L z J' →
      (bw pA.w (r ≫ (snd (Over.mk t) A'.A).left) z (fun i => J ((r ≫ (snd (Over.mk t) A'.A).left) ≫ (pA.pr i).left))
        (J' (r ≫ (snd (Over.mk t) A'.A).left)) ^ k).val * sval (t' a) r z J' =
        ∏ i, sval (b (a i)) (r ≫ ((Over.mk t) ◁ pA.pr i).left) z J))
    (c : (Fin j → Fin m) → F)
    (hc : ∀ jj, ∑ a, liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c a)) * (t' a).f jj = 0) :
    c = 0 := by
  have := A.isAb.smooth
  have := A.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres A.A.hom
  have hint : IsIntegral (Over.mk t ⊗ A.A).left :=
    hg.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t A.A.hom).flip
  obtain ⟨j₀, hj₀⟩ := exists_chart A.isLB ((snd (Over.mk t) A.A).left (genericPoint (Over.mk t ⊗ A.A).left))
  have hx : genericPoint (Over.mk t ⊗ A.A).left ∈
      LB.wchart A.L (fun _ : Fin 1 => (snd (Over.mk t) A.A).left) (fun _ => j₀) := Set.mem_iInter.2 fun _ => hj₀
  obtain ⟨Z, q, r, hq, hr, H⟩ := exists_test (F := F) (fst (Over.mk t) A.A).left _ hx (fun l => (b l).f (fun _ => j₀))
    (fun c hc => hb c fun jj => by
      refine fn_ext fun y hy => congrArg _ ?_
      have hy' : genericPoint (Over.mk t ⊗ A.A).left ∈
          LB.wchart A.L (fun _ : Fin 1 => (snd (Over.mk t) A.A).left) jj :=
        ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
      apply germ_injective_of_isIntegral _ _ hy'
      refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
      refine (gs_comb A.A t _ (𝟙 _) _ hy' c _).trans ?_
      simp only [fun l => sec_trans (b l) (𝟙 _) _ hy' hx, Category.id_comp, mul_left_comm _ (Units.val _)]
      rw [← Finset.mul_sum]
      exact (congrArg _ hc).trans (mul_zero _)) j
  let T : Over S := Over.mk (q ≫ t)
  let q' : T ⟶ Over.mk t := Over.homMk q rfl
  let r' : Fin j → (T ⟶ Over.mk t ⊗ A.A) := fun i => Over.homMk (r i) (by
    rw [← Over.w (fst (Over.mk t) A.A), ← Category.assoc, hq]; rfl)
  let ρ : T ⟶ Over.mk t ⊗ A'.A := lift q' (Fan.IsLimit.lift pA.lim fun i => r' i ≫ snd _ _)
  have hρ : ∀ i, ρ ≫ Over.mk t ◁ pA.pr i = r' i := fun i => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext (hq i).symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact Fan.IsLimit.fac pA.lim _ i
  have hρ' : ∀ i, (ρ.left : Z ⟶ _) ≫ (Over.mk t ◁ pA.pr i).left = r i := fun i => congrArg (fun g => g.left) (hρ i)
  have hρq : (ρ.left : Z ⟶ _) ≫ (fst (Over.mk t) A'.A).left = q :=
    congrArg (fun g => g.left) (lift_fst q' (Fan.IsLimit.lift pA.lim fun i => r' i ≫ snd _ _))
  refine H c fun z => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good A.L A.isLB z (fun i => r i ≫ (snd (Over.mk t) A.A).left) (fun _ => j₀)
    (fun _ _ _ => rfl) (fun i => Set.mem_iInter.1 (hr i z) 0)
  choose J' hJ' using fun ψ : Z ⟶ A'.A.left => exists_chart A'.isLB (ψ z)
  have hJ' : Good A'.L z J' := hJ'
  have hm := hJ'.mem (fun _ : Fin 1 => (snd (Over.mk t) A'.A).left) (ρ.left : Z ⟶ _)
  have E := (gs_comb A'.A t _ (ρ.left : Z ⟶ _) z hm c _).symm.trans
    ((congrArg _ (hc _)).trans (gs_zero _ _ _ hm))
  have E' := fun a => ht a Z ρ.left z J J' hJ hJ'
  simp only [hρ'] at E'
  rw [hρq] at E
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) (t' a) ρ.left z J' =
      ∏ i, sval (b (a i)) (r i) z J := ⟨_, E'⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ u).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ ((Finset.prod_congr rfl fun i _ =>
    (sval_of (b (a i)) (r i) z J (fun _ => j₀) (fun _ => eJ i)).symm).trans (hu a).symm)) ?_
  exact mul_left_comm _ _ _

end BoxIndep

theorem boxProduct_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (m : ℕ) (b : Fin m → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))), (∀ c : Fin m → F, (∀ jj, ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (b l).f jj = 0) → c = 0) → ∀ t' : (Fin j → Fin m) → LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))), (∀ a, (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval (t' a) r z J' = ∏ i, Geo.Tor.sval (b (a i)) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J)) → ∀ c : (Fin j → Fin m) → F, (∀ jj, ∑ a, liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c a)) * (t' a).f jj = 0) → c = 0 :=
  fun R _ _ j A A' pA F _ _ k m b hb t' ht c hc =>
    BoxIndep.box_indep j A A' pA F (jFK (R := R) F) k m b hb t' ht c hc

end GlobalTheory
