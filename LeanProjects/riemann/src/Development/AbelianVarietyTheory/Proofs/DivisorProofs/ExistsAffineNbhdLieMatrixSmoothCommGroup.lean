import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LieFrameCoord

open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

section Lin

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {n : ℕ}

def coordEquiv (b : Fin n → M) (h : ∀ m : M, ∃! a : Fin n → R, m = ∑ i, a i • b i) : M ≃ₗ[R] (Fin n → R) :=
  (LinearEquiv.ofBijective (Fintype.linearCombination R b)
    ⟨fun a a' haa' => by
        obtain ⟨c, -, hc⟩ := h (Fintype.linearCombination R b a)
        have e1 := hc a (by rw [Fintype.linearCombination_apply])
        have e2 := hc a' (by rw [haa', Fintype.linearCombination_apply])
        rw [e1, e2],
     fun m => by
        obtain ⟨a, ha, -⟩ := h m
        exact ⟨a, by rw [Fintype.linearCombination_apply, ha]⟩⟩).symm

theorem coordEquiv_symm_apply (b : Fin n → M) (h : ∀ m : M, ∃! a : Fin n → R, m = ∑ i, a i • b i)
    (a : Fin n → R) : (coordEquiv b h).symm a = ∑ i, a i • b i := by
  unfold coordEquiv
  rw [LinearEquiv.symm_symm]
  change Fintype.linearCombination R b a = _
  rw [Fintype.linearCombination_apply]

theorem coordEquiv_symm_single (b : Fin n → M) (h : ∀ m : M, ∃! a : Fin n → R, m = ∑ i, a i • b i)
    (j : Fin n) : (coordEquiv b h).symm (Pi.single j 1) = b j := by
  rw [coordEquiv_symm_apply]
  simp [Pi.single_apply]

theorem coord_transport {R' M' : Type} [CommRing R'] [AddCommGroup M'] [Module R' M'] (f : R →+* R')
    (e : M ≃ₗ[R] (Fin n → R)) (e' : M' ≃ₗ[R'] (Fin n → R')) (T : M →+ M')
    (hT : ∀ (a : R) (m : M), T (a • m) = f a • T m)
    (hb : ∀ j, T (e.symm (Pi.single j 1)) = e'.symm (Pi.single j 1))
    (α : M →ₗ[R] M) (α' : M' →ₗ[R'] M') (hα : ∀ m, T (α m) = α' (T m)) (v : M') :
    e' (α' v) = ((Matrix.of fun i j => e (α (e.symm (Pi.single j 1))) i).map f).mulVec (e' v) := by
  have hTe : ∀ m, e' (T m) = fun i => f (e m i) := by
    intro m
    have hm : m = ∑ j, e m j • e.symm (Pi.single j 1) := by
      apply e.injective
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hm]
    simp only [map_sum, hT, hb, map_smul, LinearEquiv.apply_symm_apply]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : v = ∑ j, e' v j • T (e.symm (Pi.single j 1)) := by
    simp_rw [hb]
    apply e'.injective
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, ← hα, hTe]
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

end Lin

section Geo

variable {X0 : Scheme.{0}} {A : Over X0} [GrpObj A] [IsCommMonObj A]

theorem dualMapR_comp_alg {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') :
    (Chart.dualMapR g).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp g := by
  apply RingHom.ext
  intro r
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMapR_comp_epsMul {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (a : R) :
    (Chart.dualMapR g).comp (epsMul a) = (epsMul (g a)).comp (Chart.dualMapR g) := by
  apply RingHom.ext
  intro r
  ext <;> simp [Chart.dualMapR, epsMul, mul_comm]

theorem dualMapR_comp_dualMapR {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (g : R' →+* R'')
    (h : R →+* R') : (Chart.dualMapR g).comp (Chart.dualMapR h) = Chart.dualMapR (g.comp h) := by
  apply RingHom.ext
  intro r
  ext <;> simp [Chart.dualMapR]

variable {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (x0 : Sp R ⟶ X0) (x' : Sp R' ⟶ X0)
  (hx : spMap g ≫ x0 = x')

def liftEps : overAt x' (DualNumber R') ⟶ overAt x0 (DualNumber R) :=
  Over.homMk (spMap (Chart.dualMapR g)) (by
    show spMap (Chart.dualMapR g) ≫ spMap (algebraMap R (DualNumber R)) ≫ x0 =
      spMap (algebraMap R' (DualNumber R')) ≫ x'
    rw [← hx, ← Category.assoc, ← Category.assoc, PullbackSections.spMap_comp_spMap, PullbackSections.spMap_comp_spMap,
      dualMapR_comp_alg])

variable {g x0 x' hx}

theorem smT_liftEps (a : R) (p : overAt x0 (DualNumber R) ⟶ A) :
    smT x' (g a) (liftEps g x0 x' hx ≫ p) = liftEps g x0 x' hx ≫ smT x0 a p := by
  apply Over.OverMorphism.ext
  rw [smT_left, Over.comp_left, Over.comp_left, smT_left]
  simp only [liftEps, Over.homMk_left]
  rw [← Category.assoc, ← Category.assoc, PullbackSections.spMap_comp_spMap, PullbackSections.spMap_comp_spMap, dualMapR_comp_epsMul]

variable (g x0 x' hx)

def tanMap : TanM x0 A →+ TanM x' A where
  toFun v := mkT (liftEps g x0 x' hx ≫ tv v) (by rw [← map_zero g, smT_liftEps, tv_mem, MonObj.comp_one])
  map_zero' := tanM_ext (by rw [tv_mkT, tv_zero, tv_zero, MonObj.comp_one])
  map_add' u v := tanM_ext (by rw [tv_mkT, tv_add, tv_add, tv_mkT, tv_mkT, MonObj.comp_mul])

variable {g x0 x' hx}

theorem tv_tanMap (v : TanM x0 A) : tv (tanMap g x0 x' hx v) = liftEps g x0 x' hx ≫ tv v := rfl

theorem tanMap_smul (a : R) (v : TanM x0 A) : tanMap g x0 x' hx (a • v) = g a • tanMap g x0 x' hx v :=
  tanM_ext (by rw [tv_tanMap, tv_smul, tv_smul, tv_tanMap, smT_liftEps])

theorem tanMap_actR {O : Type} [CommRing O] (act : OAct O A) (c : O) (v : TanM x0 A) :
    tanMap g x0 x' hx (actR (x0 := x0) (S := R) act c v) = actR (x0 := x') (S := R') act c (tanMap g x0 x' hx v) :=
  tanM_ext (by rw [tv_tanMap, tv_actR, tv_actR, tv_tanMap, Category.assoc])

theorem tangent_vector_finset_sum_eq_prod {S0 : Type} [CommRing S0] {y : Sp S0 ⟶ X0} {κ : Type} (s : Finset κ) (w : κ → TanM y A) :
    tv (∑ i ∈ s, w i) = ∏ i ∈ s, tv (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, tv_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, tv_add, ih]

end Geo

end GlobalTheory.LieFrameCoord

namespace GlobalTheory.LieFrameCoord

open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

variable {X0 : Scheme.{0}} {A : Over X0} [GrpObj A] [IsCommMonObj A]

theorem exists_frame {U : X0.Opens} (hU : IsAffineOpen U) {n : ℕ} (v₀ : Fin n → (Sp (DualNumber Γ(X0, U)) ⟶ A.left))
    (hv : ∀ (R' : Type) [CommRing R'] (f : Γ(X0, U) →+* R') (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ A.left),
      IsGrpPullback G' A (spMap f ≫ hU.fromSpec) φ →
        ∃ v' : Fin n → (epsR R' ⟶ G'), (∀ j, (v' j).left ≫ φ = spMap (Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v')
    (R' : Type) [CommRing R'] (f : Γ(X0, U) →+* R') :
    ∃ b : Fin n → TanM (spMap f ≫ hU.fromSpec) A, (∀ j, (tv (b j)).left = spMap (Chart.dualMapR f) ≫ v₀ j) ∧
      ∀ m, ∃! a : Fin n → R', m = ∑ i, a i • b i := by
  have h := isGrpPullback_pullback A (spMap f ≫ hU.fromSpec)
  obtain ⟨v', hleft, hvb⟩ := hv R' f _ _ h
  let b : Fin n → TanM (spMap f ≫ hU.fromSpec) A := fun i =>
    mkT (pushHom h (epsR R') (v' i)) ((isTangent_iff h _).1 (hvb.1 i))
  refine ⟨b, fun j => hleft j, fun m => ?_⟩
  obtain ⟨w', hw'⟩ := push_surj h (tv m)
  have htan : IsTangent w' := (isTangent_iff h w').2 (by rw [hw']; exact tv_mem m)
  have key : ∀ a : Fin n → R', IsLieComb a v' w' ↔ m = ∑ i, a i • b i := by
    intro a
    rw [isLieComb_iff h, hw']
    constructor
    · intro h1
      apply tanM_ext
      rw [h1, tangent_vector_finset_sum_eq_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [tv_smul]
      rfl
    · intro h1
      rw [h1, tangent_vector_finset_sum_eq_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [tv_smul]
      rfl
  obtain ⟨C, hC, hCu⟩ := hvb.2 w' htan
  exact ⟨C, (key C).1 hC, fun a ha => hCu a ((key a).2 ha)⟩

end GlobalTheory.LieFrameCoord

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieFrameCoord

theorem exists_affine_lieMatrix : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], Smooth A.hom →
  ∀ (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A) (z : S),
    ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ (n : ℕ) (M : O →+* Matrix (Fin n) (Fin n) Γ(S, U)),
      ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'),
        ∃ e : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A ≃ₗ[R'] (Fin n → R'),
          ∀ (c : O) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A),
            e (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := spMap f ≫ hU.fromSpec) (S := R') act c v) = matAct M f c (e v) := by
  intro O _ S A _ _ hsm act z
  haveI := hsm
  obtain ⟨U, hU, hzU, -, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange S A z ⊤ trivial
  refine ⟨U, hU, hzU, n, ?_⟩
  have hfr := exists_frame hU v₀ hv
  obtain ⟨b0, hb0l, hb0⟩ := hfr Γ(S, U) (RingHom.id _)
  let E0 := coordEquiv b0 hb0
  let B0 := Module.Basis.ofEquivFun E0
  let M : O →+* Matrix (Fin n) (Fin n) Γ(S, U) := (LinearMap.toMatrixAlgEquiv B0).toRingEquiv.toRingHom.comp
    (actR (x0 := spMap (RingHom.id Γ(S, U)) ≫ hU.fromSpec) (S := Γ(S, U)) act)
  refine ⟨M, fun R' _ f => ?_⟩
  obtain ⟨bf, hbfl, hbf⟩ := hfr R' f
  refine ⟨coordEquiv bf hbf, fun c v => ?_⟩
  have hx : spMap f ≫ spMap (RingHom.id Γ(S, U)) ≫ hU.fromSpec = spMap f ≫ hU.fromSpec := by
    rw [← Category.assoc, PullbackSections.spMap_comp_spMap, RingHom.comp_id]
  have hb : ∀ j, tanMap f _ _ hx (E0.symm (Pi.single j 1)) = (coordEquiv bf hbf).symm (Pi.single j 1) := by
    intro j
    rw [coordEquiv_symm_single, coordEquiv_symm_single]
    apply tanM_ext
    apply Over.OverMorphism.ext
    rw [tv_tanMap, Over.comp_left, hb0l, hbfl]
    simp only [liftEps, Over.homMk_left]
    rw [← Category.assoc, PullbackSections.spMap_comp_spMap, dualMapR_comp_dualMapR, RingHom.comp_id]
  have key := coord_transport f E0 (coordEquiv bf hbf) (tanMap f _ _ hx) (fun a m => tanMap_smul a m) hb
    (actR act c) (actR act c) (fun m => tanMap_actR act c m) v
  have hM : M c = Matrix.of fun i j => E0 (actR act c (E0.symm (Pi.single j 1))) i := by
    ext i j
    simp [M, B0, LinearMap.toMatrixAlgEquiv_apply]
  rw [matAct_apply, hM]
  exact key

end GlobalTheory
