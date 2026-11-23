import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeIntEmbEmbP
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomSquareZeroAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareZeroLiftLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareZeroInclusionHomExtStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetScaleOfTruncEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetOrderOneTangentDecompStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagonalJetSumScaleTwoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetLocalTruncKerSqAugmentStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpUniqCh0

section Helpers

variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)

theorem homAt_comp {A B C : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C]
    (f : A →ₐ[S] B) (g : B →ₐ[S] C) : Formalism.L2.Pj.homAt x0 (g.comp f) = Formalism.L2.Pj.homAt x0 g ≫ Formalism.L2.Pj.homAt x0 f := by
  apply Over.OverMorphism.ext
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem homAt_id {A : Type} [CommRing A] [Algebra S A] : Formalism.L2.Pj.homAt x0 (AlgHom.id S A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show Spec.map _ = 𝟙 _
  exact Spec.map_id _

theorem comp_one_gen {Y Z M : Over X} [GrpObj M] (f : Y ⟶ Z) : f ≫ (1 : Z ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit Z) (toUnit Y)]

end Helpers

end GlobalTheory.ExpUniqCh0

namespace GlobalTheory.ExpUniqCh0

section Tan

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {U V W : Type} [AddCommGroup U] [Module S U] [Module Sᵐᵒᵖ U] [IsCentralScalar S U]
  [AddCommGroup V] [Module S V] [Module Sᵐᵒᵖ V] [IsCentralScalar S V]
  [AddCommGroup W] [Module S W] [Module Sᵐᵒᵖ W] [IsCentralScalar S W]

theorem map_id' : TrivSqZeroExt.map (LinearMap.id : W →ₗ[S] W) = AlgHom.id S (TrivSqZeroExt S W) :=
  AlgHom.ext fun y => TrivSqZeroExt.ext (by simp) (by simp)

theorem map_comp' (f : V →ₗ[S] U) (g : W →ₗ[S] V) :
    (TrivSqZeroExt.map f).comp (TrivSqZeroExt.map g) = TrivSqZeroExt.map (f.comp g) :=
  AlgHom.ext fun y => TrivSqZeroExt.ext (by simp) (by simp)

theorem map_zero_eq : TrivSqZeroExt.map (0 : W →ₗ[S] V) =
    (Algebra.ofId S (TrivSqZeroExt S V)).comp (TrivSqZeroExt.fstHom S S W) :=
  AlgHom.ext fun y => TrivSqZeroExt.ext (by simp [TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [TrivSqZeroExt.algebraMap_eq_inl])

theorem comp_map_zero (y : overAt x0 (TrivSqZeroExt S W) ⟶ G)
    (hy : Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.fstHom S S W) ≫ y = 1) :
    Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (0 : W →ₗ[S] V)) ≫ y = 1 := by
  rw [map_zero_eq, homAt_comp, Category.assoc, hy, comp_one_gen]

theorem comp_map_nsmul (y : overAt x0 (TrivSqZeroExt S W) ⟶ G)
    (hy : Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.fstHom S S W) ≫ y = 1) (n : ℕ) :
    Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map ((n : S) • LinearMap.id : W →ₗ[S] W)) ≫ y = y ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero]; exact comp_map_zero x0 y hy
  | succ n ih =>
    rw [Nat.cast_succ, add_smul, one_smul, GlobalTheory.T.hom_square_zero_additive x0 y hy, ih, map_id', homAt_id, Category.id_comp, pow_succ]

variable [IsCommMonObj G]

theorem comp_map_sum (y : overAt x0 (TrivSqZeroExt S W) ⟶ G)
    (hy : Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.fstHom S S W) ≫ y = 1) {κ : Type} (s : Finset κ)
    (f : κ → (W →ₗ[S] V)) :
    Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (s.sum f)) ≫ y =
      s.prod (fun i => Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (f i)) ≫ y) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact comp_map_zero x0 y hy
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, GlobalTheory.T.hom_square_zero_additive x0 y hy, ih]

end Tan

end GlobalTheory.ExpUniqCh0

namespace GlobalTheory.ExpUniqCh0

section Steps

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [Field S] (x0 : Sp S ⟶ X)
  {A B : Type} [CommRing A] [Algebra S A] [IsLocalRing A] [CommRing B] [Algebra S B] [IsLocalRing B]

theorem incl_injective (q : A →ₐ[S] B) (hB : Function.Injective (algebraMap S B))
    [Module Sᵐᵒᵖ (RingHom.ker q)] [IsCentralScalar S (RingHom.ker q)] (hJ : RingHom.ker q ^ 2 = ⊥) :
    Function.Injective (incl (S := S) (RingHom.ker q) hJ) := by
  intro y z hyz
  rw [incl_apply, incl_apply] at hyz
  have h2 := congrArg q hyz
  rw [map_add, map_add, AlgHom.commutes, AlgHom.commutes, RingHom.mem_ker.1 y.snd.2, RingHom.mem_ker.1 z.snd.2,
    add_zero, add_zero] at h2
  have h3 : y.fst = z.fst := hB h2
  have h4 : (y.snd : A) = z.snd := by rw [h3] at hyz; exact add_left_cancel hyz
  exact TrivSqZeroExt.ext h3 (Subtype.ext h4)

theorem succ_two [CharZero S] (q : A →ₐ[S] B) (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
    (hB : Function.Injective (algebraMap S B)) (δ : overAt x0 A ⟶ G) (h1 : Formalism.L2.Pj.homAt x0 q ≫ δ = 1)
    (σ : A →ₐ[S] A) (N : ℕ) (hN : 2 < N) (hσ : ∀ p, q p = 0 → σ p = (N : S) • p)
    (hsc : Formalism.L2.Pj.homAt x0 σ ≫ δ = δ * δ) : δ = 1 := by
  letI : Module Sᵐᵒᵖ (RingHom.ker q) := Module.compHom _ ((RingHom.id S).fromOpposite fun _ _ => Commute.all _ _)
  haveI : IsCentralScalar S (RingHom.ker q) := ⟨fun s j => by
    show ((RingHom.id S).fromOpposite fun _ _ => Commute.all _ _) (MulOpposite.op s) • j = s • j
    rfl⟩
  obtain ⟨ε, hε1, hεδ⟩ := GlobalTheory.T.exists_square_zero_lift_local x0 q hq hJ δ h1
  have hinj := incl_injective q hB hJ
  have hθ : σ.comp (incl (S := S) (RingHom.ker q) hJ) =
      (incl (S := S) (RingHom.ker q) hJ).comp (TrivSqZeroExt.map ((N : S) • LinearMap.id)) := by
    refine AlgHom.ext fun y => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, incl_apply, incl_apply, map_add, AlgHom.commutes,
      hσ _ (RingHom.mem_ker.1 y.snd.2), TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]
    rfl
  have hpow := comp_map_nsmul x0 ε hε1
  have e1 : Formalism.L2.Pj.homAt x0 (incl (S := S) (RingHom.ker q) hJ) ≫ ε ^ N =
      Formalism.L2.Pj.homAt x0 (incl (S := S) (RingHom.ker q) hJ) ≫ ε ^ 2 := by
    rw [← hpow N, ← Category.assoc, ← homAt_comp, ← hθ, homAt_comp, Category.assoc, hεδ, hsc, ← hεδ,
      ← MonObj.comp_mul, pow_two]
  have hc := GlobalTheory.T.square_zero_inclusion_hom_ext x0 _ hJ hinj _ _ e1
  have hN' : ε ^ (N - 2) = 1 := by
    have : ε ^ (N - 2) * ε ^ 2 = ε ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hN.le]; exact hc
    exact mul_eq_right.1 this
  have hN0 : ((N - 2 : ℕ) : S) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e2 := (hpow (N - 2)).trans hN'
  have hε : ε = 1 := by
    calc ε = Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map
          ((((N - 2 : ℕ) : S)⁻¹ • LinearMap.id).comp (((N - 2 : ℕ) : S) • LinearMap.id) :
            RingHom.ker q →ₗ[S] RingHom.ker q)) ≫ ε := by
          rw [LinearMap.smul_comp, LinearMap.id_comp, smul_smul, inv_mul_cancel₀ hN0, one_smul, map_id', homAt_id,
            Category.id_comp]
      _ = 1 := by rw [← map_comp', homAt_comp, Category.assoc, e2, comp_one_gen]
  rw [← hεδ, hε, comp_one_gen]

theorem succ_one (q : A →ₐ[S] B) (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
    (δ : overAt x0 A ⟶ G) (h1 : Formalism.L2.Pj.homAt x0 q ≫ δ = 1) {κ : Type} [Fintype κ]
    (t : κ → (A →ₐ[S] DualNumber S)) (w : κ → A) (hw : ∀ r, q (w r) = 0)
    (ht : ∀ p, q p = 0 → (∀ r, (t r p).fst = 0) ∧ p = Finset.univ.sum (fun r => (t r p).snd • w r))
    (htan : ∀ r, Formalism.L2.Pj.homAt x0 (t r) ≫ δ = 1) : δ = 1 := by
  letI : Module Sᵐᵒᵖ (RingHom.ker q) := Module.compHom _ ((RingHom.id S).fromOpposite fun _ _ => Commute.all _ _)
  haveI : IsCentralScalar S (RingHom.ker q) := ⟨fun s j => by
    show ((RingHom.id S).fromOpposite fun _ _ => Commute.all _ _) (MulOpposite.op s) • j = s • j
    rfl⟩
  obtain ⟨ε, hε1, hεδ⟩ := GlobalTheory.T.exists_square_zero_lift_local x0 q hq hJ δ h1
  let ℓ : κ → (RingHom.ker q →ₗ[S] S) := fun r =>
    { toFun := fun p => (t r (p : A)).snd
      map_add' := fun p p' => by simp
      map_smul' := fun c p => by simp }
  let e : κ → (S →ₗ[S] RingHom.ker q) := fun r => LinearMap.toSpanSingleton S _ ⟨w r, hw r⟩
  have hsum : Finset.univ.sum (fun r => (e r).comp (ℓ r)) = LinearMap.id := by
    refine LinearMap.ext fun p => Subtype.ext ?_
    rw [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.id_apply]
    refine ((ht p p.2).2.trans (Finset.sum_congr rfl fun r _ => ?_)).symm
    rfl
  have hmap : ∀ r, (t r).comp (incl (S := S) (RingHom.ker q) hJ) = TrivSqZeroExt.map (ℓ r) := by
    intro r
    refine AlgHom.ext fun y => TrivSqZeroExt.ext ?_ ?_
    · rw [AlgHom.comp_apply, incl_apply, map_add, AlgHom.commutes, TrivSqZeroExt.fst_add, (ht _ y.snd.2).1 r,
        add_zero, TrivSqZeroExt.fst_map]
      rfl
    · rw [AlgHom.comp_apply, incl_apply, map_add, AlgHom.commutes, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_map]
      simp [TrivSqZeroExt.algebraMap_eq_inl, ℓ]
  have hℓ : ∀ r, Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (ℓ r)) ≫ ε = 1 := fun r => by
    rw [← hmap r, homAt_comp, Category.assoc, hεδ]
    exact htan r
  have hε : ε = 1 := by
    calc ε = Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (Finset.univ.sum (fun r => (e r).comp (ℓ r)))) ≫ ε := by
          rw [hsum, map_id', homAt_id, Category.id_comp]
      _ = Finset.univ.prod (fun r => Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map ((e r).comp (ℓ r))) ≫ ε) :=
          comp_map_sum x0 ε hε1 _ _
      _ = 1 := Finset.prod_eq_one fun r _ => by
          rw [← map_comp', homAt_comp, Category.assoc, hℓ r, comp_one_gen]
  rw [← hεδ, hε, comp_one_gen]

end Steps

end GlobalTheory.ExpUniqCh0

namespace GlobalTheory.ExpUniqCh0

theorem expUnique : ∀ {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (a : OAct O G)
    {S : Type} [Field S] [CharZero S] (x0 : Sp S ⟶ X) {ρ : Type} [Fintype ρ] [DecidableEq ρ] (ch : ρ → O →+* S)
    (u : ρ → (Sp (DualNumber S) ⟶ G.left)) (x x' : ∀ m, overAt x0 (Jet S ρ m) ⟶ G),
    IsExp a x0 ch u x → IsExp a x0 ch u x' → x = x' := by
  intro X G _ _ O _ a S _ _ x0 ρ _ _ ch u x x' hx hx'
  let δ : ∀ m, overAt x0 (Jet S ρ m) ⟶ G := fun m => x' m * (x m)⁻¹
  have htr : ∀ m, Formalism.L2.Pj.homAt x0 (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) ≫ δ (m + 1) = δ m := fun m => by
    simp only [δ, MonObj.comp_mul, GrpObj.comp_inv, hx.trunc m, hx'.trunc m]
  have hlaw : ∀ m, Formalism.L2.Pj.homAt x0 (jetSum (Finset.univ : Finset (Fin 2)) : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m) ≫ δ m =
      (Formalism.L2.Pj.homAt x0 (jetIn (0 : Fin 2) : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m) ≫ δ m) *
        (Formalism.L2.Pj.homAt x0 (jetIn (1 : Fin 2) : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m) ≫ δ m) := fun m => by
    simp only [δ, MonObj.comp_mul, GrpObj.comp_inv, hx.law m, hx'.law m]
    rw [_root_.mul_inv, _root_.mul_mul_mul_comm]
  have hzero : Formalism.L2.Pj.homAt x0 (jetAug : Jet S ρ 0 →ₐ[S] S) ≫ δ 0 = 1 := by
    simp only [δ, MonObj.comp_mul, GrpObj.comp_inv, hx.zero 0, hx'.zero 0, inv_one, _root_.mul_one]
  have htan : ∀ r, Formalism.L2.Pj.homAt x0 (jetTan r : Jet S ρ (0 + 1) →ₐ[S] DualNumber S) ≫ δ 1 = 1 := fun r => by
    have e : Formalism.L2.Pj.homAt x0 (jetTan r : Jet S ρ (0 + 1) →ₐ[S] DualNumber S) ≫ x' 1 =
        Formalism.L2.Pj.homAt x0 (jetTan r : Jet S ρ (0 + 1) →ₐ[S] DualNumber S) ≫ x 1 :=
      Over.OverMorphism.ext ((hx'.tan r).trans (hx.tan r).symm)
    simp only [δ, MonObj.comp_mul, GrpObj.comp_inv, e, _root_.mul_inv_cancel]
  have key : ∀ m, δ m = 1 := by
    intro m
    induction m with
    | zero =>
      have e := congrArg (fun f => Formalism.L2.Pj.homAt x0 (Algebra.ofId S (Jet S ρ 0)) ≫ f) hzero
      simp only [← Category.assoc, ← homAt_comp, (GlobalTheory.T.jet_local_trunc_ker_sq_augment (S := S) (ρ := ρ) 0).2.2, homAt_id, Category.id_comp,
        comp_one_gen] at e
      exact e
    | succ m ih =>
      have h1 : Formalism.L2.Pj.homAt x0 (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) ≫ δ (m + 1) = 1 := by rw [htr, ih]
      haveI : IsLocalRing (Jet S ρ m) := (GlobalTheory.T.jet_local_trunc_ker_sq_augment (S := S) (ρ := ρ) m).1
      haveI : IsLocalRing (Jet S ρ (m + 1)) := (GlobalTheory.T.jet_local_trunc_ker_sq_augment (S := S) (ρ := ρ) (m + 1)).1
      have hJ2 := (GlobalTheory.T.jet_local_trunc_ker_sq_augment (S := S) (ρ := ρ) m).2.1
      have hq : Function.Surjective (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) := by
        intro y
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨Ideal.Quotient.mk _ p, rfl⟩
      have hB : Function.Injective (algebraMap S (Jet S ρ m)) := fun a b h => by
        have := congrArg (jetAug : Jet S ρ m →ₐ[S] S) h
        rwa [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply] at this
      obtain rfl | ⟨m', rfl⟩ : m = 0 ∨ ∃ m', m = m' + 1 := by
        rcases m with _ | m'
        · exact Or.inl rfl
        · exact Or.inr ⟨m', rfl⟩
      · obtain ⟨hX, hp⟩ := GlobalTheory.T.jet_order_one_tangent_decomp (S := S) (ρ := ρ)
        exact succ_one x0 _ hq hJ2 (δ (0 + 1)) h1 (fun r => jetTan r)
          (fun r => Ideal.Quotient.mk _ (MvPolynomial.X r)) hX hp htan
      · have hdiag := GlobalTheory.T.diagonal_jet_sum_scale_two (S := S) (ρ := ρ) (m' + 1 + 1)
        refine succ_two x0 _ hq hJ2 hB (δ (m' + 1 + 1)) h1 (jetScale fun _ => (2 : S)) (2 ^ (m' + 1 + 1))
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ m' + 1 + 1))) ?_ ?_
        · intro p hp
          rw [GlobalTheory.T.jetScale_of_trunc_eq_zero (m' + 1) (2 : S) p hp, Nat.cast_pow, Nat.cast_ofNat]
        · rw [← hdiag.1, homAt_comp, Category.assoc, hlaw, MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
            ← homAt_comp, ← homAt_comp, hdiag.2 0, hdiag.2 1, homAt_id, Category.id_comp]
  funext m
  exact (_root_.mul_inv_eq_one.1 (key m)).symm

end GlobalTheory.ExpUniqCh0
