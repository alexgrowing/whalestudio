import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorLieBasisExists
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TensorDet

section Algebra

noncomputable def rightAction (k O O' M : Type) [CommRing k] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O O']
    [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M] : O' →+* Module.End k (k ⊗[O] M) :=
  (Module.End.baseChangeHom O k M).toRingHom.comp (Algebra.lsmul O O M : O' →ₐ[O] Module.End O M).toRingHom

variable {k O O' M : Type} [CommRing k] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O O']
    [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]

theorem rightAction_apply (a : O') :
    rightAction k O O' M a = LinearMap.baseChange k (Algebra.lsmul O O M a : M →ₗ[O] M) := rfl

theorem rightAction_tmul (a : O') (c : k) (m : M) : rightAction k O O' M a (c ⊗ₜ m) = c ⊗ₜ (a • m) := rfl

theorem nonempty_eigenSub_equiv [Algebra O' k] [IsScalarTower O O' k] {I : Type} {σ : I → O' →+* k}
    (h : EigenSplit.IsSplitting σ) (i : I) (hi : σ i = algebraMap O' k) :
    Nonempty (EigenSplit.eigenSub (rightAction k O O' M) (σ i) ≃ₗ[k] k ⊗[O'] M) := by
  classical
  let ρ := rightAction k O O' M
  let π : k ⊗[O] M →ₗ[k] k ⊗[O'] M := ((TensorProduct.mk O' k M 1).restrictScalars O).liftBaseChange k
  have hπ : ∀ m, π (1 ⊗ₜ m) = 1 ⊗ₜ m := fun m => by simp [π]
  let ρ' : O' →+* Module.End k (k ⊗[O'] M) := (algebraMap k _).comp (σ i)
  have he : EigenSplit.IsEquivariant ρ ρ' π := fun a x => by
    have : π ∘ₗ ρ a = ρ' a ∘ₗ π := by
      ext m
      simp only [TensorProduct.AlgebraTensorModule.curry_apply,
        TensorProduct.curry_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars, ρ, rightAction_tmul, hπ]
      simp [ρ', hi]
    exact congr($this x)
  let g : M →ₗ[O'] k ⊗[O] M :=
    { toFun := fun m => EigenSplit.proj h ρ i (1 ⊗ₜ m)
      map_add' := fun m n => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun a m => by
        rw [← rightAction_tmul, ← (EigenSplit.isEquivariant_action ρ a).proj h,
          EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem h ρ i _), hi, algebraMap_smul]
        rfl }
  let s : k ⊗[O'] M →ₗ[k] k ⊗[O] M := g.liftBaseChange k
  have h1 : s ∘ₗ π = EigenSplit.proj h ρ i := by
    ext m
    simp [hπ, s, g]
  have h2 : ∀ x, π (EigenSplit.proj h ρ i x) = π x := fun x => by
    rw [he.proj h]
    exact EigenSplit.proj_of_mem h (EigenSplit.mem_eigenSub.2 fun a => rfl)
  have h3 : π ∘ₗ s = LinearMap.id := by
    ext m
    simp [s, g, h2, hπ]
  refine ⟨LinearEquiv.ofBijective (π ∘ₗ Submodule.subtype _) ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_,
    fun y => ⟨EigenSplit.projTo h ρ i (s y), (h2 _).trans congr($h3 y)⟩⟩⟩
  refine Subtype.ext ((EigenSplit.proj_of_mem h x.2).symm.trans ?_)
  rw [← h1]
  exact (congrArg s hx).trans (map_zero s)

end Algebra

theorem injective_of_charZero {E k : Type} [Field E] [NumberField E] [Field k] [CharZero k] (τ : 𝓞 E →+* k) :
    Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot, ← Ideal.absNorm_eq_zero_iff]
  simpa using RingHom.mem_ker.1 (Ideal.absNorm_mem (RingHom.ker τ))

theorem finrank_eigenSub {E k O M : Type} [Field E] [NumberField E] [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing O] [Algebra O k] [Algebra O (𝓞 E)] [AddCommGroup M] [Module O M] [Module (𝓞 E) M]
    [IsScalarTower O (𝓞 E) M] (τ : 𝓞 E →+* k) (hτ : τ.comp (algebraMap O (𝓞 E)) = algebraMap O k) :
    Module.finrank k (EigenSplit.eigenSub (rightAction k O (𝓞 E) M) τ) = Module.finrank (𝓞 E) M := by
  have hs : EigenSplit.IsSplitting fun φ : E →+* k => φ.comp (algebraMap (𝓞 E) E) := by
    classical
    obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E k)
    exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  have hi := injective_of_charZero τ
  let _ := τ.toAlgebra
  have : IsScalarTower O (𝓞 E) k := IsScalarTower.of_algebraMap_eq' hτ.symm
  have : FaithfulSMul (𝓞 E) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have e : (IsFractionRing.lift hi : E →+* k).comp (algebraMap (𝓞 E) E) = τ :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hi a
  obtain ⟨f⟩ := nonempty_eigenSub_equiv (O := O) (M := M) hs (IsFractionRing.lift hi) e
  rw [← (TensorProduct.isBaseChange (𝓞 E) M k).finrank_eq, ← f.finrank_eq, e]

theorem lieMult_of_param {k O V : Type} [Field k] [CommRing O] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {A : Over (Sp k)} [GrpObj A] (act : OAct O A) (ρ : O →+* Module.End k V) (Φ : V → (epsR k ⟶ A))
    (inj : Function.Injective Φ) (tan : ∀ x, IsTangent x ↔ x ∈ Set.range Φ) (add : ∀ y z, Φ (y + z) = Φ y * Φ z)
    (smul : ∀ (c : k) y, IsLieComb ![c] ![Φ y] (Φ (c • y))) (eqv : ∀ a y, Φ (ρ a y) = Φ y ≫ act.act a)
    (τ : O →+* k) {n : ℕ} (hn : Module.finrank k (EigenSplit.eigenSub ρ τ) = n) :
    LieMult act (𝟙 (Sp k)) τ n := by
  have sm : ∀ (c : k) y x, x.left = spMap (epsScaleR c) ≫ (Φ y).left ↔ x = Φ (c • y) := fun c y x => by
    rw [← (LieMultiple.isLieComb_one_iff _ _ _).1 (smul c y)]
    exact ⟨fun h => Over.OverMorphism.ext h, fun h => by rw [h]⟩
  let F : Multiplicative V →* (epsR k ⟶ A) := MonoidHom.mk' (fun y => Φ y.toAdd) (fun y z => add _ _)
  have pr : ∀ (n : ℕ) (y : Fin n → V), (List.ofFn fun i => Φ (y i)).prod = Φ (∑ i, y i) := fun n y => by
    have := map_list_prod F (List.ofFn fun i => Multiplicative.ofAdd (y i))
    rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum] at this
    exact this.symm
  let B := Module.finBasisOfFinrankEq k _ hn
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ A) ≃* (epsR k ⟶ A) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl A)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ A).left = η[A].left := Category.id_comp _
  have mem : ∀ y, y ∈ EigenSplit.eigenSub ρ τ ↔
      ∀ a, (Φ y ≫ act.act a).left = spMap (epsScaleR (τ a)) ≫ (Φ y).left := fun y => by
    rw [EigenSplit.mem_eigenSub]
    exact forall_congr' fun a => by rw [sm, ← eqv, inj.eq_iff]
  refine LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ)
    (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (P := fun w => IsTangent w ∧ ∀ a, (w ≫ act.act a).left = spMap (epsScaleR (τ a)) ≫ w.left)
    (fun w => and_congr (by rw [IsTangent, he', one]) (forall_congr' fun a => by
      rw [Over.comp_left, Over.comp_left, he']
      rfl))
    (fun c u v => by rw [he', he']; rfl) n
    ⟨fun i => Φ (B i), fun i => ⟨(tan _).2 ⟨_, rfl⟩, (mem _).1 (B i).2⟩, ?_⟩
  rintro w ⟨hw, hw'⟩
  obtain ⟨y, rfl⟩ := (tan w).1 hw
  let y' : EigenSplit.eigenSub ρ τ := ⟨y, (mem y).2 hw'⟩
  refine (existsUnique_congr fun d => ?_).1 (existsUnique_eq' (a' := B.equivFun y'))
  have e₁ : B.equivFun y' = d ↔ y = ∑ i, d i • (B i : V) := by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [y']
  rw [e₁, ← inj.eq_iff, ← pr]
  constructor
  · exact fun h => ⟨_, fun i => (sm _ _ _).2 rfl, h⟩
  · rintro ⟨u, hu, h⟩
    rw [h, show u = fun i => Φ (d i • (B i : V)) from funext fun i => (sm _ _ _).1 (hu i)]

end GlobalTheory.TensorDet
