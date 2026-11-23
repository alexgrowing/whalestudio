import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSub
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)

theorem exists_basis_of_isExtension {K L : Type} [Field K] [Field L] [Algebra K L] {V W : Type} [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module L W] {g : V →ₛₗ[algebraMap K L] W} (hg : IsExtension g) {I : Type}
    (v : Module.Basis I K V) : ∃ B : Module.Basis I L W, ∀ i, B i = g (v i) := by
  refine ⟨Module.Basis.mk (linearIndependent_of_isExtension hg v.linearIndependent) ?_,
    fun i => Module.Basis.mk_apply _ _ i⟩
  rw [← hg.span, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Submodule.span K (Set.range v) := v.mem_span x
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul d y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem exists_basis_of_components {L : Type} [Field L] {M : Type} [AddCommGroup M] [Module L M] {C : Type}
    [Finite C] {W : C → Type} [∀ x, AddCommGroup (W x)] [∀ x, Module L (W x)] (p : ∀ x, M →ₗ[L] W x)
    (inj : ∀ m, (∀ x, p x m = 0) → m = 0) {Idx : C → Type} (bs : ∀ x, Module.Basis (Idx x) L (W x))
    (v : ∀ x, Idx x → M) (h₁ : ∀ x i, p x (v x i) = bs x i) (h₂ : ∀ x y i, y ≠ x → p y (v x i) = 0) :
    ∃ B : Module.Basis (Σ x, Idx x) L M, ∀ x i, B ⟨x, i⟩ = v x i := by
  classical
  have := Fintype.ofFinite C
  have key : ∀ x i, LinearMap.pi p (v x i) = Pi.basis bs ⟨x, i⟩ := fun x i => by
    rw [Pi.basis_apply]
    funext y
    by_cases h : y = x
    · subst h
      rw [LinearMap.pi_apply, h₁, Pi.single_eq_same]
    · rw [LinearMap.pi_apply, h₂ x y i h, Pi.single_eq_of_ne h]
  have hb : Function.Bijective (LinearMap.pi p) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun m hm => inj m fun x => congrFun hm x, ?_⟩
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basis bs).span_eq, Submodule.span_le]
    rintro _ ⟨⟨x, i⟩, rfl⟩
    exact ⟨v x i, key x i⟩
  refine ⟨(Pi.basis bs).map (LinearEquiv.ofBijective _ hb).symm, fun x i => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.symm_apply_eq]
  exact (key x i).symm

theorem finite_of_reps {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {j : ℕ} (hj : 1 ≤ j) {C : Type}
    (rep : C → X) (hrep : ∀ α, ∃! x, ∃ mu, rep x + j • mu = α) : Finite C := by
  have : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg X (show j ≠ 0 by omega)
  refine Finite.of_injective
    (fun x => (QuotientAddGroup.mk (rep x) : X ⧸ (nsmulAddMonoidHom j : X →+ X).range)) fun x y h => ?_
  obtain ⟨mu, hmu⟩ := QuotientAddGroup.eq.1 h
  refine (hrep (rep y)).unique ⟨mu, ?_⟩ ⟨0, by rw [smul_zero, add_zero]⟩
  rw [show j • mu = -rep x + rep y from hmu, add_neg_cancel_left]

theorem exists_basis_constFam {C : Type} (rep : C → a.D₀.X) (hrep : ∀ α, ∃! x, ∃ mu, rep x + j • mu = α)
    {Idx : C → Type} (bas : ∀ x, Module.Basis (Idx x) k (SecBMod a.D₀ j (rep x))) :
    ∃ B : Module.Basis (Σ x, Idx x) F (Fam P.toPre F j),
      ∀ x i, B ⟨x, i⟩ = constFam hW F hG hj (rep x) (bas x i) := by
  let _ : Algebra k F := (constF k F).toAlgebra
  have := finite_of_reps hj rep hrep
  choose bs hbs using fun x => exists_basis_of_isExtension (isExtension_pullF hW F j (rep x)) (bas x)
  refine exists_basis_of_components (fun x => famComp P.toPre F j (e (rep x))) (fun m hm => ?_) bs _
    (fun x i => (constFam_self hW F hG hj _ _).trans (hbs x i).symm) (fun x y i h => ?_)
  · refine fam_ext fun χ i => ?_
    obtain ⟨x, ⟨mu, hmu⟩, -⟩ := hrep (e.symm χ)
    have hχ : ∃ nu, e (rep x) + j • nu = χ :=
      ⟨e mu, by rw [← map_nsmul, ← map_add, hmu, LinearEquiv.apply_symm_apply]⟩
    exact congrArg (fun q => LB.Sec.f q i) (FamFree.eq_of_eq_add_nsmul hG m 0 hχ (hm x))
  · refine constFam_off hW F hG hj _ _ _ fun mu hmu => h ?_
    refine (hrep (rep y)).unique ⟨0, by rw [smul_zero, add_zero]⟩ ⟨e.symm mu, e.injective ?_⟩
    rw [map_add, map_nsmul, LinearEquiv.apply_symm_apply, hmu]

end GlobalTheory.ConstFam
