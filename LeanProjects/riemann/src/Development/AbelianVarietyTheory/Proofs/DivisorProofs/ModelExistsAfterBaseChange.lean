import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqNsmul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.LevelRaise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem exists_enum (o : Obj D l b s) {M : ℕ} (hM : 0 < M) :
    ∃ (J : Type) (_ : Finite J), ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
      ∃ u : J → (Over.mk x ⟶ o.t.G), Function.Injective u ∧ ∀ w, w ^ M = 1 ↔ ∃ j, u j = w := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient D M hM
  refine ⟨J, inferInstance, fun K _ _ x => ?_⟩
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨-, I, -⟩ := o.geom K x β.hom hβ.symm
  have hI : ∀ a b, I.ev M a = I.ev M b ↔ π a = π b := fun a b => by
    have h : I.ev M a = I.ev M (a - b) * I.ev M b := by rw [← I.add, sub_add_cancel]
    rw [hπ, h, mul_eq_right, I.ker M hM]
    rfl
  refine ⟨fun j => I.ev M (r j), fun i j hij => ?_, fun w => (I.onto M hM w).trans ⟨?_, ?_⟩⟩
  · have := (hI _ _).1 hij
    rwa [hr, hr] at this
  · rintro ⟨a, rfl⟩
    exact ⟨π a, (hI _ _).2 (hr _)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, rfl⟩

theorem exists_eq_comp (o : Obj D l b s) {M : ℕ} (hM : 0 < M) {K L : Type} [Field K] [Field L]
    [IsAlgClosed K] [IsAlgClosed L] {x : Sp K ⟶ S} {y : Sp L ⟶ S} (ψ : K →+* L) (g : Over.mk y ⟶ Over.mk x)
    (hg : g.left = spMap ψ) (w : Over.mk y ⟶ o.t.G) (hw : w ^ M = 1) :
    ∃ a : Over.mk x ⟶ o.t.G, a ^ M = 1 ∧ g ≫ a = w := by
  obtain ⟨J, _, hJ⟩ := exists_enum o hM
  obtain ⟨u, hu, hu'⟩ := hJ K x
  obtain ⟨v, -, hv'⟩ := hJ L y
  have hp : ∀ j, u j ^ M = 1 := fun j => (hu' _).2 ⟨j, rfl⟩
  choose τ hτ using fun j => (hv' (g ≫ u j)).1 (by rw [← MonObj.comp_pow, hp, MonObj.comp_one])
  have hτi : Function.Injective τ := fun i j hij =>
    hu (TorsionRat.comp_injective ψ g hg (by rw [← hτ, ← hτ, hij]))
  obtain ⟨j, rfl⟩ := (hv' w).1 hw
  obtain ⟨i, rfl⟩ := Finite.surjective_of_injective hτi j
  exact ⟨u i, hp i, (hτ i).symm⟩

theorem exists_finite_set (o : Obj D l b s) {M : ℕ} (hM : 0 < M) {K F : Type} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed F] (x : Sp K ⟶ S) :
    ∃ T : Set F, T.Finite ∧ ∀ L : IntermediateField K F, T ⊆ L →
      ∀ w : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ o.t.G, w ^ M = 1 →
        ∃ q : Over.mk (spMap (algebraMap K L) ≫ x) ⟶ o.t.G, spMap (algebraMap L F) ≫ q.left = w.left := by
  haveI := o.proper
  obtain ⟨J, _, hJ⟩ := exists_enum o hM
  obtain ⟨u, -, hu⟩ := hJ F (spMap (algebraMap K F) ≫ x)
  choose T hT using fun j => TorsionRat.exists_finset_over o.t.G x (u j)
  refine ⟨⋃ j, (T j : Set F), Set.finite_iUnion fun j => (T j).finite_toSet, fun L hL w hw => ?_⟩
  obtain ⟨j, rfl⟩ := (hu w).1 hw
  exact hT j L ((Set.subset_iUnion (fun j => (T j : Set F)) j).trans hL)

theorem exists_field {k : Type} [Field k] [NumberField k] {s : Sp k ⟶ Sp B} (o : Obj D l b s) {M : ℕ} (hM : 0 < M)
    (σ : k →+* ℂ) (C : IntermediateField ℚ ℂ) [FiniteDimensional ℚ C] :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (i : k →+* L) (j : C →+* L) (σ' : L →+* ℂ),
      σ'.comp i = σ ∧ (∀ c, σ' (j c) = c) ∧
      ∀ w : Over.mk (spMap σ' ≫ spMap i) ⟶ o.t.G, w ^ M = 1 →
        ∃ q : Sp L ⟶ o.t.G.left, q ≫ o.t.G.hom = spMap i ∧ spMap σ' ≫ q = w.left := by
  letI : Algebra k ℂ := σ.toAlgebra
  let F := algebraicClosure k ℂ
  haveI : IsAlgClosed F := (algebraicClosure.isAlgClosure k ℂ).isAlgClosed
  have hC : ∀ c : C, (c : ℂ) ∈ F := fun c => by
    rw [mem_algebraicClosure_iff]
    have h1 : IsAlgebraic ℚ (c : ℂ) :=
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c).algHom C.val
    exact h1.tower_top k
  let g : C →+* F := (C.val : C →+* ℂ).codRestrict F hC
  obtain ⟨T, hT, hT'⟩ := exists_finite_set o hM (K := k) (F := F) (𝟙 _)
  obtain ⟨U, hU⟩ := (Module.Finite.fg_top (R := ℚ) (M := C))
  let T' : Set F := T ∪ g '' U
  haveI : Finite T' := (hT.union (U.finite_toSet.image g)).to_subtype
  let L := IntermediateField.adjoin k T'
  haveI : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hg : ∀ c, g c ∈ L := fun c => by
    have hc : c ∈ Submodule.span ℚ (U : Set C) := hU ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (Or.inr ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul q x _ hx =>
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact mul_mem (SubfieldClass.ratCast_mem L q) hx
  refine ⟨L, inferInstance, NumberField.of_module_finite k L, algebraMap k L, g.codRestrict L hg,
    (algebraMap F ℂ).comp (algebraMap L F), rfl, fun c => rfl, fun w hw => ?_⟩
  let g₂ : Over.mk (spMap ((algebraMap F ℂ).comp (algebraMap L F)) ≫ spMap (algebraMap k L)) ⟶
      Over.mk (spMap (algebraMap k F) ≫ 𝟙 _) := Over.homMk (spMap (algebraMap F ℂ)) (by
    change spMap (algebraMap F ℂ) ≫ spMap (algebraMap k F) ≫ 𝟙 _ =
      spMap ((algebraMap F ℂ).comp (algebraMap L F)) ≫ spMap (algebraMap k L)
    rw [Category.comp_id, TorsionRat.sp_comp, TorsionRat.sp_comp]
    rfl)
  obtain ⟨a, ha, ha'⟩ := exists_eq_comp o hM (algebraMap F ℂ) g₂ rfl w hw
  obtain ⟨q, hq⟩ := hT' L (Set.subset_union_left.trans (IntermediateField.subset_adjoin _ _)) a ha
  refine ⟨q.left, (Over.w q).trans (Category.comp_id _), ?_⟩
  have h1 : spMap (algebraMap F ℂ) ≫ a.left = w.left := congrArg CommaMorphism.left ha'
  rw [← h1, ← hq, ← TorsionRat.sp_comp, Category.assoc]

theorem exists_obj_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (c₂ : Coeff l₂) (k : Type) [Field k] [NumberField k] (s : Sp k ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), 1 ≤ D.p + D.q → l₂.A = 1 → ∃ (k' : Type) (_ : Field k') (_ : NumberField k') (i : k →+* k') (j₂ : c₂.F →+* k') (o₂ : Obj D l₂ (baseKA l₂) (spMap j₂ ≫ spMap (IntermediateField.inclusion c₂.le).toRingHom)), Nonempty (SABMap o₂.t o.t (spMap i)) := by
  intro E _ _ _ H D l l₂ c₂ k _ _ s o _ hA
  obtain ⟨b₀, rfl⟩ : ∃ ν : KA l →+* k, s = spMap ν := ⟨(Spec.preimage s).hom, (Spec.map_preimage s).symm⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : k →+* ℂ, ∀ a, σ (b₀ a) = a := by
    letI : Algebra (KA l) k := b₀.toAlgebra
    haveI : Algebra.IsAlgebraic (KA l) k := Algebra.IsAlgebraic.tower_top (K := ℚ) (KA l)
    let τ : k →ₐ[KA l] ℂ := IsAlgClosed.lift
    exact ⟨τ, fun a => τ.commutes a⟩
  have hM : 0 < l₂.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l₂.three_le) l₂.A_pos
  haveI := c₂.fin
  obtain ⟨L, _, _, i, j, σ', hi, hj, hrat⟩ := exists_field o hM σ c₂.F
  obtain ⟨t', ⟨m⟩⟩ := exists_sab (spMap i) o.t
  let o' := ModelCompare.objOfSABMap o m
  let T : PAT H (Sp L) := ⟨t', ObjDim.isAbelianScheme o', _, ObjDim.smoothOfRelativeDimension o', ObjDim.sym,
    o'.ample, o'.ktriv⟩
  let j' : KA l₂ →+* L := j.comp (IntermediateField.inclusion c₂.le).toRingHom
  have hρ : j' (baseKA l₂).ρ = i (b₀ (baseKA l).ρ) := σ'.injective (by
    rw [← RingHom.comp_apply σ' i, hi, hσ]
    exact hj _)
  have hs : ∀ {k₁ : Type} [Field k₁] (β : L →+* k₁),
      spMap β ≫ spMap i ≫ spMap b₀ = spMap (β.comp (i.comp b₀)) := fun β => by
    rw [TorsionRat.sp_comp, TorsionRat.sp_comp]
  obtain ⟨-, I, -⟩ := o'.geom ℂ (spMap σ') _ (hs σ')
  obtain ⟨o₂, ho₂⟩ := RationalTorsion.exists_obj abelianSchemeLaws_all.1 E H D l₂ (KA l₂) (baseKA l₂) L j' σ' T I
    (fun k₁ _ _ β _ => by
      rw [hρ]
      exact (o'.geom k₁ (spMap β) _ (hs β)).1)
    (by
      have h1 := I.ζ_prim 1 one_pos
      have h2 := (baseKA l₂).ζ_prim
      rw [hA] at h2 ⊢
      rw [IsPrimitiveRoot.one_right_iff] at h1 h2
      rw [h1, h2, map_one, map_one, Units.val_one])
    (fun x hx => by
      obtain ⟨q, hq, hq'⟩ := hrat (ObjPull.pushEquiv m.cart (Over.mk (spMap σ')) x) (by rw [← map_pow, hx, map_one])
      refine ⟨Over.homMk (m.cart.1.lift q (𝟙 _) (hq.trans (Category.id_comp _).symm)) (m.cart.1.lift_snd _ _ _), ?_⟩
      apply Over.OverMorphism.ext
      apply m.cart.1.hom_ext
      · rw [Over.comp_left, ObjPull.toUnit_left', Category.assoc]
        exact (congrArg (spMap σ' ≫ ·) (m.cart.1.lift_fst _ _ _)).trans hq'
      · rw [Over.w, Over.w])
  refine ⟨L, inferInstance, inferInstance, i, j, ?_⟩
  rw [TorsionRat.sp_comp]
  exact ⟨o₂, ho₂ ▸ ⟨m⟩⟩

end GlobalTheory.LevelRaise
