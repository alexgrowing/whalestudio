import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section
namespace GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {k : Type} [Field k] (t : Sp k ⟶ S)

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : C →+* A) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem left_iff (c : k) (u v : epsPt t ⟶ G) :
    u.left = spMap (epsScale c) ≫ v.left ↔ u = smT t c v := by
  constructor
  · intro h; apply Over.OverMorphism.ext; rw [h, smT_left]; rfl
  · rintro rfl; rw [smT_left]; rfl

theorem tang_iff (v : epsPt t ⟶ G) :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left ↔ smT t 0 v = 1 := by
  have e0 : (epsMul (0 : k)) = (algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    have h1 : (1 : epsPt t ⟶ G) = (Over.homMk (spMap (algebraMap k (DualNumber k))) rfl : epsPt t ⟶ Over.mk t) ≫ 1 :=
      (MonObj.comp_one _).symm
    rw [smT_left, e0, ← spMap_comp', Category.assoc, h, h1]
    rfl
  · intro h
    have hw : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) ≫ t = t := by
      rw [← Category.assoc, spMap_comp']
      have : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k))) = RingHom.id k := by
        refine RingHom.ext fun x => ?_; simp
      rw [this]
      simp [spMap]
    let s : Over.mk t ⟶ epsPt t := Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) hw
    have h2 := congrArg (fun φ => (s ≫ φ).left) h
    simp only [MonObj.comp_one] at h2
    rw [← h2]
    change _ = s.left ≫ (smT t 0 v).left
    rw [smT_left, ← Category.assoc]
    change _ = (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (epsMul 0)) ≫ v.left
    rw [spMap_comp']
    congr 2
    refine RingHom.ext fun x => ?_
    simp [epsMul, s]

end GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication

namespace GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {k : Type} [Field k] (t : Sp k ⟶ S)
variable {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* k)

theorem lieEigen_tan {w : epsPt t ⟶ G} (h : IsLieEigen act t τ w) : smT t 0 w = 1 := (tang_iff t w).1 h.1

theorem mem_iff (x : TanM t G) :
    x ∈ eigSub (actR (x0 := t) (S := k) act) τ ↔ IsLieEigen act t τ (tv x) := by
  rw [mem_eigSub]
  refine ⟨fun h => ⟨(tang_iff t _).2 (tv_mem x), fun a => ?_⟩, fun h a => ?_⟩
  · rw [left_iff]
    have := congrArg tv (h a)
    rw [tv_actR, tv_smul] at this
    exact this
  · apply tanM_ext
    rw [tv_actR, tv_smul]
    exact (left_iff t _ _ _).1 (h.2 a)

theorem prod_eq {m : ℕ} (x : Fin m → TanM t G) (c : Fin m → k) :
    (List.ofFn (fun i => smT t (c i) (tv (x i)))).prod = tv (∑ i, c i • x i) := by
  rw [List.prod_ofFn]
  show _ = ((Additive.toMul (∑ i, c i • x i) : tanSub t G) : overAt t (DualNumber k) ⟶ G)
  rw [toMul_sum, SubmonoidClass.coe_finset_prod]
  rfl

end GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication

namespace GlobalTheory.UPel.HT.LieLin
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj LieAlgebraMultiplication

theorem lieMult_iff_finrank : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G]
  (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (k : Type) [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (m : ℕ),
    Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM t G) →
      (LieMult act t τ m ↔ Module.finrank k (eigSub (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := t) (S := k) act) τ) = m) := by
  intro O _ S G _ _ act k _ t τ m hfin
  haveI := hfin
  constructor
  · rintro ⟨v, hv, huniq⟩
    let b : Fin m → eigSub (actR (x0 := t) (S := k) act) τ := fun i =>
      ⟨mkT (v i) (lieEigen_tan t act τ (hv i)), (mem_iff t act τ _).2 (hv i)⟩
    have key : ∀ (y : eigSub (actR (x0 := t) (S := k) act) τ) (e : Fin m → k),
        (y : TanM t G) = ∑ i, e i • (b i : TanM t G) →
        ∃ u : Fin m → (epsPt t ⟶ G), (∀ i, (u i).left = spMap (epsScale (e i)) ≫ (v i).left) ∧
          tv (y : TanM t G) = (List.ofFn u).prod := by
      intro y e he
      refine ⟨fun i => smT t (e i) (tv (b i : TanM t G)), fun i => (left_iff t _ _ _).2 rfl, ?_⟩
      rw [prod_eq t (fun i => (b i : TanM t G)) e, he]
    have hb : Function.Bijective (Fintype.linearCombination k b) := by
      constructor
      · intro c c' hcc
        rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply] at hcc
        let y : eigSub (actR (x0 := t) (S := k) act) τ := ∑ i, c i • b i
        have hy : IsLieEigen act t τ (tv (y : TanM t G)) := (mem_iff t act τ _).1 y.2
        obtain ⟨d, _, hd⟩ := huniq _ hy
        have h1 := hd c (key y c (by simp [y, Submodule.coe_sum]))
        have h2 := hd c' (key y c' (by rw [show y = ∑ i, c' i • b i from hcc]; simp [Submodule.coe_sum]))
        exact h1.trans h2.symm
      · intro y
        have hy : IsLieEigen act t τ (tv (y : TanM t G)) := (mem_iff t act τ _).1 y.2
        obtain ⟨c, ⟨u, hu, hw⟩, _⟩ := huniq _ hy
        refine ⟨c, ?_⟩
        have hu' : u = fun i => smT t (c i) (tv (b i : TanM t G)) :=
          funext fun i => (left_iff t _ _ _).1 (hu i)
        rw [hu', prod_eq] at hw
        rw [Fintype.linearCombination_apply]
        apply Subtype.ext
        apply tanM_ext
        rw [hw]
        simp [Submodule.coe_sum]
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_fin_fun]
  · intro h
    let B := Module.finBasisOfFinrankEq k (eigSub (actR (x0 := t) (S := k) act) τ) h
    refine ⟨fun i => tv (B i : TanM t G), fun i => (mem_iff t act τ _).1 (B i).2, fun w hw => ?_⟩
    have h0 := lieEigen_tan t act τ hw
    let y : eigSub (actR (x0 := t) (S := k) act) τ := ⟨mkT w h0, (mem_iff t act τ _).2 hw⟩
    refine ⟨B.equivFun y, ⟨fun i => smT t (B.equivFun y i) (tv (B i : TanM t G)),
      fun i => (left_iff t _ _ _).2 rfl, ?_⟩, ?_⟩
    · rw [prod_eq]
      show tv (y : TanM t G) = _
      congr 1
      have hs : ((∑ i, B.repr y i • B i : eigSub (actR (x0 := t) (S := k) act) τ) : TanM t G) = y :=
        congrArg Subtype.val (B.sum_repr y)
      refine hs.symm.trans ?_
      rw [Submodule.coe_sum]
      rfl
    · rintro c ⟨u, hu, hwu⟩
      have hu' : u = fun i => smT t (c i) (tv (B i : TanM t G)) :=
        funext fun i => (left_iff t _ _ _).1 (hu i)
      rw [hu', prod_eq] at hwu
      have hy : y = ∑ i, c i • B i := by
        apply Subtype.ext
        apply tanM_ext
        show w = _
        rw [hwu]
        simp [Submodule.coe_sum]
      rw [hy, ← B.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.UPel.HT.LieLin
