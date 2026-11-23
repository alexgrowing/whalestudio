import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.SmLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.LevelDescend

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S₀ : Scheme.{0}}
    {X : Obj F 𝔠 S} {X₀ : Obj F 𝔠 S₀} {b : S₀ ⟶ S} {i : X₀.A.left ⟶ X.A.left}

theorem push_injective (h : X₀.IsPullBy X b i) {T : Over S₀} {z z' : T ⟶ X₀.A}
    (e : pushPt h.grp.1.w z = pushPt h.grp.1.w z') : z = z' := by
  have e' : z.left ≫ i = z'.left ≫ i := congrArg (fun f => CommaMorphism.left f) e
  apply Over.OverMorphism.ext
  exact h.grp.1.hom_ext e' (by rw [Over.w z, Over.w z'])

theorem push_surjective (h : X₀.IsPullBy X b i) {T : Over S₀} (y : Over.mk (T.hom ≫ b) ⟶ X.A) :
    ∃ z : T ⟶ X₀.A, pushPt h.grp.1.w z = y := by
  have hy : y.left ≫ X.A.hom = T.hom ≫ b := by simpa using Over.w y
  refine ⟨Over.homMk (h.grp.1.lift y.left T.hom hy) (h.grp.1.lift_snd _ _ _), ?_⟩
  apply Over.OverMorphism.ext
  exact h.grp.1.lift_fst _ _ _

theorem push_mul (h : X₀.IsPullBy X b i) {T : Over S₀} (z z' : T ⟶ X₀.A) :
    pushPt h.grp.1.w (z * z') = pushPt h.grp.1.w z * pushPt h.grp.1.w z' := by
  apply Over.OverMorphism.ext
  exact (h.grp.2 T z z' _ _ rfl rfl).symm

theorem push_one (h : X₀.IsPullBy X b i) (T : Over S₀) :
    pushPt h.grp.1.w (1 : T ⟶ X₀.A) = 1 := by
  have e := push_mul h (1 : T ⟶ X₀.A) 1
  rw [_root_.mul_one] at e
  exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)

theorem push_pow (h : X₀.IsPullBy X b i) {T : Over S₀} (z : T ⟶ X₀.A) (n : ℕ) :
    pushPt h.grp.1.w (z ^ n) = pushPt h.grp.1.w z ^ n := by
  induction n with
  | zero => rw [_root_.pow_zero, _root_.pow_zero, push_one h]
  | succ n ih => rw [_root_.pow_succ, _root_.pow_succ, push_mul h, ih]

theorem push_pt_act (h : X₀.IsPullBy X b i) {N : ℕ} (α₀ : X₀.Level N) (q : Fin 2 → (𝟙_ (Over S) ⟶ X.A))
    (hpq : ∀ k, (α₀.pt k).left ≫ i = b ≫ (q k).left) {W : Scheme.{0}} (t₀ : W ⟶ S₀) (k : Fin 2) (a : 𝓞 F) :
    pushPt h.grp.1.w (toUnit (Over.mk t₀) ≫ α₀.pt k ≫ X₀.rm.act a) =
      toUnit (Over.mk (t₀ ≫ b)) ≫ q k ≫ X.rm.act a := by
  apply Over.OverMorphism.ext
  simp only [pushPt, Over.homMk_left, Over.comp_left, Over.toUnit_left, Over.mk_hom, Category.assoc,
    h.act a]
  rw [reassoc_of% (hpq k)]

end GlobalTheory.RealMult.LevelDescend

namespace GlobalTheory.RealMult

open LevelDescend in

theorem level_descend : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S₀ : Scheme.{0}}
    {X : Obj F 𝔠 S} {X₀ : Obj F 𝔠 S₀} {b : S₀ ⟶ S} {i : X₀.A.left ⟶ X.A.left}, X₀.IsPullBy X b i →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), ∃ t₀ : Sp Ω ⟶ S₀, t₀ ≫ b = t) →
    ∀ {N : ℕ} (α₀ : X₀.Level N) (q : Fin 2 → (𝟙_ (Over S) ⟶ X.A)), (∀ k, q k ^ N = 1) →
    (∀ k, (α₀.pt k).left ≫ i = b ≫ (q k).left) → Nonempty (X.Level N) := by
  intro F _ _ 𝔠 S S₀ X X₀ b i h hfac N α₀ q hq hpq
  refine ⟨{ pt := q, tors := hq, inj := ?_, surj := ?_ }⟩
  · intro Ω _ _ t a c e
    obtain ⟨t₀, rfl⟩ := hfac Ω t
    apply α₀.inj Ω t₀ a c
    apply push_injective h
    rw [push_mul h, push_one h, push_pt_act h α₀ q hpq, push_pt_act h α₀ q hpq]
    exact e
  · intro Ω _ _ t y hy
    obtain ⟨t₀, rfl⟩ := hfac Ω t
    obtain ⟨z, rfl⟩ := push_surjective h (T := Over.mk t₀) y
    have hz : z ^ N = 1 := by
      apply push_injective h
      rw [push_pow h, push_one h]
      exact hy
    obtain ⟨a, c, hac⟩ := α₀.surj Ω t₀ z hz
    refine ⟨a, c, ?_⟩
    rw [hac, push_mul h, push_pt_act h α₀ q hpq, push_pt_act h α₀ q hpq]

end GlobalTheory.RealMult
