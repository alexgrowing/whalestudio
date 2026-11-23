import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieCoordMult

theorem lieMult_iff_finrank_eig : ∀ (W : Type) [CommRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n : ℕ) (k : Type) [Field k] (β : W →+* k) (T : (Fin n → k) → (epsPtR (spMap β) ⟶ G)) (A : O → Matrix (Fin n) (Fin n) k), Function.Injective T → (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : k) c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) → (∀ a c, T c ≫ act.act a = T ((A a).mulVec c)) → ∀ (τ : O →+* k) (N : ℕ), LieMult act (spMap β) τ N ↔ Module.finrank k (⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) : Submodule k (Fin n → k)) = N := by
  intro W _ G _ _ O _ act n k _ β T A hinj htan hadd hsc hact τ N
  set E : Submodule k (Fin n → k) :=
    ⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) with hE
  have memE : ∀ x, x ∈ E ↔ ∀ a, (A a).mulVec x = τ a • x := by
    intro x
    simp [hE, Submodule.mem_iInf, sub_eq_zero]
  have T0 : T 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have Tsum : ∀ (m : ℕ) (y : Fin m → (Fin n → k)), (List.ofFn (fun i => T (y i))).prod = T (∑ i, y i) := by
    intro m
    induction m with
    | zero => intro y; simp [T0]
    | succ m ih => intro y; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have eig : ∀ w, IsLieEigen act (spMap β) τ w ↔ ∃ x ∈ E, w = T x := by
    intro w
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨x, rfl⟩ := (htan w).1 h1
      refine ⟨x, (memE x).2 fun a => hinj (Over.OverMorphism.ext ?_), rfl⟩
      rw [← hact, h2 a, hsc]
      rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(htan _).2 ⟨x, rfl⟩, fun a => ?_⟩
      rw [hact, (memE x).1 hx a, hsc]
      rfl
  have comb : ∀ (x : Fin N → (Fin n → k)) (y : Fin n → k) (c : Fin N → k),
      (∃ u : Fin N → (epsPt (spMap β) ⟶ G), (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (T (x i)).left) ∧
        T y = (List.ofFn u).prod) ↔ y = ∑ i, c i • x i := by
    intro x y c
    constructor
    · rintro ⟨u, hu, hy⟩
      have hu' : u = fun i => T (c i • x i) := funext fun i => Over.OverMorphism.ext ((hu i).trans (hsc _ _).symm)
      rw [hu', Tsum] at hy
      exact hinj hy
    · intro hy
      exact ⟨fun i => T (c i • x i), fun i => hsc _ _, by rw [Tsum, hy]⟩
  show (∃ v : Fin N → (epsPt (spMap β) ⟶ G), (∀ i, IsLieEigen act (spMap β) τ (v i)) ∧ ∀ w, IsLieEigen act (spMap β) τ w →
    ∃! c : Fin N → k, ∃ u : Fin N → (epsPt (spMap β) ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod) ↔ _
  constructor
  · rintro ⟨v, hv, H⟩
    choose x hxE hx using fun i => (eig _).1 (hv i)
    obtain rfl : v = fun i => T (x i) := funext hx
    let b : Fin N → E := fun i => ⟨x i, hxE i⟩
    have bij : Function.Bijective (Fintype.linearCombination k b) := by
      refine (Function.bijective_iff_existsUnique _).2 fun y => ?_
      refine (existsUnique_congr fun c => ?_).1 (H (T y) ((eig _).2 ⟨y, y.2, rfl⟩))
      rw [comb x y c, Subtype.ext_iff, Fintype.linearCombination_apply]
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, b]
      exact eq_comm
    rw [← (LinearEquiv.ofBijective _ bij).finrank_eq, Module.finrank_fin_fun]
  · intro h
    let b := Module.finBasisOfFinrankEq k E h
    refine ⟨fun i => T (b i), fun i => (eig _).2 ⟨_, (b i).2, rfl⟩, fun w hw => ?_⟩
    obtain ⟨y, hy, rfl⟩ := (eig w).1 hw
    refine (existsUnique_congr fun c => ?_).2
      ((Function.bijective_iff_existsUnique _).1 b.equivFun.symm.bijective ⟨y, hy⟩)
    rw [comb (fun i => (b i : Fin n → k)) y c, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    exact eq_comm

end GlobalTheory.LieCoordMult
