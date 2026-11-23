import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqOfSecConst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical
namespace DimZero
open Inh

theorem res_one {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) : res h (1 : Γ(X, U)ˣ) = 1 := map_one _

theorem pullU_one {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) : pullU f U (1 : Γ(X, U)ˣ) = 1 := map_one _

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(X, U)ˣ) :
    res h' (res h u) = res (h'.trans h) u := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

def oneG {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Gen (LB.LinComb (trivLB X) φ ε) := ⟨fun _ => 1⟩

theorem oneG_gen {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (oneG φ ε).IsGen := by
  intro i j; rw [linComb_triv_g, _root_.one_mul]; exact (res_one _).trans (res_one _).symm

def oneS {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Sec (LB.LinComb (trivLB X) φ ε) := ⟨fun _ => 1, by
  intro i j; rw [linComb_triv_g, Units.val_one, _root_.one_mul]; exact (map_one _).trans (map_one _).symm⟩

theorem wchart_triv {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → (trivLB X).ι) :
    LB.wchart (trivLB X) φ j = ⊤ := by
  apply top_unique
  intro x _
  exact Set.mem_iInter.2 fun _ => trivial

theorem corr_of_one {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (h : ∀ j, t.s j = 1) (h' : ∀ j, t'.s j = 1) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' _ _ _
  exact ((congrArg _ (h j)).trans (res_one _)).trans ((congrArg _ (h' j')).trans (res_one _)).symm

theorem isoOne {X : Scheme.{0}} (L M : LB X) (hL : ∀ i j, L.g i j = 1) (hM : ∀ i j, M.g i j = 1) : LBIso L M :=
  ⟨⟨fun _ => 1⟩, by
    intro i j
    have : (LB.div M L).g i j = 1 := by
      simp only [LB.div, hL, hM]
      erw [res_one, res_one]; simp; rfl
    rw [this, _root_.one_mul]; exact (res_one _).trans (res_one _).symm⟩

variable (B : Scheme.{0})

theorem hypS_zero : HypS (zeroPolAV B).A (zeroPolAV B).L := by
  refine ⟨𝟙 _, 𝟙 _, inferInstance, inferInstance, toUnit_unique _ _, ?_, ?_⟩
  · exact isoOne _ _ (fun _ _ => rfl) (fun _ _ => linComb_triv_g _ _ _ _)
  · exact isoOne _ _ (fun _ _ => linComb_triv_g _ _ _ _) (fun _ _ => linComb_triv_g _ _ _ _)

theorem liftFun_bij (T : Over B) (W : (T ⊗ (zeroPolAV B).A).left.Opens) (hW : W = ⊤) :
    Function.Bijective (liftFun (zeroPolAV B).A (T := T) W) := by
  subst hW
  haveI : IsIso (fst T (zeroPolAV B).A) := by
    show IsIso (fst T (𝟙_ (Over B)))
    rw [← rightUnitor_hom]; infer_instance
  haveI : IsIso (fst T (zeroPolAV B).A).left := inferInstanceAs (IsIso ((Over.forget B).map (fst T (zeroPolAV B).A)))
  have h := ConcreteCategory.bijective_of_isIso ((fst T (zeroPolAV B).A).left.app ⊤)
  have e : liftFun (zeroPolAV B).A (T := T) ⊤ = (fst T (zeroPolAV B).A).left.appTop.hom := by
    funext r
    simp only [liftFun]
    have : (homOfLE (le_top : (⊤ : (T ⊗ (zeroPolAV B).A).left.Opens) ≤ ⊤)).op = 𝟙 _ := rfl
    rw [this, CategoryTheory.Functor.map_id]; rfl
  rw [e]; exact h

theorem translT_id {T : Over B} (x : T ⟶ (zeroPolAV B).A) : (translT (zeroPolAV B).A x).left = 𝟙 _ := by
  have : translT (zeroPolAV B).A x = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [translT]
    · exact toUnit_unique _ _
  rw [this]; rfl

theorem corr_comm {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb (trivLB X) φ ε)) (b : LB.Gen (LB.LinComb (trivLB X) φ' ε)) (h h' : Y ⟶ Y)
    (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb (trivLB X) (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr (trivLB X) _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j' _ _ _
  let d : K → (trivLB X).ι := fun _ => PUnit.unit
  have ha : ⊤ ≤ LB.wchart (trivLB X) φ d := by rw [wchart_triv]
  have hb : ⊤ ≤ LB.wchart (trivLB X) φ' d := by rw [wchart_triv]
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, res_res, res_res]
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (res_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (res_res _ _ _)
  · exact (res_res _ _ _).symm

theorem weil_zero (k : ℤ) {T : Over B} (x y : T ⟶ (zeroPolAV B).A) :
    WeilIs (zeroPolAV B).A (zeroPolAV B).L k x y 1 := by
  intro p
  refine ⟨⊤, trivial, ⟨⟨_, oneG _ _, oneG_gen _ _⟩, ⟨_, oneG _ _, oneG_gen _ _⟩, rfl, rfl⟩, ?_⟩
  intro θx θy _ _
  have hc : unitRes (T := T) ⊤ 1 = 1 := map_one _
  rw [hc]
  exact corr_comm _ _ _ _ _ _ _ (translT_id B _) (translT_id B _) _
    (fun j => (congrArg _ (map_one _)).trans (res_one _))

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def sys0 (ζ : o) (hζ : IsPrimitiveRoot ζ ((3 * 81) ^ 2)) (hu : IsUnit ((3 * 81 : ℕ) : o)) (R : Subalgebra o Ω)
    (fg : R.FG) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) : ThetaSys o Ω where
  g := 0
  N := 81
  r := 3
  N_ge := by norm_num
  r_pos := by norm_num
  ζ := ζ
  prim := hζ
  unit := hu
  J := Unit
  ρ := fun _ => 1
  ρ_one := fun _ _ => Subsingleton.elim _ _ |> fun (_ : () = ()) => by ext i j; simp [Matrix.one_apply]
  ρ_mul := fun _ _ => ⟨0, by simp⟩
  ρ_add := fun _ _ _ => by simp
  th := fun _ => 1
  ev := fun _ _ => 1
  R := R
  fg := fg
  frac := frac
  th_mem := fun _ => R.one_mem
  ev_mem := fun _ _ => R.one_mem
  supp := by simp
  th_ne := ⟨0, one_ne_zero⟩

theorem fn_one {R : Type} [CommRing R] : fn (1 : R) = 1 := map_one _

theorem liftFun_one {T : Over B} (A : Over B) (W : (T ⊗ A).left.Opens) : liftFun A (T := T) W 1 = 1 := by
  simp only [liftFun, map_one]

theorem basis_zero (T : Over B) (k : ℤ) (J : Type) [Fintype J] [Unique J] (σ : LB.Sec (LPow (zeroPolAV B).A (zeroPolAV B).L k T)) :
    ∃! c : J → Γ(T.left, ⊤), ∀ j, σ.f j = ∑ i, liftFun (zeroPolAV B).A _ (c i) *
      (oneS _ _ : LB.Sec (LPow (zeroPolAV B).A (zeroPolAV B).L k T)).f j := by
  let d : (LPow (zeroPolAV B).A (zeroPolAV B).L k T).ι := fun _ => PUnit.unit
  have hb := liftFun_bij B T ((LPow (zeroPolAV B).A (zeroPolAV B).L k T).U d) (wchart_triv _ _)
  obtain ⟨c, hc⟩ := hb.2 (σ.f d)
  refine ⟨fun _ => c, fun j => ?_, fun c' h' => ?_⟩
  · rw [Fintype.sum_unique]; exact hc.symm.trans (_root_.mul_one _).symm
  · funext i
    have := h' d
    rw [Fintype.sum_unique] at this
    rw [Subsingleton.elim i default]
    exact hb.1 (((_root_.mul_one _).symm.trans this.symm).trans hc.symm)

theorem value_one (k : ℤ) {T : Over B} (z : T ⟶ (zeroPolAV B).A)
    (τ : LB.Gen (LB.LinComb (zeroPolAV B).L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => k))) (hτ : ∀ j, τ.s j = 1) :
    IsValueAt (zeroPolAV B).A (zeroPolAV B).L k (oneS _ _) z τ 1 := by
  intro j
  refine ((congrArg _ (map_one _)).trans (map_one _)).trans ?_
  rw [map_one, _root_.one_mul]
  exact (congrArg Units.val (hτ j)).symm

theorem mul_s_one {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (h : ∀ j, t.s j = 1) (h' : ∀ j, t'.s j = 1) (j) : (LB.mulGen L φ ε φ' ε' t t').s j = 1 :=
  (congrArg₂ (· * ·) ((congrArg _ (h _)).trans (res_one _)) ((congrArg _ (h' _)).trans (res_one _))).trans (_root_.one_mul _)

theorem pull_s_one {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ Y) (h : ∀ j, t.s j = 1) (j) : (LB.pullGen L φ ε t f).s j = 1 :=
  (congrArg _ ((congrArg _ (h _)).trans (pullU_one _ _))).trans (res_one _)

theorem inv_s_one {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (h : ∀ j, t.s j = 1) (j) : (LB.invGen L φ ε t).s j = 1 :=
  (congrArg (·⁻¹) (h j)).trans inv_one

theorem rigT_one (T : Over B) (k : ℤ) (j) : (rigT (zeroPolAV B).A (zeroPolAV B).L (oneG _ _) T k).s j = 1 :=
  (congrArg (· ^ k) ((congrArg _ (pullU_one _ _)).trans (res_one _))).trans (one_zpow _)

theorem tors_zero (n : ℕ) {T : Over B} (x : T ⟶ (zeroPolAV B).A) :
    IsTorsFrame (zeroPolAV B) (oneG _ _) n x (oneG _ _) := by
  refine ⟨toUnit_unique _ _, oneG_gen _ _, oneG _ _, oneG_gen _ _, ?_, ?_⟩
  · exact corr_of_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)
      (mul_s_one _ _ _ _ _ _ _ (fun _ => one_zpow _) (inv_s_one _ _ _ _ fun _ => rfl))
  · exact corr_of_one _ _ _ _ _ _ _ (fun _ => one_zpow _)
      (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl) (rigT_one B _ _))

theorem symLift_zero (k : ℤ) (n : ℕ) {T : Over B} (x : T ⟶ (zeroPolAV B).A) :
    SymLift (zeroPolAV B).A (zeroPolAV B).L k n x ⟨x, oneG _ _, oneG_gen _ _⟩ := by
  refine ⟨rfl, corr_of_one _ _ _ _ _ _ _ (fun j => ?_) (fun _ => rfl), oneG _ _, oneG_gen _ _,
    corr_of_one _ _ _ _ _ _ _ ?_ (fun _ => rfl)⟩
  · show (∏ j₀ : Fin n, (_ : Γ((T ⊗ (zeroPolAV B).A).left, LB.wchart (zeroPolAV B).L (powφ (zeroPolAV B).A x n) j)ˣ)) = 1
    refine Finset.prod_eq_one fun j₀ _ => ?_
    exact (congrArg _ ((congrArg _ (pullU_one _ _)).trans (res_one _))).trans (res_one _)
  · exact mul_s_one _ _ _ _ _ _ _ (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl) fun _ => rfl)
      (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)
        (inv_s_one _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)))

theorem twist_one {T : Over B} (ψ : T ⊗ (zeroPolAV B).A ⟶ T ⊗ (zeroPolAV B).A) (m) (hm : ψ ≫ snd T _ = m) (a b : ℤ) :
    IsTwistPull (zeroPolAV B).A (zeroPolAV B).L ψ m hm a b (oneG _ _) (oneS _ _) (oneS _ _) := by
  intro j
  refine (map_one _).trans ?_
  exact ((congrArg₂ (· * ·) rfl ((congrArg _ (map_one _)).trans (map_one _))).trans (_root_.one_mul _)).symm

theorem act_one {T : Over B} (x : T ⟶ (zeroPolAV B).A) (k : ℤ) (σ : LB.Sec (LPow (zeroPolAV B).A (zeroPolAV B).L k T))
    (h : IsActOf (zeroPolAV B).A (zeroPolAV B).L k ⟨x, oneG _ _, oneG_gen _ _⟩ (oneS _ _) σ) (j) : σ.f j = 1 := by
  have h1 := (h (fun _ => PUnit.unit)).trans
    ((congrArg₂ (· * ·) rfl ((congrArg _ (map_one _)).trans (map_one _))).trans (_root_.one_mul _))
  have key : ∀ (Y : Scheme.{0}) (U V : Y.Opens) (hle : V ≤ U) (_ : U = ⊤) (_ : V = ⊤) (f : Γ(Y, U)),
      (Y.presheaf.map (homOfLE hle).op).hom f = 1 → f = 1 := by
    intro Y U V hle hU hV f hf
    subst hU hV
    have : (homOfLE hle).op = 𝟙 _ := rfl
    rw [this, CategoryTheory.Functor.map_id] at hf
    exact hf
  exact key _ _ _ _ (wchart_triv _ _) (wchart_triv _ _) _ h1

def real0 (ζ : o) (hζ : IsPrimitiveRoot ζ ((3 * 81) ^ 2)) (hu : IsUnit ((3 * 81 : ℕ) : o)) (R : Subalgebra o Ω)
    (fg : R.FG) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) : (sys0 ζ hζ hu R fg frac).Real where
  P := zeroPolAV _
  g_eq := rfl
  hypS := hypS_zero _
  n := 3
  n_prime := Nat.prime_three
  n_odd := by decide
  k := 2
  two_le := le_rfl
  N_eq := rfl
  r_eq := ⟨1, le_rfl, rfl⟩
  card := rfl
  pt := fun _ => 1
  pt_add := fun _ _ => (_root_.mul_one _).symm
  pt_bij := fun K _ _ x z _ => ⟨0, toUnit_unique _ _, fun a _ => funext fun i => by
    rcases i with i | i <;> exact i.elim0⟩
  weil := fun a b c hc => by
    have h0 : eStd (sys0 ζ hζ hu R fg frac).g _ a b = 0 := Finset.sum_eq_zero fun i _ => i.elim0
    rw [h0, ZMod.val_zero, Nat.mul_zero, pow_zero, map_one] at hc
    have : c = 1 := Units.ext hc
    subst this
    have : unitOn (1 : ((sys0 ζ hζ hu R fg frac).R)ˣ) = 1 := map_one _
    rw [this]
    exact weil_zero _ _ _ _
  rig := oneG _ _
  rig_gen := oneG_gen _ _
  th₁ := oneS _ _
  th₁_basis := fun σ => basis_zero _ _ _ (Fin 1) σ
  fr := fun _ => oneG _ _
  fr_tors := fun _ => tors_zero _ _ _
  th_val := fun _ => by
    refine (congrArg _ fn_one).mpr ?_
    exact value_one _ _ _ _ fun _ => rfl
  s := fun _ => oneS _ _
  s_basis := fun σ => basis_zero _ _ _ Unit σ
  ev_val := fun _ _ => by
    refine (congrArg _ fn_one).mpr ?_
    exact value_one _ _ _ _ fun _ => one_zpow _
  i₀ := ()
  α := oneG _ _
  α_gen := oneG_gen _ _
  α_norm := corr_of_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)
    (mul_s_one _ _ _ _ _ _ _ (rigT_one _ _ _) (rigT_one _ _ _))
  s_zero := twist_one _ _ _ _ _ _
  U := fun _ => ⟨1, oneG _ _, oneG_gen _ _⟩
  U_sym := fun _ => symLift_zero _ _ _ _
  U_act := fun a i σ h j => by
    refine (act_one _ _ _ σ h j).trans ?_
    have : ∀ l : Unit, (1 : Matrix Unit Unit o) l i = 1 := fun l => Matrix.one_apply_eq _
    refine Eq.symm ((Finset.sum_eq_single_of_mem () (Finset.mem_univ _) (fun _ _ h => absurd rfl h)).trans ?_)
    refine (_root_.mul_one _).trans ?_
    refine (congrArg _ ((congrArg fn ((congrArg _ (this _)).trans (map_one _))).trans fn_one)).trans (liftFun_one _ _ _)
  orbit := fun i => ⟨0, 0, fun l => by
    refine Eq.trans ?_ ((if_pos rfl).trans (pow_zero _)).symm
    exact @Matrix.one_apply_eq Unit o instDecidableEqPUnit _ _ ()⟩

section Padic
variable (p : ℕ) [Fact p.Prime]

def fracToCl : FractionRing ℤ_[p] →+* PadicAlgCl p :=
  (algebraMap ℚ_[p] (PadicAlgCl p)).comp (FractionRing.algEquiv ℤ_[p] ℚ_[p]).toRingEquiv.toRingHom

theorem norm_fracToCl_le (x : FractionRing ℤ_[p]) :
    ‖fracToCl p x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap ℤ_[p] (FractionRing ℤ_[p])) := by
  have h : ‖fracToCl p x‖ = ‖FractionRing.algEquiv ℤ_[p] ℚ_[p] x‖ := PadicAlgCl.norm_extends _ _
  rw [h]
  constructor
  · intro hx
    refine ⟨⟨_, hx⟩, (FractionRing.algEquiv ℤ_[p] ℚ_[p]).injective ?_⟩
    exact AlgEquiv.commutes _ _
  · rintro ⟨a, rfl⟩
    rw [AlgEquiv.commutes]; exact a.2

end Padic

section Tests
variable (ζ : o) (hζ : IsPrimitiveRoot ζ ((3 * 81) ^ 2)) (hu : IsUnit ((3 * 81 : ℕ) : o)) (R : Subalgebra o Ω)
  (fg : R.FG) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (p : ℕ) [Fact p.Prime]
  (yK : R →+* FractionRing ℤ_[p])

def utest0 : (real0 ζ hζ hu R fg frac).UTest p ((fracToCl p).comp yK) where
  V := ℤ_[p]
  complete := inferInstance
  alg := (fracToCl p).toAlgebra
  norm_le := norm_fracToCl_le p
  yK := yK
  fac := rfl
  A := zeroPolAV _
  φ := spMap yK
  cart := ⟨@IsPullback.of_vert_isIso _ _ _ _ _ _ _ _ _ _ (inferInstanceAs (IsIso (𝟙 _))) (inferInstanceAs (IsIso (𝟙 _)))
      ⟨(Category.comp_id _).trans (Category.id_comp _).symm⟩, fun T x y x₀ y₀ _ _ => by
    have h1 := Over.w (x₀ * y₀)
    have h2 := Over.w (x * y)
    exact ((Category.comp_id _).symm.trans h1).trans
      (congrArg (· ≫ spMap yK) (h2.symm.trans (Category.comp_id _)))⟩
  lb := isoOne _ _ (fun _ _ => rfl) (fun _ _ => linComb_triv_g _ _ _ _)
  G := 𝟙_ _
  comm := (zeroPolAV _).isAb.comm
  semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ (zeroPolAV _).isAb
  D := UnifZero.zeroData _ _
  U := ⟨UnifZero.zeroPre _ _, fun k _ => UnifZero.expBij k⟩

def labOfZero {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}
    (u : ρ.UTest p y₀) (hg : IsEmpty (Fin S.g)) (hX : Subsingleton u.D.toPre.X) (hψ : ∀ χ, u.PsiNorm χ 1)
    (hI : ∀ a, u.Integral a) : u.Lab where
  q := 0
  pos := by
    rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot
  q_eq := fun χ => by simpa using hψ χ
  yy := 0
  yy_onto := fun x => ⟨0, by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [Subsingleton.elim y 0]; rfl⟩
  yy_eq := fun _ pk _ _ _ => by rw [Subsingleton.elim pk.y 0]; rfl
  ker_iff := fun a => ⟨fun _ => hI a, fun _ => rfl⟩
  isoFree := by
    refine ⟨fun a _ h _ => Finset.sum_eq_zero fun i _ => hg.elim i, 0, ?_⟩
    have key : ∀ T : AddSubgroup S.Gam, Nonempty (T ≃+ (Fin 0 → ZMod (S.r * S.N))) := fun T => by
      haveI : Unique T := uniqueOfSubsingleton 0
      exact ⟨AddEquiv.ofUnique⟩
    exact key _
  wt := 0
  wt_eq := fun x α _ t => by
    have h0 : eStd S.g _ t.1 x = 0 := Finset.sum_eq_zero fun i _ => hg.elim i
    rw [h0, map_zero]; rfl

theorem valF_one {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (hU : U = ⊤) (f : Γ(X, U))
    (hf : f = 1) : valF x U f = 1 := by
  subst hU hf
  rw [valF, dif_pos (by simp), map_one, map_one]

theorem psiNorm_utest0 (χ) : (utest0 ζ hζ hu R fg frac p yK).PsiNorm χ 1 := by
  intro j _
  refine (congrArg (fun z => ‖fracToCl p z‖) (valF_one _ _ (wchart_triv _ _) _ ?_)).trans (by simp)
  exact congrArg Units.val
    (((ToricData.psi_isConst (K := ℤ_[p]) (X := PUnit) (fun _ => 1) χ).of_eq ToricData.unitOn_one j).trans
      (UnifZero.gv_one _))

theorem integral_utest0 (a) : (utest0 ζ hζ hu R fg frac p yK).Integral a := by
  refine ⟨𝟙 _, pullback.lift (jK ℤ_[p]) (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm),
    Category.comp_id _, (pullback.lift_fst _ _ _).trans (Category.comp_id _).symm, pullback.lift_snd _ _ _, ?_⟩
  have h1 : (utest0 ζ hζ hu R fg frac p yK).U.gen.hom.left = pullback.snd (𝟙 (Sp ℤ_[p])) (jK ℤ_[p]) :=
    (Category.comp_id _).symm.trans (Over.w (utest0 ζ hζ hu R fg frac p yK).U.gen.hom)
  have h2 : ((real0 ζ hζ hu R fg frac).pt a).left = 𝟙 _ :=
    (Category.comp_id _).symm.trans (Over.w ((real0 ζ hζ hu R fg frac).pt a))
  rw [h1, h2]
  exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ spMap yK) (pullback.lift_snd _ _ _)).trans
    (Category.id_comp _))).trans (Category.comp_id _).symm

def lab0 : (utest0 ζ hζ hu R fg frac p yK).Lab :=
  labOfZero _ (inferInstanceAs (IsEmpty (Fin 0))) (inferInstanceAs (Subsingleton PUnit))
    (psiNorm_utest0 ζ hζ hu R fg frac p yK) (integral_utest0 ζ hζ hu R fg frac p yK)
end Tests

section Arith
open NumberField

abbrev intAway (K : Type) [Field K] [NumberField K] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (Submonoid.powers (3 : 𝓞 K))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num))

theorem arithBase_intAway (K : Type) [Field K] [NumberField K] : ArithBase (intAway K) K where
  ded := IsLocalization.isDedekindDomain (𝓞 K) (M := Submonoid.powers (3 : 𝓞 K))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num)) _
  ft := by
    haveI : Algebra.FinitePresentation (𝓞 K) (intAway K) := IsLocalization.Away.finitePresentation (3 : 𝓞 K)
    exact Algebra.FiniteType.trans (S := 𝓞 K) inferInstance inferInstance
  char := inferInstance
  inj := Subtype.val_injective

theorem isUnit_three_intAway (K : Type) [Field K] [NumberField K] : IsUnit (3 : intAway K) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := intAway K) (3 : 𝓞 K)
  rwa [map_ofNat] at this

end Arith

example {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (ζ : o) (hζ) (hu) (R : Subalgebra o Ω) (fg) (frac)
    (p : ℕ) [Fact p.Prime] (y₀ : R →+* PadicAlgCl p) : (sys0 ζ hζ hu R fg frac).delta y₀ = 1 := by
  have : ∀ x, ‖y₀ ⟨(sys0 ζ hζ hu R fg frac).th x, (sys0 ζ hζ hu R fg frac).th_mem x⟩‖ = 1 := fun x =>
    (congrArg _ (map_one y₀)).trans norm_one
  exact (iSup_congr this).trans ciSup_const

example {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (hg : S.g = 1) (hN : S.N = 81)
    (hr : S.r = 243) : S.Big := by
  have h1 : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  rw [Real.rpow_one] at h1
  simp only [ThetaSys.Big, hg, hN, hr]
  push_cast
  refine ⟨by linarith, by simp only [Nat.factorial_one, Nat.cast_one]; linarith, by norm_num⟩

example {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (hg : S.g = 1) (hN : S.N = 81)
    (hr : S.r = 81) : ¬ S.Big := by
  have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_neg_one] at h2
  simp only [ThetaSys.Big, hg, hN, hr]
  push_cast
  rintro ⟨-, h, -⟩
  simp only [Nat.factorial_one, Nat.cast_one] at h
  linarith

end DimZero
end GlobalTheory.ZH
end
