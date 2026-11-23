import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SymLin

section Alg

open Polynomial in

theorem exists_sqrt_one (R : Type) [CommRing R] [Algebra ℚ R] (a : Rˣ) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧
      Module.FaithfullyFlat R R₁) ∧ ∃ b : R₁, b ^ 2 = algebraMap R R₁ a := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨R, inferInstance, inferInstance, ⟨inferInstance, inferInstance, inferInstance⟩, 0, Subsingleton.elim _ _⟩
  let f : R[X] := X ^ 2 - C (a : R)
  have hf : f.Monic := monic_X_pow_sub_C _ two_ne_zero
  have hroot : AdjoinRoot.root f ^ 2 = algebraMap R (AdjoinRoot f) a := by
    have := AdjoinRoot.aeval_eq f (f := f)
    rw [AdjoinRoot.mk_self] at this
    simpa [f, sub_eq_zero] using this
  have hru : IsUnit (AdjoinRoot.root f) := by
    rw [← isUnit_pow_iff two_ne_zero, hroot]
    exact a.isUnit.map _
  have h2 : IsUnit (2 : R) := by
    have := (Ne.isUnit (two_ne_zero : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
    rwa [map_ofNat] at this
  have het : Algebra.Etale R (AdjoinRoot f) := by
    refine GlobalTheory.etale_adjoinRoot_of_isUnit_derivative hf ?_
    have : AdjoinRoot.mk f f.derivative = algebraMap R (AdjoinRoot f) 2 * AdjoinRoot.root f := by
      simp [f, map_ofNat, one_add_one_eq_two]
    rw [this]
    exact (h2.map _).mul hru
  have hb := (AdjoinRoot.powerBasis' hf).basis
  have hd : (AdjoinRoot.powerBasis' hf).dim = 2 := by
    rw [AdjoinRoot.powerBasis'_dim]; exact natDegree_X_pow_sub_C
  have : Nonempty (Fin (AdjoinRoot.powerBasis' hf).dim) := by rw [hd]; infer_instance
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, ⟨Module.Finite.of_basis hb, het,
    Module.FaithfullyFlat.of_linearEquiv R _ hb.repr⟩, _, hroot⟩

theorem exists_sqrt (n : ℕ) : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (a : Fin n → Rˣ),
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧
      Module.FaithfullyFlat R R₁) ∧ ∀ i, ∃ b : R₁, b ^ 2 = algebraMap R R₁ (a i) := by
  induction n with
  | zero => exact fun R _ _ a =>
      ⟨R, inferInstance, inferInstance, ⟨inferInstance, inferInstance, inferInstance⟩, fun i => i.elim0⟩
  | succ n ih =>
    intro R _ _ a
    obtain ⟨R₁, _, _, ⟨h₁, h₂, h₃⟩, b, hb⟩ := exists_sqrt_one R (a 0)
    letI : Algebra ℚ R₁ := ((algebraMap R R₁).comp (algebraMap ℚ R)).toAlgebra
    obtain ⟨R₂, _, _, ⟨k₁, k₂, k₃⟩, hc⟩ := ih R₁ fun i => Units.map (algebraMap R R₁).toMonoidHom (a i.succ)
    letI : Algebra R R₂ := ((algebraMap R₁ R₂).comp (algebraMap R R₁)).toAlgebra
    have : IsScalarTower R R₁ R₂ := IsScalarTower.of_algebraMap_eq' rfl
    refine ⟨R₂, inferInstance, inferInstance, ⟨Module.Finite.trans R₁ R₂, Algebra.Etale.comp R R₁ R₂,
      Module.FaithfullyFlat.trans R R₁ R₂⟩, fun i => ?_⟩
    refine Fin.cases ⟨algebraMap R₁ R₂ b, by rw [← map_pow, hb]; rfl⟩ (fun i => hc i) i

def bas {n : ℕ} (i : Fin n) : Multiplicative (Fin n → ZMod 2) := Multiplicative.ofAdd (Pi.single i 1)

theorem mul_self_eq {n : ℕ} (c : Multiplicative (Fin n → ZMod 2)) : c * c = 1 :=
  funext fun i => CharTwo.add_self_eq_zero (c.toAdd i)

theorem exists_hom.{u} {n : ℕ} {G : Type u} [Monoid G] (g : Fin n → G) (h₁ : ∀ i, g i * g i = 1)
    (h₂ : ∀ i k, Commute (g i) (g k)) : ∃ Φ : Multiplicative (Fin n → ZMod 2) →* G, ∀ i, Φ (bas i) = g i := by
  let ϕ : ∀ i : Fin n, Multiplicative (ZMod 2) →* G := fun i =>
    { toFun := fun a => g i ^ a.toAdd.val
      map_one' := pow_zero _
      map_mul' := fun a b => by
        have h : g i ^ 2 = 1 := (pow_two _).trans (h₁ i)
        rw [toAdd_mul, ZMod.val_add, ← pow_add, pow_eq_pow_mod (a.toAdd.val + b.toAdd.val) h] }
  have hc : Pairwise fun i k => ∀ x y, Commute (ϕ i x) (ϕ k y) := fun i k _ x y => (h₂ i k).pow_pow _ _
  refine ⟨(MonoidHom.noncommPiCoprod ϕ hc).comp
    (MulEquiv.piMultiplicative fun _ : Fin n => ZMod 2).toMonoidHom, fun i => ?_⟩
  have e : (MulEquiv.piMultiplicative fun _ : Fin n => ZMod 2) (bas i) = Pi.mulSingle i (Multiplicative.ofAdd 1) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp [bas]
    · simp [bas, hk]
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, MonoidHom.noncommPiCoprod_mulSingle]
  exact pow_one _

theorem hom_ext.{u} {n : ℕ} {G : Type u} [Monoid G] {Φ Ψ : Multiplicative (Fin n → ZMod 2) →* G}
    (h : ∀ i, Φ (bas i) = Ψ (bas i)) (c : Multiplicative (Fin n → ZMod 2)) : Φ c = Ψ c := by
  have key : ∀ a : Fin n → ZMod 2, Φ (Multiplicative.ofAdd a) = Ψ (Multiplicative.ofAdd a) := fun a => by
    induction a using Pi.single_induction with
    | zero => exact (map_one Φ).trans (map_one Ψ).symm
    | add f g hf hg => rw [ofAdd_add, map_mul, map_mul, hf, hg]
    | single i m =>
      fin_cases m
      · show Φ (Multiplicative.ofAdd (Pi.single i 0)) = Ψ (Multiplicative.ofAdd (Pi.single i 0))
        rw [Pi.single_zero, ofAdd_zero, map_one, map_one]
      · exact h i
  exact key c.toAdd

theorem exists_cocycle.{u} {n : ℕ} {N : Type u} [CommGroup N] (ρ : Multiplicative (Fin n → ZMod 2) →* Monoid.End N)
    (Q : Multiplicative (Fin n → ZMod 2) → N → Prop) (q₁ : Q 1 1)
    (qm : ∀ c c' f f', Q c f → Q c' f' → Q (c * c') (f * ρ c f')) (w : Fin n → N) (hw : ∀ i, Q (bas i) (w i))
    (h₁ : ∀ i, w i * ρ (bas i) (w i) = 1) (h₂ : ∀ i k, w i * ρ (bas i) (w k) = w k * ρ (bas k) (w i)) :
    ∃ u : Multiplicative (Fin n → ZMod 2) → N, (∀ c, Q c (u c)) ∧ ∀ c c', u (c * c') = u c * ρ c (u c') := by
  let op : Multiplicative (Fin n → ZMod 2) → N → Multiplicative (Fin n → ZMod 2) × Function.End N :=
    fun c f => (c, fun g => f * ρ c g)
  have om : ∀ c c' f f', op c f * op c' f' = op (c * c') (f * ρ c f') := fun c c' f f' =>
    Prod.ext rfl (funext fun g => by
      show f * ρ c (f' * ρ c' g) = f * ρ c f' * ρ (c * c') g
      rw [map_mul (ρ c), map_mul ρ, _root_.mul_assoc]; rfl)
  have o₁ : op 1 1 = 1 := Prod.ext rfl (funext fun g => by
      show 1 * ρ 1 g = g
      rw [map_one, _root_.one_mul]; rfl)
  let S : Submonoid (Multiplicative (Fin n → ZMod 2) × Function.End N) :=
    { carrier := {p | ∃ f, Q p.1 f ∧ p = op p.1 f}
      one_mem' := ⟨1, q₁, o₁.symm⟩
      mul_mem' := by
        rintro p p' ⟨f, hf, e⟩ ⟨f', hf', e'⟩
        exact ⟨_, qm _ _ _ _ hf hf', (congrArg₂ (· * ·) e e').trans (om _ _ _ _)⟩ }
  obtain ⟨Φ, hΦ⟩ := exists_hom (G := S) (fun i => ⟨op (bas i) (w i), w i, hw i, rfl⟩)
    (fun i => Subtype.ext ((om (bas i) (bas i) (w i) (w i)).trans (by rw [mul_self_eq, h₁]; exact o₁)))
    (fun i k => Subtype.ext ((om (bas i) (bas k) (w i) (w k)).trans
      (by rw [mul_comm (bas i), h₂]; exact (om (bas k) (bas i) (w k) (w i)).symm)))
  have e : ∀ c, (Φ c).1.1 = c := hom_ext (Φ := (MonoidHom.fst _ _).comp (S.subtype.comp Φ)) (Ψ := MonoidHom.id _)
    fun i => congrArg (fun p : S => p.1.1) (hΦ i)
  choose u hu hu' using fun c => (Φ c).2
  simp only [e] at hu hu'
  refine ⟨u, hu, fun c c' => ?_⟩
  have := (hu' (c * c')).symm.trans ((congrArg Subtype.val (map_mul Φ c c')).trans
    ((congrArg₂ (· * ·) (hu' c) (hu' c')).trans (om _ _ _ _)))
  simpa [op] using congrArg (fun p => p.2 1) this

end Alg

section Values

variable {X X' Y Y' Y'' : Scheme.{0}}

abbrev Vals (M : LB X) (Y : Scheme.{0}) : Type 1 :=
  ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : {J // Good M z J}), (Z.presheaf.stalk z)ˣ

variable {M : LB X}

def vals {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε)) : Vals M Y :=
  fun _ r z J => val t r z J.1

def pl (h : Y' ⟶ Y) : Vals M Y →* Vals M Y' := MonoidHom.mk' (fun f Z r => f Z (r ≫ h)) fun _ _ => rfl

theorem pl_pl (h' : Y'' ⟶ Y') (h : Y' ⟶ Y) (f : Vals M Y) : pl h' (pl h f) = pl (h' ≫ h) f := by
  funext Z r
  exact congrArg (f Z) (Category.assoc _ _ _)

theorem pl_id (f : Vals M Y) : pl (𝟙 Y) f = f := by
  funext Z r
  exact congrArg (f Z) (Category.comp_id _)

def uv (M : LB X) (Y : Scheme.{0}) : Γ(Y, ⊤)ˣ →* Vals M Y :=
  MonoidHom.mk' (fun a _ r z _ => gm r z ⊤ a) fun a b => by
    funext Z r z J
    exact map_mul _ _ _

theorem pl_uv (h : Y' ⟶ Y) (a : Γ(Y, ⊤)ˣ) : pl h (uv M Y a) = uv M Y' (pullU h ⊤ a) := by
  funext Z r z J
  exact (gm_pull r h z ⊤ trivial a).symm

open FreeAbelianGroup in

def Rep (M : LB X) (D : FreeAbelianGroup (Y ⟶ X)) (f : Vals M Y) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb M φ ε)),
    t.IsGen ∧ ∑ k, ε k • of (φ k) = D ∧ vals t = f

open FreeAbelianGroup

theorem rep_vals {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen) :
    Rep M (∑ k, ε k • of (φ k)) (vals t) := ⟨K, _, φ, ε, t, ht, rfl, rfl⟩

theorem Rep.form {D D' : FreeAbelianGroup (Y ⟶ X)} {f : Vals M Y} (h : Rep M D f) (e : D = D') : Rep M D' f := e ▸ h

theorem Rep.mul {D D' : FreeAbelianGroup (Y ⟶ X)} {f f' : Vals M Y} (h : Rep M D f) (h' : Rep M D' f') :
    Rep M (D + D') (f * f') := by
  obtain ⟨K, _, φ, ε, t, ht, rfl, rfl⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', rfl, rfl⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen M _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    Fintype.sum_sum_type _, ?_⟩
  funext Z r z J
  exact val_mul J.2 _ _ _

theorem Rep.inv {D : FreeAbelianGroup (Y ⟶ X)} {f : Vals M Y} (h : Rep M D f) : Rep M (-D) f⁻¹ := by
  obtain ⟨K, _, φ, ε, t, ht, rfl, rfl⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen M _ _ t, DVR.invGen_isGen _ _ _ _ ht, by simp, ?_⟩
  funext Z r z J
  exact val_inv _ _

theorem Rep.pull {D : FreeAbelianGroup (Y ⟶ X)} {f : Vals M Y} (h : Rep M D f) (g : Y' ⟶ Y) :
    Rep M (FreeAbelianGroup.map (g ≫ ·) D) (pl g f) := by
  obtain ⟨K, _, φ, ε, t, ht, rfl, rfl⟩ := h
  refine ⟨K, inferInstance, _, _, LB.pullGen M _ _ t g, DVR.pullGen_isGen _ _ _ _ ht _, by simp, ?_⟩
  funext Z r z J
  exact val_pull J.2 _ _ _

theorem rep_uv (a : Γ(Y, ⊤)ˣ) : Rep M 0 (uv M Y a) := by
  refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ⟨fun _ => res le_top a⟩,
    isGen_of_gm _ fun y j j' hj hj' => ?_, by simp, ?_⟩
  · refine (gm_res _ y le_top hj a).trans (Eq.trans ?_ (congrArg _ (gm_res _ y le_top hj' a)).symm)
    simp [trF]
  · funext Z r z J
    exact gm_res r z le_top (J.2.mem _ r) a

theorem Rep.out (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) {f : Vals M Y}
    (h : Rep M (∑ k, ε k • of (φ k)) f) : ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ vals t = f := by
  obtain ⟨K', _, φ', ε', t', ht', e, rfl⟩ := h
  obtain ⟨t, ht, hv⟩ := exists_gen hM (φ' := φ) (ε' := ε) (fun U _ h => by
    have := congrArg (FreeAbelianGroup.lift fun ψ => Additive.ofMul (h ψ)) e
    simp only [map_sum, map_zsmul, lift_apply_of] at this
    apply Additive.ofMul.injective
    simpa only [ofMul_prod, ofMul_zpow] using this) t' ht'
  exact ⟨t, ht, funext fun Z => funext fun r => funext fun z => funext fun J => hv Z r z J.1 J.2⟩

theorem Rep.zero (hM : M.IsLB) {f : Vals M Y} (h : Rep M 0 f) : ∃ a, f = uv M Y a := by
  obtain ⟨t, -, rfl⟩ := Rep.out hM (K := PEmpty) PEmpty.elim PEmpty.elim (h.form (by simp))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), ?_⟩
  funext Z r z J
  exact (val_of t r z J.1 PEmpty.elim (fun k => k.elim)).trans (gm_res r z le trivial _).symm

def dn (M : LB X) (F : X' ⟶ X) (δ : ℤ) (Y : Scheme.{0}) :
    Vals (LB.LinComb M (K := PUnit) (fun _ => F) (fun _ => δ)) Y →* Vals M Y :=
  MonoidHom.mk' (fun f Z r z I => f Z r z ⟨fun χ _ => I.1 (χ ≫ F), fun χ => Set.mem_iInter.2 fun _ => I.2 (χ ≫ F)⟩)
    fun _ _ => rfl

theorem Rep.down (hM : M.IsLB) (F : X' ⟶ X) (δ : ℤ) {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) {f : Vals M Y}
    (h : Rep M (∑ k, (δ * ε k) • of (φ k ≫ F)) f) :
    ∃ t : LB.Gen (LB.LinComb (LB.LinComb M (K := PUnit) (fun _ => F) (fun _ => δ)) φ ε), t.IsGen ∧
      dn M F δ Y (vals t) = f := by
  obtain ⟨t, ht, rfl⟩ := Rep.out hM _ _ h
  have le : ∀ j : K → PUnit → M.ι, LB.wchart (LB.LinComb M (K := PUnit) (fun _ => F) (fun _ => δ)) φ j ≤
      LB.wchart M (fun k => φ k ≫ F) (fun k => j k PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) PUnit.unit
  refine ⟨⟨fun j => res (le j) (t.s _)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, ?_⟩
  · refine (gm_res _ y (le j) hj _).trans ((gen_trans ht (𝟙 Y) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (gm_res _ y (le j') hj' _).symm))
    refine Eq.trans ?_ (congrArg (· ^ ε k) (gm_linComb M (fun _ : PUnit => F) (fun _ => δ) (𝟙 Y ≫ φ k) y (j k) (j' k)
      (Set.mem_iInter.1 hj k) (Set.mem_iInter.1 hj' k))).symm
    rw [Fintype.prod_unique, zpow_mul, Category.assoc]
  · funext Z r z I
    refine Eq.trans ?_ (val_of t r z I.1 (fun k => I.1 ((r ≫ φ k) ≫ F)) (fun k => by rw [Category.assoc])).symm
    exact gm_res r z (le _) (Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => I.2 ((r ≫ φ k) ≫ F)) _

theorem uv_eq_one (hM : M.IsLB) (N : LB X') {a : Γ(Y, ⊤)ˣ} (h : uv M Y a = 1) : uv N Y a = 1 := by
  funext Z r z J
  choose I hI using fun χ : Z ⟶ X => exists_chart hM (χ z)
  exact congrFun (congrFun (congrFun (congrFun h Z) r) z) ⟨I, hI⟩

end Values

section Core

open FreeAbelianGroup GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

omit [IsCommMonObj A] in

abbrev tr (h : 𝟙_ (Over S) ⟶ A) : A ⟶ A := (toUnit A ≫ h) * 𝟙 A

omit [IsCommMonObj A] in
theorem comp_tr {T : Over S} (x : T ⟶ A) (h : 𝟙_ (Over S) ⟶ A) : x ≫ tr h = (toUnit T ≫ h) * x := by
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem tr_tr (h k : 𝟙_ (Over S) ⟶ A) : tr h ≫ tr k = tr (k * h) := by
  rw [comp_tr, tr, tr, MonObj.comp_mul, _root_.mul_assoc]

theorem tr_one : tr (1 : 𝟙_ (Over S) ⟶ A) = 𝟙 A := by
  rw [tr, MonObj.comp_one, _root_.one_mul]

theorem comp_inv' {T : Over S} (x : T ⟶ A) : x ≫ GrpObj.inv = x⁻¹ := rfl

theorem tr_inv {h : 𝟙_ (Over S) ⟶ A} (hh : h * h = 1) : tr h ≫ GrpObj.inv = GrpObj.inv ≫ tr h := by
  have e : (toUnit A ≫ h)⁻¹ = toUnit A ≫ h :=
    inv_eq_of_mul_eq_one_right (by rw [← MonObj.comp_mul, hh, MonObj.comp_one])
  rw [comp_tr, comp_inv', tr, mul_inv, e, ← comp_inv' (𝟙 A), Category.id_comp]

theorem cls_diag {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {s : S ⟶ Sp o} (hG : Out.GlobalFnsSt) (c : SiegPre h k ζ s)
    (hc : c.Principal) (hM : c.diag.IsLB) (T : Over S) :
    (∀ x y : T ⟶ c.A, y * y = 1 → pull (y * x).left (cls _ hM) = pull x.left (cls _ hM) + pull y.left (cls _ hM)) ∧
    (∀ y : T ⟶ c.A, y * y = 1 → pull y.left (cls _ hM) + pull y.left (cls _ hM) = 0) ∧
    ∀ x : T ⟶ c.A, pull (x⁻¹).left (cls _ hM) = pull x.left (cls _ hM) := by
  have hP := c.isLB
  let B : (T ⟶ c.A) → (T ⟶ c.A) → Pic T.left := fun a b => pull (lift a b).left (cls c.P hP)
  have hm : ∀ x : T ⟶ c.A, pull x.left (cls _ hM) = B x x := fun x => by
    have k : x.left ≫ (lift (𝟙 c.A) (𝟙 c.A)).left = (lift x x).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id]
    show pull x.left (pull (lift (𝟙 c.A) (𝟙 c.A)).left (cls c.P hP)) = pull (lift x x).left (cls c.P hP)
    rw [← k, pull_comp]
  have hb : ∀ a a' b, B (a * a') b = B a b + B a' b := fun a a' b => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab hM
      hc.1 c.P hP c.rig₁ c.rig₂ T a a' b).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [B]
    abel
  have hs : ∀ a b, B a b = B b a := fun a b => by
    have e : cls c.P hP = pull (lift (snd c.A c.A) (fst c.A c.A)).left (cls c.P hP) :=
      (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
    have k : (lift b a).left ≫ (lift (snd c.A c.A) (fst c.A c.A)).left = (lift a b).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    show pull (lift a b).left (cls c.P hP) = pull (lift b a).left (cls c.P hP)
    rw [← k, pull_comp, ← e]
  have h1 : ∀ b, B 1 b = 0 := fun b => by simpa using hb 1 1 b
  have hi : ∀ a b, B a⁻¹ b = -B a b := fun a b => eq_neg_of_add_eq_zero_left (by rw [← hb, inv_mul_cancel, h1])
  have h2 : ∀ y b, y * y = 1 → B y b + B y b = 0 := fun y b hy => by rw [← hb, hy, h1]
  simp only [hm]
  refine ⟨fun x y hy => ?_, fun y hy => h2 y y hy, fun x => by rw [hi, hs, hi, neg_neg]⟩
  rw [hb, hs y, hs x, hb, hb, hs x y]
  linear_combination (norm := abel) h2 y x hy

theorem core (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB)
    (H : ∀ T : Over S,
      (∀ x y : T ⟶ A, y * y = 1 → pull (y * x).left (cls _ hM) = pull x.left (cls _ hM) + pull y.left (cls _ hM)) ∧
      (∀ y : T ⟶ A, y * y = 1 → pull y.left (cls _ hM) + pull y.left (cls _ hM) = 0) ∧
      ∀ x : T ⟶ A, pull (x⁻¹).left (cls _ hM) = pull x.left (cls _ hM))
    {κ : Type} (h : κ → (𝟙_ (Over S) ⟶ A)) (hh : ∀ i, h i * h i = 1) :
    ∃ (v : κ → Vals M A.left) (j : Vals M A.left) (a : κ → Γ(S, ⊤)ˣ),
      (∀ i, Rep M (of (𝟙 _) + of (𝟙 _) - of (tr (h i)).left - of (tr (h i)).left) (v i)) ∧
      Rep M (of (𝟙 _) + of (𝟙 _) - of (GrpObj.inv : A ⟶ A).left - of (GrpObj.inv : A ⟶ A).left) j ∧
      (∀ i, v i * pl (tr (h i)).left (v i) = pl A.hom (uv M S (a i))) ∧
      (∀ i k, v i * pl (tr (h i)).left (v k) = v k * pl (tr (h k)).left (v i)) ∧
      ∀ i, v i * pl (tr (h i)).left j = j * pl (GrpObj.inv : A ⟶ A).left (v i) := by
  have ex : ∀ {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ A.left)) (ε : K → ℤ),
      ∑ k, ε k • pull (φ k) (cls M hM) = 0 → ∃ f, Rep M (∑ k, ε k • of (φ k)) f := fun φ ε e => by
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff (LB.isLB_linComb hM φ ε)).1 ((cls_linComb hM φ ε _).trans e)
    exact ⟨_, rep_vals ht⟩
  have base : ∀ f, Rep M 0 f → ∃ b : Γ(S, ⊤)ˣ, f = pl A.hom (uv M S b) := fun f hf => by
    obtain ⟨a, rfl⟩ := hf.zero hM
    let e := RingEquiv.ofBijective _ (hG S A hA)
    refine ⟨Units.map e.symm.toRingHom.toMonoidHom a, ?_⟩
    rw [pl_uv]
    exact congrArg _ (Units.ext (e.apply_symm_apply a.val).symm)
  have cst : ∀ f, Rep M 0 f → ∀ x : A ⟶ A, pl x.left f = f := fun f hf x => by
    obtain ⟨b, rfl⟩ := base f hf
    rw [pl_pl, Over.w]
  have pp : ∀ (x y : A ⟶ A) (f : Vals M A.left), pl x.left (pl y.left f) = pl (x ≫ y).left f := fun x y f => pl_pl _ _ _
  have h2 : ∀ i, (toUnit A ≫ h i) * (toUnit A ≫ h i) = 1 := fun i => by rw [← MonObj.comp_mul, hh, MonObj.comp_one]
  have tt : ∀ i, tr (h i) ≫ tr (h i) = 𝟙 A := fun i => by rw [tr_tr, hh, tr_one]
  have tc : ∀ i k, tr (h i) ≫ tr (h k) = tr (h k) ≫ tr (h i) := fun i k => by rw [tr_tr, tr_tr, mul_comm]
  have ii : (GrpObj.inv : A ⟶ A) ≫ GrpObj.inv = 𝟙 A := GrpObj.inv_comp_inv A
  choose ψ hψ using fun i => ex ![(𝟙 A : A ⟶ A).left, (tr (h i)).left, (toUnit A ≫ h i).left] ![1, -1, 1] (by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul]
    rw [(H A).1 _ _ (h2 i)]; abel)
  choose τ₀ hτ₀ using fun i => ex ![(h i).left, (h i).left] ![-1, -1] (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
    rw [← neg_add, (H _).2.1 _ (hh i), neg_zero])
  obtain ⟨j, hj⟩ := ex ![(𝟙 A : A ⟶ A).left, (GrpObj.inv : A ⟶ A).left] ![1, -1] (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
    rw [← (H A).2.2 (𝟙 A), ← comp_inv', Category.id_comp, add_neg_cancel])
  have rψ : ∀ i (x : A ⟶ A), Rep M (of x.left - of (x ≫ tr (h i)).left + of (toUnit A ≫ h i).left) (pl x.left (ψ i)) :=
    fun i x => ((hψ i).pull x.left).form (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul,
        map_add, map_neg, map_of_apply, ← Over.comp_left, Category.comp_id, comp_toUnit_assoc, sub_eq_add_neg])
  have rj : ∀ x : A ⟶ A, Rep M (of x.left - of (x ≫ GrpObj.inv).left) (pl x.left j) :=
    fun x => (hj.pull x.left).form (by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul,
        map_add, map_neg, map_of_apply, ← Over.comp_left, Category.comp_id, sub_eq_add_neg])
  let τ : κ → Vals M A.left := fun i => pl (toUnit A).left (τ₀ i)
  have rτ : ∀ i, Rep M (-of (toUnit A ≫ h i).left - of (toUnit A ≫ h i).left) (τ i) :=
    fun i => ((hτ₀ i).pull (toUnit A).left).form (by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul,
        map_add, map_neg, map_of_apply, ← Over.comp_left, sub_eq_add_neg])
  have cτ : ∀ i (x : A ⟶ A), pl x.left (τ i) = τ i := fun i x => by
    simp only [τ]
    rw [pl_pl, ← Over.comp_left, comp_toUnit]
  have p₁ : ∀ f : Vals M A.left, pl (𝟙 A : A ⟶ A).left f = f := fun f => pl_id f
  have rψ₁ := fun i => p₁ _ ▸ rψ i (𝟙 A)
  have rj₁ := p₁ _ ▸ rj (𝟙 A)
  simp only [Category.id_comp] at rψ₁ rj₁
  have rv : ∀ i, Rep M (of (𝟙 _) + of (𝟙 _) - of (tr (h i)).left - of (tr (h i)).left) (ψ i * ψ i * τ i) := fun i =>
    (((rψ₁ i).mul (rψ₁ i)).mul (rτ i)).form (by rw [Over.id_left]; abel)
  choose a ha using fun i => base _ (((rv i).mul (((rψ i (tr (h i))).mul (rψ i (tr (h i)))).mul (rτ i))).form (by
    rw [tt, Over.id_left]; abel))
  have α : ∀ i (x : A ⟶ A), pl x.left (ψ i * pl (tr (h i)).left (ψ i) * τ i) = ψ i * pl (tr (h i)).left (ψ i) * τ i :=
    fun i => cst _ ((((rψ₁ i).mul (rψ i (tr (h i)))).mul (rτ i)).form (by rw [tt]; abel))
  have E := fun {p q : Vals M A.left} (e : p = q) => congrArg Additive.ofMul e
  refine ⟨fun i => ψ i * ψ i * τ i, j * j, a, rv, (rj₁.mul rj₁).form (by rw [Over.id_left]; abel), fun i => ?_,
    fun i k => ?_, fun i => ?_⟩
  · rw [← ha, map_mul, map_mul, cτ]
  · have e := cst _ ((((rψ₁ i).mul (rψ k (tr (h i)))).mul ((rψ₁ k).mul (rψ i (tr (h k)))).inv).form (by
      rw [tc]; abel)) (tr (h i))
    have e' := α i (tr (h k))
    simp only [map_mul, map_inv, pp, cτ, tt, p₁, tc k i] at e e' ⊢
    have a₁ := E e; have a₂ := E e'
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ ⊢
    linear_combination (norm := abel) -a₁ - a₂
  · have e := cst _ ((((rψ₁ i).mul (rj (tr (h i)))).mul (rj₁.mul (rψ i GrpObj.inv)).inv).form (by
      rw [tr_inv (hh i)]; abel)) GrpObj.inv
    have e' := cst _ ((rj₁.mul (rj GrpObj.inv)).form (by rw [ii]; abel)) (tr (h i))
    simp only [map_mul, map_inv, pp, cτ, ii, p₁, tr_inv (hh i)] at e e' ⊢
    have a₁ := E e; have a₂ := E e'
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₂ - a₁

end Core

open FreeAbelianGroup in
set_option maxHeartbeats 1000000 in

theorem main : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (g : ℕ) (i₀ : (Multiplicative (Fin (2 * g) → ZMod 2)) →* (𝟙_ (Over (Sp R)) ⟶ c.A)), c.Principal → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧ ∀ (A : Over (Sp R₁)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ c.A.left) (i : (Multiplicative (Fin (2 * g) → ZMod 2)) →* (𝟙_ (Over (Sp R₁)) ⟶ A)) (L : LB A.left), IsGrpPullback A c.A (spMap (algebraMap R R₁)) φ → (∀ a, (i a).left ≫ φ = spMap (algebraMap R R₁) ≫ (i₀ a).left) → L = lbPow (c.diag.pull φ) 2 → ∃ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1])) (j : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, -1])), (∀ c, (u c).IsGen) ∧ (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c')) (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) ∧ j.IsGen ∧ ∀ c (T : Over (Sp R₁)) (x : T ⟶ A) (z : T.left) (J), Good L z J → val (u c) x.left z J * val j ((toUnit T ≫ i c) * x).left z J = val j x.left z J * val (u c⁻¹) (x⁻¹).left z J := by
  intro hL h k o _ ζ R _ _ _ β c g i₀ hc
  have hM : c.diag.IsLB := pull_isLB c.isLB _
  obtain ⟨v, j, a, rv, rj, h₁, h₂, h₃⟩ := core hL.globalFns c.ab hM (cls_diag hL.globalFns c hc hM)
    (fun n => i₀ (bas n)) (fun n => by rw [← map_mul, mul_self_eq, map_one])
  obtain ⟨R₁, _, _, hR, hb⟩ := exists_sqrt (2 * g) R fun n =>
    Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom (a n)
  refine ⟨R₁, inferInstance, inferInstance, hR, fun A _ _ φ i L hφ hi hLe => ?_⟩
  subst hLe
  have hb' : ∀ n, ∃ b : Γ(Sp R₁, ⊤)ˣ, b * b = pullU (spMap (algebraMap R R₁)) ⊤ (a n) := fun n => by
    obtain ⟨b, e⟩ := hb n
    have e' : (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom b * (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom b =
        (pullU (spMap (algebraMap R R₁)) ⊤ (a n)).val := by
      rw [← map_mul, ← pow_two, e]
      have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (a n).val))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R R₁)))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply] at this
      exact this
    have hu := isUnit_of_mul_isUnit_left (e' ▸ Units.isUnit _)
    exact ⟨hu.unit, Units.ext e'⟩
  choose b hb' using hb'
  have htr : ∀ q, (tr (i q)).left ≫ φ = φ ≫ (tr (i₀ q)).left := fun q => by
    let x₀ := pushPt hφ.1.w (𝟙 A)
    have e := hφ.2 A (toUnit A ≫ i q) (𝟙 A) (toUnit _ ≫ i₀ q) x₀ (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hi]
      exact Category.assoc _ _ _) rfl
    rw [← comp_tr, Over.comp_left] at e
    exact e.symm.trans (congrArg (· ≫ _) (Category.id_comp φ))
  have hinv : (GrpObj.inv : A ⟶ A).left ≫ φ = φ ≫ (GrpObj.inv : c.A ⟶ c.A).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom hφ A) (𝟙 A))
    rw [← comp_inv', ← comp_inv', Category.id_comp] at e
    exact e.trans (congrArg (· ≫ _) (Category.id_comp φ))
  let ρ : Multiplicative (Fin (2 * g) → ZMod 2) →* Monoid.End (Vals c.diag A.left) :=
    { toFun := fun q => pl (tr (i q)).left
      map_one' := MonoidHom.ext fun f => by rw [map_one, tr_one]; exact pl_id f
      map_mul' := fun q q' => MonoidHom.ext fun f => by
        show _ = pl (tr (i q)).left (pl (tr (i q')).left f)
        rw [pl_pl, ← Over.comp_left, tr_tr, mul_comm q, map_mul] }
  have ρe : ∀ q f, ρ q f = pl (tr (i q)).left f := fun _ _ => rfl
  have ρφ : ∀ q (f : Vals c.diag c.A.left), pl (tr (i q)).left (pl φ f) = pl φ (pl (tr (i₀ q)).left f) := fun q f => by rw [pl_pl, pl_pl, htr]
  have ρb : ∀ (x : A ⟶ A) (f : Vals c.diag (Sp R₁)), pl x.left (pl A.hom f) = pl A.hom f := fun x f => by
    rw [pl_pl, Over.w]
  have iφ : ∀ f : Vals c.diag c.A.left, pl (GrpObj.inv : A ⟶ A).left (pl φ f) =
      pl φ (pl (GrpObj.inv : c.A ⟶ c.A).left f) := fun f => by rw [pl_pl, pl_pl, hinv]
  have ii : ∀ q, i q * i q = 1 := fun q => by rw [← map_mul, mul_self_eq, map_one]
  obtain ⟨u, hu, hu'⟩ := exists_cocycle ρ (fun q f =>
      Rep c.diag (of φ + of φ - of ((tr (i q)).left ≫ φ) - of ((tr (i q)).left ≫ φ)) f ∧
      f * ρ q (pl φ j) = pl φ j * pl (GrpObj.inv : A ⟶ A).left f)
    ⟨(map_one (uv c.diag A.left) ▸ rep_uv 1).form (by rw [map_one, tr_one, Over.id_left, Category.id_comp]; abel),
      by simp⟩
    (fun q q' f f' hf hf' => ⟨(hf.1.mul (hf'.1.pull (tr (i q)).left)).form (by
        simp only [map_add, map_sub, map_of_apply]
        rw [← Category.assoc, ← Over.comp_left, tr_tr, mul_comm q, map_mul]; abel), by
      have e : pl (GrpObj.inv : A ⟶ A).left (ρ q f') = ρ q (pl (GrpObj.inv : A ⟶ A).left f') := by
        rw [ρe, ρe, pl_pl, pl_pl, ← Over.comp_left, ← Over.comp_left, tr_inv (ii q)]
      rw [map_mul ρ, Monoid.End.coe_mul, Function.comp_apply, _root_.mul_assoc, ← map_mul, hf'.2, map_mul, ← _root_.mul_assoc, hf.2,
        map_mul, e, _root_.mul_assoc]⟩)
    (fun n => pl φ (v n) * pl A.hom (uv _ _ (b n)⁻¹))
    (fun n => ⟨(((rv n).pull φ).mul ((rep_uv _).pull A.hom)).form (by
        simp only [map_add, map_sub, map_of_apply, map_zero, htr, Category.comp_id, add_zero]), by
      rw [ρe, ρφ, map_mul, ρb, iφ, mul_right_comm, ← map_mul, h₃, map_mul, _root_.mul_assoc]⟩)
    (fun n => by
      rw [ρe, map_mul, ρb, ρφ, _root_.mul_mul_mul_comm, ← map_mul, h₁, pl_pl, hφ.1.w, ← pl_pl, pl_uv (spMap _), ← hb',
        ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← mul_inv, mul_inv_cancel, map_one, map_one])
    (fun n m => by
      rw [ρe, ρe, map_mul, map_mul, ρb, ρb, ρφ, ρφ, _root_.mul_mul_mul_comm, ← map_mul (pl φ), h₂, map_mul (pl φ)]
      ac_rfl)
  have hM' : (c.diag.pull φ).IsLB := pull_isLB hM φ
  have hL' : (lbPow (c.diag.pull φ) 2).IsLB := LB.isLB_linComb hM' _ _
  let D : Vals (lbPow (c.diag.pull φ) 2) A.left →* Vals c.diag A.left :=
    (dn c.diag φ 1 A.left).comp (dn (c.diag.pull φ) (𝟙 _) ((2 : ℕ) : ℤ) A.left)
  have Dpl : ∀ (x : A.left ⟶ A.left) f, D (pl x f) = pl x (D f) := fun _ _ => rfl
  have Dinj : ∀ {E} {f f'}, Rep (lbPow (c.diag.pull φ) 2) E f → Rep (lbPow (c.diag.pull φ) 2) E f' → D f = D f' →
      f = f' := fun {E f f'} hf hf' e => by
    obtain ⟨a, ha⟩ := ((hf.mul hf'.inv).form (add_neg_cancel _)).zero hL'
    have : uv c.diag A.left a = 1 := by
      have := congrArg D ha
      rw [map_mul, map_inv, e, mul_inv_cancel] at this
      exact this.symm
    exact mul_inv_eq_one.1 (ha.trans (uv_eq_one hM _ this))
  have down : ∀ (x : A.left ⟶ A.left) f, Rep c.diag (of φ + of φ - of (x ≫ φ) - of (x ≫ φ)) f →
      ∃ t : LB.Gen (LB.LinComb (lbPow (c.diag.pull φ) 2) (K := Fin 2) ![𝟙 A.left, x] ![1, -1]), t.IsGen ∧
        D (vals t) = f := fun x f hf => by
    obtain ⟨t, ht, e⟩ := Rep.down hM φ 1 (K := Fin 2) ![𝟙 A.left, x] ![2, -2] (hf.form (by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp]; module))
    obtain ⟨t', ht', e'⟩ := Rep.down hM' (𝟙 _) ((2 : ℕ) : ℤ) (K := Fin 2) ![𝟙 A.left, x] ![1, -1] ((rep_vals ht).form (by
      simp [Fin.sum_univ_two]))
    exact ⟨t', ht', (congrArg _ e').trans e⟩
  choose U hU eU using fun q => down _ _ (hu q).1
  obtain ⟨J₀, hJ₀, eJ⟩ := down (GrpObj.inv : A ⟶ A).left (pl φ j) ((rj.pull φ).form (by
    simp only [map_add, map_sub, map_of_apply, hinv, Category.comp_id]))
  have r₂ : ∀ {x : A.left ⟶ A.left} {t : LB.Gen (LB.LinComb (lbPow (c.diag.pull φ) 2) (K := Fin 2) ![𝟙 A.left, x] ![1, -1])},
      t.IsGen → ∀ y : A.left ⟶ A.left, Rep _ (of y - of (y ≫ x)) (pl y (vals t)) := fun ht y =>
    ((rep_vals ht).pull y).form (by simp [Fin.sum_univ_two, sub_eq_add_neg])
  have r₁ := fun q => pl_id (M := lbPow (c.diag.pull φ) 2) _ ▸ r₂ (hU q) (𝟙 _)
  have r₃ := pl_id (M := lbPow (c.diag.pull φ) 2) _ ▸ r₂ hJ₀ (𝟙 _)
  simp only [Category.id_comp] at r₁ r₃
  refine ⟨U, J₀, hU, fun q q' => corr_of_val hL' fun y J hJ => ?_, hJ₀, fun q T x z J hJ => ?_⟩
  · have e := Dinj (r₁ (q * q')) (((r₁ q).mul (r₂ (hU q') (tr (i q)).left)).form (by
      rw [← Over.comp_left, tr_tr, mul_comm q, map_mul]; abel)) (by rw [map_mul D, Dpl, eU, eU, eU, hu', ρe])
    rw [val_mul hJ, val_pull hJ]
    exact congrFun (congrFun (congrFun (congrFun e _) (𝟙 _)) y) ⟨J, hJ⟩
  · have e := Dinj ((r₁ q).mul (r₂ hJ₀ (tr (i q)).left)) ((r₃.mul (r₂ (hU q) (GrpObj.inv : A ⟶ A).left)).form (by
      rw [← Over.comp_left, ← Over.comp_left, tr_inv (ii q)]; abel)) (by
        rw [map_mul D, map_mul D, Dpl, Dpl, eU, eJ, ← ρe, (hu q).2])
    rw [inv_eq_of_mul_eq_one_right (mul_self_eq q), ← comp_tr x (i q), ← comp_inv' x, Over.comp_left, Over.comp_left]
    exact congrFun (congrFun (congrFun (congrFun e _) x.left) z) ⟨J, hJ⟩

end GlobalTheory.SymLin
