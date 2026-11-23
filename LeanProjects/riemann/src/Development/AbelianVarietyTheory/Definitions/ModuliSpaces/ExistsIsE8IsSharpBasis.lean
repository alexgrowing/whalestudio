import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Definitions.Degenerations.LabKerUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZM.Model

theorem isE8_W8 : IsE8 W8 := by
  unfold IsE8
  rw [w8_add_transpose_eq_e8]
  exact ⟨e8_posDef, e8_det_eq_one⟩

theorem not_isE8_one : ¬ IsE8 1 := by
  rintro ⟨-, h⟩
  rw [Matrix.transpose_one, ← two_smul ℤ, Matrix.det_smul] at h
  simp at h

theorem arBase_int : ArBase (Int.castRingHom ℂ) :=
  ⟨inferInstance, inferInstance, RingHom.injective_int _⟩

theorem not_arBase_field {K : Type} [Field K] (em : K →+* ℂ) : ¬ ArBase em := by
  rintro ⟨-, h, -⟩
  haveI : CharZero K := em.charZero
  haveI := h
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ K := finite_of_finite_type_of_isJacobsonRing ℤ K
  have hi : Algebra.IsIntegral ℤ K := inferInstance
  have := (Algebra.IsIntegral.isField_iff_isField (R := ℤ) (S := K) (RingHom.injective_int _)).2 (Field.toIsField K)
  exact Int.not_isField this

section Away
variable {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {n : ℕ} (hn : n ≠ 0)

def awayEmb : Localization.Away (n : 𝓞 F) →+* ℂ :=
  IsLocalization.Away.lift (n : 𝓞 F) (g := φ.comp (algebraMap (𝓞 F) F)) (by simpa using hn)

theorem arBase_away : ArBase (awayEmb φ hn) := by
  have hn' : (n : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  have hM : Submonoid.powers (n : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) := powers_le_nonZeroDivisors_of_noZeroDivisors hn'
  haveI : IsDomain (Localization.Away (n : 𝓞 F)) := IsLocalization.isDomain_localization hM
  refine ⟨IsLocalization.isDedekindDomain (𝓞 F) hM _, ?_, ?_⟩
  · have h1 : Algebra.FiniteType ℤ (𝓞 F) := inferInstance
    have h2 : Algebra.FiniteType (𝓞 F) (Localization.Away (n : 𝓞 F)) := inferInstance
    convert h1.trans h2
    · rfl
    · exact Subsingleton.elim _ _
  · unfold awayEmb IsLocalization.Away.lift
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      rw [IsLocalization.injective _ hM h]
    · intro h
      have : x = y := (φ.injective.comp (RingOfIntegers.coe_injective)) h
      rw [this]

def tbaseAway (z : 𝓞 F) (hz : IsPrimitiveRoot z n) : TBase (Localization.Away (n : 𝓞 F)) n where
  ζ := Units.map (algebraMap (𝓞 F) (Localization.Away (n : 𝓞 F))).toMonoidHom (hz.isUnit hn).unit
  unit := by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (n : 𝓞 F)) (n : 𝓞 F)
  prim := by
    intro K _ β
    have hu : IsUnit (n : Localization.Away (n : 𝓞 F)) := by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (n : 𝓞 F)) (n : 𝓞 F)
    haveI : NeZero (n : K) := ⟨by simpa using (hu.map β).ne_zero⟩
    have h0 := (hz.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map
      (f := β.comp (algebraMap (𝓞 F) (Localization.Away (n : 𝓞 F))))
    rw [Polynomial.map_cyclotomic] at h0
    simpa using Polynomial.isRoot_cyclotomic_iff.1 h0
end Away

section Basis
variable (h : ℕ)

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem halves_inl (g : ℕ) (a : Fin g) : (halves g (.inl a) : ℕ) = a := by simp [halves]
theorem halves_inr (g : ℕ) (a : Fin g) : (halves g (.inr a) : ℕ) = g + a := by simp [halves, add_comm]

theorem sum_halves (g : ℕ) (i j : Fin (2 * g)) :
    ∑ a : Fin g, ((Pi.single i 1 : Fin (2 * g) → ℤ) (halves g (.inl a)) * (Pi.single j 1 : Fin (2 * g) → ℤ) (halves g (.inr a)) -
      (Pi.single i 1 : Fin (2 * g) → ℤ) (halves g (.inr a)) * (Pi.single j 1 : Fin (2 * g) → ℤ) (halves g (.inl a))) =
      Out.stdSymp g i j := by
  obtain ⟨i, rfl⟩ := (halves g).surjective i
  obtain ⟨j, rfl⟩ := (halves g).surjective j
  unfold Out.stdSymp
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Pi.single_apply, (halves g).injective.eq_iff, halves_inl, halves_inr, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, if_false, mul_zero, zero_mul, sub_zero, zero_sub, ite_mul, one_mul, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  all_goals
    try simp only [Fin.ext_iff]
    have := i.2
    have := j.2
    split_ifs <;> omega

def sharpBas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) where
  toFun x u := Sum.elim (fun i => x (halves _ (.inl (finProdFinEquiv (u, i)))))
    (fun i => ∑ v, E8inv u v * x (halves _ (.inr (finProdFinEquiv (v, i)))))
  invFun y k := Sum.elim (fun a => y (finProdFinEquiv.symm a).1 (.inl (finProdFinEquiv.symm a).2))
    (fun a => ∑ v, E8 (finProdFinEquiv.symm a).1 v * y v (.inr (finProdFinEquiv.symm a).2)) ((halves _).symm k)
  map_add' x y := by
    funext u i; rcases i with i | i <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext u i; rcases i with i | i <;> simp [Finset.mul_sum, mul_left_comm]
  left_inv x := by
    funext k
    obtain ⟨k, rfl⟩ := (halves _).surjective k
    rcases k with a | a
    · simp only [Equiv.symm_apply_apply, Sum.elim_inl, Prod.mk.eta, Equiv.apply_symm_apply]
    · obtain ⟨⟨u, i⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp only [Equiv.symm_apply_apply, Sum.elim_inr, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Matrix.mul_apply, e8_mul_e8inv, Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
  right_inv y := by
    funext u i
    rcases i with i | i
    · simp only [Equiv.symm_apply_apply, Sum.elim_inl]
    · simp only [Equiv.symm_apply_apply, Sum.elim_inr, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Matrix.mul_apply, e8inv_mul_e8, Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem dual_sum (y : Fin 8 → ℤ) (u : Fin 8) : ∑ v, E8 u v * ∑ w, E8inv v w * y w = y u := by
  have : E8.mulVec (E8inv.mulVec y) = y := by rw [Matrix.mulVec_mulVec, e8_mul_e8inv, Matrix.one_mulVec]
  exact congrFun this u

theorem sharp_form (x x' : Fin (2 * (8 * h)) → ℤ) :
    ∑ u, ∑ v, E8 u v * omegaStd (sharpBas h x u) (sharpBas h x' v) =
      ∑ a : Fin (8 * h), (x (halves _ (.inl a)) * x' (halves _ (.inr a)) - x (halves _ (.inr a)) * x' (halves _ (.inl a))) := by
  have hs : ∀ u v, E8 u v = E8 v u := fun u v => congrFun (congrFun e8_transpose v) u
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  have key : ∀ (A B : Fin 8 → Fin h → ℤ), ∑ u, ∑ v, ∑ i, E8 u v * (A u i * ∑ w, E8inv v w * B w i) = ∑ u, ∑ i, A u i * B u i := by
    intro A B
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← dual_sum (fun w => B w i) u, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have k1 := key (fun u i => x (halves _ (.inl (finProdFinEquiv (u, i))))) (fun u i => x' (halves _ (.inr (finProdFinEquiv (u, i)))))
  have k2 := key (fun u i => x' (halves _ (.inl (finProdFinEquiv (u, i))))) (fun u i => x (halves _ (.inr (finProdFinEquiv (u, i)))))
  rw [Finset.sum_comm] at k2
  simp only [Finset.sum_sub_distrib]
  rw [← k1, show (∑ u, ∑ i, x (halves _ (.inr (finProdFinEquiv (u, i)))) * x' (halves _ (.inl (finProdFinEquiv (u, i))))) =
    ∑ u, ∑ i, x' (halves _ (.inl (finProdFinEquiv (u, i)))) * x (halves _ (.inr (finProdFinEquiv (u, i)))) from by
      simp only [mul_comm], ← k2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_sub_distrib, omegaStd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hs v u]
  simp only [sharpBas, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
  ring

theorem isSharpBasis_sharpBas : IsSharpBasis W8 (sharpBas h) := by
  intro i j
  rw [w8_add_transpose_eq_e8, sharp_form, sum_halves]

end Basis

theorem exists_isE8_isSharpBasis : ∃ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W ∧ ∀ h : ℕ,
    ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas :=
  ⟨W8, isE8_W8, fun h => ⟨sharpBas h, isSharpBasis_sharpBas h⟩⟩

theorem eq_eight_mul {g h : ℕ} (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) : g = 8 * h := by
  have := bas.finrank_eq
  simp [Module.finrank_pi_fintype] at this
  omega

section Use
open AlgebraicGeometry CategoryTheory MonObj
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

theorem act_mul_act_of_isPEL {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {a : J → 𝓞 E}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {ρ : o} {t : TObj g k J b s} {τ : SAB H S} (ht : IsPEL D a bas ρ t τ)
    {w w' : J} (hw : a w + a w' = 1) : t.act w * t.act w' = 𝟙 t.A := by
  obtain ⟨φ, hφ, -, h, -⟩ := ht
  rw [← cancel_epi φ.hom, MonObj.comp_mul, ← h, ← h, ← MonObj.mul_comp, ← τ.act.add, hw, τ.act.one]
  simp

theorem act_one_of_isSharp {h : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {t : TObj g k J b s} {c : SiegPre h k (b.ζ : o) s}
    (ht : IsSharp W a bas t c) {j : J} (hj : a j = 1) : t.act j = 𝟙 t.A := by
  obtain ⟨pr, -, hu, -, h, -⟩ := ht
  refine (hu t.A pr).unique (fun u => ?_) (fun u => by simp)
  rw [h, hj, List.prod_ofFn, Finset.prod_eq_single u] <;> simp +contextual [Matrix.one_apply, eq_comm]
end Use

section Zero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi Out.Inh
open scoped CategoryTheory.Obj
variable {o : Type} [CommRing o] {S : Scheme.{0}} {k : ℕ} {J : Type}

theorem corr_comm_pull {X X' Y : Scheme.{0}} (f : X ⟶ X') {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb ((trivLB X').pull f) φ ε)) (b : LB.Gen (LB.LinComb ((trivLB X').pull f) φ' ε)) (h h' : Y ⟶ Y)
    (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb ((trivLB X').pull f) (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr ((trivLB X').pull f) _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j'
  obtain rfl : j = fun _ _ => PUnit.unit := rfl
  obtain rfl : j' = fun _ _ => PUnit.unit := rfl
  intro _ _ _
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, ZH.RealModel.res_res, ZH.RealModel.res_res]
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (ZH.RealModel.res_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (ZH.RealModel.res_res _ _ _)
  · exact (ZH.RealModel.res_res _ _ _).symm

theorem isGen_one {X : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) : (⟨fun _ => 1⟩ : L.Gen).IsGen := by
  intro i j; rw [hL, _root_.one_mul]; exact (map_one _).trans (map_one _).symm

theorem weil_pull_zero {X : Scheme.{0}} (f : (𝟙_ (Over S)).left ⟶ X) (n : ℤ) {T : Over S} (x y : T ⟶ 𝟙_ (Over S)) :
    Out.WeilIs (𝟙_ (Over S)) ((trivLB X).pull f) n x y 1 := by
  intro p
  refine ⟨⊤, trivial, ⟨⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩,
    ⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩, rfl, rfl⟩, ?_⟩
  intro θx θy _ _
  have hc : Out.unitRes (T := T) ⊤ 1 = 1 := map_one _
  rw [hc]
  exact corr_comm_pull _ _ _ _ _ _ _ _ (ZH.RealModel.translT_id S _) (ZH.RealModel.translT_id S _) _
    (fun j => (congrArg _ (map_one _)).trans (ZH.RealModel.res_one _))

theorem relAmple_unit (M : LB (𝟙_ (Over S)).left) (hg : ∀ i j, M.g i j = 1) (i₀ : M.ι) (hi₀ : M.U i₀ = ⊤) :
    Out.RelAmple (𝟙_ (Over S)) M := by
  intro U hU
  haveI : IsIso (𝟙_ (Over S)).hom := by show IsIso (𝟙 S); infer_instance
  let Y := ((𝟙_ (Over S)).hom ⁻¹ᵁ U).toScheme
  have hp : ∀ i j, (Out.powOver (𝟙_ (Over S)) M U 1).g i j = 1 := fun i j => by
    exact linComb_g_one M hg _ _ i j
  let s0 : LB.Sec (Out.powOver (𝟙_ (Over S)) M U 1) :=
    ⟨fun _ => 1, by
      intro i j; rw [hp, Units.val_one, _root_.one_mul]; repeat erw [map_one]
      all_goals rfl⟩
  have hD : Out.nonzeroLocus s0 = ⊤ := by
    apply top_unique
    intro x _
    simp only [Out.nonzeroLocus, s0, Scheme.basicOpen_one]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i₀, Set.mem_iInter.2 fun _ => by
      show _ ∈ M.U i₀
      rw [hi₀]; trivial⟩
  refine ⟨1, le_rfl, 0, fun _ => s0, by simp only [iSup_const]; exact hD,
    fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
  · rw [hD]
    have : IsAffine Y := hU
    exact isAffineOpen_top Y
  · intro j k
    erw [map_one]; (try erw [map_one]); (try erw [map_one]); exact (_root_.mul_one _).symm
  · intro p
    obtain ⟨a, rfl⟩ := surj_appLE ((𝟙_ (Over S)).hom ∣_ U) _ hD le_top p
    exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩

def zeroSieg (ζ : o) (s : S ⟶ Sp o) : SiegPre 0 k ζ s where
  A := 𝟙_ (Over S)
  ab := UU.isAbelianScheme_unit S
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  rig₂ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 𝟙 _
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
    fun g _ => ⟨0, toUnit_unique _ _⟩, fun a b => by
      have : unitOn (z ^ (2 * omegaStd a b)) = 1 := by simp [omegaStd, unitOn]
      rw [this]; exact weil_pull_zero _ _ _ _⟩

theorem isSharp_zero (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas) (b : TBase o k) (s : S ⟶ Sp o) :
    IsSharp W a bas (zeroObj J b s) (zeroSieg (b.ζ : o) s) :=
  ⟨fun _ => 𝟙 _, fun _ => inferInstanceAs (IsMonHom (𝟙 (𝟙_ (Over S)))),
    fun T y => ⟨toUnit T, fun _ => toUnit_unique _ _, fun _ _ => toUnit_unique _ _⟩,
    lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _), fun _ _ => toUnit_unique _ _, fun i => i.elim0⟩

theorem zeroSieg_principal (ζ : o) (s : S ⟶ Sp o) : (zeroSieg (k := k) ζ s).Principal :=
  ⟨relAmple_unit _ (linComb_triv_g _ _) (fun _ => PUnit.unit) (ZH.RealModel.wchart_triv _ _),
    fun _ _ _ => toUnit_unique _ _⟩

theorem sharpClass_zero (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas) (b : TBase o k) (em : o →+* ℂ) :
    SharpClass (h := 0) W a bas em (zeroObj J b (spMap em)) :=
  ⟨_, zeroSieg_principal _ _, isSharp_zero W a bas b _⟩

theorem isPEL_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : J → 𝓞 E) (bas) (ρ : ℂ) (hk : k ≠ 0)
    (s : S ⟶ Sp ℂ) : IsPEL (Test.zeroDatum H) a bas ρ (zeroObj J (baseC k hk) s) (Models.Inhab.zeroTriple H S) := by
  refine ⟨Iso.refl _, inferInstanceAs (IsMonHom (𝟙 (𝟙_ (Over S)))), lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _),
    fun _ => toUnit_unique _ _, fun K _ _ _ x β _ => ⟨fun τ => ?_, ?_⟩⟩
  · have : LieMult (Models.Inhab.zeroTriple H S).act x τ 0 :=
      ⟨fun i => i.elim0, fun i => i.elim0, fun w _ => ⟨fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0, toUnit_unique _ _⟩,
        fun _ _ => Subsingleton.elim _ _⟩⟩
    exact ⟨fun _ => this, fun _ => this⟩
  · refine ⟨⟨fun n => Units.mk0 (β (Complex.exp (2 * Real.pi * Complex.I / n))) (by simp), fun n hn => ?_, fun n m hn hm => ?_,
      fun _ _ => toUnit _, fun _ _ _ => toUnit_unique _ _, fun _ _ _ => toUnit_unique _ _,
      fun _ _ _ => ⟨fun _ => ⟨PUnit.unit, rfl⟩, fun _ => toUnit_unique _ _⟩,
      fun _ _ _ => ⟨fun _ => ⟨PUnit.unit, toUnit_unique _ _⟩, fun _ => toUnit_unique _ _⟩,
      fun _ _ _ _ _ => toUnit_unique _ _, fun n _ u v => ?_⟩, rfl, fun i => i.elim0⟩
    · rw [← IsPrimitiveRoot.coe_units_iff]
      exact (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective β.injective
    · ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, ← Complex.exp_nat_mul]
      congr 2
      have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
      push_cast
      field_simp
    · have : ∀ z : Kˣ, unitOn (z ^ (Test.zeroDatum H).EF u v) = 1 := fun z => by
        show unitOn (z ^ (0 : ℤ)) = 1
        simp [unitOn]
      rw [this]
      exact ZH.RealModel.weil_zero S _ _ _

theorem pelClass_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : J → 𝓞 E) (bas) (ρ : ℂ) (hk : k ≠ 0) :
    PELClass (Test.zeroDatum H) a bas ρ (RingHom.id ℂ) (zeroObj J (baseC k hk) _) :=
  ⟨_, isPEL_zero H a bas ρ hk _⟩

theorem pt_act_of_pelClass {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ}
    {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {ρ : o} {b : TBase o k} {em : o →+* ℂ} {t : TObj g k J b (spMap em)}
    (ht : PELClass D a bas ρ em t) (j : J) (i : Fin (2 * g)) :
    t.pt i ≫ t.act j = (List.ofFn fun i' => t.pt i' ^ (bas.symm (a j • bas (Pi.single i 1)) i')).prod := by
  obtain ⟨τ, φ, hφ, -, hact, h⟩ := ht
  obtain ⟨-, I, -, hI⟩ := h ℂ (𝟙 _) em (Category.id_comp _)
  have hI' : ∀ i, I.ev k (bas (Pi.single i 1)) ≫ φ.hom = t.pt i := fun i => (hI i).trans (Category.id_comp _)
  haveI := t.ab.comm
  let f : D.La →+ Additive (Out.baseOver (Sp ℂ) ⟶ t.A) :=
    AddMonoidHom.mk' (fun v => Additive.ofMul (I.ev k v ≫ φ.hom)) fun u v => by
      rw [I.add, MonObj.mul_comp]; rfl
  have e : a j • bas (Pi.single i 1) = ∑ i', bas.symm (a j • bas (Pi.single i 1)) i' • bas (Pi.single i' 1) := by
    simp only [← map_zsmul, ← map_sum]
    rw [← LinearEquiv.symm_apply_eq]
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  have := congrArg f e
  rw [map_sum] at this
  simp only [map_zsmul] at this
  rw [List.prod_ofFn, ← hI' i, Category.assoc, ← hact, ← Category.assoc]
  refine (congrArg (· ≫ φ.hom) (I.lin k (a j) _).symm).trans ((congrArg Additive.toMul this).trans ?_)
  rw [toMul_sum]
  exact Finset.prod_congr rfl fun l _ => by rw [← hI' l]; rfl

theorem act_comp_of_isSharp {h g : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ} {b : TBase o k}
    {s : S ⟶ Sp o} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {t : TObj g k J b s}
    {c : SiegPre h k (b.ζ : o) s} (ht : IsSharp W a bas t c) {j j' l : J} (hl : a l = a j' * a j) :
    t.act j ≫ t.act j' = t.act l := by
  obtain ⟨pr, -, hu, -, h, -⟩ := ht
  refine (hu t.A fun u => t.act l ≫ pr u).unique (fun u => ?_) (fun u => rfl)
  let f : (t.A ⟶ c.A) →* (t.A ⟶ c.A) := MonoidHom.mk' (fun y => t.act j ≫ y) fun _ _ => MonObj.comp_mul _ _ _
  have hf : ∀ y, t.act j ≫ y = f y := fun _ => rfl
  rw [Category.assoc, h j', hf, h l, List.prod_ofFn, List.prod_ofFn, map_prod]
  simp only [map_zpow]
  simp only [← hf, h j, List.prod_ofFn, ← Finset.prod_zpow, ← zpow_mul, hl, Matrix.mul_apply]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => ?_
  have := map_prod (zpowersHom _ (pr v)) (fun x => Multiplicative.ofAdd (a j' u x * a j x v)) Finset.univ
  rw [← ofAdd_sum] at this
  simp only [zpowersHom_apply, toAdd_ofAdd] at this
  rw [this]
  exact Finset.prod_congr rfl fun x _ => by rw [_root_.mul_comm]
end Zero

end GlobalTheory.ZM.Model
end
