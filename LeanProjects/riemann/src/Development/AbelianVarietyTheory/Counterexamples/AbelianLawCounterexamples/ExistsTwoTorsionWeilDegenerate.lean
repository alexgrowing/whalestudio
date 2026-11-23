import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLawZeroCounterexample

open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

theorem laws : WeilSt ∧ WeilNondegSt ∧ CharPairSt :=
  have h := GlobalTheory.AbLaw.FromCube.all_of_cubeGen GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem lifts : ∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 →
    ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x :=
  (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).2.2

theorem skew {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : WeilIs P.A P.L k x y c) : WeilIs P.A P.L k y x c⁻¹ :=
  (GlobalTheory.weilIs_alternating_skew_natural GlobalTheory.laws_without_cohomology.1 lifts S P k T).2.1 x y c h

theorem mul_right {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ) {T : Over S}
    {x y y' : T ⟶ P.A} {c c' : Γ(T.left, ⊤)ˣ}
    (h : WeilIs P.A P.L k x y c) (h' : WeilIs P.A P.L k x y' c') :
    WeilIs P.A P.L k x (y * y') (c * c') := by
  have := skew P k ((laws.1 S P k T).2.1 _ _ _ _ _ (skew P k h) (skew P k h'))
  rwa [← mul_inv, inv_inv] at this

def zeroLift {S : Scheme.{0}} (P : PolAV S) {T : Over S} (x : T ⟶ P.A) : ThetaGrp P.A P.L ((0 : ℕ) : ℤ) T where
  pt := x
  φ := ⟨fun _ => 1⟩
  isGen := by
    intro i j
    have h : (thetaLB P.A P.L ((0 : ℕ) : ℤ) x).g i j = 1 := by
      unfold thetaLB LB.LinComb
      dsimp only
      refine (Fin.prod_univ_two _).trans ?_
      exact (congrArg₂ (· * ·) (zpow_zero _) (zpow_zero _)).trans (_root_.mul_one _)
    rw [h]
    exact (map_one _).trans ((_root_.one_mul _).trans (map_one _)).symm

theorem weilIs_zero {S : Scheme.{0}} (P : PolAV S) {T : Over S} (x y : T ⟶ P.A) :
    WeilIs P.A P.L ((0 : ℕ) : ℤ) x y 1 := by
  have g := GlobalTheory.laws_without_cohomology.1
  refine ((GlobalTheory.weilIs_iff_commIsOf_and_lift_subsingleton g lifts
    (GlobalTheory.symLift_odd g lifts (GlobalTheory.exists_gen_negLB g)).1 S P 0 T).1 (zeroLift P x) (zeroLift P y) 1).2 ?_
  intro j j' _ _ _
  have h : ∀ {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) {a : Γ(X, U)ˣ}, a = 1 → res h a = 1 :=
    fun h a e => e ▸ map_one _
  have m : ∀ {G : Type} [Monoid G] {a b : G}, a = 1 → b = 1 → a * b = 1 :=
    fun ha hb => by rw [ha, hb, _root_.mul_one]
  refine (h _ (m (h _ rfl) (h _ (h _ (map_one _))))).trans (h _ ?_).symm
  exact m (h _ (m (h _ rfl) (h _ (h _ (map_one _))))) (h _ (h _ (map_one _)))

def curve (K : Type) [Field K] : _root_.WeierstrassCurve K := ⟨1, 0, 0, 1, 0⟩

theorem isElliptic_curve (K : Type) [Field K] (h : (63 : K) ≠ 0) : (curve K).IsElliptic := ⟨by
  have : (curve K).Δ = -63 := by
    norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
  rw [this]
  exact Ne.isUnit (neg_ne_zero.2 h)⟩

theorem exists_order_two (K : Type) [Field K] (h : (63 : K) ≠ 0) :
    ∃ (P : PolAV (Spec (CommRingCat.of K))) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A),
      P.g = 1 ∧ x ≠ 1 ∧ x ^ 2 = 1 := by
  haveI := isElliptic_curve K h
  have sol : IsUnimodularSol ((curve K).baseChange K) ![0, 0, 1] :=
    isUnimodularSol_some (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [curve])
  let p : specOver K K ⟶ (ellPolAV (curve K)).A := ptOver (curve K) _ sol
  have hinv : p⁻¹ = p := by
    refine (ptOver_inv (curve K) sol).trans
      (Over.OverMorphism.ext (pt_congr (curve K) _ sol.neg ?_ sol))
    simp [curve, WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY]
  have hsq : p ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← hinv]
    exact inv_mul_cancel p
  have hne : p ≠ 1 := by
    intro e
    have e' : ptOver (curve K) _ sol = 1 := e
    rw [one_eq_ptOver] at e'
    obtain ⟨v, hv⟩ := (ptOver_eq_ptOver_iff (curve K) _ _).mp e'.symm
    simpa using congrFun hv 2
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ := Spec.map_id _
  let e : baseOver (Spec (CommRingCat.of K)) ≅ specOver K K :=
    Over.isoMk (Iso.refl _) (by exact (Category.id_comp _).trans h1)
  refine ⟨ellPolAV (curve K), e.hom ≫ p, rfl, fun hx => hne ?_, ?_⟩
  · rw [← cancel_epi e.hom, hx, MonObj.comp_one]
  · rw [← MonObj.comp_pow, hsq, MonObj.comp_one]

theorem exists_value_ne_one :
    ∃ (P : PolAV (Spec (CommRingCat.of ℂ))) (x y : baseOver (Spec (CommRingCat.of ℂ)) ⟶ P.A) (c : _),
      x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ WeilIs P.A P.L ((2 : ℕ) : ℤ) x y c ∧ c ≠ 1 ∧
        ¬ WeilIs P.A P.L ((2 : ℕ) : ℤ) x y 1 := by
  obtain ⟨P, x, -, hx, hx2⟩ := exists_order_two ℂ (by norm_num)
  have := mt (laws.2.1 ℂ P 2 (by norm_num) x hx2) hx
  push_neg at this
  obtain ⟨y, hy, hn⟩ := this
  obtain ⟨c, hc, -⟩ := (laws.1 _ P 2 _).1 x y hx2 hy
  exact ⟨P, x, y, c, hx2, hy, hc, fun e => hn (e ▸ hc), hn⟩

theorem nondeg_fails_at_zero :
    ∃ (P : PolAV (Spec (CommRingCat.of ℂ))) (x : baseOver (Spec (CommRingCat.of ℂ)) ⟶ P.A),
      x ^ 0 = 1 ∧ (∀ y : baseOver _ ⟶ P.A, y ^ 0 = 1 → WeilIs P.A P.L ((0 : ℕ) : ℤ) x y 1) ∧ x ≠ 1 := by
  obtain ⟨P, x, -, hx, -⟩ := exists_order_two ℂ (by norm_num)
  exact ⟨P, x, pow_zero x, fun y _ => weilIs_zero P x y, hx⟩

theorem value_pow {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ) {T : Over S}
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hx : x ^ k = 1) (hy : y ^ k = 1)
    (h : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  obtain ⟨hu, hm, -, -⟩ := laws.1 S P k T
  obtain ⟨d, hd, hd'⟩ := hu 1 y (one_pow k) hy
  have hd1 : d = 1 := by
    have := hm 1 1 y d d hd hd
    rw [_root_.mul_one] at this
    simpa using hd' _ this
  have : ∀ n : ℕ, WeilIs P.A P.L k (x ^ n) y (c ^ n) := by
    intro n
    induction n with
    | zero => simpa [hd1] using hd
    | succ n ih => rw [pow_succ, pow_succ]; exact hm _ _ _ _ _ ih h
  have h2 := this k
  rw [hx] at h2
  exact (hd' _ h2).trans hd1

theorem exists_twoTorsion_weil_degenerate :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (P : PolAV (Spec (CommRingCat.of K)))
      (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A),
      x ^ 2 = 1 ∧ (∀ y : baseOver _ ⟶ P.A, y ^ 2 = 1 → WeilIs P.A P.L ((2 : ℕ) : ℤ) x y 1) ∧ x ≠ 1 := by
  let K := AlgebraicClosure (ZMod 2)
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨P, x, -, hx, hx2⟩ := exists_order_two K (by
    intro h
    have : (1 : K) = 0 := by linear_combination h - 31 * h2
    exact one_ne_zero this)
  refine ⟨K, inferInstance, inferInstance, P, x, hx2, fun y hy => ?_, hx⟩
  obtain ⟨c, hc, -⟩ := (laws.1 _ P 2 _).1 x y hx2 hy
  have hc2 := value_pow P 2 hx2 hy hc
  let e : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) ≃+* K :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have : c = 1 := by
    ext
    apply e.injective
    have h3 : (e c) ^ 2 = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hc2, Units.val_one, map_one]
    have h4 : (e c - 1) ^ 2 = 0 := by linear_combination h3 + (1 - e c) * h2
    rw [Units.val_one, map_one]
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h4)
  exact this ▸ hc

theorem isotropic_at_sq {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (m : ℕ) {T : Over S}
    (hm : IsUnit ((m * m : ℕ) : Γ(T.left, ⊤))) {x y : T ⟶ P.A} (hx : x ^ m = 1) (hy : y ^ m = 1) :
    WeilIs P.A P.L (m * m) x y 1 := by
  obtain ⟨hu, hmul, -, hl⟩ := laws.1 S P m T
  refine (hl m x y 1 hm (by rw [pow_mul, hx, one_pow]) hy).2 ?_
  rw [hx]
  obtain ⟨d, hd, hd'⟩ := hu 1 y (one_pow m) hy
  have hd1 : d = 1 := by
    have := hmul 1 1 y d d hd hd
    rw [_root_.mul_one] at this
    simpa using hd' _ this
  exact hd1 ▸ hd

theorem levels_differ :
    ∃ (P : PolAV (Spec (CommRingCat.of ℂ))) (x y : baseOver (Spec (CommRingCat.of ℂ)) ⟶ P.A),
      x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ WeilIs P.A P.L (((2 : ℕ) : ℤ) * ((2 : ℕ) : ℤ)) x y 1 ∧
        ¬ WeilIs P.A P.L ((2 : ℕ) : ℤ) x y 1 := by
  obtain ⟨P, x, y, c, hx, hy, -, -, hn⟩ := exists_value_ne_one
  refine ⟨P, x, y, hx, hy, isotropic_at_sq P 2 ?_ hx hy, hn⟩
  let e : Γ((baseOver (Spec (CommRingCat.of ℂ))).left, ⊤) ≃+* ℂ :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  have : IsUnit (((2 * 2 : ℕ) : ℂ)) := Ne.isUnit (by norm_num)
  rw [← map_natCast e.symm]
  exact this.map e.symm

end GlobalTheory.PairingLawZeroCounterexample
