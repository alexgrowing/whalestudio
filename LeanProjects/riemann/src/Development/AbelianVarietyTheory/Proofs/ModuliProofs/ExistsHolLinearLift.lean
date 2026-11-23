import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

namespace GlobalTheory.LocLift

noncomputable section

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

theorem exists_hol_linear_lift {B : Set (Fin m → ℂ)} (hB : IsOpen B) {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ} (hr : 0 < r)
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    (f : G ⟶ G) [IsMonHom f] :
    ∃ L : (Fin m → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ b ∈ B, ∀ z, e b (L b z) = e b z ≫ f) ∧
      ∀ z, DifferentiableOn ℂ (fun b => L b z) B := by
  have key : ∀ b₁ ∈ B, ∃ L : (Fin m → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ᶠ b in 𝓝 b₁, ∀ z, e b (L b z) = e b z ≫ f) ∧ ∀ z, DifferentiableAt ℂ (fun b => L b z) b₁ := by
    intro b₁ hb₁
    obtain ⟨ζ, -, h2, h3⟩ := hl.lift (W := B ×ˢ Set.univ) (β := Prod.fst)
      (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2 ≫ f) (w₀ := (b₁, 0)) (z₀ := 0)
      (hB.prod isOpen_univ) ⟨hb₁, trivial⟩ differentiableOn_fst (fun _ h => h.1) (isHolTo_comp_hom hol f.left)
      (by simp only [hom_zero (he b₁ hb₁).1.1, MonObj.one_comp])
    refine ⟨fun b => ((fderiv ℂ ζ (b, 0)).comp (ContinuousLinearMap.inr ℂ _ _)).toLinearMap, ?_, fun z => ?_⟩
    · have ht : Tendsto (fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) (𝓝 b₁) (𝓝 (b₁, 0)) :=
        (Continuous.prodMk_left _).tendsto _
      filter_upwards [hB.mem_nhds hb₁, ht.eventually h2.eventually_analyticAt, ht.eventually h3.eventually_nhds]
        with b hb ha hz z
      have hd := ha.differentiableAt.hasFDerivAt.comp (0 : Fin g → ℂ) (hasFDerivAt_prodMk_right b (0 : Fin g → ℂ))
      have := fderiv_lift (x := fun z => e b z ≫ f) (fun z w => by simp only [(he b hb).1.1, MonObj.mul_comp])
        (he b hb).1.1 (he b hb).1.2.1 hr (he b hb).2 hd.differentiableAt
        (((Continuous.prodMk_right b).tendsto 0).eventually hz) z
      rwa [hd.fderiv] at this
    · have : DifferentiableAt ℂ (fun b : Fin m → ℂ => fderiv ℂ ζ (b, 0) ((0 : Fin m → ℂ), z)) b₁ :=
        (h2.fderiv.differentiableAt.comp b₁ (hasFDerivAt_prodMk_left b₁ (0 : Fin g → ℂ)).differentiableAt).clm_apply
          (differentiableAt_const ((0 : Fin m → ℂ), z))
      exact this
  choose! L h1 h2 using key
  refine ⟨fun b => L b b, fun b hb => (h1 b hb).self_of_nhds, fun z b₁ hb₁ => ?_⟩
  refine ((h2 b₁ hb₁ z).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hB.mem_nhds hb₁, h1 b₁ hb₁] with b hb h
  rw [linear_lift_unique (he b hb).1.1 hr (he b hb).2 (L := L b b) (L' := L b₁ b)
    fun z => ((h1 b hb).self_of_nhds z).trans (h z).symm]

theorem exists_hol_rep {O : Type} [CommRing O] {B : Set (Fin m → ℂ)} (hB : IsOpen B) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B)
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ} (hr : 0 < r)
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    (act : OAct O G) :
    ∃ F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ),
      (∀ b ∈ B, ∀ a z, e b ((F b a).mulVec z) = e b z ≫ act.act a) ∧
      ∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B := by
  classical
  choose L h1 h2 using fun a => haveI := act.hom a; exists_hol_linear_lift hB hr hol he hl (act.act a)
  have key : ∀ b ∈ B, ∃ F : O →+* Matrix (Fin g) (Fin g) ℂ, ∀ a, F a = LinearMap.toMatrix' (L a b) := by
    intro b hb
    have u := fun L L' => linear_lift_unique (he b hb).1.1 hr (he b hb).2 (V := Fin g → ℂ) (L := L) (L' := L')
    refine ⟨RingHom.mk' ⟨⟨fun a => LinearMap.toMatrix' (L a b), ?_⟩, fun a a' => ?_⟩ fun a a' => ?_, fun _ => rfl⟩
    · rw [u (L 1 b) LinearMap.id fun z => by rw [h1 1 b hb, act.one, Category.comp_id, LinearMap.id_apply],
        LinearMap.toMatrix'_id]
    · change LinearMap.toMatrix' (L (a * a') b) = _
      rw [u (L (a * a') b) (L a b ∘ₗ L a' b) fun z => by
        rw [h1 _ b hb, LinearMap.comp_apply, h1 _ b hb, h1 _ b hb, mul_comm, act.mul, Category.assoc],
        LinearMap.toMatrix'_comp]
    · change LinearMap.toMatrix' (L (a + a') b) = LinearMap.toMatrix' (L a b) + LinearMap.toMatrix' (L a' b)
      rw [u (L (a + a') b) (L a b + L a' b) fun z => by
        rw [h1 _ b hb, LinearMap.add_apply, (he b hb).1.1, h1 _ b hb, h1 _ b hb, act.add, MonObj.comp_mul], map_add]
  choose F hF using key
  refine ⟨fun b => if hb : b ∈ B then F b hb else F b₀ hb₀, fun b hb a z => ?_, fun a i j => ?_⟩
  · simp only [dif_pos hb, hF, LinearMap.toMatrix'_mulVec, h1 a b hb]
  · refine (differentiableOn_pi.1 (h2 a (Pi.single j 1)) i).congr fun b hb => ?_
    simp only [dif_pos hb, hF, LinearMap.toMatrix'_apply]

def HasForm {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (P : La → (Fin g → ℂ)) : Prop :=
  ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    ∀ x y, (hermForm Hm (P x) (P y)).im = EF x y

open Matrix in
theorem HasForm.of_comp {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La} {P : La → (Fin g → ℂ)} {g' : ℕ}
    (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hL : Function.Injective L) (h : HasForm EF (fun x => L (P x))) :
    HasForm EF P := by
  obtain ⟨Hm, h1, h2, h3⟩ := h
  let M := LinearMap.toMatrix' L
  have key : ∀ z w, hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [← LinearMap.toMatrix'_mulVec L z, ← LinearMap.toMatrix'_mulVec L w, hermForm, hermForm, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, star_mulVec, ← mulVec_transpose]
    rfl
  refine ⟨Mᵀ * Hm * Mᵀᴴ, isHermitian_mul_mul_conjTranspose _ h1, fun z hz => ?_, fun x y => ?_⟩
  · rw [key]
    exact h2 _ fun h0 => hz (hL (h0.trans (map_zero L).symm))
  · rw [key, h3]

theorem int_eq_of_exp {a b : ℤ} (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (a : ℂ) / k) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (b : ℂ) / k)) : a = b := by
  have hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ b - a := fun k hk => by
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k hk)
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have hp := Complex.two_pi_I_ne_zero
    refine ⟨n, ?_⟩
    have : ((b : ℂ) - a) = k * n := by
      refine mul_left_cancel₀ hp ?_
      field_simp at hn
      linear_combination (2 * Real.pi * Complex.I) * hn
    exact_mod_cast this
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((b - a).natAbs + 1) (Nat.succ_pos _)) (by
    rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem hasForm_of_weil (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt)
    (A : Out.PolAV X) (y₀ y : Sp ℂ ⟶ X) (hy : y = (𝟙_ (Over (Sp ℂ))).hom ≫ y₀)
    {e : (Fin g → ℂ) → (Over.mk y ⟶ A.A)} (he : IsExp y e) {r : ℝ} (hr : 0 < r)
    (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0)
    (hl : ∀ (n : ℕ) (x : (Fin n → ℂ) → (Over.mk y ⟶ A.A)), IsHolTo Set.univ (fun w => (x w).left) → e 0 = x 0 →
      ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), AnalyticAt ℂ ζ 0 ∧ ∀ᶠ w in 𝓝 0, e (ζ w) = x w)
    {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (P : La → (Fin g → ℂ)) (hP : ∀ a, e (P a) = 1)
    (hw : ∀ (k : ℕ) (a a₂ : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs A.A A.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) : HasForm EF P := by
  subst hy
  obtain ⟨A', φ, hφ, -, hm, t, ht⟩ := hB _ _ y₀ A
  have hgp : IsGrpPullback A'.A A.A y₀ φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
    rfl⟩
  obtain ⟨rig, hrig⟩ := A'.rigid
  obtain ⟨u, Hm, χ, Ef, ⟨h1, h2, -⟩, -, -, -, -, -, h3, -, h4⟩ := hT A' rig hrig
  let x : (Fin A'.g → ℂ) → (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ y₀) ⟶ A.A) := fun w => Out.toBase hφ.w (u.ex w)
  have hx : ∀ z w, x (z + w) = x z * x w := fun z w => by simp only [x, u.ex_add, hm]
  have hinj : Function.Injective (fun p : 𝟙_ (Over (Sp ℂ)) ⟶ A'.A => Out.toBase hφ.w p) := fun p q h =>
    Over.OverMorphism.ext (hφ.hom_ext (congrArg (fun s => s.left) h) ((Over.w p).trans (Over.w q).symm))
  have hker : ∀ z, x z = 1 ↔ z ∈ u.Λ := fun z => by
    rw [← u.ker, ← hom_zero hx, ← hom_zero u.ex_add]
    exact hinj.eq_iff
  have hsx : Function.Surjective x := fun q => by
    obtain ⟨w, hw⟩ := u.ex_onto (Over.homMk (hφ.lift q.left (𝟙_ (Over (Sp ℂ))).hom (Over.w q)) (hφ.lift_snd _ _ _))
    refine ⟨w, Over.OverMorphism.ext ?_⟩
    change (u.ex w).left ≫ φ = _
    rw [hw]
    exact hφ.lift_fst _ _ _
  have hhol : IsHolTo Set.univ (fun w => (u.ex w).left) := fun U f => by simpa using u.hol U f
  obtain ⟨ζ, hζ, hζ'⟩ := hl _ x (isHolTo_comp_hom hhol φ) (by rw [hom_zero hx, hom_zero he.1])
  obtain ⟨L, hL⟩ := exists_linearEquiv_lift hx he.1 hsx he.2.1 (by
    haveI := u.discrete
    rw [show {z | x z = 1} = (u.Λ : Set _) from Set.ext hker]
    exact DiscreteTopology.isDiscrete) hr hk hζ.differentiableAt hζ'
  have hmem : ∀ a, L.symm (P a) ∈ u.Λ := fun a => by rw [← hker, ← hL, L.apply_symm_apply, hP]
  refine HasForm.of_comp L.symm.toLinearEquiv.toLinearMap L.symm.injective ⟨Hm, h1, h2, fun a a₂ => ?_⟩
  refine (h3 ⟨_, hmem a⟩ ⟨_, hmem a₂⟩).symm.trans (congrArg _ (int_eq_of_exp fun k hk0 => ?_))
  have e1 := h4 k ⟨_, hmem a⟩ ⟨_, hmem a₂⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have e2 := hw k a a₂ (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have hp : ∀ a, (e ((k : ℂ)⁻¹ • P a)).left = (u.ex ((k : ℂ)⁻¹ • L.symm (P a))).left ≫ φ := fun a => by
    rw [← map_smul, ← L.apply_symm_apply ((k : ℂ)⁻¹ • P a), hL, L.symm_apply_apply]
    rfl
  haveI := A.isAb.comm
  have e3 := (weilIs_grpPullback_of_comm _ _ A.A A'.A y₀ φ A.L A'.L A.isLB A'.isLB hgp (LBIso.symm ⟨t, ht⟩) _ k _ _ _ _ _ (hp a) (hp a₂)).1 e1
  exact congrArg Units.val (weilIs_unique_fieldPoint _ A.A A.L A.isLB ℂ _ k _ _ _ _ e3 e2)

end

end GlobalTheory.LocLift
