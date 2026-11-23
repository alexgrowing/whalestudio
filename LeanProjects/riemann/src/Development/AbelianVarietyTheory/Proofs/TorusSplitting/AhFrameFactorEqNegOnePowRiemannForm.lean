import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TripleProductTorusPeriodicBounded

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FrameSign

open GlobalTheory.AppellHumbertTrivial GlobalTheory.FrameUnits GlobalTheory.CubeValues

theorem prod_factor_eq_one {g : ℕ} {Ix K : Type} [Fintype K] {S : Set (Fin g → ℂ)} {R : ℝ}
    (hS : ∀ z, ∃ l ∈ S, ‖z + l‖ ≤ R) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (χ : (Fin g → ℂ) → ℂ) (W : Ix → Set (Fin g → ℂ)) (hWo : ∀ j, IsOpen (W j)) (hWc : ∀ z, ∃ j, z ∈ W j)
    (hWp : ∀ l ∈ S, ∀ j z, z ∈ W j → z + l ∈ W j)
    (fr : Ix → (Fin g → ℂ) → ℂ) (c : Ix → Ix → (Fin g → ℂ) → ℂ)
    (hd : ∀ j, DifferentiableOn ℂ (fr j) (W j)) (hne : ∀ j z, z ∈ W j → fr j z ≠ 0)
    (hc : ∀ j j' z, z ∈ W j → z ∈ W j' → fr j z = c j j' z * fr j' z)
    (hχ : ∀ l ∈ S, ‖χ l‖ = 1)
    (hf : ∀ l ∈ S, ∀ j z, z ∈ W j → fr j z = χ l * Complex.exp (Real.pi * hermForm Hm z l +
      Real.pi / 2 * hermForm Hm l l) * fr j (z + l))
    (ε : K → ℤ) (lam : K → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hΛ : ∀ l ∈ S, ∀ k, lam k l ∈ S)
    (T : (K → Ix) → (Fin g → ℂ) → ℂ)
    (hTd : ∀ j, DifferentiableOn ℂ (T j) {z | ∀ k, lam k z ∈ W (j k)})
    (hT0 : ∀ j z, (∀ k, lam k z ∈ W (j k)) → T j z ≠ 0)
    (hTc : ∀ j j' z, (∀ k, lam k z ∈ W (j k)) → (∀ k, lam k z ∈ W (j' k)) →
      T j z = (∏ k, c (j k) (j' k) (lam k z) ^ ε k) * T j' z)
    (hTp : ∀ l ∈ S, ∀ j z, T j (z + l) = T j z) :
    ∀ l ∈ S, ∏ k, χ (lam k l) ^ ε k = 1 := by
  have hld : ∀ k, Differentiable ℂ (lam k) := fun k =>
    (LinearMap.toContinuousLinearMap (lam k)).differentiable
  let D : (K → Ix) → Set (Fin g → ℂ) := fun j => {z | ∀ k, lam k z ∈ W (j k)}
  have hDo : ∀ j, IsOpen (D j) := fun j => by
    simp only [D, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun k => (hWo (j k)).preimage (hld k).continuous
  have hcov : ∀ z, ∃ j, z ∈ D j := fun z => by
    choose a ha using hWc
    exact ⟨fun k => a (lam k z), fun k => ha _⟩
  let F : (K → Ix) → (Fin g → ℂ) → ℂ := fun j z => ∏ k, fr (j k) (lam k z) ^ ε k
  have hF0 : ∀ j z, z ∈ D j → F j z ≠ 0 := fun j z hz =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne _ _ (hz k))
  obtain ⟨ψ, hψ, hG⟩ := PullHermitian.exists_glue D hDo hcov
    (fun j z => T j z * (F j z)⁻¹)
    (fun j => by
      have dF : DifferentiableOn ℂ (fun z => ∏ k, fr (j k) (lam k z) ^ ε k) (D j) :=
        differentiableOn_fun_prod _ fun k => DifferentiableOn.zpow
          ((hd (j k)).comp (hld k).differentiableOn fun z hz => hz k)
          (Or.inl fun z hz => hne _ _ (hz k))
      exact (hTd j).mul (dF.inv (hF0 j)))
    (fun j j' z hz hz' => by
      have e3 := hTc j j' z hz hz'
      have c1 : F j z = (∏ k, c (j k) (j' k) (lam k z) ^ ε k) * F j' z := by
        simp only [F]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [hc _ _ _ (hz k) (hz' k), mul_zpow]
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff (hF0 _ _ hz) (hF0 _ _ hz'), e3, c1]
      ring)
  have hψ0 : ∀ z, ψ z ≠ 0 := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    rw [hG j z hj]
    exact mul_ne_zero (hT0 j z hj) (inv_ne_zero (hF0 j z hj))
  have hper : ∀ l ∈ S, ∀ z, ψ (z + l) = (∏ k, χ (lam k l) ^ ε k) *
      Complex.exp (Real.pi * ∑ k, (ε k : ℂ) * hermForm Hm (lam k z) (lam k l) +
        Real.pi / 2 * ∑ k, (ε k : ℂ) * hermForm Hm (lam k l) (lam k l)) * ψ z := fun l hl z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : z + l ∈ D j := fun k => by
      rw [map_add]
      exact hWp _ (hΛ l hl k) _ _ (hj k)
    have c1 : F j z = (∏ k, χ (lam k l) ^ ε k) *
        Complex.exp (Real.pi * ∑ k, (ε k : ℂ) * hermForm Hm (lam k z) (lam k l) +
          Real.pi / 2 * ∑ k, (ε k : ℂ) * hermForm Hm (lam k l) (lam k l)) * F j (z + l) := by
      simp only [F]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Complex.exp_sum,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hf _ (hΛ l hl k) (j k) (lam k z) (hj k), map_add, mul_zpow, mul_zpow,
        ← Complex.exp_int_mul]
      congr 3
      ring
    rw [hG j z hj, hG j _ hj', hTp l hl]
    have key : ∀ a b c d : ℂ, b ≠ 0 → c ≠ 0 → b = a * c → d * c⁻¹ = a * (d * b⁻¹) := by
      rintro a _ c d h1 h2 rfl
      have := left_ne_zero_of_mul h1
      field_simp
    exact key _ _ _ _ (hF0 j z hj) (hF0 j _ hj') c1
  obtain ⟨h1, h2⟩ := form_eq_zero_and_const hS ψ hψ hψ0
    (fun z w => ∑ k, (ε k : ℂ) * hermForm Hm (lam k z) (lam k w))
    (continuous_finset_sum _ fun k _ => continuous_const.mul
      ((continuous_hermForm_self Hm).comp (hld k).continuous))
    (fun z z' w => by simp only [map_add, hermForm_add_left, mul_add, Finset.sum_add_distrib])
    (fun c z w => by
      simp only [map_smul, hermForm_smul_left, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun z w => by
      simp only [star_sum, star_mul', star_intCast]
      exact Finset.sum_congr rfl fun k _ => by rw [hermForm_swap hH])
    (fun l hl => ⟨_, by simp [norm_prod, norm_zpow, hχ _ (hΛ l hl _)], hper l hl⟩)
  intro l hl
  have := hper l hl 0
  rw [h1, h1, h2, mul_zero, mul_zero, add_zero, Complex.exp_zero, _root_.mul_one] at this
  exact (mul_eq_right₀ (hψ0 0)).1 this.symm

theorem factor_add {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (f : (Fin g → ℂ) → ℂ)
    (a b : Fin g → ℂ) (x y s : ℂ) (n : ℤ) (hn : (hermForm Hm a b).im = n) (h0 : f 0 ≠ 0)
    (ha : f 0 = x * Complex.exp (Real.pi * hermForm Hm 0 a + Real.pi / 2 * hermForm Hm a a) * f (0 + a))
    (hb : f a = y * Complex.exp (Real.pi * hermForm Hm a b + Real.pi / 2 * hermForm Hm b b) * f (a + b))
    (hs : f 0 = s * Complex.exp (Real.pi * hermForm Hm 0 (a + b) +
      Real.pi / 2 * hermForm Hm (a + b) (a + b)) * f (0 + (a + b))) :
    s = x * y * ((Int.negOnePow n : ℤˣ) : ℤ) := by
  have z0 : ∀ w, hermForm Hm 0 w = 0 := fun w => by simp [hermForm]
  rw [z0, mul_zero, zero_add, zero_add] at ha hs
  have hab : f (a + b) ≠ 0 := fun h => h0 (by rw [hs, h, mul_zero])
  have e1 : hermForm Hm a b - hermForm Hm b a = n * (2 * Complex.I) := by
    rw [hermForm_swap hH a b, Complex.star_def, Complex.sub_conj, hn]
    push_cast
    ring
  have e2 : ((((Int.negOnePow n : ℤˣ) : ℤ)) : ℂ) = Complex.exp (n * (Real.pi * Complex.I)) := by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I, Int.cast_negOnePow]
  have e3 : Complex.exp (Real.pi / 2 * hermForm Hm a a) *
      Complex.exp (Real.pi * hermForm Hm a b + Real.pi / 2 * hermForm Hm b b) =
      Complex.exp (n * (Real.pi * Complex.I)) * Complex.exp (Real.pi / 2 * hermForm Hm (a + b) (a + b)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hermForm_add_left, hermForm_add_right, hermForm_add_right]
    congr 1
    linear_combination (Real.pi / 2 : ℂ) * e1
  refine mul_right_cancel₀ (mul_ne_zero (Complex.exp_ne_zero (Real.pi / 2 * hermForm Hm (a + b) (a + b))) hab) ?_
  rw [e2]
  rw [hb] at ha
  linear_combination ha - hs + x * y * f (a + b) * e3

theorem exists_period_norm_le' {g : ℕ} {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    ∃ R : ℝ, ∀ z : Fin g → ℂ, ∃ l ∈ Set.range P, ‖z + l‖ ≤ R := by
  let Λ : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology Λ := hd
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let b := (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  refine ⟨∑ i, ‖b i‖, fun z => ⟨-(ZSpan.floor b z : Fin g → ℂ), Λ.neg_mem ?_, ?_⟩⟩
  · exact ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis_span ℝ Λ).le (ZSpan.floor b z).2
  · rw [← sub_eq_add_neg, ← ZSpan.fract_apply]
    exact ZSpan.norm_fract_le b z

theorem val_iso_linComb {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X) {K : Type} [Fintype K] (φ : K → (X ⟶ X))
    (ε : K → ℤ) (w : LB.Iso L (L.LinComb φ ε)) (hw : w.IsGen) (J J' : K → L.ι) (j j' : L.ι)
    (hJ : ⊤ ≤ x ⁻¹ᵁ L.wchart φ J) (hJ' : ⊤ ≤ x ⁻¹ᵁ L.wchart φ J') (hj : ⊤ ≤ x ⁻¹ᵁ L.U j)
    (hj' : ⊤ ≤ x ⁻¹ᵁ L.U j') :
    valAt' x _ (w.s (J, j)).val =
      (valAt' x (L.U j ⊓ L.U j') (L.g j j').val ^ (-1 : ℤ) *
        ∏ k, valAt' (x ≫ φ k) (L.U (J k) ⊓ L.U (J' k)) (L.g (J k) (J' k)).val ^ ε k) *
        valAt' x _ (w.s (J', j')).val := by
  have h := congrArg Units.val (PullHermitian.unitVal_iso x w hw J J' j j' hJ hJ' hj hj')
  rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val] at h
  simp only [← PullHermitian.valAt'_eq_unitVal] at h
  rw [← val_linComb x valAt'_rules L φ ε J J' hJ hJ', zpow_neg_one, mul_comm (_ ⁻¹),
    PullHermitian.valAt'_eq_unitVal x (U := ((L.LinComb φ ε).div L).U (J, j)) (PullHermitian.inf_of x hJ hj),
    PullHermitian.valAt'_eq_unitVal x (U := ((L.LinComb φ ε).div L).U (J', j')) (PullHermitian.inf_of x hJ' hj')]
  exact h

theorem hol_slice {X : Scheme.{0}} {g : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : IsHolTo ((Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun bz => e bz.2))
    (U : X.Opens) (f : Γ(X, U)) :
    IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun z => valAt' (e z) U f) {z | ⊤ ≤ e z ⁻¹ᵁ U} := by
  obtain ⟨h1, h2⟩ := h U f
  have hm : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  refine ⟨?_, ?_⟩
  · convert h1.preimage hm.continuous using 1
    ext z
    exact ⟨fun hz => ⟨⟨trivial, trivial⟩, hz⟩, fun hz => hz.2⟩
  · have := h2.comp (s := {z | ⊤ ≤ e z ⁻¹ᵁ U}) hm.differentiableOn fun z hz => ⟨⟨trivial, trivial⟩, hz⟩
    exact this

end GlobalTheory.FrameSign

open GlobalTheory.FrameSign GlobalTheory.CubeValues in

theorem GlobalTheory.ahFrame_factor_eq_negOnePow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (Fu.Di i) ty Pm → AHFrame Fu i Pm Hm χl fr → ∀ a, χl (Pm a) = ((Int.negOnePow ((Fu.Di i).EF a (H.w0 • a)) : ℤˣ) : ℤ) := by
  intro E _ _ _ H Dw l Xo σ g ty Fu i Pm Hm χl fr hP hF a
  obtain ⟨hH, -, him, hd, hne, hc, -, hf⟩ := hF
  obtain ⟨R, hR⟩ := exists_period_norm_le' Pm hP.2.2.1 hP.2.2.2.1
  obtain ⟨w, hw⟩ := Xo.univ.t.prim
  have hch : ∀ z, ∃ j, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    PullHermitian.exists_chart _ Xo.univ.t.PP.isLB
  have hex : ∀ b z, Fu.ex i Pm (z + Pm b) = Fu.ex i Pm z := fun b z => by
    rw [Fu.ex_add i Pm hP, (Fu.ex_ker i Pm hP (Pm b)).2 ⟨b, rfl⟩, _root_.mul_one]
  have hhol : ∀ (U : Xo.univ.t.G.left.Opens) (f : Γ(Xo.univ.t.G.left, U)),
      IsOpen {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (Fu.ex i Pm z).left U f) {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ U} :=
    hol_slice (fun z => (Fu.ex i Pm z).left) (Fu.hol i 0 Set.univ (fun _ => Pm) isOpen_univ
      ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  let Wl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    LinearMap.pi fun k => ty k (H.w0 : E) • LinearMap.proj k
  have hWl : ∀ z, Fu.ex i Pm (Wl z) = Fu.ex i Pm z ≫ Xo.univ.t.act.act H.w0 := fun z =>
    Fu.ex_lin i Pm hP H.w0 z
  have hWP : ∀ b, Wl (Pm b) = Pm (H.w0 • b) := fun b => funext fun k => (hP.1 H.w0 b k).symm
  let lam0 : Finset (Fin 2) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun I => ∑ s ∈ I, ![LinearMap.id, Wl] s
  have huniv : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have l0 : ∀ z, lam0 ∅ z = 0 := fun z => by simp [lam0]
  have l1 : ∀ z, lam0 {0} z = z := fun z => by simp [lam0]
  have l2 : ∀ z, lam0 {1} z = Wl z := fun z => by simp [lam0]
  have l3 : ∀ z, lam0 {0, 1} z = z + Wl z := fun z => by simp [lam0]
  have hlam0 : ∀ I z, (Fu.ex i Pm z).left ≫
      (psum Xo.univ.t.G ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0] I).left = (Fu.ex i Pm (lam0 I z)).left := by
    intro I z
    rw [← Over.comp_left]
    congr 1
    have h0 : Fu.ex i Pm 0 = 1 := (Fu.ex_ker i Pm hP 0).2 (zero_mem _)
    have hI : I ∈ ({∅, {0}, {1}, {0, 1}} : Finset (Finset (Fin 2))) := huniv ▸ Finset.mem_univ I
    simp only [Finset.mem_insert, Finset.mem_singleton] at hI
    rcases hI with rfl | rfl | rfl | rfl
    · rw [l0, h0]
      exact MonObj.comp_one _
    · rw [l1]
      change _ ≫ (𝟙 Xo.univ.t.G * 1) = _
      simp
    · rw [l2, hWl]
      change _ ≫ (Xo.univ.t.act.act H.w0 * 1) = _
      simp
    · rw [l3, Fu.ex_add i Pm hP, hWl]
      change _ ≫ (𝟙 Xo.univ.t.G * (Xo.univ.t.act.act H.w0 * 1)) = _
      simp [MonObj.comp_mul]
  have hwc : ∀ (J : ULift.{0} (Finset (Fin 2)) → Xo.univ.t.PP.L.ι) z,
      (∀ I, ⊤ ≤ (Fu.ex i Pm (lam0 I.down z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (J I)) →
      ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.wchart (fun I : ULift.{0} (Finset (Fin 2)) =>
        (psum Xo.univ.t.G ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0] I.down).left) J := fun J z h =>
    (le_preimage_wchart _ _ _ _).2 fun I => by rw [hlam0]; exact h I
  have key := prod_factor_eq_one (K := Option (ULift.{0} (Finset (Fin 2)))) hR hH χl
    (fun j => {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) (fun j => (hhol _ 0).1) hch
    (by
      rintro _ ⟨b, rfl⟩ j z hz
      simpa only [Set.mem_setOf_eq, hex] using hz)
    fr (fun j j' z => valAt' (Fu.ex i Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val) hd hne
    (fun j j' z hz hz' => hc j j' z ((le_preimage_inf _ _ _).2 ⟨hz, hz'⟩))
    (by
      rintro _ ⟨b, rfl⟩
      obtain ⟨j, -⟩ := hch 0
      exact (hf b j 0).1)
    (by
      rintro _ ⟨b, rfl⟩ j z hz
      exact (hf b j z).2 hz)
    (fun k => k.elim (-1) fun I => (-1) ^ (2 - I.down.card))
    (fun k => k.elim LinearMap.id fun I => lam0 I.down)
    (by
      rintro _ ⟨b, rfl⟩ (_ | ⟨I⟩)
      · exact ⟨b, rfl⟩
      · refine ⟨∑ s ∈ I.down, ![b, H.w0 • b] s, ?_⟩
        simp only [lam0, Option.elim, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun s _ => ?_
        fin_cases s
        · rfl
        · exact (hWP b).symm)
    (fun j z => valAt' (Fu.ex i Pm z).left _ (w.s (fun I => j (some I), j none)).val)
    (fun j => (hhol _ _).2.mono fun z hz =>
      (le_preimage_inf _ _ _).2 ⟨hwc _ z fun I => hz (some I), hz none⟩)
    (fun j z hz => val_unit_ne_zero _ valAt'_rules
      ((le_preimage_inf _ _ _).2 ⟨hwc _ z fun I => hz (some I), hz none⟩) _)
    (fun j j' z hz hz' => by
      refine (val_iso_linComb _ _ _ _ w hw _ _ _ _ (hwc _ z fun I => hz (some I))
        (hwc _ z fun I => hz' (some I)) (hz none) (hz' none)).trans ?_
      rw [Fintype.prod_option]
      simp only [hlam0]
      rfl)
    (by
      rintro _ ⟨b, rfl⟩ j z
      simp only [hex])
    (Pm a) ⟨a, rfl⟩
  have hadd : ∀ b b', χl (Pm (b + b')) =
      χl (Pm b) * χl (Pm b') * ((Int.negOnePow ((Fu.Di i).EF b b') : ℤˣ) : ℤ) := fun b b' => by
    obtain ⟨j, hj⟩ := hch 0
    have hj' : ⊤ ≤ (Fu.ex i Pm (Pm b)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
      rw [← zero_add (Pm b), hex]; exact hj
    have h3 := (hf (b + b') j 0).2 hj
    rw [map_add] at h3 ⊢
    exact factor_add hH (fr j) _ _ _ _ _ _ (him b b') (hne j 0 hj) ((hf b j 0).2 hj) ((hf b' j _).2 hj') h3
  have hn : ∀ b, χl (Pm b) ≠ 0 := fun b => by
    obtain ⟨j, -⟩ := hch 0
    exact norm_ne_zero_iff.1 (by rw [(hf b j 0).1]; exact one_ne_zero)
  have h0 : χl 0 = 1 := by
    have := hadd 0 0
    have n0 := hn 0
    simp only [add_zero, map_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, _root_.mul_one] at this n0
    exact (mul_eq_left₀ n0).1 this.symm
  rw [Fintype.prod_option] at key
  simp only [Option.elim] at key
  rw [Fintype.prod_equiv Equiv.ulift
    (fun I : ULift.{0} (Finset (Fin 2)) => χl (lam0 I.down (Pm a)) ^ ((-1 : ℤ) ^ (2 - I.down.card)))
    (fun I : Finset (Fin 2) => χl (lam0 I (Pm a)) ^ ((-1 : ℤ) ^ (2 - I.card))) (fun I => rfl), huniv,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, l0, l1, l2, l3, hWP, ← map_add, hadd, h0] at key
  have c01 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  have n1 := hn a
  have n2 := hn (H.w0 • a)
  rw [c01] at key
  generalize (((Int.negOnePow ((Fu.Di i).EF a (H.w0 • a)) : ℤˣ) : ℤ) : ℂ) = s at key ⊢
  norm_num at key
  field_simp at key
  exact key.symm
