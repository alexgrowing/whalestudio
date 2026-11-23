import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TripleProductTorusPeriodicBounded
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBase
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AbelianHolomorphicFrameReadingConstOfFormsCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CubeReading

def colsEquiv (n g : ℕ) : (Fin (n * g) → ℂ) ≃ₗ[ℂ] (Fin n → Fin g → ℂ) where
  toFun := colsOf n g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x k := x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv v := by
    funext k
    simp only [colsOf, Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv x := by
    funext i j
    simp only [colsOf, Equiv.symm_apply_apply]

theorem psumL_apply {n g : ℕ} (I : ULift.{0} (Finset (Fin n))) (x : Fin n → Fin g → ℂ) :
    psumL n g I x = ∑ a ∈ I.down, x a := by
  simp [psumL]

theorem sum_finset_fin_three (f : Finset (Fin 3) → ℂ) :
    ∑ I : ULift.{0} (Finset (Fin 3)), f I.down =
      f ∅ + f {0} + f {1} + f {2} + f {0, 1} + f {0, 2} + f {1, 2} + f {0, 1, 2} := by
  rw [← Equiv.sum_comp Equiv.ulift.symm]
  simp only [Equiv.ulift_symm_down]
  have hu : (Finset.univ : Finset (Finset (Fin 3))) =
      (insert 0 (insert 1 (insert 2 ∅)) : Finset (Fin 3)).powerset := by
    rw [← Finset.powerset_univ]; rfl
  rw [hu]
  simp only [Finset.sum_powerset_insert (show (0 : Fin 3) ∉ insert 1 (insert 2 ∅) by decide),
    Finset.sum_powerset_insert (show (1 : Fin 3) ∉ insert 2 ∅ by decide),
    Finset.sum_powerset_insert (show (2 : Fin 3) ∉ (∅ : Finset (Fin 3)) by decide),
    Finset.powerset_empty, Finset.sum_singleton]
  simp only [Finset.insert_empty]
  ring

theorem third_difference {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin 3 → Fin g → ℂ) :
    ∑ I : thK, ((thε I : ℤ) : ℂ) * hermForm Hm (psumL 3 g I z) (psumL 3 g I w) = 0 := by
  have hs : ∀ f : Finset (Fin 3) → ℂ, ∑ I : thK, f I.down =
      f ∅ + f {0} + f {1} + f {2} + f {0, 1} + f {0, 2} + f {1, 2} + f {0, 1, 2} :=
    fun f => sum_finset_fin_three f
  have he : ∀ J : Finset (Fin 3), thε (ULift.up J : ULift.{0} (Finset (Fin 3))) = (-1) ^ (3 - J.card) :=
    fun J => rfl
  refine (hs fun J => ((thε (ULift.up J : ULift.{0} (Finset (Fin 3))) : ℤ) : ℂ) *
      hermForm Hm (psumL 3 g (ULift.up J) z) (psumL 3 g (ULift.up J) w)).trans ?_
  simp only [he, psumL_apply]
  simp [Finset.sum_insert, hermForm, add_dotProduct, dotProduct_add, Matrix.mulVec_add, star_add]
  ring

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
  (Φ : AnFr A L x0 g)

theorem e_zero : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)

omit [IsCommMonObj A] in
theorem e_add_period (z : Fin g → ℂ) {a : Fin g → ℂ} (ha : a ∈ Φ.lat) : Φ.e (z + a) = Φ.e z := by
  rw [Φ.e_add, (Φ.e_ker a).2 ha, _root_.mul_one]

omit [IsCommMonObj A] in

theorem hol_lin {N : ℕ} (Λ : (Fin N → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : IsHolFam fun v => (Φ.e (Λ v)).left := by
  have h := Φ.hol
  unfold IsHolFam at h ⊢
  intro U f
  obtain ⟨ho, hd⟩ := h U f
  refine ⟨ho.preimage (LinearMap.continuous_of_finiteDimensional Λ), ?_⟩
  exact hd.comp (LinearMap.toContinuousLinearMap Λ).differentiable.differentiableOn (fun v hv => hv)

theorem hol_lift {N : ℕ} {B C : Over S} (p : (Fin N → ℂ) → (Over.mk x0 ⟶ B)) (q : (Fin N → ℂ) → (Over.mk x0 ⟶ C))
    (hp : IsHolFam fun v => (p v).left) (hq : IsHolFam fun v => (q v).left) :
    IsHolFam fun v => (lift (p v) (q v)).left := by
  have key := isHolFam_pullback_lift S B.left C.left B.hom C.hom N (fun v => (p v).left) (fun v => (q v).left) x0
    (fun z => by simp) (fun z => by simp) hp hq
  exact key

def tri (x : Fin 3 → Fin g → ℂ) : Over.mk x0 ⟶ G3 A := lift (Φ.e (x 0)) (lift (Φ.e (x 1)) (Φ.e (x 2)))

theorem hol_tri : IsHolFam fun z => (tri Φ (colsEquiv 3 g z)).left := by
  have hc : ∀ k : Fin 3, IsHolFam fun z => (Φ.e (colsEquiv 3 g z k)).left := by
    intro k
    have h := hol_lin Φ (LinearMap.proj k ∘ₗ (colsEquiv 3 g).toLinearMap)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply] using h
  have h12 := hol_lift (B := A) (C := A) (fun z => Φ.e (colsEquiv 3 g z 1)) (fun z => Φ.e (colsEquiv 3 g z 2))
    (hc 1) (hc 2)
  exact hol_lift (B := A) (C := A ⊗ A) (fun z => Φ.e (colsEquiv 3 g z 0))
    (fun z => lift (Φ.e (colsEquiv 3 g z 1)) (Φ.e (colsEquiv 3 g z 2))) (hc 0) h12

theorem tripleProductPoint_comp_projection (x : Fin 3 → Fin g → ℂ) (k : Fin 3) : tri Φ x ≫ x3 A k = Φ.e (x k) := by
  fin_cases k <;> simp [tri, x3]

private theorem tri_comp_foldr_lift_mul_eq_e_sum (x : Fin 3 → Fin g → ℂ) (l : List (Fin 3)) :
    tri Φ x ≫ l.foldr (fun k acc => lift (x3 A k) acc ≫ μ) (toUnit (G3 A) ≫ η) = Φ.e (l.map x).sum := by
  induction l with
  | nil =>
    simp only [List.foldr_nil, List.map_nil, List.sum_nil, e_zero]
    rw [comp_toUnit_assoc]
    rfl
  | cons k l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, Φ.e_add, ← ih, ← tripleProductPoint_comp_projection]
    rw [← Category.assoc, comp_lift]
    rfl

theorem tri_psum (x : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)) :
    tri Φ x ≫ psum A (x3 A) I = Φ.e (∑ a ∈ I, x a) := by
  unfold psum padd pzero
  rw [tri_comp_foldr_lift_mul_eq_e_sum]
  congr 1
  have hs : ∑ a ∈ I, x a = ∑ a : Fin 3, if a ∈ I then x a else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hl : List.finRange 3 = [0, 1, 2] := by decide
  rw [hs, Fin.sum_univ_three, hl]
  by_cases h0 : (0 : Fin 3) ∈ I <;> by_cases h1 : (1 : Fin 3) ∈ I <;> by_cases h2 : (2 : Fin 3) ∈ I <;>
    simp [h0, h1, h2, add_assoc]

theorem origin_face : (lift (Φ.e 0) (Φ.e 0)).left ≫ (faceMap A 0).left = (tri Φ 0).left := by
  rw [← Over.comp_left]
  congr 1
  unfold faceMap x2 G2 pzero
  simp [tri, e_zero]
  rfl

def lat3 : AddSubgroup (Fin (3 * g) → ℂ) :=
  (AddSubgroup.pi Set.univ fun _ : Fin 3 => Φ.lat).comap (colsEquiv 3 g).toLinearMap.toAddMonoidHom

omit [IsCommMonObj A] in
theorem tripleColumnPeriodLattice_span_real_top : Submodule.span ℝ (lat3 Φ : Set (Fin (3 * g) → ℂ)) = ⊤ := by
  set e : (Fin (3 * g) → ℂ) ≃ₗ[ℝ] (Fin 3 → Fin g → ℂ) := (colsEquiv 3 g).restrictScalars ℝ with he
  have hmem : ∀ w, w ∈ lat3 Φ ↔ ∀ k, colsEquiv 3 g w k ∈ Φ.lat := by
    intro w
    show colsEquiv 3 g w ∈ AddSubgroup.pi Set.univ (fun _ : Fin 3 => Φ.lat) ↔ _
    simp [AddSubgroup.mem_pi]
  have key : ∀ (k : Fin 3) (y : Fin g → ℂ),
      e.symm (Pi.single k y) ∈ Submodule.span ℝ (lat3 Φ : Set (Fin (3 * g) → ℂ)) := by
    intro k y
    have hy : y ∈ Submodule.span ℝ (Φ.lat : Set (Fin g → ℂ)) := by rw [Φ.span]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      apply Submodule.subset_span
      rw [SetLike.mem_coe, hmem]
      intro i
      have : colsEquiv 3 g (e.symm (Pi.single k x)) = Pi.single k x := e.apply_symm_apply _
      rw [this]
      by_cases hik : i = k
      · subst hik; simpa using hx
      · simp [hik, zero_mem]
    | zero => simp
    | add x y _ _ hx hy => simpa [Pi.single_add] using add_mem hx hy
    | smul r x _ hx => simpa [Pi.single_smul'] using Submodule.smul_mem _ r hx
  rw [eq_top_iff]
  rintro v -
  have hv : v = ∑ k : Fin 3, e.symm (Pi.single k (e v k)) := by
    rw [← map_sum, Finset.univ_sum_single, LinearEquiv.symm_apply_apply]
  rw [hv]
  exact Submodule.sum_mem _ fun k _ => key k _

theorem genRd_cubical (cub : CubicalStr A L) (x : Fin 3 → Fin g → ℂ) :
    Φ.GenRd (thφ A (x3 A)) thε cub.t (tri Φ x).left (fun I => psumL 3 g I x) 1 := by
  have hp : ∀ (I : thK) (y : Fin 3 → Fin g → ℂ), psumL 3 g I y = ∑ a ∈ I.down, y a :=
    fun I y => psumL_apply I y
  obtain ⟨⟨v, -, hv⟩, -⟩ := genRd_const S A L x0 g Φ (G3 A).left thK (thφ A (x3 A)) thε cub.t cub.2 (3 * g)
    (fun z => (tri Φ (colsEquiv 3 g z)).left)
    (fun I => psumL 3 g I ∘ₗ (colsEquiv 3 g).toLinearMap) (lat3 Φ) (hol_tri Φ)
    (fun z I => by
      show (tri Φ _).left ≫ (psum A (x3 A) I.down).left = _
      rw [← Over.comp_left, tri_psum]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hp])
    (tripleColumnPeriodLattice_span_real_top Φ)
    (fun gm hgm => by
      have hcol : ∀ k, colsEquiv 3 g gm k ∈ Φ.lat := fun k =>
        ((AddSubgroup.mem_pi _).1 (AddSubgroup.mem_comap.1 hgm)) k (Set.mem_univ _)
      refine ⟨fun z => ?_, fun I => ?_⟩
      · simp only [map_add, tri, Pi.add_apply, e_add_period Φ _ (hcol _)]
      · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hp]
        exact sum_mem fun a _ => hcol a)
    (fun z w => third_difference Φ.Hm (colsEquiv 3 g z) (colsEquiv 3 g w))
  have hj0 : ∃ j, ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U j := by
    have hsub : ∀ p q : PrimeSpectrum ℂ, p = q := fun p q =>
      PrimeSpectrum.ext (by rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.eq_bot_of_prime q.asIdeal])
    obtain ⟨i, hi⟩ := exists_chart L.isLB ((Φ.e 0).left.base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ))
    refine ⟨i, fun pt _ => ?_⟩
    rw [hsub pt ⟨⊥, Ideal.isPrime_bot⟩]
    exact hi
  obtain ⟨j, hj⟩ := hj0
  have hq0 : (tri Φ (colsEquiv 3 g 0)).left = (lift (Φ.e 0) (Φ.e 0)).left ≫ (faceMap A 0).left := by
    rw [map_zero, origin_face]
  have h0 := hv 0
  rw [hq0] at h0
  have hx : ∀ I : thK, ⊤ ≤ (((lift (Φ.e 0) (Φ.e 0)).left ≫ (faceMap A 0).left) ≫ thφ A (x3 A) I) ⁻¹ᵁ
      L.L.U j := by
    intro I
    rw [h0.1 I]
    simpa only [map_zero] using hj
  have hw : ⊤ ≤ ((lift (Φ.e 0) (Φ.e 0)).left ≫ (faceMap A 0).left) ⁻¹ᵁ
      LB.wchart L.L (thφ A (x3 A)) (fun _ => j) := by
    intro pt hpt
    have hk : ∀ I, pt ∈ (((lift (Φ.e 0) (Φ.e 0)).left ≫ (faceMap A 0).left) ≫ thφ A (x3 A) I) ⁻¹ᵁ
        L.L.U j := fun I => hx I hpt
    exact Set.mem_iInter.2 fun k => hk k
  have h1 := GlobalTheory.FrameUnits.val_eq_one_of_corr L.L (thφ A (x3 A)) thε cub.t (faceMap A 0).left (cub.face 0)
    (lift (Φ.e 0) (Φ.e 0)).left j (fun I => hx I)
  have hsum : ∑ k : thK, thε k = 0 := by
    rfl
  have hne : Φ.fr j 0 ≠ 0 := Φ.fr_ne j 0 hj
  have hv1 : v = 1 := by
    have h2 := h0.2 (fun _ => j) hw
    rw [h1] at h2
    simp only [map_zero] at h2
    rw [GlobalTheory.FrameUnits.prod_zpow_eq_zpow_sum _ hne] at h2
    erw [hsum, zpow_zero, _root_.mul_one] at h2
    exact h2.symm
  have hx' := hv ((colsEquiv 3 g).symm x)
  simp only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at hx'
  rw [hv1] at hx'
  exact hx'

end GlobalTheory.CubeReading

theorem GlobalTheory.cubical_reading_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ a b d : Fin g → ℂ, Φ.toAnFr.GenRd (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift (Φ.e a) (lift (Φ.e b) (Φ.e d))).left (fun I => psumL 3 g I ![a, b, d]) 1 := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ a b d
  exact GlobalTheory.CubeReading.genRd_cubical Φ.toAnFr Xo.univ.t.cub ![a, b, d]
