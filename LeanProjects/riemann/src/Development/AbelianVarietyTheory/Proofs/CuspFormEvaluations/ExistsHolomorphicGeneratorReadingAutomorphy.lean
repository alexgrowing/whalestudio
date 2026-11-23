import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValGenRd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt

attribute [local instance] Over.cartesianMonoidalCategory

theorem differentiableAt_prod {E K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Finset K)
    (f : K → E → ℂ) (z : E) (h : ∀ k, DifferentiableAt ℂ (f k) z) :
    DifferentiableAt ℂ (fun w => ∏ k ∈ s, f k w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

private theorem preimage_eq_univ_iff_forall_mem {W : Scheme.{0}} (x : Sp ℂ ⟶ W) (U : W.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ ∀ p, x p ∈ U := by
  constructor
  · intro h p
    exact h (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  · intro h p _
    exact h p

section LC

variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

theorem top_le_wchart_iff (φ : K → (Y ⟶ X)) (j : K → L.ι) (x : Sp ℂ ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  simp only [preimage_eq_univ_iff_forall_mem]
  unfold LB.wchart
  constructor
  · intro h k p
    exact Set.mem_iInter.1 (h p) k
  · intro h p
    exact Set.mem_iInter.2 fun k => h k p

theorem top_le_inf {x : Sp ℂ ⟶ Y} {U V : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) := by
  rw [preimage_eq_univ_iff_forall_mem] at h h' ⊢
  intro p
  exact TopologicalSpace.Opens.mem_inf.2 ⟨h p, h' p⟩

theorem val_prod (x : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : K → Γ(Y, U)ˣ) :
    valAt' x U (∏ k, u k).val = ∏ k, valAt' x U (u k).val := by
  rw [Units.coe_prod]
  exact map_prod (valHom x U h) _ _

private theorem valAt'_app_hom_eq_valAt'_comp {W V : Scheme.{0}} (x : Sp ℂ ⟶ V) (ψ : V ⟶ W) (U : W.Opens) (f : Γ(W, U)) :
    valAt' x (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) = valAt' (x ≫ ψ) U f := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U := h
    rw [dif_pos h, dif_pos h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U := h
    rw [dif_neg h, dif_neg h']

private theorem valAt'_pullU_eq_valAt'_comp {W V : Scheme.{0}} (x : Sp ℂ ⟶ V) (ψ : V ⟶ W) (U : W.Opens) (u : Γ(W, U)ˣ) :
    valAt' x (ψ ⁻¹ᵁ U) (pullU ψ U u).val = valAt' (x ≫ ψ) U u.val := by
  unfold pullU
  rw [Units.coe_map]
  exact valAt'_app_hom_eq_valAt'_comp x ψ U u.val

private theorem valAt'_res_unit_eq {W : Scheme.{0}} (x : Sp ℂ ⟶ W) {U V : W.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (u : Γ(W, U)ˣ) : valAt' x V (res hVU u).val = valAt' x U u.val := by
  unfold res
  rw [Units.coe_map]
  exact valAt'_res x hVU h u.val

private theorem valAt'_unit_zpow' {W : Scheme.{0}} (x : Sp ℂ ⟶ W) (U : W.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(W, U)ˣ)
    (n : ℤ) : valAt' x U (u ^ n).val = valAt' x U u.val ^ n := by
  have e := congrArg Units.val (map_zpow (Units.map (valHom x U h).toMonoidHom) u n)
  rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.coe_map] at e
  exact e

theorem val_linComb_g (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Sp ℂ ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  unfold LB.LinComb
  dsimp only
  rw [val_prod p _ h]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [valAt'_unit_zpow' p _ h]
  congr 1
  exact (valAt'_res_unit_eq p _ h _).trans (valAt'_pullU_eq_valAt'_comp p (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))

theorem val_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (p : Sp ℂ ⟶ Y) (j j' : K → L.ι) (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p (LB.wchart L φ j) (t.s j).val =
      (∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valAt' p (LB.wchart L φ j') (t.s j').val := by
  have e := congrArg (fun u => valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) (ht j j')
  simp only [Units.val_mul] at e
  have e1 := valAt'_res_unit_eq p (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) h (t.s j)
  have e2 := valAt'_res_unit_eq p (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') h (t.s j')
  have e3 := val_linComb_g L φ ε p j j' h
  exact e1.symm.trans (e.trans ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·) e3 e2)))

theorem exists_chart (hL : L.IsLB) (φ : K → (Y ⟶ X)) (x : Sp ℂ ⟶ Y) :
    ∃ j : K → L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j := by
  have hp : ∀ k, ∃ i, (x ≫ φ k) (default : PrimeSpectrum ℂ) ∈ L.U i := fun k => by
    have h0 : (x ≫ φ k) (default : PrimeSpectrum ℂ) ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.1 h0
  choose j hj using hp
  refine ⟨j, (top_le_wchart_iff L φ j x).2 fun k => (preimage_eq_univ_iff_forall_mem _ _).2 fun p => ?_⟩
  rw [Subsingleton.elim (α := PrimeSpectrum ℂ) p default]
  exact hj k

end LC

section Rd

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε))

theorem top_le_chart {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} (hq : ∀ k, q ≫ φ k = (Φ.e (p k)).left) {j : K → L.L.ι}
    (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j) (k : K) : ⊤ ≤ (Φ.e (p k)).left ⁻¹ᵁ L.L.U (j k) := by
  have h := (top_le_wchart_iff L.L φ j q).1 hj k
  rwa [hq k] at h

theorem prod_fr_ne {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} (hq : ∀ k, q ≫ φ k = (Φ.e (p k)).left) {j : K → L.L.ι}
    (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j) : ∏ k, Φ.fr (j k) (p k) ^ ε k ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ?_
  exact Φ.fr_ne _ _ (top_le_chart Φ φ hq hj k)

theorem genRd_of_chart (ht : t.IsGen) {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} (hq : ∀ k, q ≫ φ k = (Φ.e (p k)).left)
    {j' : K → L.L.ι} (hj' : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j') :
    Φ.GenRd φ ε t q p (valAt' q (LB.wchart L.L φ j') (t.s j').val / ∏ k, Φ.fr (j' k) (p k) ^ ε k) := by
  refine ⟨hq, fun j hj => ?_⟩
  have hg : ∀ k, valAt' (q ≫ φ k) (L.L.U (j k) ⊓ L.L.U (j' k)) (L.L.g (j k) (j' k)).val =
      Φ.fr (j k) (p k) / Φ.fr (j' k) (p k) := fun k => by
    rw [hq k, eq_div_iff (Φ.fr_ne _ _ (top_le_chart Φ φ hq hj' k))]
    exact (Φ.fr_g _ _ _ (top_le_inf (top_le_chart Φ φ hq hj k) (top_le_chart Φ φ hq hj' k))).symm
  have hA := prod_fr_ne Φ φ ε hq hj
  have hB := prod_fr_ne Φ φ ε hq hj'
  rw [val_isGen L.L φ ε t ht q j j' (top_le_inf hj hj')]
  simp only [hg, div_zpow, Finset.prod_div_distrib]
  field_simp

theorem genRd_eq {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} {u : ℂ} (hu : Φ.GenRd φ ε t q p u)
    {j : K → L.L.ι} (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j) :
    u = valAt' q (LB.wchart L.L φ j) (t.s j).val / ∏ k, Φ.fr (j k) (p k) ^ ε k := by
  rw [eq_div_iff (prod_fr_ne Φ φ ε hu.1 hj)]
  exact (hu.2 j hj).symm

private theorem valAt'_unit_val_ne_zero {W : Scheme.{0}} (x : Sp ℂ ⟶ W) (U : W.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (u : Γ(W, U)ˣ) : valAt' x U u.val ≠ 0 :=
  (u.isUnit.map (valHom x U h)).ne_zero

end Rd

theorem exists_reading : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (p : K → (Fin N → ℂ) → Fin g → ℂ), IsHolFam q → (∀ k, Differentiable ℂ (p k)) → (∀ z k, q z ≫ φ k = (Φ.e (p k z)).left) → ∃ v : (Fin N → ℂ) → ℂ, Differentiable ℂ v ∧ (∀ z, v z ≠ 0) ∧ (∀ z, Φ.GenRd φ ε t (q z) (fun k => p k z) (v z)) ∧ (∀ z u, Φ.GenRd φ ε t (q z) (fun k => p k z) u → u = v z) ∧ ∀ z z' (a : K → Fin g → ℂ), q z' = q z → (∀ k, a k ∈ Φ.lat ∧ p k z' = p k z + a k) → v z' = v z * ∏ k, Φ.fac (a k) (p k z) ^ ε k := by
  intro S A _ _ L x0 g Φ Z K _ φ ε t ht N q p hq hp hqp
  have hL : L.L.IsLB := L.isLB
  have hJ : ∀ z, ∃ j : K → L.L.ι, ⊤ ≤ q z ⁻¹ᵁ LB.wchart L.L φ j := fun z => exists_chart L.L hL φ (q z)
  choose J hJ using hJ
  have hgen : ∀ z, Φ.GenRd φ ε t (q z) (fun k => p k z)
      (valAt' (q z) (LB.wchart L.L φ (J z)) (t.s (J z)).val / ∏ k, Φ.fr (J z k) (p k z) ^ ε k) :=
    fun z => genRd_of_chart Φ φ ε t ht (fun k => hqp z k) (hJ z)
  refine ⟨fun z => valAt' (q z) (LB.wchart L.L φ (J z)) (t.s (J z)).val / ∏ k, Φ.fr (J z k) (p k z) ^ ε k,
    ?_, ?_, hgen, fun z u hu => genRd_eq Φ φ ε t hu (hJ z), ?_⟩
  · intro z0
    have hO := (hq (LB.wchart L.L φ (J z0)) (t.s (J z0)).val).1
    have hz0 : z0 ∈ {z | ⊤ ≤ q z ⁻¹ᵁ LB.wchart L.L φ (J z0)} := hJ z0
    have hnum : DifferentiableAt ℂ (fun z => valAt' (q z) (LB.wchart L.L φ (J z0)) (t.s (J z0)).val) z0 :=
      ((hq (LB.wchart L.L φ (J z0)) (t.s (J z0)).val).2 z0 hz0).differentiableAt (hO.mem_nhds hz0)
    have hfac : ∀ k, DifferentiableAt ℂ (fun z => Φ.fr (J z0 k) (p k z) ^ ε k) z0 := fun k => by
      have hc := top_le_chart Φ φ (fun k => hqp z0 k) (hJ z0) k
      have hO' := (Φ.hol (L.L.U (J z0 k)) 1).1
      have hfr : DifferentiableAt ℂ (Φ.fr (J z0 k)) (p k z0) :=
        (Φ.fr_hol (J z0 k) (p k z0) hc).differentiableAt (hO'.mem_nhds hc)
      exact (hfr.comp z0 ((hp k) z0)).zpow (Or.inl (Φ.fr_ne _ _ hc))
    have hden := differentiableAt_prod (Finset.univ : Finset K) (fun k z => Φ.fr (J z0 k) (p k z) ^ ε k) z0 hfac
    have hne := prod_fr_ne Φ φ ε (fun k => hqp z0 k) (hJ z0)
    have hinv : DifferentiableAt ℂ (fun z => (∏ k, Φ.fr (J z0 k) (p k z) ^ ε k)⁻¹) z0 := hden.inv hne
    have hw : DifferentiableAt ℂ (fun z => valAt' (q z) (LB.wchart L.L φ (J z0)) (t.s (J z0)).val /
        ∏ k, Φ.fr (J z0 k) (p k z) ^ ε k) z0 := by
      simpa only [div_eq_mul_inv, Pi.mul_def] using hnum.mul hinv
    refine hw.congr_of_eventuallyEq (Filter.eventually_of_mem (hO.mem_nhds hz0) fun z hz => ?_)
    exact genRd_eq Φ φ ε t (hgen z) hz
  · intro z
    exact div_ne_zero (valAt'_unit_val_ne_zero _ _ (hJ z) _) (prod_fr_ne Φ φ ε (fun k => hqp z k) (hJ z))
  · intro z z' a hzz ha
    have hz' : ⊤ ≤ q z' ⁻¹ᵁ LB.wchart L.L φ (J z) := by
      rw [hzz]
      exact hJ z
    have hA := prod_fr_ne Φ φ ε (fun k => hqp z' k) hz'
    have hper : ∀ k, Φ.fr (J z k) (p k z) = Φ.fac (a k) (p k z) * Φ.fr (J z k) (p k z + a k) := fun k =>
      Φ.fr_per (a k) (ha k).1 (J z k) (p k z) (top_le_chart Φ φ (fun k => hqp z k) (hJ z) k)
    have hC := prod_fr_ne Φ φ ε (fun k => hqp z k) (hJ z)
    have hB : ∏ k, Φ.fac (a k) (p k z) ^ ε k ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ?_
      intro h0
      have h1 := Φ.fr_ne _ _ (top_le_chart Φ φ (fun k => hqp z k) (hJ z) k)
      rw [hper k, h0, zero_mul] at h1
      exact h1 rfl
    show valAt' (q z') (LB.wchart L.L φ (J z')) (t.s (J z')).val / ∏ k, Φ.fr (J z' k) (p k z') ^ ε k = _
    rw [genRd_eq Φ φ ε t (hgen z') hz', hzz]
    simp only [(ha _).2] at hA ⊢
    simp only [hper, mul_zpow, Finset.prod_mul_distrib]
    field_simp

end GlobalTheory.AnValGenRd
