import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.AutSimilitudeAndMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaUniformisationFrameEqAutomorphyMulStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEntireGeneratorDivFramesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta

theorem span_single_block_eq_top {V : Type} [AddCommGroup V] [Module ℝ V] {Λ : Set V} (h : Submodule.span ℝ Λ = ⊤) :
    Submodule.span ℝ {s : Fin 4 → V | ∃ c, ∃ l ∈ Λ, s = Pi.single c l} = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  rw [← Finset.univ_sum_single y]
  refine Submodule.sum_mem _ fun c _ => ?_
  have hz : y c ∈ Submodule.span ℝ Λ := h ▸ Submodule.mem_top
  generalize y c = v at hz
  induction hz using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span ⟨c, v, hv, rfl⟩
  | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
  | add v v' _ _ hv hv' => rw [Pi.single_add]; exact Submodule.add_mem _ hv hv'
  | smul r v _ hv => rw [Pi.single_smul]; exact Submodule.smul_mem _ r hv

theorem ex_zsmul_eq_zpow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (s : ℤ) (z : Fin g → ℂ) :
    u.ex (s • z) = u.ex z ^ s :=
  map_zpow (MonoidHom.mk' (fun z : Multiplicative (Fin g → ℂ) => u.ex z.toAdd) fun _ _ => u.ex_add _ _)
    (Multiplicative.ofAdd z) s

theorem comp_alMap_ex {g : ℕ} (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (al : Matrix (Fin 4) (Fin 4) ℤ) (r : Fin 4)
    (t : Fin g → ℂ) (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4)
    (hpt : ∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) :
    pt ≫ alMap x al r (u.ex t) = u.ex (∑ c, al r c • y c + t) := by
  have e₀ : pt ≫ toUnit _ = 𝟙 _ := toUnit_unique _ _
  simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul,
    GrpObj.comp_zpow, MonObj.comp_one, hpt, reassoc_of% e₀, Fin.sum_univ_succ, Fin.sum_univ_zero, u.ex_add, ex_zsmul_eq_zpow,
    GlobalTheory.PowUnif.ex_zero]

theorem simil_generator_eq_exp : ∀ (g m : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), charHalf g a b → Wit x h u τ a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∀ (k n : Fin 4 → Fin g → ℤ) (ξ : Fin 4 → Pt x), (∀ r, ξ r = u.ex (tors τ al m k n r)) → ∀ w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w.IsGen → ∃ C : ℂ, C ≠ 0 ∧ ∀ (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4), (∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) → ∀ j : Fin 4 ⊕ Fin 4 → x.P.L.ι, (∀ r, ⊤ ≤ (u.ex (∑ c, al r c • y c + tors τ al m k n r)).left ⁻¹ᵁ x.P.L.U (j (Sum.inl r))) → (∀ c, ⊤ ≤ (u.ex (y c)).left ⁻¹ᵁ x.P.L.U (j (Sum.inr c))) → valAt' pt.left (LB.wchart x.P.L (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) j) (w.s j).val * Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c) = C * ((∏ r, u.fr (j (Sum.inl r)) (∑ c, al r c • y c + tors τ al m k n r)) * ∏ c, u.fr (j (Sum.inr c)) (y c) ^ (-(m : ℤ))) := by
  intro g m x h u τ a b al hab hW hm hal k n ξ hξ w hw
  obtain rfl : ξ = fun r => u.ex (tors τ al m k n r) := funext hξ
  let P : (Fin 4 → Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4) := fun y =>
    (Out.powIsLimit x.P.A 4).lift (Fan.mk _ fun c => u.ex (y c))
  have hP : ∀ y c, P y ≫ Out.powPr x.P.A c = u.ex (y c) := fun y c =>
    (Out.powIsLimit x.P.A 4).fac (Fan.mk _ fun c => u.ex (y c)) ⟨c⟩
  have hPu : ∀ (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4),
      (∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) → pt = P y := fun y pt hpt =>
    (Out.powIsLimit x.P.A 4).hom_ext fun ⟨c⟩ => (hpt c).trans (hP y c).symm
  have hd : GlobalTheory.PowUnif.IsHolFamily (fun z => (u.ex z).left) := u.hol
  let z : Fin 4 ⊕ Fin 4 → (Fin 4 → Fin g → ℂ) → Fin g → ℂ :=
    Sum.elim (fun r y => ∑ c, al r c • y c + tors τ al m k n r) (fun c y => y c)
  obtain ⟨T, hT, hT0, hTv⟩ := GlobalTheory.T.exists_entire_ne_zero_val_eq_mul_prod_frames x.P.A x.P.L g u x.P.isLB _ _ _ _ w hw (Fin 4 → Fin g → ℂ)
    (fun y => (P y).left) z
    (GlobalTheory.PowUnif.isHolFamily_powObj _ 4 P fun c => by
      simp only [hP]
      exact hd.precomp (T := fun y : Fin 4 → Fin g → ℂ => y c) (by fun_prop))
    (by
      rintro (r | c)
      · change Differentiable ℂ fun y : Fin 4 → Fin g → ℂ => ∑ c, al r c • y c + tors τ al m k n r
        fun_prop
      · change Differentiable ℂ fun y : Fin 4 → Fin g → ℂ => y c
        fun_prop)
    (by
      rintro y (r | c)
      · exact congrArg (·.left) (comp_alMap_ex x u al r _ y (P y) (hP y))
      · exact congrArg (·.left) (hP y c))
  let ee : (Fin 4 → Fin g → ℂ) → ℂ := fun y =>
    Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c)
  have hee : Differentiable ℂ ee := by
    simp only [ee, dotProduct]
    fun_prop
  have hper : ∀ y, ∀ s ∈ {s : Fin 4 → Fin g → ℂ | ∃ c, ∃ l ∈ (u.Λ : Set (Fin g → ℂ)), s = Pi.single c l},
      T (y + s) * ee (y + s) = T y * ee y := by
    rintro y _ ⟨c, l, hl, rfl⟩
    obtain ⟨k₀, n₀, hl'⟩ := (hW.2.2.1 l).1 hl
    obtain rfl : l = lat τ k₀ n₀ := hl'
    have hlat : ∀ (k n : Fin g → ℤ) (v : Fin g → ℂ), u.ex (v + lat τ k n) = u.ex v := fun k n v => by
      rw [u.ex_add, (u.ker (lat τ k n)).2 ((hW.2.2.1 _).2 ⟨k, n, rfl⟩), _root_.mul_one]
    set y' := y + Pi.single c (lat τ k₀ n₀) with hy'
    have hz₁ : ∀ r, z (Sum.inl r) y' = z (Sum.inl r) y + lat τ (al r c • k₀) (al r c • n₀) := fun r => by
      simp only [z, Sum.elim_inl, hy', Pi.add_apply, smul_add, Finset.sum_add_distrib, lat_zsmul]
      rw [Finset.sum_eq_single c (f := fun c' => al r c' • (Pi.single c (lat τ k₀ n₀) : Fin 4 → Fin g → ℂ) c')
        (fun c' _ hc => by rw [Pi.single_eq_of_ne hc, smul_zero]) (by simp),
        Pi.single_eq_same]
      abel
    have hz₂ : y' c = y c + lat τ k₀ n₀ := by simp [hy']
    have hz₃ : ∀ c', c' ≠ c → y' c' = y c' := fun c' hc => by simp [hy', Pi.single_eq_of_ne hc]
    have hex : ∀ q, u.ex (z q y') = u.ex (z q y) := by
      rintro (r | c')
      · rw [hz₁, hlat]
      · change u.ex (y' c') = u.ex (y c')
        by_cases hc : c' = c
        · rw [hc, hz₂, hlat]
        · rw [hz₃ c' hc]
    have hPP : P y' = P y := hPu y _ fun c' => (hP y' c').trans (hex (Sum.inr c'))
    choose j hj using fun q => GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex (z q y)).left
    have hj' : ∀ q, ⊤ ≤ (u.ex (z q y')).left ⁻¹ᵁ x.P.L.U (j q) := fun q => by rw [hex]; exact hj q
    have e₁ := hTv y j hj
    have e₂ := hTv y' j hj'
    rw [hPP, e₁] at e₂
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_one] at e₂
    have f₁ : ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y) =
        (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
          ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y') := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [hz₁]
      exact GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW _ _ _ _ (hj _)
    have f₂ : ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y) ^ (-(m : ℤ)) =
        aut τ a b k₀ n₀ (y c) ^ (-(m : ℤ)) * ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y') ^ (-(m : ℤ)) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
        ← _root_.mul_assoc, ← mul_zpow]
      refine congrArg₂ (· * ·) (congrArg (· ^ _) ?_) (Finset.prod_congr rfl fun c' hc => ?_)
      · change u.fr _ (y c) = _ * u.fr _ (y' c)
        rw [hz₂]
        exact GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW _ _ _ _ (hj (Sum.inr c))
      · change u.fr _ (y c') ^ _ = u.fr _ (y' c') ^ _
        rw [hz₃ c' (Finset.ne_of_mem_erase hc)]
    have n₁ : ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y') ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun r _ => u.fr_ne _ _ (hj' _)
    have n₂ : ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y') ^ (-(m : ℤ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (u.fr_ne _ _ (hj' _))
    have e₃ : T y' = T y * (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
        aut τ a b k₀ n₀ (y c) ^ (-(m : ℤ)) := by
      rw [f₁, f₂] at e₂
      refine mul_right_cancel₀ (mul_ne_zero n₁ n₂) (e₂.symm.trans ?_)
      ring
    have e₄ : ee y' = ee y * Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ lat τ k₀ n₀)) := by
      simp only [ee, hy', Pi.add_apply, dotProduct_add, Finset.sum_add_distrib, mul_add, Complex.exp_add]
      rw [Finset.sum_eq_single c (f := fun c' => (fun i => (n c' i : ℂ)) ⬝ᵥ
          (Pi.single c (lat τ k₀ n₀) : Fin 4 → Fin g → ℂ) c')
        (fun c' _ hc => by rw [Pi.single_eq_of_ne hc, dotProduct_zero]) (by simp), Pi.single_eq_same]
    have e₅ : (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) * _ = _ :=
      (aut_similitude_and_mul g m τ a b al hab hW.1 hm hal).1 k n y c k₀ n₀
    have n₃ := pow_ne_zero m (aut_ne_zero τ a b k₀ n₀ (y c))
    rw [e₃, e₄, zpow_neg, zpow_natCast]
    calc _ = T y * ee y * ((∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
          Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ lat τ k₀ n₀))) *
          (aut τ a b k₀ n₀ (y c) ^ m)⁻¹ := by ring
      _ = _ := by rw [e₅, mul_inv_cancel_right₀ n₃]
  have hc := GlobalTheory.entire_apply_eq_of_periodic_of_span_real (F := fun y => T y * ee y) (hT.mul hee)
    (span_single_block_eq_top u.full) hper
  refine ⟨T 0 * ee 0, mul_ne_zero (hT0 0) (Complex.exp_ne_zero _), fun y pt hpt j hj₁ hj₂ => ?_⟩
  obtain rfl := hPu y pt hpt
  have e₁ := hTv y j (by rintro (r | c); exacts [hj₁ r, hj₂ c])
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_one, z] at e₁
  rw [← hc y 0]
  refine (congrArg (· * ee y) e₁).trans ?_
  ring

end GlobalTheory.SimilTheta
end
