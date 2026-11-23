import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetE
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsHolomorphicGeneratorReadingAutomorphy
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

private theorem star_hermForm_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (herm : Hm.IsHermitian)
    (z w : Fin g → ℂ) : star (hermForm Hm z w) = hermForm Hm w z := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← herm.apply j i, star_star]
  ring

private theorem norm_exp_neg_hermForm_mul_exp_hermForm_eq_one {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (herm : Hm.IsHermitian) (r : ℝ)
    (x a : Fin g → ℂ) :
    ‖Complex.exp (-((r : ℂ) * hermForm Hm x a)) * Complex.exp ((r : ℂ) * hermForm Hm a x)‖ = 1 := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add, ← star_hermForm_of_isHermitian Hm herm x a]
  simp

theorem thConst_liouville {g : ℕ} (lat : AddSubgroup (Fin g → ℂ))
    (span : Submodule.span ℝ (lat : Set (Fin g → ℂ)) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ) (herm : Hm.IsHermitian)
    (k : ℤ) (x : Fin g → ℂ) (v : (Fin g → ℂ) → ℂ) (hv : Differentiable ℂ v)
    (hper : ∀ z, ∀ a ∈ lat, v (z + a) = v z * Complex.exp (-((k : ℂ) * Real.pi * hermForm Hm x a))) (z : Fin g → ℂ) :
    v z = v 0 * Complex.exp (-((k : ℂ) * Real.pi * hermForm Hm z x)) := by

  set c : ℝ := (k : ℝ) * Real.pi with hcdef
  have hcC : ((k : ℂ) * Real.pi) = (c : ℂ) := by rw [hcdef]; push_cast; ring
  simp only [hcC] at hper ⊢
  set f : (Fin g → ℂ) → ℂ := fun y => v y * Complex.exp ((c : ℂ) * hermForm Hm y x) with hf
  have hlin : ∀ y a : Fin g → ℂ, hermForm Hm (y + a) x = hermForm Hm y x + hermForm Hm a x := fun y a => by
    simp [hermForm, add_dotProduct]
  have hfd : Differentiable ℂ f := by
    refine hv.mul (Differentiable.cexp (Differentiable.const_mul ?_ _))
    simp only [hermForm, dotProduct]
    fun_prop
  have hperf : ∀ y, ∀ a ∈ lat, ‖f (y + a)‖ = ‖f y‖ := by
    intro y a ha
    have e1 : f (y + a) = (v y * Complex.exp ((c : ℂ) * hermForm Hm y x)) *
        (Complex.exp (-((c : ℂ) * hermForm Hm x a)) * Complex.exp ((c : ℂ) * hermForm Hm a x)) := by
      simp only [hf, hper y a ha, hlin, mul_add, Complex.exp_add]
      ring
    rw [e1, norm_mul, norm_exp_neg_hermForm_mul_exp_hermForm_eq_one Hm herm c x a, _root_.mul_one]

  obtain ⟨s, hsl, hss, hli⟩ := exists_linearIndependent ℝ (lat : Set (Fin g → ℂ))
  rw [span] at hss
  let b : Module.Basis s ℝ (Fin g → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact hss.ge)
  have : Finite s := Module.Finite.finite_basis b
  letI : Fintype s := Fintype.ofFinite s
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (ZSpan.fundamentalDomain_isBounded b).closure
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hfd.continuous.continuousOn
  have hmem : ∀ y, y - ZSpan.fract b y ∈ lat := by
    intro y
    rw [ZSpan.fract_apply, sub_sub_cancel]
    have h1 : Submodule.span ℤ (Set.range b) ≤ lat.toIntSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa [b, Module.Basis.mk_apply] using hsl i.2
    exact h1 (ZSpan.floor b y).2
  have hbd : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h2 := hperf (ZSpan.fract b y) _ (hmem y)
    rw [add_sub_cancel] at h2
    rw [h2]
    exact hM _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b y))
  have h0 := hfd.apply_eq_apply_of_bounded hbd z 0
  have hz0 : hermForm Hm 0 x = 0 := by simp [hermForm]
  simp only [hf, hz0, mul_zero, Complex.exp_zero, _root_.mul_one] at h0
  rw [← h0, _root_.mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, _root_.mul_one]

private theorem fac_zpow_mul_fac_add_zpow_neg_eq_exp {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (k : ℤ) (x : Fin g → ℂ) {a : Fin g → ℂ} (ha : a ∈ Φ.lat) (z : Fin g → ℂ) :
    Φ.fac a z ^ k * Φ.fac a (x + z) ^ (-k) = Complex.exp (-((k : ℂ) * Real.pi * hermForm Φ.Hm x a)) := by
  have hχ : Φ.χ a ≠ 0 := by
    intro h
    have h1 := Φ.χ_norm a ha
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hne : Φ.fac a (x + z) ≠ 0 := mul_ne_zero hχ (Complex.exp_ne_zero _)
  have hq : Φ.fac a z = Φ.fac a (x + z) * Complex.exp (-((Real.pi : ℂ) * hermForm Φ.Hm x a)) := by
    simp only [AnFr.fac, hermForm, add_dotProduct]
    rw [_root_.mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hq, mul_zpow, zpow_neg, mul_comm (Φ.fac a (x + z) ^ k), _root_.mul_assoc,
    mul_inv_cancel₀ (zpow_ne_zero _ hne), _root_.mul_one, ← Complex.exp_int_mul]
  congr 1
  ring

theorem exists_thConst : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ), U.pt = Φ.e x → ∃ c : ℂ, c ≠ 0 ∧ Φ.ThConst k U x c := by
  intro S A _ _ L x0 g Φ k U x hU

  have hs : ∀ t : Over.mk x0 ⟶ A, ptSecT A t ≫ snd (Over.mk x0) A = t := by
    intro t
    simp [ptSecT]
  have ht : ∀ t : Over.mk x0 ⟶ A, ptSecT A t ≫ translPt A U.pt = U.pt * t := by
    intro t
    simp only [ptSecT, translPt, Hom.mul_def, ← Category.assoc, comp_lift, lift_fst, lift_snd, Category.id_comp]
  have hh : IsHolFam (g := g) (fun z => (ptSecT A (Φ.e z)).left) := by
    have h := isHolFam_pullback_lift S (Over.mk x0).left A.left (Over.mk x0).hom A.hom g (fun _ => 𝟙 _)
      (fun z => (Φ.e z).left) x0 (fun _ => Category.id_comp _) (fun z => Over.w (Φ.e z))
      (isHolFam_const (g := g) _) Φ.hol
    exact h
  have hdiff : ∀ i : Fin 2, Differentiable ℂ ((![fun z => z, fun z => x + z] : Fin 2 → (Fin g → ℂ) → Fin g → ℂ) i) :=
    Fin.forall_fin_two.2 ⟨differentiable_id, (differentiable_const x).add differentiable_id⟩
  have hq : ∀ (z : Fin g → ℂ) (i : Fin 2), (ptSecT A (Φ.e z)).left ≫
      (![(snd (Over.mk x0) A).left, (translPt A U.pt).left] : Fin 2 → _) i =
      (Φ.e ((![fun z => z, fun z => x + z] : Fin 2 → (Fin g → ℂ) → Fin g → ℂ) i z)).left := by
    intro z
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show (ptSecT A (Φ.e z)).left ≫ (snd (Over.mk x0) A).left = (Φ.e z).left
      rw [← Over.comp_left, hs]
    · show (ptSecT A (Φ.e z)).left ≫ (translPt A U.pt).left = (Φ.e (x + z)).left
      rw [← Over.comp_left, ht, hU, Φ.e_add]

  obtain ⟨v, hvd, hv0, hvR, -, hvP⟩ := GlobalTheory.AnValGenRd.exists_reading S A L x0 g Φ (Over.mk x0 ⊗ A).left (Fin 2)
    ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] ![k, -k] U.φ U.isGen g
    (fun z => (ptSecT A (Φ.e z)).left) ![fun z => z, fun z => x + z] hh hdiff hq
  have hper : ∀ z, ∀ a ∈ Φ.lat, v (z + a) = v z * Complex.exp (-((k : ℂ) * Real.pi * hermForm Φ.Hm x a)) := by
    intro z a ha
    have hqa : (ptSecT A (Φ.e (z + a))).left = (ptSecT A (Φ.e z)).left := by
      rw [Φ.e_add, (Φ.e_ker a).2 ha, _root_.mul_one]
    have h := hvP z (z + a) (fun _ => a) hqa (Fin.forall_fin_two.2 ⟨⟨ha, rfl⟩, ⟨ha, (add_assoc x z a).symm⟩⟩)
    rw [Fin.prod_univ_two] at h
    rw [h, ← fac_zpow_mul_fac_add_zpow_neg_eq_exp Φ k x ha z]
    rfl
  refine ⟨v 0 * Complex.exp ((k : ℂ) * Real.pi * hermForm Φ.Hm x x / 2),
    mul_ne_zero (hv0 0) (Complex.exp_ne_zero _), hU, fun z => ?_⟩
  have hvz : v 0 * Complex.exp ((k : ℂ) * Real.pi * hermForm Φ.Hm x x / 2) * fock Φ.Hm k x (fun _ => 1) z = v z := by
    rw [thConst_liouville Φ.lat Φ.span Φ.Hm Φ.herm k x v hvd hper z]
    simp only [fock, _root_.mul_one]
    rw [_root_.mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hp : (fun i : Fin 2 => (![fun z => z, fun z => x + z] : Fin 2 → (Fin g → ℂ) → Fin g → ℂ) i z) = ![z, x + z] := by
    funext i
    fin_cases i <;> rfl
  have hR := hvR z
  rw [hp] at hR
  rw [hvz]
  exact hR

end GlobalTheory.AnVal
