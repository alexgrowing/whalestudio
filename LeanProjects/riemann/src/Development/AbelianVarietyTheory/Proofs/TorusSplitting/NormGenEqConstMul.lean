import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertTrivialOfNowhereVanishing

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstNorm

theorem exists_entire {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {e : W → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    {c : V → (Sp ℂ ⟶ Y)} (hc : IsHolTo Set.univ c) {fr : L.ι → W → ℂ}
    (hd : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j})
    (hne : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (hcomp : ∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.U j ⊓ L.U j') →
      fr j z = valAt' (e z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z)
    {K : Type} [Fintype K] {m : K → (Y ⟶ X)} {ε : K → ℤ} {w : K → V → W} (hwd : ∀ k, Differentiable ℂ (w k))
    (hw : ∀ k z, c z ≫ m k = e (w k z)) (α : LB.Gen (LB.LinComb L m ε)) (hα : α.IsGen) :
    ∃ r : V → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧ ∀ z (j : K → L.ι), (∀ k, ⊤ ≤ e (w k z) ⁻¹ᵁ L.U (j k)) →
      valAt' (c z) (LB.wchart L m j) (α.s j).val = r z * ∏ k, fr (j k) (w k z) ^ ε k := by
  classical
  have hv : CubeValues.ValueRules := valAt'_rules
  have hch : ∀ y : W, ∃ i, ⊤ ≤ e y ⁻¹ᵁ L.U i := fun y => by
    have h : e y (default : PrimeSpectrum ℂ) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩
  choose ch hch using hch
  have hiff : ∀ z (j : K → L.ι), ⊤ ≤ c z ⁻¹ᵁ LB.wchart L m j ↔ ∀ k, ⊤ ≤ e (w k z) ⁻¹ᵁ L.U (j k) := fun z j => by
    simp only [CubeValues.le_preimage_wchart, hw]
  let R : (K → L.ι) → V → ℂ := fun j z =>
    valAt' (c z) (LB.wchart L m j) (α.s j).val * ∏ k, fr (j k) (w k z) ^ (-ε k)
  let r : V → ℂ := fun z => R (fun k => ch (w k z)) z
  have hc0 : ∀ z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L m (fun k => ch (w k z)) := fun z => (hiff z _).2 fun k => hch _
  have hrR : ∀ z (j : K → L.ι), (∀ k, ⊤ ≤ e (w k z) ⁻¹ᵁ L.U (j k)) → r z = R j z := fun z j hj => by
    have hj' := (hiff z j).2 hj
    have e1 := (CubeValues.val_gen _ hv α hα _ j (hc0 z) hj').trans (congrArg (· * _)
      (CubeValues.val_linComb (c z) hv L _ _ _ j (hc0 z) hj'))
    simp only [hw] at e1
    refine (congrArg (fun t => t * _) e1).trans ?_
    rw [mul_right_comm, _root_.mul_comm, ← Finset.prod_mul_distrib]
    refine congrArg (_ * ·) (Finset.prod_congr rfl fun k _ => ?_)
    have k0 := (CubeValues.le_preimage_inf _ _ _).2 ⟨hch (w k z), hj k⟩
    have n0 := zpow_ne_zero (ε k) (CubeValues.val_unit_ne_zero _ hv k0 (L.g _ _))
    rw [hcomp _ _ _ k0, mul_zpow, zpow_neg, mul_inv_cancel_left₀ n0]
  have hopen : ∀ i, IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ L.U i} := fun i => by simpa using (he (L.U i) 0).1
  refine ⟨r, fun z => ?_, fun z => ?_, fun z j hj => ?_⟩
  · set j : K → L.ι := fun k => ch (w k z)
    obtain ⟨ho, hd'⟩ := hc _ (α.s j).val
    have hn := ho.mem_nhds ⟨Set.mem_univ z, hc0 z⟩
    have d1 : ∀ k, DifferentiableAt ℂ (fun y => fr (j k) (w k y) ^ (-ε k)) z := fun k =>
      (((hd _).differentiableAt ((hopen _).mem_nhds (hch (w k z)))).comp z (hwd k z)).zpow
        (Or.inl (hne _ _ (hch (w k z))))
    have hq : DifferentiableAt ℂ (R j) z :=
      (hd'.differentiableAt hn).mul (HasFDerivAt.finset_prod fun k _ => (d1 k).hasFDerivAt).differentiableAt
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [hn] with y hy
    exact hrR y j ((hiff y j).1 hy.2)
  · exact mul_ne_zero (CubeValues.val_unit_ne_zero _ hv (hc0 z) _)
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne _ _ (hch _)))
  · rw [hrR z j hj]
    simp only [R]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one, _root_.mul_one]
    intro k _
    rw [← zpow_add₀ (hne _ _ (hj k)), neg_add_cancel, zpow_zero]

open AppellHumbertTrivial in

theorem norm_mul_exp_add {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) {x y χ : ℂ} {z l : Fin g → ℂ}
    (hχ : ‖χ‖ = 1) (h : x = χ * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * y) :
    ‖y‖ * Real.exp (Real.pi / 2 * (hermForm Hm (z + l) (z + l)).re) =
      ‖x‖ * Real.exp (Real.pi / 2 * (hermForm Hm z z).re) := by
  rw [h, norm_mul, norm_mul, hχ, _root_.one_mul, Complex.norm_exp, _root_.mul_comm _ ‖y‖, _root_.mul_assoc,
    ← Real.exp_add, re_hermForm_add_self hH]
  have e : ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  congr 2
  ring

open AppellHumbertTrivial in

theorem exists_entire_weight {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) {K : Type} [Fintype K]
    (ε n : K → ℤ) (a : K → Fin g → ℂ) (h0 : ∑ k, ε k * n k ^ 2 = 0) :
    ∃ φ : (Fin g → ℂ) → ℂ, Differentiable ℂ φ ∧ ∀ z, Real.exp (φ z).re =
      ∏ k, Real.exp (Real.pi / 2 * (hermForm Hm ((n k : ℂ) • z + a k) ((n k : ℂ) • z + a k)).re) ^ ε k := by
  refine ⟨fun z => ∑ k, (((ε k * n k * Real.pi : ℝ) : ℂ) * hermForm Hm z (a k) +
    ((ε k * (Real.pi / 2) : ℝ) : ℂ) * hermForm Hm (a k) (a k)), ?_, fun z => ?_⟩
  · unfold hermForm dotProduct
    fun_prop
  · have hz : ∀ (t : ℝ) (s : ℤ), Real.exp t ^ s = Real.exp (s * t) := fun t s => by
      rw [← Real.rpow_intCast, ← Real.exp_mul, _root_.mul_comm]
    simp only [hz]
    rw [← Real.exp_sum, Complex.re_sum]
    congr 1
    have h1 : ∑ k, ((ε k * n k ^ 2 : ℤ) : ℝ) * (Real.pi / 2 * (hermForm Hm z z).re) = 0 := by
      rw [← Finset.sum_mul, ← Int.cast_sum, h0, Int.cast_zero, zero_mul]
    rw [← add_zero (∑ k, _), ← h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [re_hermForm_add_self hH, hermForm_smul_left, hermForm_smul_left, hermForm_smul_right]
    simp only [Complex.add_re, Complex.re_ofReal_mul, star_intCast]
    rw [← Complex.ofReal_intCast, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    push_cast
    ring

theorem isHolTo_ptSecT {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} (G : Over X)
    (y : Sp ℂ ⟶ X) (e : V → (Over.mk y ⟶ G)) (he : IsHolTo Set.univ fun z => (e z).left) :
    IsHolTo Set.univ fun z => (Out.ptSecT G (e z)).left := by
  have h1 : ∀ z, (Out.ptSecT G (e z)).left ≫ (fst (Over.mk y) G).left = 𝟙 _ := fun z => by
    rw [← Over.comp_left, Out.ptSecT, lift_fst, Over.id_left]
  have h2 : ∀ z, (Out.ptSecT G (e z)).left ≫ (snd (Over.mk y) G).left = (e z).left := fun z => by
    rw [← Over.comp_left, Out.ptSecT, lift_snd]
  refine HolFibre.isHolTo_of_isPullback (Z := (Over.mk y ⊗ G).left) (p := (fst (Over.mk y) G).left)
    (q := (snd (Over.mk y) G).left) (s := (Over.mk y).hom) (t := G.hom)
    (IsPullback.of_hasPullback (Over.mk y).hom G.hom) ?_ ?_
  · exact (funext h1).symm ▸ HolFibre.isHolTo_const isOpen_univ _
  · exact (funext h2).symm ▸ he

theorem isHolTo_slice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} {e : V × W → (Sp ℂ ⟶ X)} (he : IsHolTo (Set.univ ×ˢ Set.univ) e) (v : V) :
    IsHolTo Set.univ fun w => e (v, w) := fun U f => by
  obtain ⟨ho, hf⟩ := he U f
  have hι : Differentiable ℂ (fun w : W => (v, w)) := by fun_prop
  refine ⟨?_, hf.comp hι.differentiableOn fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩⟩
  have h := ho.preimage hι.continuous
  simp only [Set.univ_prod_univ] at h
  exact h

theorem norm_gen_eq_const_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (Fu.Di i) ty Pm → AHFrame Fu i Pm Hm χl fr → ∀ (K : Type) [Fintype K] (m : K → (Gx (Fu.u i Pm) ⟶ Xo.univ.t.G.left)) (ε n : K → ℤ) (a : K → Fin g → ℂ) (α : LB.Gen (LB.LinComb Xo.univ.t.PP.L m ε)), α.IsGen → ∑ k, ε k * n k ^ 2 = 0 → (∀ k z, (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z)).left ≫ m k = (Fu.ex i Pm ((n k : ℂ) • z + a k)).left) → ∃ C : ℝ, 0 < C ∧ ∀ (z : Fin g → ℂ) (j : K → Xo.univ.t.PP.L.ι), (∀ k, ⊤ ≤ (Fu.ex i Pm ((n k : ℂ) • z + a k)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j k)) → ‖valAt' (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z)).left ((LB.LinComb Xo.univ.t.PP.L m ε).U j) (α.s j).val‖ = C * ∏ k, (‖fr (j k) ((n k : ℂ) • z + a k)‖ * Real.exp (Real.pi / 2 * (hermForm Hm ((n k : ℂ) • z + a k) ((n k : ℂ) • z + a k)).re)) ^ ε k := by
  intro E _ _ _ H Dw l Xo σ g ty Fu i Pm Hm χl fr hP hF K _ m ε n a α hα h0 hm
  obtain ⟨hH, -, -, hd, hne, hcomp, -, hAH⟩ := hF
  have he : IsHolTo Set.univ (fun z => (Fu.ex i Pm z).left) :=
    isHolTo_slice (Fu.hol i 0 Set.univ (fun _ => Pm) isOpen_univ
      ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 0
  have hc := isHolTo_ptSecT Xo.univ.t.G _ _ he
  have hper : ∀ z b, Fu.ex i Pm (z + Pm b) = Fu.ex i Pm z := fun z b => by
    rw [Fu.ex_add i Pm hP, (Fu.ex_ker i Pm hP _).2 ⟨b, rfl⟩, _root_.mul_one]
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨r, hrd, hr0, hr⟩ := exists_entire hL he hc hd hne hcomp (w := fun k z => (n k : ℂ) • z + a k)
    (fun k => by fun_prop) hm α hα
  obtain ⟨φ, hφd, hφ⟩ := exists_entire_weight hH ε n a h0
  let F : (Fin g → ℂ) → ℂ := fun z => r z * Complex.exp (-φ z)
  have hFd : Differentiable ℂ F := hrd.mul hφd.neg.cexp
  have key : ∀ (z : Fin g → ℂ) (j : K → Xo.univ.t.PP.L.ι),
      (∀ k, ⊤ ≤ (Fu.ex i Pm ((n k : ℂ) • z + a k)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j k)) →
      ‖valAt' (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z)).left ((LB.LinComb Xo.univ.t.PP.L m ε).U j) (α.s j).val‖ =
        ‖F z‖ * ∏ k, (‖fr (j k) ((n k : ℂ) • z + a k)‖ * Real.exp (Real.pi / 2 *
          (hermForm Hm ((n k : ℂ) • z + a k) ((n k : ℂ) • z + a k)).re)) ^ ε k := fun z j hj => by
    refine (congrArg norm (hr z j hj)).trans ?_
    simp only [F, mul_zpow, Finset.prod_mul_distrib, ← hφ, norm_mul, norm_prod, norm_zpow, Complex.norm_exp,
      Complex.neg_re, Real.exp_neg]
    field_simp
  have hFp : ∀ b z, ‖F (z + Pm b)‖ = ‖F z‖ := fun b z => by
    have hch : ∀ k, ∃ j, ⊤ ≤ (Fu.ex i Pm ((n k : ℂ) • z + a k)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun k => by
      have h : (Fu.ex i Pm ((n k : ℂ) • z + a k)).left (default : PrimeSpectrum ℂ) ∈
          (⨆ j, Xo.univ.t.PP.L.U j) := by rw [hL.cover]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
    choose j hj using hch
    have hs : ∀ k, (n k : ℂ) • (z + Pm b) + a k = (n k : ℂ) • z + a k + Pm (n k • b) := fun k => by
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, smul_add]
      abel
    have e1 := key z j hj
    have e2 := key (z + Pm b) j fun k => by rw [hs, hper]; exact hj k
    rw [hper, e1] at e2
    simp only [hs] at e2
    rw [Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k)
      (norm_mul_exp_add hH (hAH (n k • b) (j k) ((n k : ℂ) • z + a k)).1 ((hAH (n k • b) (j k) _).2 (hj k)))] at e2
    exact (mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _
      (mul_ne_zero (norm_ne_zero_iff.2 (hne _ _ (hj k))) (Real.exp_ne_zero _))) e2).symm
  haveI : DiscreteTopology (AddSubgroup.toIntSubmodule Pm.range) := hP.2.2.1
  have hb : Bornology.IsBounded (Set.range F) := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      (AppellHumbertTrivial.exists_bound_of_periodic (AddSubgroup.toIntSubmodule Pm.range) hP.2.2.2.1
        (fun z => ‖F z‖) hFd.continuous.norm (by rintro ⟨_, b, rfl⟩ z; exact hFp b z))
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa using hC _ ⟨z, rfl⟩
  refine ⟨‖F 0‖, norm_pos_iff.2 (mul_ne_zero (hr0 0) (Complex.exp_ne_zero _)), fun z j hj => ?_⟩
  rw [key z j hj, hFd.apply_eq_apply_of_bounded hb z 0]

end GlobalTheory.ConstNorm
