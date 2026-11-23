import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtOfDivisorRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAdelicMetricDivisorRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormUnitLocallyHarmonicStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O

namespace GlobalTheory.CombPot

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem generatesAt_exists_nhds {D : Y.Dv} {x : Y.X} {f : Y.Fn} (h : D.GeneratesAt x f) :
    ∃ U : Y.X.Opens, x ∈ U ∧ ∀ y ∈ U, D.GeneratesAt y f := by
  obtain ⟨g, hg, hu⟩ := h
  obtain ⟨U, hU, hU'⟩ := hg.exists_nhds
  obtain ⟨V, hV, hV'⟩ := hu.exists_nhds
  exact ⟨U ⊓ V, ⟨hU, hV⟩, fun y hy => ⟨g, hU' y hy.1, hV' y hy.2⟩⟩

theorem exists_pot_comb : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (ι : Type) [Fintype ι] (Mb : Adl (cxSt F) Y) (ρ : ι → Adl (cxSt F) Y) (t : ι → ℝ) (g : ∀ σ, Pts Y σ → ℝ) (a : Fin (M.n + 1)) (Q : ι → LocPot (M.X a)), IsComb Mb ρ t g → (∀ i, IsPot (I.pt a) ((ρ i).m (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) → (M.A a).Smooth (fun z => g (I.ε a) (I.pt a z)) → ∃ QM : LocPot (M.X a), IsPot (I.pt a) (Mb.m (I.ε a)) QM ∧ IsPotential (M.A a) QM ∧ ∀ j, ∀ y ∈ ((M.A a).chart j).target, ∀ w, leviAt (M.A a) QM j y w = ((Mb.n : ℕ) : ℝ) * (∑ i, t i / (((ρ i).n : ℕ) : ℝ) * leviAt (M.A a) (Q i) j y w + leviAt (M.A a) (LocPot.ofFun fun z => g (I.ε a) (I.pt a z)) j y w) := by
  intro F _ _ Y e M I ι _ Mb ρ t g a Q hC hQ hg
  obtain ⟨q, b, hq, hqt, hD, hN, -⟩ := hC
  choose f hf using fun i => (hQ i).1
  set σ := I.ε a with hσ
  let fM : M.X a → Y.Fn := fun x => genAt Mb.D (under (I.pt a x))
  have hfM : ∀ x, Mb.D.GeneratesAt (under (I.pt a x)) (fM x) := fun x => generatesAt_genAt _ _
  let h : M.X a → Y.Fn := fun x => fM x ^ q / ∏ i, f i x ^ b i
  have hh : ∀ x, UnitAt (under (I.pt a x)) (h x) := fun x =>
    GlobalTheory.T.unit_at_of_divisor_relation F Y ι Mb.D (fun i => (ρ i).D) q b _ (fM x) (fun i => f i x) hD (hfM x)
      (fun i => by simpa using ((hf i x x ((Q i).mem_U x)).1))
  choose W hWo hxW G hG hGe using fun x => GlobalTheory.T.log_norm_unit_locally_harmonic F Y e M I a (h x) x (hh x)
  choose V hxV hV using fun x => generatesAt_exists_nhds (hfM x)
  set K : ℝ := (q : ℝ) * ((Mb.n : ℕ) : ℝ) * Mb.ci (InfinitePlace.mk σ) -
    ∑ i, (b i : ℝ) * (((ρ i).n : ℕ) : ℝ) * (ρ i).ci (InfinitePlace.mk σ) with hK
  set u : M.X a → ℝ := fun z => ((Mb.n : ℕ) : ℝ) * g σ (I.pt a z) with hu
  have hus : (M.A a).Smooth u := fun j => contDiffOn_const.mul (hg j)
  set P := InhabCalc.combPot Q (fun i => (b i : ℝ) / q) u with hP
  have hPpot : IsPotential (M.A a) P := InhabCalc.isPotential_combPot _ Q (fun i => (hQ i).2) _ u hus
  let QM : LocPot (M.X a) :=
    { U := fun x => (⋂ i, (Q i).U x) ∩ W x ∩ (I.pt a) ⁻¹' ptsIn Y.str σ (V x)
      isOpen_U := fun x => ((isOpen_iInter_of_finite fun i => (Q i).isOpen_U x).inter (hWo x)).inter
        ((isOpen_ptsIn _).preimage (I.pt a).continuous)
      mem_U := fun x => ⟨⟨Set.mem_iInter.2 fun i => (Q i).mem_U x, hxW x⟩, mem_ptsIn.2 (hxV x)⟩
      φ := fun x y => -lnN (Mb.m σ) (fM x) (I.pt a y) }
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.2 hq
  have hform : ∀ x, ∀ y ∈ QM.U x, QM.φ x y = P.φ x y + (-(q : ℝ)⁻¹) * (G x y + (K : ℂ)).re := by
    rintro x y ⟨⟨hy1, hy2⟩, hy3⟩
    have hyi : ∀ i, y ∈ (Q i).U x := fun i => Set.mem_iInter.1 hy1 i
    have hgM : Mb.D.GeneratesAt (under (I.pt a y)) (fM x) := hV x _ (mem_ptsIn.1 hy3)
    have hgi : ∀ i, (ρ i).D.GeneratesAt (under (I.pt a y)) (f i x) := fun i => by
      simpa using (hf i x y (hyi i)).1
    have hk := GlobalTheory.T.unit_at_of_divisor_relation F Y ι Mb.D (fun i => (ρ i).D) q b (under (I.pt a y)) _ _ hD (generatesAt_genAt _ _)
      (fun i => generatesAt_genAt (ρ i).D _)
    have hh' := GlobalTheory.T.unit_at_of_divisor_relation F Y ι Mb.D (fun i => (ρ i).D) q b (under (I.pt a y)) (fM x) (fun i => f i x) hD hgM hgi
    have e := GlobalTheory.T.log_adelic_metric_divisor_relation F Y ι Mb ρ q b σ (I.pt a y) (g σ (I.pt a y)) (fM x) (fun i => f i x) (hN σ _).1
      (fun i => by simpa using (hf i x y (hyi i)).2.1) (hN σ _).2 hgM hgi hk hh'
    have eQ : ∀ i, lnN ((ρ i).m σ) (f i x) (I.pt a y) = -(Q i).φ x y := fun i => by
      have := (hf i x y (hyi i)).2.2
      linarith
    simp only [eQ] at e
    rw [hGe x y hy2] at e
    show -lnN (Mb.m σ) (fM x) (I.pt a y) = (∑ i, (b i : ℝ) / q * (Q i).φ x y + u y) + _
    simp only [hu, Complex.add_re, Complex.ofReal_re]
    rw [← hK] at e
    have hs : ∑ i, (b i : ℝ) / q * (Q i).φ x y = (∑ i, (b i : ℝ) * (Q i).φ x y) / q := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    have hs2 : ∑ i, (b i : ℝ) * -(Q i).φ x y = -∑ i, (b i : ℝ) * (Q i).φ x y := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs2] at e
    rw [hs]
    field_simp
    linear_combination -e
  have hUP : ∀ x, QM.U x ⊆ P.U x := fun x y hy => hy.1.1
  have hUW : ∀ x, QM.U x ⊆ W x := fun x y hy => hy.1.2
  have hGs : ∀ x j, ContDiffOn ℝ (⊤ : ℕ∞) (fun v => (G x (((M.A a).chart j).symm v) + (K : ℂ)).re)
      (((M.A a).chart j).target ∩ ((M.A a).chart j).symm ⁻¹' W x) := by
    intro x j
    have h1 : ContDiffOn ℂ (⊤ : ℕ∞) (G x ∘ ((M.A a).chart j).symm)
        (((M.A a).chart j).target ∩ ((M.A a).chart j).symm ⁻¹' W x) :=
      (hG x j).contDiffOn (((M.A a).chart j).isOpen_inter_preimage_symm (hWo x)).uniqueDiffOn
    exact Complex.reCLM.contDiff.comp_contDiffOn ((h1.restrict_scalars ℝ).add contDiffOn_const)
  refine ⟨QM, fun x => ⟨fM x, fun y hy => ⟨hV x _ (mem_ptsIn.1 hy.2), (hN σ _).1, rfl⟩⟩,
    ⟨fun x j => ?_, fun x x' y hy => ?_⟩, fun j y hy w => ?_⟩
  · have h1 := (hPpot.1 x j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (hUP x)))
    have h2 := (hGs x j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (hUW x)))
    refine (h1.add ((contDiffOn_const (c := -(q : ℝ)⁻¹)).mul h2)).congr fun v hv => ?_
    exact hform x _ hv.2
  · obtain ⟨W1, hW1, hyW1, G1, hG1, hG1e⟩ := hPpot.2 x x' y ⟨hUP x hy.1, hUP x' hy.2⟩
    refine ⟨W1 ∩ W x ∩ W x', (hW1.inter (hWo x)).inter (hWo x'), ⟨⟨hyW1, hUW x hy.1⟩, hUW x' hy.2⟩,
      fun z => G1 z + ((-(q : ℝ)⁻¹ : ℝ) : ℂ) * (G x z - G x' z), fun j => ?_, ?_⟩
    · intro v hv
      have a1 := hG1 j v ⟨hv.1, hv.2.1.1⟩
      have a2 := hG x j v ⟨hv.1, hv.2.1.2⟩
      have a3 := hG x' j v ⟨hv.1, hv.2.2⟩
      exact a1.add (analyticAt_const.mul (a2.sub a3))
    · rintro z ⟨⟨hz, hz1⟩, hz2⟩
      rw [hform x z hz1, hform x' z hz2]
      have := hG1e z ⟨⟨hz.1.1, hUP x hz1⟩, hUP x' hz2⟩
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero]
      linarith
  · set x0 := ((M.A a).chart j).symm y with hx0
    have hS : IsOpen (((M.A a).chart j).target ∩ ((M.A a).chart j).symm ⁻¹' QM.U x0) :=
      ((M.A a).chart j).isOpen_inter_preimage_symm (QM.isOpen_U x0)
    have hyS : y ∈ ((M.A a).chart j).target ∩ ((M.A a).chart j).symm ⁻¹' QM.U x0 := ⟨hy, QM.mem_U x0⟩
    have hev : (QM.φ x0 ∘ ((M.A a).chart j).symm) =ᶠ[nhds y] fun v => (P.φ x0 ∘ ((M.A a).chart j).symm) v +
        (-(q : ℝ)⁻¹) * (G x0 (((M.A a).chart j).symm v) + (K : ℂ)).re := by
      filter_upwards [hS.mem_nhds hyS] with v hv
      exact hform x0 _ hv.2
    have hP2 : ContDiffAt ℝ 2 (P.φ x0 ∘ ((M.A a).chart j).symm) y :=
      GlobalTheory.LeviOnly.pot_two hPpot x0 j hy (P.mem_U x0)
    have hGa : AnalyticAt ℂ (fun v => G x0 (((M.A a).chart j).symm v) + (K : ℂ)) y :=
      (hG x0 j y ⟨hy, hUW x0 (QM.mem_U x0)⟩).add analyticAt_const
    have hRe2 : ContDiffAt ℝ 2 (fun v => (G x0 (((M.A a).chart j).symm v) + (K : ℂ)).re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
    have e1 : leviAt (M.A a) QM j y w = leviAt (M.A a) P j y w := by
      show levi (QM.φ x0 ∘ ((M.A a).chart j).symm) y w = levi (P.φ x0 ∘ ((M.A a).chart j).symm) y w
      rw [levi_congr hev, levi_add_smul _ hP2 hRe2, levi_re_analytic hGa, mul_zero, add_zero]
    have e2 := LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.leviAt_combPot e (M.X a) (M.A a) ι Q (fun i => (b i : ℝ) / q) u (fun i => (hQ i).2) hus j y hy w
    have hg2 : ContDiffAt ℝ 2 ((fun z => g σ (I.pt a z)) ∘ ((M.A a).chart j).symm) y :=
      ((hg j).contDiffAt ((((M.A a).chart j).isOpen_inter_preimage_symm isOpen_univ).mem_nhds
        ⟨hy, Set.mem_univ _⟩)).of_le (WithTop.coe_le_coe.2 le_top)
    have e3 : leviAt (M.A a) (LocPot.ofFun u) j y w =
        ((Mb.n : ℕ) : ℝ) * leviAt (M.A a) (LocPot.ofFun fun z => g σ (I.pt a z)) j y w := by
      have h0 : levi (fun _ : Fin e → ℂ => (0 : ℝ)) y w = 0 := by simp [levi]
      have := levi_add_smul ((Mb.n : ℕ) : ℝ) (contDiffAt_const (c := (0 : ℝ))) hg2 w
      rw [h0, zero_add] at this
      simp only [zero_add] at this
      exact this
    rw [e1, e2, e3, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hn : (0 : ℝ) < (((ρ i).n : ℕ) : ℝ) := Nat.cast_pos.2 (ρ i).n.pos
    have hc : (b i : ℝ) / q = ((Mb.n : ℕ) : ℝ) * t i / (((ρ i).n : ℕ) : ℝ) := by
      rw [div_eq_div_iff hqpos.ne' hn.ne']
      linear_combination -(hqt i)
    rw [hc]
    ring

end GlobalTheory.CombPot
