import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam
open scoped Topology

namespace GlobalTheory.BdFnCompare

section Manifold

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {R : AnRead p σ d}
  {C C' : Closeds Y} {n n' : CxPts p σ → ℝ}

theorem exists_sq_le_nhds (hC : C' ≤ C) (h : IsDivNorm R C n) (h' : IsDivNorm R C' n') (y₀ : CxPts p σ) :
    ∃ K : ℝ, ∀ᶠ z in 𝓝 y₀, n z ^ 2 ≤ K * n' z ^ 2 := by
  obtain ⟨V, t, f, hy, ht, hf, e⟩ := h.2 y₀
  obtain ⟨V', t', f', hy', ht', hf', e'⟩ := h'.2 y₀
  obtain ⟨g, g', hg, hxg⟩ := exists_basicOpen_le_affine_inter V.2 V'.2 _ ⟨mem_ptsIn.1 hy, mem_ptsIn.1 hy'⟩
  let W : Y.affineOpens := Y.affineBasicOpen g
  have hWV : W ≤ V := Y.basicOpen_le g
  have hWV' : W ≤ V' := by
    show Y.basicOpen g ≤ V'.1
    rw [hg]
    exact Y.basicOpen_le g'
  have hyW : y₀ ∈ ptsIn p σ W.1 := mem_ptsIn.2 hxg
  have m1 : (Y.presheaf.map (homOfLE hWV).op).hom t ∈ (Scheme.IdealSheafData.vanishingIdeal C').ideal W := by
    refine Scheme.IdealSheafData.vanishingIdeal_antimono hC W ?_
    rw [← (Scheme.IdealSheafData.vanishingIdeal C).map_ideal hWV, ht]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self t)
  rw [← (Scheme.IdealSheafData.vanishingIdeal C').map_ideal hWV', ht', Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton'] at m1
  obtain ⟨a, ha⟩ := m1
  have hev : ∀ z ∈ ptsIn p σ W.1, ev p σ V.1 t z = ev p σ W.1 a z * ev p σ V'.1 t' z := fun z hz => by
    rw [← ev_res hWV hz t, ← ev_res hWV' hz t', ← ev_mul]
    exact congrArg (fun u => ev p σ W.1 u z) ha.symm
  have c1 : ContinuousAt (fun z => ‖ev p σ W.1 a z‖ ^ 2 * Real.exp (f' z - f z)) y₀ :=
    ((((continuousOn_ev a).continuousAt ((isOpen_ptsIn _).mem_nhds hyW)).norm.pow 2).mul
      (Real.continuous_exp.continuousAt.comp
        (((hf'.continuousOn (isOpen_ptsIn _)).continuousAt ((isOpen_ptsIn _).mem_nhds hy')).sub
          ((hf.continuousOn (isOpen_ptsIn _)).continuousAt ((isOpen_ptsIn _).mem_nhds hy)))))
  refine ⟨‖ev p σ W.1 a y₀‖ ^ 2 * Real.exp (f' y₀ - f y₀) + 1, ?_⟩
  filter_upwards [c1.eventually (gt_mem_nhds (lt_add_one _)), (isOpen_ptsIn W.1).mem_nhds hyW] with z h1 hz
  have e1 : n z ^ 2 = ‖ev p σ W.1 a z‖ ^ 2 * Real.exp (f' z - f z) * n' z ^ 2 := by
    rw [e z (ptsIn_mono hWV hz), e' z (ptsIn_mono hWV' hz), hev z hz, norm_mul, mul_pow,
      show -f z = (f' z - f z) + -f' z by ring, Real.exp_add]
    ring
  rw [e1]
  exact mul_le_mul_of_nonneg_right h1.le (sq_nonneg _)

theorem exists_sq_le [CompactSpace (CxPts p σ)] (hC : C' ≤ C) (h : IsDivNorm R C n) (h' : IsDivNorm R C' n') :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ z, n z ^ 2 ≤ K * n' z ^ 2 := by
  choose K hK using exists_sq_le_nhds hC h h'
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun y => {z | n z ^ 2 ≤ K y * n' z ^ 2}) fun y _ => hK y
  have h0 : 0 ≤ ∑ y ∈ t, |K y| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨1 + ∑ y ∈ t, |K y|, by linarith, fun z => ?_⟩
  obtain ⟨y, hy, hz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
  have h1 := Finset.single_le_sum (f := fun y => |K y|) (fun _ _ => abs_nonneg _) hy
  exact le_trans hz (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (K y)]) (sq_nonneg _))

end Manifold

theorem exists_le_of_compList {X : Scheme.{0}} {B : Set X} {m m' : ℕ} {C : Fin m → Closeds X} {C' : Fin m' → Closeds X}
    (hC : ReciprocityTheory.AnForm.R.FinalTheorems.CompList B C) (hC' : ReciprocityTheory.AnForm.R.FinalTheorems.CompList B C') (j : Fin m') :
    ∃ i, C' j ≤ C i := by
  classical
  obtain ⟨z, hz, hDz⟩ := (isIrreducible_iff_sUnion_isClosed.1 (hC'.1 j))
    (Finset.univ.image fun i => (C i : Set X))
    (fun z hz => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      exact (C i).isClosed)
    (by
      have h1 : (C' j : Set X) ⊆ B := hC'.2.1 ▸ Set.subset_iUnion (fun j => (C' j : Set X)) j
      refine h1.trans (hC.2.1 ▸ Set.iUnion_subset fun i => ?_)
      exact Set.subset_sUnion_of_mem (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
  exact ⟨i, hDz⟩

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem exists_r_le_at (x x' : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) :
    ∃ K : ℝ, ∀ y : CxPts (genStr s.T.Z) σ, ¬ LiesIn y (genBd s.T.Z) → x'.r σ y ≤ K * x.r σ y := by
  have : CompactSpace (CxPts (genStr s.T.Z) σ) :=
    CxPts.compactSpace σ (ProjSpace.isProjOver_pullback_snd _ s.T.Z.proj)
  choose ι hι using exists_le_of_compList x.cpt_list x'.cpt_list
  choose K hK1 hK using fun i => exists_sq_le (hι i) (x.nrm_div σ (ι i)) (x'.nrm_div σ i)
  refine ⟨1 + ∑ i, (1 + Real.log (K i)), fun y hy => ?_⟩
  have hr := x.exp_le_r σ y
  have he : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hP : 0 < ∏ i, x.nrm σ i y := Finset.prod_pos fun i _ => x.nrm_pos hy i
  have key : ∀ i, -Real.log (x'.nrm σ i y ^ 2) ≤ (1 + Real.log (K i)) * x.r σ y := fun i => by
    have h1 : ∏ i, x.nrm σ i y ≤ x.nrm σ (ι i) y := by
      classical
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (ι i))]
      exact mul_le_of_le_one_right ((x.nrm_div σ _).1 y).1
        (Finset.prod_le_one (fun i _ => ((x.nrm_div σ i).1 y).1) fun i _ => ((x.nrm_div σ i).1 y).2)
    have h2 : (∏ i, x.nrm σ i y) ^ 2 ≤ K i * x'.nrm σ i y ^ 2 := (pow_le_pow_left₀ hP.le h1 2).trans (hK i y)
    have h3 := Real.log_le_log (pow_pos hP 2) h2
    rw [Real.log_mul (by linarith [hK1 i]) (pow_pos (x'.nrm_pos hy i) 2).ne'] at h3
    have h4 : x.r σ y = Real.exp 1 - Real.log ((∏ i, x.nrm σ i y) ^ 2) := rfl
    have h5 : Real.log (K i) ≤ Real.log (K i) * x.r σ y :=
      le_mul_of_one_le_right (Real.log_nonneg (hK1 i)) (he.trans hr)
    linarith
  have e : x'.r σ y = Real.exp 1 + ∑ i, -Real.log (x'.nrm σ i y ^ 2) := by
    rw [OddPrimesWithRootsOfUnity.r, ← Finset.prod_pow, Real.log_prod (fun i _ => (pow_pos (x'.nrm_pos hy i) 2).ne'),
      Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [e, add_mul, one_mul, Finset.sum_mul]
  exact add_le_add hr (Finset.sum_le_sum fun i _ => key i)

theorem exists_r_le (x x' : ToroidalCompactificationData s) : ∃ K : ℝ, 1 ≤ K ∧ ∀ (σ : κ.c.F →+* ℂ) (y : CxPts (genStr s.T.Z) σ),
    ¬ LiesIn y (genBd s.T.Z) → x'.r σ y ≤ K * x.r σ y := by
  choose K hK using exists_r_le_at x x'
  have h0 : 0 ≤ ∑ σ, |K σ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨1 + ∑ σ, |K σ|, by linarith, fun σ y hy => (hK σ y hy).trans ?_⟩
  have h1 := Finset.single_le_sum (f := fun σ => |K σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)
  exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self (K σ)]) ((Real.exp_pos 1).le.trans (x.exp_le_r σ y))

theorem exists_log_r_le (x x' : ToroidalCompactificationData s) : ∃ L : ℝ, 1 ≤ L ∧ ∀ (σ : κ.c.F →+* ℂ) (y : CxPts (genStr s.T.Z) σ),
    ¬ LiesIn y (genBd s.T.Z) → Real.log (x'.r σ y) ≤ L * Real.log (x.r σ y) := by
  obtain ⟨K, hK1, hK⟩ := exists_r_le x x'
  have hl := Real.log_nonneg hK1
  refine ⟨1 + Real.log K, by linarith, fun σ y hy => ?_⟩
  have hr0 : 0 < x.r σ y := (Real.exp_pos 1).trans_le (x.exp_le_r σ y)
  have h1 := Real.log_le_log ((Real.exp_pos 1).trans_le (x'.exp_le_r σ y)) (hK σ y hy)
  rw [Real.log_mul (by linarith) hr0.ne'] at h1
  have h2 : 1 ≤ Real.log (x.r σ y) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (x.exp_le_r σ y)
  have h3 : Real.log K ≤ Real.log K * Real.log (x.r σ y) := le_mul_of_one_le_right hl h2
  linarith

end GlobalTheory.BdFnCompare
