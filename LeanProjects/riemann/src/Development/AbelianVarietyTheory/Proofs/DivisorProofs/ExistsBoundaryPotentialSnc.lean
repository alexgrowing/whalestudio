import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRatioOfLocalGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorPotentialIsSNCBoundaryStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.DivSec

open scoped ContDiff

theorem generic_not_mem {F : Type} [Field F] {Y : Var F} {m : ℕ} {C : Fin m → Closeds Y.X}
    (hsnc : ∀ y : Y.X, LSncAt Y.X C y) (i : Fin m) : genericPoint Y.X ∉ C i := by
  intro hmem
  obtain ⟨-, nn, r, emb, hR, -⟩ := hsnc (genericPoint Y.X)
  have h0 : ringKrullDim (Y.X.presheaf.stalk (genericPoint Y.X)) = 0 :=
    ringKrullDim_eq_zero_of_field (Y.X.functionField)
  have hn0 : nn = 0 := by
    have := hR.2
    rw [h0] at this
    exact_mod_cast this
  subst hn0
  exact (emb ⟨i, hmem⟩).elim0

theorem isPotential_divPot : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) (m : ℕ) (C : Fin m → Closeds Y.X) (n : Fin m → Pts Y σ → ℝ) (hn : ∀ i, IsDivNorm (Y.an σ) (C i) (n i)) (B : FinHolAtlas Y.dim (Pts Y σ)), IsAlgAtlas B → (∀ y : Y.X, LSncAt Y.X C y) → IsPotential B (GlobalTheory.DivSec.divPot hn) := by
  intro F _ _ Y σ m C n hn B hB hsnc
  have hgen := generic_not_mem hsnc
  refine ⟨fun x => (hB.smoothOn_iff (Y.an σ) ((GlobalTheory.DivSec.divPot hn).isOpen_U x)).2 ?_, fun x x' y hy => ?_⟩
  · have h : ∀ i, (Y.an σ).SmoothOn ((GlobalTheory.DivSec.divPot hn).U x) (fun z => GlobalTheory.DivSec.eqF hn i x z / 2) := fun i j =>
      (((GlobalTheory.DivSec.eq_spec hn i x).2.2.1.mono fun z hz => GlobalTheory.DivSec.mem_eqV hn hz i) j).div_const 2
    intro j
    have key : ∀ s : Finset (Fin m), ContDiffOn ℝ ∞ ((fun z => ∑ i ∈ s, GlobalTheory.DivSec.eqF hn i x z / 2) ∘ ((Y.an σ).chart j).e.symm)
        (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' (GlobalTheory.DivSec.divPot hn).U x) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact (contDiffOn_const (c := (0 : ℝ))).congr fun v _ => by simp
      | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (h a j).add ih
    refine (key Finset.univ).congr fun v _ => ?_
    simp [GlobalTheory.DivSec.divPot]
  · have hQ : ∀ i, ∃ W : Set (Pts Y σ), IsOpen W ∧ y ∈ W ∧ ∃ G : Pts Y σ → ℂ, (Y.an σ).HoloOn W G ∧
        ∀ z ∈ W ∩ ptsIn Y.str σ (GlobalTheory.DivSec.eqV hn i x).1 ∩ ptsIn Y.str σ (GlobalTheory.DivSec.eqV hn i x').1,
          GlobalTheory.DivSec.eqF hn i x z - GlobalTheory.DivSec.eqF hn i x' z = (G z).re := fun i =>
      GlobalTheory.T.smooth_ratio_of_local_generators F Y σ (C i) (n i) _ _ _ _ _ _ ⟨_, hgen i⟩ (GlobalTheory.DivSec.eq_spec hn i x).2.1 (GlobalTheory.DivSec.eq_spec hn i x').2.1
        (GlobalTheory.DivSec.eq_spec hn i x).2.2.1 (GlobalTheory.DivSec.eq_spec hn i x').2.2.1 (GlobalTheory.DivSec.eq_spec hn i x).2.2.2
        (GlobalTheory.DivSec.eq_spec hn i x').2.2.2 y ⟨GlobalTheory.DivSec.mem_eqV hn hy.1 i, GlobalTheory.DivSec.mem_eqV hn hy.2 i⟩
    choose W hW hyW G hG he using hQ
    refine ⟨⋂ i, W i, isOpen_iInter_of_finite hW, Set.mem_iInter.2 hyW, fun z => ∑ i, G i z / 2,
      (hB.holoOn_iff (Y.an σ) (isOpen_iInter_of_finite hW)).2 ?_, fun z hz => ?_⟩
    · intro j
      have h : ∀ i, DifferentiableOn ℂ (fun v => G i (((Y.an σ).chart j).e.symm v) / 2)
          (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ⋂ i, W i) := fun i => by
        have h1 : DifferentiableOn ℂ (G i ∘ ((Y.an σ).chart j).e.symm)
            (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ⋂ i, W i) :=
          (hG i j).mono fun v hv => ⟨hv.1, Set.mem_iInter.1 hv.2 i⟩
        exact (h1.mul_const (2⁻¹ : ℂ)).congr fun v _ => by simp [div_eq_mul_inv]
      have key : ∀ s : Finset (Fin m), DifferentiableOn ℂ (fun v => ∑ i ∈ s, G i (((Y.an σ).chart j).e.symm v) / 2)
          (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ⋂ i, W i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using differentiableOn_const (c := (0 : ℂ))
        | insert a s ha ih =>
          simp only [Finset.sum_insert ha]
          exact (h a).add ih
      exact (key Finset.univ).congr fun v _ => by simp
    · have hzi : ∀ i, GlobalTheory.DivSec.eqF hn i x z - GlobalTheory.DivSec.eqF hn i x' z = (G i z).re := fun i =>
        he i z ⟨⟨Set.mem_iInter.1 hz.1.1 i, GlobalTheory.DivSec.mem_eqV hn hz.1.2 i⟩, GlobalTheory.DivSec.mem_eqV hn hz.2 i⟩
      simp only [GlobalTheory.DivSec.divPot, Complex.re_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_div, hzi i, Complex.div_ofNat_re]

theorem bdSec_of_divNorm : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (m : ℕ) (C : Fin m → Closeds Y.X) (n : Fin m → Pts Y (I.ε a) → ℝ), Y.dim = e → (∀ y : Y.X, LSncAt Y.X C y) → (∀ i, IsDivNorm (Y.an (I.ε a)) (C i) (n i)) → (∀ z, z ∈ M.Z a ↔ ∃ i, under (I.pt a z) ∈ C i) → (∀ z, z ∉ M.Z a → M.r a z = Real.exp 1 - Real.log ((∏ i, n i (I.pt a z)) ^ 2)) → ∃ (L : LocPot (M.X a)) (t : M.X a → M.X a → ℂ), IsBdSec (M.A a) (M.Z a) (M.r a) L t ∧ IsSNC (M.A a) L t (fun _ : Fin m => 1) fun i => {z | under (I.pt a z) ∈ C i} := by
  intro F _ _ Y e M I a m C n hdim hsnc hn hZ hr
  subst hdim
  have hA : GlobalTheory.DivSec.ChartsAlg (M.A a) (I.pt a) := I.alg a
  have hlog : ∀ z, logNormSec ((GlobalTheory.DivSec.divPot hn).pullback (I.pt a) (I.pt a).continuous)
      (fun x w => GlobalTheory.DivSec.divSec hn (I.pt a x) (I.pt a w)) z = Real.log (∏ i, n i (I.pt a z)) := fun z => by
    simp only [logNormSec, LocPot.pullback]
    rw [GlobalTheory.DivSec.norm_divSec_mul hn ((GlobalTheory.DivSec.divPot hn).mem_U _)]
  refine ⟨(GlobalTheory.DivSec.divPot hn).pullback (I.pt a) (I.pt a).continuous,
    fun x w => GlobalTheory.DivSec.divSec hn (I.pt a x) (I.pt a w),
    ⟨GlobalTheory.DivSec.isPotential_pullback hA (isPotential_divPot F Y _ m C n hn _ (GlobalTheory.DivSec.isAlgAtlas_algAtlas hA) hsnc),
     GlobalTheory.DivSec.isSection_pullback hA (GlobalTheory.DivSec.isSection_divSec hn (GlobalTheory.DivSec.isAlgAtlas_algAtlas hA)),
     fun z => ?_, ?_, ?_, fun z hz => ?_⟩,
    GlobalTheory.DivSec.isSNC_pullback hA (GlobalTheory.T.divisor_potential_isSNC_boundary F Y _ m C n hn _ (GlobalTheory.DivSec.isAlgAtlas_algAtlas hA) hsnc)⟩
  · rw [hlog]
    exact Real.log_nonpos (Finset.prod_nonneg fun i _ => ((hn i).1 _).1)
      (Finset.prod_le_one (fun i _ => ((hn i).1 _).1) fun i _ => ((hn i).1 _).2)
  · ext z
    rw [hZ z]
    exact (GlobalTheory.DivSec.divSec_eq_zero_iff hn (I.pt a z)).symm
  · intro hu
    obtain ⟨z, hz⟩ := IsBd.compl_nonempty (M.A a) (M.Z a) (M.r a) (M.Om a) (M.bd a)
    exact hz (hu ▸ Set.mem_univ z)
  · rw [hr z hz, P.rW, hlog, Real.log_pow]
    push_cast
    ring

end GlobalTheory.DivSec
