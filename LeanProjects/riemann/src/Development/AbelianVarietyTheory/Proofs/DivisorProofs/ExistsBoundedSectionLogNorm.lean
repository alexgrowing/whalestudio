import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRatioOfLocalGeneratorsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DivSecAtlas

open scoped ContDiff

theorem isPotential_divPot_of_generic {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {m : ℕ}
    {C : Fin m → Closeds Y.X} {n : Fin m → Pts Y σ → ℝ} (hn : ∀ i, IsDivNorm (Y.an σ) (C i) (n i))
    (hgen : ∀ i, genericPoint Y.X ∉ C i) (B : FinHolAtlas Y.dim (Pts Y σ)) (hB : IsAlgAtlas B) :
    IsPotential B (GlobalTheory.DivSec.divPot hn) := by
  refine ⟨fun x => (hB.smoothOn_iff (Y.an σ) ((GlobalTheory.DivSec.divPot hn).isOpen_U x)).2 ?_, fun x x' y hy => ?_⟩
  · have h : ∀ i, (Y.an σ).SmoothOn ((GlobalTheory.DivSec.divPot hn).U x) (fun z => GlobalTheory.DivSec.eqF hn i x z / 2) := fun i j =>
      (((GlobalTheory.DivSec.eq_spec hn i x).2.2.1.mono fun z hz => GlobalTheory.DivSec.mem_eqV hn hz i) j).div_const 2
    intro j
    have key : ∀ s : Finset (Fin m), ContDiffOn ℝ ∞
        ((fun z => ∑ i ∈ s, GlobalTheory.DivSec.eqF hn i x z / 2) ∘ ((Y.an σ).chart j).e.symm)
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
      GlobalTheory.T.smooth_ratio_of_local_generators F Y σ (C i) (n i) _ _ _ _ _ _ ⟨_, hgen i⟩ (GlobalTheory.DivSec.eq_spec hn i x).2.1
        (GlobalTheory.DivSec.eq_spec hn i x').2.1 (GlobalTheory.DivSec.eq_spec hn i x).2.2.1 (GlobalTheory.DivSec.eq_spec hn i x').2.2.1
        (GlobalTheory.DivSec.eq_spec hn i x).2.2.2 (GlobalTheory.DivSec.eq_spec hn i x').2.2.2 y
        ⟨GlobalTheory.DivSec.mem_eqV hn hy.1 i, GlobalTheory.DivSec.mem_eqV hn hy.2 i⟩
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
      have key : ∀ s : Finset (Fin m), DifferentiableOn ℂ
          (fun v => ∑ i ∈ s, G i (((Y.an σ).chart j).e.symm v) / 2)
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

theorem exists_pt_not_mem {F : Type} [Field F] {Y : Var F} (σ : F →+* ℂ) {m : ℕ} {C : Fin m → Closeds Y.X}
    (hgen : ∀ i, genericPoint Y.X ∉ C i) : ∃ z : Pts Y σ, ∀ i, under z ∉ C i := by
  obtain ⟨hne, hd⟩ := GlobalTheory.CxPtsDense.nonempty_and_dense F Y σ
  haveI := hne
  let W : Y.X.Opens := ⟨(⋃ i, (C i : Set Y.X))ᶜ, (isClosed_iUnion_of_finite fun i => (C i).isClosed).isOpen_compl⟩
  have hWne : (W : Set Y.X).Nonempty :=
    ⟨genericPoint Y.X, fun h => by obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h; exact hgen i hi⟩
  obtain ⟨z, hz⟩ := (hd W hWne).nonempty
  refine ⟨z, fun i hi => ?_⟩
  have hzW : under z ∈ (W : Set Y.X) := GlobalTheory.CxPts.mem_ptsIn.1 hz
  exact hzW (Set.mem_iUnion.2 ⟨i, hi⟩)

theorem isBdSec_atlasOf : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) (m : ℕ) (C : Fin m → Closeds Y.X) (n : Fin m → Pts Y σ → ℝ), (∀ i, IsDivNorm (Y.an σ) (C i) (n i)) → (∀ i, genericPoint Y.X ∉ C i) → ∃ (L : LocPot (Pts Y σ)) (t : Pts Y σ → Pts Y σ → ℂ), IsBdSec (atlasOf Y σ) {z | ∃ i, under z ∈ C i} (fun z => Real.exp 1 - Real.log ((∏ i, n i z) ^ 2)) L t := by
  intro F _ _ Y σ m C n hn hgen
  have hlog : ∀ z, logNormSec (GlobalTheory.DivSec.divPot hn) (GlobalTheory.DivSec.divSec hn) z = Real.log (∏ i, n i z) := fun z => by
    simp only [logNormSec]
    rw [GlobalTheory.DivSec.norm_divSec_mul hn ((GlobalTheory.DivSec.divPot hn).mem_U _)]
  refine ⟨GlobalTheory.DivSec.divPot hn, GlobalTheory.DivSec.divSec hn,
    isPotential_divPot_of_generic hn hgen _ (isAlgAtlas_atlasOf σ),
    GlobalTheory.DivSec.isSection_divSec hn (isAlgAtlas_atlasOf σ), fun z => ?_, ?_, ?_, fun z hz => ?_⟩
  · rw [hlog]
    exact Real.log_nonpos (Finset.prod_nonneg fun i _ => ((hn i).1 _).1)
      (Finset.prod_le_one (fun i _ => ((hn i).1 _).1) fun i _ => ((hn i).1 _).2)
  · ext z
    exact (GlobalTheory.DivSec.divSec_eq_zero_iff hn z).symm
  · intro hu
    obtain ⟨z, hz⟩ := exists_pt_not_mem σ hgen
    have hzZ : z ∈ {z : Pts Y σ | ∃ i, under z ∈ C i} := hu ▸ Set.mem_univ z
    obtain ⟨i, hi⟩ := hzZ
    exact hz i hi
  · show Real.exp 1 - Real.log ((∏ i, n i z) ^ 2) = P.rW (GlobalTheory.DivSec.divPot hn) (GlobalTheory.DivSec.divSec hn) z
    rw [P.rW, hlog, Real.log_pow]
    push_cast
    ring

end GlobalTheory.DivSecAtlas
