import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Sector
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableRationalSubgroupInRealSpecialUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFrameCongruenceSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetDetImPosAtIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureFinitePartPreimageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMassProductLowerBoundUnitaryPqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteFrameRealSpecialUnitaryStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.MassBridge

theorem core (D : D7) (V : HSp D) (r : ℕ) (hrk : V.rank = r) (hV : V.SigOK) (P Q : ℕ)
    (hsig : ∀ τ, V.sig τ = (P, Q)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)))
    (hKo : IsOpen {h : GA D V | finE V h ∈ K}) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (hF : IsMeasFD V K μ 𝓕) (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ))
    (x : Frame Ψ r) (p0 : Ψ → ℕ) (J : Type)
    (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → GA D V)
    (hr : 2 ≤ r)
    (hx : ∀ τ : Ψ, gram τ.1 (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm))) (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ))
    (hΨ : ∃ eΨ : D.what₂.Tau ≃ Ψ, ∀ ρ, ((eΨ ρ : Ψ) : D.host.E →+* ℂ) = tauE D ρ)
    (hh : ∀ j, h j ∈ GfC V)
    (h4 : ∀ (j j' : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E), g ∈ GQ V →
      matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
      finE V ((h j')⁻¹ * g * h j) ∈ K → IsIntegral ℤ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det ∧
        ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 → j = j'))
    (h5 : ∀ (j : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E) (γr : GL (Fin r) D.host.E), g ∈ GQ V →
      matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
      (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm) =
        (γr : Matrix (Fin r) (Fin r) D.host.E) → (γr : Matrix (Fin r) (Fin r) D.host.E).det = 1 →
      finE V ((h j)⁻¹ * g * h j) ∈ K →
      γr ∈ ratStab (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm)))
        (Λ : Set (Fin r → D.host.E)) (s j)) :
    ENNReal.ofReal ((1 / 32 : ℝ) ^ (D.R.f * r ^ 2)) * ∑' j, covolume
      (inReal Ψ (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm)))
        (ratStab (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm)))
          (Λ : Set (Fin r → D.host.E)) (s j)))
      (realSU Ψ (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm))))
      (riemHaar Ψ (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm))) x) ≤ μ 𝓕 := by
  subst hrk
  classical
  change ENNReal.ofReal ((1 / 32 : ℝ) ^ (D.R.f * V.rank ^ 2)) * ∑' j, covolume
      (inReal Ψ (V.gram)ᵀ (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
      (realSU Ψ (V.gram)ᵀ) (riemHaar Ψ (V.gram)ᵀ x) ≤ μ 𝓕
  have hx' : ∀ τ : Ψ, gram τ.1 (V.gram)ᵀ (mat x τ) = Matrix.diagonal fun a : Fin V.rank => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) := hx
  obtain ⟨hLC, hSC, hB, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := hF.1.1
  obtain ⟨⟨θ, hθ⟩, H1⟩ := hF.1.2
  obtain ⟨⟨A, hA⟩, H2⟩ := H1 θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := H2 A hA
  obtain ⟨X₀, σ, x₀, e, hG, hσ, hx₀, hid⟩ := GlobalTheory.T.exists_flagDomain_orthonormalFrame_identification D V P Q hV hsig A hA
  obtain ⟨rp, hrpc, hrp⟩ := GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic D V θ A hV hθ hA
  let a₀ : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 :=
    fun ρ => (e ρ).symm ⟨0, by omega⟩
  obtain ⟨π, hπc, hπ, hπe⟩ := GlobalTheory.T.exists_continuous_equivariant_detOneFactorProjection D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x₀ σ A e a₀ hid
  have hcard : X₀.Ψ.card = D.R.f := by
    rw [← Fintype.card_coe, ← Fintype.card_congr σ, D.what₂.card_Tau]
  have hf : 1 ≤ D.R.f := UpperTheory.Mu.one_le_f D.R
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; omega
  obtain ⟨eΨ, heΨ⟩ := hΨ
  have hΨX : X₀.Ψ = Ψ := by
    ext τ; constructor
    · intro hτ
      obtain ⟨ρ, hρ⟩ := σ.surjective ⟨τ, hτ⟩
      have e1 : τ = tauE D ρ := by rw [← hσ ρ, hρ]
      rw [e1, ← heΨ ρ]; exact (eΨ ρ).2
    · intro hτ
      obtain ⟨ρ, hρ⟩ := eΨ.surjective ⟨τ, hτ⟩
      have e1 : τ = tauE D ρ := by rw [← heΨ ρ, hρ]
      rw [e1, ← hσ ρ]; exact (σ ρ).2
  have hherm : ∀ a b, cc ((V.gram)ᵀ a b) = (V.gram)ᵀ b a := by
    intro a b
    have e1 := X₀.Gm_herm a b
    rw [hG] at e1
    simp only [cc, Matrix.neg_apply, Matrix.transpose_apply, map_neg, neg_inj] at e1 ⊢
    exact e1
  have htr : ∀ j, covolume (inReal Ψ (V.gram)ᵀ (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
      (realSU Ψ (V.gram)ᵀ) (riemHaar Ψ (V.gram)ᵀ x) =
      covolume (inReal X₀.Ψ X₀.Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
      (realSU X₀.Ψ X₀.Gm) (riemHaar X₀.Ψ X₀.Gm x₀) := fun j =>
    GlobalTheory.T.gram_frame_congruence_subgroup D.host.E V.rank Ψ X₀.Ψ (V.gram)ᵀ X₀.Gm x x₀ p0 X₀.p0 _ hΨX hG hherm hx' hx₀
  choose F hFm hFcov hFfree using fun j => GlobalTheory.T.exists_packingSet_measure_ge_covolume (realSU X₀.Ψ X₀.Gm) (riemHaar X₀.Ψ X₀.Gm x₀)
    (inReal X₀.Ψ X₀.Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j))) (GlobalTheory.T.countable_rationalSubgroupInRealSpecialUnitary _ _ _ _ _)
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  let B : J → Set (∀ ρ, Upq V ρ) := fun j => π ⁻¹' F j ∩ {b | 0 < (UpqT.mat (b ρ₀)).det.im}
  have hBm : ∀ j, MeasurableSet (B j) := fun j =>
    (hπc.measurable (hFm j)).inter (GlobalTheory.T.measurableSet_det_im_pos_at_index D.what₂.Tau _ _ ρ₀)
  let T : J → Set (GA D V) := fun j => {y | finE V ((h j)⁻¹ * y) ∈ K ∧ rp y ∈ B j}
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    ((hKo.preimage (continuous_const.mul continuous_id)).measurableSet).inter (hrpc.measurable (hBm j))
  have hμT : ∀ j, μ (T j) = Measure.pi m (B j) := fun j =>
    GlobalTheory.T.level_measure_finite_part_preimage D V θ A m rp K μ hV hθ hA hm hrpc hrp hKo hF.1 (h j) (hh j) (B j) (hBm j)
  have hlow : ∀ j, ENNReal.ofReal ((1 / 16 : ℝ) ^ (X₀.Ψ.card * V.rank ^ 2)) * riemHaar X₀.Ψ X₀.Gm x₀ (F j) ≤ μ (T j) := by
    intro j
    rw [hμT j]
    exact GlobalTheory.T.archimedean_mass_product_lower_bound_unitary_pq D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x₀ σ A e a₀ π m ρ₀ (by omega) hid hπc hπ hπe hm (F j) (hFm j)
  have hdisj := GlobalTheory.T.indefinite_frame_real_special_unitary D V θ A rp X₀.Ψ X₀.Gm x₀ σ e π K Λ J s h F ρ₀ hG hθ hrp hid hσ hπe hFfree h4
    (fun j g γ hg hmg hd hK => h5 j g γ γ hg hmg rfl hd hK)
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.mul_iSup]
  refine iSup_le fun J0 => ?_
  let sc : GA D V → ℕ := fun y => UpperTheory.Ram.Sector.sec (NumberField.Units.torsionOrder D.host.E) (UpqT.mat (rp y ρ₀)).det
  have hscm : Measurable sc := by
    have hc : Continuous fun g : Upq V ρ₀ => (UpqT.mat g).det := (continuous_id.matrix_det).comp GlobalTheory.UpqTopology.continuous_mat
    exact (UpperTheory.Ram.Sector.measurable_sec _).comp
      (hc.measurable.comp ((measurable_pi_apply ρ₀).comp hrpc.measurable))
  have hlay : ∀ k, ∑ j ∈ J0, μ (T j ∩ {y | sc y = k}) ≤ μ 𝓕 := by
    intro k
    let Tk : J → Set (GA D V) := fun j => T j ∩ {y | sc y = k}
    have hTkm : ∀ j, MeasurableSet (Tk j) := fun j => (hTm j).inter (hscm (measurableSet_singleton k))
    let S := ⋃ j ∈ J0, Tk j
    have hSm : MeasurableSet S := Finset.measurableSet_biUnion J0 fun j _ => hTkm j
    have hTd : Set.PairwiseDisjoint (↑J0) Tk := by
      intro j _ j' _ hne
      refine Set.disjoint_left.2 fun y hy hy' => hne ?_
      exact (hdisj 1 (GQ V).one_mem j j' y hy.1 (by rw [one_mul]; exact hy'.1) (by rw [one_mul])).2
    have hμS : μ S = ∑ j ∈ J0, μ (Tk j) := measure_biUnion_finset hTd fun j _ => hTkm j
    have hSF : μ S ≤ μ 𝓕 := by
      refine hF.2.measure_le_of_pairwise_disjoint hSm.nullMeasurableSet ?_
      intro g g' hne
      refine Disjoint.aedisjoint (Set.disjoint_left.2 fun z hz hz' => hne ?_)
      obtain ⟨y, hy, hyz⟩ := Set.mem_smul_set.1 hz.1
      obtain ⟨y', hy', hyz'⟩ := Set.mem_smul_set.1 hz'.1
      obtain ⟨j, -, hyj⟩ := Set.mem_iUnion₂.1 hy
      obtain ⟨j', -, hyj'⟩ := Set.mem_iUnion₂.1 hy'
      have h1 : (g : GA D V) * y = z := hyz
      have h2 : (g' : GA D V) * y' = z := hyz'
      have e1 : ((g'⁻¹ * g : GQ V) : GA D V) * y = y' := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, h1, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
      have e2 := (hdisj _ (g'⁻¹ * g).2 j j' y hyj.1 (by rw [e1]; exact hyj'.1)
        (by rw [e1]; exact (hyj.2 : sc y = k).trans (hyj'.2 : sc y' = k).symm)).1
      have e3 : g'⁻¹ * g = 1 := Subtype.ext e2
      exact (inv_mul_eq_one.1 e3).symm
    exact hμS ▸ hSF
  have hw : NumberField.Units.torsionOrder D.host.E ≤ 2 ^ (D.R.f * V.rank ^ 2) :=
    (UpperTheory.Mu.host_torsionOrder_le D.host).trans (UpperTheory.Ram.Sector.eight_sq_le hf (by omega))
  refine UpperTheory.Ram.Sector.le_of_mul_le hw ?_
  rw [Finset.mul_sum]
  calc ∑ j ∈ J0, ENNReal.ofReal ((1 / 16 : ℝ) ^ (D.R.f * V.rank ^ 2)) *
        covolume (inReal Ψ (V.gram)ᵀ (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
          (realSU Ψ (V.gram)ᵀ) (riemHaar Ψ (V.gram)ᵀ x) ≤ ∑ j ∈ J0, μ (T j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [htr j, ← hcard]
        calc _ ≤ ENNReal.ofReal ((1 / 16 : ℝ) ^ (X₀.Ψ.card * V.rank ^ 2)) * riemHaar X₀.Ψ X₀.Gm x₀ (F j) := by
              gcongr; exact hFcov j
          _ ≤ μ (T j) := hlow j
    _ ≤ _ := UpperTheory.Ram.Sector.sum_le_of_layers μ T sc _
        (fun y => UpperTheory.Ram.Sector.sec_lt (NumberField.Units.torsionOrder_pos D.host.E) _) J0 _ hlay

end GlobalTheory.CovTop.MassBridge

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

namespace GlobalTheory.CovTop.MassBridge

theorem bridge_bound : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ 𝓕 → letI : IsCMField D.host.E := D.host.isCMField_hostE; ∀ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ D.R.r) (p0 : Ψ → ℕ) (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → Theta.GA D (Wc D i)), (2 ≤ D.R.r ∧ GlobalTheory.UCls.Unr D.host.E ∧ GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) ∧ (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) ∧ GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin D.R.r → D.host.E)) 1 s ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f) → (G = Matrix.transpose ((HSpace.gram (Wc D i)).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm)) ∧ (∃ eΨ : D.what₂.Tau ≃ Ψ, ∀ ρ, ((eΨ ρ : Ψ) : D.host.E →+* ℂ) = TH.tauE D ρ) ∧ (∀ j, h j ∈ Theta.GfC (Wc D i)) ∧ (∀ (j j' : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → Formalism.IndefR.Lev.finE (Wc D i) ((h j')⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → IsIntegral ℤ (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det ∧ ((γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det = 1 → j = j')) ∧ (∀ (j : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) → (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 → Formalism.IndefR.Lev.finE (Wc D i) ((h j)⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → γr ∈ GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) → (letI : MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G) := borel _; haveI : BorelSpace (GlobalTheory.SUVol.realSU Ψ G) := ⟨rfl⟩; ENNReal.ofReal (c ^ (D.R.f * D.R.r ^ 2)) * ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) ≤ μ 𝓕) := by
  refine ⟨1 / 32, by norm_num, by norm_num, ?_⟩
  intro D Tu Cl t0 hCl i μ 𝓕 hF G Λ Ψ x p0 J s h hdata hlink
  obtain ⟨hr, -, -, -, hx, -, -⟩ := hdata
  obtain ⟨hG, hΨ, hh, h4, h5⟩ := hlink
  subst hG
  exact core D (Wc D i) D.R.r (rank_Wc i) (D.sp.W_sig _) _ _ (D.sp.W_sigval _ (Nat.le_add_left _ _) i.2) _
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev _ _ _) μ 𝓕 hF Λ Ψ x p0 J s h hr hx hΨ hh h4 h5

end GlobalTheory.CovTop.MassBridge
