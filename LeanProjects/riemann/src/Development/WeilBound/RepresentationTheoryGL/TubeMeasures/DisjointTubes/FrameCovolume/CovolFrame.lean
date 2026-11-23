import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.FrameCovolume.TubeDisj
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.FrameCovolume.MeasTransl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableRationalSubgroupInRealSpecialUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetDetImPosAtIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMassProductLowerBoundUnitaryPqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrameStatement
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MainStatements.Tam.T2

theorem exists_frames (D : D7) (V : HSp D) (hV : V.SigOK) : ∃ A : Frames V, IsFrames V A := by
  classical
  have h : ∀ ρ : D.what₂.Tau, ∃ a : Matrix (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2) (Fin V.rank) ℂ,
      aᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * a = gramAt D V ρ := by
    intro ρ
    obtain ⟨e, Q, hQ⟩ := hV (tauE D ρ)
    have hQ' : (Q : Matrix _ _ ℂ)ᴴ * ((HSpace.gram V).map (tauE D ρ)).reindex e e * (Q : Matrix _ _ ℂ) =
        Formalism.UG.Jpq _ _ := hQ
    have h1 : ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)ᴴ * Formalism.UG.Jpq _ _ * ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) =
        ((HSpace.gram V).map (tauE D ρ)).reindex e e := by
      rw [← hQ']
      calc _ = ((Q : Matrix _ _ ℂ) * ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ))ᴴ *
            ((HSpace.gram V).map (tauE D ρ)).reindex e e * ((Q : Matrix _ _ ℂ) * ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [Units.mul_inv]; simp
    let Pm : Matrix (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2)
        (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2) ℂ := ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)
    let a : Matrix (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2) (Fin V.rank) ℂ := Pm.submatrix id e
    have h1' : Pmᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * Pm =
        ((HSpace.gram V).map (tauE D ρ)).reindex e e := h1
    refine ⟨a, ?_⟩
    have h2 : aᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * a =
        (Pmᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * Pm).submatrix e e := by
      ext i j
      simp [a, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [h2, h1']
    ext a b
    simp [gramAt]
  choose A hA using h
  exact ⟨A, hA⟩

theorem covol_frame {E : Type} [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ Ψ' : Finset (E →+* ℂ))
    (G G' : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (x' : Frame Ψ' r) (p0 p1 : ℕ) (Γ : Subgroup (GL (Fin r) E))
    (hΨ : Ψ = Ψ') (hG : G = G') (hh : ∀ a b, cc (G a b) = G b a)
    (hx : ∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ))
    (hx' : ∀ τ : Ψ', gram τ.1 G' (mat x' τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) :
    covolume (inReal Ψ G Γ) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ' G' Γ) (realSU Ψ' G') (riemHaar Ψ' G' x') := by
  subst hΨ
  subst hG
  rw [GlobalTheory.T.riemannianHaar_independent_of_orthonormal_frame E r p0 p1 Ψ G x x' hh hx hx']

end MainStatements.Tam.T2

namespace MainStatements.Tam

open MainStatements.Tam.T2

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tube : VolSt → StabSt → IdxSt → TubeSt := by
  intro hvol hstab hidx D V P Q hV hsig hr M hM ι _ X g x0 hdist hX
  classical
  obtain ⟨hLC, hSC, hBor, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  let μ : Measure (GA D V) := Measure.haar
  haveI hμH : μ.IsHaarMeasure := by infer_instance
  obtain ⟨𝓕, hFD⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμH
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨A, hA⟩ := exists_frames D V hV
  choose mm hmm using GlobalTheory.MinfMeasure.exists_isMinf
  let m : ∀ ρ, Measure (Upq V ρ) := fun ρ => mm _ _
  have hm : ∀ ρ, IsMinf (m ρ) := fun ρ => hmm _ _
  obtain ⟨X₀, σ, x₀, e, hG, hσ, hx₀, hid⟩ := GlobalTheory.T.exists_flagDomain_orthonormalFrame_identification D V P Q hV hsig A hA
  obtain ⟨rp, hrpc, hrp⟩ := GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic D V θ A hV hθ hA
  let a₀ : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 :=
    fun ρ => (e ρ).symm ⟨0, by omega⟩
  obtain ⟨π, hπc, hπ, hπe⟩ := GlobalTheory.T.exists_continuous_equivariant_detOneFactorProjection D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x₀ σ A e a₀ hid
  have hcard : X₀.Ψ.card = D.R.f := by
    rw [← Fintype.card_coe, ← Fintype.card_congr σ, D.what₂.card_Tau]
  have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; omega
  have hΨk : ∀ k, (X k).Ψ = X₀.Ψ := by
    intro k
    ext τ
    rw [(hX k).2.1 τ]
    constructor
    · rintro ⟨ρ, rfl⟩
      rw [← hσ ρ]
      exact (σ ρ).2
    · intro hτ
      obtain ⟨ρ, hρ⟩ := σ.surjective ⟨τ, hτ⟩
      exact ⟨ρ, by rw [← hσ ρ, hρ]⟩
  have htr : ∀ k, covolume (inReal (X k).Ψ (X k).Gm (X k).Γ) (realSU (X k).Ψ (X k).Gm) (riemHaar (X k).Ψ (X k).Gm (x0 k)) =
      covolume (inReal X₀.Ψ X₀.Gm (X k).Γ) (realSU X₀.Ψ X₀.Gm) (riemHaar X₀.Ψ X₀.Gm x₀) := fun k =>
    covol_frame V.rank _ _ _ _ (x0 k) x₀ (X k).p0 X₀.p0 (X k).Γ (hΨk k) ((hX k).1.trans hG.symm) (X k).Gm_herm
      (hX k).2.2.2.2 hx₀
  choose F hFm hFcov hFfree using fun k => GlobalTheory.T.exists_packingSet_measure_ge_covolume (realSU X₀.Ψ X₀.Gm) (riemHaar X₀.Ψ X₀.Gm x₀)
    (inReal X₀.Ψ X₀.Gm (X k).Γ) (GlobalTheory.T.countable_rationalSubgroupInRealSpecialUnitary _ _ _ _ _)
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  let B : ι → Set (∀ ρ, Upq V ρ) := fun k => π ⁻¹' F k ∩ {b | 0 < (UpqT.mat (b ρ₀)).det.im}
  have hBm : ∀ k, MeasurableSet (B k) := fun k =>
    (hπc.measurable (hFm k)).inter (GlobalTheory.T.measurableSet_det_im_pos_at_index D.what₂.Tau _ _ ρ₀)
  choose g' hg'C hg'f using fun k => GlobalTheory.SplitDec.exists_finPart V (g k)
  let T : ι → Set (GA D V) := fun k => {y | (g' k)⁻¹ * y ∈ KM V M ∧ rp y ∈ B k}
  have hKMo : IsOpen (KM V M) := (hstab.1 D V).2 M (by omega)
  have hTm : ∀ k, MeasurableSet (T k) := fun k =>
    ((hKMo.preimage (continuous_const.mul continuous_id)).measurableSet).inter (hrpc.measurable (hBm k))
  have hdisj := tube_disj D V θ A rp X₀.Ψ X₀.Gm σ π M ι X g' F hM hG hθ hrp hσ hπe hFfree
    (fun k k' h => hdist k k' (by rw [hg'f k, hg'f k']; exact h)) (fun k => (hX k).1)
    (fun k => by rw [← hg'f k]; exact (hX k).2.2.1) (fun k => (hX k).2.2.2.1)

  have hTd : Pairwise (Function.onFun Disjoint T) := by
    intro k k' hne
    refine Set.disjoint_left.2 fun y hy hy' => hne ?_
    exact (hdisj 1 (GQ V).one_mem k k' y ⟨hy.1, hy.2.1⟩ (by rw [one_mul]; exact ⟨hy'.1, hy'.2.1⟩)).2
  let S := ⋃ k, T k
  have hSm : MeasurableSet S := MeasurableSet.iUnion hTm
  have hμS : μ S = ∑ k, μ (T k) := by
    rw [measure_iUnion hTd hTm, tsum_fintype]
  have hSF : μ S ≤ μ 𝓕 := by
    refine hFD.measure_le_of_pairwise_disjoint hSm.nullMeasurableSet ?_
    intro γ γ' hne
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun z hz hz' => hne ?_)
    obtain ⟨y, hy, hyz⟩ := Set.mem_smul_set.1 hz.1
    obtain ⟨y', hy', hyz'⟩ := Set.mem_smul_set.1 hz'.1
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.1 hy
    obtain ⟨j', hyj'⟩ := Set.mem_iUnion.1 hy'
    have h1 : (γ : GA D V) * y = z := hyz
    have h2 : (γ' : GA D V) * y' = z := hyz'
    have e1 : ((γ'⁻¹ * γ : GQ V) : GA D V) * y = y' := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, h1, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 := (hdisj _ (γ'⁻¹ * γ).2 j j' y ⟨hyj.1, hyj.2.1⟩ (by rw [e1]; exact ⟨hyj'.1, hyj'.2.1⟩)).1
    have e3 : γ'⁻¹ * γ = 1 := Subtype.ext e2
    exact (inv_mul_eq_one.1 e3).symm

  have hKM1 : Stab V = KM V 1 := (hstab.1 D V).1
  have hlowk : ∀ k, μ {h | h ∈ Stab V ∧ rp h ∈ B k} ≤ ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ (T k) := by
    intro k
    have e1 : μ (T k) = μ {z | z ∈ KM V M ∧ rp z ∈ B k} :=
      meas_transl D V θ A rp hV hA hrp μ (g' k) (hg'C k) (KM V M) (B k)
    rw [e1, hKM1]
    exact meas_low D V θ A rp hV hA hrp μ hidx M (by omega) (B k)
  have hvk : ∀ k, μ 𝓕 * Measure.pi m (B k) = μ {h | h ∈ Stab V ∧ rp h ∈ B k} *
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) := fun k =>
    hvol D V P Q hV hsig μ 𝓕 hFD θ A m rp hθ hA hm hrpc hrp (B k) (hBm k)
  have h16 : ∀ k, ENNReal.ofReal ((1 / 16 : ℝ) ^ (D.R.f * V.rank ^ 2)) * riemHaar X₀.Ψ X₀.Gm x₀ (F k) ≤
      Measure.pi m (B k) := by
    intro k
    rw [← hcard]
    exact GlobalTheory.T.archimedean_mass_product_lower_bound_unitary_pq D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x₀ σ A e a₀ π m ρ₀ (by omega) hid hπc hπ hπe hm
      (F k) (hFm k)

  have hvolU : 0 < ReciprocityTheory.ChartRestriction.DS.volU V.rank := by
    unfold ReciprocityTheory.ChartRestriction.DS.volU
    exact Finset.prod_pos fun i _ => by positivity
  have hCpos : 0 < ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank :=
    mul_pos (pow_pos hvolU _) (Formalism.MainNotions.StandardLattice.massI_pos D V.rank)
  have hFtop : μ 𝓕 ≠ ⊤ := (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμH hFD).ne
  have hF0 : μ 𝓕 ≠ 0 := by
    intro h0
    have e0 := hvol D V P Q hV hsig μ 𝓕 hFD θ A m rp hθ hA hm hrpc hrp Set.univ MeasurableSet.univ
    rw [h0, zero_mul] at e0
    have hset : {h | h ∈ Stab V ∧ rp h ∈ (Set.univ : Set (∀ ρ, Upq V ρ))} = KM V 1 := by
      ext h
      simp [hKM1]
    have h1mem : (1 : GA D V) ∈ KM V 1 := by
      show IsKM _ _ _ _ _
      rw [map_one, Units.val_one]
      exact isKM_one _ _ _ _
    have hpos : 0 < μ (KM V 1) := ((hstab.1 D V).2 1 le_rfl).measure_pos μ ⟨1, h1mem⟩
    rw [hset] at e0
    exact (mul_ne_zero hpos.ne' (ENNReal.ofReal_pos.2 hCpos).ne') e0.symm

  have hsum : ∑ k, Measure.pi m (B k) ≤
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) * ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) := by
    have h1 : μ 𝓕 * ∑ k, Measure.pi m (B k) ≤ μ 𝓕 *
        (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) * ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2))) := by
      rw [Finset.mul_sum]
      calc ∑ k, μ 𝓕 * Measure.pi m (B k)
          = ∑ k, μ {h | h ∈ Stab V ∧ rp h ∈ B k} *
              ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) :=
            Finset.sum_congr rfl fun k _ => hvk k
        _ ≤ ∑ k, ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ (T k) *
              ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) :=
            Finset.sum_le_sum fun k _ => by gcongr; exact hlowk k
        _ = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) *
              ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * ∑ k, μ (T k) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ ≤ ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) *
              ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ 𝓕 := by
            gcongr
            rw [← hμS]
            exact hSF
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_right hF0 hFtop).1 h1
  have hcov : ∀ k, covolume (inReal (X k).Ψ (X k).Gm (X k).Γ) (realSU (X k).Ψ (X k).Gm) (riemHaar (X k).Ψ (X k).Gm (x0 k)) ≤
      ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * V.rank ^ 2)) * Measure.pi m (B k) := by
    intro k
    rw [htr k]
    calc _ ≤ riemHaar X₀.Ψ X₀.Gm x₀ (F k) := hFcov k
      _ = ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * V.rank ^ 2)) *
            (ENNReal.ofReal ((1 / 16 : ℝ) ^ (D.R.f * V.rank ^ 2)) * riemHaar X₀.Ψ X₀.Gm x₀ (F k)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (16 : ℝ) ^ (D.R.f * V.rank ^ 2)), ← mul_pow]
          norm_num
      _ ≤ _ := by gcongr; exact h16 k
  calc _ ≤ ∑ k, ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * V.rank ^ 2)) * Measure.pi m (B k) :=
        Finset.sum_le_sum fun k _ => hcov k
    _ = ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * V.rank ^ 2)) * ∑ k, Measure.pi m (B k) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * V.rank ^ 2)) *
          (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) *
            ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2))) := by gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (16 : ℝ) ^ (D.R.f * V.rank ^ 2) * (M : ℝ) ^ (2 * D.R.f * V.rank ^ 2)),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (16 : ℝ) ^ (D.R.f * V.rank ^ 2)),
          ENNReal.ofReal_pow (Nat.cast_nonneg M), ENNReal.ofReal_natCast]
        ring

end MainStatements.Tam
