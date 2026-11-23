import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.CompSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeNegTransposeGramStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixUnitaryGroupPreservesGramStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjRationalPrincipalCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeRealSpecialUnitaryEqFlagDomainMassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThreeStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMassUpperBound
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuAllData
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HolomorphicSectionSignatureOneOne

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MainStatements.Tam.C

theorem sum_muF_le (hT : TubeSt) (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) [Fintype Comp]
    (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ)
    (hK : IsLevelK V M Kf) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hm : ∀ k, ModelW V hr (X k)) (hM : 3 ≤ M)
    (hΨ : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (X k).Ψ ↔ ∃ ρ, τ = tauE D ρ)
    (P Q : ℕ) (hs : V.SigOK) (hsig : ∀ τ, V.sig τ = (P, Q)) (h2 : 2 ≤ r)
    (x0 : ∀ k, Frame (X k).Ψ r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd (X k))))
    (hF : ∀ k, IsOrth (X k) (x0 k) ∧ IsFundSet (X k) (x0 k) (FF k)) :
    ∑ k, muF (X k) (x0 k) (FF k) ≤ ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * r ^ 2) * (M : ℝ) ^ (2 * D.R.f * r ^ 2) *
      (ReciprocityTheory.ChartRestriction.DS.volU r ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D r)) := by
  subst hr
  classical
  obtain ⟨x1, hx1, hact⟩ := hD.2.2.1
  choose gA hgA using fun c => (hx1 c).2
  have hG : ∀ k, (X k).Gm = -(V.gram)ᵀ := fun k => by
    have := (hm k).1
    simpa [Matrix.reindex_apply] using this
  have hL := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  choose Λk hΛk using fun k => GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (finHom V (gA k))
    hL.2.2.1 hL.2.2.2.1
  have hX' := fun k => GlobalTheory.T.exists_flagDomainData_principalCongruenceLevel D.host.E V.rank M (X k) (Λk k) hM (hΛk k).2.1 (hΛk k).2.2.1
  choose X' hX'Gm hX'Ψ hX'p0 hX'Λ hX'Γ using hX'
  have hfm : ∀ k, ∃ y, IsOrth (X' k) y ∧ ∃ FF', IsFundSet (X' k) y FF' ∧ muF (X' k) y FF' < ⊤ :=
    fun k => GlobalTheory.finMu_all_data D.host.E V.rank (X' k)
  choose y hy FF' hFF' _ using hfm
  have hμ : ∀ k, muF (X k) (x0 k) (FF k) = muF (X' k) (y k) (FF' k) := by
    intro k
    refine GlobalTheory.T.covolume_eq_of_realUnitary_conj D.host.E V.rank (X k) (X' k) (hX'Ψ k)
      (fun τ => if h : τ ∈ (X k).Ψ then archM V (th k ⟨τ, h⟩) (gA k) else 1) (x0 k) (y k) (FF k) (FF' k)
      (hX'Gm k) (hX'p0 k) ?_ ?_ ?_ (hF k).1 (hy k) (hF k).2 (hFF' k)
    · intro τ hτ
      simp only [dif_pos hτ]
      rw [hG k]
      exact GlobalTheory.T.archimedeanMatrix_unitaryGroup_preserves_gram D V τ _ (hth k ⟨τ, hτ⟩) (gA k)
    · intro γ hγ
      obtain ⟨γ', h1, h2⟩ := GlobalTheory.T.arithmeticGroup_conj_rational_principalCongruence D V Comp X dict Kf th M x1 hK hth hD (fun c => (hx1 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 γ hγ
      refine ⟨γ', (hX'Γ k γ').2 (by rw [hG k]; exact h1), fun τ hτ => ?_⟩
      simp only [dif_pos hτ]
      exact h2 τ hτ
    · intro γ' hγ'
      have h1 := (hX'Γ k γ').1 hγ'
      rw [hG k] at h1
      obtain ⟨γ, hγ, h2⟩ := GlobalTheory.T.principalCongruence_conj_mem_arithmeticGroup D V Comp X dict Kf th M x1 hK hth hD (fun c => (hx1 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 (hΛk k).2.2.2 γ' h1
      refine ⟨γ, hγ, fun τ hτ => ?_⟩
      simp only [dif_pos hτ]
      exact h2 τ hτ
  have hdist := GlobalTheory.T.componentRepresentatives_injective_doubleCoset D V Comp X dict Kf th M gA hK hth hD (fun k => by rw [hgA k])
  have hΓ' : ∀ k γ, γ ∈ (X' k).Γ ↔ IsUStab (X' k).Gm (X' k).Λ γ ∧ ∀ x ∈ (X' k).Λ, ∃ z ∈ (X' k).Λ,
      (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ x - x = M • z := by
    intro k γ
    rw [hX'Γ k γ, hX'Gm k, hX'Λ k]
  have hdet : ∀ k, ∀ γ ∈ (X' k).Γ, (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 := fun k =>
    GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three D.host.E V.rank M (X' k) hM (hΓ' k)
  have hCc := fun k => GlobalTheory.T.covolume_realSpecialUnitary_eq_flagDomain_mass D.host.E V.rank (X' k) (y k) (FF' k) (by omega) (hdet k) (hy k) (hFF' k)
  have hTube := hT D V P Q hs hsig h2 M hM Comp X' gA y hdist (fun k => ⟨(hX'Gm k).trans (hG k),
    fun τ => by rw [hX'Ψ k]; exact hΨ k τ, by rw [hX'Λ k]; exact (hΛk k).1, hΓ' k, hy k⟩)
  have hC1 : (1 : ℝ) ≤ ((2 : ℝ) ^ (V.rank * (V.rank - 1) / 2) * (2 * Real.pi) ^ (V.rank - 1) *
      Real.sqrt V.rank) ^ fdeg D.host.E := by
    apply one_le_pow₀
    have h1 : (1 : ℝ) ≤ 2 ^ (V.rank * (V.rank - 1) / 2) := one_le_pow₀ (by norm_num)
    have h2' : (1 : ℝ) ≤ (2 * Real.pi) ^ (V.rank - 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
    have h3 : (1 : ℝ) ≤ Real.sqrt V.rank := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ V.rank))
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2') h3
  rw [Finset.sum_congr rfl (fun k _ => hμ k)]
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) hTube
  rw [← hCc k]
  exact le_mul_of_one_le_left' (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hC1)

end MainStatements.Tam.C

open MainStatements.Tam

theorem MainStatements.Tam.comp : TubeSt → NumSt → CompSt := by
  intro hT hN D j H Dw l Xo c U dict hL σ hσ x0 FF hF
  obtain ⟨Kf, th, hr, hK, hth, hD, -⟩ := hL.dictU σ hσ
  obtain ⟨hr', hm⟩ := hL.modelW σ hσ
  have hunf := hL.unf σ hσ
  have hΨ : ∀ k (τ : D.host.E →+* ℂ), τ ∈ ((U σ).X k).Ψ ↔ ∃ ρ, τ = tauE D ρ := by
    intro k τ
    have hf := GlobalTheory.HolDictModel.fix_iff (D := D) τ
    rw [← hL.host.2.2.1, ← hL.host.2.1] at hf
    rw [(hunf.2.1 k).2 τ]
    simpa using hf
  have h2r : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have key := MainStatements.Tam.C.sum_muF_le hT D (D.sp.W j) D.R.r hr (U σ).Comp (U σ).X (dict σ) Kf th l.M hK hth hD hm
    l.three_le hΨ (D.R.sigW j).1 (D.R.sigW j).2 (D.sp.W_sig j) (fun τ => D.sp.W_sigval j hL.inR.1 hL.inR.2 τ) h2r
    x0 FF hF
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  obtain ⟨hv0, hv1⟩ := hN D.R.r h2r
  have hvnn : 0 ≤ ReciprocityTheory.ChartRestriction.DS.volU D.R.r := le_trans (by positivity) hv0
  have hA : ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f ≤ (13 : ℝ) ^ (D.R.f * D.R.r ^ 2) := by
    rw [mul_comm, pow_mul]
    exact pow_le_pow_left₀ hvnn hv1 _
  have hAnn : 0 ≤ ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f := pow_nonneg hvnn _
  have hB : Formalism.MainNotions.StandardLattice.massI D D.R.r ≤ massB D.host.E D.R.r := GlobalTheory.mass_stdLat_le D.host.E (fun _ => rfl) D.R.r
  have hBnn : 0 ≤ massB D.host.E D.R.r := by unfold massB; positivity
  have hAB : ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D D.R.r ≤
      (13 : ℝ) ^ (D.R.f * D.R.r ^ 2) * massB D.host.E D.R.r := by
    rcases le_total 0 (Formalism.MainNotions.StandardLattice.massI D D.R.r) with h | h
    · exact mul_le_mul hA hB h (by positivity)
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hAnn h) (by positivity)
  unfold massLev2
  rw [hfin]
  have h15 : (15 : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) = 225 ^ (D.R.f * D.R.r ^ 2) := by
    rw [mul_assoc, pow_mul]; norm_num
  rw [h15]
  have h208 : (16 : ℝ) ^ (D.R.f * D.R.r ^ 2) * 13 ^ (D.R.f * D.R.r ^ 2) ≤ 225 ^ (D.R.f * D.R.r ^ 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  calc (16 : ℝ) ^ (D.R.f * D.R.r ^ 2) * (l.M : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) *
        (ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D D.R.r)
      ≤ (16 : ℝ) ^ (D.R.f * D.R.r ^ 2) * (l.M : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) *
        ((13 : ℝ) ^ (D.R.f * D.R.r ^ 2) * massB D.host.E D.R.r) := by gcongr
    _ = (l.M : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) * ((16 : ℝ) ^ (D.R.f * D.R.r ^ 2) * 13 ^ (D.R.f * D.R.r ^ 2)) *
        massB D.host.E D.R.r := by ring
    _ ≤ (l.M : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) * 225 ^ (D.R.f * D.R.r ^ 2) * massB D.host.E D.R.r := by gcongr

end
