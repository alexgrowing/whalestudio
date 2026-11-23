import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFielStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig
open Formalism.L2

theorem not_bad_of_genAt {D : D7} {M : Formalism.L2.MtFam D} (T : Formalism.L2.NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl)
    (i : D.nd.Loc) (h : i ∈ D.nd.locs j w) (v : PlE D.host) (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k) (hc : IsConjPl D.host v s.w) :
    s.v ∉ Formalism.L2.badPl D i := by
  intro hmem
  obtain ⟨w', hover, hw'⟩ := hmem
  obtain ⟨-, e2⟩ := (D.nd.locs_mem j w i).1 h
  have hl : D.nd.l i = D.what₂.places.resChar w := by rw [← D.nd.w_l i, e2]
  have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → v ∈ placesOver D.host.E p := by
    intro p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).2 h3
  rcases hw' with hQ | ⟨kk, hg⟩ | hpd
  · rw [T.Q_eq j w i h] at hQ
    have hsw : s.w ∈ T.B.Qc j w := T.B.Qc_over j w w' s.w hQ ⟨s.v, hover, s.w_under⟩
    exact hvk.2.2.2.1 (T.B.Qc_conj j w v s.w hsw hc)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    have hv := hp _ hg
    fin_cases kk
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    rw [hl] at hpd
    exact Or.inr (Or.inr (hp _ hpd))

theorem main : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → Formalism.L2.HeckeRational D M → Formalism.L2.AVTied D M → Formalism.L2.NormalizedLocalCompatibility D M → ∀ i : D.nd.Loc, (∀ (P : D.naut.AV i) (w : PlE D.host), SplitOut D.nd i w → ∃ lam : ℕ → ℂ, galPol D.naut (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) = X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV, C ((-1) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (D.R.nV - k) ∧ ∀ (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host w s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i P, Formalism.L2.NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = lam k • (M.loc i).real y) → GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  intro D M HT HR AV NL i hyp P x hcong
  classical
  have tN0 : ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ),
      Formalism.L2.NG.tN (M.loc i).J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → (M.loc i).wt.W) = 0 := by
    intro s ϖ k; ext g; simp [Formalism.L2.NG.tN, Formalism.L2.NG.heckeD]
  by_cases hP0 : D.naut.typeV i P = ⊥
  · refine ⟨x, (AV.ptV i P x).2 ?_⟩
    intro v k s ϖ _ _ _ _ _ y hy
    rw [hP0, Submodule.mem_bot] at hy
    subst hy
    rw [map_zero, smul_zero, tN0]
  obtain ⟨y0, hy0, hy0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have h : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  let lamF : PlE D.host → ℕ → ℂ := fun v =>
    if hv : SplitOut D.nd i v then Classical.choose (hyp P v hv) else 0
  have hlamF : ∀ v (hv : SplitOut D.nd i v), lamF v = Classical.choose (hyp P v hv) := fun v hv => dif_pos hv
  have hinjO : Function.Injective (iotaO D.nd D.naut i) := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i).injective.comp ((D.naut.iotaQ i).injective.comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))))
  have hcoef : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → ∃ a : D.nd.O i,
      iotaO D.nd D.naut i a = lamF v k ∧
      IsLocalRing.residue (D.nd.O i) a = IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    intro v k hv hk1 hk2
    obtain ⟨p, hp1, hp2⟩ := hcong v hv
    have e1 := (Classical.choose_spec (hyp P v hv)).1
    rw [← hlamF v hv] at e1
    exact coeff_extract (iotaO D.nd D.naut i) hinjO D.R.nV (normV v) (normV_unit D i v hv.2.1) p (lamF v)
      (fun k => (D.nd.hT i v k : D.nd.X i → D.nd.O i) x) (hp1.trans e1) hp2 k hk1 hk2
  let aF : PlE D.host → ℕ → D.nd.O i := fun v k =>
    if hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV then Classical.choose (hcoef v k hv.1 hv.2.1 hv.2.2) else 0
  have haF : ∀ v k (hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV), iotaO D.nd D.naut i (aF v k) = lamF v k ∧
      IsLocalRing.residue (D.nd.O i) (aF v k) =
        IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    intro v k hv
    simp only [aF, dif_pos hv]
    exact Classical.choose_spec (hcoef v k hv.1 hv.2.1 hv.2.2)
  have hiotaC : ∀ z, iotaO D.nd D.naut i z = NL.iotaC _ _ (NL.phO _ _ i h z) := NL.iotaC_coh _ _ i h
  have hinjC : Function.Injective (NL.iotaC (D.nd.j i) (D.nd.w i)) := by
    intro a b hab
    have e2 : (NL.phO _ _ i h).symm a = (NL.phO _ _ i h).symm b := hinjO (by
      rw [hiotaC, hiotaC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; exact hab)
    simpa using congrArg (NL.phO _ _ i h) e2
  let φ : FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = NL.iotaC _ _ z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (NL.phK _ _ i h).toRingHom = (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, NL.phK_alg, hφalg]
    rw [← hiotaC]
    rfl
  have hφ : ∀ y, φ (NL.B.ec _ _ y) = D.what₂.embLL y := by
    intro y
    rw [← NL.phK_emb _ _ i h y, ← D.naut.iota_LL i y]
    exact congrArg (fun f : FractionRing (D.nd.O i) →+* ℂ => f (D.nd.embK i y)) hφK
  let κ : PlE D.host → ℕ → FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) := fun v k =>
    algebraMap _ _ (NL.phO _ _ i h (aF v k))
  have hκ : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → φ (κ v k) = lamF v k := by
    intro v k hv hk1 hk2
    simp only [κ, hφalg]
    rw [← hiotaC]
    exact (haF v k ⟨hv, hk1, hk2⟩).1
  obtain ⟨e, hene, he⟩ := GlobalTheory.T.complexHeckeEigenvector_descends_to_coefficientField D M NL.B (D.nd.j i) (D.nd.w i) (D.nd.mu i) (D.nd.j_range i).1
    (D.nd.j_range i).2 (D.nd.mu_w i) φ hφ κ y0 hy0ne (by
      intro v k hvk
      obtain ⟨hv, hk1, hk2⟩ := (Formalism.L2.genAt_iff NL h v k).2 hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.T.splitEx_every_datum D v hv.1
      have hbad : s.v ∉ Formalism.L2.badPl D i := not_bad_of_genAt NL _ _ i h v k s hvk hc
      have hfin := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (M.loc i).J (M.loc i).χ (Formalism.L2.badPl D i) (HT.J_hyp i)
        s ϖ k hbad hu
      refine ⟨s, ϖ, hc, hu, ?_, ?_⟩
      · intro c f f'
        show Formalism.L2.NG.tN (M.loc i).J s ϖ k (c • f + f') =
          c • Formalism.L2.NG.tN (M.loc i).J s ϖ k f + Formalism.L2.NG.tN (M.loc i).J s ϖ k f'
        simp only [Formalism.L2.NG.tN]
        rw [heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]
      · rw [hκ v k hv hk1 hk2]
        have e3 := (Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y0 hy0
        rw [← hlamF v hv] at e3
        exact e3)
  have hinjK : Function.Injective (algebraMap (NL.B.Oc (D.nd.j i) (D.nd.w i))
      (FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)))) := IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := pt_of_eigvec (Formalism.L2.heckeGens NL.B (D.nd.j i) (D.nd.w i)) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨NL.phO _ _ i h (aF v k), he v k hvk⟩)
  have hψv : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k),
      ψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = NL.phO _ _ i h (aF v k) := by
    intro v k hvk
    apply hinjK
    have h1 := hψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have h2 := he v k hvk
    change NL.B.hK _ _ v k e = _ at h1
    rw [h2] at h1
    exact (smul_left_injective _ hene h1).symm
  have hcls : Formalism.L2.NCov.cls ψ = NL.mx _ _ i := by
    refine (cls_eq_of_residue _ ψ (NL.ptX _ _ i h x).1 ?_).trans (NL.ptX _ _ i h x).2.1
    rintro _ ⟨v, k, hvk, rfl⟩
    rw [hψv v k hvk, ← NL.ptX_hT _ _ i h x v k hvk]
    obtain ⟨hv, hk1, hk2⟩ := (Formalism.L2.genAt_iff NL h v k).2 hvk
    exact residue_map_equiv (NL.phO _ _ i h) (haF v k ⟨hv, hk1, hk2⟩).2
  have hW : Formalism.L2.NCov.W (Formalism.L2.heckeAlg NL.B _ _) (Formalism.L2.NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3
  refine ⟨(NL.ptX _ _ i h).symm ⟨ψ, hcls, hW⟩, (AV.ptV i P _).2 ?_⟩
  intro v k s ϖ hv hc hu hk1 hk2 y hy
  have hvk := (Formalism.L2.genAt_iff NL h v k).1 ⟨hv, hk1, hk2⟩
  have e1 := (Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y hy
  rw [← hlamF v hv] at e1
  rw [e1]
  congr 1
  show lamF v k = iotaO D.nd D.naut i _
  rw [hiotaC, NL.ptX_hT _ _ i h _ v k hvk, Equiv.apply_symm_apply]
  show lamF v k = NL.iotaC _ _ (ψ ⟨NL.B.hK _ _ v k, _⟩)
  rw [hψv v k hvk, ← hiotaC]
  exact (haF v k ⟨hv, hk1, hk2⟩).1.symm

end GlobalTheory.PtLocalEig
