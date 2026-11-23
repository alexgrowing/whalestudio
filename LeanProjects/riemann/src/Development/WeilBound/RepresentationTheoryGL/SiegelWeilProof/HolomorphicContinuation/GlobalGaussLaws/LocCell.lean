import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGaussIndicator

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocCell

variable {D : D7} {n : ℕ}

theorem exists_away (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) :
    ∃ Ψ ∈ awayA θ V n l s τ, Ψ 0 ≠ 0 := by
  classical
  let W : AddSubgroup (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ intAE D}
      add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (intAE D).zero_mem
      neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin V.rank) (Fin n) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  refine ⟨fun x => gAway V l s τ (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j)), ?_, ?_⟩
  · refine Submodule.subset_span ⟨1, g, hg, by simp, ?_⟩
    funext x
    simp [evalPoly]
  · have hg0 : g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = 1 := by
      simp only [g]
      rw [if_pos]
      exact (QuotientAddGroup.eq_zero_iff (N := W) _).2 fun i j => by simp
    show gAway V l s τ (fun τ => compAt θ τ 0) * g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) ≠ 0
    rw [hg0, mul_one]
    simp [gAway, compAt]

def piT {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x : Mx D m n) : Fin m → Fin n → ℂ := fun a i => compAt θ τ x a i

theorem exists_sec (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (m n : ℕ) :
    ∃ S : (Fin m → Fin n → ℂ) → Mx D m n,
      (∀ x u, piT θ τ (x + S u) = piT θ τ x + u) ∧
      (∀ x u τ', τ' ≠ τ → compAt θ τ' (x + S u) = compAt θ τ' x) ∧
      ∀ x u, (x + S u).map (finPart D) = x.map (finPart D) := by
  classical
  have hL := fun z : Matrix (Fin m) (Fin n) ℂ => GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let S : (Fin m → Fin n → ℂ) → Mx D m n := fun u =>
    ∑ a, ∑ i, (lineAt θ τ (Matrix.single a i 1) (u a i).re + lineAt θ τ (Matrix.single a i Complex.I) (u a i).im)
  have e : ∀ (τ' : D.what₂.Tau) (y : Mx D m n),
      compAt θ τ' y = ((θ τ').comp (infPart D)).toAddMonoidHom.mapMatrix y := fun _ _ => rfl
  have ef : ∀ y : Mx D m n, y.map (finPart D) = (finPart D).toAddMonoidHom.mapMatrix y := fun _ => rfl
  have hc : ∀ τ' (u : Fin m → Fin n → ℂ), compAt θ τ' (S u) = if τ' = τ then Matrix.of u else 0 := by
    intro τ' u
    rw [e]
    simp only [S]
    simp_rw [map_sum, map_add]
    simp_rw [← e, (hL _).2.2]
    split_ifs with h
    · ext a' i'
      simp [Matrix.sum_apply, Matrix.single_apply]
      rw [Fintype.sum_eq_single a' (fun c hc => by simp [hc]), Fintype.sum_eq_single i' (fun c hc => by simp [hc])]
      simp only [and_self, if_true]
      exact Complex.re_add_im _
    · simp
  have hf : ∀ u, (S u).map (finPart D) = 0 := by
    intro u
    rw [ef]
    simp only [S]
    simp_rw [map_sum, map_add]
    simp_rw [← ef, (hL _).2.1]
    simp
  refine ⟨S, fun x u => ?_, fun x u τ' h => ?_, fun x u => ?_⟩
  · funext a i
    simp only [piT, Pi.add_apply]
    rw [e, map_add, ← e, ← e, hc, if_pos rfl]
    rfl
  · rw [e, map_add, ← e, ← e, hc, if_neg h, add_zero]
  · rw [ef, map_add, ← ef, ← ef, hf, add_zero]

theorem cov {m n : ℕ} (fr : Matrix (Fin m) (Fin m) ℂ) (hfr : IsUnit fr.det) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ f : (Fin m → Fin n → ℂ) → ℂ,
      ∫ u : Fin m → Fin n → ℂ, f (fr⁻¹ * Matrix.of u) = (c' : ℂ) * ∫ y, f y := by
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hfr
  have h2 : fr⁻¹ * fr = 1 := Matrix.nonsing_inv_mul fr hfr
  let T : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) :=
    { toFun := fun u => Matrix.of.symm (fr⁻¹ * Matrix.of u)
      invFun := fun u => Matrix.of.symm (fr * Matrix.of u)
      map_add' := fun u v => by
        ext a i
        simp [Matrix.mul_apply, Finset.sum_add_distrib, mul_add]
      map_smul' := fun r u => by
        ext a i
        simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, RingHom.id_apply,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Complex.real_smul]
        ring
      left_inv := fun u => by
        show fr * (fr⁻¹ * Matrix.of u) = u
        rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        rfl
      right_inv := fun u => by
        show fr⁻¹ * (fr * Matrix.of u) = u
        rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
        rfl }
  have hT : LinearMap.det (T : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' T).ne_zero
  refine ⟨|(LinearMap.det (T : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ)))⁻¹|, abs_pos.2 (inv_ne_zero hT),
    fun f => ?_⟩
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → Fin n → ℂ))) hT
  let Te : (Fin m → Fin n → ℂ) ≃ᵐ (Fin m → Fin n → ℂ) :=
    (T.toContinuousLinearEquiv.toHomeomorph).toMeasurableEquiv
  have hTe : ∀ u, Te u = fr⁻¹ * Matrix.of u := fun u => rfl
  have hm : Measure.map Te volume = Measure.map (T : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ)) volume := rfl
  calc ∫ u : Fin m → Fin n → ℂ, f (fr⁻¹ * Matrix.of u) = ∫ u, f (Te u) := rfl
    _ = ∫ y, f y ∂(Measure.map Te volume) := (integral_map_equiv Te f).symm
    _ = _ := by
      rw [hm, hmap, integral_smul_measure]
      simp [ENNReal.toReal_ofReal (abs_nonneg _)]

theorem continuous_evX {m n : ℕ} (P : PX m n) : Continuous (evX P) := by
  unfold evX
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)
  split_ifs
  · exact continuous_star.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  · exact (continuous_apply k.2.1).comp (continuous_apply k.1)

theorem int_gauss_ne (hSF : SchFP) {m n : ℕ} {c : ℝ} (hc : 0 < c) : ∫ y : Fin m → Fin n → ℂ, fP c (1 : PX m n) y ≠ 0 := by
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨S, hS⟩ := hSF m n c hc 1
  have hint : Integrable (fP c (1 : PX m n)) := hS ▸ S.integrable
  have e : fP c (1 : PX m n) = fun y => ((Real.exp (-(c * ∑ a, ∑ i, ‖y a i‖ ^ 2)) : ℝ) : ℂ) := by
    funext y
    simp [fP, evX, gs, Complex.ofReal_exp]
  rw [e]
  beta_reduce
  rw [integral_complex_ofReal]
  have hr : Integrable (fun y : Fin m → Fin n → ℂ => Real.exp (-(c * ∑ a, ∑ i, ‖y a i‖ ^ 2))) := by
    refine hint.norm.congr (Filter.Eventually.of_forall fun y => ?_)
    show ‖fP c (1 : PX m n) y‖ = _
    rw [congrFun e y, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact_mod_cast (integral_exp_pos hr).ne'

theorem weyl0 {θ : InfFam D} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (W : G D n) (hW : mat W = blk4 0 1 (-1) 0) (Φ : schwartzA θ V.rank n) :
    (ω W Φ).1 0 = ∫ y, Φ.1 y ∂μ := by
  rw [hω.weyl W hW Φ 0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [GlobalTheory.StdUnn.inner]

theorem trivInv {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} (hx : IsTrivAt θ τ x) : IsTrivAt θ τ x⁻¹ := by
  have e : mat x * mat x⁻¹ = 1 := by
    unfold mat
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h2 : compAt θ τ (mat x * mat x⁻¹) = compAt θ τ (mat x) * compAt θ τ (mat x⁻¹) :=
    Matrix.map_mul (f := (θ τ).comp (infPart D))
  unfold IsTrivAt at *
  rw [e, hx, one_mul] at h2
  rw [← h2]
  exact Matrix.map_one ((θ τ).comp (infPart D)) (map_zero _) (map_one _)

theorem wSplit (hDA : DecompAway) {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n}
    (hι : IsPlaceEmb θ τ ι) (W : G D n) (hW : mat W = blk4 0 1 (-1) 0) :
    ∃ x : G D n, IsTrivAt θ τ x ∧ (∃ y0 : GR n, mR y0 = JJ n) ∧ ∀ (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ),
      mR g = JJ n * nU b → ∃ Nb : GR n, mR Nb = nU b ∧ ι g = W * ι Nb * x⁻¹ := by
  obtain ⟨x, y, hx, hWxy, hcomm⟩ := hDA D n θ τ ι hθ hι W
  have hmm : ∀ a b : G D n, mat (a * b) = mat a * mat b := fun a b => by
    unfold mat
    rw [map_mul, Units.val_mul]
  have hy : mR y = JJ n := by
    have h1 : compAt θ τ (mat W) = compAt θ τ (mat x) * compAt θ τ (mat (ι y)) := by
      rw [hWxy, hmm]
      exact Matrix.map_mul (f := (θ τ).comp (infPart D))
    unfold IsTrivAt at hx
    rw [hx, Matrix.one_mul, (hι.2 y).1, hW] at h1
    have h2 : compAt θ τ (blk4 (0 : Matrix (Fin n) (Fin n) (AE D)) 1 (-1) 0) = reidx (JJ n) := by
      change (blk4 (0 : Matrix (Fin n) (Fin n) (AE D)) 1 (-1) 0).map ((θ τ).comp (infPart D)) = _
      rw [LocCellA.block_matrix_map, LocCellA.map_neg_one', LocCellA.map_one', Matrix.map_zero _ (map_zero _)]
      rfl
    rw [h2] at h1
    ext i j
    have := congrFun (congrFun h1 (finSumFinEquiv i)) (finSumFinEquiv j)
    simpa [reidx] using this.symm
  refine ⟨x, hx, ⟨y, hy⟩, fun g b hgb => ⟨y⁻¹ * g, ?_, ?_⟩⟩
  · have hm : ∀ a c : GR n, mR (a * c) = mR a * mR c := fun _ _ => rfl
    have hyy : mR y⁻¹ * mR y = 1 := by rw [← hm, inv_mul_cancel]; rfl
    rw [hm, hgb, ← hy, ← Matrix.mul_assoc, hyy, Matrix.one_mul]
  · have hyW : ι y = W * x⁻¹ := by
      rw [hWxy, hcomm y]
      group
    have hc2 : ι (y⁻¹ * g) * x⁻¹ = x⁻¹ * ι (y⁻¹ * g) := by
      have := hcomm (y⁻¹ * g)
      calc ι (y⁻¹ * g) * x⁻¹ = x⁻¹ * (x * ι (y⁻¹ * g)) * x⁻¹ := by group
        _ = x⁻¹ * (ι (y⁻¹ * g) * x) * x⁻¹ := by rw [this]
        _ = x⁻¹ * ι (y⁻¹ * g) := by group
    calc ι g = ι y * ι (y⁻¹ * g) := by rw [← map_mul, mul_inv_cancel_left]
      _ = W * x⁻¹ * ι (y⁻¹ * g) := by rw [hyW]
      _ = W * ι (y⁻¹ * g) * x⁻¹ := by rw [mul_assoc, ← hc2, ← mul_assoc]

end PositivityTheory.Rg.Sw.Glob.LocCell

namespace PositivityTheory.Rg.Sw.Glob

open LocCell in

theorem lIcell_of (hAw : AwayAct) (hDA : DecompAway) (hU : UnipTau) (hAI : AwayIn) (hSF : SchFP) (hLN : LNe)
    (hLc : LIcont) (hLl : LIlaw) (hLv : LIvac) : LIcell := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hTM L hL
  have hl0 : ∀ τ', l τ' ≠ 0 := hLN D ψ θ l hC.hψ hC.hθ hC.hl
  have hcpos : 0 < cLoc l τ := by
    unfold cLoc
    have := abs_pos.2 (hl0 τ)
    positivity
  obtain ⟨Ψ0, hΨ0a, hΨ00⟩ := exists_away θ V n l s τ
  have hΨ0 : AwayCls θ τ fr Ψ0 := hAI D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr hl0 Ψ0 hΨ0a
  obtain ⟨W, hW⟩ := wEx D n
  obtain ⟨x, hx, ⟨y0, hy0⟩, hsplit⟩ := wSplit hDA hC.hθ hC.hι W hW
  obtain ⟨A, hA⟩ := hAw D n V ψ χ θ μ ω H l s ν τ ε fr ι hC x⁻¹ (trivInv hx)
  obtain ⟨hB, hAf⟩ := hA Ψ0 hΨ0
  have hphi : ∀ P : PX V.rank n, phiS θ τ fr (cLoc l τ) Ψ0 P =
      ⟨tens θ τ fr (fP (cLoc l τ) P) Ψ0, hΨ0.2 _ (hSF _ _ _ hcpos P)⟩ := by
    intro P
    unfold phiS
    rw [dif_pos (hΨ0.2 _ (hSF _ _ _ hcpos P))]

  let aF : PX V.rank n → Matrix (Fin n) (Fin n) ℂ → (Fin V.rank → Fin n → ℂ) → ℂ := fun P b u =>
    Complex.exp (Complex.I * tLoc l τ * (b * gramX ε (fr⁻¹ * Matrix.of u)).trace) *
      fP (cLoc l τ) P (fr⁻¹ * Matrix.of u)
  have key : ∀ P (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR g = JJ n * nU b →
      ∃ Nb : GR n, (∀ z, aF P b (piT θ τ z) * A Ψ0 z =
        (ω (ι Nb) (ω x⁻¹ (phiS θ τ fr (cLoc l τ) Ψ0 P))).1 z) ∧
        sLd L (cLoc l τ) P g * Ψ0 0 = ∫ z, aF P b (piT θ τ z) * A Ψ0 z ∂μ := by
    intro P g b hb hgb
    obtain ⟨Nb, hNb, hg⟩ := hsplit g b hgb
    have hpt : ∀ z, aF P b (piT θ τ z) * A Ψ0 z = (ω (ι Nb) (ω x⁻¹ (phiS θ τ fr (cLoc l τ) Ψ0 P))).1 z := by
      intro z
      rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC Nb b hb hNb, hphi P, hAf _ (hSF _ _ _ hcpos P)]
      have e : Matrix.of (piT θ τ z) = compAt θ τ z := rfl
      simp only [aF, tens, e]
      ring
    refine ⟨Nb, hpt, ?_⟩
    have e1 : (ω (ι g) (phiS θ τ fr (cLoc l τ) Ψ0 P)).1 0 = sLd L (cLoc l τ) P g * Ψ0 0 := by
      rw [hL g Ψ0 hΨ0a P]
      simp [tens, sLd, compAt]
      exact Or.inl rfl
    rw [← e1, hg, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, weyl0 hC.hω W hW]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hpt z).symm)
  obtain ⟨𝓕, hμ1⟩ := hC.hμ
  haveI : μ.IsAddHaarMeasure := hμ1.1
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  obtain ⟨S, hS1, hS2, hS3⟩ := exists_sec θ hC.hθ τ V.rank n
  have hπc : Continuous (piT θ τ : Mx D V.rank n → Fin V.rank → Fin n → ℂ) := by
    have := GlobalTheory.RealWeil.continuous_compAt hC.hθ τ V.rank n
    exact continuous_pi fun a => continuous_pi fun i => this.matrix_elem a i
  have hBinv : ∀ z u, A Ψ0 (z + S u) = A Ψ0 z := fun z u => hB.1 _ _ (fun τ' h => hS2 z u τ' h) (hS3 z u)
  have hfPc : ∀ P : PX V.rank n, Continuous (fP (cLoc l τ) P) := fun P => by
    obtain ⟨Sf, hSf⟩ := hSF _ _ _ hcpos P
    rw [← hSf]
    exact Sf.continuous
  have hlin : Continuous (fun u : Fin V.rank → Fin n → ℂ => fr⁻¹ * Matrix.of u) :=
    continuous_const.matrix_mul continuous_id
  have hne1 : ∀ y, fP (cLoc l τ) (1 : PX V.rank n) y ≠ 0 := fun y => by
    simp [fP, evX, gs, Complex.exp_ne_zero]
  have hBm : Measurable (A Ψ0) := by
    have hm := hB.2 (fP (cLoc l τ) 1) (hSF _ _ _ hcpos 1)
    have hcont := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hC.hθ _ _ _ hm).1
    have e : A Ψ0 = fun z => tens θ τ fr (fP (cLoc l τ) 1) (A Ψ0) z / fP (cLoc l τ) 1 (fr⁻¹ * compAt θ τ z) := by
      funext z
      simp only [tens]
      exact (mul_div_cancel_left₀ _ (hne1 _)).symm
    rw [e]
    refine (hcont.div ((hfPc 1).comp ?_) fun z => hne1 _).measurable
    exact continuous_const.matrix_mul (GlobalTheory.RealWeil.continuous_compAt hC.hθ τ V.rank n)
  let a0 : (Fin V.rank → Fin n → ℂ) → ℂ := fun u => fP (cLoc l τ) 1 (fr⁻¹ * Matrix.of u)
  have ha0c : Continuous a0 := (hfPc 1).comp hlin
  have haFc : ∀ P b, Continuous (aF P b) := fun P b =>
    ((Complex.continuous_exp.comp (continuous_const.mul (Continuous.matrix_trace (continuous_const.matrix_mul
      (continuous_pi fun i => continuous_pi fun j => (continuous_evX (Qp ε i j)).comp hlin))))).mul
      ((hfPc P).comp hlin))
  have hTF : ∀ (P : PX V.rank n) (b : Matrix (Fin n) (Fin n) ℂ) (Nb : GR n),
      (∀ z, aF P b (piT θ τ z) * A Ψ0 z = (ω (ι Nb) (ω x⁻¹ (phiS θ τ fr (cLoc l τ) Ψ0 P))).1 z) →
      ∃ κ : ℂ, (∫ z, aF P b (piT θ τ z) * A Ψ0 z ∂μ = κ * ∫ u, aF P b u) ∧
        ∫ z, a0 (piT θ τ z) * A Ψ0 z ∂μ = κ * ∫ u, a0 u := by
    intro P b Nb hpt
    have hint1 : Integrable (fun z => aF P b (piT θ τ z) * A Ψ0 z) μ := by
      simp_rw [hpt]
      exact GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hC.hθ hμ1 (ω (ι Nb) (ω x⁻¹ (phiS θ τ fr (cLoc l τ) Ψ0 P))).2
    have hint2 : Integrable (fun z => a0 (piT θ τ z) * A Ψ0 z) μ := by
      have := GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hC.hθ hμ1 (hB.2 (fP (cLoc l τ) 1) (hSF _ _ _ hcpos 1))
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      rfl
    obtain ⟨κ, hκ⟩ := LocCellT.tauFact μ (piT θ τ) hπc S hS1 (A Ψ0) hBm hBinv
      (fun u => ‖aF P b u‖ + ‖a0 u‖) ((haFc P b).norm.add ha0c.norm)
      (fun u => add_pos_of_nonneg_of_pos (norm_nonneg _) (norm_pos_iff.2 (hne1 _)))
      ((hint1.norm.add hint2.norm).congr (Filter.Eventually.of_forall fun z => by
        simp only [Pi.add_apply, norm_mul]; ring))
    refine ⟨κ, hκ _ (haFc P b).measurable ⟨1, fun u => ?_⟩, hκ _ ha0c.measurable ⟨1, fun u => ?_⟩⟩
    · simp only [one_mul]; exact le_add_of_nonneg_right (norm_nonneg _)
    · simp only [one_mul]; exact le_add_of_nonneg_left (norm_nonneg _)
  obtain ⟨c', hc'pos, hcov⟩ := cov (n := n) fr hC.hfr.1
  have hy0' : mR y0 = JJ n * nU 0 := by
    rw [hy0]
    simp [nU]
  obtain ⟨N0, hpt0, -⟩ := key 1 y0 0 (by simp) hy0'
  obtain ⟨κ, -, hκ0⟩ := hTF 1 0 N0 hpt0
  have hint0 : ∫ u, a0 u ≠ 0 := by
    have e : (∫ u, a0 u) = (c' : ℂ) * ∫ y, fP (cLoc l τ) (1 : PX V.rank n) y := hcov (fP (cLoc l τ) 1)
    rw [e]
    exact mul_ne_zero (by exact_mod_cast hc'pos.ne') (int_gauss_ne hSF hcpos)
  have hcell : ∀ (P : PX V.rank n) (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b →
      sLd L (cLoc l τ) P g = κ * c' / Ψ0 0 * secN ε (cLoc l τ) (tLoc l τ) P b := by
    intro P g b hb hgb
    obtain ⟨Nb, hpt, hv⟩ := key P g b hb hgb
    obtain ⟨κ', h1, h2⟩ := hTF P b Nb hpt
    have hk : κ' = κ := mul_right_cancel₀ hint0 (h2.symm.trans hκ0)
    have hcovP : ∫ u, aF P b u = (c' : ℂ) *
        ∫ y, Complex.exp (Complex.I * tLoc l τ * (b * gramX ε y).trace) * fP (cLoc l τ) P y :=
      hcov (fun y => Complex.exp (Complex.I * tLoc l τ * (b * gramX ε y).trace) * fP (cLoc l τ) P y)
    have hsec : (∫ y, Complex.exp (Complex.I * tLoc l τ * (b * gramX ε y).trace) * fP (cLoc l τ) P y) =
        secN ε (cLoc l τ) (tLoc l τ) P b := by
      unfold secN
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [fP]
      ring
    rw [h1, hk, hcovP, hsec] at hv
    field_simp
    rw [hv]
    ring
  refine ⟨κ * c' / Ψ0 0, ?_, hcell⟩
  intro hC0
  obtain ⟨e, he⟩ := hLl D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hTM L hL
  have hsign : (tLoc l τ = cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε true ∧ (pqOf ε l τ).2 = cnt ε false) ∨
      (tLoc l τ = -cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε false ∧ (pqOf ε l τ).2 = cnt ε true) := by
    unfold tLoc cLoc pqOf
    rcases lt_or_gt_of_ne (hl0 τ) with h | h
    · right
      refine ⟨?_, ?_, ?_⟩
      · rw [abs_of_neg h]; ring
      · simp [if_neg (not_lt.2 h.le)]
      · simp [if_neg (not_lt.2 h.le)]
    · left
      refine ⟨?_, ?_, ?_⟩
      · rw [abs_of_pos h]
      · simp [if_pos h]
      · simp [if_pos h]
  have hS1 : sLd L (cLoc l τ) 1 1 = 1 := by
    have h := congrFun (hL 1 Ψ0 hΨ0a 1) 0
    rw [map_one, map_one, hphi 1] at h
    simp only [Module.End.one_apply, tens] at h
    have h0 : fr⁻¹ * compAt θ τ (0 : Mx D V.rank n) = 0 := by simp [compAt]
    rw [h0] at h
    have h' := mul_right_cancel₀ hΨ00 h
    simp only [sLd]
    calc L 1 (fP (cLoc l τ) 1) 0 = L 1 (fP (cLoc l τ) 1) (0 : Matrix (Fin V.rank) (Fin n) ℂ) := rfl
      _ = fP (cLoc l τ) 1 (0 : Matrix (Fin V.rank) (Fin n) ℂ) := h'.symm
      _ = 1 := by simp [fP, evX, gs]
  have hv := hLv V.rank n ε (cLoc l τ) (tLoc l τ) (pqOf ε l τ).1 (pqOf ε l τ).2 e hcpos hsign
    (sLd L (cLoc l τ) 1) (κ * c' / Ψ0 0) (hLc D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hTM L hL 1) hS1
    (fun y g hy => he 1 y g hy) (fun g b hb hgb => hcell 1 g b hb hgb) y0
  rw [hcell 1 y0 0 (by simp [Matrix.IsHermitian]) hy0', hC0, zero_mul] at hv
  have hdet : (mR y0).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 y0.1.isUnit
    exact this.ne_zero
  have hu1 : (u1 (mR y0)).det ≠ 0 := by
    rw [hy0]
    simp only [u1, JJ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, add_zero, smul_neg,
      Matrix.det_neg, Matrix.det_smul, Matrix.det_one]
    simp [Complex.I_ne_zero]
  have hu2 : (u2 (mR y0)).det ≠ 0 := by
    rw [hy0]
    simp only [u2, JJ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, add_zero, smul_neg, neg_neg,
      Matrix.det_smul, Matrix.det_one]
    simp [Complex.I_ne_zero]
  have : F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e y0 ≠ 0 := by
    unfold F0 f0
    exact mul_ne_zero (zpow_ne_zero _ hdet) (mul_ne_zero (zpow_ne_zero _ hu1) (zpow_ne_zero _ hu2))
  exact this hv.symm

end PositivityTheory.Rg.Sw.Glob
