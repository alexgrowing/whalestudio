import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMulEquivCongruenceTopologyAdelicStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianRapidDecay
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupRealPointsEquivPiIndefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AdelicModels

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (HA HR HFinIn AF Ainf IsCMExt IsHermND)
open Formalism.MainNotions.StandardLattice (finMat infMat IsInfEmb)
open GlobalTheory.Mem.Vol.Scale
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_real_equiv (I : AutInst) (hcm : IsCMExt I.F I.E I.cm.sig)
    (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)) (hθ : ∀ v, IsInfEmb (I.φ v) (θ v)) :
    ∃ e : HA (Ainf I.F) I.cm.sig I.J ≃ₜ* I.Ginf, ∀ h v, uMat (e h v) =
      (I.P v)⁻¹ * ((HA.mat (Ainf I.F) I.cm.sig I.J h : GL (Fin I.n) (Ainf I.F ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Ainf I.F ⊗[I.F] I.E)).map (θ v) * I.P v := by
  obtain ⟨e, he, hc, hc', hs⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv I.F I.E I.cm.sig _ I.φ θ hcm
    (GlobalTheory.GaussDecay.isCMFam_of_over _ hcm I.φ I.φ_over) hθ
  choose p q s hsort using fun v => exists_sorts (I.ε v)
  have hd : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h1 : ∀ v, (I.P v)⁻¹ * I.P v = 1 := fun v => Matrix.nonsing_inv_mul _ (hd v)
  have h2 : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v => Matrix.mul_nonsing_inv _ (hd v)
  have hJ : ∀ v, Formalism.UG.Jpq (p v) (q v) = (Formalism.REAL.Jm (I.ε v)).submatrix (s v) (s v) := fun v => by
    rw [← (hsort v).reindex_Jpq]
    ext a b
    simp
  obtain ⟨f, hf⟩ := GlobalTheory.Mem.InfGroup.exists_equiv he hc hc' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf I.F) I.cm.sig)
    (fun x i => by rw [← he, ← he, hs]) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Ainf I.F) I.J) p q
    (fun v => (I.P v)⁻¹.submatrix (s v) (Equiv.refl _)) (fun v => (I.P v).submatrix (Equiv.refl _) (s v))
    (fun v => by rw [Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_one_equiv])
    (fun v => by rw [Matrix.submatrix_mul_equiv, h2, Matrix.submatrix_one_equiv])
    (fun v => by
      have h3 : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Ainf I.F) I.J).map (θ v) = I.J.map (I.φ v) := by
        ext a b
        exact (hθ v).1 (I.J a b)
      rw [h3, hJ, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
        ← I.P_spec v]
      change (I.P v)⁻¹ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹ = _
      calc _ = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [h2]; simp)
  let g : (∀ v, Formalism.BasicNotions.UpqT (p v) (q v)) ≃ₜ* I.Ginf :=
    { toFun := fun x v => (hsort v).equiv (x v)
      invFun := fun y v => (hsort v).equiv.symm (y v)
      left_inv := fun x => funext fun v => (hsort v).equiv.symm_apply_apply _
      right_inv := fun x => funext fun v => (hsort v).equiv.apply_symm_apply _
      map_mul' := fun x y => funext fun v => map_mul (hsort v).equiv _ _
      continuous_toFun := continuous_pi fun v => (hsort v).equiv.continuous.comp (continuous_apply v)
      continuous_invFun := continuous_pi fun v => (hsort v).equiv.symm.continuous.comp (continuous_apply v) }
  refine ⟨f.trans g, fun h v => ?_⟩
  have h4 := hf h v
  change Matrix.reindex (s v) (s v) (Formalism.BasicNotions.UpqT.mat (f h v)) = (I.P v)⁻¹ * (h.1.1).map (θ v) * I.P v
  generalize Formalism.BasicNotions.UpqT.mat (f h v) = X at h4 ⊢
  generalize (h.1.1).map (θ v) = Y at h4 ⊢
  have h5 : Matrix.reindex (s v) (s v) X * (I.P v)⁻¹ = (I.P v)⁻¹ * Y := by
    ext a b
    have := congrFun (congrFun h4 ((s v).symm a)) b
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.coe_refl, id] at this
    rw [Matrix.mul_apply, Matrix.mul_apply, ← this, ← (s v).sum_comp]
    simp
  rw [← h5, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem bc_mem {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {γ : GL (Fin M) E}
    (hγ : γ ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R) γ ∈ HR R σ J := by
  have h : Formalism.UG.cT (σ : E →+* E) γ.1 * J * γ.1 = J := hγ
  have h2 := congrArg (fun X => Matrix.map X (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) h
  simp only [Matrix.map_mul] at h2
  change Formalism.UG.cT _ (γ.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) * J.map _ * γ.1.map _ = J.map _
  rw [← h2]
  congr 2

theorem exists_adelic_equiv : ∀ I : AutInst, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt I.F I.E I.cm.sig ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND I.cm.sig I.J ∧ ∃ T : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ≃ₜ* I.GA, (∀ h, (show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J from h) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ↔ T h ∈ I.GFset) ∧ (∀ h, I.fmat (T h).2 = (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _)) ∧ ∀ v θ, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ → ∀ h, uMat ((T h).1 v) = (I.P v)⁻¹ * Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θ h * I.P v := by
  intro I
  have hcm : IsCMExt I.F I.E I.cm.sig := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1
  refine ⟨hcm, ⟨fun i j => congrFun (congrFun I.J_herm i) j, I.J_det⟩, ?_⟩
  have hex := GlobalTheory.Mem.VolEmb.existsUnique_infEmb I.F I.E I.cm.sig hcm
  choose θ hθ hθu using fun v => hex (I.φ v)
  obtain ⟨er, her⟩ := exists_real_equiv I hcm θ hθ
  obtain ⟨ef, hef, -⟩ := GlobalTheory.T.exists_continuousMulEquiv_congruenceTopology_adelicUnitary I
  obtain ⟨sp, hsp⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split I.F I.E I.cm.sig I.n I.J
  let g : HA (Ainf I.F) I.cm.sig I.J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af I.F) I.cm.sig I.J ≃ₜ* I.GA :=
    { toFun := fun x => (er x.1, ef.symm x.2)
      invFun := fun y => (er.symm y.1, ef y.2)
      left_inv := fun x => Prod.ext (er.symm_apply_apply _) (ef.apply_symm_apply _)
      right_inv := fun x => Prod.ext (er.apply_symm_apply _) (ef.symm_apply_apply _)
      map_mul' := fun x y => Prod.ext (map_mul er _ _) (map_mul ef.symm _ _)
      continuous_toFun := (er.continuous.comp continuous_fst).prodMk (ef.symm.continuous.comp continuous_snd)
      continuous_invFun := (er.symm.continuous.comp continuous_fst).prodMk (ef.continuous.comp continuous_snd) }
  have hfin : ∀ h, I.fmat ((sp.trans g) h).2 =
      (finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _) := by
    intro h
    have h1 := hef (ef.symm (sp h).2)
    rw [ef.apply_symm_apply, (hsp h).1] at h1
    rw [h1]
    change I.fmat (ef.symm (sp h).2) = _
    ext a b
    exact ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm_apply_apply _).symm
  have hinf : ∀ v h, uMat (((sp.trans g) h).1 v) = (I.P v)⁻¹ * infMat I.cm.sig I.J (θ v) h * I.P v := by
    intro v h
    have h1 := her (sp h).1 v
    rw [(hsp h).2] at h1
    exact h1
  have hrat : ∀ (γ : GL (Fin I.n) I.E) (h : HA (AF I.F) I.cm.sig I.J),
      Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := I.F) (AF I.F)) γ = HA.mat _ _ _ h →
      (∀ v, uMat (((sp.trans g) h).1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat ((sp.trans g) h).2 =
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    intro γ h hh
    refine ⟨fun v => ?_, ?_⟩
    · rw [hinf]
      congr 2
      unfold infMat
      rw [← hh]
      ext a b
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, ← (hθ v).1]
      change θ v (Algebra.TensorProduct.map _ _ ((1 : AF I.F) ⊗ₜ[I.F] γ.1 a b)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    · rw [hfin]
      unfold finMat
      rw [← hh]
      ext a b
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
      change Algebra.TensorProduct.comm I.F _ _
        (Algebra.TensorProduct.map _ _ ((1 : AF I.F) ⊗ₜ[I.F] γ.1 a b)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
  refine ⟨sp.trans g, fun h => ⟨?_, ?_⟩, hfin, fun v θ' hθ' h => ?_⟩
  · rintro ⟨γ, hγ, hh⟩
    exact ⟨γ, hγ, hrat γ h hh⟩
  · rintro ⟨γ, hγ, h1, h2⟩
    let h' : HA (AF I.F) I.cm.sig I.J :=
      (⟨_, bc_mem (AF I.F) I.cm.sig I.J hγ⟩ : HR (AF I.F) I.cm.sig I.J)
    obtain ⟨h3, h4⟩ := hrat γ h' rfl
    have : h = h' := (sp.trans g).injective (Prod.ext
      (funext fun v => Subtype.ext (Units.ext ((h1 v).trans (h3 v).symm)))
      (Subtype.ext (Units.ext (h2.trans h4.symm))))
    rw [this]
    exact ⟨γ, hγ, rfl⟩
  · rw [hθu v θ' hθ']
    exact hinf v h

end GlobalTheory.AdelicModels
