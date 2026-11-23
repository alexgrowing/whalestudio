import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IotaReal

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem thetaV_eq_gen (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (θ' : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ' : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ') (y : AF I.F ⊗[I.F] I.E) :
    Formalism.L2.SG.AdBridge.thetaV I v y = θ' (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E) y) := by
  have hb : ∀ b : Ainf I.F,
      InfinitePlace.Completion.extensionEmbedding v (b v) = θ' (b ⊗ₜ[I.F] (1 : I.E)) := by
    intro b
    have hc : Continuous fun b : Ainf I.F => InfinitePlace.Completion.extensionEmbedding v (b v) :=
      (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)
    refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap I.F).equalizer hc hθ'.2 (funext fun x => ?_)) b
    show InfinitePlace.Completion.extensionEmbedding v (algebraMap I.F (Ainf I.F) x v) =
      θ' ((algebraMap I.F (Ainf I.F) x) ⊗ₜ[I.F] (1 : I.E))
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul x, hθ'.1, I.φ_over]
    exact Formalism.L2.SG.AdBridge.evV_algebraMap I v x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.thetaV_tmul, Algebra.TensorProduct.map_tmul]
    have e : (fstA I.F a) ⊗ₜ[I.F] ((AlgHom.id I.F I.E) x) =
        ((fstA I.F a) ⊗ₜ[I.F] (1 : I.E)) * ((1 : Ainf I.F) ⊗ₜ[I.F] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
    rw [e, map_mul, hθ'.1, ← hb]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem map_thetaV_gen (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (θ' : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ' : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ') (k : Formalism.L2.SG.AdBridge.HAd I) :
    (Formalism.L2.SG.AdBridge.hmat I k).map (Formalism.L2.SG.AdBridge.thetaV I v) = Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θ' k := by
  ext i j
  exact thetaV_eq_gen I v θ' hθ' _

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem tauF_eq_comm (I : Formalism.MainNotions.S.AutInst) (y : AF I.F ⊗[I.F] I.E) :
    Formalism.L2.SG.AdBridge.tauF I y = Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E
      (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.tauF_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem ofHAFin_eq_one (I : Formalism.MainNotions.S.AutInst) (k : Formalism.L2.SG.AdBridge.HAd I)
    (h : (Formalism.L2.SG.AdBridge.hmat I k).map (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E)) = 1) :
    Formalism.L2.SG.AdBridge.ofHAFin I k = 1 := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at e
  simp only [Formalism.L2.SG.AdBridge.ofHAFin, Matrix.map_apply, tauF_eq_comm, e, Matrix.one_apply]
  split_ifs <;> simp

theorem infMat_of_mem_GfC {D : D7} (k : GA D (D.sp.Y 0)) (hk : k ∈ GfC (D.sp.Y 0))
    (θ' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (D.sp.Y 0).gram θ' k = 1 := by
  have e : (infHom (D.sp.Y 0) k).val = 1 := by
    rw [show infHom (D.sp.Y 0) k = 1 from hk]; rfl
  ext i j
  have e2 := congrFun (congrFun e i) j
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [Matrix.map_apply, Matrix.map_apply]
  refine (congrArg θ' e2).trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_GfC_of_infMat {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (k : GA D (D.sp.Y 0))
    (hk : ∀ τ, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (D.sp.Y 0).gram (θ τ) k = 1) : k ∈ GfC (D.sp.Y 0) := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter fun σ => ∃ ρ, tauE D ρ = σ
  have hmem : ∀ σ, σ ∈ Ψ ↔ ∃ ρ, tauE D ρ = σ := fun σ => by simp [Ψ]
  choose r hr using fun σ : Ψ => (hmem σ.1).1 σ.2
  obtain ⟨h1, -⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D (D.sp.Y 0)).2 Ψ (fun σ => θ (r σ))
    (fun σ => by rw [hmem, hmem]; exact GlobalTheory.PointAtPlace.tauE_cm σ) (fun σ => by rw [← hr σ]; exact hθ _)
  exact h1 k fun σ => hk (r σ)

theorem conj_eq_iff {n : ℕ} (P M N : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    P⁻¹ * M * P = N ↔ M = P * N * P⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  constructor
  · rintro rfl
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  · rintro rfl
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

theorem isAtTau_atTau {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ)
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ)) : IsAtTau θ (D.sp.Y 0) τ g (atTau θ (D.sp.Y 0) τ g) := by
  have hu := GlobalTheory.PointAtPlace.existsUnique_isAtTau (D.sp.Y 0) τ θ hθ g hg
  unfold atTau
  rw [dif_pos hu.exists]
  exact hu.exists.choose_spec

theorem iota_real_finite_of_eq {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (hι : ∀ x : I.E, HEq (ιE x) x) :
    let ι := (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)
    (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (ι k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (ι (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ pl.symm τ → (ι (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (I.ε (pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (ι (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ) = y := by
  intro ι
  subst h
  have hι' : ∀ x, ιE x = x := fun x => eq_of_heq (hι x)
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := by
    ext v
    have e1 : embS D (pl v) = embS D ((Formalism.L2.Host.tauPl D).symm v) := by
      ext x
      exact (congrArg (embS D (pl v)) (hι' x).symm).trans (hφ v x).symm
    exact GlobalTheory.PointAtPlace.tauE_injective e1
  subst hpl
  have key : ∀ k, (∀ v, Formalism.MainNotions.S.uMat ((ι k).1 v) = Formalism.L2.SG.AdBridge.ofHAInf (Formalism.L2.SG.InstExistsPf.instOf D) k v) ∧ (Formalism.L2.SG.InstExistsPf.instOf D).fmat (ι k).2 = Formalism.L2.SG.AdBridge.ofHAFin _ k := by
    intro k
    have := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D k)
    have e := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply k
    exact ⟨fun v => (this.1 v).trans (congrArg (fun z => Formalism.L2.SG.AdBridge.ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) z v) e),
      this.2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (Formalism.IndefR.RationalEmbedding.inst D)) e)⟩
  have hinf : ∀ k v, Formalism.MainNotions.S.uMat ((ι k).1 v) = ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ *
      Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J (θ ((Formalism.L2.Host.tauPl D).symm v)) k *
      (Formalism.L2.SG.InstExistsPf.instOf D).P v := fun k v =>
    ((key k).1 v).trans (congrArg (fun M => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M * (Formalism.L2.SG.InstExistsPf.instOf D).P v)
      (map_thetaV_gen (Formalism.L2.SG.InstExistsPf.instOf D) v (θ ((Formalism.L2.Host.tauPl D).symm v)) (hθ _) k))
  have hPu := (Formalism.L2.SG.InstExistsPf.instOf D).P_unit

  have hd : ∀ v, IsUnit ((Formalism.L2.SG.InstExistsPf.instOf D).P v).det := fun v =>
    (Matrix.isUnit_iff_isUnit_det _).1 (hPu v)
  refine ⟨fun k => ⟨fun hk => ?_, fun hk => ?_⟩, ?_, ?_⟩
  · funext v
    apply Subtype.ext
    apply Units.ext
    show Formalism.MainNotions.S.uMat ((ι k).1 v) = 1
    rw [hinf k v]
    have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ ((Formalism.L2.Host.tauPl D).symm v)) k = 1 := infMat_of_mem_GfC k hk _
    rw [e, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd v)]
  · apply mem_GfC_of_infMat θ hθ k
    intro τ
    have e := hinf k (Formalism.L2.Host.tauPl D τ)
    rw [congrFun hk (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply] at e
    have e2 := (conj_eq_iff _ _ _ (hPu _)).1 e.symm
    refine e2.trans ?_
    rw [show Formalism.MainNotions.S.uMat ((1 : (Formalism.L2.SG.InstExistsPf.instOf D).Ginf) (Formalism.L2.Host.tauPl D τ)) = 1 from rfl,
      Matrix.mul_one]
    exact Matrix.mul_nonsing_inv _ (hd _)
  · intro τ g hg
    have hat := isAtTau_atTau θ hθ τ g hg
    refine ⟨?_, fun v hv => ?_, ?_⟩
    · apply Subtype.ext
      apply Units.ext
      have e := (key (atTau θ (D.sp.Y 0) τ g)).2
      refine e.trans (ofHAFin_eq_one _ _ ?_)
      · have e3 : (finHom (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g)).val = 1 := by
          rw [show finHom (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) = 1 from hat.1]; rfl
        ext i j
        exact congrFun (congrFun e3 i) j
    · apply Subtype.ext
      apply Units.ext
      show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 v) = 1
      rw [hinf _ v]
      have hne : (Formalism.L2.Host.tauPl D).symm v ≠ τ := fun e => hv ((Equiv.symm_apply_eq _).1 e)
      have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
          (θ ((Formalism.L2.Host.tauPl D).symm v)) (atTau θ (D.sp.Y 0) τ g) = 1 := hat.2.2 _ hne
      rw [e, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd v)]
    · apply heq_of_eq
      show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 (Formalism.L2.Host.tauPl D τ)) = _
      rw [hinf _ (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply]
      have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
          (θ τ) (atTau θ (D.sp.Y 0) τ g) = g := hat.2.1
      rw [e]
      rfl
  · intro τ y
    set P := (Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ) with hP
    have hdP : IsUnit P.det := hd _
    set H : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ :=
      gramAt D (D.sp.Y 0) τ with hH
    set Y : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ :=
      Formalism.MainNotions.S.uMat y with hY
    have hs : Pᴴ * H * P = Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) := by
      have := (Formalism.L2.SG.InstExistsPf.instOf D).P_spec (Formalism.L2.Host.tauPl D τ)
      have eφ : (Formalism.L2.SG.InstExistsPf.instOf D).φ (Formalism.L2.Host.tauPl D τ) = tauE D τ := by
        show embS D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D τ)) = _
        rw [Equiv.symm_apply_apply]
        rfl
      rw [eφ] at this
      exact this
    have hy : Yᴴ * Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) * Y =
        Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) := y.2
    have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdP
    have hPiH : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
    have hg : (P * Y * P⁻¹)ᴴ * H * (P * Y * P⁻¹) = H := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      calc (P⁻¹)ᴴ * (Yᴴ * Pᴴ) * H * (P * Y * P⁻¹) = (P⁻¹)ᴴ * (Yᴴ * (Pᴴ * H * P) * Y) * P⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = (P⁻¹)ᴴ * (Pᴴ * H * P) * P⁻¹ := by rw [hs, hy]
        _ = H := by
            simp only [Matrix.mul_assoc]
            rw [hPi, Matrix.mul_one, ← Matrix.mul_assoc, hPiH, Matrix.one_mul]
    refine ⟨P * Y * P⁻¹, hg, ?_⟩
    have hat := isAtTau_atTau θ hθ τ (P * Y * P⁻¹) hg
    apply Subtype.ext
    apply Units.ext
    show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ (P * Y * P⁻¹))).1 (Formalism.L2.Host.tauPl D τ)) = Y
    rw [hinf _ (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply]
    have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ τ) (atTau θ (D.sp.Y 0) τ (P * Y * P⁻¹)) = P * Y * P⁻¹ := hat.2.1
    rw [e]
    exact (conj_eq_iff _ _ _ (hPu _)).2 rfl

theorem iotaX_real_finite : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ hMod hιE
  exact iota_real_finite_of_eq R.θ hMod.inf X.B.I h X.ιE X.pl X.φ_eq hιE

end GlobalTheory.IotaReal
