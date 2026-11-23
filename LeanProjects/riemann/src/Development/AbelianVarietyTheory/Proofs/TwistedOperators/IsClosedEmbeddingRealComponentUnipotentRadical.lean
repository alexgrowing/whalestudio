import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FibreAtTauEmb

section Lin

variable {n r : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} {K : Matrix (Fin n) (Fin r) ℂ}

theorem herm_mulVec (hG : Gᴴ = G) (a : Fin r → ℂ) (w : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm G (K *ᵥ a) w = star (star a ⬝ᵥ ((Kᴴ * G) *ᵥ w)) := by
  unfold Formalism.QuantumDeterminants.herm
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, hG, Matrix.star_mulVec, Matrix.dotProduct_mulVec (star a),
    Matrix.vecMul_vecMul]

theorem eq_zero_of_herm (hG : Gᴴ = G) (w : Fin n → ℂ) (h : ∀ a, Formalism.QuantumDeterminants.herm G (K *ᵥ a) w = 0) :
    (Kᴴ * G) *ᵥ w = 0 := by
  funext k
  have := h (Pi.single k 1)
  rw [herm_mulVec hG, star_eq_zero] at this
  simpa [dotProduct, Pi.single_apply] using this

theorem herm_conj {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ} (hPG : Pᴴ * Formalism.REAL.Jm ε * P = G)
    (u v : Fin n → ℂ) : Formalism.QuantumDeterminants.herm (Formalism.REAL.Jm ε) (P *ᵥ u) (P *ᵥ v) = Formalism.QuantumDeterminants.herm G u v := by
  unfold Formalism.QuantumDeterminants.herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hPG]

end Lin

end GlobalTheory.FibreAtTauEmb

namespace GlobalTheory.FibreAtTauEmb

section Conj

variable {n r : ℕ} {ε : Fin n → Bool} {G P : Matrix (Fin n) (Fin n) ℂ} {K : Matrix (Fin n) (Fin r) ℂ}

theorem mem_range_iff (x : Fin n → ℂ) :
    x ∈ LinearMap.range (P * K).mulVecLin ↔ ∃ a, x = P *ᵥ (K *ᵥ a) := by
  rw [LinearMap.mem_range]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩

theorem mem_NW_iff (hP : IsUnit P) (hPG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hG : Gᴴ = G) (u : Formalism.REAL.UJ ε)
    (m : Matrix (Fin n) (Fin n) ℂ) (hu : Formalism.MainNotions.S.umat u = P * m * P⁻¹) :
    u ∈ GlobalTheory.Dec.NW ε (LinearMap.range (P * K).mulVecLin) ↔
      ((m - 1) * K = 0 ∧ (Kᴴ * G) * (m - 1) = 0 ∧ ∀ y, (Kᴴ * G) *ᵥ y = 0 → ∃ a, (m - 1) *ᵥ y = K *ᵥ a) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hP1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hP2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have e1 : ∀ y, (Formalism.MainNotions.S.umat u - 1) *ᵥ y = P *ᵥ ((m - 1) *ᵥ (P⁻¹ *ᵥ y)) := fun y => by
    have : Formalism.MainNotions.S.umat u - 1 = P * (m - 1) * P⁻¹ := by
      rw [hu, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP1]
    rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have e2 : ∀ y, P⁻¹ *ᵥ (P *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hP2, Matrix.one_mulVec]
  have e3 : ∀ y, P *ᵥ (P⁻¹ *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hP1, Matrix.one_mulVec]
  have Pinj : ∀ x y, P *ᵥ x = P *ᵥ y → x = y := fun x y h => by rw [← e2 x, h, e2]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, fun y hy => ?_⟩
    · rw [← GlobalTheory.CuspCompare.forall_mulVec_eq_zero]
      intro a
      have := h1 (P *ᵥ (K *ᵥ a)) ((mem_range_iff _).2 ⟨a, rfl⟩)
      rw [e1, e2] at this
      rw [← Matrix.mulVec_mulVec]
      exact Pinj _ _ (this.trans (Matrix.mulVec_zero P).symm)
    · rw [← GlobalTheory.CuspCompare.forall_mulVec_eq_zero]
      intro y
      rw [← Matrix.mulVec_mulVec]
      refine eq_zero_of_herm hG _ fun a => ?_
      have := h3 (P *ᵥ y) (P *ᵥ (K *ᵥ a)) ((mem_range_iff _).2 ⟨a, rfl⟩)
      rwa [e1, e2, herm_conj hPG] at this
    · have := h2 (P *ᵥ y) fun x hx => by
        obtain ⟨a, rfl⟩ := (mem_range_iff x).1 hx
        rw [herm_conj hPG, herm_mulVec hG, hy, dotProduct_zero, star_zero]
      rw [e1, e2] at this
      obtain ⟨a, ha⟩ := (mem_range_iff _).1 this
      exact ⟨a, Pinj _ _ ha⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩
    · obtain ⟨a, rfl⟩ := (mem_range_iff x).1 hx
      rw [e1, e2, Matrix.mulVec_mulVec _ (m - 1) K, h1, Matrix.zero_mulVec, Matrix.mulVec_zero]
    · have hz : (Kᴴ * G) *ᵥ (P⁻¹ *ᵥ y) = 0 := eq_zero_of_herm hG _ fun a => by
        have := hy (P *ᵥ (K *ᵥ a)) ((mem_range_iff _).2 ⟨a, rfl⟩)
        rwa [← e3 y, herm_conj hPG] at this
      obtain ⟨a, ha⟩ := h3 _ hz
      rw [e1, ha]
      exact (mem_range_iff _).2 ⟨a, rfl⟩
    · obtain ⟨a, rfl⟩ := (mem_range_iff x).1 hx
      rw [e1, herm_conj hPG, herm_mulVec hG, Matrix.mulVec_mulVec _ (Kᴴ * G) (m - 1), h2, Matrix.zero_mulVec,
        dotProduct_zero, star_zero]

end Conj

end GlobalTheory.FibreAtTauEmb

namespace GlobalTheory.FibreAtTauEmb

section Iso

variable {n r : ℕ} {ε : Fin n → Bool} {G P : Matrix (Fin n) (Fin n) ℂ} {K : Matrix (Fin n) (Fin r) ℂ}

theorem isIsoC_range (hP : IsUnit P) (hPG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hG : Gᴴ = G) (hK : Kᴴ * G * K = 0)
    {a₀ : Fin r → ℂ} (ha₀ : K *ᵥ a₀ ≠ 0) : GlobalTheory.Dec.IsIsoC ε (LinearMap.range (P * K).mulVecLin) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨P *ᵥ (K *ᵥ a₀), (mem_range_iff _).2 ⟨a₀, rfl⟩, fun h => ha₀ ?_⟩,
    fun x hx y hy => ?_⟩
  · have := congrArg (fun v => P⁻¹ *ᵥ v) h
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
    rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hd, Matrix.one_mul] at this
  · obtain ⟨a, rfl⟩ := (mem_range_iff x).1 hx
    obtain ⟨b, rfl⟩ := (mem_range_iff y).1 hy
    rw [herm_conj hPG, herm_mulVec hG, Matrix.mulVec_mulVec, hK, Matrix.zero_mulVec, dotProduct_zero, star_zero]

theorem inv_val_UJ (u : Formalism.REAL.UJ ε) :
    (((u : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      Formalism.REAL.Jm ε * (Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm ε := by
  apply Units.inv_eq_of_mul_eq_one_left
  have h : ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε *
      ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Formalism.REAL.Jm ε := u.2
  calc Formalism.REAL.Jm ε * (Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm ε * ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Formalism.REAL.Jm ε * (((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε *
        ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Formalism.REAL.Jm_mul_self]

theorem conj_mem_UH (hP : IsUnit P) (hPG : Pᴴ * Formalism.REAL.Jm ε * P = G) (u : Formalism.REAL.UJ ε) :
    P⁻¹ * Formalism.MainNotions.S.umat u * P ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hP1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h : (Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.umat u = Formalism.REAL.Jm ε := u.2
  show (P⁻¹ * Formalism.MainNotions.S.umat u * P)ᴴ * G * (P⁻¹ * Formalism.MainNotions.S.umat u * P) = G
  rw [← hPG]
  calc (P⁻¹ * Formalism.MainNotions.S.umat u * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * Formalism.MainNotions.S.umat u * P)
      = Pᴴ * (Formalism.MainNotions.S.umat u)ᴴ * (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) * Formalism.MainNotions.S.umat u * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * ((Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.umat u) * P := by
        rw [hP1, Matrix.conjTranspose_one]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [h]

end Iso

end GlobalTheory.FibreAtTauEmb

namespace GlobalTheory.FibreAtTauEmb

section Adelic

variable {D : D7}

theorem tauE_sig_of {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : D.host.E) :
    tauE D τ (D.sp.cm.sig x) = starRingEnd ℂ (tauE D τ x) := by
  have hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  have h := GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ τ) ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] x)
  have e : sigR (Ainf D.host.F) D.sp.cm.sig ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] x) =
      (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (D.sp.cm.sig x) := rfl
  rw [e, (hθ τ).1, (hθ τ).1] at h
  exact h

theorem psi_incA {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (x : D.host.E) :
    ((θ ρ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom) (incA D x) =
      tauE D ρ x := by
  simp only [incA, inclR, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]
  exact (hθ ρ).1 x

theorem fin_incA (x : D.host.E) :
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (incA D x) =
      inclR (Af D.host.F) x := by
  simp only [incA, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem adele_eq_zero {θ : InfFam D} (hθ : IsInfFam θ) (z : AF D.host.F ⊗[D.host.F] D.host.E)
    (h1 : ∀ ρ, ((θ ρ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom) z = 0)
    (h2 : (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom z = 0) : z = 0 := by
  have hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  have hb := GlobalTheory.Mem.VolExists.infEmb_bijective hcm hτ (θ := θ) hθ
  refine GlobalTheory.CuspCompare.adele_tens_eq_zero (A := Ainf D.host.F) (B := Af D.host.F) z ?_ h2
  apply hb.1
  funext ρ
  exact (h1 ρ).trans (map_zero _).symm

theorem map_psi {θ : InfFam D} (V : HSp D) (ρ : D.what₂.Tau) (g : GA D V) :
    ((matHom V g).1 - 1).map ((θ ρ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom) =
      infMat D.sp.cm.sig V.gram (θ ρ) g - 1 := by
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem map_fin {V : HSp D} {g : GA D V} (hg : g ∈ GinfC V) :
    ((matHom V g).1 - 1).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = 0 := by
  have h : finHom V g = 1 := hg
  have h' := congrArg Units.val h
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  change (finHom V g).val - 1 = 0
  rw [h', Units.val_one, sub_self]

end Adelic

end GlobalTheory.FibreAtTauEmb

namespace GlobalTheory.FibreAtTauEmb

section Adelic2

variable {D : D7}

theorem unipEq_of_real {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {r : ℕ} {C R : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B L : Matrix (Fin r) (Fin V.rank) D.host.E} (g : GA D V) (hg : g ∈ GinfC V)
    (h : ∀ ρ, GlobalTheory.CuspCompare.UnipEq (tauE D ρ) C R B L (infMat D.sp.cm.sig V.gram (θ ρ) g - 1)) :
    GlobalTheory.CuspCompare.UnipEq (incA D) C R B L ((matHom V g).1 - 1) := by
  refine GlobalTheory.CuspCompare.UnipEq.of_map (incA D) (fun ρ => (θ ρ).comp (Algebra.TensorProduct.map (fstA D.host.F)
    (AlgHom.id D.host.F D.host.E)).toRingHom) (Algebra.TensorProduct.map (sndA D.host.F)
    (AlgHom.id D.host.F D.host.E)).toRingHom (psi_incA hθ) fin_incA (adele_eq_zero hθ) (fun ρ => ?_) ?_
  · rw [map_psi]
    exact h ρ
  · rw [map_fin hg]
    exact ⟨by simp, by simp, by simp⟩

theorem unipEq_at {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {r : ℕ} {C R : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B L : Matrix (Fin r) (Fin V.rank) D.host.E} (g : GA D V) (ρ : D.what₂.Tau)
    (h : GlobalTheory.CuspCompare.UnipEq (incA D) C R B L ((matHom V g).1 - 1)) :
    GlobalTheory.CuspCompare.UnipEq (tauE D ρ) C R B L (infMat D.sp.cm.sig V.gram (θ ρ) g - 1) := by
  have h' := GlobalTheory.CuspCompare.UnipEq.map (incA D) ((θ ρ).comp (Algebra.TensorProduct.map (fstA D.host.F)
    (AlgHom.id D.host.F D.host.E)).toRingHom) (psi_incA hθ ρ) h
  rwa [map_psi] at h'

theorem mem_NI_iff_unipEq {V : HSp D} {r : ℕ} {C R : Matrix (Fin V.rank) (Fin r) D.host.E}
    {L : Matrix (Fin r) (Fin V.rank) D.host.E} (hL : L * C = 1)
    (hR : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram * R = 1) (g : GA D V) :
    (GlobalTheory.CuspCompare.UnipEq (incA D) C R (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) L
      ((matHom V g).1 - 1)) ↔
    g ∈ {g : GA D V | let m : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) := (matHom V g).1 - 1
      HMul.hMul m (C.map (incA D)) = 0 ∧
      HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D)) m = 0 ∧
      ∀ x : Fin V.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec x = 0 →
        ∃ a : Fin r → AF D.host.F ⊗[D.host.F] D.host.E,
          m.mulVec (fun i => incA D (x i)) = (C.map (incA D)).mulVec a} :=
  and_congr Iff.rfl (and_congr Iff.rfl (GlobalTheory.CuspCompare.perp_cond (incA D) hL hR _).2.symm)

theorem NI_eq (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    NI V C = Subgroup.closure {g : GA D V | let m : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) := (matHom V g).1 - 1
      HMul.hMul m (C.map (incA D)) = 0 ∧
      HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D)) m = 0 ∧
      ∀ x : Fin V.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec x = 0 →
        ∃ a : Fin r → AF D.host.F ⊗[D.host.F] D.host.E,
          m.mulVec (fun i => incA D (x i)) = (C.map (incA D)).mulVec a} := rfl

end Adelic2

end GlobalTheory.FibreAtTauEmb

namespace GlobalTheory.FibreAtTauEmb

theorem isClosedEmbedding_atP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ E : GA D V →* Formalism.REAL.UJ (M.ε τ), (∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) → ∃ W : Submodule ℂ (Fin V.rank → ℂ), GlobalTheory.Dec.IsIsoC (M.ε τ) W ∧ Topology.IsClosedEmbedding (fun p : GlobalTheory.FibreAtTau.atP θ V C τ => E ((p : NI V C) : GA D V)) ∧ Set.range (fun p : GlobalTheory.FibreAtTau.atP θ V C τ => E ((p : NI V C) : GA D V)) = GlobalTheory.Dec.NW (M.ε τ) W := by
  intro D θ hθ V S M τ r C hC E hE

  set P := M.fr τ with hPdef
  set G := gramAt D V τ with hGdef
  set K : Matrix (Fin V.rank) (Fin r) ℂ := C.map (tauE D τ) with hKdef
  have hP : IsUnit P := M.fr_unit τ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hP1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hP2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have hPG : Pᴴ * Formalism.REAL.Jm (M.ε τ) * P = G := M.fr_gram τ
  have hG : Gᴴ = G := by
    rw [← hPG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Formalism.REAL.Jm_conjTranspose, Matrix.mul_assoc]
  set B0 := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram with hB0
  have hB : Kᴴ * G = B0.map (tauE D τ) := by
    rw [Matrix.map_mul]
    congr 1
    ext i j
    simp [K, Formalism.UG.cT, Matrix.conjTranspose_apply, tauE_sig_of hθ]
  have hKGK : Kᴴ * G * K = 0 := by
    rw [hB, hKdef, ← Matrix.map_mul, hC.2.2, Matrix.map_zero _ (map_zero _)]

  have hJ : V.gram.det ≠ 0 := by
    intro h0
    have h1 : G.det = 0 := by
      rw [hGdef, gramAt, show (HSpace.gram V).map (tauE D τ) = (tauE D τ).mapMatrix (HSpace.gram V) from rfl,
        ← RingHom.map_det, h0, map_zero]
    have hJd : IsUnit (Formalism.REAL.Jm (M.ε τ)).det := Matrix.isUnit_det_of_left_inverse (Formalism.REAL.Jm_mul_self (M.ε τ))
    rw [← hPG, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hd.ne_zero) hJd.ne_zero) hd.ne_zero h1
  obtain ⟨L, R, hL, hR⟩ := GlobalTheory.CuspCompare.exists_inverses (D.sp.cm.sig : D.host.E →+* D.host.E) hJ hC.2.1

  have hUC : ∀ g : Matrix (Fin V.rank) (Fin V.rank) ℂ, GlobalTheory.CuspCompare.UnipEq (tauE D τ) C R B0 L (g - 1) ↔
      ((g - 1) * K = 0 ∧ (Kᴴ * G) * (g - 1) = 0 ∧ ∀ y, (Kᴴ * G) *ᵥ y = 0 → ∃ a, (g - 1) *ᵥ y = K *ᵥ a) := by
    intro g
    rw [hB]
    exact and_congr Iff.rfl (and_congr Iff.rfl (GlobalTheory.CuspCompare.perp_cond (tauE D τ) hL hR _).1.symm)
  set W : Submodule ℂ (Fin V.rank → ℂ) := LinearMap.range (P * K).mulVecLin with hWdef

  have hle : NI V C ≤ (GlobalTheory.Dec.nwSub (M.ε τ) W).comap E := by
    rw [NI_eq]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    have hu' := unipEq_at hθ g τ ((mem_NI_iff_unipEq hL hR g).2 hg)
    exact (GlobalTheory.FibreAtTauEmb.mem_NW_iff hP hPG hG (E g) _ (hE g)).2 ((hUC _).1 hu')

  have hback : ∀ u ∈ GlobalTheory.Dec.NW (M.ε τ) W, atTau θ V τ (P⁻¹ * Formalism.MainNotions.S.umat u * P) ∈ NI V C ∧
      IsAtTau θ V τ (P⁻¹ * Formalism.MainNotions.S.umat u * P) (atTau θ V τ (P⁻¹ * Formalism.MainNotions.S.umat u * P)) := by
    intro u hu
    set g' := P⁻¹ * Formalism.MainNotions.S.umat u * P with hg'
    have hcj : Formalism.MainNotions.S.umat u = P * g' * P⁻¹ := by
      rw [hg', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1, Matrix.one_mul, Matrix.mul_assoc, hP1, Matrix.mul_one]
    have hc := (hUC g').2 ((GlobalTheory.FibreAtTauEmb.mem_NW_iff hP hPG hG u g' hcj).1 hu)
    have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (GlobalTheory.FibreAtTauEmb.conj_mem_UH hP hPG u)
    refine ⟨?_, hs⟩
    rw [NI_eq]
    refine Subgroup.subset_closure ((mem_NI_iff_unipEq hL hR _).1 (unipEq_of_real hθ _ hs.1 fun ρ => ?_))
    by_cases hρ : ρ = τ
    · subst hρ
      rw [hs.2.1]
      exact hc
    · rw [hs.2.2 ρ hρ, sub_self]
      exact ⟨by simp, by simp, by simp⟩

  set f : GlobalTheory.FibreAtTau.atP θ V C τ → Formalism.REAL.UJ (M.ε τ) := fun p => E ((p : NI V C) : GA D V) with hfdef
  set ψ : Formalism.REAL.UJ (M.ε τ) → GA D V := fun u => atTau θ V τ (P⁻¹ * Formalism.MainNotions.S.umat u * P) with hψdef
  have hleft : ∀ p : GlobalTheory.FibreAtTau.atP θ V C τ, ψ (f p) = ((p : NI V C) : GA D V) := by
    intro p
    have hm := GlobalTheory.FibreAtTau.mem_atP.1 p.2
    have e : P⁻¹ * Formalism.MainNotions.S.umat (f p) * P = cmp θ τ ((p : NI V C) : GA D V) := by
      simp only [hfdef]
      rw [hE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP2, Matrix.one_mul, Matrix.mul_assoc, hP2, Matrix.mul_one]
    have hUH := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V ((p : NI V C) : GA D V) τ
    simp only [hψdef]
    rw [e]
    exact (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ _ hUH).unique (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hUH)
      ⟨hm.1, rfl, hm.2⟩
  have hcomp : ψ ∘ f = fun p : GlobalTheory.FibreAtTau.atP θ V C τ => ((p : NI V C) : GA D V) := funext hleft

  have hval : Continuous fun p : GlobalTheory.FibreAtTau.atP θ V C τ => Formalism.MainNotions.S.umat (f p) := by
    have e : (fun p : GlobalTheory.FibreAtTau.atP θ V C τ => Formalism.MainNotions.S.umat (f p)) =
        fun p : GlobalTheory.FibreAtTau.atP θ V C τ => P * infMat D.sp.cm.sig V.gram (θ τ) ((p : NI V C) : GA D V) * P⁻¹ := funext fun p => hE _
    rw [e]
    exact (continuous_const.matrix_mul ((GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ)).comp
      (continuous_subtype_val.comp continuous_subtype_val))).matrix_mul continuous_const
  have hcont : Continuous f := by
    refine Topology.IsInducing.subtypeVal.continuous_iff.2 (Units.continuous_iff.2 ⟨hval, ?_⟩)
    exact ((continuous_const.matrix_mul hval.matrix_conjTranspose).matrix_mul continuous_const).congr
      fun p => (GlobalTheory.FibreAtTauEmb.inv_val_UJ (f p)).symm
  have hψc : Continuous ψ :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous
      ((continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul continuous_const)
      (fun u => GlobalTheory.FibreAtTauEmb.conj_mem_UH hP hPG u)
  have hind : Topology.IsInducing f := by
    refine Topology.IsInducing.of_comp hcont hψc ?_
    rw [hcomp]
    exact Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hinj : Function.Injective f := fun p q h => by
    have := congrArg ψ h
    rw [hleft, hleft] at this
    exact Subtype.ext (Subtype.ext this)

  have hrange : Set.range f = GlobalTheory.Dec.NW (M.ε τ) W := by
    ext u
    constructor
    · rintro ⟨p, rfl⟩
      exact hle (p : NI V C).2
    · intro hu
      obtain ⟨hN, hs⟩ := hback u hu
      refine ⟨⟨⟨_, hN⟩, GlobalTheory.FibreAtTau.mem_atP.2 ⟨hs.1, hs.2.2⟩⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      show Formalism.MainNotions.S.umat (E _) = Formalism.MainNotions.S.umat u
      rw [hE]
      change P * infMat D.sp.cm.sig V.gram (θ τ) (atTau θ V τ (P⁻¹ * Formalism.MainNotions.S.umat u * P)) * P⁻¹ = _
      rw [hs.2.1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1, Matrix.one_mul, Matrix.mul_assoc, hP1, Matrix.mul_one]

  have hne : ∃ a₀ : Fin r → ℂ, K *ᵥ a₀ ≠ 0 := by
    refine ⟨Pi.single ⟨0, hC.1⟩ 1, fun h => hC.2.1.ne_zero ⟨0, hC.1⟩ ?_⟩
    funext j
    have := congrFun h j
    simp only [hKdef, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.map_apply, Pi.zero_apply] at this
    simpa using (map_eq_zero_iff _ (tauE D τ).injective).1 this
  obtain ⟨a₀, ha₀⟩ := hne
  exact ⟨W, GlobalTheory.FibreAtTauEmb.isIsoC_range hP hPG hG hKGK ha₀, ⟨⟨hind, hinj⟩, by rw [hrange]; exact GlobalTheory.Dec.isClosed_NW _ _⟩,
    hrange⟩

end GlobalTheory.FibreAtTauEmb
