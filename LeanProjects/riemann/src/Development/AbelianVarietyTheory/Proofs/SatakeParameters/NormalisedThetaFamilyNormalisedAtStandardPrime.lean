import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LocNormAmbOfOf
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.StdDataCmProof
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationIntertwinerPrimeIndexStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveIdealBaseThetaVectorNormalisedEveryPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTensorPowersStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalizationIntegralScalarStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)

noncomputable section
open scoped BigOperators ComplexConjugate

namespace GlobalTheory.ThLoc.LocStd

open Formalism.L2.Th1.H (Sesq IsSelfDual IsHerm dualLat altE Th alphaQ blk4 pow4 slice imgLat)
open Formalism.L2.Th1.F (cmTheta)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem cmTheta_odd (b : ℤ) (hb : Odd b) (d : ℕ) : ∃ k : ℤ, cmTheta b d = cmTheta 1 d + (k : ℂ) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  simp only [cmTheta]
  push_cast
  ring

theorem stable_of_one {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) (d : ℕ)
    (h : ∀ x ∈ Λ, cmTheta 1 d • x ∈ Λ) (b : ℤ) (hb : Odd b) : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ := by
  intro x hx
  obtain ⟨k, hk⟩ := cmTheta_odd b hb d
  rw [hk, add_smul]
  refine Λ.add_mem (h x hx) ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.zsmul_mem hx k

theorem hermitianSelfDual_of_fourfoldBlock {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hsd : IsSelfDual (matH (blk4 h)) (pow4 Λ)) : IsSelfDual (matH h) Λ := by
  have key : ∀ (x : n → ℂ) (y : Fin 4 × n → ℂ),
      altE (matH (blk4 h)) (Formalism.L2.Th1.H.CmData.embA 0 x) y = altE (matH h) x (slice 0 y) := by
    intro x y
    simp only [altE, Formalism.L2.Th1.H.matrixForm_fourfoldBlock, Formalism.L2.Th1.H.CmData.slice_embA]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  ext x
  constructor
  · intro hx
    have h1 : Formalism.L2.Th1.H.CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      intro y hy
      obtain ⟨m, hm⟩ := hx (slice 0 y) (hy 0)
      exact ⟨m, by rw [key, hm]⟩
    rw [hsd] at h1
    have h2 := h1 0
    rwa [Formalism.L2.Th1.H.CmData.slice_embA, if_pos rfl] at h2
  · intro hx y hy
    have h1 : Formalism.L2.Th1.H.CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      rw [hsd]
      exact Formalism.L2.Th1.H.CmData.embA_mem Λ 0 hx
    obtain ⟨m, hm⟩ := h1 _ (Formalism.L2.Th1.H.CmData.embA_mem Λ 0 hy)
    refine ⟨m, ?_⟩
    rw [key, Formalism.L2.Th1.H.CmData.slice_embA, if_pos rfl] at hm
    exact hm

section Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem selfDual_fourfold_curveIdeal_lattice (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (blk4 (hOne B.L D.what₂.Tau))) (pow4 B.lamM) := by
  have h := ((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _
    (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2] at h
  have h2 := SO.selfDual_img _ _ (SO.reix D.what₂.Tau) (SO.reix_isom B.L D.what₂.Tau) _ h
  rw [SO.reix_pow] at h2
  exact h2

theorem selfDual_lamM (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (hOne B.L D.what₂.Tau)) B.lamM :=
  hermitianSelfDual_of_fourfoldBlock _ _ (selfDual_fourfold_curveIdeal_lattice B hcc hδ)

theorem stable_lamM (b : ℤ) (hb : Odd b) : ∀ x ∈ B.lamM, cmTheta b D.host.d • x ∈ B.lamM := by
  refine stable_of_one _ _ (fun x hx => ?_) b hb
  have := SO.lamMM_smul (AR.om D) hx
  rw [← SO.theta_eq] at this
  exact this

end Base

end GlobalTheory.ThLoc.LocStd

namespace GlobalTheory.ThLoc.LocStd

open Formalism.L2.Th1.H (Sesq IsSelfDual IsHerm dualLat altE Th alphaQ blk4 pow4 slice imgLat)
open Formalism.L2.Th1.F (cmTheta)

section Reindex₂

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (σ : n' ≃ n)

abbrev reixE : (n' → ℂ) ≃ₗ[ℂ] (n → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ σ.symm

theorem matH_reix (h : Matrix n n ℂ) (h' : Matrix n' n' ℂ) (hh : ∀ i j, h' i j = h (σ i) (σ j)) (x y : n' → ℂ) :
    matH h' x y = matH h (reixE σ x) (reixE σ y) := by
  show (∑ i, ∑ j, x i * h' i j * conj (y j)) = ∑ i, ∑ j, x (σ.symm i) * h i j * conj (y (σ.symm j))
  rw [← Equiv.sum_comp σ.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp σ.symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hh, σ.apply_symm_apply, σ.apply_symm_apply]

theorem locNorm_reix (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ dK) (h : Matrix n n ℂ) (h' : Matrix n' n' ℂ) (hh : ∀ i j, h' i j = h (σ i) (σ j))
    (Λ : AddSubgroup (n → ℂ)) (hSD : IsSelfDual (matH h) Λ) (hSt : ∀ x ∈ Λ, cmTheta b₀ dK • x ∈ Λ)
    (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (H : LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι) :
    LocNorm a₀ b₀ dK ha hdK lam hlam h' (Λ.comap (reixE σ).toLinearMap.toAddMonoidHom) (fun z => θ (reixE σ z)) p ι := by
  obtain ⟨g₁, ε, hiso, hnd, hidx, hε, hker⟩ := H
  set σ₄ : Fin 4 × n' ≃ Fin 4 × n := Equiv.prodCongr (Equiv.refl _) σ with hσ₄
  set E4 := reixE σ₄ with hE4
  set L₀ := cmL a₀ b₀ dK ha hdK lam hlam with hL₀
  have hblk : ∀ w w', blk4 h' w w' = blk4 h (σ₄ w) (σ₄ w') := by
    intro w w'
    simp only [blk4, hσ₄, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id, hh]
  have hstd : ∀ w w' : Fin 4 × n', (((Formalism.L2.Th1.F.area L₀ : ℝ) : ℂ)⁻¹ • (1 : Matrix (Fin 4 × n') (Fin 4 × n') ℂ)) w w' =
      (((Formalism.L2.Th1.F.area L₀ : ℝ) : ℂ)⁻¹ • (1 : Matrix (Fin 4 × n) (Fin 4 × n) ℂ)) (σ₄ w) (σ₄ w') := by
    intro w w'
    simp only [Matrix.smul_apply, Matrix.one_apply, σ₄.injective.eq_iff]
  have hHs : ∀ x y, Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n') x y = Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n) (E4 x) (E4 y) :=
    matH_reix σ₄ _ _ hstd
  have hHb : ∀ x y, matH (blk4 h') x y = matH (blk4 h) (E4 x) (E4 y) := matH_reix σ₄ _ _ hblk
  let g₁' : (Fin 4 × n' → ℂ) ≃ₗ[ℂ] (Fin 4 × n' → ℂ) := E4.trans (g₁.trans E4.symm)
  have hg : ∀ z, E4 (g₁' z) = g₁ (E4 z) := fun z => by simp [g₁']
  have hP : pow4 (Λ.comap (reixE σ).toLinearMap.toAddMonoidHom) = (pow4 Λ).comap E4.toLinearMap.toAddMonoidHom := by
    ext z
    exact Iff.rfl
  have hS : Formalism.L2.Th1.H.stdLat L₀ (Fin 4 × n') =
      (Formalism.L2.Th1.H.stdLat L₀ (Fin 4 × n)).comap E4.toLinearMap.toAddMonoidHom := by
    ext z
    simp only [Formalism.L2.Th1.H.stdLat, AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hz w
      exact hz _
    · intro hz w
      have h1 := hz (σ₄ w)
      have e : (E4.toLinearMap.toAddMonoidHom z) (σ₄ w) = z w := by
        show z (σ₄.symm (σ₄ w)) = z w
        rw [σ₄.symm_apply_apply]
      rwa [e] at h1
  have hI : imgLat (g₁' : (Fin 4 × n' → ℂ) →ₗ[ℂ] (Fin 4 × n' → ℂ)) (pow4 (Λ.comap (reixE σ).toLinearMap.toAddMonoidHom)) =
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)).comap E4.toLinearMap.toAddMonoidHom := by
    rw [hP]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨E4 x, hx, (hg x).symm⟩
    · rintro ⟨y, hy, hyz⟩
      refine ⟨E4.symm y, ?_, ?_⟩
      · show E4 (E4.symm y) ∈ pow4 Λ
        rw [LinearEquiv.apply_symm_apply]
        exact hy
      · show g₁' (E4.symm y) = z
        apply E4.injective
        rw [hg, LinearEquiv.apply_symm_apply]
        exact hyz
  have hnz : Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat L₀ (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 := fun h0 => hnd (h0 ▸ dvd_zero p)
  have SD := Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ g₁ hiso hSD hSt hnz hidx
  have hF := (Formalism.L2.Th1.H.product_theta_mem L₀ (lam * a₀) (Fin 4 × n) SD.per SD.half _ SD.betaStd).1.2
  have hF0 : Formalism.L2.Th1.H.F0 L₀ (lam * a₀) (Fin 4 × n') = fun v => Formalism.L2.Th1.H.F0 L₀ (lam * a₀) (Fin 4 × n) (E4 v) := by
    funext v
    exact (Equiv.prod_comp σ₄.symm (fun w' => Formalism.L2.Th1.F.th0 L₀ (lam * a₀ / 2) (v w'))).symm
  have hHerm : IsHerm (Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n)) := by
    intro x y
    show (∑ i, ∑ j, y i * _ * conj (x j)) = conj (∑ i, ∑ j, x i * _ * conj (y j))
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul, Complex.conj_conj, map_inv₀, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hα : ∀ x, alphaQ (Real.sqrt dK / 2) (Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n')) x =
      alphaQ (Real.sqrt dK / 2) (Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n)) (E4 x) := by
    intro x
    simp only [alphaQ, Formalism.L2.Th1.H.qOf, hHs]
  have e1 := Formalism.L2.Ker.KS.inter_pb E4 _ _ hHs hHerm (Formalism.L2.Th1.H.stdLat L₀ (Fin 4 × n))
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) _ _ (fun x _ => hα x) (fun x _ => hα x) SD.betaSemi hnz _ hF
  refine ⟨g₁', ε, ?_, ?_, ?_, hε, ?_⟩
  · intro x y
    show Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n') (g₁' x) (g₁' y) = matH (blk4 h') x y
    rw [hHs, hg, hg, hHb]
    exact hiso (E4 x) (E4 y)
  · rw [hS, hI, Formalism.L2.Ker.KS.relIdx_pb]
    exact hnd
  · rw [hS, hI, Formalism.L2.Ker.KS.relIdx_pb]
    exact hidx
  · funext z
    have t1 : Formalism.L2.Th1.H.tens4 (fun z => θ (reixE σ z)) z = Formalism.L2.Th1.H.tens4 θ (E4 z) := rfl
    rw [t1, hker]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    unfold Formalism.L2.Th1.H.kernel4
    rw [hS, hI, hF0]
    have e2 := congrFun e1 (g₁' z)
    rw [hg] at e2
    exact e2.symm

end Reindex₂

section Main

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem hOne_reix {X : Fields} (s : Seam D X) (L : PeriodPair) (i j : X.Tau) :
    hOne L X.Tau i j = hOne L D.what₂.Tau (s.iT i) (s.iT j) := by
  simp only [hOne, Matrix.smul_apply, Matrix.one_apply, s.iT.injective.eq_iff]

theorem alphaQ_reix {X : Fields} (s : Seam D X) (L : PeriodPair) (c : ℝ) (x : X.Tau → ℂ) :
    alphaQ c (matH (hOne L X.Tau)) x = alphaQ c (matH (hOne L D.what₂.Tau)) (reixE s.iT x) := by
  simp only [alphaQ, Formalism.L2.Th1.H.qOf, matH_reix s.iT _ _ (hOne_reix s L)]

theorem latAt_std : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N) L → TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N') L' → GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  intro D cc δ hcc hδ B χ hχ X s hok a₀ b₀ c₀ ha hd lam hlam hcm hl N N' L L' hA p _ ι hL hL'
  have hb : Odd b₀ := Formalism.L2.Ker.KS.Lat.odd_of_cmOK hcm
  set B' := Formalism.L2.Ker.KS.cmBase B a₀ b₀ c₀ ha hd lam hlam hcm hl with hB'

  have hω : (B.ω₀ - lam * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice := by
    have e : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - cmTheta 1 D.host.d := by
      rw [Formalism.L2.Ker.KS.theta_val']; ring
    have h := Formalism.L2.Ker.KS.half_period_unique_CM a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (B.ω₀ / 2)
      ((Formalism.L2.Ker.KS.mem_lam_iff a₀ b₀ ha hd lam hlam hl _).1 B.t0.1)
      (by rw [← Formalism.L2.Ker.KS.mem_lam_iff a₀ b₀ ha hd lam hlam hl, Formalism.L2.Ker.KS.theta_val']; exact B.t0.2.1)
      (by rw [← Formalism.L2.Ker.KS.mem_lam_iff a₀ b₀ ha hd lam hlam hl, ← e]; exact B.t0.2.2)
    have e2 : (B.ω₀ - lam * a₀) / 2 = B.ω₀ / 2 - lam * a₀ / 2 := by ring
    rw [e2]
    exact h
  have hE : B.eNat χ = B'.eNat χ := Formalism.L2.Ker.KS.eNat_reBase B _ hl _ _ hω χ
  have hT : B'.tor = B.tor := rfl

  have hH : ∀ x y, matH (hOne B'.L X.Tau) x y = matH (hOne B'.L D.what₂.Tau) (reixE s.iT x) (reixE s.iT y) :=
    matH_reix s.iT _ _ (hOne_reix s B'.L)
  have hSDM : IsSelfDual (matH (hOne B'.L X.Tau)) (Formalism.L2.Ker.KS.lamM' s B') :=
    Formalism.L2.Ker.KS.selfDual_pb (reixE s.iT) _ _ hH (selfDual_lamM B' hcc hδ)
  have hStM : ∀ x ∈ Formalism.L2.Ker.KS.lamM' s B', cmTheta b₀ D.host.d • x ∈ Formalism.L2.Ker.KS.lamM' s B' := by
    intro x hx
    show reixE s.iT (cmTheta b₀ D.host.d • x) ∈ B'.lamM
    rw [map_smul]
    exact stable_lamM B' b₀ hb _ hx
  have hThM : Formalism.L2.Ker.KS.thM' s B' ∈ Th (matH (hOne B'.L X.Tau))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B'.L X.Tau))) (Formalism.L2.Ker.KS.lamM' s B') :=
    Formalism.L2.Ker.KS.th_pb (reixE s.iT) _ _ hH (fun x _ => alphaQ_reix s B'.L _ x)
      (B'.thMM_spec (B'.stdOK hcc hδ)).1
  have hMM0 := GlobalTheory.T.curveIdeal_baseThetaVector_normalised_every_place D cc δ hcc hδ B' a₀ b₀ c₀ ha hd lam hlam hcm
    (Formalism.L2.Ker.KS.cmBase_isCm B a₀ b₀ c₀ ha hd lam hlam hcm hl) p ι
  have hMM : LocNorm a₀ b₀ D.host.d ha hd lam hlam (hOne B'.L X.Tau) (Formalism.L2.Ker.KS.lamM' s B')
      (Formalism.L2.Ker.KS.thM' s B') p ι :=
    locNorm_reix s.iT a₀ b₀ c₀ D.host.d ha hd lam hlam hcm _ _ (hOne_reix s B'.L) _ (selfDual_lamM B' hcc hδ)
      (stable_lamM B' b₀ hb) _ p ι hMM0

  have hχu : ‖ι (Base.chiFac χ N N' L L')‖ ≤ 1 := by
    let lm : TaylorLogMetric.Qbar →+* ℂ_[p] := (ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.Qbar).val.toRingHom
    obtain ⟨h1, h2⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.chiFacUnit χ hχ p lm N N' L L' hA hL hL'
    have e : TaylorLogMetric.lamC lm (Base.chiFac χ N N' L L') = ι (Base.chiFac χ N N' L L') := by
      simp only [TaylorLogMetric.lamC, dif_pos h1]
      rfl
    rw [← e, h2]
  have key := Formalism.L2.Ker.KS.locNorm_thF_of s B' GlobalTheory.T.localNormalization_integral_scalar GlobalTheory.T.localNormalisation_tensorPowers GlobalTheory.T.localNormalisation_intertwiner_prime_index χ a₀ b₀ c₀ ha hd lam hlam p ι
    hcc hδ hcm hSDM hStM hThM hMM (Formalism.L2.Ker.KS.Lat.posDef_hSc (Formalism.L2.Ker.KS.Lat.sc_pos B) N N')
    (fun L L' h => Formalism.L2.Ker.KS.Lat.isLat_laF s B' hcc hδ h)
    (fun L L' h x hx => Formalism.L2.Ker.KS.Lat.theta_laF s B' hb hx) hA hL hL' hχu
  rw [← hE, hT] at key
  exact ⟨hcm, Formalism.L2.Ker.KS.Lat.selfDual_laF s B hcc hδ hA, fun x hx => Formalism.L2.Ker.KS.Lat.theta_laF s B hb hx,
    Formalism.L2.Ker.KS.Lat.eNat_laF s B hcc hδ χ hA, key⟩

end Main

end GlobalTheory.ThLoc.LocStd
