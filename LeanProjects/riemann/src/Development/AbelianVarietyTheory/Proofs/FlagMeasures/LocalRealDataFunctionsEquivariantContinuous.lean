import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorCR
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem uh_mul {k r : ℕ} {a b : MatKR k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

theorem b_eq_wT (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = wT C u τ (m * C.y τ) := by
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := uh_mul hm (C.y_mem τ)
  have hJ := Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hmy
  have hex : ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ :=
    ⟨Formalism.L2.SG.Pf.LocJEq.ujOf' _ hJ, rfl⟩
  unfold wT
  rw [dif_pos hex, Formalism.L2.SG.Pf.LocJEq.wloc_eq C hB u τ]
  have hc : Formalism.MainNotions.S.umat hex.choose = C.Q τ * (m * C.y τ) * C.Qi τ := hex.choose_spec
  rw [hc]
  unfold v0Of sigB
  rw [← Formalism.L2.SG.Pf.LocJEq.sig_mul τ (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hm)
    (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ (C.y_mem τ))]
  congr 2
  have e : C.Q τ * m * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ) = C.Q τ * m * (C.Qi τ * C.Q τ) * C.y τ * C.Qi τ := by
    simp only [Matrix.mul_assoc]
  rw [e, (C.isT τ).1, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem isSPsiEquiv_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {W F : MatKR k r → Wp}
    {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hW : IsSPsiEquiv z ψ π W)
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) : IsSPsiEquiv z ψ π F := by
  intro h hh n hn g hg
  have hhng : h * n * g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := uh_mul (uh_mul hh.1 hn.1) hg
  rw [hF _ hhng, hF g hg, Matrix.mul_assoc (h * n) g y, hW h hh n hn (g * y) (uh_mul hg hy), map_smul,
    smul_comm s (ψ n)]

theorem continuousOn_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {W F : MatKR k r → Wp} {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hW : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)))
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) :
    ContinuousOn F (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  have h1 : ContinuousOn (fun m : MatKR k r => s • W (m * y)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (hW.comp (continuous_id.matrix_mul continuous_const).continuousOn fun m hm => uh_mul hm hy).const_smul s
  exact h1.congr hF

theorem phi_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), (locS hB u u' τ).Φ m = (1 : ℂ) • wT C u τ (m * C.y τ) :=
  fun m hm => by rw [one_smul]; exact b_eq_wT C hB u τ hm

theorem phi'_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      (locS hB u u' τ).Φ' m = sclOf hB u u' τ • wT C u' τ (m * C.y τ) :=
  fun m hm => by
    show sclOf hB u u' τ • bOf hB u' τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = _
    rw [b_eq_wT C hB u' τ hm]

theorem tie_of (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hc : ∀ u, ContinuousOn (wT C u τ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)))
    (he : ∀ u, IsSPsiEquiv (zB X (C.Qi τ) u τ) (psiS D (zB X (C.Qi τ) u τ)) (piB X (C.Q τ) (C.Qi τ) u τ) (wT C u τ)) :
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  ⟨isSPsiEquiv_transl 1 (C.y_mem τ) (he u) (phi_eq C hB u u' τ),
    isSPsiEquiv_transl _ (C.y_mem τ) (he u') (phi'_eq C hB u u' τ),
    continuousOn_transl 1 (C.y_mem τ) (hc u) (phi_eq C hB u u' τ),
    continuousOn_transl _ (C.y_mem τ) (hc u') (phi'_eq C hB u u' τ)⟩

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

theorem locS_phi_equiv_cont : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  fun D X θ C hB u u' τ _ =>
    tie_of C hB u u' τ (fun u => Formalism.L2.SG.Pf.LocF.local_continuity_all D X θ C u τ)
      (fun u => Formalism.L2.SG.Pf.EquivPf.local_equivalence_all D X θ C u τ)

end GlobalTheory.SlocTie
