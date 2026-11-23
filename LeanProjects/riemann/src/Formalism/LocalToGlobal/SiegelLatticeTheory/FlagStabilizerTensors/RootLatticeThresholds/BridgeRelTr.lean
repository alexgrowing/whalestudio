import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierSizes

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions
open Classical

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

section Gen

variable {n : ℕ} {ε : Fin n → Bool}

theorem jUnit_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε)
    (hB : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε) : (A * B)ᴴ * Formalism.REAL.Jm ε * (A * B) = Formalism.REAL.Jm ε := by
  rw [Matrix.conjTranspose_mul]
  calc Bᴴ * Aᴴ * Formalism.REAL.Jm ε * (A * B) = Bᴴ * (Aᴴ * Formalism.REAL.Jm ε * A) * B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hA, hB]

theorem inN_one {r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : InN ε e z 1 := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> simp [Submodule.zero_mem]

theorem psi_norm {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd ρ) * Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd ρ = 1 := by
  unfold Formalism.QuantumDeterminants.psi
  rw [show ∀ x : ℂ, star (Complex.exp x) = (starRingEnd ℂ) (Complex.exp x) from fun _ => rfl, ← Complex.exp_conj,
    ← Complex.exp_add]
  simp [Complex.conj_ofReal, Complex.conj_I]

end Gen

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

theorem psiR_one' (v : InfinitePlace X.B.I.F) (w : D.what₂.Word) (gg : ℕ) :
    psiR (X.B.I.ε v) gg (PtRepPf.frU X w v).e (PtRepPf.frU X w v).fd (PtRepPf.frU X w v).z 1 = 1 :=
  Bridge.psiR_of ⟨fun a => Matrix.one_mulVec _, Matrix.one_mulVec _, fun y _ => by simp [Submodule.zero_mem]⟩ gg

theorem qrq_unit {n r k : ℕ} {ε : Fin n → Bool} {F : PtRepPf.Fr ε r k} {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ} (hT : Bridge.TrHyp F Qm Qim c)
    {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hρ : ρᴴ * Formalism.QuantumDeterminants.Hpk k r * ρ = Formalism.QuantumDeterminants.Hpk k r) :
    (Qm * ρ * Qim)ᴴ * Formalism.REAL.Jm ε * (Qm * ρ * Qim) = Formalism.REAL.Jm ε := by
  have h2 : Qimᴴ * Qmᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hT.h2, Matrix.conjTranspose_one]
  calc (Qm * ρ * Qim)ᴴ * Formalism.REAL.Jm ε * (Qm * ρ * Qim)
      = Qimᴴ * ((ρᴴ * (Qmᴴ * Formalism.REAL.Jm ε * Qm) * ρ) * Qim) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Qimᴴ * (Qmᴴ * Formalism.REAL.Jm ε * Qm) * Qim := by rw [hT.hH, hρ, Matrix.mul_assoc]
    _ = (Qimᴴ * Qmᴴ) * Formalism.REAL.Jm ε * (Qm * Qim) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h2, hT.h2, Matrix.one_mul, Matrix.mul_one]

theorem relTr_carrierOf (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀)))
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) :
    0 < sc → StRel X u u' →
    (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).FromX →
    (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).Base i0 i0' →
    (∀ j x, (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).S.emb j
        (X.ιE x) = X.B.I.φ
          ((CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).τ j) x) →
    ∀ w, OkPt X u u' w → ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' → ∀ v : InfinitePlace X.B.I.F,
      Formalism.FourierDecayAlt.C6.IsRelevant
        ((CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).T
          ((CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).τ.symm v)).base
        (trG ((CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).Q v)
          ((CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).Qi v)
          ((h v)⁻¹ * (gamW X u u' w) v * h' v)) := by
  intro _ hSR hFX _ _ w hw h h' hD v
  obtain ⟨hHu, hH'u, -⟩ := hD
  obtain ⟨hQ, hz, hz', -⟩ := hFX v
  have hz2 : (T ((tauE X e).symm v)).base.z = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u) := hz
  have hz2' : (T ((tauE X e).symm v)).base.z' = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u') := hz'
  set Qm := Formalism.L2.SG.LocWSOf.Qcs C (X.pl v) with hQm
  set Qim := Formalism.L2.SG.LocWSOf.Qics C (X.pl v) with hQim
  set gg : ℕ := X.B.g with hggdef
  have hgg0 : 0 < gg := by
    rw [hggdef, X.g_eq]; exact Nat.mul_pos (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1 (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2
  set κ : ℂ := -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ) with hκ
  have hc : ∀ a : Fin D.R.rS, cTor ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) D.R.rS a = κ ^ (D.R.rS - a.val) := by
    intro a
    unfold cTor
    congr 1
    rw [hκ, hggdef, X.g_eq]
    push_cast
    field_simp
  have hTr : Bridge.TrHyp (PtRepPf.frU X u v) Qm Qim (fun a => cTor ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (PtRepPf.frU X u' v) Qm Qim (fun a => cTor ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hfix : ∀ (w : D.what₂.Word) (s : X.B.I.Ginf), s ∈ HsetU X w →
      (∀ a, Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).e a = (PtRepPf.frU X w v).e a) ∧
      (∀ a, Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).fd a = (PtRepPf.frU X w v).fd a) ∧
      Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).z = (PtRepPf.frU X w v).z := by
    intro w s hs
    refine ⟨fun a => hs v _ ?_, fun a => hs v _ ?_, hs v _ ?_⟩
    · exact Or.inl (Or.inl ⟨a, rfl⟩)
    · exact Or.inl (Or.inr ⟨a, rfl⟩)
    · exact Or.inr rfl
  obtain ⟨hHe, hHf, hHz⟩ := hfix u h hHu
  obtain ⟨hH'e, hH'f, hH'z⟩ := hfix u' h' hH'u
  set H := Formalism.MainNotions.S.uMat (h v)
  set Hi := Formalism.MainNotions.S.uMat (h v)⁻¹
  set H' := Formalism.MainNotions.S.uMat (h' v)
  set H'i := Formalism.MainNotions.S.uMat (h' v)⁻¹
  set G := Formalism.MainNotions.S.uMat ((gamW X u u' w) v)
  set Gi := Formalism.MainNotions.S.uMat ((gamW X u u' w) v)⁻¹
  set A := Formalism.MainNotions.S.uMat ((h v)⁻¹ * (gamW X u u' w) v * h' v)
  set Ai := Formalism.MainNotions.S.uMat ((h v)⁻¹ * (gamW X u u' w) v * h' v)⁻¹
  have hAA : A * Ai = 1 := uMat_mul_inv _
  have hAdef : A = Hi * G * H' := rfl
  have hAidef : Ai = H'i * Gi * H := by
    have e : ((h v)⁻¹ * (gamW X u u' w) v * h' v)⁻¹ = (h' v)⁻¹ * ((gamW X u u' w) v)⁻¹ * h v := by group
    show Formalism.MainNotions.S.uMat ((h v)⁻¹ * (gamW X u u' w) v * h' v)⁻¹ = _
    rw [e]
    rfl
  have hδinv : (Qim * A * Qm)⁻¹ = Qim * Ai * Qm := by
    apply Matrix.inv_eq_right_inv
    calc Qim * A * Qm * (Qim * Ai * Qm) = Qim * (A * ((Qm * Qim) * (Ai * Qm))) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hTr.h2, Matrix.one_mul, ← Matrix.mul_assoc A Ai Qm, hAA, Matrix.one_mul, hTr.h1]
  refine ⟨Bridge.delta_GV hTr (uMat_unitary _), fun ρ0 hρ => ?_⟩
  obtain ⟨ρ, rfl⟩ : ∃ ρ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, ρ = ρ0 := ⟨ρ0, rfl⟩
  have hρ1 : ρ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := hρ.1
  have hρ2 : (Qim * A * Qm)⁻¹ * ρ * (Qim * A * Qm) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := hρ.2
  change Formalism.QuantumDeterminants.psi D.R.k D.R.rS (T ((tauE X e).symm v)).base.z Formalism.QuantumDeterminants.cStd ρ =
    Formalism.QuantumDeterminants.psi D.R.k D.R.rS (T ((tauE X e).symm v)).base.z' Formalism.QuantumDeterminants.cStd ((Qim * A * Qm)⁻¹ * ρ * (Qim * A * Qm))
  rw [hδinv] at hρ2 ⊢
  rw [hz2, hz2']

  have hρu := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hρ1
  set ρi := ρ⁻¹
  have hρρ : ρ * ρi = 1 := Matrix.mul_nonsing_inv ρ hρu
  have hρρ' : ρi * ρ = 1 := Matrix.nonsing_inv_mul ρ hρu

  set M := H * (Qm * ρ * Qim) * Hi with hM
  set Mi := H * (Qm * ρi * Qim) * Hi with hMi
  have hHiH : Hi * H = 1 := uMat_inv_mul (h v)
  have hHHi : H * Hi = 1 := uMat_mul_inv (h v)
  have hMMi : M * Mi = 1 := by
    calc M * Mi = H * (Qm * (ρ * ((Qim * ((Hi * H) * (Qm * (ρi * (Qim * Hi)))))))) := by
          simp only [hM, hMi, Matrix.mul_assoc]
      _ = 1 := by
        rw [hHiH, Matrix.one_mul, ← Matrix.mul_assoc Qim Qm, hTr.h1, Matrix.one_mul, ← Matrix.mul_assoc ρ ρi,
          hρρ, Matrix.one_mul, ← Matrix.mul_assoc Qm Qim, hTr.h2, Matrix.one_mul, hHHi]
  have hMiM : Mi * M = 1 := by
    calc Mi * M = H * (Qm * (ρi * ((Qim * ((Hi * H) * (Qm * (ρ * (Qim * Hi)))))))) := by
          simp only [hM, hMi, Matrix.mul_assoc]
      _ = 1 := by
        rw [hHiH, Matrix.one_mul, ← Matrix.mul_assoc Qim Qm, hTr.h1, Matrix.one_mul, ← Matrix.mul_assoc ρi ρ,
          hρρ', Matrix.one_mul, ← Matrix.mul_assoc Qm Qim, hTr.h2, Matrix.one_mul, hHHi]
  have hMJ : Mᴴ * Formalism.REAL.Jm (X.B.I.ε v) * M = Formalism.REAL.Jm (X.B.I.ε v) :=
    jUnit_mul (jUnit_mul (uMat_unitary (h v)) (qrq_unit hTr hρ1.1)) (uMat_unitary (h v)⁻¹)
  let sv : Formalism.REAL.UJ (X.B.I.ε v) := ⟨⟨M, Mi, hMMi, hMiM⟩, hMJ⟩
  let s : X.B.I.Ginf := Pi.mulSingle (M := fun v' => Formalism.REAL.UJ (X.B.I.ε v')) v sv
  have hsv : Formalism.MainNotions.S.uMat (s v) = M := by simp [s, sv, Formalism.MainNotions.S.uMat]
  have hso : ∀ v', v' ≠ v → s v' = 1 := fun v' hv' => by
    show Pi.mulSingle (M := fun v' => Formalism.REAL.UJ (X.B.I.ε v')) v sv v' = 1
    exact Pi.mulSingle_eq_of_ne (M := fun v' => Formalism.REAL.UJ (X.B.I.ε v')) hv' sv
  have huone : ∀ v', Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ (X.B.I.ε v')) = 1 := fun v' => by simp [Formalism.MainNotions.S.uMat]

  have hkey : Gi * M * G = H' * (Qm * (Qim * Ai * Qm * ρ * (Qim * A * Qm)) * Qim) * H'i := by
    have e1 : Qm * (Qim * Ai * Qm * ρ * (Qim * A * Qm)) * Qim = Ai * (Qm * ρ * Qim) * A := by
      calc Qm * (Qim * Ai * Qm * ρ * (Qim * A * Qm)) * Qim
          = (Qm * Qim) * Ai * (Qm * ρ * Qim) * A * (Qm * Qim) := by simp only [Matrix.mul_assoc]
        _ = Ai * (Qm * ρ * Qim) * A := by rw [hTr.h2, Matrix.one_mul, Matrix.mul_one]
    rw [e1, hAdef, hAidef]
    have hH'H'i : H' * H'i = 1 := uMat_mul_inv (h' v)
    calc Gi * M * G = Gi * (H * (Qm * ρ * Qim) * Hi) * G := rfl
      _ = (H' * H'i) * (Gi * (H * ((Qm * ρ * Qim) * (Hi * (G * (H' * H'i)))))) := by
          rw [hH'H'i, Matrix.one_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = H' * (H'i * Gi * H * (Qm * ρ * Qim) * (Hi * G * H')) * H'i := by simp only [Matrix.mul_assoc]
  have hs : s ∈ StInf X u u' (gamW X u u' w) := by
    refine ⟨fun v' => ?_, fun v' => ?_⟩
    · by_cases hv' : v' = v
      · subst hv'
        show InN (X.B.I.ε v') (PtRepPf.frU X u v').e (PtRepPf.frU X u v').z (Formalism.MainNotions.S.uMat (s v'))
        rw [hsv]
        exact Bridge.inN_conj (uMat_unitary (h v')) hHHi hHiH hHe hHz (Bridge.inN_Q hTr hρ1)
      · show InN _ _ _ (Formalism.MainNotions.S.uMat (s v'))
        rw [hso v' hv', huone]
        exact inN_one _ _
    · by_cases hv' : v' = v
      · subst hv'
        show InN (X.B.I.ε v') (PtRepPf.frU X u' v').e (PtRepPf.frU X u' v').z
          (Formalism.MainNotions.S.uMat ((gamW X u u' w) v')⁻¹ * Formalism.MainNotions.S.uMat (s v') * Formalism.MainNotions.S.uMat ((gamW X u u' w) v'))
        rw [hsv, hkey]
        exact Bridge.inN_conj (uMat_unitary (h' v')) (uMat_mul_inv (h' v')) (uMat_inv_mul (h' v')) hH'e hH'z
          (Bridge.inN_Q hTr' hρ2)
      · show InN _ _ _ (Formalism.MainNotions.S.uMat ((gamW X u u' w) v')⁻¹ * Formalism.MainNotions.S.uMat (s v') *
          Formalism.MainNotions.S.uMat ((gamW X u u' w) v'))
        rw [hso v' hv', huone, Matrix.mul_one, uMat_inv_mul]
        exact inN_one _ _
  have hR := hSR w hw s hs
  have hp1 : psiU X u s = Formalism.QuantumDeterminants.psi D.R.k D.R.rS (Qim *ᵥ rv X.B.I v (X.zR u)) Formalism.QuantumDeterminants.cStd ρ := by
    unfold psiU psiInf
    rw [Finset.prod_eq_single v (fun v' _ hv' => by rw [hso v' hv', huone]; exact psiR_one' X v' u gg)
      (fun h0 => absurd (Finset.mem_univ v) h0)]
    show psiR (X.B.I.ε v) gg (PtRepPf.frU X u v).e (PtRepPf.frU X u v).fd (PtRepPf.frU X u v).z
      (Formalism.MainNotions.S.uMat (s v)) = _
    rw [hsv, Bridge.psiR_conj (uMat_unitary (h v)) hHiH hHe hHf hHz gg, Bridge.psiR_Q hTr gg hgg0 hc hκ ρ]
    rfl
  have hp2 : psiU X u' ((gamW X u u' w)⁻¹ * s * gamW X u u' w) =
      Formalism.QuantumDeterminants.psi D.R.k D.R.rS (Qim *ᵥ rv X.B.I v (X.zR u')) Formalism.QuantumDeterminants.cStd (Qim * Ai * Qm * ρ * (Qim * A * Qm)) := by
    unfold psiU psiInf
    rw [Finset.prod_eq_single v (fun v' _ hv' => by
        show psiR _ gg _ _ _ (Formalism.MainNotions.S.uMat ((gamW X u u' w) v')⁻¹ * Formalism.MainNotions.S.uMat (s v') *
          Formalism.MainNotions.S.uMat ((gamW X u u' w) v')) = 1
        rw [hso v' hv', huone, Matrix.mul_one, uMat_inv_mul]; exact psiR_one' X v' u' gg)
      (fun h0 => absurd (Finset.mem_univ v) h0)]
    show psiR (X.B.I.ε v) gg (PtRepPf.frU X u' v).e (PtRepPf.frU X u' v).fd (PtRepPf.frU X u' v).z
      (Gi * Formalism.MainNotions.S.uMat (s v) * G) = _
    rw [hsv, hkey, Bridge.psiR_conj (uMat_unitary (h' v)) (uMat_inv_mul (h' v)) hH'e hH'f hH'z gg,
      Bridge.psiR_Q hTr' gg hgg0 hc hκ]
    rfl
  rw [hp1, hp2] at hR
  calc Formalism.QuantumDeterminants.psi D.R.k D.R.rS (Qim *ᵥ rv X.B.I v (X.zR u)) Formalism.QuantumDeterminants.cStd ρ
      = Formalism.QuantumDeterminants.psi D.R.k D.R.rS (Qim *ᵥ rv X.B.I v (X.zR u)) Formalism.QuantumDeterminants.cStd ρ *
          (star (Formalism.QuantumDeterminants.psi D.R.k D.R.rS (Qim *ᵥ rv X.B.I v (X.zR u')) Formalism.QuantumDeterminants.cStd
            (Qim * Ai * Qm * ρ * (Qim * A * Qm))) *
          Formalism.QuantumDeterminants.psi D.R.k D.R.rS (Qim *ᵥ rv X.B.I v (X.zR u')) Formalism.QuantumDeterminants.cStd
            (Qim * Ai * Qm * ρ * (Qim * A * Qm))) := by rw [psi_norm, mul_one]
    _ = _ := by rw [← mul_assoc, hR, one_mul]

end Formalism.L2.SG.Pf.Carrier
