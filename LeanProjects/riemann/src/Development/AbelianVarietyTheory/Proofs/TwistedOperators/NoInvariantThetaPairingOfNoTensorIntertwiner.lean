import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairingTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryImage

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.PairVanish

open GlobalTheory.ArchRec.PairTensor (ext_ctr exists_map)
open GlobalTheory.Chain.IoLift.UImg (sumAct sumMod sumAct_single)

variable {p q r s : ℕ} {T : GrpData p q} (R : DSRep T)

theorem ctr_map_right {U U' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
    (g : U →ₗ[ℂ] U') (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U' v (TensorProduct.map LinearMap.id g z) = g (ctr R U v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ctr_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_universal (M : GKMod r s) (a : Mat p q →ₗ[ℂ] Module.End ℂ M.V)
    (hc : ∀ Y Z, a Y * M.act Z = M.act Z * a Y) (U : Type) [AddCommGroup U] [Module ℂ U] :
    ∃ (Q : GKMod r s) (B₀ : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] Q.V), PInv a R B₀ ∧
      (∀ Z P v, B₀ (M.act Z P) v = Q.act Z (B₀ P v)) ∧
      ∀ P v, B₀ P v = 0 → ∀ B : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U, PInv a R B → B P v = 0 := by

  obtain ⟨G, hG⟩ : ∃ G : Set (R.HK.V →₀ M.V), G =
      {x | (∃ (P : M.V) (v w : R.HK.V),
          x = Finsupp.single (v + w) P - Finsupp.single v P - Finsupp.single w P) ∨
        (∃ (P : M.V) (v : R.HK.V) (c : ℂ),
          x = Finsupp.single (c • v) P - starRingEnd ℂ c • Finsupp.single v P) ∨
        ∃ (P : M.V) (v : R.HK.V) (Z : Mat p q),
          Z ∈ upq p q ∧ x = Finsupp.single v (a Z P) + Finsupp.single (R.HK.act Z v) P} := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Submodule ℂ (R.HK.V →₀ M.V), N = Submodule.span ℂ G := ⟨_, rfl⟩
  have hGN : ∀ x ∈ G, x ∈ N := fun x hx => hNdef ▸ Submodule.subset_span hx

  have hN : ∀ Z : Mat r s, N ≤ N.comap (sumAct M R.HK.V Z) := by
    intro Z
    conv_lhs => rw [hNdef]
    rw [Submodule.span_le]
    intro x hx
    rw [hG] at hx
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rcases hx with ⟨P, v, w, rfl⟩ | ⟨P, v, c, rfl⟩ | ⟨P, v, Y, hY, rfl⟩
    · refine hGN _ ?_
      rw [hG]
      exact Or.inl ⟨M.act Z P, v, w, by simp [sumAct_single]⟩
    · refine hGN _ ?_
      rw [hG]
      exact Or.inr (Or.inl ⟨M.act Z P, v, c, by simp [sumAct_single]⟩)
    · refine hGN _ ?_
      rw [hG]
      have hcomm : a Y (M.act Z P) = M.act Z (a Y P) := LinearMap.congr_fun (hc Y Z) P
      exact Or.inr (Or.inr ⟨M.act Z P, v, Y, hY, by simp [sumAct_single, hcomm]⟩)
  let actQ : Mat r s →ₗ[ℂ] Module.End ℂ ((R.HK.V →₀ M.V) ⧸ N) :=
    { toFun := fun Z => N.mapQ N (sumAct M R.HK.V Z) (hN Z)
      map_add' := fun Z Z' => by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp [Submodule.mapQ_apply]
      map_smul' := fun c Z => by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp [Submodule.mapQ_apply] }
  have hQ : ∀ Z y, actQ Z (Submodule.Quotient.mk y) = Submodule.Quotient.mk (sumAct M R.HK.V Z y) :=
    fun _ _ => rfl
  let Q : GKMod r s :=
    { V := (R.HK.V →₀ M.V) ⧸ N
      act := actQ
      lie := fun X Y => by
        have h : sumAct M R.HK.V (X * Y - Y * X) =
            sumAct M R.HK.V X * sumAct M R.HK.V Y - sumAct M R.HK.V Y * sumAct M R.HK.V X :=
          (sumMod M R.HK.V).lie X Y
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.sub_apply, Module.End.mul_apply, hQ]
        rw [h]
        simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.Quotient.mk_sub]
      kfin := fun x => by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
        obtain ⟨W, hW, hy, hK⟩ : ∃ W : Submodule ℂ (R.HK.V →₀ M.V), FiniteDimensional ℂ W ∧ y ∈ W ∧
            KStable (sumAct M R.HK.V) W := (sumMod M R.HK.V).kfin y
        refine ⟨W.map N.mkQ, Module.Finite.map W N.mkQ, Submodule.mem_map_of_mem hy, ?_⟩
        intro X hX w hw
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
        exact Submodule.mem_map_of_mem (hK X hX u hu)
      wts := fun x => by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
        have hy : y ∈ ⨆ μ : Ix r s → ℚ, wtSub (sumAct M R.HK.V) μ := (sumMod M R.HK.V).wts y
        have hle : (⨆ μ : Ix r s → ℚ, wtSub (sumAct M R.HK.V) μ).map N.mkQ ≤
            ⨆ μ : Ix r s → ℚ, wtSub actQ μ := by
          rw [Submodule.map_iSup]
          refine iSup_mono fun μ => ?_
          rw [Submodule.map_le_iff_le_comap]
          intro u hu
          rw [Submodule.mem_comap]
          simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker] at hu ⊢
          intro i
          have hi := hu i
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hi ⊢
          rw [Submodule.mkQ_apply, hQ, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, hi,
            Submodule.Quotient.mk_zero]
        exact hle (Submodule.mem_map_of_mem hy) }
  let B₀ : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] ((R.HK.V →₀ M.V) ⧸ N) :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P v => N.mkQ (Finsupp.single v P))
      (fun P P' v => by simp [Finsupp.single_add])
      (fun c P v => by
        simp only [RingHom.id_apply]
        rw [← Finsupp.smul_single, map_smul])
      (fun P v w => by
        rw [← map_add, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        refine hGN _ ?_
        rw [hG]
        exact Or.inl ⟨P, v, w, by abel⟩)
      (fun c P v => by
        rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        refine hGN _ ?_
        rw [hG]
        exact Or.inr (Or.inl ⟨P, v, c, rfl⟩))
  refine ⟨Q, B₀, ?_, ?_, ?_⟩
  · intro Z hZ P v
    show N.mkQ (Finsupp.single v (a Z P)) + N.mkQ (Finsupp.single (R.HK.act Z v) P) = 0
    rw [← map_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine hGN _ ?_
    rw [hG]
    exact Or.inr (Or.inr ⟨P, v, Z, hZ, rfl⟩)
  · intro Z P v
    show N.mkQ (Finsupp.single v (M.act Z P)) = actQ Z (N.mkQ (Finsupp.single v P))
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, hQ, sumAct_single]
  · intro P v h B hB
    let L : (R.HK.V →₀ M.V) →ₗ[ℂ] U := Finsupp.lsum ℂ fun w => B.flip w
    have hL : ∀ w (P' : M.V), L (Finsupp.single w P') = B P' w := by
      intro w P'
      simp [L]
    have hNL : N ≤ LinearMap.ker L := by
      rw [hNdef, Submodule.span_le]
      intro x hx
      rw [hG] at hx
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      rcases hx with ⟨P', w, w', rfl⟩ | ⟨P', w, c, rfl⟩ | ⟨P', w, Z, hZ, rfl⟩
      · simp [hL]
      · simp [hL]
      · rw [map_add, hL, hL]
        exact hB Z hZ P' w
    have h' : N.mkQ (Finsupp.single v P) = 0 := h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
    have := hNL h'
    rw [LinearMap.mem_ker, hL] at this
    exact this

theorem pairNo_of_tensNo : ∀ (p q r s : ℕ) (T₁ : GrpData p q) (σ : Type) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (R₁ : DSRep T₁), IsGK a₁ → IsGK a₂ → (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → AdmGK R₁.HK → TensNo a₁ a₂ R₁ → PairNo a₁ R₁ := by
  intro p q r s T₁ σ a₁ a₂ R₁ h₁ h₂ hc hA hT U _ _ B hB

  let M : GKMod r s :=
    { V := MvPolynomial σ ℂ
      act := a₂
      lie := h₂.1
      kfin := h₂.2.1
      wts := h₂.2.2 }
  obtain ⟨Q, B₀, hB₀, hZ, huniv⟩ := exists_universal R₁ M a₁ hc U
  obtain ⟨f, hf, hfB⟩ := GlobalTheory.ArchRec.PairTensor.exists_map R₁ a₁ h₁ hA B₀ hB₀
  have hT' : TIntw a₁ a₂ R₁.HK Q f := by
    refine ⟨hf, fun Y => LinearMap.ext fun P => ?_⟩
    refine GlobalTheory.ArchRec.PairTensor.ext_ctr R₁ Q.V _ _ fun v => ?_
    simp only [LinearMap.comp_apply]
    rw [← hfB, ctr_map_right, ← hfB]
    exact hZ Y P v
  have hf0 : f = 0 := hT Q f hT'
  refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  refine huniv P v ?_ B hB
  rw [hfB, hf0, LinearMap.zero_apply, map_zero]

end GlobalTheory.ArchRec.PairVanish
