import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefTraceCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def zc (k r : ℕ) (φ : ℝ) : Q.Mx k r :=
  B2.embWb k r (Complex.exp ((φ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))

def dOne (k : ℕ) (φ : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j = Fin.last k then 1 else Complex.exp ((φ : ℂ) * Complex.I)

def dTwo (k : ℕ) (φ : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j = 0 then Complex.exp ((φ : ℂ) * Complex.I) else 1

def hL (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (φ : ℝ) : Q.Mx k r :=
  B2.embWb k r (TheSec.gA k (wbPart k r z) (Tz k r z) * dOne k φ * (TheSec.gA k (wbPart k r z) (Tz k r z))⁻¹)

def hR (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (φ : ℝ) : Q.Mx k r :=
  B2.embWb k r ((TheSec.gB k (wbPart k r z') (Tz k r z'))⁻¹ * dTwo k φ * TheSec.gB k (wbPart k r z') (Tz k r z'))

def rotM {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)) (E : M.Ty P → (Wq →L[ℂ] Wp))
    (φ : ℝ) (ρ ρ' : M.Ty P) : ℂ :=
  inner ℂ (B.hsVec (E ρ)) (B.hsVec ((π (hL P.k P.r z φ)).comp ((E ρ').comp (π' (hR P.k P.r z' φ)))))

def GTRRotK : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → (∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ') →
    ∀ (Rt : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (s : ℤ),
      (∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), Rt ((d.κ f).1 Φ) = (d.κ f).1 (Rt Φ)) →
      (∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Rt Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) →
      ∀ ρ : M.Ty P, ∃ m : ℤ, ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
        trR P Bs e (Rt Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
          fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + ((m : ℂ)) • trR P Bs e Φ ρ

def GTRRCentre : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (Φ : Q.RadSp k r z z' π π'), ∀ x ∈ Q.DomR k r z z',
      HasDerivAt (fun φ : ℝ => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 (x.2 * zc k r φ))
        (Complex.I • ∑ a : Fin (Q.mdim k r (Fin.last r)),
          Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) a) ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1) x.2) 0

def GTRRSec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    (∀ φ : ℝ, hL k r z φ ∈ UWset k r z ∧ hR k r z' φ ∈ UWset k r z') ∧
    (hL k r z 0 = 1 ∧ hR k r z' 0 = 1 ∧ hL k r z (2 * Real.pi) = 1 ∧ hR k r z' (2 * Real.pi) = 1) ∧
    (∀ φ ψ : ℝ, hL k r z (φ + ψ) = hL k r z φ * hL k r z ψ ∧ hR k r z' (φ + ψ) = hR k r z' φ * hR k r z' ψ) ∧
    (∀ φ : ℝ, ∀ g ∈ UWset k r z', zc k r φ * g = g * zc k r φ) ∧
    ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ → ∀ φ : ℝ,
      NF.muZ k r (TheSec.theSection k r z z') ζ * zc k r φ =
        hL k r z φ * NF.muZ k r (TheSec.theSection k r z z') (ζ * Complex.exp ((φ : ℂ) * Complex.I)) * hR k r z' φ ∧
      ∀ c : Fin r → ℂ, c ∈ OmX r → (c, NF.muZ k r (TheSec.theSection k r z z') ζ * zc k r φ) ∈ Q.DomR k r z z'

def GTRRODE : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Mf : ℝ → Matrix ι ι ℂ) (Bm : Matrix ι ι ℂ),
    Mf 0 = 1 → (∀ φ ψ : ℝ, Mf (φ + ψ) = Mf φ * Mf ψ) → Mf (2 * Real.pi) = 1 →
    (∀ i j, HasDerivAt (fun φ => Mf φ i j) (Bm i j) 0) → (∀ i j, i ≠ j → Bm i j = 0) →
    ∃ n : ι → ℤ, ∀ (φ : ℝ) (i j : ι), Mf φ i j = if i = j then Complex.exp ((n i : ℂ) * (φ : ℂ) * Complex.I) else 0

def GTRRWirt : Prop :=
  ∀ (r : ℕ) (u : MA.E r → ℂ) (x : MA.E r), DifferentiableAt ℝ u x →
    HasDerivAt (fun φ : ℝ => u (x.1, x.2 * Complex.exp ((φ : ℂ) * Complex.I)))
      (Complex.I * (x.2 * MA.wirt M.vz u x - star x.2 * MA.wirt M.vzb u x)) 0

def GTRRMat : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → (∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ') →
    ∀ (Rt : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (s : ℤ),
      (∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), Rt ((d.κ f).1 Φ) = (d.κ f).1 (Rt Φ)) →
      (∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Rt Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) →
      ∃ n : M.Ty P → ℤ, ∀ (φ : ℝ) (ρ ρ' : M.Ty P),
        rotM P Bs.z Bs.z' Bs.π Bs.π' (fun σ => e σ 0) φ ρ ρ' =
          if ρ = ρ' then Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) else 0

def GTRRMatFrom : Prop := GTRRCentre → GTRRSec → GTRRODE → GTRRMat

def GTRRFin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → (∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ') →
    ∀ n : M.Ty P → ℤ, (∀ (φ : ℝ) (ρ ρ' : M.Ty P),
        rotM P Bs.z Bs.z' Bs.π Bs.π' (fun σ => e σ 0) φ ρ ρ' =
          if ρ = ρ' then Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) else 0) →
    ∀ (Rt : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (s : ℤ),
      (∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Rt Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) →
      ∀ (ρ : M.Ty P) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
        trR P Bs e (Rt Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
          fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + (((n ρ + s : ℤ) : ℂ)) • trR P Bs e Φ ρ

def GTRRFinFrom : Prop := GTRRCentre → GTRRSec → GTRRWirt → GTRRFin

theorem gTRRotK_of_mat_fin_centre_sec_ode_wirt (hM : GTRRMatFrom) (hF : GTRRFinFrom) (hC : GTRRCentre) (hS : GTRRSec) (hO : GTRRODE)
    (hW : GTRRWirt) : GTRRotK := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp hsec e he hk hc Rt s hRK hRt ρ
  obtain ⟨n, hn⟩ := hM hC hS hO Wp Wq P Bs X d hyp hsec e he hk hc Rt s hRK hRt
  exact ⟨n ρ + s, fun Φ => hF hC hS hW Wp Wq P Bs hyp.1 hyp.2.1 hsec e he hc n hn Rt s hRt ρ Φ⟩

theorem thetaNF_commute_kap (P : M.Par) {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜)
    (hR : d.Rel) (f : M.Ty P → ℂ) : Commute (d.κ f) (ThetaNF P d) := by
  have hfn : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hz : Commute (d.κ f) d.L.ζ := hfn _ (by simp [R.LevelData.fns])
  have hzb : Commute (d.κ f) d.L.ζb := hfn _ (by simp [R.LevelData.fns])
  have hGi : Commute (d.κ f) d.L.GGi := hfn _ (by simp [R.LevelData.fns])
  have hn : Commute (d.κ f) d.L.nab := hR.2.1 f _ (Or.inr (by simp))
  have hns : Commute (d.κ f) d.L.nabs := hR.2.1 f _ (Or.inr (by simp))
  have hkk : ∀ g : M.Ty P → ℂ, Commute (d.κ f) (d.κ g) := fun g => by
    show d.κ f * d.κ g = d.κ g * d.κ f
    rw [← map_mul, ← map_mul, mul_comm]
  unfold ThetaNF
  exact (((hz.mul_right hn).add_right (hzb.mul_right hns)).add_right (hkk _)).add_right
    (((Algebra.commute_algebraMap_right _ _).mul_right hGi).mul_right (hkk _))

def GTCRefTraceOfCutK : Prop :=
  GTRMove → GTRConst → GTRTopNF → GTRTopAct → GTRRotK → GTRInt → GTRTrans → GTCReal → GTCRefTrace

theorem gTCRefTrace_of_cutK : GTCRefTraceOfCutK := by
  intro hMove hConst hNF hAct hRot hInt hTrans hReal Wp Wq _ _ _ _ _ _ P Bs X d hyp
  obtain ⟨hpl, hk, hcs, hL, hS, hR, hQ⟩ := hyp
  have hcs0 := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  set Bs0 := BsAt P Bs (TheSec.theSection P.k P.r Bs.z Bs.z') hcs0.1 with hBs0
  have hyp0 : GTHyp P Bs0 X d := ⟨hpl, hk, hcs0, hL, hS, hR, hQ⟩
  obtain ⟨e0, he0, hk0, hc0⟩ := hConst Wp Wq P Bs0 X d hyp0
  obtain ⟨A, B, hAB, hC⟩ := gauge_locality_holds Wp Wq P Bs0 X d hyp0 e0 he0 hk0

  obtain ⟨cA, hcA, sA, hsA⟩ := hAct Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk X
  have hTT : d.L.TT = ((P.TT : ℝ) : ℂ) := by
    rw [hL.2.2.2.2.2.2.2.2.2.2.2.2, hpl.2.2.2.1, hpl.2.2.2.2.1]
    rfl
  obtain ⟨cN, hcN, sN, hsN⟩ := hNF P _ d hpl.1 hk hS hR hTT
  have hcoef : ∀ Y : ℂ, ∑ j ∈ Finset.range (P.k + 2), Y ^ j • cA j =
      ∑ j ∈ Finset.range (P.k + 2), Y ^ j • (cN j).1 := by
    intro Y
    rw [← hcA Y]
    have h1 : X.t Y 0 0 = (X.QQ Y 0 0).1 := rfl
    rw [h1, hQ Y, hcN Y, pr_fst_sum]
    exact Finset.sum_congr rfl fun j _ => pr_fst_smul _ _
  have hk' := poly_coeff_eq (P.k + 2) cA (fun j => (cN j).1) hcoef P.k (by omega)
  have hTh : (ThetaNF P d).1 = cA P.k - ((sN : ℂ)) • (1 : Module.End ℂ _) := by
    rw [hk']
    show (ThetaNF P d).1 = (cN P.k).1 - _
    rw [hsN, pr_fst_add, pr_fst_smul, pr_fst_one, add_sub_cancel_right]
  have hpt : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      (((ThetaNF P d).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
          Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
            ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
          (((sA - sN : ℤ) : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    intro Φ x hx
    rw [hTh, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sub,
      Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, hsA Φ x hx]
    push_cast
    rw [sub_smul]
    abel
  obtain ⟨e, he, htr⟩ := hMove Wp Wq P Bs hpl hk _ hcs0.1 e0 he0
  have htrF : trR P Bs e = trR P Bs0 e0 := funext htr
  refine ⟨e, he, ?_, A, B, hAB, ?_, fun ρ => ?_⟩
  · intro f Φ
    rw [htrF]
    exact hk0 f Φ
  · intro Φ ρ
    rw [htrF]
    exact hC Φ ρ
  · obtain ⟨m, hm⟩ := hRot Wp Wq P Bs0 X d hyp0 rfl e0 he0 hk0 hc0 (ThetaNF P d).1 (sA - sN)
      (fun f Φ =>
        (congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs0.z Bs0.z' Bs0.π Bs0.π') => x.1 Φ)
          (thetaNF_commute_kap P d hR f).eq).symm) hpt ρ
    obtain ⟨N, hN⟩ := hInt Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk ρ
    refine ⟨N - m, fun ζ hζ => ?_⟩
    have hT := hTrans Wp Wq P Bs0 X d hyp0 e0 he0 hk0 A B hAB hC ρ (m : ℂ) hm ζ hζ
    rw [hReal Wp Wq P Bs0 X d hyp0 e0 he0 hk0 A B hAB hC ρ ζ hζ] at hT
    exact final_arith P ρ (A ρ ζ) ζ hζ m N hN hT

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
