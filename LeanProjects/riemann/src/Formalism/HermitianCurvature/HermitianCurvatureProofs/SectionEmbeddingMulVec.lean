import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPolyRadialCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTWNeAlgSt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCLineNonzero

open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW

noncomputable section

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

theorem eb_intertwine {k r m : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {y z z' : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (h : IsFrameOf k r [y, z'] Bs)
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (hR : IsRepW k r z π) (hR' : IsRepW k r z' π')
    {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (hgB : IsFrameOf k r [z] (fun a => g *ᵥ Bs a)) (A : Wq →L[ℂ] Wp)
    (hint : ∀ h' ∈ UWset k r z', h' *ᵥ y = y → ∀ v, A (π' h' v) = π (g * h' * g⁻¹) (A v)) (a b : Fin m) (v : Wq) :
    A (EB π' Bs a b v) = EB π (fun a => g *ᵥ Bs a) a b (A v) := by
  have hB' : IsFrameOf k r [z'] Bs := Qx8.frame_sub h (by simp)
  have l' := QrD.frame_lie hB' a b
  have l := QrD.frame_lie hgB a b
  show A (QrD.ecOp π' _ v) = QrD.ecOp π _ (A v)
  rw [← QrD.ecRep_eq hR'.1 hR'.2 l'.1 l'.2, ← QrD.ecRep_eq hR.1 hR.2 l.1 l.2]
  have hU := Qx8.frame_InU h (z := z') (by simp) a b
  have hky := Qx8.hpart_kill Bs a b (Qx8.frame_orth h (v := y) (by simp))
  have hc := Qx8.hpart_conj Bs a b hg
  show A (dRep π' _ v + Complex.I • dRep π' _ v) = dRep π _ (A v) + Complex.I • dRep π _ (A v)
  rw [map_add, map_smul, hc.1, hc.2]
  congr 1
  · refine Qx8.dRep_intertwine A (Qx8.rep_hasDeriv hR'.1 hR'.2 hU.1 v) fun t => ?_
    rw [Qx8.exp_conj_uh hg]
    exact hint _ (hU.1 t) (Qx8.exp_fix hky.1 t) v
  · congr 1
    refine Qx8.dRep_intertwine A (Qx8.rep_hasDeriv hR'.1 hR'.2 hU.2 v) fun t => ?_
    rw [Qx8.exp_conj_uh hg]
    exact hint _ (hU.2 t) (Qx8.exp_fix hky.2 t) v

theorem hyp_snoc {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {n r : ℕ}
    {z e : Fin (2 * r + (n + 1) + 1) → ℂ} {π : Mx (n + 1) r → (W →L[ℂ] W)} {u : ℕ → ℝ} {β : ℂ}
    {L : Fin (n + 1) → ℤ} (hz : inWb (n + 1) r z) (hT : 0 < Tz (n + 1) r z) (hty : IsType (n + 1) r z π u)
    (hL : StrictAnti L)
    (hu : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ))
    (he : inWb (n + 1) r e) (hez : herm (Hpk (n + 1) r) e z = 0) (hee : herm (Hpk (n + 1) r) e e = 1)
    {Bs₀ : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ} (hB₀ : IsFrameOf (n + 1) r [z, e] Bs₀) :
    Hyp (EB π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e)) β L := by
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  obtain ⟨hgl, hq⟩ := frame_general_linear W (n + 1) r (n + 1) z π Bs₁ hR hB₁
  refine ⟨hgl, ⟨hnt, fun S hS => hirr S (lie_stabilizer W (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
  intro w v
  rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
  congr 1
  unfold cpol shf
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← hu j]
  ring

theorem labels2 {n r : ℕ} {T T' : ℝ} {u u' : ℕ → ℝ} (hOK : (⟨n + 1, r, T, T', u, u'⟩ : M.Par).OK)
    (ρ : M.Ty ⟨n + 1, r, T, T', u, u'⟩) (L L' : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hL' : ∀ j : Fin (n + 1), u' ((j : ℕ) + 1) - u 1 = (L' j : ℝ)) (lab : Fin n → ℤ)
    (hlab : ∀ j : Fin n, (lab j : ℝ) = M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) - u 1 + 1 / 2) :
    Box L lab ∧ Box L' lab ∧
      ∀ Y : ℂ, cpol (shf ((u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) lab) (Y + (((n + 1 : ℕ) : ℂ) - 2) / 2) =
        Formalism.FourierDecayAlt.M.xC ⟨n + 1, r, T, T', u, u'⟩ ρ Y := by
  have hmem : ∀ j : Fin n, (j : ℕ) + 1 ∈ Finset.Icc 1 ((⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩
  have hI := types_interlace _ hOK ρ
  have hI' : ∀ j : Fin n, M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u ((j : ℕ) + 1) ∧
      M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u' ((j : ℕ) + 1) ∧ u ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) ∧
      u' ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) := fun j => hI _ (hmem j)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have h1 := hL j.succ
    have h2 := hL j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hlab j
    constructor
    · have : (L j.succ : ℝ) < (lab j : ℝ) := by linarith
      exact_mod_cast this
    · have : (lab j : ℝ) ≤ (L j.castSucc : ℝ) := by linarith
      exact_mod_cast this
  · intro j
    have h1 := hL' j.succ
    have h2 := hL' j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hlab j
    constructor
    · have : (L' j.succ : ℝ) < (lab j : ℝ) := by linarith
      exact_mod_cast this
    · have : (lab j : ℝ) ≤ (L' j.castSucc : ℝ) := by linarith
      exact_mod_cast this
  · intro Y
    unfold M.xC cpol
    rw [show (⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1 = n from rfl, ProductIntervalFrames.prod_Icc_one]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h4 : (lab j : ℂ) = (M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) + 1 / 2 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) (hlab j)
      push_cast at this
      exact this
    simp only [shf]
    rw [h4]
    push_cast
    ring

section io

variable {k r : ℕ}

theorem section_embedding_mul_vec (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ)
    (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.io0 k r z z' μsec ζ *ᵥ v = NF.muZ k r μsec ζ *ᵥ (SSn.prWv k r z' v -
      herm (Hpk k r) (SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) • SSn.nu0' k r z z' μsec ζ) := by
  set ν := SSn.nu0' k r z z' μsec ζ with hν
  let f : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    { toFun := fun v => NF.muZ k r μsec ζ *ᵥ (SSn.prWv k r z' v - herm (Hpk k r) (SSn.prWv k r z' v) ν • ν)
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add, TF.prWv_add, DU.hadd_l, add_smul]
        congr 1
        abel
      map_smul' := fun c x => by
        rw [TF.prWv_smul, DU.hsmul_l, RingHom.id_apply, ← Matrix.mulVec_smul, smul_sub, smul_smul] }
  have e : SSn.io0 k r z z' μsec ζ = LinearMap.toMatrix' f := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl
  rw [e, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

end io

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
