import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThtAdapted
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTWNeAlg

open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

theorem core (hAlg : TW.TWNeAlg) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (n r : ℕ) (T T' : ℝ) (u u' : ℕ → ℝ) (Bs : B.RealPlaceData (n + 1) r Wp Wq)
    (hpl : IsPlace ⟨n + 1, r, T, T', u, u'⟩ Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ n + 1)
    (Pr : M.Ty ⟨n + 1, r, T, T', u, u'⟩ → (Fin (2 * r + (n + 1) + 1) → ℂ) → (Wp →L[ℂ] Wp))
    (hPr : PRho.PRhoSpec ⟨n + 1, r, T, T', u, u'⟩ Bs.z Bs.π Pr)
    (Bw Bw' : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ) (hBw : IsFrameOf (n + 1) r [Bs.z] Bw)
    (hBw' : IsFrameOf (n + 1) r [Bs.z'] Bw') (l : ℕ) (hl : l ∈ Finset.Icc 1 n)
    (π ρ : M.Ty ⟨n + 1, r, T, T', u, u'⟩) (hUp : M.Up ⟨n + 1, r, T, T', u, u'⟩ l π ρ) (ζ : ℂ)
    (hζT : T * T' < Complex.normSq ζ) (Xf : Wq →L[ℂ] Wp)
    (hXf : Xf ∈ NF.Fib (n + 1) r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ)
    (hfix : (Pr π (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf) (hX0 : Xf ≠ 0) :
    (Pr ρ (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ)).comp (tht (n + 1) r Bs.z Bs.z' Bs.π Bs.π' Bw Bw'
      (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ) (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ)
      (SSn.io0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ) Xf) ≠ 0 := by
  have hOK : (⟨n + 1, r, T, T', u, u'⟩ : M.Par).OK := hpl.1
  have hz : inWb (n + 1) r Bs.z := Bs.z_mem
  have hz' : inWb (n + 1) r Bs.z' := Bs.z'_mem
  have hTz : Tz (n + 1) r Bs.z = T := hpl.2.2.2.1
  have hTz' : Tz (n + 1) r Bs.z' = T' := hpl.2.2.2.2.1
  have hπ : IsType (n + 1) r Bs.z Bs.π u := hpl.2.2.2.2.2.1
  have hπ' : IsType (n + 1) r Bs.z' Bs.π' u' := hpl.2.2.2.2.2.2
  have hζ' : Tz (n + 1) r Bs.z * Tz (n + 1) r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT : 0 < Tz (n + 1) r Bs.z := Bs.T_pos
  have hT' : 0 < Tz (n + 1) r Bs.z' := Bs.T'_pos
  have hR : IsRepW (n + 1) r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  have hR' : IsRepW (n + 1) r Bs.z' Bs.π' := ⟨Bs.π'_rep, Bs.π'_cont⟩
  obtain ⟨hνfix, hνν, hν'fix, hν'ν'⟩ := DU.base hz hz' hT hT' Bs.sec hζ'
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hU : NF.muZ (n + 1) r Bs.μsec ζ ∈ UH (Hpk (n + 1) r) := hG.1
  have hmm : NF.muZ (n + 1) r Bs.μsec ζ * (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ = 1 := Gauge.GC.KLAM.mul_inv_uh hU
  have hy : inWb (n + 1) r (NF.muZ (n + 1) r Bs.μsec ζ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb (n + 1) r (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ) := by
    show inWb (n + 1) r (SSn.unitH (n + 1) r (SSn.prWv (n + 1) r Bs.z (NF.muZ (n + 1) r Bs.μsec ζ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk (n + 1) r) (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ) Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  obtain ⟨Fr, hFr⟩ := exists_frame_two n r Bs.z _ hz hT hνW hνz hνν
  have hFr' : IsFrameOf (n + 1) r [(NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z']
      (fun a => (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Fr a) :=
    (PRho.GL.gauge_left_line_holds Wp Wq ⟨n + 1, r, T, T', u, u'⟩ Bs hpl hk ζ hζT Fr hFr).1
  obtain ⟨hν'W, hν'z, hFr2⟩ := TW.nu0'_facts Bs hζ' hFr'
  have hB₁ := FrameExtension.frame_snoc hFr hνW hνz hνν
  set μ := NF.muZ (n + 1) r Bs.μsec ζ with hμ
  set ν := SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ with hν
  set ν' := SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ with hν'

  have hIcc : ∀ j : Fin (n + 1), (j : ℕ) + 1 ∈ Finset.Icc 1 (n + 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by omega⟩
  choose L hL using fun j : Fin (n + 1) => hOK.int_u ((j : ℕ) + 1) (hIcc j)
  choose L' hL' using fun j : Fin (n + 1) => hOK.int_u' ((j : ℕ) + 1) (hIcc j)
  have hL2 : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ) := hL
  have hL2' : ∀ j : Fin (n + 1), u' ((j : ℕ) + 1) - u 1 = (L' j : ℝ) := hL'
  have hgap : ∀ j : Fin n, max (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1)) + 1 / 2 ≤
      min (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1)) - 1 / 2 := fun j =>
    hOK.gap ((j : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩)
  have hanti : StrictAnti L := Fin.strictAnti_iff_succ_lt.2 fun j => by
    have h1 := hL2 j.castSucc
    have h2 := hL2 j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have h5 := le_max_left (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1))
    have h6 := min_le_left (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1))
    have : (L j.succ : ℝ) < (L j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  have hanti' : StrictAnti L' := Fin.strictAnti_iff_succ_lt.2 fun j => by
    have h1 := hL2' j.castSucc
    have h2 := hL2' j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have h5 := le_max_right (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1))
    have h6 := min_le_right (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1))
    have : (L' j.succ : ℝ) < (L' j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  set β : ℂ := (u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 with hβ
  have hrel : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ) := fun j => by
    have h : (u ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L j : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL2 j)
    rw [hβ, ← h]
    ring
  have hrel' : ∀ j : Fin (n + 1), (u' ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L' j : ℂ) := fun j => by
    have h : (u' ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L' j : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL2' j)
    rw [hβ, ← h]
    ring

  have hmem : ∀ j : Fin n, (j : ℕ) + 1 ∈ Finset.Icc 1 ((⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩
  choose N hN using fun j : Fin n => Qx8.rho_int hOK π ((j : ℕ) + 1) (hmem j)
  have hl' := Finset.mem_Icc.1 hl
  have hln : l - 1 < n := by omega
  set i₀ : Fin n := ⟨l - 1, hln⟩ with hi₀
  set Mπ : Fin n → ℤ := fun j => N j + 1 with hMπ
  have hlabπ : ∀ j : Fin n, (Mπ j : ℝ) = M.rho ⟨n + 1, r, T, T', u, u'⟩ π ((j : ℕ) + 1) - u 1 + 1 / 2 := fun j => by
    have := hN j
    change M.rho ⟨n + 1, r, T, T', u, u'⟩ π ((j : ℕ) + 1) - u 1 - 1 / 2 = (N j : ℝ) at this
    rw [hMπ]
    push_cast
    linarith
  have hlabρ : ∀ j : Fin n, ((Function.update Mπ i₀ (Mπ i₀ + 1) j : ℤ) : ℝ) =
      M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) - u 1 + 1 / 2 := fun j => by
    rw [rho_raise _ l π ρ hUp _ (hmem j)]
    by_cases hj : j = i₀
    · subst hj
      have e : ((i₀ : Fin n) : ℕ) + 1 = l := by rw [hi₀]; show l - 1 + 1 = l; omega
      rw [Function.update_self, if_pos e]
      push_cast
      rw [hlabπ i₀]
      ring
    · have e : ¬ ((j : ℕ) + 1 = l) := fun h => hj (Fin.ext (by rw [hi₀]; show (j : ℕ) = l - 1; omega))
      rw [Function.update_of_ne hj, if_neg e, hlabπ j]
      ring
  obtain ⟨hbπ, hbπ', hcpπ⟩ := TW.labels2 hOK π L L' hL2 hL2' Mπ hlabπ
  obtain ⟨hbρ, hbρ', hcpρ⟩ := TW.labels2 hOK ρ L L' hL2 hL2' _ hlabρ

  have hH := TW.hyp_snoc hz hT hπ hanti hrel hνW hνz hνν hFr
  have hH' := TW.hyp_snoc hz' hT' hπ' hanti' hrel' hν'W hν'z hν'ν' hFr2
  have hsub : subA (EB Bs.π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr ν)) = EB Bs.π Fr :=
    FrameExtension.subA_EB Bs.π Fr ν
  have hsub' : subA (EB Bs.π' (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) (fun a => μ⁻¹ *ᵥ Fr a) ν')) =
      EB Bs.π' (fun a => μ⁻¹ *ᵥ Fr a) := FrameExtension.subA_EB Bs.π' _ ν'
  have hq := (frame_general_linear Wp (n + 1) r n Bs.z Bs.π Fr hR (FrameExtension.frame_weaken hFr)).2
  have hback : (fun a => μ *ᵥ (μ⁻¹ *ᵥ Fr a)) = Fr := by
    funext a
    rw [Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
  have hXF : Xf ∈ Gauge.GC.FibAt (n + 1) r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hXf (h, h') ⟨hh, hh', he⟩
  have hpos : 0 < PRho.nrmW (n + 1) r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp
  have hrange : ∀ (σ : M.Ty ⟨n + 1, r, T, T', u, u'⟩) (x : Wp), Pr σ ν x = x ↔
      ∀ Fr2 : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ, IsFrameOf (n + 1) r [Bs.z, SSn.prWv (n + 1) r Bs.z ν] Fr2 →
        ∀ w : ℂ, capRep (n + 1) r Bs.π Fr2 w x =
          M.xC ⟨n + 1, r, T, T', u, u'⟩ σ (w - (((n + 1 : ℕ) : ℂ) - 2) / 2) • x := (hPr.2.2 ν hpos).2.2.2
  have hJi : ∀ (a b : Fin n) (v : Wq), (Xf : Wq →ₗ[ℂ] Wp)
      (subA (EB Bs.π' (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) (fun a => μ⁻¹ *ᵥ Fr a) ν')) a b v) =
      subA (EB Bs.π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr ν)) a b ((Xf : Wq →ₗ[ℂ] Wp) v) := by
    intro a b v
    rw [hsub, hsub']
    have h := TW.eb_intertwine hFr' hR hR' hU (by rw [hback]; exact FrameExtension.frame_weaken hFr) Xf
      (fun h' hh' hy' w => Gauge.GC.KLAM.fib_intertwine Bs.π_rep hG hXF hh' hy' w) a b v
    rw [hback] at h
    exact h
  have hJr : ∀ v : Wq, (Xf : Wq →ₗ[ℂ] Wp) v ∈
      CapSp (subA (EB Bs.π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr ν))) (shf β Mπ) := by
    intro v
    rw [hsub, mem_CapSp]
    intro w
    have h1 : Pr π ν (Xf v) = Xf v := by
      have := congrArg (fun A : Wq →L[ℂ] Wp => A v) hfix
      exact this
    have h2 := (hrange π (Xf v)).1 h1 Fr (by rw [hνfix]; exact hFr) w
    have h3 := hcpπ (w - (((n + 1 : ℕ) : ℂ) - 2) / 2)
    rw [sub_add_cancel] at h3
    show qdet (EB Bs.π Fr) w (Xf v) = _
    rw [← hq w (Xf v), h3]
    exact h2
  have hJ0 : (Xf : Wq →ₗ[ℂ] Wp) ≠ 0 := fun h => hX0 (by
    ext v
    exact LinearMap.congr_fun h v)
  obtain ⟨v', hne, hmemW⟩ := hAlg Wp Wq n _ _ β β L L' Mπ Mπ i₀ hH hH' hbπ hbπ' hbρ hbρ' rfl
    (Xf : Wq →ₗ[ℂ] Wp) hJ0 hJi hJr
  intro h0
  apply hne
  have h1 := congrArg (fun A : Wq →L[ℂ] Wp => A v') h0
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at h1
  rw [TW.tht_adapted Bs hζ' hBw hBw' hB₁ hFr' Xf v'] at h1
  rw [← h1]
  symm
  refine (hrange ρ _).2 ?_
  intro Fr2 hFr2 w
  rw [hνfix] at hFr2
  rw [hsub, mem_CapSp] at hmemW
  have h3 := hcpρ (w - (((n + 1 : ℕ) : ℂ) - 2) / 2)
  rw [sub_add_cancel] at h3
  rw [Topx1.typ_frame_change (n + 1) r (by omega) Bs.z ν Bs.π Fr2 Fr hz hT hνW hνz hνν hR hFr2 hFr w _, hq w _]
  refine (hmemW w).trans ?_
  rw [h3]
  rfl

theorem tWNe_of_alg (hAlg : TW.TWNeAlg) : TWNe := by
  intro Wp Wq _ _ _ _ _ _ P
  obtain ⟨k, r, T, T', u, u'⟩ := P
  rcases k with _ | n
  · intro Bs hpl hk
    exact absurd hk (by show ¬ (2 ≤ 0); omega)
  intro Bs hpl hk Pr hPr Bw Bw' hBw hBw' l hl π ρ hUp ζ hζ Xf hXf hfix hX0
  exact core hAlg n r T T' u u' Bs hpl hk Pr hPr Bw Bw' hBw hBw' l hl π ρ hUp ζ hζ Xf hXf hfix hX0

theorem word_nonvanishing_holds : TWNe := tWNe_of_alg TW.word_nonvanishing_algebraic

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
