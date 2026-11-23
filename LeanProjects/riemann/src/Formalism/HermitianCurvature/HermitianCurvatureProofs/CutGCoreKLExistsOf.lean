import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLineCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOfAlg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProductIntervalFrames

open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExOf

noncomputable section

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA

theorem side {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {n r : ℕ}
    {z e : Fin (2 * r + (n + 1) + 1) → ℂ} {π : Mx (n + 1) r → (W →L[ℂ] W)} {u : ℕ → ℝ} {β : ℂ}
    {L : Fin (n + 1) → ℤ} (hz : inWb (n + 1) r z) (hT : 0 < Tz (n + 1) r z) (hty : IsType (n + 1) r z π u)
    (hL : StrictAnti L)
    (hu : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ))
    (he : inWb (n + 1) r e) (hez : herm (Hpk (n + 1) r) e z = 0) (hee : herm (Hpk (n + 1) r) e e = 1)
    {Bs₀ : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ} (hB₀ : IsFrameOf (n + 1) r [z, e] Bs₀) :
    GlRel (EB π Bs₀) ∧ DirectSum.IsInternal (fun M : {M : Fin n → ℤ // Box L M} => CapSp (EB π Bs₀) (shf β M.1)) ∧
      ∀ M : {M : Fin n → ℤ // Box L M}, CapSp (EB π Bs₀) (shf β M.1) ≠ ⊥ ∧
        ∀ S' : Submodule ℂ W, S' ≤ CapSp (EB π Bs₀) (shf β M.1) → Stab (EB π Bs₀) S' →
          S' = ⊥ ∨ S' = CapSp (EB π Bs₀) (shf β M.1) := by
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  have hsub : subA (EB π Bs₁) = EB π Bs₀ := FrameExtension.subA_EB π Bs₀ e
  obtain ⟨hgl, hq⟩ := frame_general_linear W (n + 1) r (n + 1) z π Bs₁ hR hB₁
  have hH : Hyp (EB π Bs₁) β L := by
    refine ⟨hgl, ⟨hnt, fun S hS => hirr S (lie_stabilizer W (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
    intro w v
    rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [← hu j]
    ring
  obtain ⟨hint, hS⟩ := branching_algebraic W n (EB π Bs₁) β L hH
  rw [hsub] at hint hS
  exact ⟨(frame_general_linear W (n + 1) r n z π Bs₀ hR (FrameExtension.frame_weaken hB₀)).1, hint, hS⟩

theorem labels {n r : ℕ} {T T' : ℝ} {u u' : ℕ → ℝ} (hOK : (⟨n + 1, r, T, T', u, u'⟩ : M.Par).OK)
    (ρ : M.Ty ⟨n + 1, r, T, T', u, u'⟩) (L L' : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hL' : ∀ j : Fin (n + 1), u' ((j : ℕ) + 1) - u 1 = (L' j : ℝ)) :
    ∃ lab : Fin n → ℤ, Box L lab ∧ Box L' lab ∧
      SDec (shf ((u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) lab) ∧
      ∀ Y : ℂ, cpol (shf ((u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) lab) (Y + (((n + 1 : ℕ) : ℂ) - 2) / 2) =
        Formalism.FourierDecayAlt.M.xC ⟨n + 1, r, T, T', u, u'⟩ ρ Y := by
  have hmem : ∀ j : Fin n, (j : ℕ) + 1 ∈ Finset.Icc 1 ((⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩
  choose N hN using fun j : Fin n => Qx8.rho_int hOK ρ ((j : ℕ) + 1) (hmem j)
  have hN' : ∀ j : Fin n, M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) = (N j : ℝ) + u 1 + 1 / 2 := fun j => by
    have := hN j
    change M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) - u 1 - 1 / 2 = (N j : ℝ) at this
    linarith
  have hI := types_interlace _ hOK ρ
  have hI' : ∀ j : Fin n, M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u ((j : ℕ) + 1) ∧
      M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u' ((j : ℕ) + 1) ∧ u ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) ∧
      u' ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) := fun j => hI _ (hmem j)
  refine ⟨fun j => N j + 1, ?_, ?_, ?_, ?_⟩
  · intro j
    have h1 := hL j.succ
    have h2 := hL j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hN' j
    constructor
    · have : (L j.succ : ℝ) < ((N j + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((N j + 1 : ℤ) : ℝ) ≤ (L j.castSucc : ℝ) := by push_cast; linarith
      exact_mod_cast this
  · intro j
    have h1 := hL' j.succ
    have h2 := hL' j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hN' j
    constructor
    · have : (L' j.succ : ℝ) < ((N j + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((N j + 1 : ℤ) : ℝ) ≤ (L' j.castSucc : ℝ) := by push_cast; linarith
      exact_mod_cast this
  · intro a b hab
    have hlt := Qx8.rho_anti hOK ρ ((a : ℕ) + 1) ((b : ℕ) + 1) (by omega) (by simp only [Fin.lt_def] at hab; omega)
      (by show (b : ℕ) + 1 ≤ n + 1 - 1; omega)
    have ha := hN' a
    have hb := hN' b
    have hNab : N b < N a := by
      have : (N b : ℝ) < (N a : ℝ) := by linarith
      exact_mod_cast this
    refine ⟨(N a - N b - 1).toNat, ?_⟩
    have h1 : (((N a - N b - 1).toNat : ℕ) : ℤ) = N a - N b - 1 := Int.toNat_of_nonneg (by omega)
    have h2 : (((N a - N b - 1).toNat : ℕ) : ℂ) = ((N a - N b - 1 : ℤ) : ℂ) := by exact_mod_cast h1
    simp only [shf]
    rw [h2]
    push_cast
    ring
  · intro Y
    unfold M.xC cpol
    rw [show (⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1 = n from rfl, ProductIntervalFrames.prod_Icc_one]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h4 : (M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) : ℂ) = (N j : ℂ) + (u 1 : ℂ) + 1 / 2 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) (hN' j)
      push_cast at this
      exact this
    simp only [shf]
    rw [h4]
    push_cast
    ring

theorem lie_existence_of_iso_group : KLExistsOf := by
  intro hIso hLG Wp Wq _ _ _ _ _ _ P
  obtain ⟨k, r, T, T', u, u'⟩ := P
  intro z z' π π' hPl hk
  have hk' : 2 ≤ k := hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  intro g hg hGG Fr hFr ρ
  obtain ⟨hOK, hz, hz', hTz, hTz', hπ, hπ'⟩ := id hPl
  have hT : 0 < Tz (n + 1) r z := by
    have h2 : Tz (n + 1) r z = T := hTz
    rw [h2]; exact hOK.T_pos
  have hT' : 0 < Tz (n + 1) r z' := by
    have h2 : Tz (n + 1) r z' = T' := hTz'
    rw [h2]; exact hOK.T'_pos
  obtain ⟨-, hrep, hcont, -, -, -⟩ := id hπ
  obtain ⟨-, hrep', hcont', -, -, -⟩ := id hπ'
  obtain ⟨e', f, -, -, -, -, -, -, -, -, ⟨he'W, he'z, he'e⟩, ⟨hfW, hfz, hff⟩, hFr1, hFr2⟩ :=
    KLAM.geom_fr hz hz' hT hT' hg hGG hFr

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
  obtain ⟨M, hbox, hbox', hsd, hcp⟩ := labels hOK ρ L L' hL2 hL2'
  have hfin : Finite {M : Fin n → ℤ // Box L' M} := by
    refine Finite.of_injective (β := ∀ j : Fin n, Finset.Ioc (L' j.succ) (L' j.castSucc))
      (fun M j => ⟨M.1 j, Finset.mem_Ioc.2 (M.2 j)⟩) ?_
    intro M₁ M₂ h
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun h j)
  letI : Fintype {M : Fin n → ℤ // Box L' M} := Fintype.ofFinite _

  obtain ⟨hgl', hint', hS'⟩ := side hz' hT' hπ' hanti' hrel' he'W he'z he'e hFr1
  obtain ⟨hgl, -, hS⟩ := side hz hT hπ hanti hrel hfW hfz hff hFr2
  set Mb : {M : Fin n → ℤ // Box L M} := ⟨M, hbox⟩ with hMb
  set Mb' : {M : Fin n → ℤ // Box L' M} := ⟨M, hbox'⟩ with hMb'
  set E := EB π (fun a => g *ᵥ Fr a) with hE
  set E' := EB π' Fr with hE'
  have hstabs' : ∀ (j : {M : Fin n → ℤ // Box L' M}) (a b : Fin n), ∀ v ∈ CapSp E' (shf β j.1), E' a b v ∈ CapSp E' (shf β j.1) :=
    fun j a b => (capelli_stabilizer Wq n E' (shf β j.1) hgl').1 a b
  have hstab : Stab E (CapSp E (shf β M)) := (capelli_stabilizer Wp n E (shf β M) hgl).1
  have hstab' : Stab E' (CapSp E' (shf β M)) := (capelli_stabilizer Wq n E' (shf β M) hgl').1
  obtain ⟨A, hA0, hAi⟩ := hIso (CapSp E (shf β M)) (CapSp E' (shf β M)) n (resE E _ hstab) (resE E' _ hstab')
    (shf β M) (glRel_resE hgl _ hstab) (glRel_resE hgl' _ hstab') (irr_resE _ hstab (hS Mb).1 (hS Mb).2)
    (irr_resE _ hstab' (hS' Mb').1 (hS' Mb').2) hsd (cap_resE (shf β M) hstab) (cap_resE (shf β M) hstab')

  set p : Wq →ₗ[ℂ] CapSp E' (shf β M) := projI hint' Mb' with hp
  have hpE : ∀ a b v, p (E' a b v) = resE E' _ hstab' a b (p v) := fun a b v =>
    projI_comm hint' (E' a b) (fun j => hstabs' j a b) Mb' v
  set Xl : Wq →ₗ[ℂ] Wp := (CapSp E (shf β M)).subtype ∘ₗ (A ∘ₗ p) with hXl
  set X : Wq →L[ℂ] Wp := LinearMap.toContinuousLinearMap Xl with hX
  have hXv : ∀ v, X v = (A (p v) : Wp) := fun v => by
    rw [hX, LinearMap.coe_toContinuousLinearMap']
    rfl
  have hAv : ∀ a b x, A (resE E' _ hstab' a b x) = resE E _ hstab a b (A x) := fun a b x =>
    LinearMap.congr_fun (hAi a b) x
  have hXint : ∀ (a b : Fin n) (v : Wq), X (EB π' Fr a b v) = EB π (fun i => g *ᵥ Fr i) a b (X v) := by
    intro a b v
    rw [hXv, hXv]
    change (A (p (E' a b v)) : Wp) = E a b (A (p v) : Wp)
    rw [hpE, hAv, resE_apply]
  refine ⟨X, hLG Wp Wq (n + 1) r z z' π π' hz hz' hT hT' ⟨hrep, hcont⟩ ⟨hrep', hcont'⟩ g hg hGG Fr hFr X hXint, ?_, ?_⟩
  · intro Y v
    rw [hXv, hXv]
    change (A (p (qdet E' (Y + (((n + 1 : ℕ) : ℂ) - 2) / 2) v)) : Wp) = Formalism.FourierDecayAlt.M.xC ⟨n + 1, r, T, T', u, u'⟩ ρ Y • (A (p v) : Wp)
    rw [qdet_int p hpE, cap_resE (shf β M) hstab', map_smul, Submodule.coe_smul, hcp Y]
  · intro hX0
    obtain ⟨x, hx⟩ : ∃ x, A x ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hA0 (LinearMap.ext hc)
    apply hx
    have h1 : X (x : Wq) = 0 := by rw [hX0]; rfl
    rw [hXv, hp, projI_self hint' (i := Mb') x] at h1
    exact_mod_cast h1

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExOf

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem lie_existence_of_iso_group : KLExistsOf := KLExOf.lie_existence_of_iso_group

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
