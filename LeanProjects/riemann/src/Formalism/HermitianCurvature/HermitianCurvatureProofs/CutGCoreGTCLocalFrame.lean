import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTCLocalFrameC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section fin

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem gcl_fn_mulZ {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    ((X.fn 0 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' id (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ∧
      ((X.fn 2 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
  have key : ∀ (j : Fin 6) (f : ℂ → ℂ),
      (∀ g, Q.fnVal P.k P.r Bs.z Bs.z' j g = f (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g)) →
      ((X.fn j Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' f (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro j f hf
    funext c g
    unfold NF.mulZ
    by_cases hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z'
    · rw [Set.indicator_of_mem hx]
      have h1 := X.fn_apply j Φ (c, g) hx
      dsimp only at h1
      rw [h1, hf]
    · simp only [Set.indicator, hx, if_false]
      obtain ⟨h0, -, -⟩ := (X.fn j Φ).2
      exact h0 (c, g) hx
  exact ⟨key 0 id (fun _ => rfl), key 2 (starRingEnd ℂ) (fun _ => rfl)⟩

end fin

private theorem fnZ_apply_eq_snd (P : M.Par) (f : ℂ → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ann P)) (q : MA.Qp P.r P.TT) :
    ((fnZ P f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = f q.1.2 := by
  have hmem : (fun q : MA.Qp P.r P.TT => f q.1.2) ∈ MA.smSub P.r P.TT := by
    show ContDiffOn ℝ _ (MA.ext _) (MA.Qset P.r P.TT)
    refine (hf.comp contDiff_snd.contDiffOn (fun x hx => hx.2)).congr (fun x hx => ?_)
    simp [MA.ext, hx]
  simp only [fnZ, MA.toSm, dif_pos hmem]

theorem local_frame_holds : GTCLFrame := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk hN hNs
  have hTT : 0 ≤ P.TT := torus_parameter Wp Wq P Bs X d hH
  have hact := hH.2.2.2.1
  have hR := hH.2.2.2.2.2.1
  have hζ1 : d.L.ζ.1 = X.fn 0 := by
    rw [hact.2.2.2.2.2.2.1]
    rfl
  have hζb1 : d.L.ζb.1 = X.fn 2 := by
    rw [hact.2.2.2.2.2.2.2.2.1]
    rfl
  have hmulζ : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ((d.L.ζ.1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' id (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Φ
    rw [hζ1]
    exact (gcl_fn_mulZ X Φ).1
  have hmulζb : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ((d.L.ζb.1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Φ
    rw [hζb1]
    exact (gcl_fn_mulZ X Φ).2
  have hΨζ : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = NF.mulZ P.k P.r Bs.z Bs.z' id (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) →
        Ψ = d.L.ζ.1 Φ :=
    fun Φ Ψ h => Subtype.ext (h.trans (hmulζ Φ).symm)
  have hΨζb : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) →
        Ψ = d.L.ζb.1 Φ :=
    fun Φ Ψ h => Subtype.ext (h.trans (hmulζb Φ).symm)
  have c1 : d.L.nab.1 * d.L.ζ.1 = d.L.ζ.1 * d.L.nab.1 + 1 := congrArg Prod.fst d.L.nab_ζ
  have c2 : d.L.nab.1 * d.L.ζb.1 = d.L.ζb.1 * d.L.nab.1 := congrArg Prod.fst d.L.nab_ζb
  have c3 : d.L.nabs.1 * d.L.ζ.1 = d.L.ζ.1 * d.L.nabs.1 := congrArg Prod.fst d.L.nabs_ζ
  have c4 : d.L.nabs.1 * d.L.ζb.1 = d.L.ζb.1 * d.L.nabs.1 - 1 := congrArg Prod.fst d.L.nabs_ζb
  have hκ1 : ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      d.L.nab.1 ((d.κ f).1 Φ) = (d.κ f).1 (d.L.nab.1 Φ) := by
    intro f Φ
    have h := (hR.2.1 f d.L.nab (Or.inr (Or.inl rfl))).eq
    have h1 : (d.κ f).1 * d.L.nab.1 = d.L.nab.1 * (d.κ f).1 := congrArg Prod.fst h
    exact (LinearMap.congr_fun h1 Φ).symm
  have hκ2 : ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      d.L.nabs.1 ((d.κ f).1 Φ) = (d.κ f).1 (d.L.nabs.1 Φ) := by
    intro f Φ
    have h := (hR.2.1 f d.L.nabs (Or.inr (Or.inr rfl))).eq
    have h1 : (d.κ f).1 * d.L.nabs.1 = d.L.nabs.1 * (d.κ f).1 := congrArg Prod.fst h
    exact (LinearMap.congr_fun h1 Φ).symm
  obtain ⟨A, hAs, hA⟩ := gcl_core P Bs X d hH e he hk d.L.nab.1 hN 1 0
    (fun Φ Ψ h => by
      rw [hΨζ Φ Ψ h, show d.L.nab.1 (d.L.ζ.1 Φ) = d.L.ζ.1 (d.L.nab.1 Φ) + Φ from LinearMap.congr_fun c1 Φ,
        Submodule.coe_add, hmulζ, one_smul])
    (fun Φ Ψ h => by
      rw [hΨζb Φ Ψ h, show d.L.nab.1 (d.L.ζb.1 Φ) = d.L.ζb.1 (d.L.nab.1 Φ) from LinearMap.congr_fun c2 Φ,
        hmulζb, zero_smul, add_zero])
    hκ1
  obtain ⟨B, hBs, hB⟩ := gcl_core P Bs X d hH e he hk d.L.nabs.1 hNs 0 (-1)
    (fun Φ Ψ h => by
      rw [hΨζ Φ Ψ h, show d.L.nabs.1 (d.L.ζ.1 Φ) = d.L.ζ.1 (d.L.nabs.1 Φ) from LinearMap.congr_fun c3 Φ,
        hmulζ, zero_smul, add_zero])
    (fun Φ Ψ h => by
      rw [hΨζb Φ Ψ h, show d.L.nabs.1 (d.L.ζb.1 Φ) = d.L.ζb.1 (d.L.nabs.1 Φ) - Φ from LinearMap.congr_fun c4 Φ,
        Submodule.coe_sub, hmulζb, neg_one_smul, sub_eq_add_neg])
    hκ2
  refine ⟨A, B, fun ρ => ⟨hAs ρ, hBs ρ⟩, fun Φ ρ => ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    funext q
    rw [hA Φ ρ q]
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Pi.add_apply, Pi.mul_apply]
    rw [dzQ_apply P hTT, fnZ_apply_eq_snd P (A ρ) (hAs ρ)]
    ring
  · apply Subtype.ext
    funext q
    rw [hB Φ ρ q]
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg, Pi.add_apply, Pi.mul_apply,
      Pi.neg_apply]
    rw [dzbQ_apply P hTT, fnZ_apply_eq_snd P (B ρ) (hBs ρ)]
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
