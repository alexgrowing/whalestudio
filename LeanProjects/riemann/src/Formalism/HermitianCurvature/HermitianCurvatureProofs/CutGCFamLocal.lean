import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_locality_holds : FamLocal := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk X Dc Φ hΦ q
  have hk1 : 1 ≤ P.k := by omega
  have hz := hpl.2.1
  have hz' := hpl.2.2.1
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hpl.2.2.2.1]; exact hpl.1.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos
  have hsec := Bs.sec
  obtain ⟨hOpen, hIsDom, hMu, hFF⟩ := hΦ

  have hdom : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', x.2 ∈ Dc x.1 := by
    intro x hx
    obtain ⟨h, hh, h', hh', hg⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp hk1 hz hz' hT hT' hsec hx.2.1 hx.2.2
    set ζ := Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2 with hζ
    have hζT : P.TT < Complex.normSq ζ := by
      have h1 := hx.2.2
      unfold Q.GGl at h1
      show P.T * P.T' < _
      rw [← hpl.2.2.2.1, ← hpl.2.2.2.2.1]
      linarith
    let q' : MA.Qp P.r P.TT := ⟨(x.1, ζ), hx.1, hζT⟩
    have hmu : NF.muZ P.k P.r Bs.μsec ζ ∈ Dc x.1 := hMu q'
    have hmuG : NF.muZ P.k P.r Bs.μsec ζ ∈ Q.Glev P.k P.r (Fin.last P.r) :=
      Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem.muZ_glev hpl q'
    have hS : ∀ {w : Fin (2 * P.r + P.k + 1) → ℂ} {s : Q.Mx P.k P.r}, s ∈ UWset P.k P.r w →
        s ∈ Q.Slev P.k P.r w (Fin.last P.r) := by
      intro w s hs
      exact ⟨s, hs, 1, Formalism.FourierDecayAlt.P.Qx6.one_nlev _, by simp⟩
    rw [hg]
    exact (hIsDom x.1 hx.1).2 _ ⟨hmuG, hmu⟩ h (hS hh) h' (hS hh')

  let Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp) := fun c g => if (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ c g else 0
  have hΦt_mem : Φt ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0) = 0
      rw [if_neg hx]
    · obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := hFF.1 x₀ ⟨hx₀.1, hdom x₀ hx₀⟩ hx₀.2.1
      have hO : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r ∧ 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} := by
        have h1 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r} := by
          have : IsOpen (OmX P.r) := by
            have e : OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
            rw [e]
            exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
          exact this.preimage continuous_fst
        have h2 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} :=
          isOpen_lt continuous_const ((Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z').comp continuous_snd)
        exact h1.inter h2
      refine ⟨U ∩ {x | x.1 ∈ OmX P.r ∧ 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2}, F, hU.inter hO, ⟨hx₀U, hx₀.1, hx₀.2.2⟩,
        hF.mono Set.inter_subset_left, fun x hx hxG => ?_⟩
      have hxD : x ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hx.2.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0) = F x
      rw [if_pos hxD]
      exact hΦF x hx.1 hxG
    · have hxD' := Formalism.FourierDecayAlt.P.Qx5.DomR_inv hh hh' hx
      show (if (x.1, h * x.2 * h') ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 (h * x.2 * h') else 0) =
        (Bs.π h).comp ((if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0).comp (Bs.π' h'))
      rw [if_pos hxD', if_pos hx]
      exact (hFF.2 x.1 hx.1).2.2.2 x.2 ⟨hx.2.1, hdom x hx⟩ h hh h' hh'
  refine ⟨⟨Φt, hΦt_mem⟩, {ζ' | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ'}, ?_, fun ζ' hζ' => ?_⟩
  · refine (isOpen_lt continuous_const Complex.continuous_normSq).mem_nhds ?_
    show Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact q.2.2
  have hqD : (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec (q := (q.1.1, ζ')) ⟨q.2.1, hζ'⟩
  have hval : Φt q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') = Φ q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') := by
    show (if (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') ∈ Q.DomR P.k P.r Bs.z Bs.z' then _ else 0) = _
    rw [if_pos hqD]
  refine ⟨hval, fun Y a b => ?_⟩
  rw [X.t_apply Y a b ⟨Φt, hΦt_mem⟩ (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') hqD]
  show Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (Φt q.1.1) (NF.muZ P.k P.r Bs.μsec ζ') =
    Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (Φ q.1.1) (NF.muZ P.k P.r Bs.μsec ζ')
  have hDo : IsOpen {g : Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' g} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z')
  refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := Fin.last P.r) hDo Bs.z Bs.z' Y a b).1 (Φt q.1.1) (Φ q.1.1) (fun x hx => ?_)
    _ ⟨hqD.2.1, hqD.2.2⟩
  show (if (q.1.1, x) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ q.1.1 x else 0) = Φ q.1.1 x
  rw [if_pos ⟨q.2.1, hx.1, hx.2⟩]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
