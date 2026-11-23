import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormLeadMinorOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTIn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HsNormSqEqHilbertSchmidtSq

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem rd_eq' : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE := by
  simp [Formalism.FourierDecayAlt.S6.rd, Formalism.BasicNotions.Host.rdE, one_div]

theorem blk_norm (τ : D.what₂.Tau) (σ : D.host.E →+* ℂ) (hσ : ∀ t, σ t = Formalism.MainNotions.S.plEmb D τ t) (b s m : ℕ)
    (t : D.host.E) :
    ‖((Formalism.MainNotions.S.rhoReal D b s : ℝ) : ℂ) * Formalism.MainNotions.S.plEmb D τ ((-1) ^ m * t)‖ =
      Formalism.FourierDecayAlt.S6.rd D.host.E ^ (-(Formalism.FourierDecayAlt.S6.nuBlock (D.R.rS : ℤ) (b : ℤ) (s : ℤ) : ℝ)) * ‖σ t‖ := by
  have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by unfold Formalism.MainNotions.S.rhoReal; positivity), map_mul,
    map_pow, map_neg, map_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← hσ, rd_eq']
  unfold Formalism.MainNotions.S.rhoReal Formalism.FourierDecayAlt.S6.nuBlock
  rw [show (-(((2 * (D.R.rS : ℤ) + 3 - 2 * (b : ℤ) - (s : ℤ)) : ℤ) : ℝ)) =
      ((-(((2 * D.R.rS + 3 : ℕ) : ℤ) - 2 * (b : ℤ) - (s : ℤ)) : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]

theorem weightDeterminant_block_eq (τ : D.what₂.Tau) (σ : D.host.E →+* ℂ) (hσ : ∀ t, σ t = Formalism.MainNotions.S.plEmb D τ t) (k : ℕ) (GG : ℝ) :
    ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (b : ℕ), 1 ≤ b →
    Formalism.FourierDecayAlt.C.nAux k D.R.rS GG
              (fun b s => Formalism.FourierDecayAlt.S6.rd D.host.E ^ (-(Formalism.FourierDecayAlt.S6.nuBlock (D.R.rS : ℤ) (b : ℤ) (s : ℤ) : ℝ))) b
              (Formalism.FourierDecayAlt.C.loc σ p) =
      WtDet.FA k D.R.rS GG b (Formalism.MainNotions.S.locBlocksFrom D (Formalism.MainNotions.S.rhoReal D) τ (b - 1)
        ((Formalism.L2.SG.DataInst.signAux D.R.rS b p).map Prod.swap))
  | [], _, _ => by simp [Formalism.FourierDecayAlt.C.loc, Formalism.FourierDecayAlt.C.nAux, Formalism.L2.SG.DataInst.signAux, Formalism.MainNotions.S.locBlocksFrom, WtDet.FA]
  | (s, t) :: rest, b, hb => by
    have ih := weightDeterminant_block_eq τ σ hσ k GG rest (b + s) (by omega)
    simp only [Formalism.FourierDecayAlt.C.loc, List.map_cons, Formalism.FourierDecayAlt.C.nAux, Formalism.L2.SG.DataInst.signAux, Prod.swap_prod_mk,
      Formalism.MainNotions.S.locBlocksFrom, WtDet.FA]
    rw [show b - 1 + 1 = b by omega, show b - 1 + s = b + s - 1 by omega]
    simp only [Formalism.FourierDecayAlt.C.loc] at ih
    rw [ih, blk_norm τ σ hσ b s _ t]

theorem nHead_eq (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : InfinitePlace X.B.I.F) (τ : D.what₂.Tau) (hpl : X.pl v = τ) :
    ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (b : ℕ), 1 ≤ b → b + (p.map Prod.fst).sum ≤ D.R.rS + 2 → (∀ x ∈ p, 1 ≤ x.1) →
    RealObj.nHead X v b ((Formalism.L2.SG.DataInst.signAux D.R.rS b p).map Prod.swap) =
      WtDet.FH D.R.rS b (Formalism.MainNotions.S.locBlocksFrom D (Formalism.MainNotions.S.rhoReal D) τ (b - 1)
        ((Formalism.L2.SG.DataInst.signAux D.R.rS b p).map Prod.swap))
  | [], _, _, _, _ => by simp [RealObj.nHead, Formalism.L2.SG.DataInst.signAux, Formalism.MainNotions.S.locBlocksFrom, WtDet.FH]
  | (s, t) :: rest, b, hb, hsz, hpos => by
    simp only [List.map_cons, List.sum_cons] at hsz
    have hs1 : 1 ≤ s := hpos (s, t) (by simp)
    have ih := nHead_eq X v τ hpl rest (b + s) (by omega) (by omega) (fun x hx => hpos x (by simp [hx]))
    simp only [List.map_cons, RealObj.nHead, Formalism.L2.SG.DataInst.signAux, Prod.swap_prod_mk,
      Formalism.MainNotions.S.locBlocksFrom, WtDet.FH]
    rw [show b - 1 + 1 = b by omega, show b - 1 + s = b + s - 1 by omega, ih]
    congr 2
    have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
    have hφ : X.B.I.φ v (X.ιE.symm ((-1) ^ (D.R.rS + 1 - (b + s - 1)) * t)) =
        Formalism.MainNotions.S.plEmb D τ ((-1) ^ (D.R.rS + 1 - (b + s - 1)) * t) := by
      rw [X.φ_eq, RingEquiv.apply_symm_apply, hpl]; rfl
    rw [hφ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by unfold Formalism.MainNotions.S.rhoReal; positivity)]
    congr 1
    unfold Formalism.MainNotions.S.rhoReal
    obtain ⟨d, hd⟩ : ∃ d, 2 * (D.R.rS + 1) - b - (b + s - 1) = d := ⟨_, rfl⟩
    have hd' : (d : ℤ) = 2 * (D.R.rS : ℤ) + 3 - 2 * (b : ℤ) - (s : ℤ) := by omega
    rw [hd, ← zpow_natCast, ← zpow_neg, hd']
    push_cast
    ring_nf

theorem signFlip_append {K : Type} [Ring K] (r : ℕ) : ∀ (L1 L2 : Formalism.FourierDecayAlt.TB.Pt K) (b : ℕ),
    Formalism.L2.SG.DataInst.signAux r b (L1 ++ L2) =
      Formalism.L2.SG.DataInst.signAux r b L1 ++ Formalism.L2.SG.DataInst.signAux r (b + (L1.map Prod.fst).sum) L2
  | [], L2, b => by simp [Formalism.L2.SG.DataInst.signAux]
  | (s, t) :: L1, L2, b => by
    simp only [List.cons_append, Formalism.L2.SG.DataInst.signAux, signFlip_append r L1 L2 (b + s), List.map_cons,
      List.sum_cons, add_assoc]

theorem locBlocksFrom_append (ρ : ℕ → ℕ → ℝ) (τ : D.what₂.Tau) : ∀ (L1 L2 : List (D.host.E × ℕ)) (a : ℕ),
    Formalism.MainNotions.S.locBlocksFrom D ρ τ a (L1 ++ L2) =
      Formalism.MainNotions.S.locBlocksFrom D ρ τ a L1 ++ Formalism.MainNotions.S.locBlocksFrom D ρ τ (a + (L1.map Prod.snd).sum) L2
  | [], L2, a => by simp [Formalism.MainNotions.S.locBlocksFrom]
  | (t, s) :: L1, L2, a => by
    simp only [List.cons_append, Formalism.MainNotions.S.locBlocksFrom, locBlocksFrom_append ρ τ L1 L2 (a + s), List.map_cons,
      List.sum_cons, add_assoc]

theorem nHead_nonneg (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : InfinitePlace X.B.I.F) :
    ∀ (b : ℕ) (L : List (D.host.E × ℕ)), 0 ≤ RealObj.nHead X v b L
  | _, [] => by simp [RealObj.nHead]
  | b, (t, s) :: rest => by
    simp only [RealObj.nHead]
    have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
    exact mul_nonneg (pow_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hrd.le _)) (norm_nonneg _)) _)
      (nHead_nonneg X v (b + s) rest)

theorem sqrt_prod' {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    Real.sqrt (∏ i, x i) = ∏ i, Real.sqrt (x i) := by
  rw [Real.sqrt_eq_iff_mul_self_eq (Finset.prod_nonneg fun i _ => hx i)
    (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (Real.mul_self_sqrt (hx i)).symm

variable (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT in

theorem wtTie_carrierInT (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ) :
    WtTie X (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)) u u' := by
  intro p w hp hgood
  obtain ⟨hrep, hG⟩ := hgood
  have hk := Formalism.MainNotions.BridgeLemma.five_le_k D

  have hpt := hp
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList at hpt
  split_ifs at hpt with hPtL
  have hw1 : w.1 = (Formalism.L2.SG.DataInst.signAux D.R.rS 1 p).map Prod.swap := by
    rw [← Option.some_inj.mp hpt]; rfl
  have hfst : (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst = p.map Prod.fst :=
    Formalism.L2.SG.DataInst.sign_list_fst D.R.rS 1 p
  have hblk : ∀ b ∈ p, 1 ≤ b.1 := by
    intro b hb
    have : b.1 ∈ (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst := by
      rw [hfst]; exact List.mem_map_of_mem hb
    obtain ⟨b', hb', hbb⟩ := List.mem_map.mp this
    rw [← hbb]; exact (hPtL.2 b' hb').1
  have hsum : (p.map Prod.fst).sum = D.R.rS + 1 := by rw [← hfst, hPtL.1]
  have hne : p ≠ [] := by rintro rfl; simp at hsum

  have hplace : ∀ j : Fin (nfE D),
      Formalism.FourierDecayAlt.C.nLoc (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.k
        (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.r
        (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).fr
        ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).pd j).G
        (Formalism.FourierDecayAlt.C.loc ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j) p) =
      GX X u u' D.host.rdE (gamW X u u' w) (tauE X e j) ^ (D.R.k - 1) * RealObj.nHead X (tauE X e j) 1 w.1 := by
    intro j
    set τ := e (plE D j) with hτ
    have hpl : X.pl (tauE X e j) = τ := by
      show X.pl (X.pl.symm (e (plE D j))) = _
      exact Equiv.apply_symm_apply _ _
    have hσ : ∀ t, (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j t =
        Formalism.MainNotions.S.plEmb D τ t := by
      intro t
      show X.B.I.φ (tauE X e j) (X.ιE.symm t) = _
      rw [X.φ_eq, RingEquiv.apply_symm_apply, hpl]; rfl
    obtain ⟨p1, x, hpx⟩ : ∃ p1 x, p = p1 ++ [x] := ⟨p.dropLast, p.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    obtain ⟨s, t⟩ := x
    have hq : (Formalism.MainNotions.S.ThB.ptLoc D τ w).1 =
        Formalism.MainNotions.S.locBlocksFrom D (Formalism.MainNotions.S.rhoReal D) τ 0 ((Formalism.L2.SG.DataInst.signAux D.R.rS 1 p).map Prod.swap) := by
      rw [← hw1]; rfl
    set L1 := Formalism.MainNotions.S.locBlocksFrom D (Formalism.MainNotions.S.rhoReal D) τ 0
      ((Formalism.L2.SG.DataInst.signAux D.R.rS 1 p1).map Prod.swap)
    have hsz1 : (((Formalism.L2.SG.DataInst.signAux D.R.rS 1 p1).map Prod.swap).map Prod.snd).sum = (p1.map Prod.fst).sum := by
      rw [List.map_map]
      have := Formalism.L2.SG.DataInst.sign_list_fst D.R.rS 1 p1
      rw [← this]; rfl
    have hq2 : (Formalism.MainNotions.S.ThB.ptLoc D τ w).1 = L1 ++
        [(((Formalism.MainNotions.S.rhoReal D (1 + (p1.map Prod.fst).sum) s : ℝ) : ℂ) *
          Formalism.MainNotions.S.plEmb D τ ((-1) ^ (D.R.rS + 1 - (1 + (p1.map Prod.fst).sum + s - 1)) * t), s)] := by
      rw [hq, hpx, signFlip_append, List.map_append, locBlocksFrom_append, hsz1]
      simp [Formalism.L2.SG.DataInst.signAux, Formalism.MainNotions.S.locBlocksFrom, add_comm]
      rfl
    have hsum1 : (p1.map Prod.fst).sum + s = D.R.rS + 1 := by
      rw [hpx] at hsum; simpa using hsum

    have hGv : ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).pd j).G
        (Formalism.FourierDecayAlt.C.loc ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j) p) =
        Complex.normSq (Formalism.MainNotions.S.plEmb D τ t) - Tw (D := D) u * Tw (D := D) u' := by
      have hT := (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).hT j
      show Formalism.FourierDecayAlt.D.ptGG (Formalism.QuantumDeterminants.Tz _ _ _ * Formalism.QuantumDeterminants.Tz _ _ _) _ = _
      rw [hT.1, hT.2]
      unfold Formalism.FourierDecayAlt.D.ptGG Formalism.FourierDecayAlt.D.ptLast
      rw [hpx]
      simp [Formalism.FourierDecayAlt.C.loc, hσ]
      rfl
    have hGG : s = 1 → Complex.normSq (Formalism.MainNotions.S.plEmb D τ t) - Tw (D := D) u * Tw (D := D) u' =
        ‖((Formalism.MainNotions.S.rhoReal D (1 + (p1.map Prod.fst).sum) s : ℝ) : ℂ) *
          Formalism.MainNotions.S.plEmb D τ ((-1) ^ (D.R.rS + 1 - (1 + (p1.map Prod.fst).sum + s - 1)) * t)‖ ^ 2 -
          Tw (D := D) u * Tw (D := D) u' := by
      intro hs1
      rw [blk_norm τ (Formalism.MainNotions.S.plEmb D τ) (fun _ => rfl), Complex.normSq_eq_norm_sq]
      congr 2
      have : (Formalism.FourierDecayAlt.S6.nuBlock (D.R.rS : ℤ) ((1 + (p1.map Prod.fst).sum : ℕ) : ℤ) (s : ℤ)) = 0 := by
        unfold Formalism.FourierDecayAlt.S6.nuBlock; subst hs1; rw [Nat.cast_add, Nat.cast_one]; omega
      rw [this]; simp
    have hcore := WtDet.core_wt D.R.k D.R.rS (by omega) (Tw (D := D) u) (Tw (D := D) u') (Formalism.MainNotions.S.ThB.ptLoc D τ w)
      L1 _ s hq2 _ hGG
    have hA := weightDeterminant_block_eq τ ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j) hσ
      D.R.k (Complex.normSq (Formalism.MainNotions.S.plEmb D τ t) - Tw (D := D) u * Tw (D := D) u') p 1 le_rfl
    have hH := nHead_eq X (tauE X e j) τ hpl p 1 le_rfl (by omega) hblk
    have hgx := Formalism.L2.SG.Pf.OOCoreHilbertSchmidt.gx_eq u u' w hrep τ
    unfold Formalism.FourierDecayAlt.C.nLoc
    rw [hGv]
    change Formalism.FourierDecayAlt.C.nAux D.R.k D.R.rS _
      (fun b s => Formalism.FourierDecayAlt.S6.rd D.host.E ^ (-(Formalism.FourierDecayAlt.S6.nuBlock (D.R.rS : ℤ) (b : ℤ) (s : ℤ) : ℝ))) 1 _ = _
    rw [hA, show (1 : ℕ) - 1 = 0 from rfl, ← hq, ← hcore, hw1, hH, ← hq]
    rw [show tauE X e j = vOf X τ from rfl, hgx]
  unfold nW
  rw [sqrt_prod' _ (fun v => mul_nonneg (pow_nonneg (hG v).le _) (nHead_nonneg X v 1 w.1))]
  symm
  exact Fintype.prod_equiv (tauE X e) _ _ (fun j => by rw [hplace j])

end Formalism.L2.SG.Pf.Carrier.CarPinVt
