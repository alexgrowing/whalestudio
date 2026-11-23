import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionSumMulMiddleCoordinate
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMixSmooth

variable {D : D7}

theorem finite_rat_mem (m n : ℕ) (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, hlc, -, ht2, hdisc, -⟩ := lattice_Mx D m n
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, γ, rfl⟩, hγ, rfl⟩

theorem contDiff_of_additive {k : ℕ} (f : (Fin k → ℝ) → ℂ) (h0 : f 0 = 0) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hc : Continuous f) : ContDiff ℝ ∞ f :=
  GlobalTheory.WeilVacMove.contDiff_additive (⟨⟨f, h0⟩, hadd⟩ : (Fin k → ℝ) →+ ℂ) hc

def rmul {m n p : ℕ} (Q : Mx D n p) : Mx D m n →+ Mx D m p where
  toFun x := x ⬝ Q
  map_zero' := Matrix.zero_mul _
  map_add' x y := Matrix.add_mul _ _ _

theorem continuous_rmul {m n p : ℕ} (Q : Mx D n p) : Continuous (rmul (m := m) Q) :=
  continuous_id.matrix_mul continuous_const

theorem contDiff_psi_symplOH {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {k : ℕ}
    (A B : (Fin k → ℝ) →+ WO S T) (hA : Continuous A) (hB : Continuous B)
    (hA0 : ∀ t, (A t).map (finPart D) = 0) (hB0 : ∀ t, (B t).map (finPart D) = 0) (c c' : WO S T) :
    ContDiff ℝ ∞ fun t => ψ (symplOH S T (c + A t) (c' + B t)) := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  have hadd1 := GlobalTheory.WeilVacMove.symplOH_add_left S T
  have hadd2 := GlobalTheory.WeilVacMove.symplOH_add_right S T
  have hz1 := GlobalTheory.WeilVacMove.symplOH_zero_left S T
  have hz2 := GlobalTheory.WeilVacMove.symplOH_zero_right S T
  have h1 : ContDiff ℝ ∞ fun t => lam (symplOH S T c (B t)) :=
    contDiff_of_additive _ (by rw [map_zero, hz2, map_zero]) (fun x y => by rw [map_add, hadd2, map_add])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_const hB))
  have h2 : ContDiff ℝ ∞ fun t => lam (symplOH S T (A t) c') :=
    contDiff_of_additive _ (by rw [map_zero, hz1, map_zero]) (fun x y => by rw [map_add, hadd1, map_add])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hA continuous_const))
  have hQ : ContDiff ℝ ∞ fun t => lam (symplOH S T (A t) (B t)) := by
    let φ : (Fin k → ℝ) → ((Fin k → ℝ) →+ ℂ) := fun t =>
      { toFun := fun s => lam (symplOH S T (A s) (B t))
        map_zero' := by rw [map_zero, hz1, map_zero]
        map_add' := fun x y => by rw [map_add, hadd1, map_add] }
    have hφ : ∀ t, Continuous (φ t) := fun t =>
      hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hA continuous_const)
    have e : (fun t => lam (symplOH S T (A t) (B t))) =
        fun t => ∑ i, t i • lam (symplOH S T (A fun j => if i = j then 1 else 0) (B t)) := by
      funext t
      exact LinearMap.pi_apply_eq_sum_univ ((φ t).toRealLinearMap (hφ t) : (Fin k → ℝ) →ₗ[ℝ] ℂ) t
    rw [e]
    refine ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).smul ?_
    exact contDiff_of_additive _ (by rw [map_zero, hz2, map_zero]) (fun x y => by rw [map_add, hadd2, map_add])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_const hB))
  have e : ∀ t, ψ (symplOH S T (c + A t) (c' + B t)) = ψ (symplOH S T c c') *
      Complex.exp (lam (symplOH S T c (B t)) + lam (symplOH S T (A t) c') + lam (symplOH S T (A t) (B t))) := by
    intro t
    have hs : sndA D.host.F (symplOH S T c (B t) + symplOH S T (A t) c' + symplOH S T (A t) (B t)) = 0 := by
      rw [map_add, map_add, GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inr (hB0 t)),
        GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inl (hA0 t)), GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inl (hA0 t)),
        add_zero, add_zero]
    rw [hadd1, hadd2, hadd2, show ∀ a b c d : AF D.host.F, a + b + (c + d) = a + (b + c + d) from fun _ _ _ _ => by abel,
      AddChar.map_add_eq_mul, hlam _ hs, map_add, map_add]
  rw [show (fun t => ψ (symplOH S T (c + A t) (c' + B t))) = _ from funext e]
  exact contDiff_const.mul ((h1.add h2).add hQ).cexp

end GlobalTheory.BumpMixSmooth

namespace GlobalTheory.BumpMixSmooth

theorem poinX_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ)
    (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L →
    (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => poinX ψ d T β (w + L t) := by
  intro D ψ hψ S S₀ T ρ d β hβ k L hL hL0 w
  obtain ⟨hg, hlc, -, -, -, -⟩ := lattice_Mx D T.rank ρ
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg
  have hx : Continuous fun t => (w + L t) ⬝ d.jX := (continuous_const.add hL).matrix_mul continuous_const
  let lX := (rmul (m := T.rank) d.jX).comp L
  let lY := (rmul (m := T.rank) d.jY).comp L
  have hlX : Continuous lX := (continuous_rmul _).comp hL
  have hlY : Continuous lY := (continuous_rmul _).comp hL
  have hlX0 : ∀ t, (lX t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hL0 t) _
  have hlY0 : ∀ t, (lY t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hL0 t) _
  let A := (d.extX T).comp lX
  let B := (d.extY T).comp lY
  have hA : Continuous A := show Continuous fun t => lX t ⬝ d.pX from hlX.matrix_mul continuous_const
  have hB : Continuous B := show Continuous fun t => lY t ⬝ d.pY from hlY.matrix_mul continuous_const
  have hA0 : ∀ t, (A t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hlX0 t) d.pX
  have hB0 : ∀ t, (B t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hlY0 t) d.pY
  have hterm : ∀ γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ContDiff ℝ ∞ fun t =>
      ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) * β ((w + L t) ⬝ d.jX + rat γ) := by
    intro γ
    have e : ∀ t, ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) *
        β ((w + L t) ⬝ d.jX + rat γ) = ψ (symplOH S T (d.extX T (w ⬝ d.jX + 2 • rat γ) + A t)
          (d.extY T (w ⬝ d.jY) + B t)) * β ((w ⬝ d.jX + rat γ) + lX t) := by
      intro t
      have hx' : (w + L t) ⬝ d.jX = w ⬝ d.jX + lX t := Matrix.add_mul _ _ _
      have hy' : (w + L t) ⬝ d.jY = w ⬝ d.jY + lY t := Matrix.add_mul _ _ _
      have e1 : d.extX T (w ⬝ d.jX + lX t + 2 • rat γ) = d.extX T (w ⬝ d.jX + 2 • rat γ) + A t := by
        rw [add_right_comm, map_add]; rfl
      have e2 : d.extY T (w ⬝ d.jY + lY t) = d.extY T (w ⬝ d.jY) + B t := map_add _ _ _
      rw [hx', hy', ← d.symplOH_extX_extY T, e1, e2, add_right_comm (w ⬝ d.jX)]
    rw [show (fun t => ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) *
        β ((w + L t) ⬝ d.jX + rat γ)) = _ from funext e]
    exact (contDiff_psi_symplOH hψ A B hA hB hA0 hB0 _ _).mul (hβ.smooth k lX hlX hlX0 _)
  rw [contDiff_iff_contDiffAt]
  intro t₀
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds t₀
  have hC : IsCompact ((fun p : Mx D T.rank ρ × Mx D T.rank ρ => p.1 - p.2) ''
      (tsupport β ×ˢ ((fun t => (w + L t) ⬝ d.jX) '' K))) :=
    (hβ.supp.isCompact.prod (hK.image hx)).image (continuous_fst.sub continuous_snd)
  have hF := finite_rat_mem T.rank ρ _ hC
  have hsum : ContDiff ℝ ∞ fun t => ∑ γ ∈ hF.toFinset,
      ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) * β ((w + L t) ⬝ d.jX + rat γ) :=
    ContDiff.sum fun γ _ => hterm γ
  refine hsum.contDiffAt.congr_of_eventuallyEq (Filter.eventually_of_mem hKn fun t ht => ?_)
  show poinX ψ d T β (w + L t) = _
  rw [poinX]
  refine tsum_eq_sum fun γ hγ => ?_
  have h0 : β ((w + L t) ⬝ d.jX + rat γ) = 0 := by
    by_contra hne
    exact hγ (hF.mem_toFinset.2 ⟨((w + L t) ⬝ d.jX + rat γ, (w + L t) ⬝ d.jX),
      ⟨subset_tsupport β hne, t, ht, rfl⟩, add_sub_cancel_left _ _⟩)
  rw [h0, mul_zero]

end GlobalTheory.BumpMixSmooth

end
