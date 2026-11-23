import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.GoodLatCM
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtTransInvHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AmbIsTrueOfAmbTrue
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical
namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xi_zero_embedding_value (D : D7) (hc : D.host.ccK = ⊤) (τ : D.what₂.Tau) :
    tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ) := by
  have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℝ) :=
    ((Formalism.BasicNotions.factEmb D.R D.host).2 _).2 (D.eTau τ).2
  have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (Nat.cast_pos.2 D.host.hyp.2.1.pos)
  rw [Host.xi0, hc, Ideal.absNorm_top, map_div₀, map_mul, h1, map_natCast, map_neg, map_one]
  have : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.ne'
  push_cast
  field_simp
  simp

theorem stdPair_world {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z)) (hψ : IsStdChar (I.rec7 l Z) ψ (-1)) (hθ : IsInfFam θ)
    (i : ℕ) : StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ := by
  obtain ⟨hs, hX, -⟩ := hI.spaces
  have hg : ∀ j, ((I.rec7 l Z).sp.X j).gram = 1 := fun j => by
    have e : (I.rec7 l Z).sp.X j = Formalism.BasicNotions.Examples₂.posSpace hs (B.R.N j) := hX j
    rw [e]
    refine Matrix.ext fun a b => ?_
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs (B.R.N j) (fun _ => false) (B.R.N j) 0 a b).trans ?_
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq]
      exact (if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn]; rfl)
    · rw [Matrix.one_apply_ne h]
      exact if_neg h
  have hr : ∀ j, ((I.rec7 l Z).sp.X j).rank = B.R.N j := fun j => by
    have e : (I.rec7 l Z).sp.X j = Formalism.BasicNotions.Examples₂.posSpace hs (B.R.N j) := hX j
    rw [e]; rfl
  have hev : ∀ j, Even (B.R.N j) := fun j =>
    B.R.k_even.add (Even.mul_left (B.R.t_odd.add_one) j)
  have hδ : I.J.δ ≠ 0 := I.J.δ_ne_zero
  have hd : 0 < Real.sqrt B.host.d := Real.sqrt_pos.2 (Nat.cast_pos.2 B.host.hyp.2.1.pos)
  refine ⟨hψ, hθ, hg _, hg _, (I.rec7 l Z).sp.X_sig _, (I.rec7 l Z).sp.X_sig _, ?_, B.ccK_top, hδ,
    xi_zero_embedding_value _ B.ccK_top, ?_⟩
  · rw [hr, hr]
    refine ⟨?_, ?_, hev _, hev _⟩
    · have := B.R.m_add_three_le_k; unfold Ranks.N; omega
    · unfold Ranks.N; nlinarith
  · have hA := Formalism.MainNotions.Ext.area_lamOf (I.rec7 l Z) ⊤ top_ne_bot I.J.δ hδ
    rw [Formalism.MainNotions.Ext.discr_K (I.rec7 l Z).host, Ideal.absNorm_top] at hA
    have hA' : Formalism.MainNotions.TaylorLogMetric.area (Th.lamOf B.host ⊤ I.J.δ) = ‖I.J.δ‖ ^ 2 * Real.sqrt B.host.d / 2 := by
      refine hA.trans ?_
      simp
      exact Or.inl rfl
    show (Formalism.MainNotions.TaylorLogMetric.area (Th.lamOf B.host ⊤ I.J.δ))⁻¹ * ‖I.J.δ‖ ^ 2 = 2 * (Real.sqrt B.host.d)⁻¹
    rw [hA']
    have : ‖I.J.δ‖ ≠ 0 := norm_ne_zero_iff.2 hδ
    field_simp

end GlobalTheory.AdForm
