import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.QpEqUnit
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemCrit

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section E1

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem mem_of_exp [NeZero n] [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hMC : MemCrit W) (hT : IsCrys PD T.ρ) (c : ZMod n) (ζ₀ : LL)
    (hTr : ∀ ζ : LL, IsPrimitiveRoot ζ PD.p → ∃ δ ∈ W.DelF, ∃ χ : LL, χ ≠ 0 ∧
      (∀ (x : ↥(W.N T)) (hx : W.γD T δ x ∈ W.N T) (k : ℤ),
        W.levN T c ζ ⟨W.γD T δ x, hx⟩ k = χ ^ k • W.levN T c ζ₀ x k) ∧
      (∀ f : LetA O n, W.lev c ζ (W.γA δ f) = PowerSeries.rescale χ (W.lev c ζ₀ f)))
    (u₀ : PowerSeries LL) (hu₀ : W.lev c ζ₀ W.q = X * u₀)
    {w : W.DD T} (hwl : (letE c : LetA O n) • w = w) (hwΔ : ∀ δ ∈ W.DelF, W.γD T δ w = w)
    {K : ℕ} (hK : W.Q ^ K • w ∈ W.N T) {dd : ℤ → T.V ⊗[Qp] BdR} (hdd : ∃ m, LB m dd)
    (he : W.levN T c ζ₀ ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u₀) ^ K) dd)
    (hF : ∀ i : ℤ, dd i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i)) : w ∈ W.N T := by
  apply hMC T hT c w K hK hwl
  intro ζ hζ j
  obtain ⟨u, hu, hu0⟩ := lev_q_simple W c ζ hζ
  obtain ⟨m, hm⟩ := W.levN_supp T c ζ ⟨W.Q ^ K • w, hK⟩
  obtain ⟨dz, hdzLB, hdz⟩ := div_exists hm u hu0 K
  obtain ⟨δ, hδ, χ, hχ0, hN', hA'⟩ := hTr ζ hζ
  have htr := trans_d W T hs hR c δ hδ ζ ζ₀ χ hχ0 hN' hA' (hwΔ δ hδ) hK u u₀ hu hu₀ hu0
    ⟨_, hdzLB⟩ hdd hdz.symm he
  have hanti := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T c 0
  have hDg : Dg (fun a => Formalism.MainNotions.WachCoordinates.FilLev W T c 0 a) 0 dz := by
    intro i
    rw [htr, zero_sub]
    exact (Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i)).smul_mem _ (hF i)
  rw [← hdz, mul_pow, smulS_mul hdzLB, smulS_X_pow (LB_smulS hdzLB _)]
  have h := Dg_smulS hanti hdzLB hDg (u ^ K) (j - K)
  rw [show (0 : ℤ) - (j - K) = (K : ℤ) - j by ring] at h
  exact h

end E1

end Formalism.MainNotions.N.Pv.LocalLengthBound
