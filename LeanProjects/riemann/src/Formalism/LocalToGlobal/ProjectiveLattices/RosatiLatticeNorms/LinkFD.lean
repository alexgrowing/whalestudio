import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.D6P4Statement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer
import Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup

noncomputable section

namespace Formalism.L2.Pj.abelian₂

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem holSub_SS (h5 : SiegelSpaceAlgebra (E := E)) {Comp : Type} (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r)
    {P : FDSec X} (hP : P ∈ holSub X la) : ∀ c, P c ∈ (X c).SS (la c) := by
  intro c
  unfold holSub at hP
  unfold SiegelSpaceAlgebra at h5
  have hs := (h5 r (X c) (la c) (la c) 0).1
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    unfold IsHolCusp at hQ
    exact hQ c
  | zero => exact hs.1
  | add Q R _ _ hQ hR => exact hs.2.1 _ hQ _ hR
  | smul a Q _ hQ => exact hs.2.2 a _ hQ

theorem pnorm_le_supN {Comp : Type} (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X)
    (hfin : supE X la P ≠ ⊤) (c : Comp) (x : Frame (X c).Ψ r) (hx : x ∈ (X c).dom) :
    (X c).pnorm (la c) (P c) x ≤ supN X la P := by
  unfold supN
  unfold supE at hfin ⊢
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
  exact le_iSup_of_le ⟨c, ⟨x, hx⟩⟩ le_rfl

theorem half_max {Comp : Type} (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X)
    (hpos : 0 < supN X la P) (hfin : supE X la P ≠ ⊤) :
    ∃ (c : Comp) (z0 : Frame (X c).Ψ r), z0 ∈ (X c).dom ∧ supN X la P < 2 * (X c).pnorm (la c) (P c) z0 := by
  have hE : supE X la P = ENNReal.ofReal (supN X la P) := by
    unfold supN
    rw [ENNReal.ofReal_toReal hfin]
  have h1 : ENNReal.ofReal (supN X la P / 2) < supE X la P := by
    rw [hE]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 (half_lt_self hpos)
  unfold supE at h1
  obtain ⟨p, hp⟩ := lt_iSup_iff.1 h1
  have h2 : supN X la P / 2 < (X p.1).pnorm (la p.1) (P p.1) p.2.1 :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 hp
  exact ⟨p.1, p.2.1, p.2.2, by linarith⟩

theorem cm_frame (Xx : DataX E r) (la : Wt Xx.Ψ r) (P : Frame Xx.Ψ r → ℂ) (z0 : Frame Xx.Ψ r) (M w : ℝ)
    (hSS : P ∈ Xx.SS la) (hM : 0 < M) (hw : (∑ τ, Xx.spread la τ) ≤ w) (hw1 : 1 ≤ w) (hr : 0 < r)
    (htr : ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ Xx.Γ, Xx.χ la γ = 1 ∧
        ∀ τ : Xx.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Xx.flowMat v τ ((M : ℂ) * τ.1 b))
    (hz0 : z0 ∈ Xx.dom) (hhalf : ∀ x ∈ Xx.dom, Xx.pnorm la P x ≤ 2 * Xx.pnorm la P z0)
    (hpos : 0 < Xx.pnorm la P z0) :
    ∃ (x : Frame Xx.Ψ r) (lam : Fin r → Fin r → E), x ∈ Xx.dom ∧
      LamBasis Xx (frameBasisRadius r Xx.p0 (fdeg E) (dE E) (Real.sqrt (epStar M (fdeg E) w Xx.k0))
        (3 * frameRadius w r / 5)) x lam ∧
      P x ≠ 0 ∧ ∀ τ v, Xx.maj x τ v ≤ 2 * Xx.maj z0 τ v := by
  have hmax := maxBound_holds r Xx la P M w hSS hM hw (by linarith) htr z0 hz0 hhalf hpos
  have hfw : 0 < (fdeg E : ℝ) * w + 2 := by
    have := (Nat.cast_nonneg (fdeg E) : (0 : ℝ) ≤ fdeg E)
    nlinarith
  have hep0 : 0 < epStar M (fdeg E) w Xx.k0 := by
    refine lt_min one_pos (div_pos Real.pi_pos ?_)
    have := Xx.minWeight_pos
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  have hep1 : epStar M (fdeg E) w Xx.k0 ≤ 1 := min_le_left _ _
  refine Formalism.L2.Pj.FundamentalDomainD5.t41H_statement r Xx la P z0 (Real.sqrt (epStar M (fdeg E) w Xx.k0)) w hSS.1.1 hz0
    hhalf hpos hw hw1 hr (Real.sqrt_pos.2 hep0) (Real.sqrt_le_one.2 hep1) ?_
  intro v hv hv0
  obtain ⟨τ, hτ⟩ := hmax v hv hv0
  rw [Real.sq_sqrt hep0.le]
  exact hτ.trans (Finset.single_le_sum (f := fun τ => Xx.maj z0 τ (Data.emb τ.1 v))
    (fun τ _ => MajorantConjugateTransfer.maj_nonneg Xx.toData hz0 τ _) (Finset.mem_univ τ))

end Formalism.L2.Pj.abelian₂
