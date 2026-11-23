import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HaarPushforward
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MapConjOfBounded

noncomputable section

open scoped ComplexConjugate
open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.CovariantRepresentation Formalism.L2.SG.HaarPushforward

namespace Formalism.L2.SG.HaarRelevantTerms

def RHaarRelC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    (∀ r ∈ Rset t, X.psiInfU u r * starRingEnd ℂ (X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)) = 1) →
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∃ ν : Measure X.B.I.Ginf, SigmaFinite ν ∧ ν ≠ 0 ∧ ν (Rset t)ᶜ = 0 ∧
      (∀ K : Set X.B.I.Ginf, IsCompact K → ν K < ⊤) ∧ (∀ r ∈ Rset t, ν.map (fun x => r * x) = ν) ∧
      ν.map (fun x => x⁻¹) = ν ∧ ν.map (fun x => h⁻¹ * x * h) = ν

def FixDecC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), t.relevant →
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∃ k n : X.B.I.Ginf, h = k * n ∧ n ∈ Rset t ∧ (∀ r, r ∈ Rset t ↔ k⁻¹ * r * k ∈ Rset t) ∧
      ∃ C : Set X.B.I.Ginf, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C

theorem rHaarRelC_of_rHaarC (h : RHaarC) : RHaarRelC := fun D X Y u u' t _ => h D X Y u u' t

theorem relevant_of_triv (hNR : NonRelCharC) {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (hχ : ∀ r ∈ Rset t, X.psiInfU u r * starRingEnd ℂ (X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)) = 1) :
    t.relevant := by
  by_contra hr
  obtain ⟨r, hr, hne⟩ := hNR D X Y u u' t hr
  apply hne
  have h1 := hχ r hr
  have hb : starRingEnd ℂ (X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)) * X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1) = 1 := by
    rw [mul_comm, Complex.mul_conj', psiInfU_norm X u']
    simp
  calc X.psiInfU u r = X.psiInfU u r * (starRingEnd ℂ (X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)) *
        X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)) := by rw [hb, mul_one]
    _ = X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1) := by rw [← mul_assoc, h1, one_mul]

theorem rHaarRelC_of (hN : NLamNinf) (hG : PsiInfChar) (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC)
    (hNR : NonRelCharC) (hFD : FixDecC) : RHaarRelC := by
  intro D X Y u u' t hχ h hh
  have hΓR : ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin ≤ Rsub hG t := by
    intro s hs
    have hs0 : s ∈ ROset X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin := hs
    obtain ⟨z, n, hz, hzs, hn, hn'⟩ := hs0
    have hl : RatLink X (t.pt⁻¹ * z * t.pt) (t.lin⁻¹ * n * t.lin) :=
      ratLink_mul X (ratLink_mul X (ratLink_inv X t.rep.2.1) hz) t.rep.2.1
    have hs2 := hN D X u' t.lam' _ _ hl hn'
    rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← hzs] at hs2
    exact ⟨hzs ▸ hN D X u t.lam z n hz hn, hs2⟩
  haveI := ROsub_countable X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin
  haveI := h2 D X Y u u' t
  obtain ⟨K, hK, hKc⟩ := h3 D X Y u u' t
  obtain ⟨ν, hs, h0, hc, hKf, hl, hi⟩ :=
    pushHaar_inv (Rsub hG t) (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin) (h1 D X Y u u' t) hΓR
      ⟨K, hK, fun r hr => hKc r hr⟩
  obtain ⟨k, n, rfl, hn, hk, hC⟩ := hFD D X Y u u' t (relevant_of_triv hNR Y t hχ) h hh
  exact ⟨ν, hs, h0, hc, hKf, hl, hi,
    conj_of_decomp (Rsub hG t) (h1 D X Y u u' t) ν hs h0 hc hKf hl hi k n hk hn hC⟩

end Formalism.L2.SG.HaarRelevantTerms
