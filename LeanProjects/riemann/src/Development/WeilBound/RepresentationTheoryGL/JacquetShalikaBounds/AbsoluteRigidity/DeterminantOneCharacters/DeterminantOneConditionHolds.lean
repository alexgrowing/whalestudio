import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SphericalVectorMemFixedRight

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace PositivityTheory.RgJS

namespace LocalDeterminantOne

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def locU (w : HeightOneSpectrum (𝓞 E)) : (w.adicCompletion E)ˣ →* (Af E)ˣ := Units.map (corner (sLoc E w))

theorem locGL_sc (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) :
    locGL E a w (GlobalTheory.CompanionTheory.Ipf.Val.SphM.sc w a h0) =
      Matrix.GeneralLinearGroup.scalar (Fin a) (locU w (Units.mk0 ϖ h0)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e1 : ((locGL E a w (GlobalTheory.CompanionTheory.Ipf.Val.SphM.sc w a h0) : GL (Fin a) (Af E)) : Matrix (Fin a) (Fin a) (Af E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Af E)) i j - sLoc E w ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) +
        sLoc E w ((ϖ • (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E))) i j) := rfl
  have e2 : ((Matrix.GeneralLinearGroup.scalar (Fin a) (locU w (Units.mk0 ϖ h0)) : GL (Fin a) (Af E)) :
      Matrix (Fin a) (Fin a) (Af E)) i j = if i = j then 1 - sLoc E w 1 + sLoc E w ϖ else 0 := by
    simp [Matrix.GeneralLinearGroup.scalar, locU, corner, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [e1, e2]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h, h]

theorem satEig_self (q a : ℕ) (B : Multiset ℂˣ) (hB : B.card = a) :
    GlobalTheory.LFun.satEig q a B a = ((B.prod : ℂˣ) : ℂ) := by
  have hp := Multiset.powersetCard_self (B.map fun b : ℂˣ => (b : ℂ))
  rw [Multiset.card_map, hB] at hp
  simp only [GlobalTheory.LFun.satEig, Multiset.esymm, hp, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul,
    Multiset.map_singleton, Multiset.sum_singleton]
  exact ((Units.coeHom ℂ).map_multiset_prod B).symm

end LocalDeterminantOne

open LocalDeterminantOne in
theorem determinant_one_condition_holds : DetOne := by
  intro E _ _ _ m π w B hu hB
  induction π using Quotient.inductionOn with | _ π => ?_
  obtain ⟨ω, hω, hc⟩ := hu
  change (CG.mk π).HasSat w B at hB
  change (CG.mk π).HasCentChar ω at hc
  rw [CG.hasSat_mk] at hB
  rw [CG.hasCentChar_mk] at hc
  obtain ⟨x, hx⟩ := hB.exists_vec
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have h0 : ϖ ≠ 0 := fun h => by simp [Formalism.UG.IsUnifV, h] at hϖ
  have h1 := hx.2.2.2 ϖ hϖ m le_rfl
  rw [GlobalTheory.CompanionTheory.Ipf.Val.SphM.Tj_self w m h0,
    GlobalTheory.CompanionTheory.Ipf.Val.SphM.heckeVec_central _ hx.2.1 (GlobalTheory.CompanionTheory.Ipf.Val.SphM.sc_central w m h0),
    CuspSub.locRep_eq, locGL_sc m w h0, satEig_self _ m B hx.2.2.1] at h1
  have h2 : π.op (.fin (Matrix.GeneralLinearGroup.scalar (Fin m) (locU w (Units.mk0 ϖ h0)))) x =
      ((ω.1 (finId E (locU w (Units.mk0 ϖ h0))) : ℂˣ) : ℂ) • x := hc _ x
  rw [h1] at h2
  have h3 : ((B.prod : ℂˣ) : ℂ) = ((ω.1 (finId E (locU w (Units.mk0 ϖ h0))) : ℂˣ) : ℂ) :=
    smul_left_injective ℂ hx.1 h2
  rw [h3]
  exact hω _

end PositivityTheory.RgJS
