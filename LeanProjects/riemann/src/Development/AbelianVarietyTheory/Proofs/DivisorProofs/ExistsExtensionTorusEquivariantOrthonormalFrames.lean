import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFramesStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.TorusExt

open ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem value_indep (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ)
    (hF : ∀ y, IsUnitFr X y → ∀ c ∈ Bor X.Ψ r, IsUnitFr X (rmul y c) → F (rmul y c) = bchar la c * F y)
    {y y' b b' : Frame X.Ψ r} (hy : IsUnitFr X y) (hy' : IsUnitFr X y') (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r)
    (h : rmul y b = rmul y' b') : bchar la b * F y = bchar la b' * F y' := by
  have hi := ExtFPf.invF_mem X hb'
  have hc := ExtFPf.mul_mem X hb hi
  have e : rmul y (rmul b (ExtFPf.invF X b')) = y' := by
    rw [← ExtFPf.rmul_assoc, h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb', ExtFPf.rmul_oneF]
  have h1 := hF y hy _ hc (by rw [e]; exact hy')
  rw [e, ExtFPf.bchar_mul X la hb hi] at h1
  have h2 : bchar la b' * bchar la (ExtFPf.invF X b') = 1 := by
    rw [← ExtFPf.bchar_mul X la hb' hi, ExtFPf.rmul_invF X hb', ExtFPf.bchar_oneF]
  rw [h1]
  linear_combination (-(bchar la b * F y)) * h2

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ), (∀ y, IsUnitFr X y → ∀ t : X.Ψ → Fin r → ℝ, F (rmul y (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) = bchar la (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) * F y) → ∃ Q : Frame X.Ψ r → ℂ, (∀ y, IsUnitFr X y → Q y = F y) ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x := by
  intro E _ _ _ r X la F hF
  obtain ⟨-, hex, huniq, -⟩ := GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames E r X
  have hF' : ∀ y, IsUnitFr X y → ∀ c ∈ Bor X.Ψ r, IsUnitFr X (rmul y c) → F (rmul y c) = bchar la c * F y := by
    intro y hy c hc hyc
    obtain ⟨t, rfl⟩ := huniq y hy c hc hyc
    exact hF y hy t
  let D : Frame X.Ψ r → Prop := fun x => ∃ p : Frame X.Ψ r × Frame X.Ψ r,
    IsUnitFr X p.1 ∧ p.2 ∈ Bor X.Ψ r ∧ x = rmul p.1 p.2
  let Q : Frame X.Ψ r → ℂ := fun x => if h : D x then bchar la h.choose.2 * F h.choose.1 else 0
  have hQ : ∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, Q (rmul y b) = bchar la b * F y := by
    intro y hy b hb
    have hD : D (rmul y b) := ⟨(y, b), hy, hb, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hD.choose_spec
    show (if h : D (rmul y b) then bchar la h.choose.2 * F h.choose.1 else 0) = _
    rw [dif_pos hD]
    exact (value_indep X la F hF' hy h1 hb h2 h3).symm
  refine ⟨Q, fun y hy => ?_, fun x hx b hb => ?_⟩
  · have := hQ y hy _ (ExtFPf.oneF_mem X)
    rwa [ExtFPf.rmul_oneF, ExtFPf.bchar_oneF, one_mul] at this
  · obtain ⟨y, hy, c, hc, rfl⟩ := hex x hx
    rw [ExtFPf.rmul_assoc, hQ y hy _ (ExtFPf.mul_mem X hc hb), hQ y hy c hc, ExtFPf.bchar_mul X la hc hb]
    ring

end GlobalTheory.HolRead.TorusExt
