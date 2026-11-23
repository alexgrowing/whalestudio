import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem label_le_preserves_splitting (h₁ : LiftOk) (h₂ : LiftBlocks) {a b : Lbl} (ha : a.Ok) (hab : a.Le b) :
    b.Ok ∧ b.rk = a.rk ∧ ∀ Q, b.Splits Q → a.Splits Q ∧ b.blocks Q = a.blocks Q := by
  induction hab with
  | refl => exact ⟨ha, rfl, fun Q hQ => ⟨hQ, rfl⟩⟩
  | @tail m c _ hstep ih =>
    obtain ⟨l, hl, rfl⟩ := hstep
    obtain ⟨hb, hrk, hS⟩ := ih
    obtain ⟨hc, hrk'⟩ := h₁ m l hl hb
    refine ⟨hc, hrk'.trans hrk, fun Q hQ => ?_⟩
    obtain ⟨hbQ, hblk⟩ := h₂ m l Q hl hb hQ
    obtain ⟨haQ, hblk'⟩ := hS Q hbQ
    exact ⟨haQ, hblk.trans hblk'⟩

theorem UpperTheory.Gal.InertialTypesAlt.leTop :
    LiftOk → LiftBlocks → LeRank → LeTop := by
  intro h₁ h₂ h₃ a b ha hab hs
  obtain ⟨hb, hrk, hS⟩ := label_le_preserves_splitting h₁ h₂ ha hab
  obtain ⟨f, hf, hq, hd⟩ := hs
  obtain ⟨c, hc, hbq, hp⟩ := h₃ a b ha hab
  have hcf : c = f := Nat.pow_right_injective ha.1 (hbq.symm.trans hq)
  subst hcf
  have hone : ∀ p ∈ b.L, p.1 = 1 := by
    intro p hpL
    obtain ⟨r, hr, hpr⟩ := hp p hpL
    have hr0 : 0 < r.1 := (ha.2.2 r hr).1
    rw [Nat.gcd_eq_left (hd r hr)] at hpr
    exact Nat.eq_of_mul_eq_mul_right hr0 (by simpa using hpr)
  refine ⟨hb, hrk, hone, (hS b.q ⟨1, Nat.one_pos, (pow_one _).symm, fun p hpL => ?_⟩).2⟩
  rw [hone p hpL]
