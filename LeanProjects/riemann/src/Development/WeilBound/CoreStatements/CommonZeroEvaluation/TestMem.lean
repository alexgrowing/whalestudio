import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecDesc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
open NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace ModelDimension.Spread

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem spec_bor {Ω : Type} [Field Ω] [Algebra c.F Ω] {S₁ S₂ : Type} [CommRing S₁] [Algebra c.F S₁] [CommRing S₂]
    [Algebra c.F S₂] (φ₁ : S₁ →ₐ[c.F] Ω) (φ₂ : S₂ →ₐ[c.F] Ω) {y₁ : FrPt Xo c S₁} {y₂ : FrPt Xo c S₂}
    {z₁ z₂ : FrPt Xo c Ω} {t : Ix Dw → Ωˣ} (h₁ : FrMap φ₁ y₁ z₁) (h₂ : FrMap φ₂ y₂ z₂) (hb : FrBor t z₁ z₂)
    (A : Subring Ω) (hA₁ : ∀ r, φ₁ r ∈ A) (hA₂ : ∀ r, φ₂ r ∈ A) (hAt : ∀ k, (((t k)⁻¹ : Ωˣ) : Ω) ∈ A)
    {L : Type} [CommRing L] [Algebra c.F L] (ev : A →+* L) (ψ₁ : S₁ →ₐ[c.F] L) (ψ₂ : S₂ →ₐ[c.F] L)
    (e₁ : ∀ r, ψ₁ r = ev ⟨_, hA₁ r⟩) (e₂ : ∀ r, ψ₂ r = ev ⟨_, hA₂ r⟩) {w₁ w₂ : FrPt Xo c L}
    (k₁ : FrMap ψ₁ y₁ w₁) (k₂ : FrMap ψ₂ y₂ w₂) : ∃ t' : Ix Dw → Lˣ, FrBor t' w₁ w₂ := by
  have hL := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  have hc : ∀ a : c.F, algebraMap c.F Ω a ∈ A := fun a => by
    rw [← φ₁.commutes]; exact hA₁ _
  let D : Subalgebra c.F Ω := { A with algebraMap_mem' := hc }
  let evD : D →ₐ[c.F] L :=
    { toFun := fun x => ev ⟨x.1, x.2⟩
      map_one' := map_one ev
      map_mul' := fun x y => map_mul ev ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
      map_zero' := map_zero ev
      map_add' := fun x y => map_add ev ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
      commutes' := fun a => by
        rw [← ψ₁.commutes a, e₁]
        exact congrArg ev (Subtype.ext (φ₁.commutes a).symm) }
  let χ₁ : S₁ →ₐ[c.F] D := φ₁.codRestrict D hA₁
  let χ₂ : S₂ →ₐ[c.F] D := φ₂.codRestrict D hA₂
  obtain ⟨u₁, hu₁⟩ := hL.bc _ _ χ₁ y₁
  obtain ⟨u₂, hu₂⟩ := hL.bc _ _ χ₂ y₂
  have g₁ : FrMap D.val u₁ z₁ := frMap_cancel _ _ _ χ₁ D.val y₁ u₁ z₁ hu₁ h₁
  have g₂ : FrMap D.val u₂ z₂ := frMap_cancel _ _ _ χ₂ D.val y₂ u₂ z₂ hu₂ h₂
  obtain ⟨tD, hD, -⟩ := frBor_descend D.val Subtype.val_injective g₁ g₂ hb (fun k => ⟨⟨_, hAt k⟩, rfl⟩)
  have m₁ : FrMap evD u₁ w₁ := frMap_cancel _ _ _ χ₁ evD y₁ u₁ w₁ hu₁
    (by rw [show evD.comp χ₁ = ψ₁ from AlgHom.ext fun r => (e₁ r).symm]; exact k₁)
  have m₂ : FrMap evD u₂ w₂ := frMap_cancel _ _ _ χ₂ evD y₂ u₂ w₂ hu₂
    (by rw [show evD.comp χ₂ = ψ₂ from AlgHom.ext fun r => (e₂ r).symm]; exact k₂)
  exact ⟨_, frBorBC _ _ evD _ _ _ _ _ hD m₁ m₂⟩

theorem test_mem {K Ω : Type} [Field K] [CommRing Ω] [Algebra K Ω] (q : TRing K) (φ : q.R →ₐ[K] Ω) (A : Subring Ω)
    (hc : ∀ a : K, algebraMap K Ω a ∈ A) (hx : ∀ i, φ (Ideal.Quotient.mk q.I (MvPolynomial.X i)) ∈ A) (r : q.R) :
    φ r ∈ A := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : Ideal.Quotient.mk q.I (MvPolynomial.C a) = algebraMap K q.R a := rfl
    rw [this, φ.commutes]; exact hc a
  | add p p' hp hp' => rw [map_add, map_add]; exact A.add_mem hp hp'
  | mul_X p i hp => rw [map_mul, map_mul]; exact A.mul_mem hp (hx i)

def evAlg {K S Ω L : Type} [Field K] [CommRing S] [Algebra K S] [CommRing Ω] [Algebra K Ω] [CommRing L] [Algebra K L]
    (φ : S →ₐ[K] Ω) (A : Subring Ω) (hA : ∀ r, φ r ∈ A) (ev : A →+* L)
    (hc : ∀ (a : K) (h : algebraMap K Ω a ∈ A), ev ⟨_, h⟩ = algebraMap K L a) : S →ₐ[K] L :=
  { ev.comp (φ.toRingHom.codRestrict A hA) with
    commutes' := fun a => by
      have h : algebraMap K Ω a ∈ A := by rw [← φ.commutes]; exact hA _
      rw [← hc a h]
      exact congrArg ev (Subtype.ext (φ.commutes a)) }

end ModelDimension.Spread
