import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CharValsFixed

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∀ (σ : F →+* F), (∀ t ∈ T, σ t = t) → ∀ (g : GtPtF D F) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ (S : Set D.X), AddSubgroup.closure S = ⊤ → (∀ χ ∈ S, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → ∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) := by
  intro R _ _ D F _ _ T _ φ₁ hφ₁ J₀ h₀ J hJ eJ σ hσ g b hb hbA S hS hSfix
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ₁) := Over.homMk (spMap T.subtype) (by
    show spMap T.subtype ≫ spMap φ₁ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ₁)
  let w : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ →* Fˣ :=
    (Units.map σ.toMonoidHom).comp (sig F) * (sig F)⁻¹
  have hwv : ∀ u, ((w u : Fˣ) : F) = σ (sig F u : F) * ((sig F u)⁻¹ : Fˣ) := fun u => rfl
  have hw1 : ∀ u, w u = 1 ↔ σ (sig F u : F) = (sig F u : F) := fun u => by
    constructor
    · intro h
      have e := congrArg Units.val h
      rw [hwv, Units.val_one] at e
      calc σ (sig F u : F) = σ (sig F u : F) * ((sig F u)⁻¹ : Fˣ) * (sig F u : F) := by
            rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]
        _ = (sig F u : F) := by rw [e, _root_.one_mul]
    · intro h
      apply Units.ext
      rw [hwv, h, Units.mul_inv, Units.val_one]
  have hw : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (Over.mk (spMap φ₁)).left ⟶ Y),
      w (val t (ρ.left ≫ r) (closedPoint F) J) = 1 := by
    intro Y K _ φ ε t r
    obtain ⟨u, hu⟩ := val_integral T.subtype h₀ eJ t r
    refine (hw1 _).2 ?_
    have hu' : (sig F (val t (ρ.left ≫ r) (closedPoint F) J) : F) = T.subtype u := hu
    rw [hu']
    exact hσ _ (u : T).2
  let b' : Over.mk (spMap φ₁) ⟶ D.P.A := Over.homMk b hbA
  have hgb : g.b = ρ ≫ b' := by
    ext1
    exact hb.symm
  have hth : ∀ χ χ', w (th D (closedPoint F) J (cP D _ χ) (cP D _ χ') g.b) = 1 := fun χ χ' => by
    rw [hgb, ← comp_cP D ρ χ, ← comp_cP D ρ χ']
    exact w_th ρ w hw _ _ _
  let H : AddSubgroup D.X :=
    { carrier := {χ | w (charVal g χ (closedPoint F) J) = 1}
      zero_mem' := by
        show w _ = 1
        rw [charVal_zero g hJ, map_one]
      add_mem' := fun {χ χ'} (h : w _ = 1) (h' : w _ = 1) => by
        show w _ = 1
        have e := congrArg w (charVal_add g hJ χ χ')
        rw [map_mul, map_mul, hth, h, h', _root_.mul_one, _root_.mul_one] at e
        exact e
      neg_mem' := fun {χ} (h : w _ = 1) => by
        show w _ = 1
        have e := congrArg w (charVal_add g hJ χ (-χ))
        rw [map_mul, map_mul, hth, h, _root_.mul_one, _root_.one_mul, add_neg_cancel, charVal_zero g hJ,
          map_one] at e
        exact e.symm }
  have hSH : S ⊆ H := fun χ hχ => (hw1 _).2 (hSfix χ hχ)
  have hH : H = ⊤ := eq_top_iff.2 (hS ▸ (AddSubgroup.closure_le H).2 hSH)
  intro χ
  exact (hw1 _).1 (show χ ∈ H by rw [hH]; trivial)

end GlobalTheory.CharValsFixed
