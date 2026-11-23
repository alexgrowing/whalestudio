import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ContPf

def PC (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x) ∧
  ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
    ∃ (k : J) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0

def ContAff : Prop := Hyp → ∀ (X : Scheme.{0}) [IsAffine X], PC X

def ContStep : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PC X

def ContInd : Prop := ∀ (P : Scheme.{0} → Prop), (∀ (X : Scheme.{0}) [IsAffine X], P X) →
  (∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) → U ⊔ V = ⊤ →
    P U.toScheme → P V.toScheme → P (U ⊓ V).toScheme → P X) →
  ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X], P X

theorem Cont_of (hMV : MV) (hA : ContAff) (hS : ContStep) (hI : ContInd) : Cont := by
  intro h q J _ _ D c hc ha hcs hqs hu n i
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have := hcs j0
  have := hqs j0
  have key : PC (D.obj j0) := hI PC (fun X _ => hA h X) (fun X U V hU hV hUV pU pV pW => hS h hMV X U V hU hV hUV pU pV pW)
    (D.obj j0)
  exact key q D c hc ha hcs hqs hu j0 ⟨Iso.refl _⟩ n i

end LateralTheory.E.ContPf
