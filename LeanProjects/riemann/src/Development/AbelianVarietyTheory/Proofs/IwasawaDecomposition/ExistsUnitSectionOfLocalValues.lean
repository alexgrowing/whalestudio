import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FieldPtGlue

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X}

theorem valF_ne_zero_iff {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF x U a ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dif_pos h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  rw [e3]
  constructor
  · intro hne
    exact (Scheme.basicOpen_of_isUnit _ ((Ne.isUnit hne).map _)).ge
  · intro hle h0
    rw [h0, map_zero, Scheme.basicOpen_zero] at hle
    exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

theorem valF_restrict {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem valF_sub {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valF x U (a - b) = valF x U a - valF x U b := by
  simp only [valF, dif_pos h, map_sub]

theorem le_preimage_iff (U : X.Opens) : ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint F) ∈ U := by
  constructor
  · intro h
    exact h (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)
  · intro h y _
    have : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
    subst this
    exact h

end Val

noncomputable def resPt (X : Scheme.{0}) (z : X) : Sp (X.residueField z : Type) ⟶ X := X.fromSpecResidueField z

theorem resPt_le_iff (X : Scheme.{0}) (z : X) (U : X.Opens) : ⊤ ≤ resPt X z ⁻¹ᵁ U ↔ z ∈ U := by
  rw [le_preimage_iff]
  have : resPt X z (IsLocalRing.closedPoint (X.residueField z : Type)) = z :=
    Scheme.fromSpecResidueField_apply z _
  rw [this]

theorem section_ext {X : Scheme.{0}} [IsReduced X] {U : X.Opens} (a b : Γ(X, U))
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → valF w U a = valF w U b) : a = b := by
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro z hz
  have hU : ⊤ ≤ resPt X z ⁻¹ᵁ U := (resPt_le_iff X z U).2 (X.basicOpen_le _ hz)
  have h1 := (valF_ne_zero_iff hU (a - b)).2 ((resPt_le_iff X z _).2 hz)
  rw [valF_sub hU, h _ _ hU, sub_self] at h1
  exact absurd rfl h1

theorem exists_unit_of_locally : ∀ (X : Scheme.{0}) [IsReduced X] (U : X.Opens) (P : ∀ (k : Type) [Field k], (Sp k ⟶ X) → k → Prop), (∀ (k : Type) [Field k] (w : Sp k ⟶ X) (a a' : k), ⊤ ≤ w ⁻¹ᵁ U → P k w a → P k w a' → a = a') → (∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → ¬ P k w 0) → (∀ z ∈ U, ∃ (V : X.Opens) (s : Γ(X, V)), z ∈ V ∧ V ≤ U ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ V → P k w (valF w V s)) → ∃ s : Γ(X, U)ˣ, ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → P k w (valF w U s.val) := by
  intro X _ U P huniq hne hloc
  choose V s hzV hVU hP using hloc
  let V' : U → X.Opens := fun z => V z.1 z.2
  let s' : ∀ z : U, Γ(X, V' z) := fun z => s z.1 z.2
  have hcov : U ≤ iSup V' := fun z hz =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzV z hz⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf V' s' := by
    intro i j
    refine section_ext (X := X) (U := V' i ⊓ V' j) _ _ fun k _ w hw => ?_
    have hi : ⊤ ≤ w ⁻¹ᵁ V' i := fun q hq => (hw hq).1
    have hj : ⊤ ≤ w ⁻¹ᵁ V' j := fun q hq => (hw hq).2
    refine (valF_restrict inf_le_left hw (s' i)).trans
      (Eq.trans ?_ (valF_restrict inf_le_right hw (s' j)).symm)
    exact huniq k w _ _ (fun q hq => hVU i.1 i.2 (hi hq)) (hP i.1 i.2 k w hi) (hP j.1 j.2 k w hj)
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' V' U (fun i => homOfLE (hVU i.1 i.2)) hcov s' hcomp
  have key : ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → P k w (valF w U t) := by
    intro k _ w hw
    have hz := (le_preimage_iff U).1 hw
    have hV : ⊤ ≤ w ⁻¹ᵁ V _ hz := (le_preimage_iff _).2 (hzV _ hz)
    have e : valF w U t = valF w (V _ hz) (s _ hz) :=
      (valF_restrict (hVU _ hz) hV t).symm.trans (congrArg (valF w (V _ hz)) (ht ⟨_, hz⟩))
    rw [e]
    exact hP _ hz k w hV
  have hu : IsUnit (M := Γ(X, U)) t := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    have hU : ⊤ ≤ resPt X z ⁻¹ᵁ U := (resPt_le_iff X z U).2 hz
    have h0 : valF (resPt X z) U t ≠ 0 := fun h0 => hne _ _ hU (h0 ▸ key _ _ hU)
    have h1 := (resPt_le_iff X z _).1 ((valF_ne_zero_iff hU t).1 h0)
    exact (X.mem_basicOpen t z hz).1 h1
  exact ⟨hu.unit, key⟩

end GlobalTheory.FieldPtGlue
