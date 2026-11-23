import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliser
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

noncomputable section

namespace GlobalTheory.BCT.StTw2Add

section Generic

variable {G : Type} [Group G]

theorem twRel_equiv (θ : G →* G) : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g := by
  refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [map_inv, inv_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by simp only [map_mul, mul_inv_rev]; group⟩

theorem twCl_eq_iff (θ : G →* G) (x y : G) :
    (Quot.mk _ x : TwCl θ) = Quot.mk _ y ↔ ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun h => (twRel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem mk_rep (θ : G →* G) (c : TwCl θ) : (Quot.mk _ c.rep : TwCl θ) = c := Quot.out_eq c

theorem rep_mk_iff (θ : G →* G) (P : G → Prop) (hP : ∀ x g, P (g⁻¹ * x * θ g) ↔ P x) (x : G) :
    P (TwCl.rep (θ := θ) (Quot.mk _ x)) ↔ P x := by
  obtain ⟨g, hg⟩ := (twCl_eq_iff θ _ _).1 (mk_rep θ (Quot.mk _ x : TwCl θ))
  have h := hP (TwCl.rep (θ := θ) (Quot.mk _ x)) g
  rw [← hg] at h
  exact h.symm

variable [TopologicalSpace G]

variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem finite_prod (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (P₁ : G₁ → Prop) (P₂ : G₂ → Prop)
    (h₁ : ∀ x g, P₁ (g⁻¹ * x * θ₁ g) ↔ P₁ x) (h₂ : ∀ x g, P₂ (g⁻¹ * x * θ₂ g) ↔ P₂ x)
    (f₁ : {c : TwCl θ₁ | P₁ c.rep}.Finite) (f₂ : {c : TwCl θ₂ | P₂ c.rep}.Finite) :
    {c : TwCl (θ₁.prodMap θ₂) | P₁ c.rep.1 ∧ P₂ c.rep.2}.Finite := by
  refine Set.Finite.of_finite_image (f := fun c : TwCl (θ₁.prodMap θ₂) =>
    ((Quot.mk _ c.rep.1 : TwCl θ₁), (Quot.mk _ c.rep.2 : TwCl θ₂))) ((f₁.prod f₂).subset ?_) ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨(rep_mk_iff θ₁ P₁ h₁ _).2 hc.1, (rep_mk_iff θ₂ P₂ h₂ _).2 hc.2⟩
  · intro c _ d _ hcd
    obtain ⟨g₁, hg₁⟩ := (twCl_eq_iff θ₁ _ _).1 (congrArg Prod.fst hcd)
    obtain ⟨g₂, hg₂⟩ := (twCl_eq_iff θ₂ _ _).1 (congrArg Prod.snd hcd)
    rw [← mk_rep _ c, ← mk_rep _ d]
    exact Quot.sound ⟨(g₁, g₂), Prod.ext hg₁ hg₂⟩

end Generic

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem charpoly_nrmL_twConj (hU : Unr E) (n : ℕ) (w : Pl E) (x g : GLw n w) :
    (nrmL n w (g⁻¹ * x * thL n w g)).val.charpoly = (nrmL n w x).val.charpoly := by
  rw [GlobalTheory.LocFin.nrmL_twConj hU, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

theorem isOpen_isCompact_KK (a b : ℕ) (w : Pl E) :
    IsOpen (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) ∧
    IsCompact (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
  rw [Subgroup.coe_prod]
  exact ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1,
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2⟩

end Local

end GlobalTheory.BCT.StTw2Add
