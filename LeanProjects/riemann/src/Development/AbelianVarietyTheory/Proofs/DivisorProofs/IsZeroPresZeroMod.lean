import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobCokernelSmulHomPow

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains

namespace GlobalTheory.FrobFilt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
  (B : GlobalTheory.Vert.Model O)

def frob : B.X.Modules ⥤ B.X.Modules :=
  Scheme.Modules.pullback (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out
      (FrobQuot.natCast_eq_zero_fibI p B) ≫ (fibI p B).subschemeι) ⋙
    Scheme.Modules.pushforward (fibI p B).subschemeι

variable {p B} in

theorem isFrob_iff {F F' : B.X.Modules} : IsFrob p F F' ↔ Nonempty (F' ≅ (frob p B).obj F) :=
  ⟨fun ⟨_, e⟩ => e, fun e => ⟨FrobQuot.natCast_eq_zero_fibI p B, e⟩⟩

def IsGenSpecial (x : B.X) : Prop := x ∉ B.gen ∧ ∀ y : B.X, y ∉ B.gen → y ⤳ x → y = x

def NoEmb (F : B.X.Modules) : Prop :=
  ∀ (U V : B.X.Opens) (h : V ≤ U), (∀ x ∈ U, IsGenSpecial B x → x ∈ V) →
    Function.Injective ((Scheme.Modules.presheaf F).map (homOfLE h).op)

instance : (frob p B).Additive := inferInstanceAs ((_ ⋙ _).Additive)

variable {B}

theorem kills_of_iso {g : Γ(B.X, ⊤)} {F G : B.X.Modules} (h : Kills g F) (e : F ≅ G) : Kills g G := by
  unfold Kills at *
  have := smulHom_comp e.hom g
  rw [h, zero_comp] at this
  have h2 : e.inv ≫ e.hom ≫ smulHom G g = 0 := by rw [← this, comp_zero]
  simpa using h2

theorem NoEmb.of_iso {F G : B.X.Modules} (h : NoEmb B F) (e : F ≅ G) : NoEmb B G := by
  intro U V hVU hV s t hst
  have nat : ∀ u : Γ(G, U), (e.inv.app V) ((Scheme.Modules.presheaf G).map (homOfLE hVU).op u) =
      (Scheme.Modules.presheaf F).map (homOfLE hVU).op (e.inv.app U u) := fun u =>
    ConcreteCategory.congr_hom (e.inv.mapPresheaf.naturality (homOfLE hVU).op) u
  have h1 : e.inv.app U s = e.inv.app U t := h U V hVU hV (by rw [← nat, ← nat, hst])
  have h2 := congrArg (e.hom.app U) h1
  have h3 : ∀ u : Γ(G, U), e.hom.app U (e.inv.app U u) = u := fun u => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id,
      Scheme.Modules.Hom.id_app]
    rfl
  rwa [h3, h3] at h2

theorem isZero_frob_obj (p : ℕ) [Fact p.Prime] {F : B.X.Modules} (hF : IsZero F) : IsZero ((frob p B).obj F) :=
  Functor.map_isZero (Scheme.Modules.pushforward (fibI p B).subschemeι)
    (Functor.map_isZero (Scheme.Modules.pullback (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out
      (FrobQuot.natCast_eq_zero_fibI p B) ≫ (fibI p B).subschemeι)) hF)

variable (B) in

def presZero : Pres B where
  r := 1
  E := QCoh.structureModule B.X
  E' := QCoh.structureModule B.X
  vb := VB.isVB_structureModule _
  vb' := VB.isVB_structureModule _
  ψ := 𝟙 _
  iso := by rw [CategoryTheory.Functor.map_id]; infer_instance

theorem isZero_presZero_mod : IsZero (presZero B).mod :=
  isZero_cokernel_of_epi (𝟙 (QCoh.structureModule B.X))

end GlobalTheory.FrobFilt
