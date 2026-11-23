import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobCokernelSmulHomPow

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains

namespace GlobalTheory.MixedLocalChains.ChainOne

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

abbrev sO (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    (Model.base O).X.Modules := GlobalTheory.QCoh.structureModule (Model.base O).X

theorem mono_smulHom_const {a : O} (ha : a ≠ 0) : Mono (smulHom (sO O) ((Model.base O).const a)) :=
  GlobalTheory.QCoh.mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun _ _ h =>
    (mul_cancel_left_mem_nonZeroDivisors ((Model.base O).isRegularFn_const ha W le_top)).1 h⟩

theorem gammaSpec_const (a : O) :
    (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom ((Model.base O).const a) = a := by
  change (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom (Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of O)))
    ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) = a
  simp

theorem kills_cokernel {a b : Γ((Model.base O).X, ⊤)} (h : a ∣ b) :
    Kills b (cokernel (smulHom (sO O) a)) := by
  obtain ⟨c, rfl⟩ := h
  unfold Kills
  rw [← cancel_epi (cokernel.π (smulHom (sO O) a)), comp_zero, ← smulHom_comp, smulHom_mul,
    Category.assoc, cokernel.condition, comp_zero]

theorem not_isZero_cokernel {a : O} (hu : ¬ IsUnit a) :
    ¬ IsZero (cokernel (smulHom (sO O) ((Model.base O).const a))) := fun h => by
  have : Epi (smulHom (sO O) ((Model.base O).const a)) := Preadditive.epi_of_isZero_cokernel _ h
  have := (VB.isVB_structureModule (Model.base O).X).isQuasicoherent
  haveI : IsAffine (Model.base O).X := inferInstanceAs (IsAffine (Spec (CommRingCat.of O)))
  obtain ⟨s, hs⟩ := QCoh.surjective_app_of_epi (smulHom (sO O) ((Model.base O).const a))
    (isAffineOpen_top _) (1 : Γ((Model.base O).X, ⊤))
  rw [smulHom_app_apply, restrictGlobal_top] at hs
  have h1 : IsUnit ((Model.base O).const a) := isUnit_iff_exists_inv.2 ⟨_, hs⟩
  have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom
  exact hu (by convert h2 using 1; exact (gammaSpec_const a).symm)

def presMul {a : O} (ha : a ≠ 0) : Pres (Model.base O) where
  r := 1
  E := sO O
  E' := sO O
  vb := VB.isVB_structureModule _
  vb' := VB.isVB_structureModule _
  ψ := smulHom (sO O) ((Model.base O).const a)
  iso := Model.isIso_genRes_map_smulHom (Z := Model.base O) (sO O) ha

def presId : Pres (Model.base O) where
  r := 1
  E := sO O
  E' := sO O
  vb := VB.isVB_structureModule _
  vb' := VB.isVB_structureModule _
  ψ := 𝟙 (sO O)
  iso := by rw [CategoryTheory.Functor.map_id]; infer_instance

section Chain

variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

variable (O) in

abbrev cst : O →+* Γ((Model.base O).X, ⊤) := algebraMap O Γ((Model.base O).X, ⊤)

end Chain

end GlobalTheory.MixedLocalChains.ChainOne
