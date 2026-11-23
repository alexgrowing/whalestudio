import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericRatSec

open ReciprocityTheory.ChartRestriction.G.DVR (res_res' pullU_res res_pullU_eq)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

abbrev unifOn {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O)) (ϖ : O) : Γ(Z, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)

theorem isOpenImmersion_genericι {ϖ : O} (hϖ : Irreducible ϖ) {Z : Scheme.{0}}
    (f : Z ⟶ Spec (.of O)) : IsOpenImmersion (genericι f) := by
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.isOpenImmersion_frac hϖ
  exact inferInstanceAs (IsOpenImmersion (pullback.fst f (Spec.map _)))

theorem opensRange_genericι {ϖ : O} (hϖ : Irreducible ϖ) {Z : Scheme.{0}}
    (f : Z ⟶ Spec (.of O)) :
    haveI := isOpenImmersion_genericι hϖ f
    (genericι f).opensRange = Z.basicOpen (unifOn f ϖ) := by
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.isOpenImmersion_frac hϖ
  change (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))).opensRange = _
  rw [Scheme.Hom.opensRange_pullbackFst,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.opensRange_frac hϖ, Scheme.preimage_basicOpen_top]

theorem gen_mem_basicOpen {ϖ : O} (hϖ : Irreducible ϖ) {Z : Scheme.{0}} [IsIntegral Z]
    (f : Z ⟶ Spec (.of O)) [Flat f] : genericPoint Z ∈ Z.basicOpen (unifOn f ϖ) := by
  set x := genericPoint Z
  set r' := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ with hr'def
  have hr' : r' ≠ 0 := by
    intro h0
    apply hϖ.ne_zero
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom h0
    rwa [hr'def, Iso.inv_hom_id_apply, map_zero] at this
  set g := (Spec (.of O)).presheaf.germ ⊤ (f.base x) trivial r' with hgdef
  have hg : g ≠ 0 := fun h0 =>
    hr' (germ_injective_of_isIntegral (Spec (.of O)) (U := ⊤) (f.base x) trivial
      (h0.trans (map_zero _).symm))
  letI := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat _ (Z.presheaf.stalk x) := Flat.stalkMap f x
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Z.presheaf.stalk x)
    (mem_nonZeroDivisors_of_ne_zero hg)
  rw [Scheme.mem_basicOpen_top]
  have h1 : (f.stalkMap x).hom g = Z.presheaf.germ ⊤ x trivial (unifOn f ϖ) :=
    Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial r'
  rw [← h1]
  refine (isUnit_iff_ne_zero (G₀ := Z.functionField)).2 (fun h0 => ?_)
  have e : g • (1 : Z.presheaf.stalk x) = g • 0 := by
    rw [smul_zero, Algebra.smul_def, mul_one]; exact h0
  exact one_ne_zero (α := Z.functionField) (hreg e)

section Main

theorem res_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (u : Γ(X, U)ˣ) : res h u = u := by
  ext
  simp [res]

theorem res_injective {X : Scheme.{0}} {A B : X.Opens} (h : A ≤ B) (h' : B ≤ A) :
    Function.Injective (res h) := fun a b e => by
  have := congrArg (res h') e
  rwa [res_res', res_res', res_self, res_self] at this

variable {ϖ : O} {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O))

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem preimage_le (D : LB Z) (i : D.ι) (W : Z.Opens) (hW : W ≤ D.U i) :
    genericι f ⁻¹ᵁ W ≤ (D.pull (genericι f)).U (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hW hy

theorem fnOf_res [IsIntegral Z] {U V : Z.Opens} (e : V ≤ U) (h : genericPoint Z ∈ V) (u : Γ(Z, U)ˣ) :
    fnOf V h (res e u : Γ(Z, V)) = fnOf U (e h) u :=
  Z.presheaf.germ_res_apply (homOfLE e) _ h _

variable (hϖ : Irreducible ϖ)
include hϖ

theorem exists_pre (W : Z.Opens) (hW : W ≤ Z.basicOpen (unifOn f ϖ))
    (u : Γ(genericFibre f, genericι f ⁻¹ᵁ W)ˣ) : ∃ a : Γ(Z, W)ˣ, pullU (genericι f) W a = u := by
  haveI := isOpenImmersion_genericι hϖ f
  haveI := Scheme.Hom.isIso_app (genericι f) W (hW.trans (opensRange_genericι hϖ f).ge)
  let e := RingEquiv.ofBijective ((genericι f).app W).hom (ConcreteCategory.bijective_of_isIso _)
  refine ⟨Units.map e.symm.toMonoidHom u, Units.ext ?_⟩
  show ((genericι f).app W).hom (e.symm u) = u
  exact e.apply_symm_apply _

theorem app_injective (W : Z.Opens) (hW : W ≤ Z.basicOpen (unifOn f ϖ)) :
    Function.Injective ((genericι f).app W).hom := by
  haveI := isOpenImmersion_genericι hϖ f
  haveI := Scheme.Hom.isIso_app (genericι f) W (hW.trans (opensRange_genericι hϖ f).ge)
  exact (ConcreteCategory.bijective_of_isIso _).1

theorem pullU_injective (W : Z.Opens) (hW : W ≤ Z.basicOpen (unifOn f ϖ)) :
    Function.Injective (pullU (genericι f) W) := fun _ _ h =>
  Units.ext (app_injective f hϖ W hW (congrArg Units.val h))

def locU (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι) :
    Γ(Z, D.U i ⊓ Z.basicOpen (unifOn f ϖ))ˣ :=
  (exists_pre f hϖ _ inf_le_right
    (res (preimage_le f D i _ inf_le_left) (sig.s (fun _ => i)))).choose

theorem pullU_locU (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι) :
    pullU (genericι f) _ (locU f hϖ D sig i) =
      res (preimage_le f D i _ inf_le_left) (sig.s (fun _ => i)) :=
  (exists_pre f hϖ _ inf_le_right _).choose_spec

theorem pullU_res_locU (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι) (W : Z.Opens)
    (hW : W ≤ D.U i ⊓ Z.basicOpen (unifOn f ϖ)) :
    pullU (genericι f) W (res hW (locU f hϖ D sig i)) =
      res (preimage_le f D i W (hW.trans inf_le_left)) (sig.s (fun _ => i)) := by
  rw [pullU_res, pullU_locU, res_res']

variable [IsIntegral Z]

open Classical in

def tau (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι) : Z.functionFieldˣ :=
  if h : genericPoint Z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ) then
    Units.map (fnOf _ h).toMonoidHom (locU f hϖ D sig i) else 1

theorem val_tau (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι)
    (h : genericPoint Z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ)) :
    (tau f hϖ D sig i : Z.functionField) = fnOf _ h (locU f hϖ D sig i) := by
  rw [tau, dif_pos h]; rfl

theorem isRatSec_tau [Flat f] (D : LB Z) (sig : (D.pull (genericι f)).Gen) (hsig : sig.IsGen) :
    IsRatSec D (tau f hϖ D sig) := by
  intro i j h
  have hV := gen_mem_basicOpen hϖ f
  set V := Z.basicOpen (unifOn f ϖ) with hVdef
  have hi : genericPoint Z ∈ D.U i ⊓ V := ⟨h.1, hV⟩
  have hj : genericPoint Z ∈ D.U j ⊓ V := ⟨h.2, hV⟩
  have hW : genericPoint Z ∈ D.U i ⊓ D.U j ⊓ V := ⟨h, hV⟩
  have claim : res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        D.U i ⊓ D.U j ⊓ V ≤ D.U i ⊓ V) (locU f hϖ D sig i) =
      res (inf_le_left : D.U i ⊓ D.U j ⊓ V ≤ D.U i ⊓ D.U j) (D.g i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        D.U i ⊓ D.U j ⊓ V ≤ D.U j ⊓ V) (locU f hϖ D sig j) := by
    apply pullU_injective f hϖ _ inf_le_right
    rw [map_mul, pullU_res_locU, pullU_res_locU, pullU_res]
    have e := congrArg (res (fun _ hy => ⟨(preimage_le f D i _ (inf_le_left.trans inf_le_left)) hy,
        (preimage_le f D j _ (inf_le_left.trans inf_le_right)) hy⟩ :
        genericι f ⁻¹ᵁ (D.U i ⊓ D.U j ⊓ V) ≤
          (D.pull (genericι f)).U (fun _ => i) ⊓ (D.pull (genericι f)).U (fun _ => j)))
      (hsig (fun _ => i) (fun _ => j))
    rw [map_mul] at e
    erw [res_res', res_res'] at e
    erw [e]
    congr 1
    show res _ (∏ _k : PUnit, (res _ (pullU (genericι f) _ (D.g i j))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    erw [res_res']
  have e := congrArg (fun u : Γ(Z, D.U i ⊓ D.U j ⊓ V)ˣ => fnOf _ hW (u : Γ(Z, _))) claim
  simp only [Units.val_mul, map_mul, fnOf_res] at e
  rw [val_tau f hϖ D sig i hi, val_tau f hϖ D sig j hj]
  exact e

theorem unitAt_tau (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι) (z : Z)
    (hz : z ∈ D.U i) (hz' : z ∈ Z.basicOpen (unifOn f ϖ)) :
    UnitAt z (tau f hϖ D sig i : Z.functionField) := by
  have h : genericPoint Z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ) := gen_mem (show z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ) from ⟨hz, hz'⟩)
  rw [val_tau f hϖ D sig i h]
  exact unitAt_fnOf (show z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ) from ⟨hz, hz'⟩) h _

end Main

section Pow

variable {ϖ : O} {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O)) (hϖ : Irreducible ϖ)

theorem val_constUnit :
    ((constUnit (genericStr f) (unifUnit ϖ hϖ) : Γ(genericFibre f, ⊤)ˣ) : Γ(genericFibre f, ⊤)) =
      (genericι f).appTop.hom (unifOn f ϖ) := by
  show (genericStr f).appTop.hom ((Scheme.ΓSpecIso (.of (FractionRing O))).inv.hom
    (algebraMap O (FractionRing O) ϖ)) = _
  have h1 : (Scheme.ΓSpecIso (.of (FractionRing O))).inv.hom (algebraMap O (FractionRing O) ϖ) =
      (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))).appTop.hom
        ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ) :=
    congrArg (fun t => t.hom ϖ)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O (FractionRing O))))
  have h2 := congrArg (fun t => t.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ))
    (pullback.condition (f := f) (g := Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))
  rw [h1]
  exact h2.symm

include hϖ

theorem exists_unif (W : Z.Opens) (hWV : W ≤ Z.basicOpen (unifOn f ϖ))
    (hle : genericι f ⁻¹ᵁ W ≤ ⊤) [IsIntegral Z] :
    ∃ b : Γ(Z, W)ˣ, pullU (genericι f) W b = res hle (constUnit (genericStr f) (unifUnit ϖ hϖ)) ∧
      ∀ hW : genericPoint Z ∈ W, fnOf W hW b = fnOf ⊤ trivial (unifOn f ϖ) := by
  obtain ⟨b, hb⟩ := exists_pre f hϖ W hWV (res hle (constUnit (genericStr f) (unifUnit ϖ hϖ)))
  refine ⟨b, hb, fun hW => ?_⟩
  have e : (b : Γ(Z, W)) = (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (unifOn f ϖ) := by
    apply app_injective f hϖ W hWV
    refine (congrArg Units.val hb).trans ?_
    show ((genericFibre f).presheaf.map (homOfLE hle).op).hom
      ((constUnit (genericStr f) (unifUnit ϖ hϖ) : Γ(genericFibre f, ⊤)ˣ) : Γ(genericFibre f, ⊤)) = _
    rw [val_constUnit f hϖ]
    exact (congrArg (fun t => t.hom (unifOn f ϖ))
      (Scheme.Hom.naturality (genericι f) (homOfLE (le_top : W ≤ ⊤)).op)).symm
  rw [e]
  exact Z.presheaf.germ_res_apply (homOfLE le_top) _ hW _

theorem powEq_of [IsIntegral Z] (D : LB Z) (sig : (D.pull (genericι f)).Gen) (M : ℕ) (n : ℤ)
    (gen : (lbPow D M).Gen)
    (H : ∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
      fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (unifOn f ϖ) ^ n =
        (tau f hϖ D sig i : Z.functionField) ^ M) :
    PowEq f ϖ hϖ D sig M n gen := by
  intro j
  obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j PUnit.unit, funext fun _ => rfl⟩
  haveI := isOpenImmersion_genericι hϖ f
  have hle := preimage_le f D i (D.U i ⊓ Z.basicOpen (unifOn f ϖ)) inf_le_left
  have hle' : (D.pull (genericι f)).U (fun _ => i) ≤
      genericι f ⁻¹ᵁ (D.U i ⊓ Z.basicOpen (unifOn f ϖ)) := fun y hy =>
    ⟨Set.mem_iInter.1 hy PUnit.unit,
      (opensRange_genericι hϖ f).le (show (genericι f).base y ∈ (genericι f).opensRange from ⟨y, rfl⟩)⟩
  apply res_injective hle hle'
  show res hle ((sig.s (fun _ => i)) ^ M) = res hle ((res _ (constUnit (genericStr f) (unifUnit ϖ hϖ))) ^ n *
    res _ (pullU (genericι f) (D.U i) (gen.s i)))
  obtain ⟨b, hb, hbf⟩ := exists_unif f hϖ (D.U i ⊓ Z.basicOpen (unifOn f ϖ)) inf_le_right le_top
  erw [map_mul, map_pow, map_zpow, ← pullU_locU f hϖ D sig i, res_res', res_res', ← hb,
    res_pullU_eq (genericι f) (inf_le_left : D.U i ⊓ Z.basicOpen (unifOn f ϖ) ≤ D.U i) _ le_rfl,
    res_self, ← map_pow, ← map_zpow, ← map_mul]
  congr 1
  by_cases hW : genericPoint Z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ)
  · apply Units.map_injective (f := (fnOf _ hW).toMonoidHom) (fnOf_injective _ hW)
    apply Units.ext
    simp only [map_pow, map_zpow, map_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [← val_tau f hϖ D sig i hW, hbf hW]
    erw [fnOf_res]
    rw [← H i hW.1, mul_comm]
    rfl
  · exact Units.ext (fn_ext fun h => (hW h).elim)

end Pow

theorem exists_ratSec : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)) (D : LB Z), Flat f → D.IsLB →
  ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
  ∃ τ : D.ι → Z.functionFieldˣ, IsRatSec D τ ∧
    (∀ (i : D.ι) (z : Z), z ∈ D.U i → z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
      UnitAt z (τ i : Z.functionField)) ∧
    ∀ (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen),
      (∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
        fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n =
          (τ i : Z.functionField) ^ M) →
      PowEq f ϖ hϖ D sig M n gen := by
  intro O _ _ _ ϖ hϖ Z _ f D hf _ sig hsig
  refine ⟨tau f hϖ D sig, isRatSec_tau f hϖ D sig hsig, fun i z hz hz' => unitAt_tau f hϖ D sig i z hz hz',
    fun M n gen H => powEq_of f hϖ D sig M n gen H⟩

end GlobalTheory.GenericRatSec
