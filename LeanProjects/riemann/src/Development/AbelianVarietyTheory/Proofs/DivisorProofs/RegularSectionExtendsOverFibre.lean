import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReducedFibrePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSectionUnitStalkStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.PropZCore

theorem unitAt_zpow {X : Scheme.{0}} [IsIntegral X] {x : X} {g : X.functionField} (h : UnitAt x g)
    (n : ℤ) : UnitAt x (g ^ n) := by
  have hp : ∀ m : ℕ, UnitAt x (g ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero]; exact unitAt_one x
    | succ m ih => rw [pow_succ]; exact ih.mul h
  rcases n with m | m
  · rw [Int.ofNat_eq_coe, zpow_natCast]; exact hp m
  · rw [zpow_negSucc]; exact (hp _).inv

theorem gen_of_exponent : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D → genericPoint Z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  IsField Γ(reducedSpecialFibre f, ⊤) →
  (∀ (φ : Z.functionField) (x : Z),
    (∀ z : Z, z ⤳ x → IsDiscreteValuationRing (Z.presheaf.stalk z) → RegAt z φ) → RegAt x φ) →
  ∀ τ : D.ι → Z.functionFieldˣ, IsRatSec D τ →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) → UnitAt z (τ i : Z.functionField)) →
  ∀ (M : ℕ) (n : ℤ) (x₀ : Z), 1 ≤ M → x₀ ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → IsDiscreteValuationRing (Z.presheaf.stalk z) →
    RegAt z (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  (∀ i : D.ι, x₀ ∈ D.U i → UnitAt x₀ (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  ∃ gen : (lbPow D M).Gen, gen.IsGen ∧
    ∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
      fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n = (τ i : Z.functionField) ^ M := by
  have L1 := GlobalTheory.T.exists_reduced_fibre_point
  have L2 := GlobalTheory.T.exists_global_section_unit_stalk
  intro O _ _ _ ϖ hϖ Z _ f D hD hgen hfield hhart τ hτ hτu M n x₀ hM hx₀ hreg hunit
  set π := f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ) with hπ
  set P : Z.functionField := fnOf ⊤ trivial π with hP
  have hDLB : D.IsLB := hD.2.2.2.2.2.1
  obtain ⟨t, ht⟩ := hD.2.2.2.2.2.2
  obtain ⟨φ, hφ⟩ : ∃ φ : D.ι → Z.functionField, ∀ i, φ i = P ^ n * ((τ i : Z.functionField) ^ M)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hregU : ∀ i, ∀ z ∈ D.U i, RegAt z (φ i) := fun i z hz =>
    hhart _ z fun z' hz' hdvr => hφ i ▸ hreg i z' (hz'.mem_open (D.U i).isOpen hz) hdvr
  have ha : ∀ i, ∃ a : Γ(Z, D.U i), ∀ h, fnOf (D.U i) h a = φ i := by
    intro i
    by_cases h : genericPoint Z ∈ D.U i
    · obtain ⟨a, ha⟩ := exists_fnOf_eq h (hregU i)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose a ha using ha
  have hgne : ∀ i j (h : genericPoint Z ∈ D.U i ⊓ D.U j),
      fnOf _ h (D.g i j : Γ(Z, D.U i ⊓ D.U j)) ≠ 0 := fun i j h =>
    ((D.g i j).isUnit.map (fnOf _ h)).ne_zero
  have hφg : ∀ i j (h : genericPoint Z ∈ D.U i ⊓ D.U j),
      φ i * (fnOf _ h (D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M = φ j := by
    intro i j h
    have e := hτ i j h
    have h1 := hgne i j h
    rw [hφ, hφ, e, mul_pow, mul_inv, mul_comm (((fnOf _ h _) ^ M)⁻¹), mul_assoc, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ h1), mul_one]
  have key : ∀ i j (h : genericPoint Z ∈ D.U i ⊓ D.U j),
      (φ i)⁻¹ = (fnOf _ h (D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M * (φ j)⁻¹ := by
    intro i j h
    rw [← hφg i j h, mul_inv (φ i), mul_left_comm (_ ^ M) (φ i)⁻¹,
      mul_inv_cancel₀ (pow_ne_zero _ (hgne i j h)), mul_one]
  have hcompat : ∀ i j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (a i) *
      ((D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (a j) := by
    intro i j
    apply fn_ext
    intro h
    rw [map_mul, map_pow, fnOf_resG, fnOf_resG, ha, ha, hφg]
  obtain ⟨hh, hhu⟩ := L2 _ _ (reducedSpecialι f) D hDLB t ht M a hcompat
  have germUnit : ∀ i (z : Z) (hz : z ∈ D.U i), UnitAt z (φ i) ↔
      IsUnit ((Z.presheaf.germ (D.U i) z hz).hom (a i)) := by
    intro i z hz
    rw [← ha i (gen_mem hz), unitAt_fnOf_iff hz, Z.mem_basicOpen (a i) z hz]
  obtain ⟨i₀, hi₀⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hDLB x₀
  have hne : hh ≠ 0 := by
    intro h0
    obtain ⟨y₀, rfl⟩ := L1 O ϖ hϖ Z f x₀ hx₀
    obtain ⟨u, hu⟩ := hhu i₀ y₀ hi₀
    have h1 := ((germUnit i₀ _ hi₀).1 (hφ i₀ ▸ hunit i₀ hi₀)).map ((reducedSpecialι f).stalkMap y₀).hom
    have h2 := h1.mul u.isUnit
    rw [← hu, h0, map_zero] at h2
    exact not_isUnit_zero h2
  have hhunit : IsUnit hh := by
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
    exact IsUnit.of_mul_eq_one b hb
  have hspecial : ∀ i (z : Z) (hz : z ∈ D.U i), z ∉ Z.basicOpen π → UnitAt z (φ i) := by
    intro i z hz hzπ
    obtain ⟨y, rfl⟩ := L1 O ϖ hϖ Z f z hzπ
    obtain ⟨u, hu⟩ := hhu i y hz
    have h1 := hhunit.map ((reducedSpecialFibre f).presheaf.germ ⊤ y trivial).hom
    rw [hu] at h1
    have h2 := h1.mul (u⁻¹).isUnit
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] at h2
    have : IsLocalHom ((reducedSpecialι f).stalkMap y).hom := inferInstance
    exact (germUnit i _ hz).2 (isUnit_of_map_unit _ _ h2)
  have hgenU : UnitAt (genericPoint Z) P := (unitAt_fnOf_iff (U := ⊤) trivial trivial π).2 hgen
  have hPne : P ≠ 0 := hgenU.ne_zero
  have hall : ∀ i, ∀ z ∈ D.U i, UnitAt z (φ i)⁻¹ := by
    intro i z hz
    refine UnitAt.inv ?_
    by_cases hzπ : z ∈ Z.basicOpen π
    · have h3 := unitAt_zpow (hτu i z hz hzπ) M
      rw [zpow_natCast] at h3
      rw [hφ]
      exact (unitAt_zpow ((unitAt_fnOf_iff (U := ⊤) trivial trivial π).2 hzπ) n).mul h3.inv
    · exact hspecial i z hz hzπ
  choose u hu using fun i => exists_unit_fnOf_eq (hall i)
  refine ⟨⟨u⟩, fun i j => ?_, fun i h => ?_⟩
  · apply Units.ext
    apply fn_ext
    intro h
    have h' : genericPoint Z ∈ D.U i ⊓ D.U j := h
    change fnOf (D.U i ⊓ D.U j) h' ((res (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (u i) : Γ(Z, D.U i ⊓ D.U j)ˣ) : Γ(Z, D.U i ⊓ D.U j)) =
      fnOf (D.U i ⊓ D.U j) h' (((D.g i j ^ M) * res (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (u j) : Γ(Z, D.U i ⊓ D.U j)ˣ) : Γ(Z, D.U i ⊓ D.U j))
    rw [Units.val_mul, Units.val_pow_eq_pow_val, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, map_mul, map_pow]
    erw [fnOf_resG, fnOf_resG, hu, hu]
    exact key i j h'
  · change fnOf _ h (u i : Γ(Z, D.U i)) * P ^ n = _
    rw [hu, hφ, mul_inv, inv_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hPne), one_mul]

end GlobalTheory.PropZCore
