import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerivationExtendOfFormallySmooth
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenDer

open GlobalTheory.Points

theorem top_le_preimage_of_mem {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (y : Sp A ⟶ X)
    (V : X.Opens) (h : y (IsLocalRing.closedPoint A) ∈ V) : ⊤ ≤ y ⁻¹ᵁ V := by
  intro z _
  exact (IsLocalRing.specializes_closedPoint z).mem_open (y ⁻¹ᵁ V).isOpen h

theorem germ_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (p : X) (hp : p ∈ V) (f : Γ(X, U)) :
    X.presheaf.germ V p hp (resG X h f) = X.presheaf.germ U p (h hp) f :=
  X.presheaf.germ_res_apply (homOfLE h) p hp f

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem eventually_zero {X : Scheme.{0}} {Ω : Type} [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X)
    (hx : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0) (O : X.Opens) (f : Γ(X, O))
    (hO : ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O)
    (hf : valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f = 0) :
    ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O' ∧ resG X h f = 0 := by
  set ξ := spMap (algebraMap Ω (FractionRing Ω)) ≫ x with hξ
  set p := ξ (IsLocalRing.closedPoint (FractionRing Ω)) with hp
  obtain ⟨U, hU, hqU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (show x (IsLocalRing.closedPoint Ω) ∈ (⊤ : X.Opens) from trivial)
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := top_le_preimage_of_mem x U hqU
  have hξU : ⊤ ≤ ξ ⁻¹ᵁ U := le_preimage_comp (V := ⊤) _ x hxU (le_preimage_top _)
  have hpU : p ∈ U := hξU (Set.mem_univ _)
  have hpO : p ∈ O := hO (Set.mem_univ _)
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hpU⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk p) (hU.primeIdealOf ⟨p, hpU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨p, hpU⟩
  obtain ⟨⟨a, s⟩, hmk⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf ⟨p, hpU⟩).asIdeal.primeCompl
    (X.presheaf.germ O p hpO f)
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk p) a s
  have hmk' : IsLocalization.mk' (X.presheaf.stalk p) a s = X.presheaf.germ O p hpO f := hmk
  rw [hmk'] at hspec
  have halg : ∀ r : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk p) r = X.presheaf.germ U p hpU r := fun _ => rfl
  rw [halg, halg] at hspec
  have hsu : IsUnit (X.presheaf.germ U p hpU (s : Γ(X, U))) := by
    rw [← halg]; exact IsLocalization.map_units _ s
  have hps : p ∈ X.basicOpen (s : Γ(X, U)) := (X.mem_basicOpen (s : Γ(X, U)) p hpU).mpr hsu
  have hg : X.presheaf.germ (O ⊓ U) p (show p ∈ O ⊓ U from ⟨hpO, hpU⟩) (resG X inf_le_left f * resG X inf_le_right (s : Γ(X, U))) =
      X.presheaf.germ U p hpU a := by
    rw [map_mul, germ_resG, germ_resG, hspec]
  obtain ⟨W₁, hpW₁, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq X.presheaf p (show p ∈ O ⊓ U from ⟨hpO, hpU⟩) hpU _ _ hg
  have e1 : X.presheaf.map iU.op = X.presheaf.map (homOfLE (leOfHom iU)).op := rfl
  have e2 : X.presheaf.map iV.op = X.presheaf.map (homOfLE (leOfHom iV)).op := rfl
  rw [e1, e2] at heq
  change resG X (leOfHom iU) _ = resG X (leOfHom iV) a at heq
  have hξW₁ : ⊤ ≤ ξ ⁻¹ᵁ W₁ := top_le_preimage_of_mem ξ W₁ hpW₁
  have hval := congrArg (valR ξ W₁) heq
  rw [valR_res ξ _ hξW₁, valR_res ξ _ hξW₁, valR_mul ξ _ (le_preimage_mono ξ (leOfHom iU) hξW₁),
    valR_res ξ _ (le_preimage_mono ξ (leOfHom iU) hξW₁), hf, zero_mul, hξ, valR_spMap_comp _ x U hxU] at hval
  have ha0 : a = 0 := hx U a hxU ((IsFractionRing.injective Ω (FractionRing Ω)) (by rw [← hval, map_zero]))
  rw [ha0, map_zero, map_mul, resG_resG, resG_resG] at heq
  set O₃ : X.Opens := W₁ ⊓ X.basicOpen (s : Γ(X, U)) with hO₃
  have h₃ : O₃ ≤ W₁ := inf_le_left
  have hunit : IsUnit (resG X (h₃.trans ((leOfHom iU).trans inf_le_right)) (s : Γ(X, U))) := by
    have h0 : IsUnit (resG X (X.basicOpen_le (s : Γ(X, U))) (s : Γ(X, U))) :=
      RingedSpace.isUnit_res_basicOpen X.toLocallyRingedSpace.toRingedSpace (s : Γ(X, U))
    rw [← resG_resG (X.basicOpen_le (s : Γ(X, U))) (show O₃ ≤ X.basicOpen (s : Γ(X, U)) from inf_le_right)]
    exact h0.map _
  refine ⟨O₃, h₃.trans ((leOfHom iU).trans inf_le_left), top_le_preimage_of_mem ξ O₃ (show p ∈ O₃ from ⟨hpW₁, hps⟩), ?_⟩
  have := congrArg (resG X h₃) heq
  rw [map_mul, resG_resG, resG_resG, map_zero] at this
  exact (hunit.mul_left_eq_zero).mp this

theorem valR_sub {C : Type} [CommRing C] {X : Scheme.{0}} (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f - g) = valR x U f - valR x U g := by
  simp only [valR_eq x U h, map_sub]

theorem top_le_preimage_inf {C : Type} [CommRing C] {X : Scheme.{0}} (x : Sp C ⟶ X) {U V : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) :=
  fun _ hz => ⟨hU hz, hV hz⟩

section Field

variable {X : Scheme.{0}} {K : Type} [Field K] (ξ : Sp K ⟶ X) (W : X.Opens)

def valField (hW : ⊤ ≤ ξ ⁻¹ᵁ W) : Subfield K where
  carrier := {y | ∃ (O : X.Opens) (f : Γ(X, O)), O ≤ W ∧ ⊤ ≤ ξ ⁻¹ᵁ O ∧ valR ξ O f = y}
  zero_mem' := ⟨W, 0, le_rfl, hW, valR_zero ξ W hW⟩
  one_mem' := ⟨W, 1, le_rfl, hW, valR_one ξ W hW⟩
  add_mem' := by
    rintro _ _ ⟨O, f, hOW, hO, rfl⟩ ⟨O', f', -, hO', rfl⟩
    have h2 := top_le_preimage_inf ξ hO hO'
    refine ⟨O ⊓ O', resG X inf_le_left f + resG X inf_le_right f', inf_le_left.trans hOW, h2, ?_⟩
    rw [valR_add ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2]
  mul_mem' := by
    rintro _ _ ⟨O, f, hOW, hO, rfl⟩ ⟨O', f', -, hO', rfl⟩
    have h2 := top_le_preimage_inf ξ hO hO'
    refine ⟨O ⊓ O', resG X inf_le_left f * resG X inf_le_right f', inf_le_left.trans hOW, h2, ?_⟩
    rw [valR_mul ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2]
  neg_mem' := by
    rintro _ ⟨O, f, hOW, hO, rfl⟩
    exact ⟨O, -f, hOW, hO, valR_neg ξ O hO f⟩
  inv_mem' := by
    rintro _ ⟨O, f, hOW, hO, rfl⟩
    by_cases h0 : valR ξ O f = 0
    · rw [h0, inv_zero]; exact ⟨W, 0, le_rfl, hW, valR_zero ξ W hW⟩
    · have hB := (le_preimage_basicOpen_iff ξ hO f).mpr (Ne.isUnit h0)
      have hfu : IsUnit (resG X (X.basicOpen_le f) f) :=
        RingedSpace.isUnit_res_basicOpen X.toLocallyRingedSpace.toRingedSpace f
      obtain ⟨u, hu⟩ := hfu
      refine ⟨X.basicOpen f, ↑u⁻¹, (X.basicOpen_le f).trans hOW, hB, ?_⟩
      have : valR ξ (X.basicOpen f) (↑u⁻¹) * valR ξ O f = 1 := by
        rw [← valR_res ξ (X.basicOpen_le f) hB f, ← valR_mul ξ _ hB]
        change valR ξ (X.basicOpen f) (↑u⁻¹ * resG X (X.basicOpen_le f) f) = 1
        rw [← hu, Units.inv_mul, valR_one ξ _ hB]
      exact eq_inv_of_mul_eq_one_left this

variable {ξ W}

theorem valR_der_eq (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (d : Fld X) (hd : IsField W d) {O O' : X.Opens} (f : Γ(X, O)) (f' : Γ(X, O')) (hOW : O ≤ W) (hO'W : O' ≤ W)
    (hO : ⊤ ≤ ξ ⁻¹ᵁ O) (hO' : ⊤ ≤ ξ ⁻¹ᵁ O') (e : valR ξ O f = valR ξ O' f') :
    valR ξ O (d O f) = valR ξ O' (d O' f') := by
  have h2 := top_le_preimage_inf ξ hO hO'
  obtain ⟨O₃, h₃, hO₃, hz⟩ := H (O ⊓ O') (resG X inf_le_left f - resG X inf_le_right f') h2
    (by rw [valR_sub ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2, e, sub_self])
  rw [map_sub, resG_resG, resG_resG, sub_eq_zero] at hz
  rw [← valR_res ξ (h₃.trans inf_le_left) hO₃, ← valR_res ξ (h₃.trans inf_le_right) hO₃,
    ← hd.2.2 O O₃ _ hOW f, ← hd.2.2 O' O₃ _ hO'W f', hz]

end Field

section Der

variable {X : Scheme.{0}} {K : Type} [Field K] (ξ : Sp K ⟶ X) (W : X.Opens)

theorem mem_valField_iff (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (y : K) :
    y ∈ valField ξ W hW ↔ ∃ (O : X.Opens) (f : Γ(X, O)), O ≤ W ∧ ⊤ ≤ ξ ⁻¹ᵁ O ∧ valR ξ O f = y := Iff.rfl

def valDer (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (y : valField ξ W hW) : K :=
  valR ξ (Classical.choose ((mem_valField_iff ξ W hW y).mp y.2))
    (d _ (Classical.choose (Classical.choose_spec ((mem_valField_iff ξ W hW y).mp y.2))))

variable {ξ W}

theorem valDer_eq (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (hd : IsField W d) (y : valField ξ W hW) {O : X.Opens} (f : Γ(X, O))
    (hOW : O ≤ W) (hO : ⊤ ≤ ξ ⁻¹ᵁ O) (e : valR ξ O f = y) : valDer ξ W hW d y = valR ξ O (d O f) := by
  obtain ⟨hOW', hO', e'⟩ := Classical.choose_spec (Classical.choose_spec ((mem_valField_iff ξ W hW y).mp y.2))
  exact valR_der_eq H d hd _ f hOW' hOW hO' hO (e'.trans e.symm)

theorem valDer_add (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (hd : IsField W d) (a b : valField ξ W hW) :
    valDer ξ W hW d (a + b) = valDer ξ W hW d a + valDer ξ W hW d b := by
  obtain ⟨O, f, hOW, hO, ea⟩ := (mem_valField_iff ξ W hW a).mp a.2
  obtain ⟨O', f', hO'W, hO', eb⟩ := (mem_valField_iff ξ W hW b).mp b.2
  have h2 := top_le_preimage_inf ξ hO hO'
  have h2W : O ⊓ O' ≤ W := inf_le_left.trans hOW
  rw [valDer_eq H hW d hd (a + b) (resG X inf_le_left f + resG X inf_le_right f') h2W h2
      (by rw [valR_add ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2, ea, eb]; rfl),
    valDer_eq H hW d hd a (resG X (inf_le_left : O ⊓ O' ≤ O) f) h2W h2 (by rw [valR_res ξ _ h2, ea]),
    valDer_eq H hW d hd b (resG X (inf_le_right : O ⊓ O' ≤ O') f') h2W h2 (by rw [valR_res ξ _ h2, eb]),
    hd.1 _ h2W, valR_add ξ _ h2]

theorem valDer_mul (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (hd : IsField W d) (a b : valField ξ W hW) :
    valDer ξ W hW d (a * b) = (a : K) * valDer ξ W hW d b + (b : K) * valDer ξ W hW d a := by
  obtain ⟨O, f, hOW, hO, ea⟩ := (mem_valField_iff ξ W hW a).mp a.2
  obtain ⟨O', f', hO'W, hO', eb⟩ := (mem_valField_iff ξ W hW b).mp b.2
  have h2 := top_le_preimage_inf ξ hO hO'
  have h2W : O ⊓ O' ≤ W := inf_le_left.trans hOW
  have ea' : valR ξ (O ⊓ O') (resG X inf_le_left f) = a := by rw [valR_res ξ _ h2, ea]
  have eb' : valR ξ (O ⊓ O') (resG X inf_le_right f') = b := by rw [valR_res ξ _ h2, eb]
  rw [valDer_eq H hW d hd (a * b) (resG X inf_le_left f * resG X inf_le_right f') h2W h2
      (by rw [valR_mul ξ _ h2, ea', eb']; rfl),
    valDer_eq H hW d hd a (resG X (inf_le_left : O ⊓ O' ≤ O) f) h2W h2 ea',
    valDer_eq H hW d hd b (resG X (inf_le_right : O ⊓ O' ≤ O') f') h2W h2 eb',
    hd.2.1 _ h2W, valR_add ξ _ h2, valR_mul ξ _ h2, valR_mul ξ _ h2, ea', eb']

end Der

theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem exists_derivation_fractionRing : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] [CharZero Ω] (x : Sp Ω ⟶ X), (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0) → ∀ (W : X.Opens) (d : Fld X), IsField W d → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ W → ∃ dt0 : Derivation ℤ (FractionRing Ω) (FractionRing Ω), ∀ (O : X.Opens) (f : Γ(X, O)), O ≤ W → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (d O f) = dt0 (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  intro X Ω _ _ _ _ x hx W d hd hW
  set K := FractionRing Ω
  set ξ := spMap (algebraMap Ω K) ≫ x with hξ
  have H := eventually_zero x hx
  set F := valField ξ W hW
  haveI : CharZero K := ⟨fun m n h => by
    rw [← map_natCast (algebraMap Ω K) m, ← map_natCast (algebraMap Ω K) n] at h
    exact Nat.cast_injective (IsFractionRing.injective Ω K h)⟩
  haveI : CharZero F := ⟨fun m n h => Nat.cast_injective (R := K) (by simpa using congrArg Subtype.val h)⟩
  haveI : Algebra.FormallySmooth F K := formallySmooth_of_charZero F K
  obtain ⟨d', hadd, hmul, hext⟩ := GlobalTheory.KS.exists_derivation_extend_of_formallySmooth F K K (RingHom.id K)
    (valDer ξ W hW d) (valDer_add H hW d hd) (fun a b => valDer_mul H hW d hd a b)
  refine ⟨{ toFun := d'
            map_add' := hadd
            map_smul' := ?_
            map_one_eq_zero' := ?_
            leibniz' := ?_ }, fun O f hOW hO => ?_⟩
  · intro m y
    have := (AddMonoidHom.mk' d' hadd).map_zsmul m y
    simp only [AddMonoidHom.mk'_apply, zsmul_eq_mul] at this
    simp only [RingHom.id_apply, Algebra.smul_def, algebraMap_int_eq, eq_intCast, smul_eq_mul]
    rw [this]; simp
  · have h1 := hmul 1 1
    simp only [RingHom.id_apply, _root_.one_mul, _root_.mul_one] at h1
    show d' 1 = 0
    linear_combination -h1
  · intro a b
    show d' (a * b) = a • d' b + b • d' a
    simp [hmul, smul_eq_mul]
  have hmem : valR ξ O f ∈ F := ⟨O, f, hOW, hO, rfl⟩
  change _ = d' (algebraMap F K ⟨_, hmem⟩)
  rw [hext]
  exact (valDer_eq H hW d hd ⟨_, hmem⟩ f hOW hO rfl).symm

end GlobalTheory.GenDer
