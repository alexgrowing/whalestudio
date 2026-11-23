import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineDeformationPointsSaturatedOrdinaryIdeStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnramifiedLiftDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnivEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

noncomputable section

namespace GlobalTheory.OrdLoc.CriticalPoints

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ)

def sub (E₀ E B : Type) [Field E₀] [Field E] [Algebra E₀ E] [CommRing B] [Algebra E B] [Algebra E₀ B]
    [IsScalarTower E₀ E B] (π : B →ₐ[E] E) : Subalgebra E₀ B where
  carrier := {b | π b ∈ Set.range (algebraMap E₀ E)}
  mul_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, by rw [map_mul, hx, hy, map_mul]⟩
  add_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, by rw [map_add, hx, hy, map_add]⟩
  algebraMap_mem' c := ⟨c, by rw [IsScalarTower.algebraMap_apply E₀ E B, π.commutes]; rfl⟩

omit [CharZero O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] in
theorem push_base {x : U.R →ₐ[O] O} (hx : IsBase D.η D.Ψ U.r.hom x) (F : Type) [Field F] [Algebra O F] :
    push ((Algebra.ofId O F).comp x) U.r.hom = D.rz F := by
  unfold Dat3.rz
  rw [← show push x U.r.hom = r0 D.η D.Ψ from hx]
  rfl

theorem reduce (hP : LocalPublishedTheorems)
    (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
    [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (f : U.R →ₐ[O] B)
    (hD : D.InDcr (π : B →+* E) (push f U.r.hom))
    (E₀ : Type) [Field E₀] [Algebra ℚ_[l] E₀] [Module.Finite ℚ_[l] E₀] [Algebra O E₀] [Algebra ℤ_[l] E₀]
    [IsScalarTower ℤ_[l] O E₀] [IsScalarTower ℤ_[l] ℚ_[l] E₀] [IsFractionRing O E₀]
    [Algebra E₀ E] [IsScalarTower O E₀ E] [Algebra E₀ B] [IsScalarTower E₀ E B]
    [IsScalarTower O E₀ B] [IsScalarTower ℚ_[l] E₀ B] [IsScalarTower ℤ_[l] E₀ B] :
    IY D U ≤ RingHom.ker f := by
  classical
  obtain ⟨x, hx, -⟩ := univEx D U
  have hfx : ∀ a, π (f a) = algebraMap O E (x a) := by
    intro a
    let y : U.R →ₐ[O] E := (π.restrictScalars O).comp f
    obtain ⟨g, -, hu⟩ := unramified_lift_deformation D U E E (AlgHom.id E E) (fun a ha => by simpa using ha) y (push y U.r.hom)
      (fun g => U.r.hasMult g) rfl
      (fun a b => (ptCont (l := l) U.R E y).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b))
    have h := (hu y rfl).trans (hu ((Algebra.ofId O E).comp x) ((push_base D U hx E).trans hD.red.symm)).symm
    exact congrArg (fun φ : U.R →ₐ[O] E => φ a) h
  have hinj : Function.Injective (algebraMap E₀ E) := (algebraMap E₀ E).injective
  let B₀ := sub E₀ E B π
  have hmem : ∀ a, f a ∈ B₀ := fun a =>
    ⟨algebraMap O E₀ (x a), by rw [hfx, IsScalarTower.algebraMap_apply O E₀ E]⟩
  let f₀ : U.R →ₐ[O] B₀ :=
    { toFun := fun a => ⟨f a, hmem a⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a b)
      map_zero' := Subtype.ext (map_zero f)
      map_add' := fun a b => Subtype.ext (map_add f a b)
      commutes' := fun c => Subtype.ext (f.commutes c) }
  have hb : ∀ b : B₀, ∃ y, algebraMap E₀ E y = π (b : B) := fun b => b.2
  choose p hp using hb
  let π₀ : B₀ →ₐ[E₀] E₀ :=
    { toFun := p
      map_one' := hinj (by rw [hp]; simp)
      map_mul' := fun a b => hinj (by rw [hp, map_mul, hp, hp]; simp)
      map_zero' := hinj (by rw [hp]; simp)
      map_add' := fun a b => hinj (by rw [hp, map_add, hp, hp]; simp)
      commutes' := fun c => hinj (by
        rw [hp]
        show π (algebraMap E₀ B c) = algebraMap E₀ E (algebraMap E₀ E₀ c)
        rw [IsScalarTower.algebraMap_apply E₀ E B, π.commutes]
        rfl) }
  have hπ₀ : ∀ a, π₀ a = 0 → IsNilpotent a := by
    intro a ha
    have h0 : π (a : B) = 0 := by
      rw [← hp]
      change algebraMap E₀ E (π₀ a) = 0
      rw [ha, map_zero]
    obtain ⟨n, hn⟩ := hπ _ h0
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  let val' : B₀ →ₐ[ℚ_[l]] B :=
    { toFun := Subtype.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI : Module.Finite ℚ_[l] B₀ := Module.Finite.of_injective val'.toLinearMap Subtype.val_injective
  have hD' : D.InDcrAt (π : B →+* E) (D.rz E) ((GG.map (val' : B₀ →+* B)).comp (push f₀ U.r.hom)) := hD
  have hq := OrdinaryDeformation.dcr_pair val' val' (fun a b h _ => Subtype.ext h) hD' hD'
  have h1 : (π₀.restrictScalars O).comp f₀ = (Algebra.ofId O E₀).comp x := AlgHom.ext fun a => hinj (by
    change algebraMap E₀ E (p (f₀ a)) = algebraMap E₀ E (algebraMap O E₀ (x a))
    rw [hp, ← IsScalarTower.algebraMap_apply O E₀ E]
    exact hfx a)
  have hred : (GG.map (π₀ : B₀ →+* E₀)).comp (push f₀ U.r.hom) = D.rz E₀ := by
    rw [← push_base D U hx E₀, ← h1]
    rfl
  have hD₀ : D.InDcr (π₀ : B₀ →+* E₀) (push f₀ U.r.hom) := ⟨hq.mult, hred, hq.cont, hq.cr⟩
  intro a ha
  have h2 := GlobalTheory.T.crystallineDeformation_points_saturatedOrdinaryIdeal_fracO hP D U E₀ B₀ π₀ hπ₀ f₀ hD₀ ha
  rw [RingHom.mem_ker] at h2 ⊢
  exact congrArg Subtype.val h2

end GlobalTheory.OrdLoc.CriticalPoints

open GlobalTheory.OrdLoc.CriticalPoints in

theorem GlobalTheory.OrdLoc.crPts_IY : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), GlobalTheory.OrdLoc.CrPts D U (GlobalTheory.OrdLoc.IY D U) := by
  intro hP l _ O _ _ _ _ _ _ _ D U
  intro E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ f hD
  have hi : Function.Injective (algebraMap ℤ_[l] O) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    have hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime := inferInstance
    have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := hp.isMaximal h
    have h2 : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) _ hm
    exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm
  haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
    exact (IsFractionRing.injective O _).comp hi
  letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ_[l])) (FractionRing O) := inferInstance
  haveI : Module.Finite ℚ_[l] (FractionRing O) :=
    Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])
  have hOE : Function.Injective (algebraMap O E) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[l]) ?_
    rw [RingHom.comap_ker, ← IsScalarTower.algebraMap_eq, ← RingHom.injective_iff_ker_eq_bot,
      IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  letI : Algebra (FractionRing O) E := (IsFractionRing.lift hOE).toAlgebra
  haveI : IsScalarTower O (FractionRing O) E :=
    IsScalarTower.of_algebraMap_eq fun c => (IsFractionRing.lift_algebraMap hOE c).symm
  letI : Algebra (FractionRing O) B := ((algebraMap E B).comp (algebraMap (FractionRing O) E)).toAlgebra
  haveI : IsScalarTower (FractionRing O) E B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower O (FractionRing O) B := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = algebraMap E B (algebraMap (FractionRing O) E (algebraMap O (FractionRing O) c))
    rw [← IsScalarTower.algebraMap_apply O (FractionRing O) E, ← IsScalarTower.algebraMap_apply O E B]
  have hQ : (algebraMap (FractionRing O) E).comp (algebraMap ℚ_[l] (FractionRing O)) = algebraMap ℚ_[l] E :=
    IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun z => by
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (FractionRing O),
        IsScalarTower.algebraMap_apply ℤ_[l] O (FractionRing O),
        ← IsScalarTower.algebraMap_apply O (FractionRing O) E, ← IsScalarTower.algebraMap_apply ℤ_[l] O E,
        IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E])
  haveI : IsScalarTower ℚ_[l] (FractionRing O) B := IsScalarTower.of_algebraMap_eq fun q => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] E B, ← hQ]
    rfl
  haveI : IsScalarTower ℤ_[l] (FractionRing O) B := IsScalarTower.of_algebraMap_eq fun z => by
    change _ = algebraMap E B (algebraMap (FractionRing O) E (algebraMap ℤ_[l] (FractionRing O) z))
    rw [IsScalarTower.algebraMap_apply ℤ_[l] O (FractionRing O), ← IsScalarTower.algebraMap_apply O (FractionRing O) E,
      ← IsScalarTower.algebraMap_apply O E B, ← IsScalarTower.algebraMap_apply ℤ_[l] O B]
  exact reduce D U hP E B π hπ f hD (FractionRing O)
