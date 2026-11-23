import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatedOrdinaryIdealCutsOutCrystallineLocusStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryLocusIdealLeKerOfIsBasePointStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnramifiedLiftDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnivEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.OrdinaryEmbeddings

open nonZeroDivisors

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ)

omit [IsAdicComplete (maximalIdeal O) O] [IsDiscreteValuationRing O] [CharZero O] in
theorem inj_OE (E : Type) [Field E] [Algebra ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] : Function.Injective (algebraMap O E) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[l]) ?_
  rw [RingHom.comap_ker, ← IsScalarTower.algebraMap_eq, ← RingHom.injective_iff_ker_eq_bot,
    IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
  exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])

omit [IsAdicComplete (maximalIdeal O) O] [CharZero O] in
theorem inj_ZO : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra h
  have hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime := inferInstance
  have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := hp.isMaximal h
  have h2 : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) _ hm
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm

theorem cont_push (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B]
    [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : U.R →ₐ[O] B) (a b : Fin 3) :
    QCont l fun g => (push f U.r.hom g).mat a b :=
  (ptCont (l := l) U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)

omit [CharZero O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] in
theorem push_base (E : Type) [Field E] [Algebra O E] {x : U.R →ₐ[O] O} (hx : IsBase D.η D.Ψ U.r.hom x) :
    push ((Algebra.ofId O E).comp x) U.r.hom = D.rz E := by
  unfold Dat3.rz
  rw [← show push x U.r.hom = r0 D.η D.Ψ from hx]
  rfl

omit [CharZero O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] in

theorem IY_le_It : GlobalTheory.OrdLoc.IY D U ≤ GlobalTheory.OrdLoc.It D U :=
  Ideal.le_radical.trans (le_sInf fun _ hP => hP.1.1.2)

theorem reg (hP : LocalPublishedTheorems) {x : U.R →ₐ[O] O} (hx : IsBase D.η D.Ψ U.r.hom x) :
    ∃ y, x y ≠ 0 ∧ ∀ a ∈ GlobalTheory.OrdLoc.It D U, y * a ∈ GlobalTheory.OrdLoc.IY D U := by
  have hi := inj_ZO (l := l) (O := O)
  haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
    exact (IsFractionRing.injective O _).comp hi
  letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O ℤ_[l]⁰) (FractionRing O) := inferInstance
  haveI : Module.Finite ℚ_[l] (FractionRing O) := Module.Finite.of_isLocalization ℤ_[l] O ℤ_[l]⁰
  obtain ⟨-, n, P, φ, -, -, ⟨y, hy, hyP⟩, hPt, -⟩ := GlobalTheory.T.exists_unique_ordinaryPrime_dim_succ_near_base hP D U (FractionRing O) x hx
  exact ⟨y, hy, fun a ha => hyP a (hPt ▸ ha)⟩

end GlobalTheory.OrdLoc.OrdinaryEmbeddings

open GlobalTheory.OrdLoc.OrdinaryEmbeddings in

theorem GlobalTheory.OrdLoc.on_iff_inDcr : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* GG 3 B), (GG.map (π : B →+* E)).comp r = D.rz E → (GlobalTheory.OrdLoc.On D U r ↔ D.InDcr (π : B →+* E) r) := by
  intro hP l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ r hr
  obtain ⟨hPts, hCr⟩ := GlobalTheory.T.saturatedOrdinaryIdeal_cuts_out_crystalline_locus hP D U
  constructor
  · rintro ⟨f, rfl, hf⟩
    exact ⟨fun g => U.r.hasMult g, hr, cont_push D U B f, hPts B f ((IY_le_It D U).trans hf)⟩
  · intro hd
    obtain ⟨x, hx, -⟩ := univEx D U
    obtain ⟨f, hf, -⟩ := unramified_lift_deformation D U E B π hπ ((Algebra.ofId O E).comp x) r hd.mult
      (hd.red.trans (push_base D U E hx).symm) hd.cont
    have hfY : GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f := hCr E B π hπ f (hf ▸ hd)
    have hfx : ∀ a, π (f a) = algebraMap O E (x a) := by
      intro a
      obtain ⟨g, -, hu⟩ := unramified_lift_deformation D U E E (AlgHom.id E E) (fun a ha => by simpa using ha)
        ((π.restrictScalars O).comp f) (push ((π.restrictScalars O).comp f) U.r.hom)
        (fun g => U.r.hasMult g) rfl (cont_push D U E _)
      have h1 : push ((π.restrictScalars O).comp f) U.r.hom = D.rz E := by
        rw [← hd.red, ← hf]; rfl
      have h := (hu ((π.restrictScalars O).comp f) rfl).trans
        (hu ((Algebra.ofId O E).comp x) ((push_base D U E hx).trans h1.symm)).symm
      exact congrArg (fun φ : U.R →ₐ[O] E => φ a) h
    obtain ⟨y, hy, hya⟩ := reg D U hP hx
    refine ⟨f, hf, fun a ha => ?_⟩
    have hne : algebraMap O E (x y) ≠ 0 := (map_ne_zero_iff _ (inj_OE (l := l) E)).2 hy
    have hnil : IsNilpotent (f y - algebraMap E B (algebraMap O E (x y))) := hπ _ (by
      rw [map_sub, hfx, AlgHom.commutes]
      exact sub_self _)
    have hu : IsUnit (f y) := by
      have := hnil.isUnit_add_right_of_commute (hne.isUnit.map (algebraMap E B)) (Commute.all _ _)
      simpa using this
    have h0 : f y * f a = 0 := by
      rw [← map_mul]
      exact hfY (hya a ha)
    exact (hu.mul_right_eq_zero).1 h0
