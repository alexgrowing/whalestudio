import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionPolarizedCMObjectExtendsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfThetaUnitInEveryCosetStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.GoodTrait
set_option linter.style.haveILetI false

theorem exists_unit_prime (O : Type) [CommRing O] [IsLocalRing O] : ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) := by
  have h : IsUnit (((3 : ℕ) : O) * 2 + -((5 : ℕ) : O)) := by
    have : ((3 : ℕ) : O) * 2 + -((5 : ℕ) : O) = 1 := by push_cast; norm_num
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩
  · exact ⟨5, by norm_num, by decide, (IsUnit.neg_iff _).1 h⟩

theorem norm_eq_one_of_isUnit {W C : Type} [CommRing W] [NormedField C] (f : W →+* C) (hf : ∀ r, ‖f r‖ ≤ 1) {x : W}
    (hx : IsUnit x) : ‖f x‖ = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h : ‖f x‖ * ‖f y‖ = 1 := by rw [← norm_mul, ← map_mul, hy, map_one, norm_one]
  have h₁ := hf x
  have h₂ := hf y
  have h₃ := norm_nonneg (f x)
  nlinarith

theorem exists_valuationSubring {K C : Type} [Field K] [NormedField C] [IsUltrametricDist C] (f : K →+* C) :
    ∃ S : ValuationSubring K, (∀ x, x ∈ S ↔ ‖f x‖ ≤ 1) ∧ ∀ x, S.valuation x = 1 ↔ ‖f x‖ = 1 := by
  let v := (NormedField.valuation (K := C)).comap f
  refine ⟨v.valuationSubring, fun x => ?_, fun x => ?_⟩
  · rw [Valuation.mem_valuationSubring_iff]
    exact Iff.rfl
  · rw [← (Valuation.isEquiv_valuation_valuationSubring v).eq_one_iff_eq_one]
    exact NNReal.coe_inj.symm

theorem isDominant_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    IsDominant (spMap f) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap f)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot f).1 hf]
  exact bot_le

set_option maxHeartbeats 1000000 in

theorem range_subset_abLocus : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → ThetaInt Y g y₁ → y₁ ≫ Y.j ≫ Y.s = jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₁ →+* W) (gam : FractionRing R₁ →+* FractionRing W), (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) → ∀ χ : Sp W ⟶ Y.X, spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ → IsUnit (φ (g PowerSeries.X)) → Set.range χ ⊆ abLocus Y.t.G := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ h₇ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hO R₁ _ _ g y₁ _ _ _ hT hy W _ _ _ hW φ gam hgam χ hχ hu
  haveI : IsLocalRing O' := by
    rcases hO with ⟨h, -⟩ | ⟨h, -⟩
    · letI := h.toField
      exact inferInstance
    · exact inferInstance
  obtain ⟨n, hn, hodd, hnu⟩ := exists_unit_prime O'
  obtain ⟨hdvr, -, hch⟩ := id hW
  obtain ⟨C, _, _, _, _, alg, -, -, hC⟩ := GlobalTheory.Ex.exists_complete_isAlgClosed_cExt W (FractionRing W)
  let iC : W →+* C := (algebraMap (FractionRing W) C).comp (algebraMap W _)
  have hiC : Function.Injective iC := (algebraMap (FractionRing W) C).injective.comp (IsFractionRing.injective W _)
  haveI : CharZero C := charZero_of_injective_ringHom hiC
  obtain ⟨o, ho, hθ⟩ := hT
  haveI := o.charZero
  let Γ : AlgebraicClosure (FractionRing R₁) →+* C :=
    letI : Algebra (FractionRing R₁) C := ((algebraMap (FractionRing W) C).comp gam).toAlgebra
    (IsAlgClosed.lift (R := FractionRing R₁) (S := AlgebraicClosure (FractionRing R₁)) (M := C)).toRingHom
  have hΓ : Γ.comp (algebraMap (FractionRing R₁) _) = (algebraMap (FractionRing W) C).comp gam := by
    letI : Algebra (FractionRing R₁) C := ((algebraMap (FractionRing W) C).comp gam).toAlgebra
    exact RingHom.ext fun x => (IsAlgClosed.lift (R := FractionRing R₁) (S := AlgebraicClosure (FractionRing R₁)) (M := C)).commutes x
  have hΓ' : ∀ r, Γ (((algebraMap (FractionRing R₁) _).comp (algebraMap R₁ _)) r) = iC (φ r) := fun r => by
    have := DFunLike.congr_fun hΓ (algebraMap R₁ _ r)
    simp only [RingHom.comp_apply, hgam] at this
    exact this
  obtain ⟨o', hext, hth, -⟩ := GlobalTheory.FullExtend.main h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D _ C Γ o
  have e₀ : spMap Γ ≫ spMap (algebraMap (FractionRing R₁) (AlgebraicClosure (FractionRing R₁))) ≫ y₁ =
      spMap (algebraMap (FractionRing W) C) ≫ spMap gam ≫ y₁ := by
    rw [← Category.assoc, ← spMap_comp', hΓ, spMap_comp', Category.assoc]
  have bF : c.F →+* AlgebraicClosure (FractionRing R₁) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫
      ((spMap (algebraMap (FractionRing R₁) (AlgebraicClosure (FractionRing R₁))) ≫ y₁) ≫ pullback.snd _ _).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing R₁)))).hom).hom
  have ho' := (GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y _ bF).2.2 C Γ _ o o' ho hext
  rw [e₀] at ho'
  have e₁ : spMap gam ≫ jK R₁ = jK W ≫ spMap φ :=
    (spMap_comp' (algebraMap R₁ _) gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp' φ (algebraMap W _)))
  have e₂ : spMap (algebraMap (FractionRing W) (FractionRing W)) = 𝟙 _ := Spec.map_id _
  obtain ⟨M, f, χ', mp, hf, hfC, hχ', -⟩ := GlobalTheory.Ex.UnifModel.exists_mdl h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y C W hW hC
    (FractionRing W) (algebraMap (FractionRing W) C) (fun _ => rfl) (spMap gam ≫ y₁)
    (φ.comp (g.comp ((PowerSeries.C (R := O')).comp b))) (by
      rw [e₂, Category.id_comp, Category.assoc, hy, spMap_comp', spMap_comp', spMap_comp', ← Category.assoc, e₁,
        Category.assoc]) o' ho'
  obtain ⟨v, hv, hint⟩ := hθ n 2 hn hodd hnu one_le_two
  obtain ⟨S, hS, hS'⟩ := exists_valuationSubring Γ
  obtain ⟨a₁, -, a₃⟩ := hint S fun r => by rw [hS, hΓ']; exact hC.1 _
  have a₄ := a₃ (by rw [hS', hΓ']; exact norm_eq_one_of_isUnit iC hC.1 hu)
  have hnC : ‖(n : C)‖ = 1 := by
    have := norm_eq_one_of_isUnit iC hC.1 (hnu.map (φ.comp (g.comp (PowerSeries.C (R := O')))))
    rwa [map_natCast, map_natCast] at this
  have hprop : IsProper M.t.G.hom := GlobalTheory.T.isProper_of_theta_unit_in_every_coset h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D C o' M n 2 hn hodd hnC le_rfl _ (hth _ _ hv)
    (fun x => (hS _).1 (a₁ x)) fun x => (a₄ x).imp fun h hh => (hS' _).1 hh
  let jC : M.W →+* C := (algebraMap (FractionRing M.W) C).comp (algebraMap M.W _)
  have hjC : Function.Injective jC := (algebraMap (FractionRing M.W) C).injective.comp (IsFractionRing.injective M.W _)
  have hjf : jC.comp f = iC := RingHom.ext hfC
  have hfi : Function.Injective f := Function.Injective.of_comp (f := jC) (by rw [← RingHom.coe_comp, hjf]; exact hiC)
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have := isDominant_spMap jC hjC
  have e₃ : χ' = spMap f ≫ χ := by
    refine ext_of_isDominant (spMap jC) ?_
    have e₄ : spMap jC = jFK (R := M.W) C ≫ jK M.W := spMap_comp' _ _
    have e₅ : spMap iC = spMap (algebraMap (FractionRing W) C) ≫ jK W := spMap_comp' _ _
    rw [← Category.assoc, ← spMap_comp', hjf, e₅, e₄, Category.assoc, hχ', Category.assoc, Category.assoc, hχ]
  rintro _ ⟨x, rfl⟩
  obtain ⟨x', rfl⟩ := hf.to_isIntegral.comap_surjective hfi x
  have h := (abLocus_pullback abLocusOne Y.t.semi mp.cart.1 x').2 fun K _ _ t _ => inferInstance
  rw [e₃] at h
  exact h

end GlobalTheory.Ex.GoodTrait
