import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjTor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private theorem gg_ext {A : Type} [CommRing A] {x y : GG 3 A} (h : ∀ a b, x.mat a b = y.mat a b)
    (h' : x.right = y.right) : x = y :=
  SemidirectProduct.ext (Units.ext (Matrix.ext h)) h'

private theorem exists_unit {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharZero O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] :
    ∃ t : Oˣ, (t : O) - 1 ∈ maximalIdeal O ∧ Function.Injective fun j : ℤ => t ^ j := by
  have h1 : (maximalIdeal O).comap (algebraMap ℤ_[l] O) = maximalIdeal ℤ_[l] :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal O))
  have h2 : (l : O) ∈ maximalIdeal O := by
    have : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    rw [← h1, Ideal.mem_comap, map_natCast] at this
    exact this
  have h3 : IsUnit (1 - (-(l : O))) := isUnit_one_sub_self_of_mem_nonunits _ (neg_mem h2)
  obtain ⟨t, ht⟩ := h3
  refine ⟨t, by simpa [ht] using h2, injective_zpow_iff_not_isOfFinOrder.2 fun h => ?_⟩
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : (((1 + l) ^ n : ℕ) : O) = ((1 : ℕ) : O) := by
    have := congrArg Units.val e
    rw [Units.val_pow_eq_pow_val, ht] at this
    simpa using this
  have e2 := Nat.cast_injective e1
  have := (Fact.out : l.Prime).pos
  have e3 : 1 < (1 + l) ^ n := Nat.one_lt_pow hn.ne' (by omega)
  omega

theorem UpperTheory.V.Loc.torAut :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (x : U.R →ₐ[O] O), IsBase D.η D.Ψ U.r.hom x → ∃ (t : Oˣ) (θ : U.R →ₐ[O] U.R), (Function.Injective fun j : ℤ => t ^ j) ∧ x.comp θ = x ∧ (∀ a ∈ D.It U, θ a ∈ D.It U) ∧ ∀ g a b, θ ((U.r.hom g).mat a b) = algebraMap O U.R ((t ^ wt a b : Oˣ) : O) * (U.r.hom g).mat a b := by
  intro hP l _ O _ _ _ _ _ _ _ D U x hx
  obtain ⟨t, ht1, ht⟩ := exists_unit (l := l) O
  have hres : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (j : ℤ),
      res O C (algebraMap O C ((t ^ j : Oˣ) : O)) = 1 := fun C _ _ _ j => by
    have e : Units.map (algebraMap O (ResidueField O) : O →* ResidueField O) t = 1 := by
      apply Units.ext
      have := (residue_eq_zero_iff _).2 ht1
      rw [map_sub, map_one, sub_eq_zero] at this
      exact this
    have e2 := congrArg Units.val (map_zpow (Units.map (algebraMap O (ResidueField O) : O →* ResidueField O)) t j)
    rw [e, one_zpow] at e2
    rw [AlgHom.commutes]
    exact e2
  have hmat : ∀ (C : Type) [CommRing C] [Algebra O C] (r : GQ l →* GG 3 C) g a b,
      (conjBy (tor C (Units.map (algebraMap O C : O →* C) t)) r g).mat a b =
        algebraMap O C ((t ^ wt a b : Oˣ) : O) * (r g).mat a b := fun C _ _ r g a b => by
    rw [(conjBy_tor r _).1, ← map_zpow]
    rfl
  let r' : GLift O D.η D.Ψ U.R :=
    { hom := conjBy (tor U.R (Units.map (algebraMap O U.R : O →* U.R) t)) U.r.hom
      cont := fun a b N => by
        simp only [hmat, map_mul]
        exact (IsLocallyConstant.const _).mul (U.r.cont a b N)
      red := fun g => by
        rw [← U.r.red g]
        refine gg_ext (fun a b => ?_) ((conjBy_tor _ _).2.1 g)
        show res O U.R (GG.mat _ a b) = res O U.R (GG.mat _ a b)
        rw [hmat, map_mul, hres, one_mul] }
  obtain ⟨θ, hθ, -⟩ := (U.rep U.R).2 r' trivial
  have hθm : ∀ g a b, θ ((U.r.hom g).mat a b) =
      algebraMap O U.R ((t ^ wt a b : Oˣ) : O) * (U.r.hom g).mat a b := fun g a b =>
    (congrArg (fun r : GLift O D.η D.Ψ U.R => (r.hom g).mat a b) hθ).trans (hmat _ _ g a b)
  have uniq : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f f' : U.R →ₐ[O] C),
      (∀ g a b, f ((U.r.hom g).mat a b) = f' ((U.r.hom g).mat a b)) → f = f' := fun C _ _ _ f f' h => by
    obtain ⟨F, -, hF⟩ := (U.rep C).2 (U.r.map f') trivial
    refine (hF f ?_).trans (hF f' rfl).symm
    exact GLift.ext (MonoidHom.ext fun g => gg_ext (h g) rfl)
  have hxe : ∀ g a b, x ((U.r.hom g).mat a b) = (r0 D.η D.Ψ g).mat a b := fun g a b =>
    congrArg (fun r : GQ l →* GG 3 O => (r g).mat a b) hx
  refine ⟨t, θ, ht, uniq O _ _ fun g a b => ?_, fun y hy => ?_, hθm⟩
  · rw [AlgHom.comp_apply, hθm, map_mul, AlgHom.commutes]
    by_cases hab : a = b
    · simp [hab, wt]
    · rw [hxe, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ hab, mul_zero]
  · by_cases hI : D.It U = ⊤
    · rw [hI]; trivial
    haveI : Nontrivial (U.R ⧸ D.It U) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsCO O (U.R ⧸ D.It U) := co_quot O U.R _ (Ideal.Quotient.mkₐ O _) (Ideal.Quotient.mkₐ_surjective O _)
    obtain ⟨f, hf, hfI⟩ := rtConj hP D U (U.R ⧸ D.It U) (push (Ideal.Quotient.mkₐ O _) U.r.hom)
      (tor _ (Units.map (algebraMap O (U.R ⧸ D.It U) : O →* _) t)) (fun a b => by
        rw [← res_eq_zero_iff O, Matrix.sub_apply, tor_val]
        by_cases hab : a = b
        · subst hab
          rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, map_sub, map_one, ← map_zpow]
          exact sub_eq_zero.2 (hres _ _)
        · rw [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab, sub_zero, map_zero])
      ⟨_, rfl, fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha⟩
    have e : f = (Ideal.Quotient.mkₐ O _).comp θ := uniq _ _ _ fun g a b => by
      rw [AlgHom.comp_apply, hθm, map_mul, AlgHom.commutes]
      exact (congrArg (fun r : GQ l →* GG 3 (U.R ⧸ D.It U) => (r g).mat a b) hf).trans (hmat _ _ g a b)
    have := hfI hy
    rw [e] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
