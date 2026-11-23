import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFD

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem exists_der (O T : Type) [CommRing O] [CommRing T] [IsLocalRing T] [Algebra O T]
    [Algebra.FormallySmooth O (ResidueField T)] :
    ∃ r : Derivation O T (maximalIdeal T).Cotangent,
      ∀ (t : T) (ht : t ∈ maximalIdeal T), r t = - (maximalIdeal T).toCotangent ⟨t, ht⟩ := by
  set m := maximalIdeal T with hm
  let g : (T ⧸ m ^ 2) →ₐ[O] ResidueField T :=
    Ideal.Quotient.liftₐ (m ^ 2) (IsScalarTower.toAlgHom O T (ResidueField T)) (fun a ha => by
      have : a ∈ m := Ideal.pow_le_self two_ne_zero ha
      exact (residue_eq_zero_iff a).2 this)
  have hg : ∀ a : T, g (Ideal.Quotient.mk _ a) = residue T a := fun a => rfl
  have hmem : ∀ a ∈ m, Ideal.Quotient.mk (m ^ 2) a ∈ m.cotangentIdeal := fun a ha =>
    Submodule.mem_map_of_mem ha
  have hker : RingHom.ker (g : (T ⧸ m ^ 2) →+* ResidueField T) = m.cotangentIdeal := by
    ext b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    constructor
    · intro h
      refine hmem a ((residue_eq_zero_iff a).1 ?_)
      rw [← hg]
      exact h
    · rintro ⟨a', ha', h⟩
      rw [RingHom.mem_ker]
      show g (Ideal.Quotient.mk _ a) = 0
      have h' : Ideal.Quotient.mk (m ^ 2) a' = Ideal.Quotient.mk (m ^ 2) a := h
      rw [← h', hg]
      exact (residue_eq_zero_iff a').2 ha'
  have hsurj : Function.Surjective g := fun y => by
    obtain ⟨a, rfl⟩ := residue_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hnil : IsNilpotent (RingHom.ker (g : (T ⧸ m ^ 2) →+* ResidueField T)) :=
    ⟨2, by rw [hker]; exact m.cotangentIdeal_square⟩
  let s : ResidueField T →ₐ[O] (T ⧸ m ^ 2) :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id O _) g hsurj hnil
  have hs : ∀ x, g (s x) = x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id O _) g hsurj hnil x
  let f : T →ₐ[O] (T ⧸ m ^ 2) := s.comp (IsScalarTower.toAlgHom O T (ResidueField T))
  have e : (Ideal.Quotient.mkₐ O m.cotangentIdeal).comp f =
      IsScalarTower.toAlgHom O T ((T ⧸ m ^ 2) ⧸ m.cotangentIdeal) := by
    ext t
    show Ideal.Quotient.mk m.cotangentIdeal (f t) = Ideal.Quotient.mk m.cotangentIdeal (Ideal.Quotient.mk (m ^ 2) t)
    rw [Ideal.Quotient.eq, ← hker, RingHom.mem_ker]
    show g (s (residue T t) - Ideal.Quotient.mk _ t) = 0
    rw [map_sub, hs, hg, sub_self]
  let d := derivationToSquareZeroOfLift m.cotangentIdeal m.cotangentIdeal_square f e
  refine ⟨m.cotangentEquivIdeal.symm.toLinearMap.compDer d, fun t ht => ?_⟩
  have hf : f t = 0 := by
    show s (residue T t) = 0
    rw [(residue_eq_zero_iff t).2 ht, map_zero]
  have hd : d t = - ⟨Ideal.Quotient.mk (m ^ 2) t, hmem t ht⟩ := by
    apply Subtype.ext
    show f t - Ideal.Quotient.mk (m ^ 2) t = _
    rw [hf, zero_sub]
    rfl
  show m.cotangentEquivIdeal.symm (d t) = _
  rw [hd, map_neg]
  congr 1
  exact m.cotangentEquivIdeal_symm_apply t ht

private theorem formally_smooth_of_char_zero_field (O E k : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
    [Field k] [CharZero k] [Algebra O k] [Algebra E k] [IsScalarTower O E k] [Algebra.IsAlgebraic O k] :
    Algebra.FormallySmooth O k := by
  haveI : Algebra.IsAlgebraic E k := (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := E) (C := k)).1 inferInstance
  haveI : CharZero E := (algebraMap E k).charZero
  haveI : Algebra.IsSeparable E k := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyEtale E k := Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale O E := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors O)
  haveI : Algebra.FormallyEtale O k := Algebra.FormallyEtale.comp O E k
  exact inferInstance

private theorem formallySmooth_res (O K k : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [FaithfulSMul O K]
    [CharZero K] [Algebra.IsAlgebraic O K] [Field k] [Algebra O k] (ι : k →+* K)
    (hι : ∀ a, ι (algebraMap O k a) = algebraMap O K a) : Algebra.FormallySmooth O k := by
  letI : Algebra k K := ι.toAlgebra
  haveI : IsScalarTower O k K := IsScalarTower.of_algebraMap_eq fun a => (hι a).symm
  haveI : CharZero k := ι.charZero
  haveI : FaithfulSMul O k := (faithfulSMul_iff_algebraMap_injective O k).2
    (Function.Injective.of_comp (f := ι) (by
      have : (ι ∘ algebraMap O k) = algebraMap O K := funext hι
      rw [this]
      exact FaithfulSMul.algebraMap_injective O K))
  haveI : Algebra.IsAlgebraic O k := Algebra.IsAlgebraic.tower_bot_of_injective (A := K) ι.injective
  letI : Algebra (FractionRing O) k := FractionRing.liftAlgebra O k
  haveI : IsScalarTower O (FractionRing O) k := FractionRing.isScalarTower_liftAlgebra O k
  exact formally_smooth_of_char_zero_field O (FractionRing O) k

private theorem algebraic_coef (l : ℕ) [Fact l.Prime] (c : Coef l) : Algebra.IsAlgebraic c.O (Qbar l) := by
  haveI : Algebra.IsAlgebraic ℤ_[l] (Qbar l) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l]) (C := Qbar l)).2 inferInstance
  refine Algebra.IsAlgebraic.extendScalars (R := ℤ_[l]) ?_
  refine Function.Injective.of_comp (f := algebraMap c.O (Qbar l)) ?_
  have : (algebraMap c.O (Qbar l)) ∘ (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] (Qbar l) :=
    funext fun a => (IsScalarTower.algebraMap_apply _ _ _ a).symm
  rw [this, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l), RingHom.coe_comp]
  exact (algebraMap ℚ_[l] (Qbar l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])

section Pt

variable {O A K T : Type} [CommRing O] [CommRing A] [Field K] [Algebra O A] [Algebra O K]
  (ξ : A →ₐ[O] K) [(RingHom.ker ξ).IsPrime] [CommRing T] [IsLocalRing T] [Algebra A T]
  [IsLocalization.AtPrime T (RingHom.ker ξ)]

include ξ in
private theorem exists_frac (t : T) : ∃ (a u : A), u ∉ RingHom.ker ξ ∧ algebraMap A T u * t = algebraMap A T a := by
  obtain ⟨a, u, rfl⟩ := IsLocalization.exists_mk'_eq (RingHom.ker ξ).primeCompl t
  exact ⟨a, u, u.2, IsLocalization.mk'_spec' T a u⟩

private theorem exists_res : ∃ ι : ResidueField T →+* K, ∀ a, ι (residue T (algebraMap A T a)) = ξ a := by
  have hu : ∀ y : (RingHom.ker ξ).primeCompl, IsUnit ((ξ : A →+* K) y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)
  let ξ' : T →+* K := IsLocalization.lift (M := (RingHom.ker ξ).primeCompl) (g := (ξ : A →+* K)) hu
  have hξ : ∀ a, ξ' (algebraMap A T a) = ξ a := fun a => IsLocalization.lift_eq hu a
  haveI : IsLocalHom ξ' := ⟨fun t ht => by
    obtain ⟨a, u, hu', h⟩ := exists_frac ξ t
    have h1 : ξ u * ξ' t = ξ a := by rw [← hξ, ← hξ, ← map_mul, h]
    have h2 : ξ a ≠ 0 := by
      rw [← h1]
      exact mul_ne_zero (fun h0 => hu' (RingHom.mem_ker.2 h0)) ht.ne_zero
    have h3 : IsUnit (algebraMap A T a) :=
      IsLocalization.map_units T (⟨a, fun h0 => h2 (RingHom.mem_ker.1 h0)⟩ : (RingHom.ker ξ).primeCompl)
    rw [← h] at h3
    exact isUnit_of_mul_isUnit_right h3⟩
  exact ⟨ResidueField.lift ξ', fun a => by rw [ResidueField.lift_residue_apply, hξ]⟩

private theorem rank_ge [Algebra O T] [IsScalarTower O A T] [IsNoetherianRing T]
    [Algebra.FormallySmooth O (ResidueField T)] :
    ((Module.finrank (ResidueField T) (CotangentSpace T) : ℕ) : Cardinal) ≤ Module.rank K (PtDer ξ K) := by
  obtain ⟨ι, hι⟩ := exists_res (T := T) ξ
  obtain ⟨r, hr⟩ := exists_der O T
  letI : Algebra (ResidueField T) K := ι.toAlgebra
  have hact : ∀ (x : A) (φ : CotangentSpace T →ₗ[ResidueField T] K) (c : CotangentSpace T),
      φ (algebraMap A T x • c) = ξ x * φ c := fun x φ c => by
    have h1 : algebraMap A T x • c = residue T (algebraMap A T x) • c := (algebraMap_smul _ _ c).symm
    rw [h1, φ.map_smul, Algebra.smul_def]
    show ι _ * _ = _
    rw [hι]
  let Dl : (CotangentSpace T →ₗ[ResidueField T] K) → (A →ₗ[O] K) := fun φ =>
    { toFun := fun x => φ (r (algebraMap A T x))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun a x => by
        have h1 : algebraMap A T (a • x) = a • algebraMap A T x :=
          map_smul (IsScalarTower.toAlgHom O A T) a x
        have h2 : a • r (algebraMap A T x) = algebraMap A T (algebraMap O A a) • r (algebraMap A T x) := by
          rw [← IsScalarTower.algebraMap_apply, algebraMap_smul]
        rw [h1, r.map_smul, h2, hact, AlgHom.commutes, Algebra.smul_def, RingHom.id_apply] }
  have hDl : ∀ φ, Dl φ ∈ PtDer ξ K := fun φ f g => by
    show φ (r (algebraMap A T (f * g))) = ξ f • φ (r (algebraMap A T g)) + ξ g • φ (r (algebraMap A T f))
    rw [map_mul, r.leibniz, map_add, hact, hact]
    rfl
  let Ψ : (CotangentSpace T →ₗ[ResidueField T] K) →ₗ[K] PtDer ξ K :=
    { toFun := fun φ => ⟨Dl φ, hDl φ⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro φ h0
    have h1 : ∀ x, φ (r (algebraMap A T x)) = 0 := fun x =>
      congrArg (fun D : PtDer ξ K => (D : A →ₗ[O] K) x) h0
    refine LinearMap.ext fun c => ?_
    obtain ⟨⟨t, ht⟩, rfl⟩ := (maximalIdeal T).toCotangent_surjective c
    obtain ⟨a, u, hu, h⟩ := exists_frac ξ t
    have ha : algebraMap A T a ∈ maximalIdeal T := by
      rw [← h]
      exact Ideal.mul_mem_left _ _ ht
    have h2 : (⟨algebraMap A T a, ha⟩ : maximalIdeal T) = algebraMap A T u • ⟨t, ht⟩ :=
      Subtype.ext h.symm
    have h3 := h1 a
    rw [hr _ ha, h2, map_smul, map_neg, neg_eq_zero] at h3
    have h4 : ξ u * φ ((maximalIdeal T).toCotangent ⟨t, ht⟩) = 0 := by
      rw [← hact]
      exact h3
    exact (mul_eq_zero.1 h4).resolve_left fun h0 => hu (RingHom.mem_ker.2 h0)
  haveI : Module.Free (ResidueField T) (CotangentSpace T) := Module.Free.of_divisionRing _ _
  let b := Module.finBasis (ResidueField T) (CotangentSpace T)
  have h5 := LinearMap.rank_le_of_injective (Ψ ∘ₗ (b.constr K).toLinearMap)
    (hinj.comp (b.constr K).injective)
  rwa [rank_fin_fun] at h5

end Pt

theorem UpperTheory.V.J.regDom :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (A : Type) [CommRing A] [IsNoetherianRing A] [Algebra c.O A] (ξ : A →ₐ[c.O] Qbar l) (d : ℕ) [(RingHom.ker ξ).IsPrime],
        Module.rank (Qbar l) (PtDer ξ (Qbar l)) ≤ d → (d : ℕ∞) ≤ (RingHom.ker ξ).height → IsDomain (Localization.AtPrime (RingHom.ker ξ)) := by
  intro l _ c A _ _ _ ξ d _ h1 h2
  haveI : IsNoetherianRing (Localization.AtPrime (RingHom.ker ξ)) :=
    IsLocalization.isNoetherianRing (RingHom.ker ξ).primeCompl _ inferInstance
  obtain ⟨ι, hι⟩ := exists_res (T := Localization.AtPrime (RingHom.ker ξ)) ξ
  haveI := algebraic_coef l c
  haveI : Algebra.FormallySmooth c.O (ResidueField (Localization.AtPrime (RingHom.ker ξ))) :=
    formallySmooth_res c.O (Qbar l) _ ι fun a => by
      have := hι (algebraMap c.O A a)
      rwa [AlgHom.commutes, ← IsScalarTower.algebraMap_apply] at this
  have h3 := (rank_ge (T := Localization.AtPrime (RingHom.ker ξ)) ξ).trans h1
  have h4 : Module.finrank (ResidueField (Localization.AtPrime (RingHom.ker ξ)))
      (CotangentSpace (Localization.AtPrime (RingHom.ker ξ))) ≤ d := by exact_mod_cast h3
  haveI : IsRegularLocalRing (Localization.AtPrime (RingHom.ker ξ)) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      IsLocalization.AtPrime.ringKrullDim_eq_height (RingHom.ker ξ)]
    have h5 : ((Module.finrank (ResidueField (Localization.AtPrime (RingHom.ker ξ)))
      (CotangentSpace (Localization.AtPrime (RingHom.ker ξ))) : ℕ) : ℕ∞) ≤ (RingHom.ker ξ).height :=
      (by exact_mod_cast h4 : ((Module.finrank _ _ : ℕ) : ℕ∞) ≤ d).trans h2
    exact_mod_cast h5
  exact GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
