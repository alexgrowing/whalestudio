import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NormFam

theorem exists_lift_of_isIntegral (A R C : Type) [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] (hinj : Function.Injective (algebraMap A R))
    [Field C] [IsAlgClosed C] (x : A →+* C) :
    ∃ y : R →+* C, y.comp (algebraMap A R) = x := by
  classical
  have : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  obtain ⟨𝔮, -, h𝔮, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker x)
    (⊥ : Ideal R) (by
      intro a ha
      simp only [Ideal.mem_comap, Ideal.mem_bot] at ha
      have : a = 0 := hinj (by simpa using ha)
      simp [this])
  let 𝔭 : Ideal A := Ideal.comap (algebraMap A R) 𝔮
  have : 𝔮.IsPrime := h𝔮
  have : 𝔭.IsPrime := Ideal.IsPrime.comap _
  let g : A ⧸ 𝔭 →+* C := Ideal.Quotient.lift 𝔭 x (fun a ha => by
    change a ∈ 𝔭 at ha
    rw [show 𝔭 = RingHom.ker x from hc] at ha
    exact ha)
  have hg : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [RingHom.mem_ker] at hq
    change x a = 0 at hq
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    change a ∈ 𝔭
    rw [show 𝔭 = RingHom.ker x from hc]
    exact hq
  let : Algebra (A ⧸ 𝔭) C := g.toAlgebra
  have : Module.IsTorsionFree (A ⧸ 𝔭) C := Module.isTorsionFree_iff_algebraMap_injective.mpr hg
  have : Module.IsTorsionFree (A ⧸ 𝔭) (R ⧸ 𝔮) := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    exact Ideal.quotientMap_injective' le_rfl
  have : Algebra.IsAlgebraic (A ⧸ 𝔭) (R ⧸ 𝔮) := Algebra.IsIntegral.isAlgebraic
  let y₀ : (R ⧸ 𝔮) →ₐ[A ⧸ 𝔭] C := IsAlgClosed.lift
  refine ⟨y₀.toRingHom.comp (Ideal.Quotient.mk 𝔮), ?_⟩
  ext a
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have h1 : (Ideal.Quotient.mk 𝔮) (algebraMap A R a) =
      algebraMap (A ⧸ 𝔭) (R ⧸ 𝔮) (Ideal.Quotient.mk 𝔭 a) := rfl
  rw [h1, y₀.commutes]
  rfl

theorem finite_algHom (A A' E : Type) [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A']
    [Algebra A A'] [Module.Finite A A'] [Field E] [Algebra A E] [Module.IsTorsionFree A A']
    [Module.IsTorsionFree A E] :
    Finite (A' →ₐ[A] E) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := A')
  have : Algebra.IsIntegral A A' := Algebra.IsIntegral.of_finite A A'
  let Ψ : (A' →ₐ[A] E) → (∀ a : s, (minpoly A (a : A')).rootSet E) := fun σ a =>
    ⟨σ a, by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), ?_⟩
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]⟩
  refine Finite.of_injective Ψ ?_
  intro σ σ' h
  apply AlgHom.toLinearMap_injective
  apply LinearMap.ext_on hs
  intro a ha
  have := congrArg (fun f => (f ⟨a, ha⟩ : E)) h
  simpa [Ψ] using this

end GlobalTheory.NormFam

namespace GlobalTheory.NormFam

open MvPolynomial Polynomial in

theorem exists_eq_algebraMap_of_fixed (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CharZero A] (c : AlgebraicClosure (FractionRing A))
    (hfix : ∀ ρ : AlgebraicClosure (FractionRing A) ≃ₐ[FractionRing A]
      AlgebraicClosure (FractionRing A), ρ c = c)
    (hint : IsIntegral A c) : ∃ a : A, algebraMap A (AlgebraicClosure (FractionRing A)) a = c := by
  have hmem : c ∈ (⊥ : IntermediateField (FractionRing A) (AlgebraicClosure (FractionRing A))) := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup
      (⊥ : IntermediateField (FractionRing A) (AlgebraicClosure (FractionRing A))),
      IntermediateField.mem_fixedField_iff]
    intro ρ _
    exact hfix ρ
  rw [IntermediateField.mem_bot] at hmem
  obtain ⟨k, rfl⟩ := hmem
  have hk : IsIntegral A k :=
    (isIntegral_algebraMap_iff (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))).injective).mp hint
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hk
  exact ⟨a, (IsScalarTower.algebraMap_apply A (FractionRing A) _ a).symm⟩

section Gauss

variable {C : Type} [NormedField C]

theorem gaussNorm_prod [IsUltrametricDist C] {κ : Type} (s : Finset κ) (p : κ → Polynomial C) :
    Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1 (∏ i ∈ s, p i) =
      ∏ i ∈ s, Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1 (p i) := by
  classical
  have hna : IsNonarchimedean (NormedField.toAbsoluteValue C) :=
    IsUltrametricDist.isNonarchimedean_norm
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [← Polynomial.C_1, Polynomial.gaussNorm_C]
    simp [NormedField.toAbsoluteValue]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Polynomial.gaussNorm_mul hna one_pos, ih]

theorem gaussNorm_eq_iSup_fin (p : Polynomial C) (n : ℕ) (hn : p.natDegree < n) :
    Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1 p = ⨆ i : Fin n, ‖p.coeff i‖ := by
  have hv : ∀ c : C, NormedField.toAbsoluteValue C c = ‖c‖ := fun c => rfl
  have hbdd : BddAbove (Set.range fun i : Fin n => ‖p.coeff i‖) := (Set.finite_range _).bddAbove
  apply le_antisymm
  · obtain ⟨i, hi⟩ := Polynomial.exists_eq_gaussNorm (NormedField.toAbsoluteValue C) 1 p
    rw [hi, hv, one_pow, _root_.mul_one]
    by_cases hin : i < n
    · exact le_ciSup hbdd ⟨i, hin⟩
    · have : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [this, norm_zero]
      exact Real.iSup_nonneg (fun _ => norm_nonneg _)
  · refine Real.iSup_le (fun i => ?_) (Polynomial.gaussNorm_nonneg _ _ zero_le_one)
    have := Polynomial.le_gaussNorm (NormedField.toAbsoluteValue C) p zero_le_one i
    rwa [hv, one_pow, _root_.mul_one] at this

theorem gaussNorm_sum_monomial {J : Type} [Fintype J] (e : J → ℕ) (he : Function.Injective e)
    (c : J → C) :
    Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1
      (∑ j, Polynomial.monomial (e j) (c j)) = ⨆ j, ‖c j‖ := by
  classical
  have hv : ∀ c : C, NormedField.toAbsoluteValue C c = ‖c‖ := fun c => rfl
  have hcoeff : ∀ i, (∑ j, Polynomial.monomial (e j) (c j)).coeff i =
      if h : ∃ j, e j = i then c h.choose else 0 := by
    intro i
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    split_ifs with h
    · rw [Finset.sum_eq_single h.choose]
      · simp [h.choose_spec]
      · intro j _ hj
        rw [if_neg]
        intro hij
        exact hj (he (hij.trans h.choose_spec.symm))
      · simp
    · apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      exact fun hij => h ⟨j, hij⟩
  have hbdd : BddAbove (Set.range fun j : J => ‖c j‖) := (Set.finite_range _).bddAbove
  apply le_antisymm
  · obtain ⟨i, hi⟩ := Polynomial.exists_eq_gaussNorm (NormedField.toAbsoluteValue C) 1 _
    rw [hi, hv, one_pow, _root_.mul_one, hcoeff]
    split_ifs with h
    · exact le_ciSup hbdd _
    · rw [norm_zero]
      exact Real.iSup_nonneg (fun _ => norm_nonneg _)
  · refine Real.iSup_le (fun j => ?_) (Polynomial.gaussNorm_nonneg _ _ zero_le_one)
    have := Polynomial.le_gaussNorm (NormedField.toAbsoluteValue C) (∑ j, Polynomial.monomial (e j) (c j))
      zero_le_one (e j)
    rw [hv, one_pow, _root_.mul_one, hcoeff] at this
    have h : ∃ j', e j' = e j := ⟨j, rfl⟩
    rw [dif_pos h] at this
    rwa [he h.choose_spec] at this

end Gauss

end GlobalTheory.NormFam

namespace GlobalTheory.NormFam

section Hom

variable {σ R S : Type} [CommRing R] [CommRing S]

def CoeffsHom (a : ℕ) (p : Polynomial (MvPolynomial σ R)) : Prop :=
  ∀ i, (p.coeff i).IsHomogeneous a

theorem CoeffsHom.mul {a b : ℕ} {p q : Polynomial (MvPolynomial σ R)} (hp : CoeffsHom a p)
    (hq : CoeffsHom b q) : CoeffsHom (a + b) (p * q) := by
  intro i
  rw [Polynomial.coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun x _ => (hp x.1).mul (hq x.2))

theorem CoeffsHom.one : CoeffsHom (σ := σ) (R := R) 0 1 := by
  intro i
  rw [Polynomial.coeff_one]
  split_ifs
  · exact MvPolynomial.isHomogeneous_one _ _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem CoeffsHom.prod {κ : Type} (s : Finset κ) (a : ℕ) (p : κ → Polynomial (MvPolynomial σ R))
    (hp : ∀ i ∈ s, CoeffsHom a (p i)) : CoeffsHom (s.card * a) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffsHom.one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi,
      show (s.card + 1) * a = a + s.card * a by ring]
    exact (hp i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem isHomogeneous_of_map_injective {f : R →+* S} (hf : Function.Injective f)
    {p : MvPolynomial σ R} {n : ℕ} (h : (MvPolynomial.map f p).IsHomogeneous n) :
    p.IsHomogeneous n := by
  intro d hd
  apply h
  rw [MvPolynomial.coeff_map]
  exact (map_ne_zero_iff f hf).mpr hd

theorem CoeffsHom.of_map_injective {f : R →+* S} (hf : Function.Injective f)
    {p : Polynomial (MvPolynomial σ R)} {a : ℕ}
    (h : CoeffsHom a (Polynomial.map (MvPolynomial.map f) p)) : CoeffsHom a p := by
  intro i
  have := h i
  rw [Polynomial.coeff_map] at this
  exact isHomogeneous_of_map_injective hf this

theorem exists_map_eq_of_coeff_mem_range (f : R →+* S) (q : MvPolynomial σ S)
    (h : ∀ m, ∃ r, f r = q.coeff m) : ∃ q₀ : MvPolynomial σ R, MvPolynomial.map f q₀ = q := by
  classical
  refine ⟨∑ m ∈ q.support, MvPolynomial.monomial m (h m).choose, ?_⟩
  rw [map_sum]
  simp only [MvPolynomial.map_monomial, (h _).choose_spec]
  exact MvPolynomial.support_sum_monomial_coeff q

theorem exists_map_eq_of_coeff_mem_range' (f : R →+* S) (P : Polynomial (MvPolynomial σ S))
    (h : ∀ i m, ∃ r, f r = (P.coeff i).coeff m) :
    ∃ P₀ : Polynomial (MvPolynomial σ R), Polynomial.map (MvPolynomial.map f) P₀ = P := by
  have : P ∈ (Polynomial.mapRingHom (MvPolynomial.map f)).range := by
    rw [Polynomial.mem_map_range]
    intro i
    obtain ⟨q₀, hq₀⟩ := exists_map_eq_of_coeff_mem_range f (P.coeff i) (h i)
    exact ⟨q₀, hq₀⟩
  obtain ⟨P₀, hP₀⟩ := this
  exact ⟨P₀, hP₀⟩

end Hom

end GlobalTheory.NormFam

namespace GlobalTheory.NormFam

section Pack

variable {A' R C σ J : Type} [CommRing A'] [CommRing R] [CommRing C] [Fintype σ] [Fintype J]

noncomputable def pack (e : J → ℕ) (ℓ : J → σ → A') : Polynomial (MvPolynomial σ A') :=
  ∑ j, Polynomial.monomial (e j) (∑ s, MvPolynomial.C (ℓ j s) * MvPolynomial.X s)

theorem map_pack (e : J → ℕ) (ℓ : J → σ → A') (f : A' →+* R) :
    Polynomial.map (MvPolynomial.map f) (pack e ℓ) = pack e (fun j s => f (ℓ j s)) := by
  simp [pack, Polynomial.map_sum, Polynomial.map_monomial, map_sum, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X]

theorem map_eval_pack (e : J → ℕ) (ℓ : J → σ → A') (f : A' →+* C) (T : σ → C) :
    Polynomial.map (MvPolynomial.eval₂Hom f T) (pack e ℓ) =
      ∑ j, Polynomial.monomial (e j) (∑ s, f (ℓ j s) * T s) := by
  simp [pack, Polynomial.map_sum, Polynomial.map_monomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]

theorem coeffsHom_pack (e : J → ℕ) (ℓ : J → σ → A') : CoeffsHom 1 (pack e ℓ) := by
  classical
  intro i
  rw [pack, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  split_ifs
  · apply MvPolynomial.IsHomogeneous.sum
    intro s _
    exact (MvPolynomial.isHomogeneous_X _ _).C_mul _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

omit [Fintype σ] in
theorem map_map_mv {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂)
    (g : R₂ →+* R₃) (p : Polynomial (MvPolynomial σ R₁)) :
    Polynomial.map (MvPolynomial.map g) (Polynomial.map (MvPolynomial.map f) p) =
      Polynomial.map (MvPolynomial.map (g.comp f)) p := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext fun q => MvPolynomial.map_map f g q

omit [Fintype σ] in
theorem map_evalHom_map (f : A' →+* R) (y : R →+* C) (T : σ → C)
    (p : Polynomial (MvPolynomial σ A')) :
    Polynomial.map (MvPolynomial.eval₂Hom y T) (Polynomial.map (MvPolynomial.map f) p) =
      Polynomial.map (MvPolynomial.eval₂Hom (y.comp f) T) p := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext fun q => by simp [MvPolynomial.eval₂_map]

end Pack

end GlobalTheory.NormFam

namespace GlobalTheory.NormFam

theorem norm_of_family : ∀ (A A' : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CharZero A] [CommRing A'] [IsDomain A'] [Algebra A A'] [Module.Finite A A'],
    Function.Injective (algebraMap A A') → ∀ (σ J : Type) [Fintype σ] [Fintype J]
    (ℓ : J → σ → A'), ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial σ A),
    (∀ i, (B i).IsHomogeneous d) ∧ ∀ (C : Type) [NormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] (x : A →+* C) (T : σ → C) (N : ℝ),
    (∀ x' : A' →+* C, x'.comp (algebraMap A A') = x →
      (⨆ j, ‖∑ s, x' (ℓ j s) * T s‖) = N) →
    N ^ (d : ℕ) = ⨆ i, ‖MvPolynomial.eval₂ x T (B i)‖ := by
  intro A A' _ _ _ _ _ _ _ _ hinj σ J _ _ ℓ
  classical

  let K := FractionRing A
  let E := AlgebraicClosure K
  let R : Subalgebra A E := integralClosure A E
  have hAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have hAR : Function.Injective (algebraMap A R) := by
    intro a b h
    apply hAE
    have := congrArg (fun r : R => (r : E)) h
    simpa using this
  have : Module.IsTorsionFree A A' := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Module.IsTorsionFree A E := Module.isTorsionFree_iff_algebraMap_injective.mpr hAE
  have : Algebra.IsIntegral A A' := Algebra.IsIntegral.of_finite A A'
  have : Finite (A' →ₐ[A] E) := finite_algHom A A' E
  let _ : Fintype (A' →ₐ[A] E) := Fintype.ofFinite _
  have : Nonempty (A' →ₐ[A] E) := ⟨IsAlgClosed.lift⟩

  let res : (A' →ₐ[A] E) → (A' →+* R) := fun τ =>
    τ.toRingHom.codRestrict R (fun a =>
      (mem_integralClosure_iff A E).mpr ((Algebra.IsIntegral.isIntegral (R := A) a).map τ))
  have hres : ∀ τ, (algebraMap R E).comp (res τ) = τ.toRingHom := fun τ => RingHom.ext fun a => rfl
  have hresA : ∀ τ, (res τ).comp (algebraMap A A') = algebraMap A R := by
    intro τ
    ext a
    simp [res]

  let e := Fintype.equivFin J
  let α := pack (fun j => (e j : ℕ)) ℓ
  let P : Polynomial (MvPolynomial σ R) := ∏ τ, Polynomial.map (MvPolynomial.map (res τ)) α
  let PE : Polynomial (MvPolynomial σ E) := Polynomial.map (MvPolynomial.map (algebraMap R E)) P
  have hPE : PE = ∏ τ : A' →ₐ[A] E, Polynomial.map (MvPolynomial.map τ.toRingHom) α := by
    simp only [PE, P, Polynomial.map_prod, map_map_mv, hres]

  have hinv : ∀ ρ : E ≃ₐ[K] E, Polynomial.map (MvPolynomial.map ρ.toRingHom) PE = PE := by
    intro ρ
    rw [hPE, Polynomial.map_prod]
    simp only [map_map_mv]
    let φ : (A' →ₐ[A] E) ≃ (A' →ₐ[A] E) :=
      { toFun := fun τ => (ρ.restrictScalars A).toAlgHom.comp τ
        invFun := fun τ => (ρ.symm.restrictScalars A).toAlgHom.comp τ
        left_inv := fun τ => by ext a; simp
        right_inv := fun τ => by ext a; simp }
    exact Fintype.prod_equiv φ _ _ (fun τ => rfl)

  have hfix : ∀ i m (ρ : E ≃ₐ[K] E), ρ (((P.coeff i).coeff m : R) : E) = (((P.coeff i).coeff m : R) : E) := by
    intro i m ρ
    have h1 : (PE.coeff i).coeff m = (((P.coeff i).coeff m : R) : E) := by
      simp only [PE, Polynomial.coeff_map, MvPolynomial.coeff_map]
      rfl
    have h2 := congrArg (fun Q : Polynomial (MvPolynomial σ E) => (Q.coeff i).coeff m) (hinv ρ)
    simp only [Polynomial.coeff_map, MvPolynomial.coeff_map] at h2
    rw [h1] at h2
    exact h2
  have hcoef : ∀ i m, ∃ a : A, algebraMap A R a = (P.coeff i).coeff m := by
    intro i m
    obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_fixed A (((P.coeff i).coeff m : R) : E) (hfix i m)
      ((mem_integralClosure_iff A E).mp ((P.coeff i).coeff m).2)
    exact ⟨a, Subtype.ext (by simpa using ha)⟩
  obtain ⟨P₀, hP₀⟩ := exists_map_eq_of_coeff_mem_range' (algebraMap A R) P hcoef

  let d : ℕ+ := ⟨Fintype.card (A' →ₐ[A] E), Fintype.card_pos⟩
  have hPhom : CoeffsHom (d : ℕ) P := by
    have := CoeffsHom.prod Finset.univ 1 (fun τ => Polynomial.map (MvPolynomial.map (res τ)) α)
      (fun τ _ => by rw [map_pack]; exact coeffsHom_pack _ _)
    rw [Finset.card_univ, _root_.mul_one] at this
    exact this
  have hP₀hom : CoeffsHom (d : ℕ) P₀ := CoeffsHom.of_map_injective hAR (hP₀ ▸ hPhom)
  refine ⟨d, P₀.natDegree + 1, fun i => P₀.coeff i, fun i => hP₀hom i, ?_⟩
  intro C _ _ _ x T N hN

  obtain ⟨y, hy⟩ := exists_lift_of_isIntegral A R C hAR x
  have hlift : ∀ τ, (y.comp (res τ)).comp (algebraMap A A') = x := by
    intro τ
    rw [RingHom.comp_assoc, hresA, hy]

  let ev : Polynomial (MvPolynomial σ R) →+* Polynomial C :=
    Polynomial.mapRingHom (MvPolynomial.eval₂Hom y T)
  have hev1 : ev P = ∏ τ, ∑ j, Polynomial.monomial (e j : ℕ)
      (∑ s, (y.comp (res τ)) (ℓ j s) * T s) := by
    simp only [ev, P, Polynomial.coe_mapRingHom, Polynomial.map_prod]
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    rw [map_evalHom_map, map_eval_pack]
  have hev2 : ev P = Polynomial.map (MvPolynomial.eval₂Hom x T) P₀ := by
    rw [← hP₀]
    simp only [ev, Polynomial.coe_mapRingHom]
    rw [map_evalHom_map, hy]
  have he : Function.Injective (fun j => (e j : ℕ)) := fun a b h => e.injective (Fin.ext h)
  have hG1 : Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1 (ev P) = N ^ (d : ℕ) := by
    have : ∀ τ ∈ (Finset.univ : Finset (A' →ₐ[A] E)),
        Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1
          (∑ j, Polynomial.monomial (e j : ℕ) (∑ s, (y.comp (res τ)) (ℓ j s) * T s)) = N := by
      intro τ _
      rw [gaussNorm_sum_monomial _ he]
      exact hN _ (hlift τ)
    rw [hev1, gaussNorm_prod, Finset.prod_congr rfl this, Finset.prod_const, Finset.card_univ]
    rfl
  have hG2 : Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1 (ev P) =
      ⨆ i : Fin (P₀.natDegree + 1), ‖MvPolynomial.eval₂ x T (P₀.coeff i)‖ := by
    rw [hev2, gaussNorm_eq_iSup_fin _ (P₀.natDegree + 1)
      (Nat.lt_succ_of_le (Polynomial.natDegree_map_le))]
    simp only [Polynomial.coeff_map, MvPolynomial.coe_eval₂Hom]
  rw [← hG1, hG2]

end GlobalTheory.NormFam
