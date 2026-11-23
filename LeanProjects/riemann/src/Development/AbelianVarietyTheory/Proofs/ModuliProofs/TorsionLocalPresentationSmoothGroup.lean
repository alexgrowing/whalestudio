import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionPres

section Alg

variable {O : Type} [CommRing O] [IsLocalRing O] {B : Type} [CommRing B] [Algebra O B]

theorem exists_lift_atPrime (e : B →ₐ[O] O) (S : Type) [CommRing S] [Algebra B S] [Algebra O S]
    [IsScalarTower O B S] [IsLocalization.AtPrime S ((IsLocalRing.maximalIdeal O).comap e)]
    {A : Type} [CommRing A] [Algebra O A] (h : B →ₐ[O] A)
    (hh : ∀ b, IsUnit (e b) → IsUnit (h b)) :
    ∃ φ : S →ₐ[O] A, ∀ b, φ (algebraMap B S b) = h b := by
  have hu : ∀ t : ((IsLocalRing.maximalIdeal O).comap e).primeCompl, IsUnit (h t) := fun t =>
    hh _ (IsLocalRing.notMem_maximalIdeal.mp t.2)
  exact ⟨IsLocalization.liftAlgHom (S := S) hu, fun b => by
    simp [IsLocalization.liftAlgHom_apply]⟩

theorem isUnit_of_aug (e : B →ₐ[O] O) (S : Type) [CommRing S] [Algebra B S] [Algebra O S]
    [IsScalarTower O B S] [IsLocalization.AtPrime S ((IsLocalRing.maximalIdeal O).comap e)]
    (eS : S →ₐ[O] O) (he : ∀ b, eS (algebraMap B S b) = e b) (s : S) (hs : IsUnit (eS s)) :
    IsUnit s := by
  obtain ⟨⟨b, t⟩, h⟩ :=
    IsLocalization.surj ((IsLocalRing.maximalIdeal O).comap e).primeCompl s
  have ht : IsUnit (e t) := IsLocalRing.notMem_maximalIdeal.mp t.2
  have hb : IsUnit (e b) := by
    have := congrArg eS h
    simp only [map_mul, he] at this
    rw [← this]
    exact hs.mul ht
  have hb' : b ∈ ((IsLocalRing.maximalIdeal O).comap e).primeCompl :=
    IsLocalRing.notMem_maximalIdeal.mpr hb
  have := IsLocalization.map_units S (⟨b, hb'⟩ : ((IsLocalRing.maximalIdeal O).comap e).primeCompl)
  exact isUnit_of_mul_isUnit_left (h ▸ this)

variable {g : ℕ}

theorem exists_smul_ker_le (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    (e : B →ₐ[O] O) :
    ∃ r : B, e r = 1 ∧ ∀ b, e b = 0 → r * b ∈ Ideal.span (Set.range fun i =>
      π (MvPolynomial.X i) - algebraMap O B (e (π (MvPolynomial.X i)))) := by
  set J : Ideal B := Ideal.span (Set.range fun i =>
      π (MvPolynomial.X i) - algebraMap O B (e (π (MvPolynomial.X i)))) with hJ
  set I : Ideal B := RingHom.ker e with hI
  have hsub : ∀ b, b - algebraMap O B (e b) ∈ I := fun b => by
    simp [hI, RingHom.mem_ker]
  have h1 : Ideal.Quotient.mkₐ O (J ⊔ I * I) =
      (Ideal.Quotient.mkₐ O (J ⊔ I * I)).comp ((Algebra.ofId O B).comp e) := by
    refine GlobalTheory.NilCoord.ext_of_nil π hπ _ _ (fun b => ⟨2, ?_⟩) (fun j => ?_)
    · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply]
      rw [← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_two]
      exact Ideal.mem_sup_right (Ideal.mul_mem_mul (hsub b) (hsub b))
    · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply]
      rw [Ideal.Quotient.eq]
      exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)
  have h2 : I ≤ J ⊔ I • I := by
    intro b hb
    have := AlgHom.congr_fun h1 b
    have hb' : e b = 0 := hb
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply, hb', map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  have hfp : Algebra.FinitePresentation O B := by
    letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
    haveI : IsScalarTower O (MvPolynomial (Fin g) O) B :=
      IsScalarTower.of_algebraMap_eq fun r => (π.commutes r).symm
    exact Algebra.FinitePresentation.trans O (MvPolynomial (Fin g) O) B
  have hfg : I.FG := Algebra.FinitePresentation.ker_fG_of_surjective e
    (fun c => ⟨algebraMap O B c, by simp⟩)
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl h2
  refine ⟨r, ?_, fun b hb => hr2 (Submodule.smul_mem_pointwise_smul b r I hb)⟩
  have : e (r - 1) = 0 := hr1
  rwa [map_sub, map_one, sub_eq_zero] at this

theorem exists_coords (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    (e : B →ₐ[O] O) (S : Type) [CommRing S] [Algebra B S] [Algebra O S]
    [IsScalarTower O B S] [IsLocalization.AtPrime S ((IsLocalRing.maximalIdeal O).comap e)]
    (eS : S →ₐ[O] O) (he : ∀ b, eS (algebraMap B S b) = e b) :
    ∃ x : Fin g → S, RingHom.ker eS = Ideal.span (Set.range x) ∧
      (∀ j, ∃ v : S →ₐ[O] DualNumber O, (TrivSqZeroExt.fstHom O O O).comp v = eS ∧
        ∀ i, v (x i) = TrivSqZeroExt.inr (if i = j then 1 else 0)) ∧
      ∃ ρ : S →ₐ[O] MvPowerSeries (Fin g) (IsLocalRing.ResidueField O),
        ∀ i, ρ (x i) = MvPowerSeries.X i := by
  let x : Fin g → S := fun i =>
    algebraMap B S (π (MvPolynomial.X i) - algebraMap O B (e (π (MvPolynomial.X i))))
  letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
  haveI : IsScalarTower O (MvPolynomial (Fin g) O) B :=
    IsScalarTower.of_algebraMap_eq fun r => (π.commutes r).symm
  refine ⟨x, le_antisymm ?_ ?_, fun j => ?_, ?_⟩
  · obtain ⟨r, hr1, hr2⟩ := exists_smul_ker_le π hπ e
    intro s hs
    have hs' : eS s = 0 := hs
    obtain ⟨⟨b, t⟩, h⟩ :=
      IsLocalization.surj ((IsLocalRing.maximalIdeal O).comap e).primeCompl s
    have hb : e b = 0 := by
      have := congrArg eS h
      simp only [map_mul, he, hs', zero_mul] at this
      exact this.symm
    have h3 : algebraMap B S (r * b) ∈ Ideal.span (Set.range x) := by
      have := Ideal.mem_map_of_mem (algebraMap B S) (hr2 b hb)
      rwa [Ideal.map_span, ← Set.range_comp] at this
    have hr : IsUnit (algebraMap B S r) := isUnit_of_aug e S eS he _ (by rw [he, hr1]; exact isUnit_one)
    have ht : IsUnit (algebraMap B S t) := IsLocalization.map_units S t
    rw [map_mul, ← h, Ideal.unit_mul_mem_iff_mem _ hr, Ideal.mul_unit_mem_iff_mem _ ht] at h3
    exact h3
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [x, he, RingHom.mem_ker]
  · obtain ⟨φ, h1, h2⟩ := GlobalTheory.NilCoord.exists_of_nil π hπ
      ((Algebra.ofId O (DualNumber O)).comp e)
      (fun i => TrivSqZeroExt.inr (if i = j then (1 : O) else 0))
      (fun i => ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩)
    have h3 : (TrivSqZeroExt.fstHom O O O).comp φ = e := by
      refine GlobalTheory.NilCoord.ext_of_nil π hπ _ _ (fun b => ?_) (fun i => ?_)
      · simpa [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl] using (h1 b).map (TrivSqZeroExt.fstHom O O O)
      · rw [AlgHom.comp_apply, h2, map_add]
        exact add_zero _
    obtain ⟨v, hv⟩ := exists_lift_atPrime e S φ (fun b hb => by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      rwa [← h3] at hb)
    refine ⟨v, ?_, fun i => ?_⟩
    · refine IsLocalization.algHom_ext ((IsLocalRing.maximalIdeal O).comap e).primeCompl ?_
      ext b
      show (v (algebraMap B S b)).fst = eS (algebraMap B S b)
      rw [hv, he]
      exact AlgHom.congr_fun h3 b
    · simp [x, hv, h2, Algebra.ofId_apply]
  · let A := MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)
    let ρ : MvPolynomial (Fin g) O →ₐ[O] A :=
      MvPolynomial.aeval (fun j => algebraMap O A (e (π (MvPolynomial.X j))) + MvPowerSeries.X j)
    letI : Algebra (MvPolynomial (Fin g) O) A := ρ.toRingHom.toAlgebra
    let J : Ideal A := Ideal.span (Set.range MvPowerSeries.X)
    have hf₀ : ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).comp π =
        (Ideal.Quotient.mkₐ O J).comp ρ := by
      apply MvPolynomial.algHom_ext
      intro j
      simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ρ,
        MvPolynomial.aeval_X, Algebra.ofId_apply]
      rw [eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
      exact Ideal.subset_span ⟨j, rfl⟩
    let f₀ : B →ₐ[MvPolynomial (Fin g) O] A ⧸ J :=
      { ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).toRingHom with
        commutes' := fun p => AlgHom.congr_fun hf₀ p }
    obtain ⟨φ', hφ'⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := J) f₀
    have hc : ∀ p, φ' (π p) = ρ p := fun p => φ'.commutes p
    let φ : B →ₐ[O] A := { φ'.toRingHom with
      commutes' := fun r => by
        show φ' (algebraMap O B r) = _
        rw [← π.commutes, hc, ρ.commutes] }
    have hφ : ∀ b, φ b = φ' b := fun _ => rfl
    have hJ : J ≤ RingHom.ker (MvPowerSeries.constantCoeff) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact MvPowerSeries.constantCoeff_X i
    obtain ⟨v, hv⟩ := exists_lift_atPrime e S φ (fun b hb => by
      have e1 : Ideal.Quotient.mk J (φ' b) = Ideal.Quotient.mk J (algebraMap O A (e b)) :=
        AlgHom.congr_fun hφ' b
      rw [Ideal.Quotient.eq] at e1
      have e2 := hJ e1
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at e2
      rw [hφ, MvPowerSeries.isUnit_iff_constantCoeff, e2]
      exact (hb.map _).map _)
    refine ⟨v, fun i => ?_⟩
    simp only [x]
    rw [hv, map_sub, AlgHom.commutes, hφ, hc]
    simp [ρ]

end Alg

section Geo

variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Sp O)} [GrpObj G]

theorem exists_pt_of_aug (C : Chart.Chart G) {A : Type} [CommRing A] [Algebra O A] (α : A →ₐ[O] O)
    (hα : ∀ a, IsUnit (α a) → IsUnit a) (z : specO O A ⟶ G) (hz : ptMap α ≫ z = 1) :
    ∃ h : Γ(G.left, C.U) →ₐ[O] A, z = Chart.pt C h ∧ α.comp h = Chart.eps C := by
  haveI : IsLocalHom α.toRingHom := ⟨hα⟩
  haveI : IsLocalRing A := RingHom.domain_isLocalRing α.toRingHom
  have hz' : Chart.spMap α ≫ z = Chart.pt C ((Algebra.ofId O O).comp (Chart.eps C)) :=
    hz.trans (Chart.pt_eps C O).symm
  have hU : ⊤ ≤ z.left ⁻¹ᵁ C.U := by
    intro p _
    have hsp : (p : PrimeSpectrum A) ⤳ IsLocalRing.closedPoint A :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum A).isPrime.ne_top)
    refine hsp.mem_open (z.left ⁻¹ᵁ C.U).isOpen ?_
    let p₀ : ↥(Spec (CommRingCat.of O)) := IsLocalRing.closedPoint O
    have hp : (Spec.map (CommRingCat.ofHom α.toRingHom)).base p₀ = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint α.toRingHom
    have e := congrArg (fun y : Chart.sp O ⟶ G => y.left.base p₀) hz'
    simp only [Over.comp_left, Chart.spMap_left, Chart.pt_left, Scheme.Hom.comp_apply] at e
    show z.left (IsLocalRing.closedPoint A) ∈ C.U
    rw [← hp, e]
    exact C.hU.range_fromSpec.subset (Set.mem_range_self _)
  obtain ⟨h, rfl⟩ := Chart.exists_pt C z hU
  refine ⟨h, rfl, ?_⟩
  rw [Chart.spMap_pt] at hz'
  exact Chart.pt_injective C hz'

theorem exists_local_ring (G : Over (Sp O)) [GrpObj G] (g : ℕ)
    (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (u : specO O S ⟶ G) (eS : S →ₐ[O] O)
      (x : Fin g → S),
      (∀ s, IsUnit (eS s) → IsUnit s) ∧
      (∀ (A : Type) [CommRing A] [Algebra O A], ptMap ((Algebra.ofId O A).comp eS) ≫ u = 1) ∧
      (∀ (A : Type) [CommRing A] [Algebra O A] (φ ψ : S →ₐ[O] A),
        ptMap φ ≫ u = ptMap ψ ≫ u → φ = ψ) ∧
      (∀ (A : Type) [CommRing A] [Algebra O A] (α : A →ₐ[O] O), (∀ a, IsUnit (α a) → IsUnit a) →
        ∀ z : specO O A ⟶ G, ptMap α ≫ z = 1 → ∃ φ : S →ₐ[O] A, ptMap φ ≫ u = z) ∧
      RingHom.ker eS = Ideal.span (Set.range x) ∧
      (∀ j, ∃ v : S →ₐ[O] DualNumber O, (TrivSqZeroExt.fstHom O O O).comp v = eS ∧
        ∀ i, v (x i) = TrivSqZeroExt.inr (if i = j then 1 else 0)) ∧
      ∃ ρ : S →ₐ[O] MvPowerSeries (Fin g) (IsLocalRing.ResidueField O),
        ∀ i, ρ (x i) = MvPowerSeries.X i := by
  obtain ⟨C, π, hπ⟩ := GlobalTheory.NilCoord.exists_etale_chart G g hG
  let e := Chart.eps C
  let S := Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap e)
  obtain ⟨eS, he⟩ := exists_lift_atPrime e S e (fun _ h => h)
  obtain ⟨x, hx⟩ := exists_coords π hπ e S eS he
  let κ : Γ(G.left, C.U) →ₐ[O] S := IsScalarTower.toAlgHom O _ S
  have hpt : ∀ (A : Type) [CommRing A] [Algebra O A] (φ : S →ₐ[O] A),
      ptMap φ ≫ Chart.pt C κ = Chart.pt C (φ.comp κ) := fun A _ _ φ => Chart.spMap_pt C φ κ
  refine ⟨S, inferInstance, inferInstance, Chart.pt C κ, eS, x, isUnit_of_aug e S eS he,
    fun A _ _ => ?_, fun A _ _ φ ψ h => ?_, fun A _ _ α hα z hz => ?_, hx⟩
  · rw [hpt, ← Chart.pt_eps C A]
    congr 1
    ext b
    exact congrArg (algebraMap O A) (he b)
  · rw [hpt, hpt] at h
    have h1 := Chart.pt_injective C h
    refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext
      ((IsLocalRing.maximalIdeal O).comap e).primeCompl ?_)
    ext b
    exact AlgHom.congr_fun h1 b
  · obtain ⟨h, rfl, hh⟩ := exists_pt_of_aug C α hα z hz
    obtain ⟨φ, hφ⟩ := exists_lift_atPrime e S h (fun b hb => hα _ (by
      rwa [← AlgHom.comp_apply, hh]))
    refine ⟨φ, ?_⟩
    rw [hpt]
    congr 1
    ext b
    exact hφ b

end Geo

theorem local_presentation : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O), ptMap ε ≫ y = 1 → ∀ (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π ∧ RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) ∧ RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) ∧ (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) ∧ (∀ i, ρ (x i) = MvPowerSeries.X i) ∧ ∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0 := by
  intro O _ _ G _ _ n H _ _ _ y g hG hy huniv ε hε T _ _ _ _ _ εT hεT
  obtain ⟨S, _, _, u, eS, x, hloc, hone, hinj, hex, hker, hv, ρ, hρ⟩ := exists_local_ring G g hG
  have hcomp : ∀ {A A' A'' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']
      [CommRing A''] [Algebra O A''] (φ : A →ₐ[O] A') (ψ : A' →ₐ[O] A'') (z : specO O A ⟶ G),
      ptMap (ψ.comp φ) ≫ z = ptMap ψ ≫ ptMap φ ≫ z := fun φ ψ z => by
    rw [← Category.assoc, GlobalTheory.TangentPow.ptMap_comp_ptMap]
  have hone' : ptMap eS ≫ u = 1 := by
    have := hone O
    rwa [show (Algebra.ofId O O).comp eS = eS from by ext; simp] at this
  obtain ⟨ν, hν⟩ := hex S eS hloc (u ^ n) (by rw [comp_pow, hone', one_pow])
  have heν : eS.comp ν = eS := hinj _ _ _ (by rw [hcomp, hν, comp_pow, hone', one_pow])
  have hxk : ∀ i, eS (x i) = 0 := fun i => by
    have : x i ∈ RingHom.ker eS := hker ▸ Ideal.subset_span ⟨i, rfl⟩
    exact this
  have ha : ∀ i, ∃ c : Fin g → S, ∑ j, c j * x j = ν (x i) := fun i => by
    rw [← Ideal.mem_span_range_iff_exists_fun, ← hker, RingHom.mem_ker, ← AlgHom.comp_apply, heν,
      hxk]
  choose a ha using ha
  have hax : Matrix.mulVec (Matrix.of a) x = fun i => ν (x i) := funext fun i => ha i
  let κ : H →ₐ[O] T := IsScalarTower.toAlgHom O H T
  have hεκ : εT.comp κ = ε := AlgHom.ext hεT
  obtain ⟨π, hπ⟩ := hex T εT (isUnit_of_aug ε T εT hεT) (ptMap κ ≫ y) (by rw [← hcomp, hεκ, hε])
  have hεπ : εT.comp π = eS := hinj _ _ _ (by rw [hcomp, hπ, ← hcomp, hεκ, hε, hone'])
  have hπν : π.comp ν = (Algebra.ofId O T).comp eS := hinj _ _ _ (by
    rw [hone, hcomp, hν, comp_pow, hπ, ← comp_pow, hy, comp_one])
  set K : Ideal S := Ideal.span (Set.range fun i => ν (x i)) with hK
  have hKπ : K ≤ RingHom.ker π := by
    rw [hK, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have := AlgHom.congr_fun hπν (x i)
    simpa [hxk, RingHom.mem_ker] using this
  let q : S →ₐ[O] S ⧸ K := Ideal.Quotient.mkₐ O K
  have hqν : q.comp ν = (Algebra.ofId O (S ⧸ K)).comp eS := by
    ext s
    have h1 : s - algebraMap O S (eS s) ∈ Ideal.span (Set.range x) := by
      rw [← hker]
      simp [RingHom.mem_ker]
    have h2 := Ideal.mem_map_of_mem ν h1
    rw [Ideal.map_span, ← Set.range_comp, map_sub, AlgHom.commutes] at h2
    exact Ideal.Quotient.eq.mpr h2
  obtain ⟨φ, hφ, -⟩ := huniv (S ⧸ K) (ptMap q ≫ u) (by rw [← comp_pow, ← hν, ← hcomp, hqν, hone])
  let πq : (S ⧸ K) →ₐ[O] T := Ideal.Quotient.liftₐ K π fun s hs => hKπ hs
  have hπq : πq.comp q = π := by ext; rfl
  have hπφ : πq.comp φ = κ := by
    refine (huniv T (ptMap κ ≫ y) (by rw [← comp_pow, hy, comp_one])).unique ?_ rfl
    rw [hcomp, hφ, ← hcomp, hπq, hπ]
  obtain ⟨ψ, hψ⟩ := exists_lift_atPrime ε T φ (fun h hh => by
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (φ h)
    have : eS s = ε h := by
      rw [← hεπ, ← hπq, ← hεκ, ← hπφ]
      simp only [AlgHom.comp_apply]
      rw [← hs]
      rfl
    rw [← hs]
    exact (hloc s (this ▸ hh)).map _)
  have hψκ : ψ.comp κ = φ := AlgHom.ext hψ
  have hψπ : ψ.comp π = q := hinj _ _ _ (by rw [hcomp, hπ, ← hcomp, hψκ, hφ])
  have hid : πq.comp ψ = AlgHom.id O T := by
    refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext
      ((IsLocalRing.maximalIdeal O).comap ε).primeCompl ?_)
    ext h
    show πq (ψ (algebraMap H T h)) = algebraMap H T h
    rw [hψ]
    exact AlgHom.congr_fun hπφ h
  have hsurj : Function.Surjective π := fun t => by
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (ψ t)
    refine ⟨s, ?_⟩
    have : πq (ψ t) = t := AlgHom.congr_fun hid t
    rw [← this, ← hs]
    rfl
  refine ⟨S, inferInstance, inferInstance, π, x, Matrix.of a, ρ.toRingHom, hsurj, ?_, ?_, ?_, hρ, ?_⟩
  · rw [hax]
    refine le_antisymm (fun s hs => ?_) hKπ
    have h1 : π s = 0 := hs
    have h2 : ψ (π s) = q s := AlgHom.congr_fun hψπ s
    rw [h1, map_zero] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2.symm
  · refine le_antisymm (fun t ht => ?_) ?_
    · obtain ⟨s, rfl⟩ := hsurj t
      have h1 : s ∈ RingHom.ker eS := by
        rw [← hεπ]
        exact ht
      have h2 := Ideal.mem_map_of_mem π (hker ▸ h1)
      rwa [Ideal.map_span, ← Set.range_comp] at h2
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (AlgHom.congr_fun hεπ (x i)).trans (hxk i)
  · intro i j
    obtain ⟨v, hv1, hv2⟩ := hv j
    have h1 := GlobalTheory.TangentPow.pow_eq_scale_comp (y := ptMap v ≫ u) (by rw [← hcomp, hv1, hone']) n
    rw [← comp_pow, ← hν, ← hcomp, ← hcomp] at h1
    have h2 := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun (hinj _ _ _ h1) (x i))
    have h3 : ∀ s, (v s).fst = eS s := fun s => AlgHom.congr_fun hv1 s
    rw [AlgHom.comp_apply, ← ha] at h2
    have h4 : εT (π (Matrix.of a i j)) = eS (a i j) := AlgHom.congr_fun hεπ _
    rw [h4]
    have h5 : eS (a i j) = n * TrivSqZeroExt.snd (if i = j then DualNumber.eps else 0 : DualNumber O) := by
      simpa [hv2, h3, TrivSqZeroExt.snd_sum] using h2
    rw [h5]
    split_ifs <;> simp
  · intro c hc
    show ρ (algebraMap O S c) = 0
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O (IsLocalRing.ResidueField O),
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff c).mpr hc, map_zero]

end GlobalTheory.TorsionPres
