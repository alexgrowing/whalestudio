import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.TrdegPf
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.TowerTrdeg

def dualHom {k K L : Type} [Field k] [Field K] [Field L] [Algebra k K] (f : K →+* L)
    (d : Derivation k K K) : K →+* DualNumber L where
  toFun a := TrivSqZeroExt.inl (f a) + TrivSqZeroExt.inr (f (d a))
  map_one' := by ext <;> simp
  map_mul' a c := by ext <;> simp [Derivation.leibniz] <;> ring
  map_zero' := by ext <;> simp
  map_add' a c := by ext <;> simp <;> ring

theorem exists_basis {K : Type} [Field K] (c : ℂ →+* K) {n : ℕ} (x : Fin n → K) (hx : TrBasis c x) :
    letI := c.toAlgebra
    ∃ b : Module.Basis (Fin n) K Ω[K⁄ℂ], ∀ i, b i = KaehlerDifferential.D ℂ K (x i) := by
  letI := c.toAlgebra
  have hx' : IsTranscendenceBasis ℂ x := hx
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin ℂ (Set.range x)) K := hx'.isAlgebraic_field
  haveI : CharZero (IntermediateField.adjoin ℂ (Set.range x)) :=
    charZero_of_injective_algebraMap (algebraMap ℂ _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin ℂ (Set.range x)) K := inferInstance
  exact exists_basis_kaehler_of_algebraicIndependent hx'.1

theorem exists_derivation {L P : Type} [Field L] [CommRing P] [Algebra P L] [Algebra ℂ L]
    [Algebra.FormallyEtale P L] (g : P →+* DualNumber L)
    (hfst : (TrivSqZeroExt.fstHom L L L).toRingHom.comp g = algebraMap P L)
    (hc : ∀ a : ℂ, ∃ p : P, algebraMap P L p = algebraMap ℂ L a ∧ (g p).snd = 0) :
    ∃ D : Derivation ℂ L L, ∀ p, D (algebraMap P L p) = (g p).snd := by
  letI : Algebra P (DualNumber L) := g.toAlgebra
  let f : DualNumber L →ₐ[P] L :=
    { (TrivSqZeroExt.fstHom L L L).toRingHom with
      commutes' := fun p => RingHom.congr_fun hfst p }
  have hs : Function.Surjective f := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hn : IsNilpotent (RingHom.ker (f : DualNumber L →+* L)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha c hc
    have ha' : a.fst = 0 := ha
    have hc' : c.fst = 0 := hc
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hc']
  let φ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id P L) f hs hn
  have hφ1 : ∀ l, (φ l).fst = l := fun l =>
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id P L) f hs hn l
  have hφ2 : ∀ p : P, φ (algebraMap P L p) = g p := fun p => φ.commutes p
  have hφc : ∀ a : ℂ, (φ (algebraMap ℂ L a)).snd = 0 := by
    intro a
    obtain ⟨p, hp, hp'⟩ := hc a
    rw [← hp, hφ2, hp']
  let D : Derivation ℂ L L := Derivation.mk'
    { toFun := fun l => (φ l).snd
      map_add' := fun a c => by simp only [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun a l => by
        simp only [RingHom.id_apply, Algebra.smul_def a l, map_mul, TrivSqZeroExt.snd_mul,
          hφ1, hφc, smul_zero, add_zero, smul_eq_mul]
        rw [Algebra.smul_def] }
    fun a c => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, TrivSqZeroExt.snd_mul, hφ1,
        smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
  exact ⟨D, fun p => by
    show (φ (algebraMap P L p)).snd = _
    rw [hφ2]⟩

theorem derivation_eq_zero {L P : Type} [Field L] [CommRing P] [Algebra P L] [Algebra ℂ L]
    [Algebra.FormallyUnramified P L] (D : Derivation ℂ L L) (hD : ∀ p, D (algebraMap P L p) = 0) :
    D = 0 := by
  let DP : Derivation P L L := Derivation.mk'
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun p l => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def p l, Derivation.leibniz, hD, smul_zero, add_zero, smul_eq_mul,
          Algebra.smul_def] }
    fun a c => D.leibniz a c
  ext l
  have e := Derivation.liftKaehlerDifferential_comp_D DP l
  rw [Subsingleton.elim (KaehlerDifferential.D P L l) 0, map_zero] at e
  exact e.symm

theorem trBasis_append : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ)
    (R : Subring K) (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
    IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
    TrBasis cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))) := by
  intro K L _ _ cK cL n r R T ι ψ τ x h hx
  classical
  letI := cK.toAlgebra
  letI := cL.toAlgebra
  obtain ⟨b, hb⟩ := exists_basis cK _ hx
  have hιinj : Function.Injective ι := Function.LeftInverse.injective h.retr
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, c, hcR, hc0, e⟩ := h.base.frac z
    exact ⟨⟨a, ha⟩, ⟨c, hcR⟩, by show z = a / c; rw [eq_div_iff hc0]; exact e⟩
  let j : R →+* L := T.subtype.comp ι
  have hj : Function.Injective j := Subtype.val_injective.comp hιinj
  let ι' : K →+* L := IsFractionRing.lift hj
  have hι' : ∀ a : R, ι' (a : K) = (ι a : L) := fun a => IsFractionRing.lift_algebraMap hj a
  have hcst : ∀ a : ℂ, ι' (cK a) = cL a := fun a =>
    (hι' ⟨cK a, h.base.const_mem a⟩).trans (h.const a)
  let P := MvPolynomial (Fin r) R
  let eP : P →+* T := MvPolynomial.eval₂Hom ι τ
  letI : Algebra P T := eP.toAlgebra
  haveI : Algebra.FormallyEtale P T := h.etale
  haveI : IsFractionRing T L := IsFractionRing.of_field T L fun z => by
    obtain ⟨a, ha, c, hcT, hc0, e⟩ := h.top.frac z
    exact ⟨⟨a, ha⟩, ⟨c, hcT⟩, by show z = a / c; rw [eq_div_iff hc0]; exact e⟩
  haveI : Algebra.FormallyEtale T L := .of_isLocalization (nonZeroDivisors T)
  letI : Algebra P L := (T.subtype.comp eP).toAlgebra
  haveI : IsScalarTower P T L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FormallyEtale P L := .comp P T L
  have hPC : ∀ a : R, algebraMap P L (MvPolynomial.C a) = (ι a : L) := fun a =>
    congrArg Subtype.val (MvPolynomial.eval₂Hom_C ι τ a)
  have hPX : ∀ i, algebraMap P L (MvPolynomial.X i) = (τ i : L) := fun i =>
    congrArg Subtype.val (MvPolynomial.eval₂Hom_X' ι τ i)

  have exD : ∀ (d : Derivation ℂ K K) (v : Fin r → L), ∃ D : Derivation ℂ L L,
      (∀ a : R, D (ι a : L) = ι' (d a)) ∧ ∀ i, D (τ i : L) = v i := by
    intro d v
    let g : P →+* DualNumber L := MvPolynomial.eval₂Hom ((dualHom ι' d).comp R.subtype)
      fun i => TrivSqZeroExt.inl (τ i : L) + TrivSqZeroExt.inr (v i)
    have gC : ∀ a : R, g (MvPolynomial.C a) =
        TrivSqZeroExt.inl (ι' a) + TrivSqZeroExt.inr (ι' (d a)) := fun a => by
      simp only [g]; rw [MvPolynomial.eval₂Hom_C]; rfl
    have gX : ∀ i, g (MvPolynomial.X i) = TrivSqZeroExt.inl (τ i : L) + TrivSqZeroExt.inr (v i) :=
      fun i => by simp only [g]; rw [MvPolynomial.eval₂Hom_X']
    have hfst : (TrivSqZeroExt.fstHom L L L).toRingHom.comp g = algebraMap P L := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [hPC a, RingHom.comp_apply, gC, ← hι' a]
        simp
      · intro i
        rw [hPX i, RingHom.comp_apply, gX]
        simp
    obtain ⟨D, hD⟩ := exists_derivation g hfst fun a => ⟨MvPolynomial.C ⟨cK a, h.base.const_mem a⟩,
      (hPC _).trans (h.const a), by
        rw [gC]
        have e2 : d (cK a) = 0 := Derivation.map_algebraMap d a
        simp [e2]⟩
    refine ⟨D, fun a => ?_, fun i => ?_⟩
    · rw [← hPC, hD, gC]; simp
    · rw [← hPX, hD, gX]; simp
  choose Dof hDof1 hDof2 using exD
  set y : Fin (r + n) → L := Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)) with hy
  let dK : Fin n → Derivation ℂ K K := fun k => (b.coord k).compDer (KaehlerDifferential.D ℂ K)
  have hdK : ∀ k k', dK k (x k' : K) = if k = k' then 1 else 0 := by
    intro k k'
    show b.coord k (KaehlerDifferential.D ℂ K (x k')) = _
    rw [← hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hkk : k = k'
    · subst hkk; simp
    · rw [if_neg (Ne.symm hkk), if_neg hkk]
  let Dfam : Fin (r + n) → Derivation ℂ L L :=
    Fin.addCases (fun i => Dof 0 (Pi.single i 1)) (fun k => Dof (dK k) 0)
  have hval : ∀ m m', Dfam m (y m') = if m = m' then 1 else 0 := by
    intro m m'
    induction m using Fin.addCases with
    | left i =>
      induction m' using Fin.addCases with
      | left i' =>
        simp only [Dfam, hy, Fin.addCases_left, Fin.append_left, hDof2, Pi.single_apply]
        by_cases hii : i = i'
        · subst hii; simp
        · rw [if_neg (Ne.symm hii), if_neg]
          intro e; exact hii (Fin.castAdd_injective _ _ e)
      | right k' =>
        have hne : Fin.castAdd n i ≠ Fin.natAdd r k' := by
          rw [Ne, Fin.ext_iff]; simp; omega
        simp only [Dfam, hy, Fin.addCases_left, Fin.append_right, hDof1, if_neg hne]
        simp
    | right k =>
      induction m' using Fin.addCases with
      | left i' =>
        have hne : Fin.natAdd r k ≠ Fin.castAdd n i' := by
          rw [Ne, Fin.ext_iff]; simp; omega
        simp only [Dfam, hy, Fin.addCases_right, Fin.append_left, hDof2, if_neg hne]
        simp
      | right k' =>
        simp only [Dfam, hy, Fin.addCases_right, Fin.append_right, hDof1, hdK]
        by_cases hkk : k = k'
        · subst hkk; simp
        · rw [if_neg hkk, if_neg, map_zero]
          intro e; exact hkk (Fin.natAdd_injective _ _ e)
  have hlin : LinearIndependent L (fun m => KaehlerDifferential.D ℂ L (y m)) := by
    let F : Ω[L⁄ℂ] →ₗ[L] (Fin (r + n) → L) :=
      LinearMap.pi fun m => (Dfam m).liftKaehlerDifferential
    refine LinearIndependent.of_comp F ?_
    convert (Pi.basisFun L (Fin (r + n))).linearIndependent using 1
    funext m' m
    simp only [Function.comp_apply, F, LinearMap.pi_apply, Derivation.liftKaehlerDifferential_comp_D,
      hval, Pi.basisFun_apply, Pi.single_apply]
  have hind : AlgebraicIndependent ℂ y := ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence ℂ L (r + n) y hlin
  have uniq : ∀ D : Derivation ℂ L L, (∀ m, D (y m) = 0) → D = 0 := by
    intro D hD0
    have h1 : ∀ i, D (τ i : L) = 0 := fun i => by
      have := hD0 (Fin.castAdd n i); rwa [hy, Fin.append_left] at this
    have h2 : ∀ k, D (ι (x k) : L) = 0 := fun k => by
      have := hD0 (Fin.natAdd r k); rwa [hy, Fin.append_right] at this
    have hK : ∀ a : K, D (ι' a) = 0 := by
      letI : Algebra K L := ι'.toAlgebra
      haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun a => (hcst a).symm
      let D' : Derivation ℂ K L := Derivation.mk'
        { toFun := fun a => D (ι' a)
          map_add' := fun a c => by simp only [map_add]
          map_smul' := fun a c => by
            simp only [RingHom.id_apply]
            rw [Algebra.smul_def, map_mul,
              show ι' (algebraMap ℂ K a) = algebraMap ℂ L a from hcst a, ← Algebra.smul_def,
              D.map_smul] }
        fun a c => by
          show D (ι' (a * c)) = a • D (ι' c) + c • D (ι' a)
          rw [map_mul, Derivation.leibniz, Algebra.smul_def a, Algebra.smul_def c,
            RingHom.algebraMap_toAlgebra, smul_eq_mul, smul_eq_mul]
      have hz : D'.liftKaehlerDifferential = 0 := b.ext fun k => by
        rw [hb, Derivation.liftKaehlerDifferential_comp_D, LinearMap.zero_apply]
        show D (ι' (x k : K)) = 0
        rw [hι']; exact h2 k
      intro a
      have e := congrArg (fun E => E (KaehlerDifferential.D ℂ K a)) hz
      simp only [Derivation.liftKaehlerDifferential_comp_D, LinearMap.zero_apply] at e
      exact e
    refine derivation_eq_zero (P := P) D fun p => ?_
    induction p using MvPolynomial.induction_on with
    | C a => rw [hPC, ← hι']; exact hK _
    | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
    | mul_X p i hp => rw [map_mul, Derivation.leibniz, hp, hPX, h1, smul_zero, smul_zero, add_zero]
  have hspan : Submodule.span L (Set.range fun m => KaehlerDifferential.D ℂ L (y m)) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hD : f.compDer (KaehlerDifferential.D ℂ L) = 0 := uniq _ fun m =>
      hle (Submodule.subset_span ⟨m, rfl⟩)
    apply hf0
    refine LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation ℂ L) fun l => ?_
    have e := congrArg (fun E : Derivation ℂ L L => E l) hD
    simpa using e
  have hess : Algebra.EssFiniteType ℂ L := by
    letI : Algebra ℂ T := (cL.codRestrict T h.top.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ T := h.top.essFiniteType
    haveI : IsScalarTower ℂ T L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Algebra.EssFiniteType T L := .of_isLocalization L (nonZeroDivisors T)
    exact .comp ℂ T L
  have hrank : Algebra.trdeg ℂ L ≤ Cardinal.mk (Fin (r + n)) := by
    rw [← rank_kaehler_eq_trdeg, ← rank_top, ← hspan]
    exact (rank_span_le _).trans Cardinal.mk_range_le
  exact hind.isTranscendenceBasis_of_trdeg_le_of_finite hrank

end GlobalTheory.FieldPair.TowerTrdeg
