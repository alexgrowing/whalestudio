import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage

noncomputable section

namespace GlobalTheory.HubLoc

section A
open Formalism Formalism.BasicNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open scoped Pointwise

def SqrtKur (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 3 → p ≠ l → ∀ y : Formalism.BasicNotions.Loc.Om l, y ^ 2 = -(p : Formalism.BasicNotions.Loc.Om l) → y ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l

section Local

open Formalism.BasicNotions.Loc Polynomial

theorem dickson_hom {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : A) (N : ℕ) :
    (dickson 1 (1 : B) N).eval (f x) = f ((dickson 1 (1 : A) N).eval x) := by
  have h : dickson 1 (1 : B) N = (dickson 1 (1 : A) N).map f := by rw [map_dickson, map_one]
  rw [h, eval_map, eval₂_hom]

variable {l : ℕ} [Fact l.Prime] {R : Ranks} (H : Host R) (J : H.E →+* Om l)

def thL (p : ℕ) : H.E := H.toHostRaw.thM (ordCompl[p] H.condN)

theorem root_mem_Kur (y : Om l) (hy : y ^ (ordCompl[l] H.condN) = 1) : y ∈ (MaximalUnramifiedExtension l).toSubfield :=
  IntermediateField.subset_adjoin _ _ ⟨_, Nat.ordCompl_pos l H.toHostRaw.condN_ne_zero,
    Nat.not_dvd_ordCompl Fact.out H.toHostRaw.condN_ne_zero, hy⟩

theorem theta_mem_Kur : J (thL H l) ∈ MaximalUnramifiedExtension l :=
  H.toHostRaw.thM_image_mem J (MaximalUnramifiedExtension l).toSubfield (Nat.ordCompl_dvd _ _) (root_mem_Kur H)

theorem adjoin_gen_top {p : ℕ} (hp : p.Prime) (hpS : ¬ p ∣ H.QS) :
    IntermediateField.adjoin ℚ ({thL H p, H.sqq, H.sqd} : Set H.E) = ⊤ := by
  have := H.hostE_isGalois
  rw [← IsGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ ({thL H p, H.sqq, H.sqd} : Set H.E)),
    ← IntermediateField.fixedField_bot]
  congr 1
  rw [eq_bot_iff]
  intro σ hσ
  have hfix : ∀ x ∈ ({thL H p, H.sqq, H.sqd} : Set H.E), σ x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x (IntermediateField.subset_adjoin _ _ hx)
  have hq0 : H.sqq ≠ 0 := by
    intro h
    have h1 := H.sqq_sq
    rw [h] at h1
    have h2 : (H.q : H.E) = 0 := by simpa using h1.symm
    exact H.hyp.1.ne_zero (by exact_mod_cast h2)
  refine H.toHostRaw.eq_one_of_mem_congrGal H.flPS hp hpS σ
    ((H.toHostRaw.fix_thM_iff _ σ).1 (hfix _ (by simp [thL]))) ?_
    ((H.galE_mem_Psi_iff σ).2 (hfix _ (by simp)))
  have h1 := (H.gal_sqq σ).symm.trans (hfix H.sqq (by simp))
  refine (Int.units_eq_one_or _).resolve_right fun h => hq0 ?_
  rw [h] at h1
  have h2 : (2 : H.E) * H.sqq = 0 := by
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at h1
    linear_combination -h1
  simpa using h2

theorem image_le (hlS : ¬ l ∣ H.QS) (M : IntermediateField ℚ_[l] (Om l)) (h1 : J (thL H l) ∈ M)
    (h2 : J (H.sqq) ∈ M) (h3 : J (H.sqd) ∈ M) (x : H.E) : J x ∈ M := by
  have hx : x ∈ IntermediateField.adjoin ℚ ({thL H l, H.sqq, H.sqd} : Set H.E) := by
    rw [adjoin_gen_top H Fact.out hlS]; trivial
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | rfl | rfl
    exacts [h1, h2, h3]
  | algebraMap r =>
    rw [eq_ratCast, map_ratCast]
    exact SubfieldClass.ratCast_mem M r
  | add a b _ _ ha hb => rw [map_add]; exact M.add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact M.inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact M.mul_mem ha hb

end Local

theorem liesOver_of_mem {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  constructor
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 E)) v.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa [placesOver] using hv
  exact hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) hle

theorem ramIdx_eq_one {R : Ranks} (H : Host R) {l : ℕ} (hl : l.Prime) (hlN : ¬ l ∣ H.condN)
    (v : HeightOneSpectrum (𝓞 H.E)) (hv : v ∈ placesOver H.E l) :
    v.asIdeal.ramificationIdx ℤ = 1 := by
  have hgal := H.hostE_isGalois
  have : IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have := liesOver_of_mem hl hv
  have := v.isPrime
  have : Fact l.Prime := ⟨hl⟩
  have hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible).isPrime
  have hIn : Nat.card (v.asIdeal.inertia Gal(H.E/ℚ)) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨1, fun ⟨σ, hσ⟩ => Subtype.ext ?_⟩
    rw [AddSubgroup.mem_inertia] at hσ
    exact ((H.der.frob l hlN v.asIdeal).2.2.2 σ).mp hσ
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v.asIdeal Gal(H.E/ℚ),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(H.E/ℚ)) (Ideal.span {(l : ℤ)}) v.asIdeal, hIn]

end A

section B
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions.Loc
section Local

open Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime] {R : Ranks} (H : Host R) (J : H.E →+* Om l)

theorem image_mem_Kur (hlN : ¬ l ∣ H.condN) (x : H.E) : J x ∈ MaximalUnramifiedExtension l :=
  H.toHostRaw.image_mem_of_roots J (MaximalUnramifiedExtension l).toSubfield (fun _ hy => IntermediateField.subset_adjoin _ _
    ⟨H.condN, Nat.pos_of_ne_zero H.toHostRaw.condN_ne_zero, hlN, hy⟩) x

theorem kw_le_Kur (hlN : ¬ l ∣ H.condN) (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) : Kw.1 ≤ MaximalUnramifiedExtension l := by
  have : FiniteDimensional ℚ_[l] ↥Kw.1 := Kw.2
  have hle : K0 Kw ≤ Kw.1 := inf_le_left
  have hfd : FiniteDimensional ℚ_[l] ↥(K0 Kw) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  have hcl : IsClosed ((K0 Kw : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (K0 Kw).toSubalgebra.toSubmodule
  intro x hx
  have hx0 : x ∈ K0 Kw := by
    refine closure_minimal ?_ hcl (hdense hx)
    rintro _ ⟨y, rfl⟩
    exact ⟨hE y, image_mem_Kur H J hlN y⟩
  exact (inf_le_right : K0 Kw ≤ MaximalUnramifiedExtension l) hx0

end Local

variable {D : D7}

theorem kw_le_Kur_of_ne (i : D.nd.Loc) (hlN : ¬ D.nd.l i ∣ D.host.condN)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    (D.nbr i w hw).Kw.1 ≤ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension (D.nd.l i) :=
  kw_le_Kur D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) hlN
    (D.nbr i w hw).Kw (D.nbr i w hw).j_E (D.nbr i w hw).j_dense

end B

section C
open Formalism
open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct Polynomial

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

local notation "μ" => mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL)

theorem FilV_anti' (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro _ ⟨x, rfl⟩
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := PD.Fil_anti a
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) x, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]
  rfl

theorem mu_mul (c d : K) (x : V ⊗[Qp] BdR) : μ (c * d) x = μ c (μ d x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mulVdR, mul_assoc]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem mu_add (c d : K) (x : V ⊗[Qp] BdR) : μ (c + d) x = μ c x + μ d x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mulVdR, add_mul, tmul_add]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]; abel

theorem mu_alg (q : Qp) (x : V ⊗[Qp] BdR) : μ (algebraMap Qp K q) x = algebraMap Qp LL q • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    rw [← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, smul_tmul', algebraMap_smul, smul_tmul]
  | add a b ha hb => rw [map_add, smul_add, ha, hb]

theorem mu_pow (c : K) (n : ℕ) (x : V ⊗[Qp] BdR) : μ (c ^ n) x = ((μ c) ^ n) x := by
  induction n generalizing x with
  | zero =>
    have := mu_alg (K := K) (LL := LL) (1 : Qp) x
    simpa using this
  | succ n ih => rw [pow_succ, mu_mul, ih, pow_succ, Module.End.mul_apply]

theorem mu_aeval (c : K) (p : Qp[X]) (x : V ⊗[Qp] BdR) :
    aeval (μ c) (p.map (algebraMap Qp LL)) x = μ (aeval c p) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hq, map_add, mu_add]
  | monomial n a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, mu_mul, mu_alg, mu_pow, Module.End.mul_apply,
      Module.algebraMap_end_apply]

theorem mu_mem (c : K) (a : ℤ) (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) :
    μ c x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a := by
  refine ⟨?_, ?_⟩
  · have hc : ∀ g y, actVdR PD ρ g (μ c y) = μ c (actVdR PD ρ g y) := by
      intro g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [mulVdR, actVdR]
      | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
    have h1 := hx.1
    simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at h1 ⊢
    intro g
    rw [hc, h1 g]
  · obtain ⟨y, rfl⟩ := hx.2
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      refine ⟨v ⊗ₜ ⟨c • (b : BdR), (PD.Fil a).smul_mem c b.2⟩, ?_⟩
      simp [mulVdR, Algebra.smul_def]
    | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb

theorem aeval_mem {W : Type} [AddCommGroup W] [Module LL W] (M : Module.End LL W) (U : Submodule LL W)
    (h : ∀ x ∈ U, M x ∈ U) (q : LL[X]) (x : W) (hx : x ∈ U) : aeval M q x ∈ U := by
  have hp : ∀ n : ℕ, (M ^ n) x ∈ U := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact h _ ih
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact U.add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact U.smul_mem _ (hp n)

theorem jump_of_total [CharZero Qp] [FiniteDimensional Qp K] (hs : Nat.card (K →ₐ[Qp] LL) = finrank Qp K) (a : ℤ)
    (h : DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) (a + 1) ≠ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) :
    ∃ τ : K →ₐ[Qp] LL, IsJumpV PD ρ τ a := by
  classical
  by_contra hn
  push Not at hn
  apply h
  refine le_antisymm (inf_le_inf_left _ (FilV_anti' PD a)) fun x hx => ?_
  let pb := Field.powerBasisOfFiniteOfSeparable Qp K
  letI : Fintype (K →ₐ[Qp] LL) := Fintype.ofFinite _
  let v : (K →ₐ[Qp] LL) → LL := fun τ => τ pb.gen
  have hv : Function.Injective v := fun τ τ' e => pb.algHom_ext e
  have hcard : (Finset.univ : Finset (K →ₐ[Qp] LL)).card = pb.dim := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hs, pb.finrank]
  have hne : (Finset.univ : Finset (K →ₐ[Qp] LL)).Nonempty := by
    rw [← Finset.card_pos, hcard]; exact pb.dim_pos
  have hnod : (minpoly Qp pb.gen).map (algebraMap Qp LL) = Lagrange.nodal Finset.univ v := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic
      ((minpoly.monic pb.isIntegral_gen).map _) ?_ ?_
    · rw [Lagrange.nodal_eq]
      refine Finset.prod_dvd_of_coprime ((Polynomial.pairwise_coprime_X_sub_C hv).set_pairwise _) fun τ _ => ?_
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
      show aeval (τ pb.gen) _ = 0
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    · rw [Polynomial.natDegree_map, pb.natDegree_minpoly, Lagrange.natDegree_nodal, hcard]
  have hz : ∀ y, aeval (μ pb.gen) (Lagrange.nodal Finset.univ v) y = 0 := by
    intro y
    rw [← hnod, mu_aeval, minpoly.aeval]
    have := mu_alg (K := K) (LL := LL) (0 : Qp) y
    simpa using this
  have hsum : x = ∑ τ, aeval (μ pb.gen) (Lagrange.basis Finset.univ v τ) x := by
    rw [← LinearMap.sum_apply, ← map_sum, Lagrange.sum_basis hv.injOn hne, map_one, Module.End.one_apply]
  rw [hsum]
  refine Submodule.sum_mem _ fun τ _ => ?_
  set y := aeval (μ pb.gen) (Lagrange.basis Finset.univ v τ) x with hy
  have hy1 : y ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a := aeval_mem _ _ (mu_mem PD ρ pb.gen a) _ x hx
  have hy2 : μ pb.gen y = τ pb.gen • y := by
    have e1 : (X - C (v τ)) * Lagrange.basis Finset.univ v τ =
        C (Lagrange.nodalWeight Finset.univ v τ) * Lagrange.nodal Finset.univ v := by
      rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ τ),
        ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ τ), Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ τ)]
      ring
    have e2 : aeval (μ pb.gen) ((X - C (v τ)) * Lagrange.basis Finset.univ v τ) x = 0 := by
      rw [e1, map_mul, Module.End.mul_apply, hz, map_zero]
    rw [map_mul, Module.End.mul_apply, ← hy, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
      Module.algebraMap_end_apply, sub_eq_zero] at e2
    exact e2
  have hy3 : ∀ c : K, μ c y = τ c • y := by
    intro c
    have hc : c ∈ Algebra.adjoin Qp {pb.gen} := by rw [pb.adjoin_gen_eq_top]; trivial
    induction hc using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff.1 hz]; exact hy2
    | algebraMap q => rw [mu_alg, AlgHom.commutes]
    | add c d _ _ hc hd => rw [mu_add, hc, hd, map_add, add_smul]
    | mul c d _ _ hc hd => rw [mu_mul, hd, map_smul, hc, map_mul, smul_smul, mul_comm]
  have hy4 : y ∈ FildR PD ρ τ a := by
    refine ⟨⟨hy1.1, ?_⟩, hy1.2⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    exact hy3
  have hj : FildR PD ρ τ (a + 1) = FildR PD ρ τ a := not_not.1 (hn τ)
  rw [← hj] at hy4
  exact ⟨hy1.1, hy4.2⟩
end C

section D
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module NumberField IsDedekindDomain Formalism.MainNotions
section Loc
variable {l : ℕ} [Fact l.Prime]

theorem Ks_mono (K : FinExt l) {s s' : ℕ} (h : s ≤ s') : Ks K s ≤ Ks K s' := by
  unfold Ks
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
  intro x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hx' : x ^ (l ^ s) = 1 := hx
  show x ^ (l ^ (s + k)) = 1
  rw [pow_add, pow_mul, hx', one_pow]

theorem good_one {K LL : FinExt l} {s : ℕ} (h : Good K s LL) (h2 : l ≠ 2) (hK : K.1 ≤ Ks K 1) :
    Good K 1 LL := by
  refine ⟨le_rfl, fun e => absurd e h2, hK, fun τ x => ?_⟩
  have e := h.2.2.2 ((τ.liftNormal (Om l)).comp (Ks K s).val) ⟨x.1, Ks_mono K h.1 x.2⟩
  have e2 : τ.liftNormal (Om l) (algebraMap ↥(Ks K 1) (Om l) x) = algebraMap (Om l) (Om l) (τ x) :=
    AlgHom.liftNormal_commutes τ (Om l) x
  have e3 : ((τ.liftNormal (Om l)).comp (Ks K s).val) ⟨x.1, Ks_mono K h.1 x.2⟩ = τ x := e2
  rwa [e3] at e

theorem card_emb (K LL : FinExt l) (h : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1) :
    Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
  classical
  have := K.2
  have e : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≃ (↥K.1 →ₐ[ℚ_[l]] Om l) :=
    { toFun := fun τ => LL.1.val.comp τ
      invFun := fun τ => τ.codRestrict LL.1.toSubalgebra (h τ)
      left_inv := fun τ => by ext x; rfl
      right_inv := fun τ => by ext x; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, AlgHom.card]

theorem finrank_sup_adjoin (F : IntermediateField ℚ_[l] (Om l)) (y : Om l) :
    finrank ℚ_[l] ↥(F ⊔ IntermediateField.adjoin ℚ_[l] {y}) = finrank ℚ_[l] ↥F * (minpoly F y).natDegree := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup, ← IntermediateField.adjoin.finrank hint]
  exact (Module.finrank_mul_finrank ℚ_[l] ↥F ↥(IntermediateField.adjoin F {y})).symm

theorem Ks_eq (K : FinExt l) (s : ℕ) {z : Om l} (hz : IsPrimitiveRoot z (l ^ s)) :
    Ks K s = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {z} := by
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  unfold Ks
  congr 1
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one (show x ^ (l ^ s) = 1 from hx)
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  · exact IntermediateField.adjoin.mono _ _ _ (by rintro x rfl; exact hz.pow_eq_one)

theorem finrank_maxUnramifiedSubfield_padicFinExt_pos (K : FinExt l) : 0 < finrank ℚ_[l] ↥(K0 K) := by
  have := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).injective
  exact finrank_pos

theorem le_Ks_one_of_Kur (K : FinExt l) (h : K.1 ≤ MaximalUnramifiedExtension l) : K.1 ≤ Ks K 1 :=
  (le_inf le_rfl h : K.1 ≤ K0 K).trans le_sup_left

end Loc

def cBnum (l h t N : ℕ) : ℕ :=
  (3 + Nat.log l (2 * h)) + t * (3 + N * (4 + 2 * Nat.log l (2 * h))) + 4 * t + 3

theorem cTB_le (l h t N e : ℕ) (hl : l.Prime) (U : Finset ℤ) (U' : Set ℤ) (hU : U' ⊆ U) (hN : U.card ≤ N)
    (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h) (he : e < t) (hth : t ≤ h) :
    LocalSituation.cTB l 1 e 0 (LocalSituation.cLL l (LocalSituation.mN l 1 (h + h)) (LocalSituation.mN l 1 (h + h) - 1) U' 0 ((e : ℤ) + 1)) ≤ cBnum l h t N := by
  classical
  have : Fact l.Prime := ⟨hl⟩
  set lam := Nat.log l (2 * h) with hlam
  have hn0 : LocalSituation.n0 l (h + h) ≤ lam + 1 := by
    refine Nat.sInf_le ?_
    have h1 := Nat.lt_pow_succ_log_self hl.one_lt (2 * h)
    have h2 : 1 ≤ l - 1 := by have := hl.two_le; omega
    show h + h ≤ l ^ (lam + 1) * (l - 1)
    calc h + h = 2 * h := by ring
      _ ≤ l ^ (lam + 1) := h1.le
      _ ≤ _ := Nat.le_mul_of_pos_right _ h2
  have hm : LocalSituation.mN l 1 (h + h) ≤ 4 + lam := by unfold LocalSituation.mN; omega
  set m := LocalSituation.mN l 1 (h + h)
  have hr : ∀ i ∈ Finset.Ico (0 : ℤ) ((e : ℤ) + 1), LocalSituation.rI l m U' i ≤ N * (4 + 2 * lam) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hfin : ({u | u ∈ U' ∧ u ≠ i} : Set ℤ).Finite := U.finite_toSet.subset fun u hu => hU hu.1
    have e1 : LocalSituation.rI l m U' i = ∑ u ∈ hfin.toFinset, (m + LocalSituation.vZ l (u - i)) := by
      rw [← finsum_mem_eq_finite_toFinset_sum _ hfin]
      unfold LocalSituation.rI
      refine finsum_congr fun u => ?_
      by_cases h1 : u ∈ U' <;> by_cases h2 : u = i <;> simp [h1, h2]
    rw [e1]
    have hc : hfin.toFinset.card ≤ N :=
      (Finset.card_le_card fun u hu => hU (hfin.mem_toFinset.1 hu).1).trans hN
    refine (Finset.sum_le_card_nsmul _ _ (4 + 2 * lam) fun u hu => ?_).trans (Nat.mul_le_mul_right _ hc)
    have hu' := hfin.mem_toFinset.1 hu
    have h1 := hb u (hU hu'.1)
    have h2 : LocalSituation.vZ l (u - i) ≤ lam := by
      unfold LocalSituation.vZ padicValInt
      refine (padicValNat_le_nat_log _).trans (Nat.log_mono_right ?_)
      omega
    omega
  have hs : ∑ i ∈ Finset.Ico (0 : ℤ) ((e : ℤ) + 1), (2 + max 1 (LocalSituation.rI l m U' i)) ≤ t * (3 + N * (4 + 2 * lam)) := by
    refine (Finset.sum_le_card_nsmul _ _ (3 + N * (4 + 2 * lam)) fun i hi => ?_).trans ?_
    · have := hr i hi
      omega
    · rw [Int.card_Ico, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (by omega)
  have v1 : padicValNat l e ≤ e := (padicValNat_le_nat_log _).trans (Nat.log_le_self _ _)
  have v2 : padicValNat l (e + 1) ≤ e + 1 := (padicValNat_le_nat_log _).trans (Nat.log_le_self _ _)
  have v3 : e / (l - 1) ≤ e := Nat.div_le_self _ _
  unfold LocalSituation.cTB LocalSituation.cLL cBnum
  rw [← hlam]
  omega

theorem vZ_le_log (l : ℕ) [Fact l.Prime] (h : ℕ) (u : ℤ) (hu : -(h : ℤ) ≤ u ∧ u ≤ h) : LocalSituation.vZ l u ≤ Nat.log l h := by
  unfold LocalSituation.vZ padicValInt
  refine (padicValNat_le_nat_log _).trans (Nat.log_mono_right ?_)
  omega

end D

end GlobalTheory.HubLoc

end
