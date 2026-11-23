import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobeniusSemisimplification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNilpotentZpowSubOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanMkQOneTmul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst

section Letter

variable {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* End LL D)
  (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)

def letterKer : Submodule F (F ⊗[LL] D) :=
  ⨆ c : U, LinearMap.range ((m c).baseChange F - τ c • LinearMap.id)

def Letter : Type := (F ⊗[LL] D) ⧸ letterKer m F τ

instance : AddCommGroup (Letter m F τ) := inferInstanceAs (AddCommGroup (_ ⧸ letterKer m F τ))

instance : Module F (Letter m F τ) := inferInstanceAs (Module F (_ ⧸ letterKer m F τ))

def letterQ : F ⊗[LL] D →ₗ[F] Letter m F τ := (letterKer m F τ).mkQ

theorem letterQ_surjective : Function.Surjective (letterQ m F τ) := Submodule.mkQ_surjective _

theorem ker_letterQ : LinearMap.ker (letterQ m F τ) = letterKer m F τ := Submodule.ker_mkQ _

def letterMk (x : D) : Letter m F τ := letterQ m F τ (1 ⊗ₜ x)

@[simp] theorem letterMk_zero : letterMk m F τ 0 = 0 := by simp [letterMk]

theorem letterMk_add (x y : D) : letterMk m F τ (x + y) = letterMk m F τ x + letterMk m F τ y := by
  simp [letterMk, tmul_add]

theorem letterMk_smul (a : LL) (x : D) :
    letterMk m F τ (a • x) = algebraMap LL F a • letterMk m F τ x := by
  rw [letterMk, letterMk, ← map_smul, tmul_smul, algebraMap_smul]

theorem letterMk_mul (c : U) (x : D) : letterMk m F τ (m c x) = τ c • letterMk m F τ x := by
  rw [letterMk, letterMk, ← map_smul, ← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ker_letterQ]
  exact Submodule.mem_iSup_of_mem c ⟨1 ⊗ₜ x, rfl⟩

theorem span_letterMk : Submodule.span F (Set.range (letterMk m F τ)) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SpanQuotientTensor.main
  | exact _root_.GlobalTheory.SpanQuotientTensor.main
  | (apply _root_.GlobalTheory.SpanQuotientTensor.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanQuotientTensor.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanQuotientTensor.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanQuotientTensor.main ..)

theorem letter_hom_ext {M : Type*} [AddCommGroup M] [Module F M] {f g : Letter m F τ →ₗ[F] M}
    (h : ∀ x, f (letterMk m F τ x) = g (letterMk m F τ x)) : f = g :=
  LinearMap.ext_on_range (span_letterMk m F τ) h

def letterMap (T : End LL D) (hT : ∀ c, T * m c = m c * T) : End F (Letter m F τ) :=
  Submodule.mapQ _ _ (T.baseChange F) (iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    refine Submodule.mem_iSup_of_mem c ⟨T.baseChange F y, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hT c)) y
    rw [LinearMap.baseChange_mul, LinearMap.baseChange_mul, End.mul_apply, End.mul_apply] at this
    simp [this])

@[simp] theorem letterMap_mk (T : End LL D) (hT : ∀ c, T * m c = m c * T) (x : D) :
    letterMap m F τ T hT (letterMk m F τ x) = letterMk m F τ (T x) := rfl

theorem finiteDimensional_letter {ι : Type} [Fintype ι] (b : ι → D)
    (hb : ∀ x, ∃ c : ι → U, x = ∑ i, m (c i) (b i)) : FiniteDimensional F (Letter m F τ) := by
  refine ⟨⟨(Set.finite_range fun i => letterMk m F τ (b i)).toFinset, eq_top_iff.mpr ?_⟩⟩
  rw [← span_letterMk, Submodule.span_le, Set.Finite.coe_toFinset]
  rintro _ ⟨x, rfl⟩
  obtain ⟨c, rfl⟩ := hb x
  rw [letterMk, tmul_sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := letterMk_mul m F τ (c i) (b i)
  rw [letterMk] at this
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Letter

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

def resDeg (l : ℕ) (w : HeightOneSpectrum (𝓞 E)) : ℕ := Nat.log l (normV w)

theorem normV_eq_pow (hw : w ∈ placesOver E l) : normV w = l ^ resDeg l w := by
  have : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  let := Ideal.Quotient.field w.asIdeal
  let := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  have : CharP (𝓞 E ⧸ w.asIdeal) l := (CharP.charP_iff_prime_eq_zero Fact.out).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hw)
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ w.asIdeal) l
  rw [resDeg, normV, Nat.card_eq_fintype_card, hn, Nat.log_pow (Fact.out : l.Prime).one_lt]

variable (Bw : LocBridge l E Ω (Dec (F := E) A) O)

def Induces : Prop := ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1

variable {Bw}

omit [NumberField E] in

theorem Induces.valuation_lt_one_iff (hj : Induces Bw) (x : Ω) : A.valuation x < 1 ↔ ‖Bw.j x‖ < 1 := by
  rw [valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖Bw.j x‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)
    simp only [hx, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem Induces.mem_placesOver (hj : Induces Bw) (h : IsPlaceOver A w) : w ∈ placesOver E l := by
  refine (h (l : 𝓞 E)).mp ?_
  rw [hj.valuation_lt_one_iff]
  simp only [map_natCast]
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff]

variable (Bw) (h : IsPlaceOver A w)

def weilToGK : ↥(Weil h) →* ↥(GK Bw.Kw) :=
  Bw.e.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))

theorem weilToGK_j (σ : ↥(Weil h)) (x : Ω) :
    (weilToGK Bw h σ : GQ l) (Bw.j x) = Bw.j ((σ : G E Ω) x) := Bw.e_comm _ x

variable {Bw h} [IsAlgClosure E Ω]

variable (l) in

def alpha (σ : ↥(Weil h)) : ℤ := resDeg l w * deg σ

theorem frobUr_pow_root (n : ℕ) (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ) (h0 : 0 < m) (hm : ¬ l ∣ m) (hc : c ^ m = 1) :
    (frobUr l ^ n) c = c ^ l ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, AlgHom.mul_apply, frobUr_root c m h0 hm hc, map_pow, ih, ← pow_mul, pow_succ]

theorem weilToGK_frobUr (hj : Induces Bw) (σ : ↥(Weil h)) {a b : ℕ}
    (hσ : ActsAs A (normV w) (σ : G E Ω) a b) (c : ↥(MaximalUnramifiedExtension l)) :
    (weilToGK Bw h σ : GQ l) (((frobUr l ^ (resDeg l w * b)) c : ↥(MaximalUnramifiedExtension l)) : Om l) =
      (((frobUr l ^ (resDeg l w * a)) c : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have : ((weilToGK Bw h σ : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp
      ((MaximalUnramifiedExtension l).val.comp (frobUr l ^ (resDeg l w * b))) =
      (MaximalUnramifiedExtension l).val.comp (frobUr l ^ (resDeg l w * a)) := by
    refine kur_algHom_ext fun c m h0 hm hc => ?_
    have hc' : (c : Om l) ^ m = 1 := congrArg Subtype.val hc
    have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    have : NeZero m := ⟨h0.ne'⟩
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
    obtain ⟨i, -, hi⟩ := (hz.map_of_injective Bw.j.injective).eq_pow_of_pow_eq_one hc'
    rw [← map_pow] at hi
    have hx : A.valuation (z ^ i) ≤ 1 := by
      rw [A.valuation_le_one_iff, hj, hi]; exact (norm_eq_one_of_pow_eq_one h0 hc').le
    have h1 := hσ.2 _ hx
    rw [hj.valuation_lt_one_iff, map_sub, map_pow Bw.j, map_pow Bw.j (z ^ i), ← weilToGK_j Bw h, hi,
      normV_eq_pow (hj.mem_placesOver h), ← pow_mul, ← pow_mul] at h1
    simp only [AlgHom.comp_apply, frobUr_pow_root _ c m h0 hm hc, map_pow]
    refine eq_of_pow_eq_one_of_norm_sub_lt hm ?_ ?_ h1
    · rw [← pow_mul, mul_comm, pow_mul, ← map_pow, IntermediateField.val_mk, hc', map_one, one_pow]
    · rw [← pow_mul, mul_comm, pow_mul, IntermediateField.val_mk, hc', one_pow]
  exact AlgHom.congr_fun this c

variable (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

section Unit

variable {K : FinExt l} (ρ : Representation LL ↥(GK K) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

def phiU : (End LL ↥(Dpst P ρ))ˣ := ((End.isUnit_iff _).mpr (phiD_bijective (P := P) (ρ := ρ))).unit

@[simp] theorem coe_phiU : (phiU P ρ : End LL ↥(Dpst P ρ)) = phiD P ρ := rfl

theorem commute_actD_phiU (g : ↥(GK K)) (n : ℤ) :
    Commute (actD P ρ g) ((phiU P ρ ^ n : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) :=
  Commute.units_zpow_right (u := phiU P ρ) (phiD_actD P ρ g).symm n

omit [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] in

theorem phiD_pow_mulD (n : ℕ) (c : ↥(MaximalUnramifiedExtension l)) :
    phiD P ρ ^ n * mulD P ρ c = mulD P ρ ((frobUr l ^ n) c) * phiD P ρ ^ n := by
  induction n generalizing c with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, phiD_mulD, ← mul_assoc, ih, mul_assoc, pow_succ, AlgHom.mul_apply]

theorem monD_phiU_zpow (n : ℤ) :
    monD P ρ * ((phiU P ρ ^ n : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) =
      (l : LL) ^ n • (((phiU P ρ ^ n : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) * monD P ρ) := by
  have : CharZero LL := charZero_of_injective_algebraMap (algebraMap ℚ_[l] LL).injective
  have hl : (l : LL) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have h1 : monD P ρ * ((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) =
      (l : LL)⁻¹ • (((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) * monD P ρ) := by
    rw [eq_inv_smul_iff₀ hl, Units.eq_inv_mul_iff_mul_eq, mul_smul_comm, ← mul_assoc, ← smul_mul_assoc,
      coe_phiU, ← monD_phiD, ← coe_phiU, Units.mul_inv_cancel_right]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, coe_phiU, monD_phiD,
      mul_smul_comm, smul_smul, zpow_add_one₀ hl, mul_assoc]
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, h1,
      mul_smul_comm, smul_smul, zpow_sub_one₀ hl, mul_assoc]

end Unit

variable (Bw h) (ρ : Representation LL ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

def weilD : Representation LL ↥(Weil h) ↥(Dpst P ρ) where
  toFun σ := actD P ρ (weilToGK Bw h σ) *
    ((phiU P ρ ^ (-alpha l σ) : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ))
  map_one' := by simp [alpha]
  map_mul' σ τ := by
    rw [map_mul, map_mul, alpha, deg_mul, mul_add, neg_add, zpow_add, Units.val_mul,
      (commute_actD_phiU P ρ _ _).mul_mul_mul_comm]
    rfl

theorem weilD_apply (σ : ↥(Weil h)) : weilD Bw h P ρ σ = actD P ρ (weilToGK Bw h σ) *
    ((phiU P ρ ^ (-alpha l σ) : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) := rfl

theorem weilD_ineIncl (σ : ↥(Ine (F := E) A)) :
    weilD Bw h P ρ (ineIncl h σ) = actD P ρ (weilToGK Bw h (ineIncl h σ)) := by
  simp [weilD_apply, alpha]

theorem weilD_monD (hj : Induces Bw) (σ : ↥(Weil h)) : weilD Bw h P ρ σ * monD P ρ =
    ((normV w : ℕ) : LL) ^ deg σ • (monD P ρ * weilD Bw h P ρ σ) := by
  have : CharZero LL := charZero_of_injective_algebraMap (algebraMap ℚ_[l] LL).injective
  have hl : (l : LL) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  rw [weilD_apply, ← mul_assoc, monD_actD, mul_assoc, mul_assoc, monD_phiU_zpow, mul_smul_comm, smul_smul,
    normV_eq_pow (hj.mem_placesOver h), Nat.cast_pow, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hl, alpha,
    add_neg_cancel, zpow_zero, one_smul]

theorem weilD_mulD (hj : Induces Bw) (σ : ↥(Weil h)) (c : ↥(MaximalUnramifiedExtension l)) :
    weilD Bw h P ρ σ * mulD P ρ c = mulD P ρ c * weilD Bw h P ρ σ := by
  obtain ⟨a, b, hσ⟩ := σ.2
  have e : -alpha l σ = ((resDeg l w * b : ℕ) : ℤ) + -((resDeg l w * a : ℕ) : ℤ) := by
    rw [alpha, deg_eq hσ]; push_cast; ring
  obtain ⟨c, rfl⟩ := (Algebra.IsAlgebraic.algHom_bijective (frobUr l ^ (resDeg l w * a))).2 c
  have h1 : (((phiU P ρ ^ (resDeg l w * a))⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) *
      mulD P ρ ((frobUr l ^ (resDeg l w * a)) c) =
      mulD P ρ c * ((phiU P ρ ^ (resDeg l w * a))⁻¹ : (End LL ↥(Dpst P ρ))ˣ) := by
    rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, Units.val_pow_eq_pow_val,
      coe_phiU, phiD_pow_mulD]
  rw [weilD_apply, e, zpow_add, zpow_neg, zpow_natCast, zpow_natCast, Units.val_mul, mul_assoc, mul_assoc, h1,
    Units.val_pow_eq_pow_val, coe_phiU, ← mul_assoc (phiD P ρ ^ _), phiD_pow_mulD, ← mul_assoc, ← mul_assoc,
    actD_mulD P ρ _ _ _ (weilToGK_frobUr hj σ hσ c)]
  simp only [mul_assoc]

theorem isSmooth_weilD (hj : Induces Bw) : IsSmooth (weilD Bw h P ρ) := by
  obtain ⟨K', hK'⟩ := exists_actD_eq_one (P := P) (ρ := ρ)
  have := K'.2
  have hc : Continuous fun σ : ↥(Ine (F := E) A) => (weilToGK Bw h (ineIncl h σ) : GQ l) :=
    continuous_subtype_val.comp (Bw.e_cont.comp (continuous_subtype_val.subtype_mk _))
  refine .of_open ((IntermediateField.fixingSubgroup_isOpen K'.1).preimage hc) (by simp) fun σ hσ => ?_
  rw [weilD_ineIncl]
  refine hK' _ hσ fun c => ?_
  rw [← weilD_ineIncl]
  exact weilD_mulD Bw h P ρ hj _ c

end Bridge

end GlobalTheory.Pst
