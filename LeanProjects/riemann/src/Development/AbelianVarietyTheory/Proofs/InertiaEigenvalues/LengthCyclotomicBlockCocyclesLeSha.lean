import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActDEqOfEqOne

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut
open Formalism.GaloisCohomology Pointwise

namespace GlobalTheory.Cut.ShaBound

section Alg

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem algebraMap_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  by_contra h
  have hk : RingHom.ker (algebraMap ℤ_[l] O) ≠ ⊥ := fun h0 => h ((RingHom.injective_iff_ker_eq_bot _).2 h0)
  have hp : (RingHom.ker (algebraMap ℤ_[l] O)).IsPrime := RingHom.ker_isPrime _
  have hm : ((⊥ : Ideal O).comap (algebraMap ℤ_[l] O)).IsMaximal := hp.isMaximal hk
  have : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hm
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal this).symm

instance faithful : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap_inj O)

theorem length_quot : Module.length ℤ_[l] (O ⧸ Ideal.span {(l : O)}) = finrank ℤ_[l] O := by
  let b := Module.finBasis ℤ_[l] O
  let R := IsLocalRing.ResidueField ℤ_[l]
  let φ : O →ₗ[ℤ_[l]] (Fin (finrank ℤ_[l] O) → R) :=
    ((Algebra.linearMap ℤ_[l] R).compLeft _).comp b.equivFun.toLinearMap
  have hs : Function.Surjective φ := by
    intro y
    choose x hx using fun j => IsLocalRing.residue_surjective (R := ℤ_[l]) (y j)
    refine ⟨b.equivFun.symm x, ?_⟩
    funext j
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact hx j
  have hk : LinearMap.ker φ = (Ideal.span {(l : O)}).restrictScalars ℤ_[l] := by
    ext x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    have key : ∀ z : ℤ_[l], algebraMap ℤ_[l] R z = 0 ↔ ∃ y, y * (l : ℤ_[l]) = z := fun z => by
      rw [← Ideal.mem_span_singleton', ← PadicInt.maximalIdeal_eq_span_p]
      exact IsLocalRing.residue_eq_zero_iff z
    constructor
    · intro h
      choose y hy using fun j => (key _).1 (congrFun h j)
      refine ⟨b.equivFun.symm y, b.equivFun.injective ?_⟩
      have : b.equivFun.symm y * (l : O) = (l : ℤ_[l]) • b.equivFun.symm y := by
        rw [Algebra.smul_def, map_natCast, mul_comm]
      rw [this, map_smul, LinearEquiv.apply_symm_apply]
      funext j
      rw [Pi.smul_apply, smul_eq_mul, mul_comm]
      exact hy j
    · rintro ⟨y, rfl⟩
      have : y * (l : O) = (l : ℤ_[l]) • y := by
        rw [Algebra.smul_def, map_natCast, mul_comm]
      rw [this, map_smul]
      funext j
      rw [Pi.smul_apply, Algebra.smul_def, (key _).2 ⟨1, one_mul _⟩, zero_mul]
      rfl
  have e1 := φ.quotKerEquivOfSurjective hs
  rw [hk] at e1
  have e2 := Submodule.Quotient.restrictScalarsEquiv ℤ_[l] (Ideal.span {(l : O)})
  have h1 : Module.length ℤ_[l] R = 1 := by
    rw [Module.length_eq_one_iff]
    exact isSimpleModule_iff_quot_maximal.2 ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩
  rw [← e2.length_eq, e1.length_eq, Module.length_pi_of_fintype]
  simp [h1]

theorem length_le {C S : Type} [AddCommGroup C] [Module O C] [Module ℤ_[l] C] [IsScalarTower ℤ_[l] O C]
    [AddCommGroup S] [Module ℤ_[l] S] (B : Submodule O C) (Ψ : C →ₗ[ℤ_[l]] (Fin (finrank ℤ_[l] O) → S))
    (h : ∀ x, Ψ x = 0 → x ∈ B) :
    Module.length O C ≤ Module.length O B +
      Module.length O (O ⧸ Ideal.span {(l : O)}) * Module.length ℤ_[l] S := by
  haveI : IsLocalHom (algebraMap ℤ_[l] O) := inferInstance
  rw [Module.length_eq_add_of_exact B.subtype B.mkQ B.subtype_injective B.mkQ_surjective
    (LinearMap.exact_subtype_mkQ B)]
  refine add_le_add le_rfl ?_
  have h1 : Module.length ℤ_[l] (C ⧸ B) ≤ Module.length ℤ_[l] (C ⧸ LinearMap.ker Ψ) := by
    refine Module.length_le_of_surjective
      ((LinearMap.ker Ψ).liftQ (B.mkQ.restrictScalars ℤ_[l]) fun x hx => ?_) fun y => ?_
    · exact (Submodule.Quotient.mk_eq_zero _).2 (h x hx)
    · obtain ⟨x, rfl⟩ := B.mkQ_surjective y
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  have h2 : Module.length ℤ_[l] (C ⧸ LinearMap.ker Ψ) ≤ (finrank ℤ_[l] O : ℕ∞) * Module.length ℤ_[l] S := by
    refine (Module.length_le_of_injective ((LinearMap.ker Ψ).liftQ Ψ le_rfl) ?_).trans (le_of_eq ?_)
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
    · rw [Module.length_pi_of_fintype]
      simp
  have h3 := h1.trans h2
  rw [← length_quot O, IsLocalRing.length_restrictScalars ℤ_[l] O (C ⧸ B),
    IsLocalRing.length_restrictScalars ℤ_[l] O (O ⧸ Ideal.span {(l : O)}), mul_right_comm] at h3
  haveI : Module.Finite (IsLocalRing.ResidueField ℤ_[l]) (IsLocalRing.ResidueField O) := inferInstance
  refine (ENat.mul_le_mul_right_iff ?_ ?_).1 h3
  · exact Module.length_pos.ne'
  · exact Module.length_ne_top

theorem exists_coord : ∃ p : KOG O 1 →+ (Fin (finrank ℤ_[l] O) → QZ l), Function.Bijective p ∧
    ∀ (z : ℤ_[l]) (x : KOG O 1), p (algebraMap ℤ_[l] O z • x) = z • p x := by
  let K := FractionRing O
  have hi : Function.Injective (algebraMap ℤ_[l] K) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O K]
    exact (IsFractionRing.injective O K).comp (algebraMap_inj O)
  letI : Algebra ℚ_[l] K := (IsFractionRing.lift (K := ℚ_[l]) hi).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] K := IsScalarTower.of_algebraMap_eq fun z =>
    (IsFractionRing.lift_algebraMap hi z).symm
  let b := Module.finBasis ℤ_[l] O
  let B := b.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) K
  let φ : (Fin 1 → K) →+ (Fin (finrank ℤ_[l] O) → QZ l) :=
    { toFun := fun v j => QZ.mk l (B.repr (v 0) j)
      map_zero' := by funext j; simp [QZ.mk]; rfl
      map_add' := fun u v => by funext j; simp [QZ.mk]; rfl }
  have hφ : ∀ v, φ v = 0 ↔ v ∈ stdG O K 1 := by
    intro v
    have h1 : φ v = 0 ↔ ∀ j, B.repr (v 0) j ∈ Set.range (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [funext_iff]
      exact forall_congr' fun j => Submodule.Quotient.mk_eq_zero _
    rw [h1, ← B.mem_span_iff_repr_mem ℤ_[l], Basis.localizationLocalization_span]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨fun _ => u, ?_⟩
      funext j
      rw [Subsingleton.elim j 0]
      exact hu
    · rintro ⟨u, rfl⟩
      exact ⟨u 0, rfl⟩
  let p : KOG O 1 →+ (Fin (finrank ℤ_[l] O) → QZ l) :=
    QuotientAddGroup.lift (stdG O K 1).toAddSubgroup φ fun v hv => (hφ v).2 hv
  refine ⟨p, ⟨?_, ?_⟩, ?_⟩
  · refine (injective_iff_map_eq_zero p).2 ?_
    intro x hx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 ((hφ v).1 hx)
  · intro y
    choose x hx using fun j => Submodule.Quotient.mk_surjective (ZlSub l) (y j)
    refine ⟨Submodule.Quotient.mk fun _ => B.equivFun.symm x, ?_⟩
    funext j
    show QZ.mk l (B.equivFun (B.equivFun.symm x) j) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hx j
  · intro z x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    funext j
    show QZ.mk l (B.repr (algebraMap ℤ_[l] O z • v 0) j) = QZ.mk l (z • B.repr (v 0) j)
    rw [algebraMap_smul, ← algebraMap_smul ℚ_[l] z, map_smul, Finsupp.smul_apply, algebraMap_smul]

end Alg

section Galois

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem mem_smul_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem valuation_smul_lt_one_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', mem_smul_iff, mem_smul_iff, map_inv₀,
    map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]

theorem conj_mem_Dec {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Dec (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Dec (F := F) A := by
  have h : σ • g • A = g • A := hσ
  show (g⁻¹ * σ * g) • A = A
  rw [mul_smul, mul_smul, h, inv_smul_smul]

theorem conj_mem_Ine' {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  refine ⟨conj_mem_Dec hσ.1, fun x hx => ?_⟩
  have hx' : (g • A).valuation (g x) ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff, mem_smul_iff]
    have : (g⁻¹ : G F Ω) (g x) = x := by
      show (g⁻¹ * g) x = x
      simp
    rw [this]
    exact (A.valuation_le_one_iff x).1 hx
  have h := (valuation_smul_lt_one_iff A g _).1 (hσ.2 _ hx')
  have e : (g⁻¹ : G F Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
    rw [map_sub]
    congr 1
    show (g⁻¹ * g) x = x
    simp
  rwa [e] at h

theorem coc_conj {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M] (ρ : Representation R Γ M)
    (f : Γ → M) (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (g h : Γ) (m : M) (hm : f h = ρ h m - m) :
    f (g * h * g⁻¹) = ρ (g * h * g⁻¹) (ρ g m - f g) - (ρ g m - f g) := by
  have h1 : f (g * h * g⁻¹ * g) = f (g * h * g⁻¹) + ρ (g * h * g⁻¹) (f g) := hf _ _
  rw [inv_mul_cancel_right, hf g h, hm] at h1
  have h2 : ρ (g * h * g⁻¹) (ρ g m) = ρ g (ρ h m) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply]
  rw [map_sub, h2, ← sub_eq_iff_eq_add.2 h1, map_sub]
  abel

variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (Dd : LData F Ω l) (e : ℤ) (A : Places F Ω)

abbrev twG : Representation ℤ_[l] (G F Ω) (QZ l) := (qzTw Dd e).comp (toGS Ω _)

theorem twG_apply (g : G F Ω) (x : QZ l) : twG Dd e g x = ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • x := by
  rw [← Dd.hchi]
  rfl

def LocTriv (f : G F Ω → QZ l) : Prop :=
  f ∈ Z1 (twG Dd e) ∧ (∀ v, v ∉ Above F l → ∀ g ∈ Ine (F := F) (A.1 v), f g = 0) ∧
    ∀ v ∈ Above F l, ∃ m, ∀ g ∈ Dec (F := F) (A.1 v), f g = twG Dd e g m - m

variable {Dd e A}

theorem LocTriv.vanish {f : G F Ω → QZ l} (hf : LocTriv Dd e A f) (n : G F Ω)
    (hn : n ∈ NS Ω (Dd.S : Set (HeightOneSpectrum (𝓞 F)))) : f n = 0 := by
  have htriv : ∀ n ∈ NS Ω (Dd.S : Set (HeightOneSpectrum (𝓞 F))), ∀ x, twG Dd e n x = x := by
    intro n hn x
    have : toGS Ω (Dd.S : Set (HeightOneSpectrum (𝓞 F))) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    show qzTw Dd e (toGS Ω _ n) x = x
    rw [this, map_one]
    rfl
  have h1 : f 1 = 0 := by
    have := hf.1.2 1 1
    rw [one_mul, map_one] at this
    exact left_eq_add.1 this
  let N : Subgroup (G F Ω) :=
    { carrier := {n | n ∈ NS Ω (Dd.S : Set (HeightOneSpectrum (𝓞 F))) ∧ f n = 0}
      one_mem' := ⟨one_mem _, h1⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hf.1.2, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have := hf.1.2 a⁻¹ a
        rw [inv_mul_cancel, h1, ha.2, map_zero, add_zero] at this
        exact this.symm⟩ }
  haveI hN : N.Normal := ⟨fun a ha g => by
    have hc := (normal_NS (Ω := Ω) (Dd.S : Set (HeightOneSpectrum (𝓞 F)))).conj_mem a ha.1 g
    refine ⟨hc, ?_⟩
    rw [coc_conj _ f hf.1.2 g a 0 (by rw [ha.2, map_zero, sub_zero]), htriv _ hc, sub_self]⟩
  have hcl : IsClosed (N : Set (G F Ω)) :=
    (isClosed_NS Ω _).inter (isClosed_singleton.preimage hf.1.1)
  refine (Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl hn).2
  intro τ hτ
  simp only [Set.mem_iUnion] at hτ
  obtain ⟨v, hv, A', hA', hτ⟩ := hτ
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (A.2 v) hA'
  have h2 := conj_mem_Ine' (F := F) hτ
  have h3 : g⁻¹ * τ * g ∈ N := by
    refine ⟨?_, hf.2.1 v (by rw [← Dd.hS]; exact hv) _ h2⟩
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion]
    exact ⟨v, hv, A.1 v, A.2 v, h2⟩
  have := hN.conj_mem _ h3 g
  simpa [mul_assoc] using this

def infl (Dd : LData F Ω l) (e : ℤ) : ↥(Z1 (qzTw Dd e)) →ₗ[ℤ_[l]] (G F Ω → QZ l) :=
  (Z1 (twG Dd e)).subtype.comp (restrictCocycles1 (qzTw Dd e) (toGS Ω _) (continuous_toGS Ω _))

theorem infl_inj : Function.Injective (infl Dd e) := by
  intro a b h
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact congrFun h g

theorem LocTriv.mem_range {f : G F Ω → QZ l} (hf : LocTriv Dd e A f) : f ∈ LinearMap.range (infl Dd e) := by
  let f' : GS Ω (Dd.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l := Quotient.lift f fun a b hab => by
    have h1 := hf.vanish _ (QuotientGroup.leftRel_apply.1 hab)
    have h2 := hf.1.2 a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h1, map_zero, add_zero] at h2
    exact h2.symm
  refine ⟨⟨f', hf.1.1.quotient_lift _, fun a b => ?_⟩, rfl⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hf.1.2 a b

theorem mk_mem_Sha (z : ↥(Z1 (qzTw Dd e))) (hz : LocTriv Dd e A (infl Dd e z)) :
    Submodule.Quotient.mk z ∈ Sha Dd e := by
  refine (Submodule.mem_iInf _).2 fun v => ?_
  refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ?_)
  obtain ⟨m, hm⟩ := hz.2.2 v.1 (by rw [← Dd.hS]; exact v.2)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) (A.2 v.1) (Dd.hA v)
  refine ⟨twG Dd e g m - infl Dd e z g, fun σ => ?_⟩
  have h1 : (σ : G F Ω) ∈ Dec (F := F) (g • A.1 v.1) := by rw [hg]; exact σ.2
  have h2 := coc_conj _ _ hz.1.2 g _ m (hm _ (conj_mem_Dec h1))
  have h3 : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
  rw [h3] at h2
  exact h2

theorem exists_toSha {C : Type} [AddCommGroup C] [Module ℤ_[l] C] (a : C →ₗ[ℤ_[l]] (G F Ω → QZ l))
    (ha : ∀ x, LocTriv Dd e A (a x)) :
    ∃ Ψ : C →ₗ[ℤ_[l]] ↥(Sha Dd e), ∀ x, Ψ x = 0 → ∃ m, ∀ g, a x g = twG Dd e g m - m := by
  let a' := LinearMap.codRestrictOfInjective a (infl Dd e) infl_inj fun x => (ha x).mem_range
  have h : ∀ x, infl Dd e (a' x) = a x := fun x => LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x
  refine ⟨LinearMap.codRestrict _ ((Submodule.mkQ _).comp a') fun x => mk_mem_Sha (A := A) _ (by rw [h]; exact ha x),
    fun x hx => ?_⟩
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val hx))
  refine ⟨m, fun g => ?_⟩
  rw [← h]
  exact hm _

end Galois

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem toLLK_surj (B : LocBridge l E Ω Gw O) : Function.Surjective (Br.toLLK B) := by
  intro x
  have := B.LL.2
  have : Algebra.IsAlgebraic ℤ_[l] ↥B.LL.1 := IsFractionRing.comap_isAlgebraic_iff.2
    (inferInstance : Algebra.IsAlgebraic ℚ_[l] ↥B.LL.1)
  obtain ⟨d, hd, hx⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ_[l]) x).exists_integral_multiple
  obtain ⟨n, hn⟩ := B.eO.surjective ⟨d • x, hx⟩
  refine ⟨algebraMap O _ n / algebraMap O _ (algebraMap ℤ_[l] O d), ?_⟩
  rw [map_div₀, Br.toLLK_alg, Br.toLLK_alg, hn, B.eO_alg, ← IsScalarTower.algebraMap_apply, div_eq_iff]
  · change d • x = _
    rw [Algebra.smul_def, mul_comm]
  · rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥B.LL.1]
    simpa using hd

theorem vecS_mulVec (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK B.Kw)) (u : Fin k → FractionRing O) :
    Br.vecS B k ((mapM (algebraMap O (FractionRing O)) M (Br.ι B g)).mulVec u) =
      (Br.locM B M g).mulVec (Br.vecS B k u) := by
  have h : ∀ i j, Br.locM B M g i j = Br.toLLK B (algebraMap O (FractionRing O) (M (Br.ι B g) i j)) := by
    intro i j
    rw [Br.toLLK_alg]; rfl
  funext i
  change Br.toLLK B (∑ j, algebraMap O (FractionRing O) (M (Br.ι B g) i j) * u j) =
    ∑ j, Br.locM B M g i j * Br.toLLK B (u j)
  simp only [map_sum, map_mul, h]

set_option synthInstance.maxHeartbeats 400000 in

theorem cob_of_bridge (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (c : ↥Gw → KOG O k) (hc : (fun g => Br.phi B k (c (Br.ι B g))) ∈ BD (Br.lat B M)) :
    ∃ m, ∀ g, c g = WKG M g m - m := by
  obtain ⟨x, hx⟩ := hc
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  choose u hu using fun j => toLLK_surj B (y j)
  have hy : y = Br.vecS B k u := funext fun j => (hu j).symm
  refine ⟨Submodule.Quotient.mk u, fun g => ?_⟩
  obtain ⟨g, rfl⟩ := (Br.ι_bijective B).2 g
  rw [← sub_eq_zero]
  apply GlobalTheory.CutTrivIne.eq_zero_of_phi B
  have h1 : Br.phi B k (c (Br.ι B g)) = Submodule.Quotient.mk ((Br.locM B M g).mulVec y - y) :=
    (congrFun hx g).symm
  rw [map_sub, h1, sub_eq_zero, hy, ← vecS_mulVec, ← map_sub]
  rfl

theorem WKG_scalar {Γ : Type} [Group Γ] (M : Γ →* Matrix (Fin 1) (Fin 1) O) (g : Γ) (x : KOG O 1) :
    WKG M g x = M g 0 0 • x := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk (((M g).map (algebraMap O (FractionRing O))).mulVec v) = Submodule.Quotient.mk (M g 0 0 • v)
  congr 1
  funext j
  rw [Subsingleton.elim j 0]
  simp [Matrix.mulVec, dotProduct, Algebra.smul_def]

end Bridge

theorem chiRatO_apply (D : D7) (i : D.nd.Loc) (c : ℕ) (h1 : 1 ≤ c) (h2 : c ≤ D.R.t) (g : GE D.nd) :
    chiRatO D.nd i c g 0 0 = algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      ((cycZ D.host.E D.nd.Om (D.nd.l i) g ^ (-((c - 1 : ℕ) : ℤ)) : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) := by
  have h : chiRatO D.nd i c g 0 0 = ((D.nd.chi i c g * (D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
    simp [chiRatO, twistM, chiU]
  rw [h, D.nd.chi_def i c h1 h2, MonoidHom.mul_apply, mul_inv_cancel_comm, MonoidHom.zpow_apply,
    MonoidHom.comp_apply, ← map_zpow, Nat.cast_sub h1, Nat.cast_one]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : D7) (i : D.nd.Loc) (c : ℕ) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)), C ≤ Z1 (WKG (chiRatO D.nd i c)) → 2 ≤ c → c ≤ D.R.t → (∀ f ∈ C, ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), locFun i (chiRatO D.nd i c) w hw f ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) → (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → resIne i C v = ⊥) → Module.length (D.nd.O i) ↥C ≤ lenCob i (chiRatO D.nd i c) (C) + lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) ((c - 1 : ℕ) : ℤ) := by
  intro D i c C hZ h2 ht hloc hine
  obtain ⟨p, hp, hps⟩ := exists_coord (l := D.nd.l i) (D.nd.O i)
  have hact : ∀ g x j, p (WKG (chiRatO D.nd i c) g x) j =
      twG (D.nd.ldat (D.nd.l i)) ((c - 1 : ℕ) : ℤ) g (p x j) := by
    intro g x j
    rw [WKG_scalar, chiRatO_apply D i c (by omega) ht, hps, twG_apply]
    rfl
  let a : Fin (finrank ℤ_[D.nd.l i] (D.nd.O i)) → (↥C →ₗ[ℤ_[D.nd.l i]] (GE D.nd → QZ (D.nd.l i))) := fun j =>
    { toFun := fun f g => p (f.1 g) j
      map_add' := fun f f' => funext fun g => congrFun (p.map_add (f.1 g) (f'.1 g)) j
      map_smul' := fun z f => funext fun g => by
        rw [← algebraMap_smul (D.nd.O i) z f]
        exact congrFun (hps z (f.1 g)) j }
  have ha : ∀ j x, LocTriv (D.nd.ldat (D.nd.l i)) ((c - 1 : ℕ) : ℤ) D.nd.plOm (a j x) := by
    intro j f
    refine ⟨⟨(continuous_of_discreteTopology (f := fun y => p y j)).comp (hZ f.2).1, fun g h => ?_⟩,
      fun v hv g hg => ?_, fun w hw => ?_⟩
    · show p (f.1 (g * h)) j = p (f.1 g) j + twG _ _ g (p (f.1 h) j)
      rw [(hZ f.2).2, map_add, Pi.add_apply, hact]
    · have h0 : LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) 1) Subtype.val f.1 ∈ resIne i C v :=
        ⟨f.1, f.2, rfl⟩
      rw [hine v hv, Submodule.mem_bot] at h0
      have h1 : f.1 g = 0 := congrFun h0 ⟨g, hg⟩
      show p (f.1 g) j = 0
      rw [h1, map_zero]
      rfl
    · obtain ⟨m, hm⟩ := cob_of_bridge (D.nbr i w hw) ((chiRatO D.nd i c).comp (decS D.nd w))
        (fun g => f.1 g.1) (hloc f.1 f.2 w hw)
      refine ⟨p m j, fun g hg => ?_⟩
      have h1 : f.1 g = WKG (chiRatO D.nd i c) g m - m := hm ⟨g, hg⟩
      show p (f.1 g) j = _
      rw [h1, map_sub, Pi.sub_apply, hact]
  choose Ψ hΨ using fun j => exists_toSha (a j) (ha j)
  have key := length_le (l := D.nd.l i) (D.nd.O i)
    ((ReciprocityTheory.Gal.B1 (WKG (chiRatO D.nd i c))).comap C.subtype) (LinearMap.pi Ψ) (fun f hf => by
      choose m hm using fun j => hΨ j f (congrFun hf j)
      obtain ⟨y, rfl⟩ := hp.2 m
      refine (mem_coboundaries1 _ _).2 ⟨y, fun g => hp.1 (funext fun j => ?_)⟩
      rw [map_sub, Pi.sub_apply, hact]
      exact hm j g)
  refine key.trans (add_le_add (le_of_eq ?_) le_rfl)
  have e := Submodule.equivMapOfInjective C.subtype C.subtype_injective
    ((ReciprocityTheory.Gal.B1 (WKG (chiRatO D.nd i c))).comap C.subtype)
  rw [Submodule.map_comap_subtype] at e
  exact e.length_eq

end GlobalTheory.Cut.ShaBound

end
