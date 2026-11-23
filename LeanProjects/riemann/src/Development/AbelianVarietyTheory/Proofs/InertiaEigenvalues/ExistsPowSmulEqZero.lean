import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteResidueField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LocalEulerFormulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticePowSmulNhdsZeroBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicallyCompleteLatticeReductionActionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeTwistExactSequenceCohomologyStatement

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (Z1 H1 H2 B1 d0)

noncomputable section

namespace GlobalTheory.FreeCoh

section Alg

variable {O : Type} [CommRing O] {lam : O}

theorem tmul_one_surj {N : Type} [AddCommGroup N] [Module O N] (y : N ⊗[O] (O ⧸ Ideal.span {lam})) :
    ∃ n : N, n ⊗ₜ[O] (1 : O ⧸ Ideal.span {lam}) = y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, TensorProduct.add_tmul _ _ _⟩
  | tmul n x =>
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨x • n, ?_⟩
    rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
    rfl

theorem tmul_one_eq_zero {N : Type} [AddCommGroup N] [Module O N] (n : N) :
    n ⊗ₜ[O] (1 : O ⧸ Ideal.span {lam}) = 0 ↔ ∃ y, n = lam • y := by
  rw [← (TensorProduct.tensorQuotEquivQuotSMul N (Ideal.span {lam})).map_eq_zero_iff,
    ← map_one (Ideal.Quotient.mk (Ideal.span {lam})),
    TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp [eq_comm]

theorem card_tensor [Nontrivial O] (N X : Type) [AddCommGroup N] [Module O N] [Module.Free O N] [Module.Finite O N]
    [AddCommGroup X] [Module O X] : Nat.card (N ⊗[O] X) = Nat.card X ^ Module.finrank O N := by
  let e : N ⊗[O] X ≃ₗ[O] (Fin (Module.finrank O N) → X) :=
    (TensorProduct.congr (Module.finBasis O N).equivFun (LinearEquiv.refl O X)).trans
      ((TensorProduct.comm O _ _).trans (TensorProduct.piScalarRight O O X _))
  rw [Nat.card_congr e.toEquiv, Nat.card_fun]
  simp

theorem exists_pow_smul_eq_zero [IsLocalRing O] (hl : ¬ IsUnit lam) {X : Type} [AddCommGroup X] [Module O X]
    [Finite X] (x : X) : ∃ a : ℕ, lam ^ a • x = 0 := by
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun a : ℕ => lam ^ a • x)
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm h.symm (by omega)
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  have hu : IsUnit (1 - lam ^ (c + 1)) := by
    refine IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ?_
    rw [pow_succ]
    exact fun h => hl (isUnit_of_mul_isUnit_right h)
  refine ⟨a, hu.smul_eq_zero.mp ?_⟩
  rw [sub_smul, one_smul, smul_smul, ← pow_add, h, sub_eq_zero]
  congr 2; ring

theorem exists_inj_res [IsDomain O] [IsDiscreteValuationRing O] (hl : Irreducible lam) (X : Type) [AddCommGroup X]
    [Module O X] [Finite X] [Nontrivial X] : ∃ i : (O ⧸ Ideal.span {lam}) →ₗ[O] X, Function.Injective i := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have h := exists_pow_smul_eq_zero hl.not_isUnit x
  have h0 : Nat.find h ≠ 0 := fun h0 => hx (by simpa [h0] using Nat.find_spec h)
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have h1 : lam ^ a • x ≠ 0 := Nat.find_min h (by omega)
  have h2 : lam • lam ^ a • x = 0 := by
    have := Nat.find_spec h
    rwa [ha, pow_succ', mul_smul] at this
  refine ⟨Submodule.liftQ (Ideal.span {lam}) (LinearMap.toSpanSingleton O X (lam ^ a • x)) (by
    rw [Ideal.span, Submodule.span_le]
    rintro _ rfl
    exact h2), ?_⟩
  rw [← LinearMap.ker_eq_bot]
  refine Submodule.ker_liftQ_eq_bot _ _ _ fun y hy => ?_
  by_contra hn
  have hu : IsUnit y := by
    rw [← hl.maximalIdeal_eq] at hn
    simpa using hn
  exact h1 (hu.smul_eq_zero.mp hy)

theorem finite_induction [IsDomain O] [IsDiscreteValuationRing O] (hl : Irreducible lam)
    (P : ∀ (X : Type) [AddCommGroup X] [Module O X], Prop)
    (h0 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Subsingleton X], P X)
    (h1 : ∀ (X Y : Type) [AddCommGroup X] [Module O X] [Finite X] [AddCommGroup Y] [Module O Y]
      (i : (O ⧸ Ideal.span {lam}) →ₗ[O] X) (p : X →ₗ[O] Y), Function.Injective i → Function.Exact i p →
      Function.Surjective p → P Y → P X)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] : P X := by
  induction hn : Nat.card X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    rcases subsingleton_or_nontrivial X with h | h
    · exact h0 X
    obtain ⟨i, hi⟩ := exists_inj_res hl X
    have : Finite (X ⧸ LinearMap.range i) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
    refine h1 X (X ⧸ LinearMap.range i) i (Submodule.mkQ _) hi (LinearMap.exact_map_mkQ_range i)
      (Submodule.mkQ_surjective _) (ih _ ?_ _ rfl)
    have hc := Submodule.card_eq_card_quotient_mul_card (LinearMap.range i)
    have : Nontrivial (O ⧸ Ideal.span {lam}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by rw [Ne, Ideal.span_singleton_eq_top]; exact hl.not_isUnit)
    have : Nontrivial (LinearMap.range i) := (LinearEquiv.ofInjective i hi).symm.toEquiv.nontrivial
    have h2 : 1 < Nat.card (LinearMap.range i) := Finite.one_lt_card
    have h3 : 0 < Nat.card (X ⧸ LinearMap.range i) := Nat.card_pos
    rw [← hn, hc]
    nlinarith

theorem inv_ext {G T S X Y : Type} [Group G] [AddCommGroup T] [Module O T] [Module.Flat O T]
    [AddCommGroup S] [Module O S] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y]
    (π : Representation O G T) (i : S →ₗ[O] X) (p : X →ₗ[O] Y) (hi : Function.Injective i)
    (he : Function.Exact i p) (hp : Function.Surjective p) (hS : (coefRep π S).invariants = ⊥)
    (hY : (coefRep π Y).invariants = ⊥) : (coefRep π X).invariants = ⊥ := by
  have nat : ∀ {A B : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B] (f : A →ₗ[O] B) g m,
      f.lTensor T (coefRep π A g m) = coefRep π B g (f.lTensor T m) := by
    intro A B _ _ _ _ f g m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [coefRep_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [Submodule.eq_bot_iff] at hS hY ⊢
  intro m hm
  have h1 : p.lTensor T m = 0 := hY _ fun g => by rw [← nat, hm g]
  obtain ⟨m₀, rfl⟩ := (lTensor_exact T he hp m).mp h1
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := T) i hi
  rw [hS m₀ fun g => hinj (by rw [nat, hm g]), map_zero]

end Alg

section Lat

variable {G LL O V : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousConstSMul LL V] {ρ : Representation LL G V}
  (L : Lattice (O := O) ρ) (χ : G →* Oˣ) (lam : O)

def AdicBasis : Prop :=
  (∀ a : ℕ, {v : V | ∃ t ∈ L.T, v = lam ^ a • t} ∈ 𝓝 (0 : V)) ∧ ∀ U ∈ 𝓝 (0 : V), ∃ a : ℕ, ∀ t ∈ L.T, lam ^ a • t ∈ U

abbrev act : Representation O G ↥L.T := twistRep (latRep L) χ⁻¹

omit [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V] in

theorem act_coe (g : G) (t : ↥L.T) : (act L χ g t : V) = twistRep ρ (chiLL LL χ⁻¹) g t :=
  (algebraMap_smul LL (χ⁻¹ g : O) (ρ g t)).symm

variable {L lam}

theorem continuous_iff_adic (hB : AdicBasis L lam) (f : G → ↥L.T) :
    Continuous (fun g => (f g : V)) ↔ ∀ (a : ℕ) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, f g - f g₀ = lam ^ a • y := by
  constructor
  · intro hf a g₀
    have h : Tendsto (fun g => (f g : V) - f g₀) (𝓝 g₀) (𝓝 0) := by
      simpa using (hf.tendsto g₀).sub_const (f g₀ : V)
    filter_upwards [h (hB.1 a)] with g hg
    obtain ⟨t, ht, h⟩ := hg
    exact ⟨⟨t, ht⟩, Subtype.ext h⟩
  · intro hf
    refine continuous_iff_continuousAt.mpr fun g₀ => ?_
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
    intro U hU
    obtain ⟨a, ha⟩ := hB.2 U hU
    rw [mem_map]
    filter_upwards [hf a g₀] with g hg
    obtain ⟨y, hy⟩ := hg
    have h : (f g : V) - f g₀ = lam ^ a • (y : V) := congrArg Subtype.val hy
    change (f g : V) - f g₀ ∈ U
    exact h ▸ ha y y.2

theorem lc_tmul (hB : AdicBasis L lam) {X : Type} [AddCommGroup X] [Module O X] (x : X) (a : ℕ)
    (ha : lam ^ a • x = 0) (f : G → ↥L.T) (hf : Continuous fun g => (f g : V)) :
    IsLocallyConstant fun g => f g ⊗ₜ[O] x := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  filter_upwards [(continuous_iff_adic hB f).mp hf a g₀] with g hg
  obtain ⟨y, hy⟩ := hg
  rw [← sub_eq_zero, ← TensorProduct.sub_tmul, hy, TensorProduct.smul_tmul, ha, TensorProduct.tmul_zero]

theorem lc_act (hB : AdicBasis L lam) (hc : ∀ v, Continuous fun g => twistRep ρ (chiLL LL χ⁻¹) g v)
    {X : Type} [AddCommGroup X] [Module O X] (hX : ∀ x : X, ∃ a : ℕ, lam ^ a • x = 0) (m : ↥L.T ⊗[O] X) :
    IsLocallyConstant fun g => twCoef (latRep L) χ X g m := by
  induction m using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact IsLocallyConstant.const _
  | add a b ha hb => simp only [map_add]; exact ha.add hb
  | tmul t x =>
    obtain ⟨a, ha⟩ := hX x
    exact lc_tmul hB x a ha (fun g => act L χ g t) (by simpa only [act_coe] using hc t)

theorem ev_mul (c : ↥(latticeCocycles (twLattice L χ⁻¹))) (g h : G) :
    (evT (twLattice L χ⁻¹) (g * h) c : ↥L.T) =
      evT (twLattice L χ⁻¹) g c + act L χ g (evT (twLattice L χ⁻¹) h c) := by
  refine Subtype.ext ?_
  rw [Submodule.coe_add, act_coe]
  exact c.2.1.2 g h

theorem tensCoc_mem (hB : AdicBasis L lam) {X : Type} [AddCommGroup X] [Module O X]
    (hX : ∀ x : X, ∃ a : ℕ, lam ^ a • x = 0) (c : ↥(latticeCocycles (twLattice L χ⁻¹))) (x : X) :
    tensCoc L χ X c x ∈ Z1 (twCoef (latRep L) χ X) ⊤ := by
  obtain ⟨a, ha⟩ := hX x
  refine ⟨⟨lc_tmul hB x a ha (fun g => evT (twLattice L χ⁻¹) g c) c.2.1.1, fun _ => Submodule.mem_top⟩, ?_⟩
  funext p
  change act L χ p.1 (evT (twLattice L χ⁻¹) p.2 c) ⊗ₜ[O] x - (evT (twLattice L χ⁻¹) (p.1 * p.2) c : ↥L.T) ⊗ₜ[O] x
    + (evT (twLattice L χ⁻¹) p.1 c : ↥L.T) ⊗ₜ[O] x = 0
  rw [ev_mul, TensorProduct.add_tmul]
  abel

theorem exists_div (hl : algebraMap O LL lam ≠ 0) (c : ↥(latticeCocycles (twLattice L χ⁻¹)))
    (h : ∀ g, ∃ y : ↥L.T, (evT (twLattice L χ⁻¹) g c : ↥L.T) = lam • y) : ∃ c', c = lam • c' := by
  refine ⟨⟨(algebraMap O LL lam)⁻¹ • c.1, (continuousCocycles _).smul_mem _ c.2.1, fun g _ => ?_⟩, Subtype.ext ?_⟩
  · obtain ⟨y, hy⟩ := h g
    have h1 : c.1 g = lam • (y : V) := congrArg Subtype.val hy
    rw [Pi.smul_apply, h1, ← algebraMap_smul LL lam, inv_smul_smul₀ hl]
    exact y.2
  · funext g
    change c.1 g = lam • (algebraMap O LL lam)⁻¹ • c.1 g
    rw [← algebraMap_smul LL lam, smul_inv_smul₀ hl]

def cobZ (hc : ∀ v, Continuous fun g => twistRep ρ (chiLL LL χ⁻¹) g v) (t : ↥L.T) : ↥(latticeCocycles (twLattice L χ⁻¹)) :=
  ⟨cob (twistRep ρ (chiLL LL χ⁻¹)) t, ⟨(hc t).sub continuous_const, fun g h => by
      simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_mul, Module.End.mul_apply,
        map_sub]
      abel⟩,
    fun g _ => L.T.sub_mem ((twLattice L χ⁻¹).stable g t t.2) t.2⟩

theorem ev_cobZ (hc : ∀ v, Continuous fun g => twistRep ρ (chiLL LL χ⁻¹) g v) (t : ↥L.T) (g : G) :
    (evT (twLattice L χ⁻¹) g (cobZ χ hc t) : ↥L.T) = act L χ g t - t := by
  refine Subtype.ext ?_
  rw [Submodule.coe_sub, act_coe]
  rfl

theorem mk_cobZ (hc : ∀ v, Continuous fun g => twistRep ρ (chiLL LL χ⁻¹) g v) (t : ↥L.T) :
    (Submodule.Quotient.mk (cobZ χ hc t) : H1tw L χ) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ⟨t, t.2, rfl⟩

omit [IsTopologicalAddGroup V] [ContinuousConstSMul LL V] [TopologicalSpace V] [TopologicalSpace G] in

theorem eq_zero_of_smul (hl : algebraMap O LL lam ≠ 0) (t : ↥L.T) (h : lam • t = 0) : t = 0 := by
  have h1 : lam • (t : V) = 0 := congrArg Subtype.val h
  rw [← algebraMap_smul LL lam] at h1
  exact Subtype.ext ((smul_eq_zero.mp h1).resolve_left hl)

theorem tensIso_res [ContinuousMul G] [IsAdicComplete (Ideal.span {lam}) ↥L.T] (hB : AdicBasis L lam)
    (hc : ∀ v, Continuous fun g => twistRep ρ (chiLL LL χ⁻¹) g v) (hl : algebraMap O LL lam ≠ 0)
    (h2 : Subsingleton (H2 (twCoef (latRep L) χ (O ⧸ Ideal.span {lam})) ⊤)) :
    TensIso L χ (O ⧸ Ideal.span {lam}) := by
  have hX : ∀ x : O ⧸ Ideal.span {lam}, ∃ a : ℕ, lam ^ a • x = 0 := fun x => ⟨1, by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [pow_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))⟩
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨h, rfl⟩ := tmul_one_surj y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [tensAmb_tmul] at hy
    obtain ⟨m, -, hm⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
    obtain ⟨t, rfl⟩ := tmul_one_surj m
    obtain ⟨c', hc'⟩ := exists_div χ hl (c - cobZ χ hc t) fun g => by
      rw [map_sub, ← tmul_one_eq_zero, ev_cobZ, TensorProduct.sub_tmul, TensorProduct.sub_tmul, sub_eq_zero]
      exact (congrFun hm g).symm
    refine (tmul_one_eq_zero _).mpr ⟨Submodule.Quotient.mk c', ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← hc', Submodule.Quotient.mk_sub, mk_cobZ, sub_zero]
  · rintro _ ⟨y, rfl⟩
    obtain ⟨h, rfl⟩ := tmul_one_surj y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    exact ⟨Submodule.Quotient.mk ⟨_, tensCoc_mem χ hB hX c 1⟩, rfl⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨c, hc1, hc2, hc3⟩ := GlobalTheory.T.exists_continuous_cocycle_lift_of_subsingleton_H2 O G ↥L.T _ lam (act L χ) _
      ((TensorProduct.mk O ↥L.T (O ⧸ Ideal.span {lam})).flip 1) inferInstance (eq_zero_of_smul hl)
      tmul_one_surj tmul_one_eq_zero (fun _ _ => rfl)
      (fun a t => (continuous_iff_adic hB fun g => act L χ g t).mp (by simpa only [act_coe] using hc t) a)
      h2 z.1 z.2
    refine ⟨Submodule.Quotient.mk ⟨fun g => (c g : V), ⟨(continuous_iff_adic hB c).mpr hc3, fun g h => ?_⟩,
      fun g _ => (c g).2⟩ ⊗ₜ 1, ?_⟩
    · beta_reduce
      rw [hc1, Submodule.coe_add, act_coe]
    · rw [tensAmb_tmul]
      exact congrArg Submodule.Quotient.mk (funext hc2)

theorem H_eq_zero_of_smul (hc : ∀ v, Continuous fun g => twistRep ρ (chiLL LL χ⁻¹) g v)
    (hl : algebraMap O LL lam ≠ 0) (h0 : (twCoef (latRep L) χ (O ⧸ Ideal.span {lam})).invariants = ⊥)
    (h : H1tw L χ) (hh : lam • h = 0) : h = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  rw [← Submodule.Quotient.mk_smul] at hh
  obtain ⟨t, ht, e⟩ := (Submodule.Quotient.mk_eq_zero _).mp hh
  have e' : cobZ χ hc ⟨t, ht⟩ = lam • c := Subtype.ext e
  have h1 : (⟨t, ht⟩ : ↥L.T) ⊗ₜ[O] (1 : O ⧸ Ideal.span {lam}) = 0 := by
    refine (Submodule.eq_bot_iff _).mp h0 _ fun g => ?_
    rw [coefRep_tmul, ← sub_eq_zero, ← TensorProduct.sub_tmul, tmul_one_eq_zero, ← ev_cobZ χ hc, e', map_smul]
    exact ⟨_, rfl⟩
  obtain ⟨y, hy⟩ := (tmul_one_eq_zero _).mp h1
  have e2 : c = cobZ χ hc y := by
    refine Subtype.ext (funext fun g => ?_)
    have h3 : lam • ((evT (twLattice L χ⁻¹) g c : ↥L.T) - evT (twLattice L χ⁻¹) g (cobZ χ hc y)) = 0 := by
      rw [smul_sub, ← map_smul, ← e', ev_cobZ, ev_cobZ, hy, map_smul, smul_sub, sub_self]
    exact congrArg Subtype.val (sub_eq_zero.mp (eq_zero_of_smul hl _ h3))
  rw [e2, mk_cobZ]

theorem H_finite [IsAdicComplete (Ideal.span {lam}) O] [IsHausdorff (Ideal.span {lam}) ↥L.T]
    (hB : AdicBasis L lam) (hl : algebraMap O LL lam ≠ 0) [Finite (↥L.T ⊗[O] (O ⧸ Ideal.span {lam}))]
    [Finite (H1 (twCoef (latRep L) χ (O ⧸ Ideal.span {lam})) ⊤)] : Module.Finite O (H1tw L χ) := by
  have hX : ∀ x : O ⧸ Ideal.span {lam}, ∃ a : ℕ, lam ^ a • x = 0 := fun x => ⟨1, by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [pow_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))⟩
  set π := twCoef (latRep L) χ (O ⧸ Ideal.span {lam})
  have hBf : Finite (B1 π ⊤) := (Set.toFinite _).image (d0 π) |>.to_subtype
  have hB' : Finite ((B1 π ⊤).submoduleOf (Z1 π ⊤)) :=
    Finite.of_injective (fun x : (B1 π ⊤).submoduleOf (Z1 π ⊤) => (⟨x.1.1, x.2⟩ : B1 π ⊤))
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun x : B1 π ⊤ => x.1) hab)))
  have hZ : Finite (Z1 π ⊤) :=
    @Finite.of_addSubgroup_quotient _ _ ((B1 π ⊤).submoduleOf (Z1 π ⊤)).toAddSubgroup hB' ‹_›
  have : IsHausdorff (Ideal.span {lam}) ↥(latticeCocycles (twLattice L χ⁻¹)) := ⟨fun c hc => by
    refine Subtype.ext (funext fun g => ?_)
    have h : (evT (twLattice L χ⁻¹) g c : ↥L.T) = 0 := IsHausdorff.haus (I := Ideal.span {lam}) inferInstance _
      fun n => by
        have h1 := hc n
        rw [SModEq.zero] at h1 ⊢
        have h2 := Submodule.mem_map_of_mem (f := evT (twLattice L χ⁻¹) g) h1
        rw [Submodule.map_smul''] at h2
        exact Submodule.smul_mono le_rfl le_top h2
    exact congrArg Subtype.val h⟩
  let f : ↥(latticeCocycles (twLattice L χ⁻¹)) →ₗ[O] Z1 π ⊤ :=
    ((tensCoc L χ _).flip 1).codRestrict _ fun c => tensCoc_mem χ hB hX c 1
  have hk : LinearMap.ker f ≤ (Ideal.span {lam} • ⊤ : Submodule O ↥(latticeCocycles (twLattice L χ⁻¹))) := by
    intro c hc
    obtain ⟨c', rfl⟩ := exists_div χ hl c fun g =>
      (tmul_one_eq_zero _).mp (congrFun (congrArg Subtype.val hc) g)
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have : Finite (↥(latticeCocycles (twLattice L χ⁻¹)) ⧸ LinearMap.ker f) :=
    Finite.of_equiv _ (LinearMap.quotKerEquivRange f).symm.toEquiv
  have : Finite (↥(latticeCocycles (twLattice L χ⁻¹)) ⧸ (Ideal.span {lam} • ⊤ : Submodule O ↥(latticeCocycles (twLattice L χ⁻¹)))) :=
    Finite.of_surjective _ (Submodule.factor_surjective hk)
  have := GlobalTheory.finite_of_isHausdorff_of_finite_quotient (Ideal.span {lam}) ↥(latticeCocycles (twLattice L χ⁻¹))
  exact Module.Finite.quotient _ _

theorem free_and_tensIso [ContinuousMul G] [IsDomain O] [IsDiscreteValuationRing O] (hi : Irreducible lam)
    [IsAdicComplete (Ideal.span {lam}) O] [Finite (O ⧸ Ideal.span {lam})] (hB : AdicBasis L lam)
    (hc : ∀ v, Continuous fun g => twistRep ρ (chiLL LL χ⁻¹) g v) (hl : algebraMap O LL lam ≠ 0)
    (h0 : (twCoef (latRep L) χ (O ⧸ Ideal.span {lam})).invariants = ⊥)
    (h2 : Subsingleton (H2 (twCoef (latRep L) χ (O ⧸ Ideal.span {lam})) ⊤)) {n : ℕ}
    (h1 : Finite (↥L.T ⊗[O] (O ⧸ Ideal.span {lam})) →
      (∀ m, IsLocallyConstant fun g => twCoef (latRep L) χ (O ⧸ Ideal.span {lam}) g m) →
      Nat.card (H1 (twCoef (latRep L) χ (O ⧸ Ideal.span {lam})) ⊤) =
        Nat.card (↥L.T ⊗[O] (O ⧸ Ideal.span {lam})) ^ n) :
    (Module.Free O (H1tw L χ) ∧ Module.Finite O (H1tw L χ) ∧
      Module.finrank O (H1tw L χ) = Module.finrank O ↥L.T * n) ∧
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], TensIso L χ X := by
  have := L.free
  have : Module.Finite O ↥L.T := Module.Finite.iff_fg.mpr L.fg
  have := isAdicComplete_of_finite (Ideal.span {lam}) ↥L.T
  have hk := tensIso_res χ hB hc hl h2
  have : Nontrivial (O ⧸ Ideal.span {lam}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [Ne, Ideal.span_singleton_eq_top]; exact hi.not_isUnit)
  have hq : 1 < Nat.card (O ⧸ Ideal.span {lam}) := Finite.one_lt_card
  have hM := card_tensor (O := O) ↥L.T (O ⧸ Ideal.span {lam})
  have hMf : Finite (↥L.T ⊗[O] (O ⧸ Ideal.span {lam})) := Nat.finite_of_card_ne_zero (by rw [hM]; positivity)
  have h1' := h1 hMf (lc_act χ hB hc (exists_pow_smul_eq_zero hi.not_isUnit))
  rw [hM, ← pow_mul] at h1'
  have : Finite (H1 (twCoef (latRep L) χ (O ⧸ Ideal.span {lam})) ⊤) :=
    Nat.finite_of_card_ne_zero (by rw [h1']; positivity)
  have hfin := H_finite χ hB hl
  have : Module.IsTorsionFree O (H1tw L χ) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a h hh => ?_
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hi
    rw [mul_smul, u.isUnit.smul_eq_zero] at hh
    clear ha
    induction k generalizing h with
    | zero => simpa using hh
    | succ k ih =>
      rw [pow_succ, mul_smul] at hh
      exact H_eq_zero_of_smul χ hc hl h0 h (ih _ hh)
  have hfree : Module.Free O (H1tw L χ) := inferInstance
  refine ⟨⟨hfree, hfin, ?_⟩, fun X _ _ _ => ?_⟩
  · refine Nat.pow_right_injective hq ?_
    beta_reduce
    rw [← h1', ← card_tensor, Nat.card_congr (LinearEquiv.ofInjective _ hk.1).toEquiv, hk.2,
      Nat.card_congr (LinearEquiv.ofInjective _ (toAmb_injective _)).toEquiv]
  · refine (finite_induction hi (fun X _ _ => (twCoef (latRep L) χ X).invariants = ⊥ ∧ TensIso L χ X)
      (fun X _ _ _ => ⟨Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _, ?_⟩)
      (fun X Y _ _ _ _ _ i p hi' he hp hY => ⟨inv_ext _ i p hi' he hp h0 hY.1,
        GlobalTheory.T.lattice_twist_exact_sequence_cohomology G LL O V ρ L χ _ X Y i p hi' he hp
          (tensCoc_mem χ hB (exists_pow_smul_eq_zero hi.not_isUnit))
          (lc_act χ hB hc (exists_pow_smul_eq_zero hi.not_isUnit)) hY.1 hk hY.2⟩) X).2
    have : Subsingleton (Amb (twCoef (latRep L) χ X)) := (Submodule.mkQ_surjective _).subsingleton
    exact Subsingleton.elim _ _

end Lat

theorem pow_mul_mem_nhds {l : ℕ} [Fact l.Prime] (LL : FinExt l) (lam : ↥(OL LL)) (hi : Irreducible lam)
    (U : Set ↥LL.1) (hU : U ∈ 𝓝 (0 : ↥LL.1)) : ∃ a : ℕ, ∀ x : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 (lam ^ a * x) ∈ U := by
  obtain ⟨_, -, hA, -⟩ := GlobalTheory.CoefInt.integers_laws l LL
  have hc : Continuous (algebraMap ↥(OL LL) ↥LL.1) := continuous_subtype_val
  obtain ⟨a, ha⟩ := (isAdic_iff.mp hA).2 _ (hc.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU))
  refine ⟨a, fun x => ha (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ a))⟩
  exact hi.not_isUnit

theorem free_and_tensIso_gal {G Qp LL O : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (Γ : GalData G Qp LL O)
    (hi : Irreducible Γ.lam) (hA : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
    (hF : Finite (IsLocalRing.ResidueField O)) (hO : IsOpen (Set.range (algebraMap O LL)))
    (hU : ∀ U ∈ 𝓝 (0 : LL), ∃ a : ℕ, ∀ x : O, algebraMap O LL (Γ.lam ^ a * x) ∈ U)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁ g)) {l : ℕ} (hl : ¬ IsUnit (l : O))
    (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥) (h2 : Subsingleton (H2 (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ) ⊤)) {r n d : ℕ}
    (hr' : Module.finrank LL Γ.T₀.V = r) (hn : n = d)
    (hE : ∀ (M : Type) [AddCommGroup M] [Module O M] [Finite M] (π : Representation O G M), (∀ m : M, l • m = 0) →
      (∀ m, IsLocallyConstant fun g => π g m) → π.invariants = ⊥ → Subsingleton (H2 π ⊤) →
      Nat.card (H1 π ⊤) = Nat.card M ^ d) :
    (Module.Free O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ) ∧ Module.Finite O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ) ∧
      Module.finrank O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ) = r * n) ∧
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], TensIso Γ.T₀.L Γ.χ₁ X := by
  subst hr' hn
  have : IsTopologicalAddGroup Γ.T₀.V := IsModuleTopology.topologicalAddGroup LL Γ.T₀.V
  have : ContinuousSMul LL Γ.T₀.V := IsModuleTopology.toContinuousSMul LL Γ.T₀.V
  have hl0 : algebraMap O LL Γ.lam ≠ 0 := fun h =>
    hi.ne_zero (IsFractionRing.injective O LL (h.trans (map_zero _).symm))
  have hr : Module.finrank O ↥Γ.T₀.L.T = Module.finrank LL Γ.T₀.V := by
    have : Submodule.IsLattice LL Γ.T₀.L.T := ⟨Γ.T₀.L.fg, Γ.T₀.L.span⟩
    rw [Module.finrank, Module.finrank, Submodule.IsLattice.rank' LL]
  have hm := hi.maximalIdeal_eq
  have hF' : Finite (O ⧸ IsLocalRing.maximalIdeal O) := hF
  have hd : Γ.lam ∣ (l : O) := by
    rw [← Ideal.mem_span_singleton, ← hm]; exact hl
  rw [hm] at hA hF'
  rw [← hr]
  refine free_and_tensIso Γ.χ₁ hi
    (GlobalTheory.T.lattice_pow_smul_nhds_zero_basis LL O Γ.T₀.V Γ.T₀.L.T Γ.lam Γ.T₀.L.fg Γ.T₀.L.span hO hl0 hU) (fun v => ?_) hl0 h0 h2
    fun _ hlc => hE _ _ (fun m => ?_) hlc h0 h2
  · have h := (hχ.comp continuous_inv).smul (Γ.T₀.cont v)
    refine h.congr fun g => ?_
    change algebraMap O LL (Γ.χ₁ g⁻¹) • Γ.T₀.ρ g v = _
    rw [map_inv]
    rfl
  · rw [← Nat.cast_smul_eq_nsmul O]
    refine smul_tensor_eq_zero (fun x => ?_) m
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr hd))

open GlobalTheory.TopSteps in

theorem freeH_of_vanish : Formalism.GaloisCohomology.LocalFinitenessK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Vanish → S.FreeH := by
  intro _ hE l _ P S hV
  obtain ⟨hS, hT, -⟩ := S.hyp
  obtain ⟨_, -, -, hA, hF, hfr⟩ := GlobalTheory.CoefInt.integers_laws l S.LL
  obtain ⟨-, -, -, hR, hO⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete S.LL
  exact free_and_tensIso_gal S.Γ hS.2.2.2.2.2 hA hF hO (pow_mul_mem_nhds S.LL _ hS.2.2.2.2.2) hT.2.2.1.1 hl
    hV.1 hV.2 hT.1 hS.2.2.1 (fun M _ _ _ π => GlobalTheory.T.card_H1_local_euler_formula hE l S.K _ M π)

end GlobalTheory.FreeCoh
