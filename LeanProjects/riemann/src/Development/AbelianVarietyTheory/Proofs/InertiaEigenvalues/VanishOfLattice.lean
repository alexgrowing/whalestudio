import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HomToCharacterLineEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N (twistRep coefRep GoodO)

namespace GlobalTheory.TopVanish

theorem subsingleton_H2 {N : ℕ} {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (Φ : G' ≃* G) (h1 : Continuous Φ) (h2 : Continuous Φ.symm) {O M : Type} [CommRing O] [AddCommGroup M]
    [Module O M] [Module (ZMod N) M] [TopologicalSpace M] [DiscreteTopology M] (π : Representation O G' M)
    (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M) (hrho : ∀ g m, rho g m = π (Φ.symm g) m)
    (hb : Function.Injective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _)))
    (hφ : ∀ φ : M →+ ZMod N, (∀ g m, φ (π g m) = (χ (Φ g) : ZMod N) * φ m) → φ = 0) :
    Subsingleton (ReciprocityTheory.Def.H2 π ⊤) := by
  have h0 : ∀ φ : ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G)), φ = 0 := fun φ => by
    have h := hφ (show M →ₗ[ZMod N] ZMod N from φ.1).toAddMonoidHom fun g m => by
      have h3 := congrArg (fun f : ReciprocityTheory.Gal.TDual (ZMod N) M => f (π g m)) (φ.2 (Φ g))
      change (χ (Φ g) : ZMod N) * φ.1 (rho (Φ g)⁻¹ (π g m)) = φ.1 (π g m) at h3
      rw [hrho, map_inv, Φ.symm_apply_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] at h3
      exact h3.symm
    exact Subtype.ext (ReciprocityTheory.Gal.TDual.ext fun m => DFunLike.congr_fun h m)
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hz' : (fun p : G × G => z (Φ.symm p.1, Φ.symm p.2)) ∈ ReciprocityTheory.Gal.Z2 (rho.comp (MonoidHom.id G)) := by
    refine ⟨hz.1.1.continuous.comp (h2.prodMap h2), fun g h k => ?_⟩
    have h3 := congrFun hz.2 (Φ.symm g, Φ.symm h, Φ.symm k)
    change rho g _ - _ + _ - _ = 0
    beta_reduce
    rw [hrho, map_mul, map_mul]
    exact h3
  have h4 : (Submodule.Quotient.mk ⟨_, hz'⟩ : ReciprocityTheory.Gal.H2 (rho.comp (MonoidHom.id G))) = 0 := by
    apply hb
    ext φ
    rw [h0 φ, map_zero, map_zero]
  obtain ⟨b, hb1, hb2⟩ := (Submodule.Quotient.mk_eq_zero _).1 h4
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨fun g => b (Φ g),
    ⟨(IsLocallyConstant.iff_continuous _).2 (Continuous.comp hb1 h1), fun _ => trivial⟩, funext fun p => ?_⟩
  have h5 := congrFun hb2 (Φ p.1, Φ p.2)
  change rho (Φ p.1) (b (Φ p.2)) - b (Φ p.1 * Φ p.2) + b (Φ p.1) = z (Φ.symm (Φ p.1), Φ.symm (Φ p.2)) at h5
  rw [hrho, ← map_mul, Φ.symm_apply_apply, Φ.symm_apply_apply] at h5
  exact h5

theorem addHom_eq_zero {k G V A : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup A]
    (ρ : Representation k G V) (c : G → ℕ)
    (h : ∀ p : V →ₗ[k] k, (∀ g x, p (ρ g x) = (c g : k) * p x) → p = 0)
    (φ : V →+ A) (hφ : ∀ g x, φ (ρ g x) = c g • φ x) : φ = 0 := by
  let N : Submodule k V :=
    { carrier := {x | ∀ a : k, φ (a • x) = 0}
      zero_mem' := fun a => by simp
      add_mem' := fun {x y} hx hy a => by rw [smul_add, map_add, hx, hy, add_zero]
      smul_mem' := fun b x hx a => by rw [smul_smul]; exact hx _ }
  by_contra hne
  have hN : N < ⊤ := lt_top_iff_ne_top.2 fun hN => hne (AddMonoidHom.ext fun x => by
    have hx : x ∈ N := hN ▸ Submodule.mem_top
    simpa using hx 1)
  obtain ⟨p, hp, hNp⟩ := Submodule.exists_le_ker_of_lt_top N hN
  refine hp (h p fun g x => ?_)
  have hx : ρ g x - c g • x ∈ N := fun a => by
    rw [smul_sub, map_sub, ← map_smul, hφ, smul_comm, map_nsmul, sub_self]
  have h1 : p (ρ g x - c g • x) = 0 := hNp hx
  rwa [map_sub, map_nsmul, sub_eq_zero, nsmul_eq_mul] at h1

theorem exists_equiv {O T N : Type} [CommRing O] [AddCommGroup T] [Module O T] [AddCommGroup N] [Module O N]
    {lam : O} (q : T →ₗ[O] N) (hq : Function.Surjective q) (hk : KerIs lam q) :
    ∃ E : (T ⊗[O] (O ⧸ Ideal.span {lam})) ≃ₗ[O] N, (∀ x, E (x ⊗ₜ 1) = q x) ∧
      ∀ y : T ⊗[O] (O ⧸ Ideal.span {lam}), ∃ x, y = x ⊗ₜ 1 := by
  have hc : ∀ m : N, lam • m = 0 := fun m => by
    obtain ⟨x, rfl⟩ := hq m
    rw [← map_smul]
    exact (hk _).2 ⟨x, rfl⟩
  let f : (T ⊗[O] (O ⧸ Ideal.span {lam})) →ₗ[O] N := TensorProduct.lift ((cycMap hc).comp q)
  have hf : ∀ x, f (x ⊗ₜ 1) = q x := fun x => by
    change cycMap hc (q x) (Ideal.Quotient.mk _ 1) = _
    rw [cycMap_mk, one_smul]
  have hs : ∀ y : T ⊗[O] (O ⧸ Ideal.span {lam}), ∃ x, y = x ⊗ₜ 1 := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x a =>
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨a • x, by rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]; rfl⟩
    | add a b ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      exact ⟨x + y, (TensorProduct.add_tmul _ _ _).symm⟩
  refine ⟨LinearEquiv.ofBijective f ⟨?_, fun m => ?_⟩, hf, hs⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨x, rfl⟩ := (hk x).1 ((hf x).symm.trans hy)
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    have : algebraMap O (O ⧸ Ideal.span {lam}) lam = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [this, TensorProduct.tmul_zero]
  · obtain ⟨x, rfl⟩ := hq m
    exact ⟨_, hf x⟩

theorem lc_reduction {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] [TopologicalSpace Qp]
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := Qp) LL O) (T : LocLat G Qp LL O) {lam : O} (hlam : lam ≠ 0) {N : Type} [AddCommGroup N]
    [Module O N] (q : ↥T.L.T →ₗ[O] N) (hk : KerIs lam q) (x : ↥T.L.T) :
    IsLocallyConstant fun g => q (latRep T.L g x) := by
  have hT := GlobalTheory.Cyc.locLat_isOpen hO T
  obtain ⟨⟨_, _, _⟩, -⟩ := hO
  have hl : algebraMap O LL lam ≠ 0 := fun h => hlam (IsFractionRing.injective O LL (by rw [h, map_zero]))
  haveI := IsModuleTopology.topologicalAddGroup LL T.V
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  have hc : Continuous fun g => (algebraMap O LL lam)⁻¹ • (T.ρ g x - T.ρ g₀ x) :=
    ((T.cont x).sub continuous_const).const_smul _
  filter_upwards [(hT.preimage hc).mem_nhds (x := g₀) (by simp)] with g hg
  rw [← sub_eq_zero, ← map_sub]
  refine (hk _).2 ⟨⟨_, hg⟩, Subtype.ext ?_⟩
  change T.ρ g x - T.ρ g₀ x = lam • ((algebraMap O LL lam)⁻¹ • (T.ρ g x - T.ρ g₀ x))
  rw [← algebraMap_smul LL lam, smul_smul, mul_inv_cancel₀ hl, one_smul]

theorem ringHom_eq_val {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (f : ℤ_[l] →+* k) (x : ℤ_[l]) :
    f x = ((PadicInt.toZModPow 1 x).val : k) := by
  have : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h : x - (((PadicInt.toZModPow 1 x).val : ℕ) : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ 1} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 h
  have h1 := congrArg f hw
  rwa [map_sub, map_natCast, map_mul, map_pow, map_natCast, CharP.cast_eq_zero k l, zero_pow one_ne_zero, zero_mul,
    sub_eq_zero] at h1

theorem vanish_of_model (hT : Formalism.GaloisCohomology.LocalTateDualityK) {l : ℕ} [Fact l.Prime] (K : FinExt l) {O M k : Type}
    [CommRing O] [AddCommGroup M] [Module O M] [Field k] [Finite k] [CharP k l]
    (π : Representation O ↥(GK K) M) (hlc : ∀ m, IsLocallyConstant fun g => π g m) (A : Ob k ↥(GK K))
    (E : M ≃+ (Fin A.m → k)) (hE : ∀ g m, E (π g m) = A.ρ g (E m)) (ω : ↥(GK K) →* kˣ)
    (hω : ∀ g, (ω g : k) = ((Formalism.GaloisCohomology.cycK l K.1 1 (K.1.fixingSubgroupEquiv g) : ZMod (l ^ 1)).val : k))
    (h : ∀ e : ℤ, -1 ≤ e → e < 1 → ∀ (A₁ : Ob k ↥(GK K)) (j : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k))
      (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)), IsHom A₁ A j → Function.Injective j →
      IsHom A₁ (chr (ω ^ (-e))) p → p = 0) :
    π.invariants = ⊥ ∧ Subsingleton (ReciprocityTheory.Def.H2 π ⊤) := by
  refine ⟨(Submodule.eq_bot_iff _).2 fun x hx => ?_, ?_⟩
  · by_contra hne
    have hv : E x ≠ 0 := fun h0 => hne (E.map_eq_zero_iff.1 h0)
    have hinv : ∀ g, A.ρ g (E x) = E x := fun g => by rw [← hE, hx g]
    have h1 := h 0 (by norm_num) (by norm_num) (chr 1)
      ((LinearMap.toSpanSingleton k _ (E x)).comp (LinearMap.proj 0)) LinearMap.id
      (fun g y => by simp [chr, hinv])
      (fun y z hyz => funext fun i => by
        rw [Subsingleton.elim i 0]
        exact smul_left_injective k hv hyz)
      (fun g y => by simp [chr])
    exact one_ne_zero (congrFun (DFunLike.congr_fun h1 (fun _ => 1)) 0)
  · obtain ⟨hΦ1, hΦ2⟩ := GlobalTheory.Cyc.TwistLift.continuous_fixingSubgroupEquiv K.1
    let Φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := K.1.fixingSubgroupEquiv
    have _ : Finite M := Finite.of_equiv _ E.symm.toEquiv
    let _ : TopologicalSpace M := ⊥
    have _ : DiscreteTopology M := ⟨rfl⟩
    have _ : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hr : ∀ m : M, l ^ 1 • m = 0 := fun m => by
      rw [pow_one, ← E.map_eq_zero_iff, map_nsmul, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
    obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ 1)) M) := ⟨AddCommGroup.zmodModule hr⟩
    let rho : Representation (ZMod (l ^ 1)) (Formalism.GaloisCohomology.GK l K.1) M :=
      { toFun := fun g => AddMonoidHom.toZModLinearMap _ (π (Φ.symm g)).toAddMonoidHom
        map_one' := LinearMap.ext fun m => by
          change π (Φ.symm 1) m = m
          rw [map_one, map_one, Module.End.one_apply]
        map_mul' := fun g g' => LinearMap.ext fun m => by
          change π (Φ.symm (g * g')) m = π (Φ.symm g) (π (Φ.symm g') m)
          rw [map_mul, map_mul, Module.End.mul_apply] }
    have hrho : ReciprocityTheory.Gal.ContAction rho :=
      continuous_prod_of_discrete_right.2 fun m => (hlc m).continuous.comp hΦ1
    refine subsingleton_H2 Φ hΦ2 hΦ1 π _ rho (fun _ _ => rfl)
      (hT l K.1 K.2 1 M rho one_pos hrho).2.2.2.2.1 fun φ hφ => ?_
    have h1 := addHom_eq_zero A.ρ (fun g => (Formalism.GaloisCohomology.cycK l K.1 1 (Φ g) : ZMod (l ^ 1)).val) (fun p hp => by
      have h2 := h (-1) le_rfl (by norm_num) A LinearMap.id (LinearMap.pi fun _ => p) (fun _ _ => rfl)
        Function.injective_id (fun g y => funext fun i => by
          change p (A.ρ g y) = ((ω ^ (-(-1 : ℤ))) g : k) * p y
          rw [neg_neg, zpow_one, hp, hω]
          rfl)
      exact LinearMap.ext fun y => congrFun (DFunLike.congr_fun h2 y) 0)
      (φ.comp E.symm.toAddMonoidHom) (fun g y => by
        obtain ⟨m, rfl⟩ := E.surjective y
        change φ (E.symm (A.ρ g (E m))) = _ • φ (E.symm (E m))
        rw [← hE, E.symm_apply_apply, E.symm_apply_apply, hφ, nsmul_eq_mul, ZMod.natCast_zmod_val])
    ext m
    simpa using DFunLike.congr_fun h1 (E m)

theorem vanish_of_lattice (hT : Formalism.GaloisCohomology.LocalTateDualityK) {l : ℕ} [Fact l.Prime] (K : FinExt l) {LL O k : Type}
    [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL] [Field k] [Finite k]
    [CharP k l] [Algebra O k] (hO : GoodO (Qp := ℚ_[l]) LL O) (Γ : GalData ↥(GK K) ℚ_[l] LL O) (hlam : Γ.lam ≠ 0)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁ g)) (A : Ob k ↥(GK K))
    (q : ↥Γ.T₀.L.T →ₗ[O] (Fin A.m → k)) (hq : Function.Surjective q) (hk : KerIs Γ.lam q)
    (hqρ : ∀ σ x, q (twistRep Γ.W₀ Γ.χ₁⁻¹ σ x) = A.ρ σ (q x)) (ω : ↥(GK K) →* kˣ)
    (hω : ∀ g, (ω g : k) = ((Formalism.GaloisCohomology.cycK l K.1 1 (K.1.fixingSubgroupEquiv g) : ZMod (l ^ 1)).val : k))
    (h : ∀ e : ℤ, -1 ≤ e → e < 1 → ∀ (A₁ : Ob k ↥(GK K)) (j : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k))
      (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)), IsHom A₁ A j → Function.Injective j →
      IsHom A₁ (chr (ω ^ (-e))) p → p = 0) :
    (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥ ∧ Subsingleton (ReciprocityTheory.Def.H2 (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ) ⊤) := by
  obtain ⟨E, hE, hs⟩ := exists_equiv q hq hk
  have hE' : ∀ g m, E (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ g m) = A.ρ g (E m) := fun g m => by
    obtain ⟨x, rfl⟩ := hs m
    rw [coefRep_tmul, hE, hE, hqρ]
  refine vanish_of_model hT K _ (fun m => ?_) A E.toAddEquiv hE' ω hω h
  obtain ⟨x, rfl⟩ := hs m
  have hχ' : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g) := by
    refine (hχ.comp continuous_inv).congr fun g => ?_
    rw [Function.comp_apply, map_inv, MonoidHom.inv_apply]
  have h1 := lc_reduction hO (twLat Γ.T₀ Γ.χ₁⁻¹ hχ') hlam q hk x
  refine IsLocallyConstant.desc _ E ?_ E.injective
  have h2 : (E ∘ fun g => GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ g (x ⊗ₜ 1)) =
      fun g => q (latRep (twLattice Γ.T₀.L Γ.χ₁⁻¹) g x) := funext fun g => by
    rw [Function.comp_apply, coefRep_tmul, hE, latRep_twLattice]
  exact h2 ▸ h1

theorem exists_residue {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {lam : O}
    (hlam : Irreducible lam) (l : ℕ) [Fact l.Prime] (hl : ¬ IsUnit (l : O))
    (hf : Finite (O ⧸ Ideal.span {(l : O) ^ 1})) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra O k) (_ : CharP k l) (_ : Finite k),
      Function.Surjective (algebraMap O k) ∧ ∀ x, algebraMap O k x = 0 ↔ lam ∣ x := by
  have h0 : algebraMap O (IsLocalRing.ResidueField O) l = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hl
  refine ⟨IsLocalRing.ResidueField O, inferInstance, inferInstance,
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rwa [map_natCast] at h0), ?_,
    IsLocalRing.residue_surjective, fun x => ?_⟩
  · refine Finite.of_surjective (Ideal.Quotient.factor (S := Ideal.span {(l : O) ^ 1})
      (T := IsLocalRing.maximalIdeal O) ?_) (Ideal.Quotient.factor_surjective _)
    rw [pow_one, Ideal.span_singleton_le_iff_mem]
    exact hl
  · rw [← Ideal.mem_span_singleton, ← hlam.maximalIdeal_eq]
    exact IsLocalRing.residue_eq_zero_iff _

theorem vanish_of_real : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Real → S.Vanish := by
  intro hT l _ P S hS
  obtain ⟨hst, ⟨-, -, hχ, hε⟩, h1, h2, h3⟩ := S.hyp
  have hlam : Irreducible S.Γ.lam := hst.2.2.2.2.2
  obtain ⟨hO, hf⟩ := GlobalTheory.LocalIntegers.good_integers l S.LL
  obtain ⟨_, -, -, hl, -⟩ := GlobalTheory.Per.integers_completeDVR l S.LL
  obtain ⟨k, _, _, _, _, hres⟩ := exists_residue hlam l hl (hf 1)
  obtain ⟨R, -, -, F, M, hω, ⟨q, hq, hk, hqρ⟩, -⟩ := hS k hres
  refine vanish_of_lattice hT S.K hO S.Γ hlam.ne_zero hχ.1 M.T q hq hk hqρ M.ω (fun g => ?_)
    fun e he he' => GlobalTheory.T.hom_to_characterLine_eq_zero F M h1 h2 h3 e he (he'.trans_le (by exact_mod_cast S.D.one_le_letterBlockLength))
  have hc : GlobalTheory.Cyc.IsCyc P.χQ := P.χQ_cyc
  let u : ℤ_[l] := (cyclotomicCharacter (PadicAlgCl l) l
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l S.K.1) (PadicAlgCl l) (S.K.1.fixingSubgroupEquiv g)) : ℤ_[l]ˣ)
  have hu : (u : ℚ_[l]) = (P.χQ (g : GQ l) : ℚ_[l]) := by
    rw [GlobalTheory.Cyc.TwistLift.isCyc_unique hc (GlobalTheory.Cyc.isCyc_cycChar l)]; rfl
  have h4 : (S.Γ.ε g : S.O) = algebraMap ℤ_[l] S.O u := by
    apply Subtype.ext
    refine (hε g).trans ?_
    rw [P.PD_χ, ← hu]
    rfl
  rw [hω, h4]
  exact ringHom_eq_val ((algebraMap S.O k).comp (algebraMap ℤ_[l] S.O)) u

end GlobalTheory.TopVanish
