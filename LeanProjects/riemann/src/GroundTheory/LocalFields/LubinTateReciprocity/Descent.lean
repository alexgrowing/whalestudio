import Mathlib
import GroundTheory.LocalFields.LubinTateReciprocity.TwistedPoint
import GroundTheory.LocalFields.CompletedUnramified
import GroundTheory.LocalFields.LubinTateTower
import GroundTheory.LocalFields.UnramifiedExistence
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.DescentPowerSubgroups

noncomputable section

open PowerSeries IsLocalRing ValuativeRel GroundTheory.LocalField.FormalGroup
open scoped Topology

namespace GroundTheory.LocalField

section PsEval

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem psEval_add' {σ : Type*} [Finite σ] (F G : MvPowerSeries σ 𝒪[K]) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (F + G) x = psEval F x + psEval G x := by
  have := t2Space_of_isValuativeTopology Ω
  have h := (hasSum_psEval' F x hx).add (hasSum_psEval' G x hx)
  have e : (fun d => psTerm F x d + psTerm G x d) = psTerm (F + G) x := by
    funext d
    simp [psTerm, add_mul]
  rw [e] at h
  exact h.tsum_eq

theorem psEval_mul' {σ : Type*} [Finite σ] (F G : MvPowerSeries σ 𝒪[K]) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (F * G) x = psEval F x * psEval G x := by
  let E := IntermediateField.adjoin K (Set.range x)
  have := finiteDimensional_adjoin_range (K := K) x
  let xE : σ → E := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  let a : σ → 𝒪[E] := fun i => ⟨xE i, ((valuation_coe_lt_one_iff E (xE i)).mp (hx i)).le⟩
  have ha : ∀ i, a i ∈ 𝓂[E] := fun i =>
    mem_maximalIdeal_integer_iff.mpr ((valuation_coe_lt_one_iff E (xE i)).mp (hx i))
  have h1 : psEval (F * G) x = _ := psEval_coe E (F * G) xE hx
  have h2 : psEval F x = _ := psEval_coe E F xE hx
  have h3 : psEval G x = _ := psEval_coe E G xE hx
  rw [h1, h2, h3]
  change ((psEval (F * G) fun i => (a i : E) : E) : Ω) =
    ((psEval F fun i => (a i : E) : E) : Ω) * ((psEval G fun i => (a i : E) : E) : Ω)
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have _ : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace 𝒪[K] := ⊥
  have _ : DiscreteUniformity 𝒪[K] := ⟨rfl⟩
  have hφ : Continuous[(⊥ : UniformSpace 𝒪[K]).toTopologicalSpace, _]
      (algebraMap 𝒪[K] 𝒪[E]) := by
    rw [UniformSpace.toTopologicalSpace_bot]
    exact continuous_bot
  rw [psEval_eq_eval₂ _ a ha, psEval_eq_eval₂ _ a ha, psEval_eq_eval₂ _ a ha,
    ← MvPowerSeries.coe_eval₂Hom hφ (hasEval_of_mem_maximalIdeal ha), map_mul]
  push_cast
  rfl

theorem psEval_eq_aeval_of_sub_mem {P h : Polynomial 𝒪[K]} {G : 𝒪[K]⟦X⟧}
    (hG : G - (h : 𝒪[K]⟦X⟧) ∈ Ideal.span {(P : 𝒪[K]⟦X⟧)}) {x : Ω} (hx : valuation Ω x < 1)
    (hP : Polynomial.aeval x (P.map (algebraMap 𝒪[K] K)) = 0) :
    psEval G (fun _ => x) = Polynomial.aeval x (h.map (algebraMap 𝒪[K] K)) := by
  have := t2Space_of_isValuativeTopology Ω
  obtain ⟨D, hD⟩ := Ideal.mem_span_singleton'.mp hG
  have hGe : G = (h : 𝒪[K]⟦X⟧) + D * (P : 𝒪[K]⟦X⟧) := by rw [hD]; ring
  rw [hGe, psEval_add' _ _ _ fun _ => hx, psEval_mul' _ _ _ fun _ => hx, psEval_polynomial,
    psEval_polynomial, hP, mul_zero, add_zero]

end PsEval

section Weierstrass

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π) (m : ℕ)

include hπ in

theorem isDistinguishedAt_ltEisenstein : (ltEisenstein π m).IsDistinguishedAt 𝓂[K] :=
  ⟨⟨fun hn => (isEisensteinAt_ltEisenstein hπ m).mem hn⟩, (ltEisenstein_monic π m).1⟩

include hπ in

theorem exists_sub_coe_mem_span_ltEisenstein (G : 𝒪[K]⟦X⟧) :
    ∃ h : Polynomial 𝒪[K], G - (h : 𝒪[K]⟦X⟧) ∈ Ideal.span {((ltEisenstein π m : Polynomial 𝒪[K]) :
      𝒪[K]⟦X⟧)} := by
  have := isAdicComplete_integer K
  have hP := isDistinguishedAt_ltEisenstein hπ m
  obtain ⟨h, hh⟩ := AdjoinRoot.mk_surjective (rootEval hP G)
  exact ⟨h, (rootEval_eq_rootEval_iff hP G h).mp (by rw [rootEval_coe, hh])⟩

variable {L : Type*} [Field L] [Algebra K L]

include hπ in

theorem ltEisenstein_dvd_of_aeval_eq_zero {x : L}
    (hx : Polynomial.aeval x ((ltEisenstein π m).map (algebraMap 𝒪[K] K)) = 0) {p : Polynomial 𝒪[K]}
    (hp : Polynomial.aeval x (p.map (algebraMap 𝒪[K] K)) = 0) : ltEisenstein π m ∣ p := by
  have hmon := (ltEisenstein_monic π m).1
  have hq := one_lt_card_residueField' K
  have hdeg : 0 < (ltEisenstein π m).natDegree := by
    rw [(ltEisenstein_monic π m).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) m)
  have hirr := irreducible_map_of_isEisensteinAt (isEisensteinAt_ltEisenstein hπ m) hdeg
  have hint : IsIntegral K x := ⟨_, hmon.map _, hx⟩
  have hmin : minpoly K x = (ltEisenstein π m).map (algebraMap 𝒪[K] K) :=
    (minpoly.eq_of_irreducible_of_monic hirr hx (hmon.map _)).symm
  have hdvd : (ltEisenstein π m).map (algebraMap 𝒪[K] K) ∣ p.map (algebraMap 𝒪[K] K) :=
    hmin ▸ minpoly.dvd K x hp
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hmon]
  apply Polynomial.map_injective (algebraMap 𝒪[K] K) (IsFractionRing.injective 𝒪[K] K)
  rw [Polynomial.map_modByMonic _ hmon, Polynomial.map_zero,
    Polynomial.modByMonic_eq_zero_iff_dvd (hmon.map _)]
  exact hdvd

end Weierstrass

section Iterate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π)

theorem pow_apply_eq_psEval (σ : Ω ≃ₐ[K] Ω) (a : 𝒪[K]) {x : Ω} (hx : valuation Ω x < 1)
    (hσ : σ x = psEval (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
      a).toPowerSeries fun _ => x) (k : ℕ) :
    (σ ^ k) x = psEval (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
      (a ^ k)).toPowerSeries fun _ => x := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, lubinTateHom_self_one, Hom.toPowerSeries_id, AlgEquiv.one_apply]
    exact (psEval_X (K := K) (fun _ : Unit => x) ()).symm
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, algEquiv_psEval σ _ _ fun _ => hx, hσ, pow_succ,
      lubinTateHom_mul hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
        (isLubinTateSeries_ltPoly π), Hom.toPowerSeries_comp, PowerSeries.subst_def,
      psEval_subst' (fun _ => Hom.constantCoeff_eq_zero' _) _ _ fun _ => hx]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

theorem exists_pow_apply_eq_self (σ : Ω ≃ₐ[K] Ω) {p : Polynomial K} (hp : p ≠ 0) {x : Ω}
    (hx : Polynomial.aeval x p = 0) : ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x :=
  _root_.GroundTheory.Variant₂.N1.exists_pow_apply_eq_self_of_aeval_eq_zero σ hp hx

end Iterate

section Maps

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {B : Type*} [CommRing B] [Algebra 𝒪[K] B]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem map_sub_coe_mem_span {P h : Polynomial 𝒪[K]} {G : 𝒪[K]⟦X⟧}
    (hG : G - (h : 𝒪[K]⟦X⟧) ∈ Ideal.span {(P : 𝒪[K]⟦X⟧)}) :
    PowerSeries.map (algebraMap 𝒪[K] B) G - ((h.map (algebraMap 𝒪[K] B) : Polynomial B) : B⟦X⟧) ∈
      Ideal.span {((P.map (algebraMap 𝒪[K] B) : Polynomial B) : B⟦X⟧)} := by
  have := Ideal.mem_map_of_mem (PowerSeries.map (algebraMap 𝒪[K] B)) hG
  rwa [Ideal.map_span, Set.image_singleton, map_sub, map_coe_polynomial, map_coe_polynomial] at this

theorem adjoinRoot_ringHom_ext {R S : Type*} [CommRing R] [CommRing S] {p : Polynomial R}
    {f g : AdjoinRoot p →+* S} (hof : ∀ r : R, f (AdjoinRoot.of p r) = g (AdjoinRoot.of p r))
    (hroot : f (AdjoinRoot.root p) = g (AdjoinRoot.root p)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro r
    exact hof r
  · exact hroot

end Maps

section Unramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω]

theorem apply_coe_eq_frobenius (σ : Ω ≃ₐ[K] Ω) (hσ : unramifiedDegree K Ω σ = Multiplicative.ofAdd 1)
    {L : IntermediateField K Ω} (hL : IsUnramifiedSubextension L) (y : L) :
    letI := hL.1
    σ (y : Ω) = ((frobenius K L hL.ramificationIndex_eq_one y : L) : Ω) := by
  have := hL.1
  have hr := (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff σ).mpr hσ
  rw [← maximalUnramifiedExtensionFrobenius_inclusion hL y, ← hr]
  exact (AlgEquiv.restrictNormal_commutes σ (maximalUnramifiedExtension K Ω)
    (IntermediateField.inclusion hL.le_maximalUnramifiedExtension y)).symm

theorem completedFrobenius_iterate_integerToCompleted {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) (k : ℕ) (c : 𝒪[L]) :
    letI := hL.1
    (completedFrobenius K Ω)^[k] (integerToCompleted K Ω hL.le_maximalUnramifiedExtension c) =
      integerToCompleted K Ω hL.le_maximalUnramifiedExtension
        (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one ^ k) c) := by
  have := hL.1
  induction k with
  | zero => rw [Function.iterate_zero, id, pow_zero, map_one, AlgEquiv.one_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, completedFrobenius_integerToCompleted hL, pow_succ',
      map_mul, AlgEquiv.mul_apply]

theorem residue_completedFrobenius_iterate (k : ℕ) (x : CompletedUnramifiedIntegers K Ω) :
    residue _ ((completedFrobenius K Ω)^[k] x) = residue _ x ^ (Nat.card 𝓀[K] ^ k) := by
  induction k with
  | zero => rw [Function.iterate_zero, id, pow_zero, pow_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', residue_completedFrobenius, ih, ← pow_mul, ← pow_succ]

theorem exists_integerToCompleted_eq_of_iterate {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) {b : CompletedUnramifiedIntegers K Ω}
    (hb : (completedFrobenius K Ω)^[Module.finrank K L] b = b) :
    ∃ c : 𝒪[L], integerToCompleted K Ω hL.le_maximalUnramifiedExtension c = b := by
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have := isAdicComplete_integer L
  set ι := integerToCompleted K Ω hL.le_maximalUnramifiedExtension with hι
  let _ : Algebra 𝒪[L] (CompletedUnramifiedIntegers K Ω) := ι.toRingHom.toAlgebra
  have hιa : ∀ c : 𝒪[L], algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω) c = ι c := fun _ => rfl
  set N := Module.finrank K L with hN
  have hfrobN : frobenius K L h ^ N = 1 := by
    rw [hN, ← orderOf_frobenius K L h]
    exact pow_orderOf_eq_one _
  let T : CompletedUnramifiedIntegers K Ω →+* CompletedUnramifiedIntegers K Ω :=
    (completedFrobenius K Ω).toAlgHom.toRingHom ^ N
  have hT : ∀ x, T x = (completedFrobenius K Ω)^[N] x := fun x => by
    rw [RingHom.coe_pow]
    rfl
  have hTc : ∀ c : 𝒪[L], T (algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω) c) =
      algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω) c := fun c => by
    rw [hT, hιa, hι, completedFrobenius_iterate_integerToCompleted hL, hfrobN, map_one,
      AlgEquiv.one_apply]
  let σN : CompletedUnramifiedIntegers K Ω →ₐ[𝒪[L]] CompletedUnramifiedIntegers K Ω :=
    { toRingHom := T, commutes' := hTc }
  have hσN : ∀ x, σN x = (completedFrobenius K Ω)^[N] x := hT
  have hres : ∀ x, residue _ (σN x) = residue _ x ^ Nat.card (ResidueField 𝒪[L]) := fun x => by
    rw [hσN, residue_completedFrobenius_iterate, card_residueField_of_unramified K L h]
  have hunrL : (maximalIdeal 𝒪[L]).map (algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω)) =
      maximalIdeal (CompletedUnramifiedIntegers K Ω) := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) ?_
    · rw [Ideal.mem_comap, hιa, hι, integerToCompleted_apply, mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal x).mp hx (isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ hu))
    · rw [← map_maximalIdeal_completedUnramifiedIntegers K Ω]
      have hcomp : algebraMap 𝒪[K] (CompletedUnramifiedIntegers K Ω) =
          (algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω)).comp (algebraMap 𝒪[K] 𝒪[L]) :=
        (ι.comp_algebraMap).symm
      rw [hcomp, ← Ideal.map_map]
      exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr fun x hx =>
        map_nonunit (algebraMap 𝒪[K] 𝒪[L]) x hx)
  obtain ⟨c, hc⟩ := (mem_range_algebraMap_iff_fixed hunrL σN hres b).mpr (by rw [hσN]; exact hb)
  exact ⟨c, hc⟩

end Unramified

section Descent

variable {R : Type*} [CommRing R]

theorem eval₂_of_mk (f p q : Polynomial R) :
    Polynomial.eval₂ (AdjoinRoot.of f) (AdjoinRoot.mk f q) p = AdjoinRoot.mk f (p.comp q) :=
  (Polynomial.hom_eval₂ p Polynomial.C (AdjoinRoot.mk f) q).symm

theorem adjoinRoot_map_mk {S : Type*} [CommRing S] (ι : R →+* S) (p : Polynomial R) (q : Polynomial S)
    (h : q ∣ p.map ι) (g : Polynomial R) :
    AdjoinRoot.map ι p q h (AdjoinRoot.mk p g) = AdjoinRoot.mk q (g.map ι) := by
  have key : (AdjoinRoot.map ι p q h).comp (AdjoinRoot.mk p) =
      (AdjoinRoot.mk q).comp (Polynomial.mapRingHom ι) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp
    · simp
  exact congrArg (fun F : Polynomial R →+* AdjoinRoot q => F g) key

theorem adjoinRoot_map_injective {S : Type*} [CommRing S] {ι : R →+* S} (hι : Function.Injective ι)
    {p : Polynomial R} (hp : p.Monic) {q : Polynomial S} (hq : q ∣ p.map ι) (hpq : p.map ι = q) :
    Function.Injective (AdjoinRoot.map ι p q hq) := by
  subst hpq
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
  rw [adjoinRoot_map_mk, AdjoinRoot.mk_eq_zero, ← Polynomial.modByMonic_eq_zero_iff_dvd (hp.map ι),
    ← Polynomial.map_modByMonic ι hp] at hw
  rw [AdjoinRoot.mk_eq_zero, ← Polynomial.modByMonic_eq_zero_iff_dvd hp]
  exact Polynomial.map_injective ι hι (by rw [hw, Polynomial.map_zero])

theorem exists_adjoinRoot_twist (p : Polynomial R) (ψ : R →+* R) (hψ : p.map ψ = p) (g : Polynomial R)
    (hg : p ∣ p.comp g) :
    ∃ τ : AdjoinRoot p →+* AdjoinRoot p, (∀ c, τ (AdjoinRoot.of p c) = AdjoinRoot.of p (ψ c)) ∧
      τ (AdjoinRoot.root p) = AdjoinRoot.mk p g := by
  refine ⟨AdjoinRoot.lift ((AdjoinRoot.of p).comp ψ) (AdjoinRoot.mk p g) ?_,
    fun c => AdjoinRoot.lift_of _, AdjoinRoot.lift_root _⟩
  rw [← Polynomial.eval₂_map, hψ, eval₂_of_mk, AdjoinRoot.mk_eq_zero]
  exact hg

theorem exists_adjoinRoot_lift {S : Type*} [CommRing S] (p : Polynomial R) (jc : R →+* S) (x : S)
    (hx : p.eval₂ jc x = 0) :
    ∃ j : AdjoinRoot p →+* S, (∀ c, j (AdjoinRoot.of p c) = jc c) ∧ j (AdjoinRoot.root p) = x ∧
      ∀ g, j (AdjoinRoot.mk p g) = g.eval₂ jc x :=
  ⟨AdjoinRoot.lift jc x hx, fun _ => AdjoinRoot.lift_of _, AdjoinRoot.lift_root _,
    fun _ => AdjoinRoot.lift_mk _ _⟩

theorem exists_adjoinRoot_map_eq {S : Type*} [CommRing S] (ι : R →+* S) (p : Polynomial R)
    {q : Polynomial S} (hq : q ∣ p.map ι) (hqm : q.Monic) (z : AdjoinRoot q)
    (d : Fin (AdjoinRoot.powerBasis' hqm).dim → R)
    (hd : ∀ i, ι (d i) = (AdjoinRoot.powerBasis' hqm).basis.repr z i) :
    ∃ y : AdjoinRoot p, AdjoinRoot.map ι p q hq y = z := by
  refine ⟨∑ i, AdjoinRoot.of p (d i) * AdjoinRoot.root p ^ (i : ℕ), ?_⟩
  conv_rhs => rw [← (AdjoinRoot.powerBasis' hqm).basis.sum_repr z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, AdjoinRoot.map_of, AdjoinRoot.map_root, hd, Algebra.smul_def,
    PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen, AdjoinRoot.algebraMap_eq]

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) (u : 𝒪[K]ˣ) (m : ℕ)

set_option maxHeartbeats 1000000 in
include hπ in

theorem exists_fixed_root_ltEisenstein (σ : Ω ≃ₐ[K] Ω)
    (hσ : unramifiedDegree K Ω σ = Multiplicative.ofAdd 1) {l : Ω}
    (hl : Polynomial.aeval l ((ltEisenstein π m).map (algebraMap 𝒪[K] K)) = 0)
    (hσl : σ l = psEval (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
      ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])).toPowerSeries fun _ => l) :
    ∃ x : Ω, Polynomial.aeval x ((ltEisenstein ((u : 𝒪[K]) * π) m).map (algebraMap 𝒪[K] K)) = 0 ∧
      σ x = x ∧ ∀ τ : Ω ≃ₐ[K] Ω, (∀ y ∈ maximalUnramifiedExtension K Ω, τ y = y) → τ l = l →
        τ x = x := by
  classical
  have hPmon : (ltEisenstein π m).Monic := (ltEisenstein_monic π m).1

  have hlv : valuation Ω l < 1 := by
    refine valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ (m + 1) ?_
    rw [ltPolyIter_succ_eq_mul, Polynomial.map_mul, map_mul, hl, mul_zero]

  obtain ⟨h, hh⟩ := exists_sub_coe_mem_span_ltEisenstein hπ m
    (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])).toPowerSeries
  have hσl' : σ l = Polynomial.aeval l (h.map (algebraMap 𝒪[K] K)) :=
    hσl.trans (psEval_eq_aeval_of_sub_mem hh hlv hl)

  obtain ⟨N, hN0, hNl⟩ := exists_pow_apply_eq_self σ ((hPmon.map (algebraMap 𝒪[K] K)).ne_zero) hl
  obtain ⟨hN', hhN'⟩ := exists_sub_coe_mem_span_ltEisenstein hπ m
    (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries
  have haevalN : Polynomial.aeval l (hN'.map (algebraMap 𝒪[K] K)) = l := by
    rw [← psEval_eq_aeval_of_sub_mem hhN' hlv hl, ← pow_apply_eq_psEval hπ σ _ hlv hσl N, hNl]
  have hdvdN : (ltEisenstein π m) ∣ hN' - Polynomial.X := by
    refine ltEisenstein_dvd_of_aeval_eq_zero hπ m hl ?_
    rw [Polynomial.map_sub, Polynomial.map_X, map_sub, haevalN, Polynomial.aeval_X, sub_self]
  have hGN : (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries -
      ((Polynomial.X : Polynomial 𝒪[K]) : 𝒪[K]⟦X⟧) ∈ Ideal.span {((ltEisenstein π m) : 𝒪[K]⟦X⟧)} := by
    obtain ⟨q, hq⟩ := hdvdN
    have e : (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries -
        ((Polynomial.X : Polynomial 𝒪[K]) : 𝒪[K]⟦X⟧) =
        ((lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries - (hN' : 𝒪[K]⟦X⟧)) +
          ((ltEisenstein π m) : 𝒪[K]⟦X⟧) * (q : 𝒪[K]⟦X⟧) := by
      rw [← Polynomial.coe_mul, ← hq, Polynomial.coe_sub]
      ring
    rw [e]
    exact add_mem hhN' (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

  have hunr := map_maximalIdeal_completedUnramifiedIntegers K Ω
  obtain ⟨z, hzfix, hzroot⟩ := exists_twistFrob_fixed_root hπ hunr m
    (completedFrobenius K Ω).toAlgHom residue_completedFrobenius u
  set T := twistFrob hπ hunr m (completedFrobenius K Ω).toAlgHom u with hT
  have hP := isDistinguishedAt_ltEisB hπ hunr m
  have hTN : T^[N] (AdjoinRoot.root (ltEisB π (CompletedUnramifiedIntegers K Ω) m)) =
      AdjoinRoot.root (ltEisB π (CompletedUnramifiedIntegers K Ω) m) := by
    rw [hT, twistFrob_iterate_root, ← rootEval_X hP, rootEval_eq_rootEval_iff]
    have := map_sub_coe_mem_span (B := CompletedUnramifiedIntegers K Ω) hGN
    rwa [Polynomial.map_X, Polynomial.coe_X] at this

  have hzN : T^[N] z = z := Function.iterate_fixed hzfix N
  obtain ⟨L, ⟨hL, hLN⟩, -⟩ := existsUnique_isUnramifiedSubextension (K := K) (Ksep := Ω) hN0.ne'
  have := hL.1
  have hcoord : ∀ i, ∃ d : 𝒪[L], integerToCompleted K Ω hL.le_maximalUnramifiedExtension d =
      (AdjoinRoot.powerBasis' (monic_ltEisB π (CompletedUnramifiedIntegers K Ω) m)).basis.repr z i :=
      fun i => by
    refine exists_integerToCompleted_eq_of_iterate hL ?_
    rw [hLN]
    have := repr_twistFrob_iterate hπ hunr m (completedFrobenius K Ω).toAlgHom u hTN z i
    rw [← hT, hzN] at this
    exact this.symm
  choose d hd using hcoord

  have hPLmap : ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).map
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _) =
      ltEisB π (CompletedUnramifiedIntegers K Ω) m := by
    rw [Polynomial.map_map, AlgHom.comp_algebraMap]
  have hdvd : ltEisB π (CompletedUnramifiedIntegers K Ω) m ∣ ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).map
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _) := hPLmap ▸ dvd_rfl
  have hιinj : Function.Injective
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* CompletedUnramifiedIntegers K Ω) :=
    integerToCompleted_injective _
  have hinj := adjoinRoot_map_injective hιinj (hPmon.map (algebraMap 𝒪[K] 𝒪[L])) hdvd hPLmap
  obtain ⟨y, hy⟩ := exists_adjoinRoot_map_eq
    (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* CompletedUnramifiedIntegers K Ω)
    ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])) hdvd (monic_ltEisB π (CompletedUnramifiedIntegers K Ω) m) z d hd
  generalize hiM : AdjoinRoot.map
    (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* CompletedUnramifiedIntegers K Ω)
    ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])) (ltEisB π (CompletedUnramifiedIntegers K Ω) m) hdvd = iM at hinj hy
  have hiMof : ∀ c : 𝒪[L], iM (AdjoinRoot.of _ c) = AdjoinRoot.of _
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension c) := fun c => by
    rw [← hiM, AdjoinRoot.map_of]
    rfl
  have hiMroot : iM (AdjoinRoot.root _) = AdjoinRoot.root _ := by
    rw [← hiM, AdjoinRoot.map_root]
  have hiMmk : ∀ g : Polynomial 𝒪[L], iM (AdjoinRoot.mk _ g) = AdjoinRoot.mk _
      (g.map (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _)) := fun g => by
    rw [← hiM, adjoinRoot_map_mk]

  have hPcomp : (ltEisenstein π m) ∣ (ltEisenstein π m).comp h := by
    refine ltEisenstein_dvd_of_aeval_eq_zero hπ m hl ?_
    rw [Polynomial.map_comp, Polynomial.aeval_comp, ← hσl']
    have e := Polynomial.aeval_algHom_apply (σ : Ω →ₐ[K] Ω) l ((ltEisenstein π m).map (algebraMap 𝒪[K] K))
    change Polynomial.aeval (σ l) _ = 0
    rw [show ((σ : Ω →ₐ[K] Ω) l) = σ l from rfl] at e
    rw [e, hl, map_zero]
  have hfrPL : ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).map
      (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).toAlgHom.toRingHom =
      (ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun c => (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).commutes c
  have hPcompL : (ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]) ∣
      ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).comp (h.map (algebraMap 𝒪[K] 𝒪[L])) := by
    rw [← Polynomial.map_comp (f := algebraMap 𝒪[K] 𝒪[L])]
    exact Polynomial.map_dvd _ hPcomp
  obtain ⟨σL, hσLof, hσLroot⟩ := exists_adjoinRoot_twist ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))
    (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).toAlgHom.toRingHom hfrPL
    (h.map (algebraMap 𝒪[K] 𝒪[L])) hPcompL

  have hφι : ∀ c : 𝒪[L], (completedFrobenius K Ω).toAlgHom
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension c) =
      integerToCompleted K Ω hL.le_maximalUnramifiedExtension
        ((integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).toAlgHom.toRingHom c) :=
    fun c => completedFrobenius_integerToCompleted hL c
  have hsq1 : iM.comp σL = T.comp iM := by
    refine adjoinRoot_ringHom_ext (fun c => ?_) ?_
    · change iM (σL _) = T (iM _)
      rw [hσLof, hiMof, hiMof, hT, twistFrob_of, hφι]
    · change iM (σL _) = T (iM _)
      rw [hσLroot, hiMmk, hiMroot, hT, twistFrob_root,
        Polynomial.map_map, AlgHom.comp_algebraMap, ← rootEval_coe hP]
      exact ((rootEval_eq_rootEval_iff hP _ _).mpr (map_sub_coe_mem_span hh)).symm

  have hσLy : σL y = y := by
    apply hinj
    change (iM.comp σL) y = iM y
    rw [hsq1]
    change T (iM y) = iM y
    rw [hy, hzfix]

  have hiMofc : iM.comp (AdjoinRoot.of ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))) =
      (AdjoinRoot.of (ltEisB π (CompletedUnramifiedIntegers K Ω) m)).comp
        (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _) :=
    RingHom.ext hiMof
  have hy' : Polynomial.eval₂ (AdjoinRoot.of ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))) y
      ((ltEisenstein ((u : 𝒪[K]) * π) m).map (algebraMap 𝒪[K] 𝒪[L])) = 0 := by
    apply hinj
    rw [map_zero, Polynomial.hom_eval₂, hiMofc, hy, ← Polynomial.eval₂_map, Polynomial.map_map,
      AlgHom.comp_algebraMap]
    exact hzroot

  have hjc : ((algebraMap L Ω).comp (algebraMap 𝒪[L] L)).comp (algebraMap 𝒪[K] 𝒪[L]) =
      (algebraMap K Ω).comp (algebraMap 𝒪[K] K) := by
    refine RingHom.ext fun c => ?_
    change algebraMap L Ω (algebraMap K L (c : K)) = algebraMap K Ω (c : K)
    exact (IsScalarTower.algebraMap_apply K L Ω (c : K)).symm
  obtain ⟨j, hjof, hjroot, hjmk⟩ := exists_adjoinRoot_lift
    ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])) ((algebraMap L Ω).comp (algebraMap 𝒪[L] L)) l
    (by rw [Polynomial.eval₂_map, hjc, ← Polynomial.eval₂_map]; exact hl)
  have hjc' : j.comp (AdjoinRoot.of ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))) =
      (algebraMap L Ω).comp (algebraMap 𝒪[L] L) := RingHom.ext hjof

  have hsq2 : (σ : Ω →+* Ω).comp j = j.comp σL := by
    refine adjoinRoot_ringHom_ext (fun c => ?_) ?_
    · change σ (j _) = j (σL _)
      rw [hσLof, hjof, hjof]
      change σ ((c : L) : Ω) = (((integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one) c :
        𝒪[L]) : L) : Ω)
      rw [coe_integerAlgEquiv_apply]
      exact apply_coe_eq_frobenius σ hσ hL (c : L)
    · change σ (j _) = j (σL _)
      rw [hσLroot, hjmk, hjroot, hσl', Polynomial.eval₂_map, hjc, ← Polynomial.eval₂_map]
      rfl
  refine ⟨j y, ?_, ?_, ?_⟩
  · change Polynomial.eval₂ (algebraMap K Ω) (j y)
      ((ltEisenstein ((u : 𝒪[K]) * π) m).map (algebraMap 𝒪[K] K)) = 0
    rw [Polynomial.eval₂_map, ← hjc, ← Polynomial.eval₂_map, ← hjc', ← Polynomial.hom_eval₂, hy',
      map_zero]
  · change ((σ : Ω →+* Ω).comp j) y = j y
    rw [hsq2]
    change j (σL y) = j y
    rw [hσLy]
  · intro τ hτ hτl
    have hτj : (τ : Ω →+* Ω).comp j = j := by
      refine adjoinRoot_ringHom_ext (fun c => ?_) ?_
      · change τ (j _) = j _
        rw [hjof]
        exact hτ _ (hL.le_maximalUnramifiedExtension (c : L).2)
      · change τ (j _) = j _
        rw [hjroot]
        exact hτl
    change ((τ : Ω →+* Ω).comp j) y = j y
    rw [hτj]

end Descent

end GroundTheory.LocalField
