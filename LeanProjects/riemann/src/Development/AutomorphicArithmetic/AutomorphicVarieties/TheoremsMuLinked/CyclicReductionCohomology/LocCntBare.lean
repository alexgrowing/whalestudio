import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem cardZ {k D M : Type} [CommRing k] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M] (σ : Representation k D M) (hσ : ContAction σ)
    [Finite (H1 σ)] : Finite (Z1 σ) ∧ Nat.card (Z1 σ) * Nat.card (H0 σ) = Nat.card (H1 σ) * Nat.card M := by
  have hle : ReciprocityTheory.Gal.B1 σ ≤ Z1 σ := by
    rintro _ ⟨m, rfl⟩
    refine ⟨(hσ.comp (continuous_id.prodMk continuous_const)).sub continuous_const, fun g h => ?_⟩
    simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hker : LinearMap.ker (d0 σ) = H0 σ := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp only [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero]
  have h1 : Nat.card M = Nat.card (H0 σ) * Nat.card (ReciprocityTheory.Gal.B1 σ) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d0 σ)), hker.symm,
      Nat.card_congr (d0 σ).quotKerEquivRange.toEquiv]
    rfl
  have h2 : Nat.card (Z1 σ) = Nat.card (ReciprocityTheory.Gal.B1 σ) * Nat.card (H1 σ) := by
    rw [Submodule.card_eq_card_quotient_mul_card ((ReciprocityTheory.Gal.B1 σ).comap (Z1 σ).subtype),
      Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv]
  have hM : Nat.card M ≠ 0 := Nat.card_pos.ne'
  refine ⟨Nat.finite_of_card_ne_zero ?_, by rw [h1, h2]; ring⟩
  rw [h2]
  exact mul_ne_zero (right_ne_zero_of_mul (h1 ▸ hM)) Nat.card_pos.ne'

private theorem cardInv {n : ℕ} [NeZero n] {D M M' : Type} [Group D] [AddCommGroup M] [Module (ZMod n) M]
    [AddCommGroup M'] [Module (ZMod n) M'] [Finite M] [Finite M'] (χ : D →* (ZMod n)ˣ)
    (σ : Representation (ZMod n) D M) (τ : D → M' → M') (b : M →+ M' →+ ZMod n)
    (hl : ∀ x, (∀ y, b x y = 0) → x = 0) (hr : ∀ y, (∀ x, b x y = 0) → y = 0)
    (he : ∀ g x y, b (σ g x) (τ g y) = χ g * b x y) :
    Nat.card (H0 ((twDual χ σ).comp (MonoidHom.id D))) = Nat.card {y : M' // ∀ g, τ g y = y} := by
  let f : M' → Module.Dual (ZMod n) M := fun y => (b.flip y).toZModLinearMap n
  have hb : Function.Bijective f := (dualZ n M).2.2 M' b hl hr
  have hf := hb.1
  have key : ∀ g y x, twDual χ σ g (f y) x = b x (τ g y) := fun g y x => by
    have := he g (σ g⁻¹ x) y
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm
  refine (Nat.card_congr ((Equiv.ofBijective f hb).subtypeEquiv fun y => ?_)).symm
  constructor
  · intro h g
    refine TDual.ext fun x => (key g y x).trans ?_
    rw [h]; rfl
  · intro h g
    refine hf (LinearMap.ext fun x => (key g y x).symm.trans ?_)
    exact congrArg (fun φ : TDual (ZMod n) M => φ x) (h g)

private def zRep (n : ℕ) {R D M : Type} [CommRing R] [Group D] [AddCommGroup M] [Module R M] [Module (ZMod n) M]
    (ρ : Representation R D M) : Representation (ZMod n) D M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul]; rfl

theorem UpperTheory.V.Th.locCntBare :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → (((l : ℕ) : 𝓞 F) ∈ v.asIdeal → LocCnt (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) (locDeg v)) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → LocCnt (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) 0) := by
  intro hF hT hE l _ F Ω _ _ _ _ _ A v hA
  suffices H : ∀ d, ((((l : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ d = locDeg v) ∨ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal ∧ d = 0)) →
      LocCnt (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) d from
    ⟨fun h => H _ (.inl ⟨h, rfl⟩), fun h => H _ (.inr ⟨h, rfl⟩)⟩
  intro d hd k hk R M M' _ _ _ _ _ _ _ ρ ρ' b hρ hb
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hl0 : ∀ z : ZMod (l ^ k), l ^ k • z = 0 := fun z => by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ k)) M) := ⟨AddCommGroup.zmodModule fun x => hb.left _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, hl0]⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ k)) M') := ⟨AddCommGroup.zmodModule fun y => hb.right _ fun x => by
    rw [map_nsmul, hl0]⟩
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  let σ : Representation (ZMod (l ^ k)) (Dec (F := F) A) M := zRep (l ^ k) ρ
  have hσ : ContAction σ := continuous_prod_of_discrete_right.2 fun m => (hρ m).continuous
  obtain ⟨-, f1, -, -⟩ := hF F Ω l k M A σ v hk hA hσ
  obtain ⟨⟨inv⟩, -, -, -, h20⟩ := hT F Ω l k M A σ v hk hA hσ
  have hE' := hE F Ω l k M A σ v hk hA hσ
  have e1 : Nat.card (H1 σ) = Nat.card (H0 σ) * Nat.card (H2 σ) * Nat.card M ^ d := by
    rcases hd with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact hE'.1 h
    · rw [pow_zero, mul_one]; exact hE'.2 h
  obtain ⟨fz, e2⟩ := cardZ σ hσ
  let EZ : Zl ρ ≃ Z1 σ := Equiv.subtypeEquivRight fun z =>
    and_congr (IsLocallyConstant.iff_continuous z) Iff.rfl
  let χ := (cycMod F Ω l k).comp (Dec (F := F) A).subtype
  have e3 := cardInv χ σ (fun g y => ρ' g y) b hb.left hb.right (fun g x y => hb.equiv g x y)
  haveI : Finite (TDual (ZMod (l ^ k)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ k)] ZMod (l ^ k)))
  let B : Type := H0 ((twDual χ σ).comp (MonoidHom.id _))
  let E : H2 σ ≃ Module.Dual (ZMod (l ^ k)) B :=
    (Equiv.ofBijective _ h20).trans (LinearEquiv.congrRight inv).toEquiv
  haveI : Finite B := Subtype.finite
  have e4 : Nat.card (H2 σ) = Nat.card ρ'.invariants := by
    rw [Nat.card_congr E, (dualZ (l ^ k) B).1]
    exact e3
  refine ⟨Finite.of_equiv _ EZ.symm, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H0 σ))
  rw [Nat.card_congr EZ, e2, e1, e4]
  ring
