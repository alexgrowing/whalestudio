import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem cardZ {k D M : Type} [CommRing k] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M] (σ : Representation k D M) (hσ : ContAction σ)
    [Finite (H1 σ)] : Finite (Z1 σ) ∧ Nat.card (Z1 σ) * Nat.card (H0 σ) = Nat.card (H1 σ) * Nat.card M := by
  classical
  have hB : B1 σ ≤ Z1 σ := by
    intro f hf
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hf
    show Continuous (d0 σ m) ∧ ∀ g h, d0 σ m (g * h) = d0 σ m g + σ g (d0 σ m h)
    refine ⟨?_, ?_⟩
    · have e : (d0 σ m) = fun g => σ g m - m := funext (fun g => amitsur_d0_apply σ m g)
      rw [e]
      exact (hσ.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · intro g h
      simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have hker : LinearMap.ker (d0 σ) = H0 σ := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp only [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero]
  have hM : Nat.card M = Nat.card (B1 σ) * Nat.card (H0 σ) := by
    rw [(LinearMap.ker (d0 σ)).card_eq_card_quotient_mul_card, mul_comm]
    congr 1
    · exact Nat.card_congr (d0 σ).quotKerEquivRange.toEquiv
    · rw [hker]
  have hS : Nat.card (Submodule.comap (Z1 σ).subtype (B1 σ)) = Nat.card (B1 σ) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hB).toEquiv
  have hZ : Nat.card (Z1 σ) =
      Nat.card (Submodule.comap (Z1 σ).subtype (B1 σ)) * Nat.card (H1 σ) :=
    Submodule.card_eq_card_quotient_mul_card _
  haveI hBfin : Finite (B1 σ) := Finite.of_surjective _ (d0 σ).surjective_rangeRestrict
  have hpos1 : 0 < Nat.card (B1 σ) := Nat.card_pos
  have hpos2 : 0 < Nat.card (H1 σ) := Nat.card_pos
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hZ, hS]
    positivity
  · rw [hZ, hS, hM]
    ring

private theorem cardDual (k V : Type) [Field k] [AddCommGroup V] [Module k V] [Finite V] :
    Nat.card (Module.Dual k V) = Nat.card V := by
  haveI : Module.Finite k V := Module.Finite.of_finite
  exact Nat.card_congr (Module.Free.chooseBasis k V).toDualEquiv.symm.toEquiv

private theorem cardInv {n : ℕ} [Fact n.Prime] {D M M' : Type} [Group D] [AddCommGroup M] [Module (ZMod n) M]
    [AddCommGroup M'] [Module (ZMod n) M'] [Finite M] [Finite M'] (χ : D →* (ZMod n)ˣ)
    (σ : Representation (ZMod n) D M) (τ : D → M' → M') (b : M →+ M' →+ ZMod n)
    (hl : ∀ x, (∀ y, b x y = 0) → x = 0) (hr : ∀ y, (∀ x, b x y = 0) → y = 0)
    (he : ∀ g x y, b (σ g x) (τ g y) = χ g * b x y) :
    Nat.card (H0 ((twDual χ σ).comp (MonoidHom.id D))) = Nat.card {y : M' // ∀ g, τ g y = y} := by
  classical
  let Φ : M' → Module.Dual (ZMod n) M := fun y => (b.flip y).toZModLinearMap n
  have hΦ : ∀ y x, Φ y x = b x y := fun y x => rfl
  have hsep : ∀ y y' : M', (∀ x, b x y = b x y') → y = y' := by
    intro y y' h
    have := hr (y - y') (fun x => by rw [map_sub, h x, sub_self])
    exact sub_eq_zero.mp this
  have hΦi : Function.Injective Φ := by
    intro y y' h
    exact hsep y y' (fun x => by rw [← hΦ, ← hΦ, h])
  have hΨi : Function.Injective (fun x : M => (b x).toZModLinearMap n) := by
    intro x x' h
    have h' : ∀ y, b x y = b x' y := fun y => LinearMap.congr_fun h y
    have := hl (x - x') (fun y => by rw [map_sub, AddMonoidHom.sub_apply, h' y, sub_self])
    exact sub_eq_zero.mp this
  have c1 := cardDual (ZMod n) M
  have c2 := cardDual (ZMod n) M'
  haveI : Finite (Module.Dual (ZMod n) M) :=
    Nat.finite_of_card_ne_zero (by rw [c1]; exact Nat.card_pos.ne')
  haveI : Finite (Module.Dual (ZMod n) M') :=
    Nat.finite_of_card_ne_zero (by rw [c2]; exact Nat.card_pos.ne')
  have le1 : Nat.card M ≤ Nat.card M' := c2 ▸ Nat.card_le_card_of_injective _ hΨi
  have hΦb : Function.Bijective Φ := hΦi.bijective_of_nat_card_le (by rw [c1]; exact le1)
  have hinv : ∀ g (x : M), σ g (σ g⁻¹ x) = x := by
    intro g x
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have htw : ∀ g y x, ((twDual χ σ) g (Φ y)) x = b x (τ g y) := by
    intro g y x
    have e := he g (σ g⁻¹ x) y
    rw [hinv] at e
    rw [e]
    rfl
  have hmem : ∀ y, Φ y ∈ H0 ((twDual χ σ).comp (MonoidHom.id D)) ↔ ∀ g, τ g y = y := by
    intro y
    show (∀ g, ((twDual χ σ).comp (MonoidHom.id D)) g (Φ y) = Φ y) ↔ _
    constructor
    · intro h g
      apply hsep
      intro x
      rw [← htw g y x]
      exact DFunLike.congr_fun (h g) x
    · intro h g
      apply TDual.ext
      intro x
      show ((twDual χ σ) g (Φ y)) x = Φ y x
      rw [htw, h g]
      rfl
  refine (Nat.card_congr (Equiv.ofBijective
    (fun y : {y : M' // ∀ g, τ g y = y} =>
      (⟨Φ y.1, (hmem y.1).2 y.2⟩ : ↥(H0 ((twDual χ σ).comp (MonoidHom.id D))))) ⟨?_, ?_⟩)).symm
  · intro y y' h
    exact Subtype.ext (hΦi (congrArg Subtype.val h))
  · intro φ
    obtain ⟨y, hy⟩ := hΦb.2 φ.1
    have hy' : Φ y ∈ H0 ((twDual χ σ).comp (MonoidHom.id D)) := by
      rw [hy]
      exact φ.2
    exact ⟨⟨y, (hmem y).1 hy'⟩, Subtype.ext hy⟩

private def zRep (n : ℕ) {R D M : Type} [CommRing R] [Group D] [AddCommGroup M] [Module R M] [Module (ZMod n) M]
    (ρ : Representation R D M) : Representation (ZMod n) D M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul]; rfl

private theorem cast_toZMod {l : ℕ} [Fact l.Prime] (h : l ^ 1 ∣ l) (x : ℤ_[l]) :
    ZMod.castHom h (ZMod (l ^ 1)) (PadicInt.toZMod x) = PadicInt.toZModPow 1 x := by
  have hinj : Function.Injective (ZMod.castHom h (ZMod (l ^ 1))) := by
    haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact (Fact.out : l.Prime).one_lt⟩
    exact (ZMod.castHom h (ZMod (l ^ 1))).injective
  have hspan : Ideal.span {((l : ℤ_[l])) ^ 1} = RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    rw [pow_one, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
  have key : (ZMod.castHom h (ZMod (l ^ 1))).comp PadicInt.toZMod = PadicInt.toZModPow 1 := by
    apply ZMod.ringHom_eq_of_ker_eq
    rw [PadicInt.ker_toZModPow, hspan]
    ext y
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
    constructor
    · intro hy
      apply hinj
      rw [hy, map_zero]
    · intro hy
      rw [hy, map_zero]
  exact congrArg (fun f : ℤ_[l] →+* ZMod (l ^ 1) => f x) key

theorem UpperTheory.V.Pa.locBare :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → (((l : ℕ) : 𝓞 F) ∈ v.asIdeal → LocCount (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) (locDeg v)) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → LocCount (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) 0) := by
  intro hF hT hE l _ F Ω _ _ _ _ _ A v hv
  haveI hl1 : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  have hdvd : l ^ 1 ∣ l := by rw [pow_one]
  have tate : ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M]
      [TopologicalSpace M] [DiscreteTopology M]
      (σ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), ReciprocityTheory.Gal.ContAction σ →
      Nat.card ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) σ).comp
        (MonoidHom.id (Dec (F := F) A)))) ≠ 0 →
      Nat.card (H2 σ) = Nat.card ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) σ).comp
        (MonoidHom.id (Dec (F := F) A)))) := by
    intro M _ _ _ _ _ σ hσ hne
    haveI := Nat.finite_of_card_ne_zero hne
    obtain ⟨⟨eχ⟩, -, -, -, h20⟩ := hT F Ω l 1 M A σ v one_pos hv hσ
    have hχiso : Nonempty (H2 ((charRep ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype)).comp
        (MonoidHom.id (Dec (F := F) A))) ≃ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) := by
      rw [MonoidHom.comp_id]
      exact ⟨eχ⟩
    obtain ⟨e2⟩ := hχiso
    have hc1 : Nat.card (H2 σ) = Nat.card (H2 (σ.comp (MonoidHom.id (Dec (F := F) A)))) := by
      rw [MonoidHom.comp_id]
    rw [hc1, Nat.card_congr (Equiv.ofBijective _ h20),
      Nat.card_congr (LinearEquiv.congrRight e2).toEquiv, cardDual]
  have core : ∀ d : ℕ, (∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M]
      [TopologicalSpace M] [DiscreteTopology M]
      (rho : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), ReciprocityTheory.Gal.ContAction rho →
      Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho) * Nat.card M ^ d) →
      LocCount (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) d := by
    intro d hEd R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hD
    have hkill : ∀ x : M, (l ^ 1 : ℕ) • x = 0 := by
      intro x
      apply hD.left
      intro y
      simp [map_nsmul, nsmul_eq_mul]
    have hkill' : ∀ y : M', (l ^ 1 : ℕ) • y = 0 := by
      intro y
      apply hD.right
      intro x
      simp [map_nsmul, nsmul_eq_mul]
    letI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule hkill
    letI : Module (ZMod (l ^ 1)) M' := AddCommGroup.zmodModule hkill'
    letI : TopologicalSpace M := ⊥
    haveI : DiscreteTopology M := ⟨rfl⟩
    let σ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M := zRep (l ^ 1) ρ
    have hσ : ReciprocityTheory.Gal.ContAction σ := by
      show Continuous fun p : (Dec (F := F) A) × M => ρ p.1 p.2
      rw [continuous_prod_of_discrete_right]
      intro m
      exact (hLC m).continuous
    obtain ⟨hf0, hf1, hf2, -⟩ := hF F Ω l 1 M A σ v one_pos hv hσ
    haveI := hf0
    haveI := hf1
    haveI := hf2
    have hE1 := hEd M σ hσ
    obtain ⟨hZfin, hZc⟩ := cardZ σ hσ
    let τ : Dec (F := F) A → M' → M' := fun g y => ρ' g y
    let c : ZMod l →+* ZMod (l ^ 1) := ZMod.castHom hdvd (ZMod (l ^ 1))
    have cinj : Function.Injective c := c.injective
    let b' : M →+ M' →+ ZMod (l ^ 1) :=
      AddMonoidHom.mk' (fun x => c.toAddMonoidHom.comp (b x)) (fun x x' => by ext y; simp)
    have hb' : ∀ x y, b' x y = c (b x y) := fun x y => rfl
    have hl' : ∀ x, (∀ y, b' x y = 0) → x = 0 := by
      intro x h
      apply hD.left
      intro y
      apply cinj
      rw [← hb', h y, map_zero]
    have hr' : ∀ y, (∀ x, b' x y = 0) → y = 0 := by
      intro y h
      apply hD.right
      intro x
      apply cinj
      rw [← hb', h x, map_zero]
    have he' : ∀ (g : Dec (F := F) A) (x : M) (y : M'),
        b' (ρ g x) (τ g y) = (((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) g : ZMod (l ^ 1)) * b' x y := by
      intro g x y
      show c (b (ρ g x) (ρ' g y)) = _ * c (b x y)
      rw [hD.equiv, map_mul]
      congr 1
      exact cast_toZMod hdvd _
    have hinvc := cardInv ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) σ τ b' hl' hr' he'
    haveI : Nonempty {y : M' // ∀ g, τ g y = y} := ⟨⟨0, fun g => map_zero (ρ' g)⟩⟩
    have hpos : Nat.card {y : M' // ∀ g, τ g y = y} ≠ 0 := Nat.card_pos.ne'
    rw [← hinvc] at hpos
    have hinv2 : Nat.card ↥ρ'.invariants = Nat.card {y : M' // ∀ g, τ g y = y} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun y => Iff.rfl))
    have hH2 : Nat.card (H2 σ) = Nat.card ↥ρ'.invariants := by
      rw [tate M σ hσ hpos, hinvc, hinv2]
    have hZeq : ↥(Zl ρ) ≃ ↥(Z1 σ) := Equiv.subtypeEquivRight (fun z => by
      show (IsLocallyConstant z ∧ _) ↔ (Continuous z ∧ _)
      rw [IsLocallyConstant.iff_continuous]
      rfl)
    refine ⟨Finite.of_equiv _ hZeq.symm, ?_⟩
    rw [Nat.card_congr hZeq]
    refine Nat.eq_of_mul_eq_mul_right ?_ (hZc.trans ?_)
    · exact Nat.card_pos_iff.2 ⟨⟨⟨0, Submodule.zero_mem _⟩⟩, hf0⟩
    · rw [hE1, ← hH2, add_comm 1 d, pow_succ (Nat.card M) d]
      ring
  refine ⟨fun hl => core (locDeg v) ?_, fun hl => core 0 ?_⟩
  · intro M _ _ _ _ _ rho hc
    exact (hE F Ω l 1 M A rho v one_pos hv hc).1 hl
  · intro M _ _ _ _ _ rho hc
    rw [pow_zero, mul_one]
    exact (hE F Ω l 1 M A rho v one_pos hv hc).2 hl
