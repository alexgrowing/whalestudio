import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDualGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.QocEquiv

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.dualEmb :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module O M] [Module (ZMod (l ^ r)) M], Nonempty (M ≃ₗ[O] (O ⧸ Ideal.span {a})) → ∃ ι : TDual (ZMod (l ^ r)) M →+ QO l O, Function.Injective ι ∧ (∀ w, a • w = 0 ↔ w ∈ Set.range ι) ∧ ∀ (y : ℤ_[l]) (x : O) (φ φ' : TDual (ZMod (l ^ r)) M), (∀ m, φ' m = PadicInt.toZModPow r y * φ (x • m)) → ι φ' = (algebraMap ℤ_[l] O y * x) • ι φ := by
  intro l _ O _ _ _ _ _ a ha r M _ _ _ hM
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨φ₀, hker, hsurj⟩ := UpperTheory.V.X.So.dualGen l O a ha r M hM
  obtain ⟨w, hw⟩ := (UpperTheory.V.ML.qoCyc l O).2.1 a ha
  choose c hc using hsurj
  have key : ∀ x x' : O, (∀ m : M, φ₀ (x • m) = φ₀ (x' • m)) → x • w = x' • w := by
    intro x x' h
    have hd : a ∣ x - x' := (hker _).1 (fun m => by rw [sub_smul, map_sub, h, sub_self])
    have h0 := (hw (x - x')).2 hd
    rwa [sub_smul, sub_eq_zero] at h0
  have kill : ∀ (s : O) (n : M), ((l : O) ^ r * s) • n = 0 := by
    intro s n
    rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)),
      ZMod.natCast_self, zero_smul]
  have scal : ∀ (y : ℤ_[l]) (n : M),
      φ₀ (algebraMap ℤ_[l] O y • n) = PadicInt.toZModPow r y * φ₀ n := by
    intro y n
    have hmem : y - ((PadicInt.toZModPow r y).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    obtain ⟨t, ht⟩ := hmem
    have hy : y = ((PadicInt.toZModPow r y).val : ℤ_[l]) + (l : ℤ_[l]) ^ r * t := by
      rw [← ht]; ring
    conv_lhs => rw [hy]
    rw [map_add, map_mul, map_pow, map_natCast, map_natCast, add_smul, kill, add_zero,
      Nat.cast_smul_eq_nsmul O, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  refine ⟨{ toFun := fun φ => c φ • w, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩
  · show c 0 • w = 0
    rw [← zero_smul O w]
    apply key
    intro m
    rw [← hc, zero_smul, map_zero]
    rfl
  · intro φ ψ
    show c (φ + ψ) • w = c φ • w + c ψ • w
    rw [← add_smul]
    apply key
    intro m
    have e1 := hc (φ + ψ) m
    have e2 := hc φ m
    have e3 := hc ψ m
    rw [add_smul, map_add, ← e1, ← e2, ← e3]
    exact TDual.add_apply φ ψ m
  · rw [injective_iff_map_eq_zero]
    intro φ hφ
    change c φ • w = 0 at hφ
    have hd := (hw _).1 hφ
    apply LinearMap.ext
    intro m
    rw [hc φ m, (hker _).2 hd m]
    rfl
  · intro v
    constructor
    · intro hv
      obtain ⟨y, rfl⟩ := (UpperTheory.V.ML.qoCyc l O).2.2.1 a w ha hw v hv
      refine ⟨(φ₀.toAddMonoidHom.comp (DistribMulAction.toAddMonoidHom M y)).toZModLinearMap (l ^ r), ?_⟩
      show c _ • w = y • w
      apply key
      intro m
      rw [← hc]
      rfl
    · rintro ⟨φ, rfl⟩
      show a • (c φ • w) = 0
      rw [smul_smul]
      exact (hw _).2 (dvd_mul_right a _)
  · intro y x φ φ' h
    show c φ' • w = (algebraMap ℤ_[l] O y * x) • (c φ • w)
    rw [smul_smul]
    apply key
    intro m
    have e1 := hc φ' m
    have e2 := hc φ (x • m)
    rw [← e1]
    refine (h m).trans ((congrArg (fun z => PadicInt.toZModPow r y * z) e2).trans ?_)
    rw [smul_smul,
      show algebraMap ℤ_[l] O y * x * c φ = algebraMap ℤ_[l] O y * (c φ * x) by ring,
      mul_smul (algebraMap ℤ_[l] O y), scal]
