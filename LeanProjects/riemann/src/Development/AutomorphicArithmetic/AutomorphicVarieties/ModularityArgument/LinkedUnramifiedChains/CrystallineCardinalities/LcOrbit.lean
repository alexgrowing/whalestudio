import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualZ

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V

private theorem cardZ {k D M : Type} [CommRing k] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M] (σ : Representation k D M) (hσ : ContAction σ)
    [Finite (H1 σ)] : Finite (Z1 σ) ∧ Nat.card (Z1 σ) * Nat.card (H0 σ) = Nat.card (H1 σ) * Nat.card M := by
  set B := Submodule.comap (Z1 σ).subtype (B1 σ) with hB
  have hBZ : B1 σ ≤ Z1 σ := by
    rintro f ⟨m, rfl⟩
    have hfun : (d0 σ m : D → M) = fun g => σ g m - m := funext fun g => amitsur_d0_apply σ m g
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact (hσ.comp (Continuous.prodMk continuous_id continuous_const)).sub continuous_const
    · intro g h
      rw [amitsur_d0_apply, amitsur_d0_apply, amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have hker : LinearMap.ker (d0 σ) = H0 σ := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp [amitsur_d0_apply, sub_eq_zero]
  have hM : Nat.card M = Nat.card (H0 σ) * Nat.card (B1 σ) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d0 σ)),
      Nat.card_congr (d0 σ).quotKerEquivRange.toEquiv, hker]
    rfl
  have hZ : Nat.card (Z1 σ) = Nat.card B * Nat.card (H1 σ) := Submodule.card_eq_card_quotient_mul_card B
  have hBc : Nat.card B = Nat.card (B1 σ) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hBZ).toEquiv
  haveI : Finite (B1 σ) := by
    show Finite (LinearMap.range (d0 σ))
    exact Finite.of_surjective (d0 σ).rangeRestrict (LinearMap.surjective_rangeRestrict _)
  have hB1pos : 0 < Nat.card (B1 σ) := Nat.card_pos
  have hH1pos : 0 < Nat.card (H1 σ) := Nat.card_pos
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hZ, hBc]
    positivity
  · rw [hZ, hBc, hM]
    ring

private def zRep (n : ℕ) {D M : Type} [Group D] [AddCommGroup M] [Module (ZMod n) M]
    (ρ : Representation ℤ D M) : Representation (ZMod n) D M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul]; rfl

private theorem cardInv {n : ℕ} {D M : Type} [Group D] [AddCommGroup M] [Module (ZMod n) M] (χ : D →* (ZMod n)ˣ)
    (σ : Representation (ZMod n) D M) :
    Nat.card (H0 ((twDual χ σ).comp (MonoidHom.id D))) =
      Nat.card {f : M →+ ZMod n // ∀ s x, f (σ s x) = χ s * f x} := by
  apply Nat.card_congr
  exact
    { toFun := fun φ => ⟨(φ.1 : M →ₗ[ZMod n] ZMod n).toAddMonoidHom, by
        intro s x
        have h1 := (Representation.mem_invariants _ _).mp φ.2 s
        have h2 := congrArg (fun ψ : TDual (ZMod n) M => ψ (σ s x)) h1
        have hinv : σ s⁻¹ (σ s x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, twDual_apply, hinv] at h2
        exact h2.symm⟩
      invFun := fun f => ⟨f.1.toZModLinearMap n, by
        refine (Representation.mem_invariants _ _).mpr ?_
        intro g
        apply TDual.ext
        intro m
        have h1 := f.2 g (σ g⁻¹ m)
        have hinv : σ g (σ g⁻¹ m) = m := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [hinv] at h1
        exact h1.symm⟩
      left_inv := fun φ => Subtype.ext (TDual.ext fun m => rfl)
      right_inv := fun f => Subtype.ext (AddMonoidHom.ext fun m => rfl) }

private theorem lc_orbit {D M : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M]
    (ρ : Representation ℤ D M) (h : IsOpen (ρ.ker : Set D)) (m : M) : IsLocallyConstant fun g => ρ g m := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun y => g⁻¹ * y) ⁻¹' (ρ.ker : Set D), h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro x hx
    have hk : ρ (g⁻¹ * x) = 1 := MonoidHom.mem_ker.mp hx
    have hx' : x = g * (g⁻¹ * x) := by group
    rw [hx', map_mul, Module.End.mul_apply, hk, Module.End.one_apply]

theorem UpperTheory.V.Z.J.leOf :
    ReciprocityTheory.Gal.LocalFiniteness → ReciprocityTheory.Gal.LocalTateDuality → ReciprocityTheory.Gal.LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), IsPlaceOver A v → ((l : ℕ) : NumberField.RingOfIntegers F) ∈ v.asIdeal → LE l (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) (locDeg v) := by
  intro hFin hTD hEC l _ F Ω _ _ _ _ _ A v hAv hlv
  unfold UpperTheory.V.Z.J.LE
  intro k hk N _ _ ρ hx hker
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  letI : Module (ZMod (l ^ k)) N := AddCommGroup.zmodModule hx
  letI tN : TopologicalSpace N := ⊥
  haveI : DiscreteTopology N := ⟨rfl⟩
  let σ : Representation (ZMod (l ^ k)) (Dec (F := F) A) N := zRep (l ^ k) ρ
  have hcont : ContAction σ := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [← IsLocallyConstant.iff_continuous, IsLocallyConstant.iff_exists_open]
    rintro ⟨g, x⟩
    obtain ⟨U, hU, hgU, hUc⟩ := (IsLocallyConstant.iff_exists_open _).mp (lc_orbit ρ hker x) g
    refine ⟨U ×ˢ {x}, hU.prod (isOpen_discrete _), ⟨hgU, rfl⟩, ?_⟩
    rintro ⟨g', x'⟩ ⟨hg', hx'⟩
    simp only [Set.mem_singleton_iff] at hx'
    subst hx'
    exact hUc g' hg'
  obtain ⟨hH0f, hH1f, hH2f, -⟩ := hFin F Ω l k N A σ v hk hAv hcont
  haveI := hH0f
  haveI := hH1f
  haveI := hH2f
  have hec := (hEC F Ω l k N A σ v hk hAv hcont).1 hlv
  obtain ⟨⟨e2⟩, -, -, -, hcup⟩ := hTD F Ω l k N A σ v hk hAv hcont
  obtain ⟨hZf, hZc⟩ := cardZ σ hcont
  haveI := hZf
  haveI hDf : Finite (N →ₗ[ZMod (l ^ k)] ZMod (l ^ k)) :=
    Finite.of_injective _ (LinearMap.coe_injective (R := ZMod (l ^ k)) (M := N) (M₃ := ZMod (l ^ k)))
  haveI hTf : Finite (TDual (ZMod (l ^ k)) N) := hDf
  have e1 := Nat.card_congr ((Equiv.ofBijective _ hcup).trans (by exact (LinearEquiv.congrRight e2).toEquiv))
  have e3 := e1.trans (by exact (Th.dualZ (l ^ k) _).1)
  have h2 := e3.trans (by exact cardInv _ σ)
  have h3 : Nat.card ↑(HomMu l k ((cycZ F Ω l).comp (Dec (F := F) A).subtype) ρ) = Nat.card (H2 σ) :=
    h2.symm
  have hZ : Zc ρ = ((Z1 σ : Submodule _ _) : Set ((Dec (F := F) A) → N)) := by
    ext z
    show (IsLocallyConstant z ∧ _) ↔ (Continuous z ∧ _)
    rw [IsLocallyConstant.iff_continuous]
    rfl
  have key : ∀ {a b c n e d : ℕ}, a * b = c * n → c = b * e * n ^ d → 0 < b → a = n ^ (1 + d) * e := by
    intro a b c n e d h1 h2 hb
    apply Nat.eq_of_mul_eq_mul_right hb
    rw [h1, h2]
    ring
  refine ⟨?_, ?_⟩
  · rw [hZ]
    exact Set.toFinite _
  · rw [hZ, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, h3]
    exact key hZc hec (by exact Nat.card_pos)
