import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.DyadicCharacterPowerNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual

private theorem vanish_zmod (hTD : LocalTateDuality) (hEC : LocalEulerChar) (F Ω : Type) [Field F] [NumberField F]
    [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (rho : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M)
    (hA : IsPlaceOver A v) (hrho : ContAction rho) (γ : Dec (F := F) A) (hχ0 : cycMod F Ω l 1 γ = 1)
    (hγ : Function.Bijective fun m : M => rho γ m - m) :
    Subsingleton (H2 rho) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Subsingleton (H1 rho)) := by
  have h0 : H0 rho = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro m hm
    have h1 : rho γ m = m := (Representation.mem_invariants rho m).mp hm γ
    apply hγ.1
    show rho γ m - m = rho γ 0 - 0
    rw [h1, map_zero, sub_self, sub_self]
  set χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype with hχdef
  have hχ : χ γ = 1 := hχ0
  have hdual : Subsingleton (H0 ((twDual χ rho).comp (MonoidHom.id _))) := by
    have key : ∀ φ ∈ H0 ((twDual χ rho).comp (MonoidHom.id _)), φ = 0 := by
      intro φ hφ
      have h1 : twDual χ rho γ φ = φ := (Representation.mem_invariants _ φ).mp hφ γ
      ext x
      obtain ⟨m, rfl⟩ := hγ.2 x
      have h3 := congrArg (fun ψ : TDual (ZMod (l ^ 1)) M => ψ (rho γ m)) h1
      simp only [twDual_apply, hχ, Units.val_one, one_mul] at h3
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h3
      show φ (rho γ m - m) = 0
      exact (LinearMap.map_sub (φ : Module.Dual (ZMod (l ^ 1)) M) (rho γ m) m).trans (sub_eq_zero.mpr h3.symm)
    refine ⟨fun a b => ?_⟩
    exact Subtype.ext ((key a.1 a.2).trans (key b.1 b.2).symm)
  have hTD' := hTD F Ω l 1 M A rho v Nat.one_pos hA hrho
  have hinj := hTD'.2.2.2.2.1
  have h2 : Subsingleton (H2 rho) := by
    refine ⟨fun x y => hinj ?_⟩
    ext z
    rw [Subsingleton.elim z 0, map_zero, map_zero]
  refine ⟨h2, fun hl => ?_⟩
  have hc0 : Nat.card (H0 rho) = 1 := by
    rw [h0]; exact Nat.card_unique
  have hc2 : Nat.card (H2 rho) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨h2, ⟨0⟩⟩
  have he := (hEC F Ω l 1 M A rho v Nat.one_pos hA hrho).2 hl
  have hc1 : Nat.card (H1 rho) = 1 := by rw [he, hc0, hc2]
  exact (Nat.card_eq_one_iff_unique.mp hc1).1

private theorem vanish_k (hTD : LocalTateDuality) (hEC : LocalEulerChar) (F Ω : Type) [Field F] [NumberField F]
    [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k] [CharP k l]
    (M : Type) [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousConstSMul k M] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (D : Subgroup (G F Ω)) (hD : D = Dec (F := F) A) (rho : Representation k D M)
    (hA : IsPlaceOver A v) (hrho : ContAction rho) (γ : D) (hχ0 : cycMod F Ω l 1 γ = 1)
    (hγ : Function.Bijective fun m : M => rho γ m - m) :
    Subsingleton (H2 rho) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Subsingleton (H1 rho)) := by
  subst hD
  haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance
  letI : Module (ZMod (l ^ 1)) M := Module.compHom _ (ZMod.castHom (dvd_refl _) k)
  haveI : ContinuousConstSMul (ZMod (l ^ 1)) M := ⟨fun _ => continuous_of_discreteTopology⟩
  let rho' : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M :=
    { toFun := fun g =>
        { toFun := rho g
          map_add' := map_add (rho g)
          map_smul' := fun c m => map_smul (rho g) (ZMod.castHom (dvd_refl _) k c) m }
      map_one' := LinearMap.ext fun m => show rho 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show rho (g * h) m = rho g (rho h m) by
        rw [map_mul]; rfl }
  have h := vanish_zmod hTD hEC F Ω l M A v rho' hA hrho γ hχ0 hγ
  refine ⟨?_, fun hl => ?_⟩
  · have h2 := Submodule.Quotient.subsingleton_iff.1 h.1
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    rintro ⟨f, hf⟩ -
    show f ∈ B2 _
    have hf' : f ∈ Z2 rho' := hf
    have hB : (⟨f, hf'⟩ : Z2 rho') ∈ (B2 rho').comap (Z2 rho').subtype := h2 ▸ Submodule.mem_top
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho' _).1 hB
    exact (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, hcf⟩
  · have h1 := Submodule.Quotient.subsingleton_iff.1 (h.2 hl)
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    rintro ⟨f, hf⟩ -
    show f ∈ B1 _
    have hf' : f ∈ Z1 rho' := hf
    have hB : (⟨f, hf'⟩ : Z1 rho') ∈ (B1 rho').comap (Z1 rho').subtype := h1 ▸ Submodule.mem_top
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho' _).1 hB
    exact (mem_coboundaries1 _ _).2 ⟨m, hm⟩

private theorem gb_ext {k : Type} [CommRing k] {j : ℤ} {X Y : Gb k j} (h : X.val = Y.val) : X = Y :=
  Subtype.ext h

private theorem gb_finite (k : Type) [CommRing k] [Finite k] (j : ℤ) : Finite (Gb k j) :=
  Finite.of_injective (fun X : Gb k j => X.val) fun _ _ h => gb_ext h

private theorem gRep_bij {k D : Type} [Field k] [Finite k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) {j : ℤ}
    (hj : j ≠ 0) (x : D) (hη : η x = 1) (hΨ : Ψ x ^ 2 ≠ 1) :
    Function.Bijective fun m : Gb k j => gRep η Ψ j x m - m := by
  haveI := gb_finite k j
  rw [← Finite.injective_iff_bijective]
  have h1 : Ψ x ≠ 1 := fun h => hΨ (by rw [h, one_pow])
  have hker : ∀ m : Gb k j, gRep η Ψ j x m = m → m = 0 := by
    intro m hm
    apply gb_ext
    ext a b
    show m.val a b = 0
    by_cases hab : wt a b = j
    · have e := congrArg (fun X : Gb k j => X.val a b) hm
      simp only [gRep_val, adRep_baseLift_apply, hη, if_true] at e
      have hne : (Ψ x ^ wt a b : kˣ) ≠ 1 := by
        have h0 : wt a b ≠ 0 := hab ▸ hj
        have hw : wt a b = 1 ∨ wt a b = 2 ∨ wt a b = -1 ∨ wt a b = -2 := by
          revert h0
          fin_cases a <;> fin_cases b <;> simp [wt, wt1]
        rcases hw with h | h | h | h <;> rw [h]
        · simpa using h1
        · exact_mod_cast hΨ
        · simpa using h1
        · rw [_root_.zpow_neg, Ne, inv_eq_one]; exact_mod_cast hΨ
      have e' : (((Ψ x ^ wt a b : kˣ) : k) - 1) * m.val a b = 0 := by rw [sub_mul, e, one_mul, sub_self]
      rcases mul_eq_zero.1 e' with h | h
      · exact absurd (Units.ext (sub_eq_zero.1 h)) hne
      · exact h
    · exact Subtype.property (p := fun X => X ∈ gw k j) m a b hab
  intro m m' h
  have h' : gRep η Ψ j x m - m = gRep η Ψ j x m' - m' := h
  refine sub_eq_zero.1 (hker _ ?_)
  rw [map_sub, sub_eq_sub_iff_sub_eq_sub]
  exact h'

private theorem gRep_cont {k D D' : Type} [CommRing k] [Group D] [TopologicalSpace D] [Group D']
    [TopologicalSpace D'] (η : D →* ℤˣ) (Ψ : D →* kˣ) (j : ℤ) (hη : IsLocallyConstant η) (hΨ : IsLocallyConstant Ψ)
    (φ : D' →* D) (hφ : Continuous φ) : ContAction (G := D') ((gRep η Ψ j).comp φ) := by
  unfold ReciprocityTheory.Gal.ContAction
  apply IsLocallyConstant.continuous
  have h1 : IsLocallyConstant fun p : D' × Gb k j => ((η (φ p.1), Ψ (φ p.1)), p.2) :=
    ((hη.comp_continuous (hφ.comp continuous_fst)).prodMk (hΨ.comp_continuous (hφ.comp continuous_fst))).prodMk
      ((IsLocallyConstant.iff_continuous _).2 continuous_snd)
  rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
  intro p
  filter_upwards [h1 p] with q hq
  simp only [Prod.mk.injEq] at hq
  apply gb_ext
  ext a b
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, gRep_val, gRep_val, adRep_baseLift_apply, adRep_baseLift_apply, hq.1.1, hq.1.2, hq.2]

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.hostFrame_locVan :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    F.LocVan := by
  intro _ hTD hEC Ω _ _ _ l hl c N _ e ψ o₁ hd S A F hF
  have hok := hostFrame_ok Ω c e ψ o₁ hd S A F hF
  have hx := exists_sigma Ω c e ψ o₁ hd S A F hF
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  have hΨ : IsLocallyConstant F.Ψbar := by
    have h1 := (hok.Ψ_cont 1)
    rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
    intro g
    filter_upwards [h1 g] with g' hg
    apply Units.ext
    show residue c.O (F.Ψ g') = residue c.O (F.Ψ g)
    rw [Ideal.Quotient.eq, pow_one] at hg
    exact Ideal.Quotient.eq.2 hg
  have key : ∀ v ∈ F.Tb, ∀ j ≠ 0, Subsingleton (H2 (F.gloc j v)) ∧
      (((l : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.1.asIdeal → Subsingleton (H1 (F.gloc j v))) := by
    intro v hv j hj
    obtain ⟨x, hη, hu, hc⟩ := hx v hv
    haveI := gb_finite (ResidueField c.O) j
    have hloc : Continuous (F.loc v) := hok.π_cont.comp continuous_subtype_val
    have hcont : ContAction (F.gloc j v) :=
      gRep_cont F.η F.Ψbar j hok.η_cont hΨ (F.loc v) hloc
    refine vanish_k hTD hEC ℚ Ω l (ResidueField c.O) _ (A v) v.1 (F.D v) (hF.D v) (F.gloc j v) (hF.isOver v)
      hcont x hc (gRep_bij F.η F.Ψbar hj (F.loc v x) hη fun h => ?_)
    have h2 := (hu.map (residue c.O)).ne_zero
    apply h2
    rw [map_sub, map_pow, map_one, sub_eq_zero]
    exact congrArg Units.val h
  refine ⟨fun v hv j hj => (key v hv j hj).1, fun v hv j hj => (key v (Set.mem_insert_of_mem _ hv) j hj).2 ?_⟩
  obtain ⟨p, hp, hpv⟩ := (hF.Sb v).1 hv
  intro hlv
  simp only [HV.Sb, Finset.mem_filter] at hp
  have hcop : Nat.Coprime p l := (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp.1) hl.out).2 hp.2.1
  obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := NumberField.RingOfIntegers ℚ) hcop)
  exact v.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (Ideal.mul_mem_left _ _ hpv) (Ideal.mul_mem_left _ _ hlv)))
