import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIsEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimAddEqOfTrBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CDimAlg

theorem trdeg_lt_aleph0_of_essFiniteType (F W : Type) [Field F] [CommRing W] [IsDomain W] [Algebra F W]
    [Algebra.EssFiniteType F W] : Algebra.trdeg F W < Cardinal.aleph0 := by
  set W₀ := Algebra.EssFiniteType.subalgebra F W
  haveI : FaithfulSMul W₀ W := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic W₀ W := IsLocalization.isAlgebraic W (Algebra.EssFiniteType.submonoid F W)
  have h := trdeg_add_eq F W₀ (A := W)
  rw [trdeg_eq_zero (R := W₀) (A := W), add_zero] at h
  rw [← h]
  exact trdeg_lt_aleph0_of_finiteType

theorem exists_nat_of_add_eq {d : WithBot ℕ∞} {n m : ℕ} (h : d + n = m) : ∃ k : ℕ, d = k ∧ k + n = m := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + n : ℕ∞) : WithBot ℕ∞) = ((m : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_inj, top_add] at h'
      exact ENat.top_ne_natCast m h'
    | coe k =>
      refine ⟨k, rfl, ?_⟩
      exact_mod_cast h

end GlobalTheory.CDimAlg

namespace GlobalTheory.CDimAlg

theorem ringKrullDim_add_trdeg_of_isComplAt : ∀ (F W R : Type) [Field F] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R] [IsLocalRing R] (b : F →+* W), b.EssFiniteType → ∀ (I : Type) [Fintype I] (ψ : MvPolynomial I W →+* R), GlobalTheory.TChart.IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) → ∀ bR : F →+* R, (ψ.comp MvPolynomial.C).comp b = bR → ((residue R).comp bR).EssFiniteType ∧ ∀ a t : ℕ, ringKrullDim W = a → (letI := ((residue W).comp b).toAlgebra; Algebra.trdeg F (ResidueField W) = t) → ∃ a' t' : ℕ, ringKrullDim R = a' ∧ (letI := ((residue R).comp bR).toAlgebra; Algebra.trdeg F (ResidueField R) = t') ∧ a' + t' = a + t + Fintype.card I := by
  intro F W R _ _ _ _ _ _ b hb I _ ψ hψ hloc bR hbR
  obtain ⟨hRn, -, hfl, hmap, hres⟩ := hψ
  letI : Algebra F W := b.toAlgebra
  haveI : Algebra.EssFiniteType F W := hb
  haveI : IsNoetherianRing W := Algebra.EssFiniteType.isNoetherianRing F W
  set q : Ideal (MvPolynomial I W) := (maximalIdeal R).comap ψ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime ψ _
  have hmemq : ∀ x, x ∈ q ↔ ¬ IsUnit (ψ x) := fun x => by
    rw [hq, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  have hu : ∀ s : q.primeCompl, IsUnit (ψ s) := fun s => by
    have h := s.2
    rw [Ideal.mem_primeCompl_iff, hmemq, not_not] at h
    exact h
  let ψA : Localization.AtPrime q →+* R := IsLocalization.lift hu
  have hψA' : ∀ x, ψA (algebraMap _ (Localization.AtPrime q) x) = ψ x := fun x => IsLocalization.lift_eq hu x
  have hψA : ψA.comp (algebraMap _ (Localization.AtPrime q)) = ψ := RingHom.ext hψA'
  haveI hlocA : IsLocalHom ψA := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    have e1 := IsLocalization.mk'_spec (Localization.AtPrime q) p s
    have hp : IsUnit (ψ p) := by
      rw [← hψA', ← e1, map_mul, hψA']
      exact hx.mul (hu s)
    have hpq : p ∈ q.primeCompl := by
      rw [Ideal.mem_primeCompl_iff, hmemq, not_not]; exact hp
    have h2 : IsUnit (algebraMap _ (Localization.AtPrime q) p) := IsLocalization.map_units _ ⟨p, hpq⟩
    rw [← e1] at h2
    exact isUnit_of_mul_isUnit_left h2
  letI : Algebra (MvPolynomial I W) R := ψ.toAlgebra
  letI : Algebra (Localization.AtPrime q) R := ψA.toAlgebra
  haveI : IsScalarTower (MvPolynomial I W) (Localization.AtPrime q) R :=
    IsScalarTower.of_algebraMap_eq (fun x => (hψA' x).symm)
  haveI : Module.Flat (MvPolynomial I W) R := hfl
  haveI : Module.Flat (Localization.AtPrime q) R :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime q) q.primeCompl R).2 inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  haveI : IsNoetherianRing R := hRn
  haveI : IsLocalHom (algebraMap (Localization.AtPrime q) R) := hlocA
  have hmA : (maximalIdeal (Localization.AtPrime q)).map (algebraMap (Localization.AtPrime q) R) = maximalIdeal R := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    change q.map (ψA.comp (algebraMap _ (Localization.AtPrime q))) = _
    rw [hψA]; exact hmap
  have hdim : ringKrullDim (Localization.AtPrime q) = ringKrullDim R :=
    GlobalTheory.RegSmooth.ringKrullDim_eq_of_flat_of_map_maximalIdeal hmA

  let κ : ResidueField (Localization.AtPrime q) →+* ResidueField R := ResidueField.map ψA
  have hκs : Function.Surjective κ := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    obtain ⟨a, c, hc, hr⟩ := hres r
    have hcq : c ∈ q.primeCompl := by rw [Ideal.mem_primeCompl_iff, hmemq, not_not]; exact hc
    refine ⟨residue _ (IsLocalization.mk' (Localization.AtPrime q) a ⟨c, hcq⟩), ?_⟩
    have e1 : ψA (IsLocalization.mk' (Localization.AtPrime q) a ⟨c, hcq⟩) * ψ c = ψ a := by
      rw [← hψA' c, ← map_mul, IsLocalization.mk'_spec, hψA']
    have e2 : residue R (r * ψ c) = residue R (ψ a) := Ideal.Quotient.eq.2 hr
    have hne : residue R (ψ c) ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hc
    change residue R (ψA _) = residue R r
    refine mul_right_cancel₀ hne ?_
    rw [← map_mul, e1, ← e2, map_mul]
  let e : ResidueField (Localization.AtPrime q) ≃+* ResidueField R := RingEquiv.ofBijective κ ⟨κ.injective, hκs⟩
  have hcomp : ∀ x : F, e (residue _ (algebraMap F (Localization.AtPrime q) x)) = residue R (bR x) := by
    intro x
    change residue R (ψA _) = _
    rw [IsScalarTower.algebraMap_apply F (MvPolynomial I W) (Localization.AtPrime q), hψA', ← hbR]
    rfl
  haveI : Algebra.EssFiniteType F (MvPolynomial I W) := Algebra.EssFiniteType.comp F W _
  haveI : Algebra.EssFiniteType (MvPolynomial I W) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_isLocalization _ q.primeCompl
  haveI hAft : Algebra.EssFiniteType F (Localization.AtPrime q) :=
    Algebra.EssFiniteType.comp F (MvPolynomial I W) _
  have hresA : ((residue (Localization.AtPrime q)).comp (algebraMap F (Localization.AtPrime q))).EssFiniteType :=
    RingHom.EssFiniteType.comp (RingHom.essFiniteType_algebraMap.2 hAft)
      (RingHom.FiniteType.of_surjective _ residue_surjective).essFiniteType
  have hRe : (residue R).comp bR =
      e.toRingHom.comp ((residue (Localization.AtPrime q)).comp (algebraMap F (Localization.AtPrime q))) :=
    RingHom.ext fun x => (hcomp x).symm
  refine ⟨?_, ?_⟩
  · rw [hRe]
    exact RingHom.EssFiniteType.comp hresA (RingHom.FiniteType.of_surjective _ e.surjective).essFiniteType
  intro a t ha ht

  obtain ⟨mW, hmW⟩ : ∃ m : ℕ, Algebra.trdeg F W = m :=
    Cardinal.lt_aleph0.1 (trdeg_lt_aleph0_of_essFiniteType F W)
  have hW : ringKrullDim W + t = mW := by
    letI : Algebra F (ResidueField W) := ((residue W).comp b).toAlgebra
    haveI : IsScalarTower F W (ResidueField W) := IsScalarTower.of_algebraMap_eq' rfl
    exact GlobalTheory.LocModelDim.ringKrullDim_add_trdeg (k := F) (R := W) (Ω := ResidueField W) residue_surjective ht hmW

  haveI : FaithfulSMul F W := (faithfulSMul_iff_algebraMap_injective _ _).2 b.injective
  haveI : FaithfulSMul W (MvPolynomial I W) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective I W)
  have hP : Algebra.trdeg F (MvPolynomial I W) = ((mW + Fintype.card I : ℕ) : Cardinal) := by
    rw [← trdeg_add_eq F W (A := MvPolynomial I W), MvPolynomial.trdeg_of_isDomain, hmW, Cardinal.lift_id,
      Cardinal.mk_fintype]
    push_cast; rfl
  haveI : FaithfulSMul (MvPolynomial I W) (Localization.AtPrime q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors)
  haveI : Algebra.IsAlgebraic (MvPolynomial I W) (Localization.AtPrime q) :=
    IsLocalization.isAlgebraic _ q.primeCompl
  have hA : Algebra.trdeg F (Localization.AtPrime q) = ((mW + Fintype.card I : ℕ) : Cardinal) := by
    rw [← trdeg_add_eq F (MvPolynomial I W) (A := Localization.AtPrime q),
      trdeg_eq_zero (R := MvPolynomial I W) (A := Localization.AtPrime q), add_zero, hP]

  letI alA : Algebra F (ResidueField (Localization.AtPrime q)) :=
    ((residue (Localization.AtPrime q)).comp (algebraMap F (Localization.AtPrime q))).toAlgebra
  haveI : IsScalarTower F (Localization.AtPrime q) (ResidueField (Localization.AtPrime q)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType F (ResidueField (Localization.AtPrime q)) := hresA
  obtain ⟨tA, htA⟩ : ∃ m : ℕ, Algebra.trdeg F (ResidueField (Localization.AtPrime q)) = m :=
    Cardinal.lt_aleph0.1 (trdeg_lt_aleph0 F (ResidueField (Localization.AtPrime q)))
  have hAf := GlobalTheory.LocModelDim.ringKrullDim_add_trdeg (k := F) (R := Localization.AtPrime q)
    (Ω := ResidueField (Localization.AtPrime q)) residue_surjective htA hA
  obtain ⟨k, hk, hkt⟩ := exists_nat_of_add_eq hAf
  letI alR : Algebra F (ResidueField R) := ((residue R).comp bR).toAlgebra
  let eA : ResidueField (Localization.AtPrime q) ≃ₐ[F] ResidueField R := { e with commutes' := fun x => hcomp x }
  refine ⟨k, tA, by rw [← hdim, hk], by rw [← eA.trdeg_eq, htA], ?_⟩
  obtain ⟨a0, ha0, ha0t⟩ := exists_nat_of_add_eq hW
  rw [ha] at ha0
  have : a = a0 := by exact_mod_cast ha0
  omega

end GlobalTheory.CDimAlg
