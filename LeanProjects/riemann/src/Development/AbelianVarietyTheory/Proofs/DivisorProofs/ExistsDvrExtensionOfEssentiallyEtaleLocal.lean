import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

open TensorProduct IsLocalRing

namespace GlobalTheory

theorem tensorLift_injective_of_flat {R S A K L : Type} [CommRing R] [CommRing S] [IsDomain S]
    [CommRing A] [Field K] [Field L] [Algebra R S] [Module.Flat R S] [Algebra R A] [Algebra R K]
    [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] (i : A →ₐ[R] K)
    (hi : Function.Injective i) (f : K →+* L)
    (hf : ∀ r, f (algebraMap R K r) = algebraMap S L (algebraMap R S r)) (g : A ⊗[R] S →+* L)
    (hg : ∀ a s, g (a ⊗ₜ s) = f (i a) * algebraMap S L s) : Function.Injective g := by
  letI : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  let fK : K →ₐ[R] L := { toRingHom := f, commutes' := hf }
  let H : K ⊗[R] S →ₐ[R] L :=
    Algebra.TensorProduct.lift fK (IsScalarTower.toAlgHom R S L) (fun _ _ => Commute.all _ _)
  have hH : ∀ k s, H (k ⊗ₜ s) = f k * algebraMap S L s := fun k s => by
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hgH : ∀ x, g x = H (LinearMap.rTensor S i.toLinearMap x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a s => rw [hg, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, hH]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hloc : IsLocalizedModule (nonZeroDivisors R) (TensorProduct.mk R K S 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).mpr (TensorProduct.isBaseChange R S K)
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  have hHinj : Function.Injective H := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨s, r⟩, hr⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R K S 1) y
    have hs : s = 0 := by
      have h1 : H (r • y) = 0 := by
        rw [Submonoid.smul_def, show H (r.1 • y) = r.1 • H y from H.toLinearMap.map_smul r.1 y, hy, smul_zero]
      rw [hr, TensorProduct.mk_apply, hH, map_one, one_mul] at h1
      exact IsFractionRing.injective S L (h1.trans (map_zero _).symm)
    have ha : algebraMap R K r.1 ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2
    have h2 : algebraMap R K r.1 • y = 0 := by
      rw [algebraMap_smul, ← Submonoid.smul_def, hr, hs, TensorProduct.mk_apply, TensorProduct.tmul_zero]
    rw [← one_smul K y, ← inv_mul_cancel₀ ha, mul_smul, h2, smul_zero]
  intro x y hxy
  rw [hgH, hgH] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := S) i.toLinearMap hi (hHinj hxy)

def rangeValuationSubring {B L : Type} [CommRing B] [IsDomain B] [ValuationRing B] [Field L]
    (j : B →+* L) (hj : ∀ x : L, ∃ a b : B, j b ≠ 0 ∧ x = j a / j b) : ValuationSubring L where
  toSubring := j.range
  mem_or_inv_mem' x := by
    obtain ⟨a, b, hb, rfl⟩ := hj x
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
    · right
      have ha : j a ≠ 0 := fun h => hb (by rw [← hc, map_mul, h, zero_mul])
      exact ⟨c, by rw [inv_div, ← hc, map_mul, mul_div_cancel_left₀ _ ha]⟩
    · left
      exact ⟨c, by rw [← hc, map_mul, mul_div_cancel_left₀ _ hb]⟩

theorem exists_valuationSubring_extend_of_formallyEtale : ∀ {K K' R S : Type} [Field K] [Field K']
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S] [Algebra R K]
    [Algebra S K'] [IsFractionRing R K] [IsFractionRing S K'] (φ : K →+* K') (σ : R →+* S)
    [IsLocalHom σ], σ.Flat → σ.FormallyEtale → σ.EssFiniteType →
    φ.comp (algebraMap R K) = (algebraMap S K').comp σ → ∀ V : ValuationSubring K,
    IsDiscreteValuationRing V → (∀ a, algebraMap R K a ∈ V) →
    ∃ (V' : ValuationSubring K') (h : ∀ x ∈ V, φ x ∈ V'), IsDiscreteValuationRing V' ∧
      (∀ b, algebraMap S K' b ∈ V') ∧ (∀ x, φ x ∈ V' → x ∈ V) ∧
      (φ.restrict V V' h).FormallyEtale ∧ (φ.restrict V V' h).EssFiniteType := by
  intro K K' R S _ _ _ _ _ _ _ _ _ _ _ _ φ σ _ hfl het hef hc V hV hRV
  letI : Algebra R S := σ.toAlgebra
  haveI : Module.Flat R S := hfl
  haveI : Algebra.FormallyEtale R S := het
  haveI : Algebra.EssFiniteType R S := hef
  haveI : IsLocalHom (algebraMap R S) := ‹IsLocalHom σ›
  haveI : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  letI : Algebra R V := ((algebraMap R K).codRestrict V hRV).toAlgebra
  letI : Algebra R K' := ((algebraMap S K').comp σ).toAlgebra
  haveI : IsScalarTower R S K' := .of_algebraMap_eq fun _ => rfl
  let fV : V →ₐ[R] K' := { toRingHom := φ.comp V.subtype, commutes' := fun r => RingHom.congr_fun hc r }
  let iV : V →ₐ[R] K := { toRingHom := V.subtype, commutes' := fun _ => rfl }
  let g : V ⊗[R] S →ₐ[R] K' :=
    Algebra.TensorProduct.lift fV (IsScalarTower.toAlgHom R S K') (fun _ _ => Commute.all _ _)
  have hg' : ∀ (a : V) (s : S), g (a ⊗ₜ s) = φ a * algebraMap S K' s := fun a s => by
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hg1 : ∀ s : S, g (1 ⊗ₜ s) = algebraMap S K' s := fun s => by
    rw [hg']; simp
  have hg : Function.Injective g :=
    tensorLift_injective_of_flat (S := S) (L := K') iV Subtype.val_injective φ (RingHom.congr_fun hc) g.toRingHom hg'
  let C := V ⊗[R] S
  haveI : IsDomain C := Function.Injective.isDomain g.toRingHom hg
  obtain ⟨⟨Q, hQ⟩, hQm⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := V) (B := C)
    ⟨maximalIdeal V, inferInstance⟩
  have hQm' : Q.comap (algebraMap V C) = maximalIdeal V := congrArg PrimeSpectrum.asIdeal hQm
  let B := Localization.AtPrime Q
  haveI : Module.Flat V B := Module.Flat.trans V C B
  haveI : Algebra.EssFiniteType V B := .comp V C B
  haveI : Algebra.FormallyEtale V B := .comp V C B
  have hQB : ∀ c : C, IsUnit (algebraMap C B c) ↔ c ∉ Q := fun c =>
    IsLocalization.AtPrime.isUnit_to_map_iff B Q c
  haveI : IsLocalHom (algebraMap V B) := ⟨fun v hv => by
    by_contra hn
    have h1 : algebraMap V C v ∈ Q := by rw [← Ideal.mem_comap, hQm']; exact hn
    rw [IsScalarTower.algebraMap_apply V C B] at hv
    exact (hQB _).mp hv h1⟩
  obtain ⟨_, hB⟩ := exists_isDiscreteValuationRing_of_unramified V B
  have hunit : ∀ y : Q.primeCompl, IsUnit (g.toRingHom y) := fun y => by
    refine Ne.isUnit fun h0 => y.2 ?_
    rw [hg (h0.trans (map_zero g).symm)]
    exact Q.zero_mem
  let j : B →+* K' := IsLocalization.lift (M := Q.primeCompl) (S := B) hunit
  have hjC : ∀ c, j (algebraMap C B c) = g c := IsLocalization.lift_eq (M := Q.primeCompl) (S := B) hunit
  have hj : Function.Injective j := IsLocalization.injective_of_map_algebraMap_zero (M := Q.primeCompl) B j fun x hx => by
    rw [hjC] at hx
    rw [hg (hx.trans (map_zero g).symm), map_zero]
  have hgen : ∀ x : K', ∃ a b : B, j b ≠ 0 ∧ x = j a / j b := fun x => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    refine ⟨algebraMap C B (1 ⊗ₜ a), algebraMap C B (1 ⊗ₜ b), ?_, ?_⟩
    · rw [hjC, hg1]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    · rw [hjC, hjC, hg1, hg1]
  let V' := rangeValuationSubring j hgen
  have hVV' : ∀ x ∈ V, φ x ∈ V' := fun x hx =>
    ⟨algebraMap C B (⟨x, hx⟩ ⊗ₜ 1), by rw [hjC, hg', map_one, mul_one]⟩
  let e₀ : B →+* V' := j.codRestrict V' fun b => ⟨b, rfl⟩
  have he₀ : Function.Bijective e₀ :=
    ⟨fun a b h => hj (congrArg Subtype.val h), fun y => by
      obtain ⟨b, hb⟩ := y.2
      exact ⟨b, Subtype.ext hb⟩⟩
  let e : B ≃+* V' := RingEquiv.ofBijective e₀ he₀
  have he : ∀ b, (e b : K') = j b := fun _ => rfl
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  have htQ : algebraMap V C t ∈ Q := by
    rw [← Ideal.mem_comap, hQm']
    exact (mem_maximalIdeal _).mpr ht.not_isUnit
  have htB : ¬ IsUnit (algebraMap C B (algebraMap V C t)) := fun h => (hQB _).mp h htQ
  have hφt : φ t ≠ 0 := by
    rw [map_ne_zero]
    exact fun h => ht.ne_zero (Subtype.ext h)
  have hjt : j (algebraMap C B (algebraMap V C t)) = φ t := by
    rw [hjC, Algebra.TensorProduct.algebraMap_apply, hg']
    simp
  have key : (φ t)⁻¹ ∉ V' := by
    rintro ⟨b, hb⟩
    refine htB (IsUnit.of_mul_eq_one b (hj ?_))
    rw [map_mul, hb, map_one, hjt, mul_inv_cancel₀ hφt]
  refine ⟨V', hVV', ?_, fun b => ⟨algebraMap C B (1 ⊗ₜ b), by rw [hjC, hg1]⟩, ?_, ?_⟩
  · obtain ⟨b, hbm, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (IsDiscreteValuationRing.not_a_field B)
    exact
      { toIsPrincipalIdealRing := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
        toIsLocalRing := inferInstance
        not_a_field' := fun h => by
          have h1 : e b ∈ maximalIdeal V' := fun hu => hbm (by simpa using hu.map e.symm.toRingHom)
          rw [h] at h1
          exact hb0 (e.injective (by simpa using h1)) }
  · intro x hx
    by_contra hxV
    have hinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
    have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨x⁻¹, hinv⟩ : V)) (fun h => inv_ne_zero hx0 (congrArg Subtype.val h)) ht
    have hn' : x⁻¹ = (u : K) * (t : K) ^ n := congrArg Subtype.val hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => hxV ?_)
      have h2 : ((u : V) : K) * (((u⁻¹ : Vˣ) : V) : K) = 1 := by
        exact_mod_cast congrArg Subtype.val u.mul_inv
      have hn0 : x⁻¹ = (u : K) := by rw [hn', h0, pow_zero, mul_one]
      have : x = (((u⁻¹ : Vˣ) : V) : K) := by
        rw [← inv_inv x, hn0]
        exact inv_eq_of_mul_eq_one_right h2
      exact this ▸ Subtype.property _
    apply key
    have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
    have : (φ t)⁻¹ = φ ((t ^ m * u : V) : K) * φ x := by
      rw [← map_inv₀, ← map_mul]
      congr 1
      have hu0 : ((u : V) : K) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
      have hx' : x = ((u : K) * (t : K) ^ (m + 1))⁻¹ := by rw [← hn', inv_inv]
      rw [hx']
      push_cast
      field_simp
      ring
    rw [this]
    exact mul_mem (hVV' _ (t ^ m * u : V).2) hx
  · letI : Algebra V V' := (φ.restrict V V' hVV').toAlgebra
    let eA : B ≃ₐ[V] V' := AlgEquiv.ofRingEquiv (f := e) fun v => Subtype.ext (by
      rw [he, IsScalarTower.algebraMap_apply V C B, hjC, Algebra.TensorProduct.algebraMap_apply,
        hg']
      simp
      rfl)
    exact ⟨Algebra.FormallyEtale.of_equiv eA, Algebra.EssFiniteType.of_surjective eA.toAlgHom eA.surjective⟩

end GlobalTheory
