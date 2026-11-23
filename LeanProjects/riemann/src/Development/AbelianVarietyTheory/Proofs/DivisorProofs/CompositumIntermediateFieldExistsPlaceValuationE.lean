import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

open NumberField IsDedekindDomain

namespace GlobalTheory.UnramCompositum

theorem card_inertia (k N : Type) [Field k] [NumberField k] [Field N] [NumberField N]
    [Algebra k N] [IsGalois k N] (Q : Ideal (𝓞 N)) [Q.IsPrime] :
    Nat.card (Q.inertia (N ≃ₐ[k] N)) = Q.ramificationIdx (𝓞 k) := by
  have : IsGaloisGroup (N ≃ₐ[k] N) (𝓞 k) (𝓞 N) := IsGaloisGroup.of_isFractionRing _ _ _ k N
  have hpr : (Q.under (𝓞 k)).IsPrime := Ideal.IsPrime.under _ Q
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[k] N) (Q.under (𝓞 k)) Q
  rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 k)) Q (N ≃ₐ[k] N)] at hcard

theorem ramificationIdx_eq_one_iff_fix (k E N : Type) [Field k] [NumberField k] [Field E] [NumberField E]
    [Field N] [NumberField N] [Algebra k E] [Algebra k N] [Algebra E N] [IsScalarTower k E N] [IsGalois k N]
    (Q : Ideal (𝓞 N)) [Q.IsPrime] :
    (Q.under (𝓞 E)).ramificationIdx (𝓞 k) = 1 ↔
      ∀ τ : N ≃ₐ[k] N, (∀ x : 𝓞 N, τ • x - x ∈ Q) → ∀ y : E, τ (algebraMap E N y) = algebraMap E N y := by
  haveI : IsGalois E N := IsGalois.tower_top_of_isGalois k E N
  have h1 := card_inertia k N Q
  have h2 := card_inertia E N Q
  have h3 : Q.ramificationIdx (𝓞 k) = (Q.under (𝓞 E)).ramificationIdx (𝓞 k) * Q.ramificationIdx (𝓞 E) :=
    Ideal.ramificationIdx_tower (Q.under (𝓞 E)) Q
  have h4 : 0 < Q.ramificationIdx (𝓞 E) := Ideal.ramificationIdx_pos Q (𝓞 E)
  let f : Q.inertia (N ≃ₐ[E] N) → Q.inertia (N ≃ₐ[k] N) := fun σ =>
    ⟨σ.1.restrictScalars k, AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp σ.2 x⟩
  have hf : Function.Injective f := fun σ σ' h =>
    Subtype.ext (AlgEquiv.restrictScalars_injective k (congrArg Subtype.val h))
  constructor
  · intro h τ hτ y
    have hb : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [h1, h2, h3, h, one_mul])
    obtain ⟨σ, hσ⟩ := hb.2 ⟨τ, AddSubgroup.mem_inertia.mpr hτ⟩
    have : σ.1.restrictScalars k = τ := congrArg Subtype.val hσ
    rw [← this]
    exact σ.1.commutes y
  · intro h
    have hs : Function.Surjective f := fun τ =>
      ⟨⟨{ τ.1.toRingEquiv with commutes' := h τ.1 (AddSubgroup.mem_inertia.mp τ.2) },
        AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp τ.2 x⟩, rfl⟩
    have hc := Nat.card_eq_of_bijective f ⟨hf, hs⟩
    rw [h1, h2, h3] at hc
    exact Nat.eq_of_mul_eq_mul_right h4 (by rw [one_mul]; exact hc.symm)

theorem exists_galois_above (K : Type) [Field K] [NumberField K] :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra K N), IsGalois ℚ N := by
  have : IsAlgClosure ℚ (AlgebraicClosure K) := IsAlgClosure.ofAlgebraic ℚ K (AlgebraicClosure K)
  have : IsGalois ℚ (AlgebraicClosure K) := ⟨⟩
  have : NumberField (IntermediateField.normalClosure ℚ K (AlgebraicClosure K)) := ⟨⟩
  exact ⟨IntermediateField.normalClosure ℚ K (AlgebraicClosure K), inferInstance, inferInstance, inferInstance,
    IsGalois.normalClosure ℚ K (AlgebraicClosure K)⟩

theorem exists_valuation_eq (F F' K : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] [Field K]
    [NumberField K] [Algebra F K] [Algebra F' K]
    (hgen : ∀ (N : Type) [Field N] (f g : K →+* N), (∀ x : F, f (algebraMap F K x) = g (algebraMap F K x)) →
      (∀ x : F', f (algebraMap F' K x) = g (algebraMap F' K x)) → f = g)
    (q : ℕ) (hq : q.Prime) (hd : ¬ (q : ℤ) ∣ discr F') (w : HeightOneSpectrum (𝓞 F))
    (hw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ∀ a : F, 𝔭.valuation K (algebraMap F K a) = w.valuation F a := by
  obtain ⟨N, _, _, _, hN⟩ := exists_galois_above K
  letI : Algebra F N := ((algebraMap K N).comp (algebraMap F K)).toAlgebra
  letI : Algebra F' N := ((algebraMap K N).comp (algebraMap F' K)).toAlgebra
  have : IsScalarTower F K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois F N := IsGalois.tower_top_of_isGalois ℚ F N
  have := w.isMaximal
  obtain ⟨Q, hQ, hQw⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) w.asIdeal
  have hqQ : ((q : ℕ) : 𝓞 N) ∈ Q := by
    have := (Ideal.mem_of_liesOver Q w.asIdeal _).1 hw
    rwa [map_natCast] at this
  have hu : Algebra.IsUnramifiedAt ℤ (Q.under (𝓞 F')) :=
    (not_dvd_discr_iff_forall_mem F' (𝓞 F') (Nat.prime_iff_prime_int.1 hq)).1 hd _ inferInstance (by
      rw [Ideal.under, Ideal.mem_comap, map_intCast, Int.cast_natCast]; exact hqQ)
  have hu' : Algebra.IsUnramifiedAt (𝓞 ℚ) (Q.under (𝓞 F')) := Algebra.IsUnramifiedAt.of_restrictScalars ℤ _
  have hfix := (ramificationIdx_eq_one_iff_fix ℚ F' N Q).1 (Ideal.ramificationIdx_eq_one _ _)
  have he : (Q.under (𝓞 K)).ramificationIdx (𝓞 F) = 1 := by
    refine (ramificationIdx_eq_one_iff_fix F K N Q).2 fun τ hτ y => ?_
    exact RingHom.congr_fun (hgen N ((τ : N →+* N).comp (algebraMap K N)) (algebraMap K N)
      (fun x => τ.commutes x) (fun x => hfix (τ.restrictScalars ℚ) hτ x)) y
  have hlo : (Q.under (𝓞 K)).LiesOver w.asIdeal := Ideal.LiesOver.tower_bot Q _ _
  let 𝔭 : HeightOneSpectrum (𝓞 K) :=
    ⟨Q.under (𝓞 K), inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot _⟩
  have hlo' : 𝔭.asIdeal.LiesOver w.asIdeal := hlo
  refine ⟨𝔭, fun a => ?_⟩
  rw [← HeightOneSpectrum.valuation_liesOver K w 𝔭 a,
    Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal 𝔭.asIdeal w.ne_bot]
  change _ ^ (Q.under (𝓞 K)).ramificationIdx (𝓞 F) = _
  rw [he, pow_one]

open Formalism.L2.Pj in

theorem exists_vLa_eq : ∀ (F F' K : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField K]
    (hF : F ≤ K), K = F ⊔ F' → ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ discr F' → ∀ w : HeightOneSpectrum (𝓞 F),
    ((q : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ 𝔭 : HeightOneSpectrum (𝓞 K),
      ∀ a : F, vLa 𝔭 (IntermediateField.inclusion hF a) = vLa w a := by
  intro F F' K _ _ _ hF hK q hq hd w hw
  have hF' : F' ≤ K := hK ▸ le_sup_right
  letI : Algebra F K := (IntermediateField.inclusion hF).toRingHom.toAlgebra
  letI : Algebra F' K := (IntermediateField.inclusion hF').toRingHom.toAlgebra
  obtain ⟨𝔭, h⟩ := exists_valuation_eq F F' K (fun N _ f g h1 h2 => by
    let T : Subfield ℂ := (RingHom.eqLocusField f g).map (K.val : K →+* ℂ)
    let S : IntermediateField ℚ ℂ := T.toIntermediateField fun x => by
      rw [eq_ratCast]; exact SubfieldClass.ratCast_mem T x
    have hle : K ≤ S := by
      refine hK.le.trans (sup_le (fun x hx => ⟨⟨x, hF hx⟩, h1 ⟨x, hx⟩, rfl⟩)
        (fun x hx => ⟨⟨x, hF' hx⟩, h2 ⟨x, hx⟩, rfl⟩))
    ext z
    obtain ⟨y, hy, hyz⟩ := hle z.2
    have hyz' : y = z := Subtype.ext hyz
    subst hyz'
    exact hy) q hq hd w hw
  exact ⟨𝔭, fun a => congrArg (fun t => -WithZero.log t) (h a)⟩

end GlobalTheory.UnramCompositum
