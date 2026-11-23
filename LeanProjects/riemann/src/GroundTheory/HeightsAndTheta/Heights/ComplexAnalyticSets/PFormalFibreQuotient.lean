import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibreQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem primeFibreLocalRing_nonempty_equiv_of_surjective
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra S S'] (f : R →+* S) (φ : R' →+* S')
    (hf : Function.Surjective f) (hφ : Function.Surjective φ)
    (hcomm : φ.comp (algebraMap R R') = (algebraMap S S').comp f)
    (hker : RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap R R'))
    (P : Ideal S') [P.IsPrime] :
    Nonempty (primeFibreLocalRing S P ≃+* primeFibreLocalRing R (P.comap φ)) := by
  set q := P.comap (algebraMap S S') with hq
  have hq' : (P.comap φ).comap (algebraMap R R') = q.comap f := by
    rw [hq, Ideal.comap_comap, Ideal.comap_comap, hcomm]
  have hmapq : ((q.comap f).map (algebraMap R R')).map φ = q.map (algebraMap S S') := by
    rw [Ideal.map_map, hcomm, ← Ideal.map_map, Ideal.map_comap_of_surjective f hf]
  let ψ : Localization.AtPrime (P.comap φ) →+* Localization.AtPrime P :=
    Localization.localRingHom (P.comap φ) P φ rfl
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    obtain ⟨a', rfl⟩ := hφ a
    obtain ⟨t', ht'⟩ := hφ (t : S')
    have ht'' : t' ∈ (P.comap φ).primeCompl := by
      change t' ∉ P.comap φ
      rw [Ideal.mem_comap, ht']
      exact t.2
    refine ⟨IsLocalization.mk' _ a' ⟨t', ht''⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht'
  let χ := (Ideal.Quotient.mk ((q.map (algebraMap S S')).map
    (algebraMap S' (Localization.AtPrime P)))).comp ψ
  have hχ : Function.Surjective χ := Ideal.Quotient.mk_surjective.comp hψ
  have hkerχ : ((q.comap f).map (algebraMap R R')).map
      (algebraMap R' (Localization.AtPrime (P.comap φ))) = RingHom.ker χ := by
    ext x
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (P.comap φ).primeCompl x
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      Localization.localRingHom_mk', IsLocalization.mk'_mem_map_algebraMap_iff,
      IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨t, ht, htr⟩
      refine ⟨φ t, ht, ?_⟩
      rw [← map_mul, ← hmapq]
      exact Ideal.mem_map_of_mem φ htr
    · rintro ⟨t, ht, htr⟩
      obtain ⟨t', rfl⟩ := hφ t
      refine ⟨t', ht, ?_⟩
      have h1 : φ (t' * r) ∈ ((q.comap f).map (algebraMap R R')).map φ := by
        rw [hmapq, map_mul]
        exact htr
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective φ hφ] at h1
      have key : Ideal.comap φ ⊥ ≤ (q.comap f).map (algebraMap R R') := by
        refine le_trans ?_ (le_trans hker (Ideal.map_mono ?_))
        · intro y hy
          simpa using hy
        · intro y hy
          rw [Ideal.mem_comap, RingHom.mem_ker.mp hy]
          exact q.zero_mem
      exact (sup_le le_rfl key) h1
  refine ⟨(((Ideal.quotEquivOfEq ?_).trans (RingHom.quotientKerEquivOfSurjective hχ))).symm⟩
  rw [← hkerχ, hq']

theorem exists_adicCompletion_surjection_of_surjective
    {B A : Type} [CommRing B] [CommRing A] (f : B →+* A) (hf : Function.Surjective f)
    (hB : IsNoetherianRing B) (m : Ideal A) :
    ∃ φ : AdicCompletion (m.comap f) B →+* AdicCompletion m A, Function.Surjective φ ∧
      φ.comp (algebraMap B (AdicCompletion (m.comap f) B)) =
        (algebraMap A (AdicCompletion m A)).comp f ∧
      RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap B (AdicCompletion (m.comap f) B)) := by
  have := hB
  have : IsNoetherianRing A := isNoetherianRing_of_surjective B A f hf
  set M := m.comap f with hM
  have hpow : ∀ n : ℕ, (M ^ n).map f = m ^ n := fun n => by
    rw [Ideal.map_pow, hM, Ideal.map_comap_of_surjective f hf]
  let fam : (n : ℕ) → AdicCompletion M B →+* A ⧸ m ^ n := fun n =>
    (Ideal.quotientMap (m ^ n) f (Ideal.le_comap_pow f n)).comp
      (AdicCompletion.evalₐ M n : AdicCompletion M B →+* B ⧸ M ^ n)
  have hfam : ∀ {k n : ℕ} (hle : k ≤ n), (Ideal.Quotient.factorPow m hle).comp (fam n) = fam k := by
    intro k n hle
    ext x
    induction x using AdicCompletion.induction_on with
    | h b =>
      simp only [fam, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk]
      change Ideal.Quotient.factorPow m hle (Ideal.Quotient.mk (m ^ n) (f (b n))) =
        Ideal.Quotient.mk (m ^ k) (f (b k))
      rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
      have hb := AdicCompletion.AdicCauchySequence.mk_eq_mk hle b
      rw [Submodule.Quotient.eq] at hb
      have hb' : b n - b k ∈ M ^ k := by simpa using hb
      rw [← map_sub]
      exact Ideal.le_comap_pow f k hb'
  let φ : AdicCompletion M B →+* AdicCompletion m A := AdicCompletion.liftRingHom m fam hfam
  have hcomm : φ.comp (algebraMap B (AdicCompletion M B)) = (algebraMap A (AdicCompletion m A)).comp f := by
    refine RingHom.ext fun b => AdicCompletion.ext_evalₐ fun n => ?_
    simp only [φ, fam, RingHom.comp_apply, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_liftRingHom,
      RingHom.coe_coe, AdicCompletion.evalₐ_of, Algebra.algebraMap_self, RingHom.id_apply]
    rfl
  refine ⟨φ, ?_, hcomm, ?_⟩
  · have fgM : M.FG := IsNoetherian.noetherian M
    have fgm : m.FG := IsNoetherian.noetherian m
    have := AdicCompletion.isAdicComplete_self M fgM
    have hmap : (M.map (algebraMap B (AdicCompletion M B))).map φ =
        m.map (algebraMap A (AdicCompletion m A)) := by
      rw [Ideal.map_map, hcomm, ← Ideal.map_map, hM, Ideal.map_comap_of_surjective f hf]
    have : IsHausdorff ((M.map (algebraMap B (AdicCompletion M B))).map φ) (AdicCompletion m A) := by
      rw [hmap]
      exact (AdicCompletion.isAdicComplete_self m fgm).toIsHausdorff
    apply surjective_of_mk_map_comp_surjective (I := M.map (algebraMap B (AdicCompletion M B))) φ
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ m y)
    obtain ⟨b, rfl⟩ := hf a
    refine ⟨algebraMap B _ b, ?_⟩
    rw [RingHom.comp_apply, ← RingHom.comp_apply φ, hcomm, RingHom.comp_apply, Ideal.Quotient.eq, hmap,
      ← AdicCompletion.ker_evalOneₐ_eq_map m fgm, RingHom.mem_ker]
    simp [ha, AdicCompletion.algebraMap_apply]
  · intro x hx
    let _ : Algebra B A := f.toAlgebra
    let K := RingHom.ker f
    let g : B →ₗ[B] A := Algebra.linearMap B A
    have hg : Function.Surjective g := hf
    have hfg : Function.Exact K.subtype g := by
      intro y
      simp [g, K, RingHom.mem_ker, Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]
    have hx' : AdicCompletion.map M g x = 0 := by
      induction x using AdicCompletion.induction_on with
      | h b => ?_
      have hb := RingHom.mem_ker.mp hx
      refine AdicCompletion.ext fun n => ?_
      have h1 : f (b n) ∈ m ^ n := by
        have := congrArg (AdicCompletion.evalₐ m n) hb
        rw [map_zero] at this
        simp only [φ, AdicCompletion.evalₐ_liftRingHom, fam, RingHom.comp_apply, RingHom.coe_coe,
          AdicCompletion.evalₐ_mk] at this
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      have h2 : g (b n) ∈ (M ^ n • ⊤ : Submodule B A) := by
        rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
        change f (b n) ∈ (M ^ n).map f
        rw [hpow]
        exact h1
      simpa [AdicCompletion.map_mk] using h2
    obtain ⟨z, rfl⟩ := ((AdicCompletion.map_exact (I := M) Subtype.val_injective hfg hg) x).mp hx'
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite M K z
    have hnat := congrArg (fun F => F t) (AdicCompletion.ofTensorProduct_naturality M K.subtype)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hnat
    rw [hnat]
    clear hnat hx hx'
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r k =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq,
        Submodule.coe_subtype, AdicCompletion.ofTensorProduct_tmul]
      exact Ideal.mul_mem_left _ r (Ideal.mem_map_of_mem _ k.2)
    | add t₁ t₂ h₁ h₂ =>
      rw [map_add, map_add]
      exact add_mem h₁ h₂

theorem FormalFibreQuotient.proof : FormalFibreQuotient.Statement := by
  intro B A _ _ f hf hB m P _
  obtain ⟨φ, hφ, hcomm, hker⟩ := exists_adicCompletion_surjection_of_surjective f hf hB m
  refine ⟨⟨P.comap φ, inferInstance⟩, ?_, ?_⟩
  · change (P.comap φ).comap _ = _
    rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  · exact primeFibreLocalRing_nonempty_equiv_of_surjective f φ hf hφ hcomm hker P

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
