import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianNormalLocalApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorModelFilteredColimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorDescentDirectedUnionSubringStatement
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginNoeth

theorem mem_originIdeal_iff {T : Type} [CommRing T] [IsLocalRing T] (f : Polynomial T) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal T ↔ f.coeff 0 ∈ maximalIdeal T := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal T ≤ (maximalIdeal T).comap (Polynomial.constantCoeff (R := T)) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simpa using ha
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp
    have := hle hf
    simpa [Polynomial.coeff_zero_eq_eval_zero] using this
  · intro hf
    have h1 : Polynomial.C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal T :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)
    have h2 : f - Polynomial.C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal T :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_sub_C))
    simpa using Ideal.add_mem _ h1 h2

theorem comap_originIdeal (A T : Type) [CommRing A] [IsLocalRing A] [CommRing T] [IsLocalRing T]
    (i : A →+* T) [IsLocalHom i] :
    (GlobalTheory.KeyOriginCut.originIdeal T).comap (Polynomial.mapRingHom i) = GlobalTheory.KeyOriginCut.originIdeal A := by
  ext f
  rw [Ideal.mem_comap, mem_originIdeal_iff, mem_originIdeal_iff, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_map_iff]

theorem isIntegrallyClosed_of_absIntClosed (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx0
  obtain ⟨p, hpm, hpx⟩ := hx0
  suffices H : ∀ n : ℕ, ∀ p : Polynomial T, p.Monic → p.natDegree = n → Polynomial.eval₂ (algebraMap T (FractionRing T)) x p = 0 →
      ∃ y, algebraMap T (FractionRing T) y = x from H _ p hpm rfl hpx
  intro n
  induction n with
  | zero =>
    intro p hp hd hx
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hp hd
    subst h1
    simp at hx
  | succ n ih =>
    intro p hp hd hx
    obtain ⟨r, hr⟩ := hT p hp (by omega)
    have hroot : p.IsRoot r := hr
    have hdec := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
    set p' := p /ₘ (Polynomial.X - Polynomial.C r)
    have hp' : p'.Monic := (Polynomial.monic_X_sub_C r).of_mul_monic_left (by rw [hdec]; exact hp)
    have hd' : p'.natDegree = n := by
      have := congrArg Polynomial.natDegree hdec
      rw [(Polynomial.monic_X_sub_C r).natDegree_mul hp', Polynomial.natDegree_X_sub_C] at this
      omega
    rw [← hdec, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h | h
    · refine ⟨r, ?_⟩
      simp at h
      exact (sub_eq_zero.mp h).symm
    · exact ih p' hp' hd' h

theorem norm_finiteType {T : Type} [CommRing T] [IsDomain T] [IsIntegrallyClosed T] (S : Finset T) :
    Algebra.FiniteType ℤ (GlobalTheory.NormalApprox.norm S) := by
  haveI := GlobalTheory.finite_integralClosure_of_essFiniteType_int (GlobalTheory.NormalApprox.gen S)
  haveI : Algebra.FiniteType ℤ
      (integralClosure (GlobalTheory.NormalApprox.gen S) (FractionRing (GlobalTheory.NormalApprox.gen S))) :=
    Algebra.FiniteType.trans (S := GlobalTheory.NormalApprox.gen S) inferInstance inferInstance
  exact Algebra.FiniteType.equiv this
    (AlgEquiv.ofRingEquiv (f := (GlobalTheory.NormalApprox.normEquiv S).symm) (fun n => by simp))

theorem loc_essFiniteType {T : Type} [CommRing T] [IsDomain T] [IsIntegrallyClosed T] (S : Finset T) :
    Algebra.EssFiniteType ℤ (GlobalTheory.NormalApprox.loc S) := by
  haveI := norm_finiteType S
  haveI := GlobalTheory.NormalApprox.loc_isLocalization S
  haveI : Algebra.EssFiniteType (GlobalTheory.NormalApprox.norm S) (GlobalTheory.NormalApprox.loc S) :=
    Algebra.EssFiniteType.of_isLocalization _ (GlobalTheory.NormalApprox.unitsIn S)
  exact Algebra.EssFiniteType.comp ℤ (GlobalTheory.NormalApprox.norm S) (GlobalTheory.NormalApprox.loc S)

theorem exists_noetherian_model : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E]
      [IsScalarTower T (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
      (Q : Ideal E) [Q.IsPrime],
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (j : Localization.AtPrime Q →+* O),
      j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O →
    ∀ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j →
    ∀ (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (_ : IsIntegrallyClosed A) (_ : Algebra.EssFiniteType ℤ A) (i : A →+* T), Function.Injective i ∧ IsLocalHom i ∧ IsUnit (q : A) ∧
      ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial A) EA) (_ : Algebra A EA)
        (_ : IsScalarTower A (Polynomial A) EA) (_ : Algebra.Etale (Polynomial A) EA)
        (QA : Ideal EA) (_ : QA.IsPrime),
        QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
      ∃ (jA : Localization.AtPrime QA →+* O),
        jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
          (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
      ∃ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA ∧
      ∃ (DA : Type) (_ : CommRing DA) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)
        (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA ∧
        ∀ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA →
          ∃ σ₁ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  intro T O _ _ _ _ _ _ _ _ hT q hq hqT E _ _ _ _ _ Q _ hQ j hj ψ hψ D₁ _ _ act₁ htor
  have hTic : IsIntegrallyClosed T := isIntegrallyClosed_of_absIntClosed T hT
  let 𝒜 : Finset T → Subring T := GlobalTheory.NormalApprox.loc
  have hmono : Monotone 𝒜 := GlobalTheory.NormalApprox.loc_mono
  have hcov : ∀ (S : Finset T), ∀ x ∈ S, x ∈ 𝒜 S := fun S x hx => GlobalTheory.NormalApprox.mem_loc_of_mem S hx
  have hprop : ∀ S, IsNoetherianRing (𝒜 S) ∧ IsIntegrallyClosed (𝒜 S) ∧ IsLocalRing (𝒜 S) ∧
      (∀ x : 𝒜 S, IsUnit (x : T) → IsUnit x) ∧ Algebra.EssFiniteType ℤ (𝒜 S) := by
    intro S
    haveI := GlobalTheory.NormalApprox.loc_isLocalization S
    haveI := GlobalTheory.NormalApprox.norm_isIntegrallyClosed S
    exact ⟨IsLocalization.isNoetherianRing (GlobalTheory.NormalApprox.unitsIn S) _ (GlobalTheory.NormalApprox.norm_isNoetherianRing S),
      isIntegrallyClosed_of_isLocalization (GlobalTheory.NormalApprox.loc S) (GlobalTheory.NormalApprox.unitsIn S)
        (GlobalTheory.NormalApprox.unitsIn_le S),
      GlobalTheory.NormalApprox.loc_isLocalRing S, GlobalTheory.NormalApprox.isUnit_of_isUnit_coe S, loc_essFiniteType S⟩
  obtain ⟨S, EA, _, _, _, _, _, e, he, β, hβ, D, _, _, actA, htorA, hlast⟩ :=
    GlobalTheory.T.exists_torsor_descent_directedUnion_subring T (Finset T) 𝒜 hmono (fun x => ⟨{x}, hcov {x} x (Finset.mem_singleton_self x)⟩) q hq E Q D₁ act₁ htor
  obtain ⟨hN, hIC, hL, hU, hEF⟩ := hprop S
  have hloc : IsLocalHom (𝒜 S).subtype := ⟨fun a ha => hU a ha⟩
  have hqA : IsUnit (q : 𝒜 S) := hU _ (by simpa using hqT)
  have horig : (Q.comap e).comap (algebraMap (Polynomial (𝒜 S)) EA) = GlobalTheory.KeyOriginCut.originIdeal (𝒜 S) := by
    rw [Ideal.comap_comap, he, ← Ideal.comap_comap, hQ]
    exact comap_originIdeal (𝒜 S) T (𝒜 S).subtype
  let jA : Localization.AtPrime (Q.comap e) →+* O := j.comp (Localization.localRingHom (Q.comap e) Q e rfl)
  have hjA : jA.comp (algebraMap (Polynomial (𝒜 S)) (Localization.AtPrime (Q.comap e))) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom (𝒜 S).subtype) := by
    refine RingHom.ext fun x => ?_
    change j (Localization.localRingHom (Q.comap e) Q e rfl
      (algebraMap (Polynomial (𝒜 S)) (Localization.AtPrime (Q.comap e)) x)) = _
    rw [IsScalarTower.algebraMap_apply (Polynomial (𝒜 S)) EA (Localization.AtPrime (Q.comap e)),
      Localization.localRingHom_to_map, ← RingHom.comp_apply e, he, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply, ← RingHom.comp_apply j, hj]
    rfl
  refine ⟨𝒜 S, inferInstance, inferInstance, hL, hN, hIC, hEF, (𝒜 S).subtype, Subtype.val_injective, hloc, hqA,
    EA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q.comap e, inferInstance, horig,
    jA, hjA, ψ.comp β, ?_, D, inferInstance, inferInstance, actA, htorA, fun σ hσ => hlast _ ψ σ hσ⟩
  rw [RingHom.comp_assoc, hβ, ← RingHom.comp_assoc, hψ]
  rfl

end GlobalTheory.KeyOriginNoeth
