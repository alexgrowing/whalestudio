import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsFibreSectionsFlat
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsGenericRestrLen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsFibreRestrKer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsRestrQuotTorsionFree
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsDedekindFibreRank
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExtendTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

open scoped Pointwise

noncomputable section

universe u w

theorem homogeneousComponent_map_eq {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {N : ℕ}
    (d : ℕ) (p : Poly R N) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem mem_of_map_mem_map {S : Type u} [CommRing S] [IsDomain S] {F : Type u} [Field F] [Algebra S F]
    [IsFractionRing S F] {N : ℕ} {qq : Ideal (Poly S N)} (hq : qq.IsPrime)
    (hconst : ∀ s : S, (C s : Poly S N) ∈ qq → s = 0) {p : Poly S N}
    (hp : MvPolynomial.map (algebraMap S F) p ∈ qq.map (MvPolynomial.map (algebraMap S F))) : p ∈ qq := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin (N + 1)) (R := S) (S := F)
  have hdisj : Disjoint (((nonZeroDivisors S).map (C : S →+* Poly S N) : Submonoid (Poly S N)) : Set (Poly S N))
      (qq : Set (Poly S N)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsq
    exact nonZeroDivisors.ne_zero hs (hconst s hsq)
  have h := IsLocalization.under_map_of_isPrime_disjoint ((nonZeroDivisors S).map (C : S →+* Poly S N))
    (Poly F N) hq hdisj
  rw [← h]
  exact hp

theorem FibreSectionsFlat.proof (hG : GenericRestrLen.Statement.{u, w}) (hK : FibreRestrKer.Statement.{u, w})
    (hT : RestrQuotTorsionFree.Statement.{u, w}) (hR : DedekindFibreRank.Statement.{u, w})
    (hF : FiniteSections.Statement.{u, w}) : FibreSectionsFlat.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x L 𝔪 h𝔪 qq hq hconst e hsub

  have hhom : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq := fun p hp d => by
    refine mem_of_map_mem_map (F := F) hq hconst ?_
    rw [← homogeneousComponent_map_eq]
    exact hsub.homog _ (Ideal.mem_map_of_mem _ hp) d
  have hx : x ≠ 0 := by
    obtain ⟨i, hi⟩ := hsub.relevant
    rintro rfl
    exact hi (hsub.le ((mem_primeOf_of_isHomogeneous (S := F) _ (isHomogeneous_X F i)).mpr (by simp)))
  filter_upwards [hK S F Ω N x L 𝔪 h𝔪 qq hq hconst e hsub] with c hc
  set Q : LineBundle S x := L.tensorProd (twistBundle S x (c : ℤ)) with hQdef
  have hQ : Q.toSubSystem = L.toSubSystem.twist (twistSys S x (c : ℤ)) := rfl

  rw [← SubSystem.extend_twistSys (S := S) (F := F) (c : ℤ), ← SubSystem.extend_twist, ← hQ,
    hG S F Ω N x Q.toSubSystem qq hhom]

  rw [← hQ] at hc
  rw [restrLen, hc]
  set A := Q.toSubSystem.secs
  set Bq := (Q.toSubSystem.twist (idealSys x qq)).secs
  set K := Bq.comap A.subtype
  have hcomap : (Bq ⊔ 𝔪 • A).comap A.subtype = K ⊔ 𝔪 • (⊤ : Submodule S A) := by
    apply Submodule.map_injective_of_injective A.injective_subtype
    rw [Submodule.map_comap_subtype, Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_smul'',
      Submodule.map_subtype_top, inf_comm, sup_comm, sup_inf_assoc_of_le _ (Submodule.smul_le_right),
      inf_comm, sup_comm]
  have hmap : (K ⊔ 𝔪 • (⊤ : Submodule S A)).map K.mkQ = 𝔪 • (⊤ : Submodule S (A ⧸ K)) := by
    rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ,
      Submodule.mkQ_map_self, bot_sup_eq]
  have hlen : Module.length S (A ⧸ (K ⊔ 𝔪 • (⊤ : Submodule S A))) =
      Module.length S ((A ⧸ K) ⧸ 𝔪 • (⊤ : Submodule S (A ⧸ K))) := by
    rw [← hmap]
    exact ((Submodule.quotientQuotientEquivQuotient K _ le_sup_left).length_eq).symm
  have : Module.Finite S A := (hF S Ω N x Q hx).1
  rw [hcomap, hlen, hR S (A ⧸ K) inferInstance (hT S F Ω N x Q qq hq hconst e hsub) 𝔪 h𝔪]
  simp

end

end GroundTheory.Heights₂.Heights.Kleiman
