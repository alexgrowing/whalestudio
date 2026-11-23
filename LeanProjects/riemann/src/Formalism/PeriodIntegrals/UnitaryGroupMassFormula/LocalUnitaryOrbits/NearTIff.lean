import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GramCoord

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem nearT_iff (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K} (hπ : IsRes σ v ϖ τ π)
    {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hT : ∀ i j, T i j ∈ OR (E := E) v) (X : lamA v Λ a) :
    (X : TupV (E := E) v n a) ∈ NearT v σ J ϖ T ↔
      ffGram τ 1 (phi σ J v Λ hSD he π a X) = fun i j => π ⟨T i j, hT i j⟩ := by
  have hg : ∀ i j, gramR (Fv F v) σ J (X : TupV (E := E) v n a) i j ∈ OR (E := E) v := fun i j =>
    (hSD _).1 (memA v Λ X j) _ (memA v Λ X i)
  have hconj : ∀ i p, π ⟨hR (Fv F v) σ J ((X : TupV (E := E) v n a) i) (e p),
      (hSD _).1 (bas_mem v Λ he p) _ (memA v Λ X i)⟩ = τ (π (cf σ J v Λ hSD he X i p)) := fun i p =>
    hπ.2.2 _ _ (by rw [cf_coe, Orb.hR_conj σ J v hcm hJ])
  have hG : ∀ i j, π ⟨_, hg i j⟩ = ffGram τ 1 (phi σ J v Λ hSD he π a X) i j := by
    intro i j
    rw [ffGram_one]
    have e1 : (⟨_, hg i j⟩ : OR (E := E) v) = ∑ p, (⟨hR (Fv F v) σ J ((X : TupV (E := E) v n a) i) (e p),
        (hSD _).1 (bas_mem v Λ he p) _ (memA v Λ X i)⟩ : OR (E := E) v) * cf σ J v Λ hSD he X j p := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
      rw [gram_coord σ J v Λ hcm hJ hSD he he1]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [cf_coe, Orb.hR_conj σ J v hcm hJ]
    rw [e1, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, hconj, phi_apply, phi_apply]
  constructor
  · intro hN
    funext i j
    rw [← hG]
    have h0 := (hπ.2.1 (⟨_, hg i j⟩ - ⟨T i j, hT i j⟩)).2 (hN i j)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  · intro hE i j
    have h1 := congrFun (congrFun hE i) j
    rw [← hG] at h1
    have h0 : π (⟨_, hg i j⟩ - ⟨T i j, hT i j⟩) = 0 := by rw [map_sub, h1, sub_self]
    exact (hπ.2.1 _).1 h0

theorem card_cls (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {ϖ : Fv F v} {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K) (hπ : IsRes σ v ϖ τ π)
    {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hT : ∀ i j, T i j ∈ OR (E := E) v) :
    Nat.card (clsU σ J v Λ a ϖ T) =
      Nat.card {X : Fin a → Fin n → K // ffGram τ 1 X = fun i j => π ⟨T i j, hT i j⟩} := by
  set Φ := phi σ J v Λ hSD he π a with hΦ
  let eq : (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) ≃+ (Fin a → Fin n → K) :=
    (QuotientAddGroup.quotientAddEquivOfEq (phi_ker σ J v Λ hSD he he1 hπ a)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective Φ (phi_surj σ J v Λ hSD he he1 hπ a))
  have heq : ∀ x : lamA v Λ a, eq (QuotientAddGroup.mk x) = Φ x := fun x => rfl
  set P : (Fin a → Fin n → K) → Prop := fun M => ffGram τ 1 M = fun i j => π ⟨T i j, hT i j⟩ with hP
  have hset : clsU σ J v Λ a ϖ T = {q | P (eq q)} := by
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      constructor
      · rintro ⟨y, hy, hyx⟩
        show P (eq (QuotientAddGroup.mk x))
        rw [← hyx, heq]
        exact (nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT y).1 hy
      · intro hx
        refine ⟨x, (nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT x).2 ?_, rfl⟩
        have : P (eq (QuotientAddGroup.mk x)) := hx
        rw [heq] at this
        exact this
  rw [hset]
  exact Nat.card_congr (Equiv.subtypeEquiv (p := fun q => q ∈ {q | P (eq q)}) eq.toEquiv (fun q => Iff.rfl))

end PI.OmLocU.Red
