import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CfCoe

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem phi_surj (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
    (he1 : gramR (Fv F v) σ J e = 1) {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K}
    {π : OR (E := E) v →+* K} (hπ : IsRes σ v ϖ τ π) (a : ℕ) :
    Function.Surjective (phi σ J v Λ hSD he π a) := by
  intro M
  choose c hc using fun i p => hπ.1 (M i p)
  have hX : (fun i => ∑ p, (c i p : Fv F v ⊗[F] E) • e p) ∈ lamA v Λ a := fun i =>
    (he _).2 ⟨fun p => (c i p : Fv F v ⊗[F] E), fun p => (c i p).2, rfl⟩
  refine ⟨⟨_, hX⟩, ?_⟩
  funext i p
  rw [phi_apply]
  have h : cf σ J v Λ hSD he ⟨_, hX⟩ i p = c i p := by
    apply Subtype.ext
    rw [cf_coe]
    exact coord_eq σ J v e he1 (fun q => (c i q : Fv F v ⊗[F] E)) p
  rw [h, hc]

theorem phi_ker (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
    (he1 : gramR (Fv F v) σ J e = 1) {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K}
    {π : OR (E := E) v →+* K} (hπ : IsRes σ v ϖ τ π) (a : ℕ) :
    (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a) = (phi σ J v Λ hSD he π a).ker := by
  ext X
  rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨Z, hZ, hZX⟩
    funext i p
    rw [phi_apply, Pi.zero_apply, Pi.zero_apply]
    apply (hπ.2.1 _).2
    rw [cf_coe, ← hZX]
    refine ⟨hR (Fv F v) σ J (e p) (Z i), (hSD _).1 (hZ i) _ (bas_mem v Λ he p), ?_⟩
    show hR (Fv F v) σ J (e p) (sc (E := E) v ϖ • Z i) = _
    rw [Orb.hR_smul_right]
  · intro h0
    have hP : ∀ i p, ∃ d ∈ OEv (E := E) v,
        hR (Fv F v) σ J (e p) ((X : TupV (E := E) v n a) i) = sc (E := E) v ϖ * d := by
      intro i p
      have := (hπ.2.1 (cf σ J v Λ hSD he X i p)).1 (by
        have h1 := congrFun (congrFun h0 i) p
        rw [phi_apply] at h1
        exact h1)
      exact this
    choose d hd hde using hP
    have hZ : (fun i => ∑ p, d i p • e p) ∈ lamA v Λ a := fun i => (he _).2 ⟨d i, hd i, rfl⟩
    refine ⟨_, hZ, ?_⟩
    funext i
    rw [DistribMulAction.toAddMonoidHom_apply, Pi.smul_apply, expand σ J v Λ he he1 (memA v Λ X i), Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hde, smul_smul]

theorem gram_coord (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1) {a : ℕ}
    (X : lamA v Λ a) (i j : Fin a) :
    gramR (Fv F v) σ J (X : TupV (E := E) v n a) i j = ∑ p, sigR (Fv F v) σ (cf σ J v Λ hSD he X i p : Fv F v ⊗[F] E) *
      (cf σ J v Λ hSD he X j p : Fv F v ⊗[F] E) := by
  show hR (Fv F v) σ J ((X : TupV (E := E) v n a) i) ((X : TupV (E := E) v n a) j) = _
  conv_lhs => rw [expand σ J v Λ he he1 (memA v Λ X j)]
  rw [Orb.hR_sum_right σ J v]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [cf_coe, cf_coe, Orb.hR_conj σ J v hcm hJ, mul_comm]

end PI.OmLocU.Red
