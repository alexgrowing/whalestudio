import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.Columns.CoefModX
import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section

variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}

theorem nd_map_star_star {σ : Type} (F : MvPolynomial σ K) :
    MvPolynomial.map (starRingEnd K) (MvPolynomial.map (starRingEnd K) F) = F := by
  rw [MvPolynomial.map_map]
  have e : (starRingEnd K).comp (starRingEnd K) = RingHom.id K := RingHom.ext fun a => star_star a
  rw [e, MvPolynomial.map_id]

theorem nd_mem_dual {lam : ι → DomWeight n} (h : VV K lam →ₗ⋆[K] VV K lam →ₗ[K] K) (L : Submodule (𝓞 K) (VV K lam)) (x : VV K lam) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]

theorem nd_half (lam : ι → DomWeight n) (T T' : Submodule (𝓞 K) (Pol K ι n))
    (G : ι → GL (Fin n) K) (M : ι → Submodule (𝓞 K) (Fin n → K))
    (hdesc : ∀ F : Pol K ι n, F ∈ transLat lam T M ↔
      MvPolynomial.map (starRingEnd K) F ∈ transLat lam T (fun τ => bcLat (starRingEnd K) (M τ)))
    (hdual : ∀ x : Pol K ι n, x ∈ VV K lam →
      (x ∈ transLat lam T' (fun τ => dualFr (bcLat (starRingEnd K) (M τ))) ↔
        ∀ y ∈ transLat lam T (fun τ => bcLat (starRingEnd K) (M τ)), y ∈ VV K lam →
          pairB lam x y ∈ (1 : Submodule (𝓞 K) K)))
    (x : VV K lam) :
    x ∈ Formalism.HermitianLatticesTheory.dual (pairK lam fun τ => ((G τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ((transLat lam T M).comap ((VV K lam).subtype.restrictScalars (𝓞 K))) ↔
      (x : Pol K ι n) ∈ transLat lam T' (fun τ => hdualFr ((G τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (M τ)) := by
  have hsp := (baseChangeSpace_holds K K (starRingEnd K) ι n lam).1
  have e1 : (fun τ => hdualFr ((G τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (M τ)) =
      fun τ => gLat (G⁻¹ τ) (dualFr (bcLat (starRingEnd K) (M τ))) := funext fun τ => du_hdualFr_eq (G τ) (M τ)
  rw [nd_mem_dual, e1, transLat_gLat]
  have e2 : (x : Pol K ι n) ∈ (transLat lam T' fun τ => dualFr (bcLat (starRingEnd K) (M τ))).map
      ((actP lam G⁻¹).restrictScalars (𝓞 K)) ↔
      actP lam G (x : Pol K ι n) ∈ transLat lam T' fun τ => dualFr (bcLat (starRingEnd K) (M τ)) := by
    constructor
    · rintro ⟨z, hz, hzx⟩
      rw [← hzx, LinearMap.coe_restrictScalars, ← polyAction_mul, mul_inv_cancel, polyAction_one₂]
      exact hz
    · intro h
      refine ⟨_, h, ?_⟩
      rw [LinearMap.coe_restrictScalars, ← polyAction_mul, inv_mul_cancel, polyAction_one₂]
  rw [e2, hdual _ (polyAction_mem_VV lam G x.2)]
  constructor
  · intro h y hy hyV
    have hy' : MvPolynomial.map (starRingEnd K) y ∈ transLat lam T M := by
      rw [hdesc, nd_map_star_star]; exact hy
    have hyV' : MvPolynomial.map (starRingEnd K) y ∈ VV K lam := (hsp y).1 hyV
    have := h ⟨_, hyV'⟩ hy'
    rw [pairK_apply, pairP_eq_pairB, nd_map_star_star] at this
    rwa [pairingBSymm_holds]
  · intro h y hy
    rw [pairK_apply, pairP_eq_pairB, pairingBSymm_holds]
    exact h _ ((hdesc _).1 hy) ((hsp _).1 y.2)

end

theorem nabDelDual_of (hD : NabDelDescent) (hK : PairBDualK) : NabDelDual := by
  intro K _ _ _ ι _ n lam G M _ hG hM
  have hMc : ∀ τ, Submodule.IsLattice K (bcLat (starRingEnd K) (M τ)) := fun τ =>
    bc_bcLat_lattice (j := starRingEnd K) tauLatticeLattice_holds (M τ) (hM τ)
  let GG : ι → GL (Fin n) K := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (G τ) (hG τ).ne_zero
  constructor
  · ext x
    have h := nd_half lam (nabStd K lam) (delStd K lam) GG M
      (fun F => (hD K K (starRingEnd K) ι n lam M hM F).1)
      (fun x hx => by
        have h1 := (hK K ι n lam (fun τ => bcLat (starRingEnd K) (M τ)) hMc ⟨x, hx⟩).1
        simp only [delK, nabK, delP, nabP, Submodule.mem_comap, LinearMap.coe_restrictScalars,
          Submodule.coe_subtype] at h1
        rw [h1]
        constructor
        · intro H y hy hyV
          exact H ⟨y, hyV⟩ hy
        · intro H y hy
          exact H y hy y.2)
      x
    exact h
  · ext x
    have h := nd_half lam (delStd K lam) (nabStd K lam) GG M
      (fun F => (hD K K (starRingEnd K) ι n lam M hM F).2)
      (fun x hx => by
        have h1 := (hK K ι n lam (fun τ => bcLat (starRingEnd K) (M τ)) hMc ⟨x, hx⟩).2
        simp only [delK, nabK, delP, nabP, Submodule.mem_comap, LinearMap.coe_restrictScalars,
          Submodule.coe_subtype] at h1
        rw [h1]
        constructor
        · intro H y hy hyV
          exact H ⟨y, hyV⟩ hy
        · intro H y hy
          exact H y hy y.2)
      x
    exact h

end Formalism.L2.DIV
