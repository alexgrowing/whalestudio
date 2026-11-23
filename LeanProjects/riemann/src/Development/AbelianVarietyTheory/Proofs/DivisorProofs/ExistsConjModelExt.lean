import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjExt

open GlobalTheory.ConjDS GlobalTheory.LowTypeDetermined

section Gen

variable {n : ℕ} {ε ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def realMap (T : H ≃ₗᵢ⋆[ℂ] H') : H →L[ℝ] H' where
  toFun := T
  map_add' := map_add T
  map_smul' r x := by
    rw [RingHom.id_apply, ← Complex.coe_smul, ← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]
  cont := T.continuous

theorem smoothVec_map (T : H ≃ₗᵢ⋆[ℂ] H') (h : ∀ g v, T (σ g v) = σ' g (T v)) {L : Set (Matrix (Fin n) (Fin n) ℂ)}
    {w : H} (hw : SmoothVec L σ w) : SmoothVec L σ' (T w) := by
  intro k Xs hX
  simp only [← h]
  exact (realMap T).contDiff.comp (hw k Xs hX)

theorem lowKSub_stab {lam : Fin n → ℝ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) {w : H}
    (hw : w ∈ lowKSub ε lam σ) : σ g w ∈ lowKSub ε lam σ := by
  have : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) :=
    sSup_le fun S hS x hx => (le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) hS) (hS.2.1 g hg x hx)
  exact this hw

theorem lowKSub_transfer (he : ∀ a, ε' a = ε a.rev) (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v))
    {lam : Fin n → ℝ} {w : H} (hw : w ∈ lowKSub ε lam σ) : T.symm w ∈ lowKSub ε' (nr lam) σ' := by
  have : lowKSub ε lam σ ≤ (lowKSub ε' (nr lam) σ').comap (T.symm.toLinearEquiv : H →ₗ⋆[ℂ] H') := by
    refine sSup_le fun S hS x hx => ?_
    have h1 := ktype_transfer (sg_symm he) T.symm (symm_inter T h) hS
    rw [← lowK_rev he] at h1
    refine (le_sSup (s := {S | IsKTypeOf ε' σ' (Formalism.QuantumDeterminants.lowK ε' (nr lam)) S}) h1) ?_
    show T (T.symm x) ∈ S
    simpa using hx
  exact this hw

def prm (ε ε' : Fin n → Bool) : Equiv.Perm (Fin n) :=
  ((Fin.revPerm.trans (revNeg ε')).trans Fin.revPerm).trans (revNeg ε).symm

theorem revNeg_prm (a : Fin n) : revNeg ε (prm ε ε' a) = (revNeg ε' a.rev).rev := by
  simp [prm]

theorem eps_prm (he : ∀ a, ε' a = ε a.rev) (a : Fin n) : ε (prm ε ε' a) = ε a := by
  rw [← eps_revNeg ε (prm ε ε' a), revNeg_prm, ← he (revNeg ε' a.rev), eps_revNeg ε' a.rev, he, Fin.rev_rev]

theorem ext_transfer (he : ∀ a, ε' a = ε a.rev) (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v))
    (hU : IsURepOn (UJset ε) σ) {lam : Fin n → ℝ} {w : H}
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w) :
    IsWtOn (Formalism.REAL.Kset ε') σ' (fun a => Formalism.QuantumDeterminants.lowK ε' (nr lam) (revNeg ε' a))
      (T.symm (σ (pM (prm ε ε')) w)) := by
  have h1 := wt_transfer (sg_symm he) T.symm (symm_inter T h) (isWtOn_perm hU (prm ε ε') (eps_prm he) hw)
  convert h1 using 1
  funext a
  simp only [lowK_rev he, nr, revNeg_prm, Fin.rev_rev]

end Gen

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem conj_rep (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : (conjModel M).H τ) :
    cj (M.H τ) ((conjModel M).rep τ g w) = M.rep τ g (cj (M.H τ) w) := by
  have e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹ := by
    rw [inv_submatrix_equiv]
    have : (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
        rv (M.fr τ * g * (M.fr τ)⁻¹) := by
      ext i j
      simp [rv, Matrix.mul_apply]
    rw [this, rv_rv]
  show M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cj _ w) = M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cj _ w)
  rw [e]

theorem smooth_translate (M : DSModel V S) (τ : D.what₂.Tau) (u : M.sm τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ UJset (M.ε τ)) : SmoothVec (lieAt V τ) (M.rep τ) (M.σ τ g u) := by
  obtain ⟨_, -, hσ, -⟩ := M.ds τ
  have hs : M.sm τ = smooth (gramAt D V τ) (M.rep τ) := Submodule.span_eq (smooth (gramAt D V τ) (M.rep τ))
  have hP := M.fr_unit τ
  have h := M.fr_gram τ
  have hu' : (u : M.H τ) ∈ smooth (gramAt D V τ) (M.rep τ) := hs ▸ u.2
  have e : M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) = M.σ τ g := congrArg (M.σ τ) (conj_conj hP g)
  rw [← e]
  exact translate_mem (isUnit_gram hP h) (isURepOn_conj hσ hP h) (conj_inv_mem hP h hg) hu'

theorem exists_conjModel_ext : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (v : M.Vec), IsExtVec M v → ∃ (M' : DSModel V (fun τ => dualPar (S τ))) (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ) (v' : M'.Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, c τ (M'.rep τ g y) = M.rep τ g (c τ y)) ∧ IsExtVec M' v' := by
  intro D V S M v hv
  have he : ∀ τ a, (conjModel M).ε τ a = M.ε τ a.rev := fun _ _ => rfl
  have hK := fun τ => pM_mem (prm (M.ε τ) ((conjModel M).ε τ)) (eps_prm (he τ))
  have hU : ∀ τ, IsURepOn (UJset (M.ε τ)) (M.σ τ) := fun τ => (M.ds τ).2.2.1
  let c : ∀ τ, (conjModel M).H τ ≃ₗᵢ⋆[ℂ] M.H τ := fun τ => cj (M.H τ)
  have hc : ∀ τ g y, c τ ((conjModel M).σ τ g y) = M.σ τ (rv g) (c τ y) := fun _ _ _ => rfl
  have hr : ∀ τ g y, (c τ).symm (M.rep τ g y) = (conjModel M).rep τ g ((c τ).symm y) := fun τ g y => by
    apply (c τ).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (conj_rep M τ g _).symm
  refine ⟨conjModel M, c, fun τ => ⟨(c τ).symm (M.σ τ (pM (prm (M.ε τ) ((conjModel M).ε τ))) (v τ)),
    Submodule.subset_span (smoothVec_map (c τ).symm (hr τ) (smooth_translate M τ (v τ) (kset_uj (hK τ))))⟩,
    fun τ g _ y => conj_rep M τ g y, fun τ => ⟨?_, ?_, ?_⟩⟩
  · rw [LinearIsometryEquiv.norm_map, (hU τ).2.1 _ (kset_uj (hK τ)), (hv τ).1]
  · exact lowKSub_transfer (he τ) (c τ) (hc τ) (lowKSub_stab (hK τ) (hv τ).2.1)
  · exact ext_transfer (he τ) (c τ) (hc τ) (hU τ) (hv τ).2.2

end GlobalTheory.ConjExt
