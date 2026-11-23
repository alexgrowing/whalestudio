import Formalism.SharpRestriction.GrowthBounds.DataGChain

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.MainNotions.G MvPolynomial

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

def levAll (P : Places p O Kf) : Level P where
  Γ := (∀ v, GL (Fin (P.m + 1)) (P.Qq v)) × ℤˣ
  act := fun v => (Pi.evalMonoidHom _ v).comp (MonoidHom.fst _ _)
  χ := (Units.map ((Int.castRingHom O : ℤ →+* O) : ℤ →* O)).comp (MonoidHom.snd _ _)

variable (P : Places p O Kf)

theorem gPos_one (v : Fin P.nV) (s : Fin (P.n' v)) : P.gPos v s 1 = 1 := by
  ext a b
  by_cases h : a = b
  · subst h; simp [Places.gPos]
  · simp [Places.gPos, Matrix.one_apply_ne h]

theorem subst_one : P.subst (fun _ _ => 1) = AlgHom.id Kf P.Xsp := by
  apply MvPolynomial.algHom_ext
  rintro ⟨v, s, a, t⟩
  simp only [Places.subst, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem natAct_one : P.natAct (fun _ => 1) = LinearMap.id := by
  unfold Places.natAct
  simp only [Units.val_one, inv_one, gPos_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul,
    subst_one]
  rfl

theorem map_colSpan {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (A g : Matrix (Fin k) (Fin k) K) :
    (colSpan R g).map ((Matrix.mulVecLin A).restrictScalars R) = colSpan R (A * g) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1

def sgnEl : (levAll P).Γ := ((1 : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)), (-1 : ℤˣ))

theorem smul_sgnEl (L : P.Tup) : (levAll P).smul (sgnEl P) L = L := by
  funext v
  show (L v).map ((Matrix.mulVecLin ((1 : GL (Fin (P.m + 1)) (P.Qq v)) : Matrix _ _ (P.Qq v))).restrictScalars (P.W v)) = L v
  rw [Units.val_one, Matrix.mulVecLin_one]
  exact Submodule.map_id _

theorem actX_sgnEl : (levAll P).actX (sgnEl P) = LinearMap.id := natAct_one P

theorem chi_sgnEl : (((levAll P).χ (sgnEl P) : Oˣ) : O) = -1 := by
  show ((Int.castRingHom O : ℤ →+* O) : ℤ →* O) ((-1 : ℤˣ) : ℤ) = -1
  simp

theorem levAll_funMod (h2 : (2 : Kf) ≠ 0) (Hv : P.Tup → Submodule O P.Xsp) : (levAll P).funMod Hv = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  have h := hF.2
  rw [SetLike.mem_coe, Submodule.mem_iInf] at h
  have h' := h (sgnEl P)
  rw [Submodule.mem_iInf] at h'
  rw [Submodule.mem_bot]
  funext L
  have h3 := h' L
  rw [LinearMap.mem_ker] at h3
  simp only [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.comp_apply, smul_sgnEl, actX_sgnEl, chi_sgnEl,
    neg_smul, one_smul] at h3
  have h5 : F L - -(F L) = 0 := h3
  have h4 : (2 : Kf) • F L = 0 := by rw [two_smul, ← sub_neg_eq_add]; exact h5
  exact (smul_eq_zero.mp h4).resolve_left h2

theorem levAll_M (h2 : (2 : Kf) ≠ 0) : (levAll P).M = ⊥ := levAll_funMod P h2 _

theorem levAll_trans (L L' : P.Tup) (hL : P.IsLatTup L) (hL' : P.IsLatTup L') :
    ∃ γ : (levAll P).Γ, L' = (levAll P).smul γ L := by
  choose g hg hgL using hL
  choose g' hg' hgL' using hL'
  refine ⟨((fun v => Matrix.GeneralLinearGroup.mk'' (g' v * (g v)⁻¹) (by
    rw [Matrix.det_mul]; exact (hg' v).mul (Matrix.isUnit_nonsing_inv_det _ (hg v)))), 1), ?_⟩
  funext v
  show L' v = (L v).map ((Matrix.mulVecLin (g' v * (g v)⁻¹)).restrictScalars (P.W v))
  rw [hgL v, hgL' v, map_colSpan, Matrix.nonsing_inv_mul_cancel_right _ _ (hg v)]

theorem exists_latTup : ∃ L : P.Tup, P.IsLatTup L :=
  ⟨fun _ => colSpan _ 1, fun _ => ⟨1, by simp, rfl⟩⟩

theorem gat_M_bot (G : GAtP p) (h : ∀ c, (G.lev c).M = ⊥) : G.M = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  rw [Submodule.mem_bot]
  funext c
  have := hF c (Set.mem_univ c)
  have h1 : F c ∈ (G.lev c).M := this
  rw [h c] at h1
  exact h1

theorem gat_d_zero (G : GAtP p) (h : G.M = ⊥) : G.d = 0 := by
  unfold GAtP.d
  rw [h]
  exact finrank_bot _ _

end Formalism.MainNotions.Inhab

end
