import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FrameAct

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

abbrev Xs (h : Fin (r + 1) → S.V) : Submodule E S.V :=
  Submodule.span E (Set.range fun a : Fin r => h a.castSucc)

theorem frameAct_castSucc_mem (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (hξ : ∀ a b, b < a → ξ a b = 0) (a : Fin r) : frameAct h ξ a.castSucc ∈ Xs h := by
  show ∑ c, ((ξ c a.castSucc : 𝓞 E) : E) • h c ∈ _
  have h0 : ((ξ (Fin.last r) a.castSucc : 𝓞 E) : E) = 0 := by
    rw [hξ _ _ (Fin.castSucc_lt_last a)]
    rfl
  rw [Fin.sum_univ_castSucc, h0, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_last_sub (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (hl : ξ (Fin.last r) (Fin.last r) = 1) : frameAct h ξ (Fin.last r) - h (Fin.last r) ∈ Xs h := by
  show ∑ c, ((ξ c (Fin.last r) : 𝓞 E) : E) • h c - h (Fin.last r) ∈ _
  have h1 : ((ξ (Fin.last r) (Fin.last r) : 𝓞 E) : E) = 1 := by
    rw [hl]
    rfl
  rw [Fin.sum_univ_castSucc, h1, one_smul, add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_mem_span (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (b : Fin (r + 1)) : frameAct h ξ b ∈ Submodule.span E (Set.range h) :=
  Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_frameAct (h : Fin (r + 1) → S.V) (ξ ξ' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) :
    frameAct (frameAct h ξ) ξ' = frameAct h (ξ * ξ') := by
  funext b
  simp only [frameAct, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  push_cast
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem frameAct_one (h : Fin (r + 1) → S.V) : frameAct h 1 = h := by
  funext b
  simp only [frameAct, Matrix.one_apply]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [hc]
  · intro hb; exact absurd (Finset.mem_univ b) hb

theorem det_unitri {n : ℕ} {R : Type*} [CommRing R] (ξ : Matrix (Fin n) (Fin n) R)
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : ξ.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => h1 i j hij)]
  simp [h2]

theorem frameAct_inv_back (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : frameAct (frameAct h ξ⁻¹) ξ = h := by
  rw [frameAct_frameAct, Matrix.nonsing_inv_mul _ (by rw [det_unitri ξ h1 h2]; exact isUnit_one),
    frameAct_one]

theorem Xs_frameAct_inv (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : Xs (frameAct h ξ⁻¹) = Xs h := by
  have hi := inv_unitri ξ h1 h2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact frameAct_castSucc_mem h _ hi.1 a
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have := frameAct_castSucc_mem (frameAct h ξ⁻¹) ξ h1 a
    rwa [frameAct_inv_back h ξ h1 h2] at this

theorem span_frameAct_inv (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    Submodule.span E (Set.range (frameAct h ξ⁻¹)) = Submodule.span E (Set.range h) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact frameAct_mem_span h _ a
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have := frameAct_mem_span (frameAct h ξ⁻¹) ξ a
    rwa [frameAct_inv_back h ξ h1 h2] at this

end FrameAct

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GZ

variable {D : D7}

theorem unitri_map (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    (∀ a b, b < a → η.map (fun x => (x : D.host.E)) a b = 0) ∧ (∀ a, η.map (fun x => (x : D.host.E)) a a = 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.map_apply, h1 a b hab]; rfl
  · rw [Matrix.map_apply, h2 a]; rfl

theorem GZ_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V) (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    GZ u (frameAct h η) = GZ u h * η.map (fun x => (x : D.host.E)) := by
  ext a b
  simp only [GZ, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, frameAct, brS, map_sum, map_smul,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem GDl_frameAct_top (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    GDl u (frameAct h η) (D.R.rS + 1) = GDl u h (D.R.rS + 1) := by
  have hm := unitri_map η h1 h2
  unfold GDl
  rw [dif_pos le_rfl, dif_pos le_rfl]
  have e : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      M.submatrix (Fin.castLE (le_refl _)) (Fin.castLE (le_refl _)) = M := fun M => by ext i j; rfl
  rw [e, e, GZ_frameAct, Matrix.det_mul, det_unitri _ hm.1 hm.2, mul_one]

theorem GDl_frameAct_r (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    GDl u (frameAct h η) D.R.rS = GDl u h D.R.rS := by
  have hm := unitri_map η h1 h2
  unfold GDl
  rw [dif_pos (Nat.le_succ _), dif_pos (Nat.le_succ _), GZ_frameAct]
  have ecs : (Fin.castLE (Nat.le_succ D.R.rS) : Fin D.R.rS → Fin (D.R.rS + 1)) = Fin.castSucc :=
    funext fun i => Fin.ext rfl
  rw [ecs]
  have e : (GZ u h * η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc =
      (GZ u h).submatrix Fin.castSucc Fin.castSucc *
      (η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
      hm.1 _ _ (Fin.castSucc_lt_last j), mul_zero, add_zero]
    rfl
  rw [e, Matrix.det_mul, det_unitri ((η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc)
    (fun a b hab => hm.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hab)) (fun a => hm.2 _), mul_one]

theorem Gom'_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    Gom' u (frameAct h η) = Gom' u h := by
  have hm := unitri_map η h1 h2
  set ηE := η.map (fun x => (x : D.host.E)) with hηE
  have hkey : ηE * (ηE.adjugate * (GZ u h).adjugate) = (GZ u h).adjugate := by
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, det_unitri _ hm.1 hm.2, one_smul, Matrix.one_mul]
  unfold Gom'
  rw [GZ_frameAct, Matrix.adjugate_mul_distrib]
  simp only [frameAct, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have := congrFun (congrFun hkey c) (Fin.last _)
  rw [Matrix.mul_apply] at this
  rw [← this]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem Gom_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    Gom u (frameAct h η) = Gom u h := by
  have hm := unitri_map η h1 h2
  set ηE := η.map (fun x => (x : D.host.E)) with hηE
  have hadj : ηE.adjugate = ηE⁻¹ := by
    rw [Matrix.inv_def, det_unitri _ hm.1 hm.2, Ring.inverse_one, one_smul]
  have hinv := inv_unitri ηE hm.1 hm.2
  unfold Gom
  rw [GZ_frameAct, Matrix.adjugate_mul_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last _), hadj, hinv.2, one_mul]
  · intro k _ hk
    rw [hadj, hinv.1 _ _ (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end GZ

end Formalism.L2.SG.Pf.ScalarFramePf
