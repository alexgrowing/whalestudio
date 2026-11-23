import Formalism.LocalToGlobal.Columns.ChainLawXiStmt
import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
import Formalism.LocalToGlobal.Columns.BlockTriangularMulVecMemPartialFlag
import Formalism.LocalToGlobal.Columns.RecLevelSym

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Pts

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem clX_ext_toLin {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) :
    ((clL_ext c κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) : Sp E (n + c) →ₗ[E] Sp E (n + c)) =
      Matrix.toLin' (ciExtM c (LinearMap.toMatrix' κ.toLinearMap)) := by
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply]
  exact clL_ext_apply c κ v

theorem clX_extM_cc {n c : ℕ} (A : Matrix (Fin n) (Fin n) E) (i j : Fin n) : ciExtM c A (Fin.castAdd c i) (Fin.castAdd c j) = A i j := by
  simp [ciExtM]

theorem clX_extM_cn {n c : ℕ} (A : Matrix (Fin n) (Fin n) E) (i : Fin n) (j : Fin c) : ciExtM c A (Fin.castAdd c i) (Fin.natAdd n j) = 0 := by
  simp [ciExtM]

theorem clX_extM_nc {n c : ℕ} (A : Matrix (Fin n) (Fin n) E) (i : Fin c) (j : Fin n) : ciExtM c A (Fin.natAdd n i) (Fin.castAdd c j) = 0 := by
  simp [ciExtM]

theorem clX_extM_nn {n c : ℕ} (A : Matrix (Fin n) (Fin n) E) (i j : Fin c) :
    ciExtM c A (Fin.natAdd n i) (Fin.natAdd n j) = if i = j then 1 else 0 := by
  simp [ciExtM, Matrix.one_apply]

theorem free_point_comp_equiv {n' c' n c : ℕ} (y : HomE E n' n) (κ : Sp E n' ≃ₗ[E] Sp E n') (t : Loc.FC n' c' n c → E) :
    Loc.xx1 (y ∘ₗ κ.toLinearMap) t = Loc.xx1 y t ∘ₗ (clL_ext c' κ).toLinearMap := by
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_comp, clX_ext_toLin, LinearMap.toMatrix'_toLin']
  unfold Loc.xx1
  rw [LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin']
  ext l s
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  refine Fin.addCases (fun s0 => ?_) (fun s1 => ?_) s
  · simp only [clX_extM_cc, clX_extM_nc, mul_zero, Finset.sum_const_zero, add_zero, Matrix.of_apply, Fin.val_castAdd]
    have hnf : ∀ m : Fin n', ¬ Loc.IsFree n' n c l.1 m.1 := fun m h => by unfold Loc.IsFree at h; omega
    rw [dif_neg (hnf s0), dif_pos s0.2]
    simp only [dif_neg (hnf _), dif_pos (Fin.is_lt _)]
    by_cases hl : l.1 < n
    · simp only [dif_pos hl, LinearMap.toMatrix'_comp, Matrix.mul_apply]
    · simp only [dif_neg hl, zero_mul, Finset.sum_const_zero]
  · simp only [clX_extM_cn, clX_extM_nn, mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply, Fin.val_natAdd]
    have hs : ¬ (n' + s1.1 < n') := by omega
    by_cases hf : Loc.IsFree n' n c l.1 (n' + s1.1)
    · rw [dif_pos hf, dif_pos hf]
    · rw [dif_neg hf, dif_neg hf, dif_neg hs, dif_neg hs]

theorem clX_ext_eN {n c : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) {s : ℕ} (hs : n ≤ s) : clL_ext c κ (Loc.eN E (n + c) s) = Loc.eN E (n + c) s := by
  rw [clL_ext_apply, ciExtM_fix]
  intro l
  unfold Loc.eN
  rw [if_neg (by simp; omega)]

theorem clX_chArg_comp {n' c' n c : ℕ} (x : HomE E (n' + c') (n + c)) (κ : Sp E n' ≃ₗ[E] Sp E n') :
    Loc.chArg (n' := n') (n := n) (c := c) (x ∘ₗ (clL_ext c' κ).toLinearMap) = Loc.chArg (n' := n') (n := n) (c := c) x := by
  unfold Loc.chArg
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [clX_ext_eN κ (by omega)]

theorem first_sum_scalar_mul {k K : Type} [CommRing k] [Field K] {n' c' n c : ℕ} (psi : k → K) (vals : Finset k) (wt : K) (a : K)
    (Φ : Loc.SF k K (n' + c') (n + c)) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt (fun x => a * Φ x) xj = a * Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Φ xj := by
  unfold Loc.E1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

theorem first_sum_source_change {K : Type} [Field K] {n' c' n c : ℕ} (psi : E → K) (vals : Finset E) (wt : K) (Φ : Loc.SF E K (n' + c') (n + c))
    (y : HomE E n' n) (κ : Sp E n' ≃ₗ[E] Sp E n') :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Φ (y ∘ₗ κ.toLinearMap) =
      Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt (fun x => Φ (x ∘ₗ (clL_ext c' κ).toLinearMap)) y := by
  unfold Loc.E1
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [free_point_comp_equiv, clX_chArg_comp]

end Pts

section Res

variable {k : Type} [CommRing k]

theorem clX_ent_fin {n c : ℕ} (φ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (a : ℕ → ℕ → k)
    (h : ∀ l s, l < n + c → s < n + c → Loc.atN (φ (Loc.eN k (n + c) s)) l = if l < n ∧ s < n then a l s else if l = s then 1 else 0)
    (l s : Fin (n + c)) : φ (Pi.single s 1) l = if l.1 < n ∧ s.1 < n then a l.1 s.1 else if l = s then 1 else 0 := by
  have h1 := h l.1 s.1 l.2 s.2
  rw [residue_basisVec_eq_single s.2] at h1
  unfold Loc.atN at h1
  rw [dif_pos l.2] at h1
  rw [h1]
  by_cases h2 : l.1 < n ∧ s.1 < n
  · rw [if_pos h2, if_pos h2]
  · rw [if_neg h2, if_neg h2]
    by_cases h3 : l = s
    · rw [if_pos h3, if_pos (congrArg Fin.val h3)]
    · rw [if_neg h3, if_neg (fun h4 => h3 (Fin.ext h4))]

theorem clX_fix_of_ent {n c : ℕ} (φ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (a : ℕ → ℕ → k)
    (h : ∀ l s, l < n + c → s < n + c → Loc.atN (φ (Loc.eN k (n + c) s)) l = if l < n ∧ s < n then a l s else if l = s then 1 else 0) :
    (∀ v (j : Fin c), φ v (Fin.natAdd n j) = v (Fin.natAdd n j)) ∧
    (∀ s, n ≤ s → φ (Loc.eN k (n + c) s) = Loc.eN k (n + c) s) ∧
    (∀ v (l : Fin n), φ v (Fin.castAdd c l) = ∑ m : Fin n, a l.1 m.1 * v (Fin.castAdd c m)) := by
  have hent := clX_ent_fin φ a h
  refine ⟨fun v j => ?_, fun s hs => ?_, fun v l => ?_⟩
  · rw [residue_linearEquiv_apply_eq_sum, Fin.sum_univ_add]
    have e1 : ∀ m : Fin n, φ (Pi.single (Fin.castAdd c m) 1) (Fin.natAdd n j) = 0 := by
      intro m
      rw [hent, if_neg (by simp), if_neg (fun h' => by have := congrArg Fin.val h'; simp at this; omega)]
    have e2 : ∀ m : Fin c, φ (Pi.single (Fin.natAdd n m) 1) (Fin.natAdd n j) = if j = m then 1 else 0 := by
      intro m
      rw [hent, if_neg (by simp)]
      by_cases hm : j = m
      · rw [hm, if_pos rfl, if_pos rfl]
      · rw [if_neg hm, if_neg (fun h' => hm (Fin.ext (by have := congrArg Fin.val h'; simp at this; exact this)))]
    simp only [e1, e2, zero_mul, Finset.sum_const_zero, zero_add, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · funext l
    rw [residue_linearEquiv_apply_eq_sum]
    by_cases hsN : s < n + c
    · rw [Finset.sum_eq_single (⟨s, hsN⟩ : Fin (n + c))]
      · rw [hent, if_neg (fun h' => by simp at h'; omega)]
        unfold Loc.eN
        by_cases hl : l = ⟨s, hsN⟩
        · subst hl
          simp
        · rw [if_neg hl, zero_mul, if_neg (fun h' => hl (Fin.ext h'))]
      · intro b _ hb
        unfold Loc.eN
        rw [if_neg (fun h' => hb (Fin.ext h')), mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · have h0 : Loc.eN k (n + c) s = 0 := by
        funext l'
        unfold Loc.eN
        rw [if_neg (by omega)]
        rfl
      rw [h0]
      simp
  · rw [residue_linearEquiv_apply_eq_sum, Fin.sum_univ_add]
    have e1 : ∀ m : Fin n, φ (Pi.single (Fin.castAdd c m) 1) (Fin.castAdd c l) = a l.1 m.1 := by
      intro m
      rw [hent, if_pos ⟨by simp, by simp⟩]
      simp
    have e2 : ∀ m : Fin c, φ (Pi.single (Fin.natAdd n m) 1) (Fin.castAdd c l) = 0 := by
      intro m
      rw [hent, if_neg (by simp), if_neg (fun h' => by have := congrArg Fin.val h'; simp at this; omega)]
    simp only [e1, e2, zero_mul, Finset.sum_const_zero, add_zero]

theorem clX_R1cond {n c : ℕ} (φ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (hfix : ∀ v (j : Fin c), φ v (Fin.natAdd n j) = v (Fin.natAdd n j))
    (hvec : ∀ s, n ≤ s → φ (Loc.eN k (n + c) s) = Loc.eN k (n + c) s) : Loc.R1cond k n c φ := by
  refine ⟨fun i v hv => ?_, hvec n le_rfl, fun i => ?_⟩
  · intro l hl
    have hl' : ¬ l.1 < n := fun h' => hl (show l.1 < n + i by omega)
    obtain ⟨j, rfl⟩ : ∃ j : Fin c, Fin.natAdd n j = l := ⟨⟨l.1 - n, by omega⟩, Fin.ext (by simp; omega)⟩
    rw [hfix]
    exact hv _ hl
  · rw [hvec (n + i) (by omega), sub_self]
    exact zero_mem _

end Res

section Assemble

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem xi_first_law_of_target {i : ℕ} (hs : cst.sharp = true) (hT : XiTgtLaw Ch sel mu cst i)
    (hΦ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → PhiGSLaw P.1 (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t (i + 1) (cOf R i) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1))) :
    FirstUnfoldingJInvarianceLaw Ch sel mu cst i := by
  intro P hP κ κ' hκ hκ' hκh hκh' y
  have hPhi : PhiAt Ch mu cst.sharp i P.1 = LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t (i + 1) (cOf R i) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1)) := by
    unfold PhiAt
    rw [if_pos hP, hs, if_pos rfl]
  have hE : ∀ z, E1at Ch sel mu cst i P 1 1 z =
      Loc.om (muAt Ch sel mu cst i P) (LocE.vP P.1 (qOf P.1)) (cst.sq P) (1 : AutY X R i) (1 : AutY X R (i + 1)) (fun _ => (1 : X.K)) 0 *
        Loc.E1 (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1)) (cst.psi P) (LocE.valsQ X.E (qOf P.1) cst.A cst.B)
          (((qOf P.1 : X.K) ^ cst.B)⁻¹) (PhiAt Ch mu cst.sharp i P.1) z := by
    intro z
    unfold E1at omPhi
    rw [firstUnfolding_omega_factor]
    rfl
  have hγ : clL_ext (cOf R (i + 1)) κ'.symm ∈ LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N (i + 1)) (cOf R (i + 1)) := by
    rw [← clL_ext_symm]
    exact Subgroup.inv_mem _ hκh'
  have hlaw := hΦ P hP _ hγ _ hκh
  have hsub : i + 1 - 1 = i := Nat.add_sub_cancel i 1
  rw [hsub] at hlaw
  rw [hE, hE, hT P hP κ' hκ' hκh' (y ∘ₗ κ.toLinearMap), first_sum_source_change]
  have hfun : (fun x => PhiAt Ch mu cst.sharp i P.1 ((clL_ext (cOf R (i + 1)) κ'.symm).toLinearMap ∘ₗ (x ∘ₗ (clL_ext (cOf R i) κ).toLinearMap))) =
      fun x => (LocE.lamGBS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.r R.t (i + 1) (R.N (i + 1)) (cOf R (i + 1))
            (clL_ext (cOf R (i + 1)) κ'.symm).toLinearMap *
          (LocE.unitV (chiP Ch P.1 i) ((LinearEquiv.det κ'.symm : X.Eˣ) : X.E))⁻¹ *
          (LocE.lamGBS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.r R.t i (R.N i) (cOf R i) (clL_ext (cOf R i) κ).toLinearMap *
            (LocE.unitV (chiP Ch P.1 i) ((LinearEquiv.det κ : X.Eˣ) : X.E))⁻¹)) * PhiAt Ch mu cst.sharp i P.1 x := by
    funext x
    rw [hPhi, ← clL_ext_det (cOf R (i + 1)) κ'.symm, ← clL_ext_det (cOf R i) κ]
    exact hlaw x
  rw [hfun, first_sum_scalar_mul]
  ring

end Assemble

section Deep

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

def clX_cstA (cst : LocCst X (rowSG Pr sel mu)) (A' : ℕ) : LocCst X (rowSG Pr sel mu) := { cst with A := max cst.A A' }

end Deep

end Formalism.L2.Col
