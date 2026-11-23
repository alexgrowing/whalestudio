import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SqChar
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Branch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeylNumeratorLaplace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSubMulNegMulOfNormOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjDiagonal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LaplaceChar

open ReciprocityTheory.ChartRestriction.TR.Weyl

theorem exists_mul_eq_mul_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ)
    (ht : Function.Injective t) (hA : A.charpoly = ∏ i, (X - C (t i))) :
    ∃ P : GL (Fin n) ℂ, A * (P : Matrix (Fin n) (Fin n) ℂ) = (P : Matrix (Fin n) (Fin n) ℂ) * diagonal t := by
  first
  | exact @_root_.GlobalTheory.DiagonalConjugateExistence.exists_conj_diagonal
  | exact _root_.GlobalTheory.DiagonalConjugateExistence.exists_conj_diagonal
  | (apply _root_.GlobalTheory.DiagonalConjugateExistence.exists_conj_diagonal <;> assumption)
  | (intros; apply _root_.GlobalTheory.DiagonalConjugateExistence.exists_conj_diagonal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DiagonalConjugateExistence.exists_conj_diagonal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DiagonalConjugateExistence.exists_conj_diagonal ..)

theorem chAt_prod_eq_gtChar {n : ℕ} (lam : DomWeight n) (t : Fin n → ℂ) (ht : Function.Injective t)
    (h0 : ∀ i, t i ≠ 0) : chAt lam (∏ i, (X - C (t i))) = gtChar n lam.w t := by
  have hdet : IsUnit (diagonal t) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => h0 i)
  have hex : ∃ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ).charpoly = ∏ i, (X - C (t i)) :=
    ⟨hdet.unit, by simp [charpoly_diagonal]⟩
  unfold chAt
  rw [dif_pos hex]
  obtain ⟨P, hP⟩ := exists_mul_eq_mul_diagonal _ t ht hex.choose_spec
  set g := hex.choose
  let D : GL (Fin n) ℂ := P⁻¹ * g * P
  have hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal t := by
    show ((P⁻¹ * g * P : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = diagonal t
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hP, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have hgD : g = P * D * P⁻¹ := by simp [D, mul_assoc]
  obtain ⟨f, hf, htr⟩ := sqChar n lam D t hD
  have hfD : f = GlobalTheory.Branching.sqRep ℂ n lam D :=
    LinearMap.ext fun x => Subtype.ext (by rw [hf, GlobalTheory.Branching.sqRep_coe])
  have e : GlobalTheory.Branching.sqRep ℂ n lam (P * D * P⁻¹) =
      GlobalTheory.Branching.sqRep ℂ n lam P * (GlobalTheory.Branching.sqRep ℂ n lam D * GlobalTheory.Branching.sqRep ℂ n lam P⁻¹) := by
    rw [map_mul, map_mul, mul_assoc]
  have e2 : GlobalTheory.Branching.sqRep ℂ n lam P⁻¹ * GlobalTheory.Branching.sqRep ℂ n lam P = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [← htr, hfD, hgD, e, LinearMap.trace_mul_comm, mul_assoc, e2, mul_one]

theorem exists_eq_prod_X_sub_C : ∀ (a : ℕ) (Q : ℂ[X]), Q.Monic → Q.natDegree = a →
    ∃ α : Fin a → ℂ, Q = ∏ i, (X - C (α i))
  | 0, Q, hm, hd => ⟨Fin.elim0, by rw [Fin.prod_univ_zero]; exact Polynomial.eq_one_of_monic_natDegree_zero hm hd⟩
  | a + 1, Q, hm, hd => by
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root Q (by
      rw [degree_eq_natDegree hm.ne_zero, hd]; exact_mod_cast Nat.succ_ne_zero a)
    have hdiv : (X - C r) * (Q /ₘ (X - C r)) = Q := mul_divByMonic_eq_iff_isRoot.mpr hr
    have hm' : (Q /ₘ (X - C r)).Monic := (monic_X_sub_C r).of_mul_monic_left (by rw [hdiv]; exact hm)
    have hd' : (Q /ₘ (X - C r)).natDegree = a := by
      rw [natDegree_divByMonic _ (monic_X_sub_C r), hd, natDegree_X_sub_C]; rfl
    obtain ⟨α, hα⟩ := exists_eq_prod_X_sub_C a _ hm' hd'
    refine ⟨Fin.cons r α, ?_⟩
    rw [Fin.prod_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [← hα, hdiv]

theorem wden_addCases (a b : ℕ) (α : Fin a → ℂ) (β : Fin b → ℂ) :
    wden (a + b) (Fin.addCases α β) = wden a α * wden b β * ∏ i, ∏ j, (α i - β j) := by
  unfold wden
  simp only [Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right, Finset.prod_mul_distrib]
  have h1 : ∀ i j : Fin a, (Fin.castAdd b i < Fin.castAdd b j) ↔ i < j := fun i j => Iff.rfl
  have h2 : ∀ (i : Fin a) (j : Fin b), Fin.castAdd b i < Fin.natAdd a j := fun i j => by
    show (i : ℕ) < a + (j : ℕ); omega
  have h3 : ∀ (i : Fin b) (j : Fin a), ¬ Fin.natAdd a i < Fin.castAdd b j := fun i j => by
    show ¬ (a + (i : ℕ) < (j : ℕ)); omega
  have h4 : ∀ i j : Fin b, (Fin.natAdd a i < Fin.natAdd a j) ↔ i < j := fun i j => by
    show a + (i : ℕ) < a + (j : ℕ) ↔ (i : ℕ) < j; omega
  simp only [h1, h2, h3, h4, if_true, if_false, Finset.prod_const_one, mul_one]
  ring

theorem le_sub_of_strictMono {a n : ℕ} (p : Fin a → Fin n) (hp : StrictMono p) :
    ∀ (d : ℕ) (k k' : Fin a), (k' : ℕ) = k + d → (p k : ℤ) + d ≤ p k'
  | 0, k, k', h => by
    have : k = k' := Fin.ext (by omega)
    subst this; simp
  | d + 1, k, k', h => by
    have hk : (k : ℕ) + d < a := by omega
    have ih := le_sub_of_strictMono p hp d k ⟨k + d, hk⟩ rfl
    have hlt : p ⟨k + d, hk⟩ < p k' := hp (by rw [Fin.lt_iff_val_lt_val]; simp; omega)
    rw [Fin.lt_iff_val_lt_val] at hlt
    push_cast
    omega

end GlobalTheory.LaplaceChar

noncomputable section

namespace GlobalTheory.LaplaceChar

open ReciprocityTheory.ChartRestriction.TR.Weyl

theorem conj_eq_inv_of_norm_one {x : ℂ} (hx : ‖x‖ = 1) : (starRingEnd ℂ) x = x⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hx]; simp

theorem resultant_prod {a b : ℕ} (α : Fin a → ℂ) (β : Fin b → ℂ) :
    resultant (∏ i, (X - C (α i))) (∏ j, (X - C (β j))) = ∏ i, ∏ j, (α i - β j) := by
  have hm : (∏ i, (X - C (α i))).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hroots : (∏ i, (X - C (α i))).roots = Finset.univ.val.map α := by
    rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map α), Multiset.map_map]
    rfl
  rw [resultant_eq_prod_eval _ _ _ le_rfl (IsAlgClosed.splits _), hm.leadingCoeff, one_pow, one_mul, hroots,
    Multiset.map_map]
  show (Finset.univ.val.map fun i => eval (α i) (∏ j, (X - C (β j)))).prod = _
  rw [← Finset.prod_eq_multiset_prod]
  simp [eval_prod]

theorem delta_apply (n : ℕ) (j : Fin n) : delta n j = (n : ℤ) - 1 - (j : ℕ) := rfl

theorem antitone_select {n m : ℕ} (lam : DomWeight n) (p : Fin m → Fin n) (hp : StrictMono p) :
    Antitone fun k : Fin m => (lam.w + delta n) (p k) - delta m k := by
  intro k k' hkk'
  have hd := le_sub_of_strictMono p hp ((k' : ℕ) - k) k k' (by rw [Fin.le_iff_val_le_val] at hkk'; omega)
  have hw : lam.w (p k') ≤ lam.w (p k) := lam.anti (hp.monotone hkk')
  rw [Fin.le_iff_val_le_val] at hkk'
  simp only [Pi.add_apply, delta_apply]
  push_cast [Nat.cast_sub hkk'] at hd ⊢
  omega

def selW {n m : ℕ} (lam : DomWeight n) (p : Fin m → Fin n) (hp : StrictMono p) (c : ℤ) : DomWeight m where
  w := fun k => (lam.w + delta n) (p k) - delta m k + c
  anti := fun k k' h => by
    have := antitone_select lam p hp h
    simp only at this ⊢
    omega

end GlobalTheory.LaplaceChar

noncomputable section

namespace GlobalTheory.LaplaceChar

open ReciprocityTheory.ChartRestriction.TR.Weyl

def selL {a b : ℕ} (J : {J : Finset (Fin (a + b)) // J.card = a}) : Fin a → Fin (a + b) :=
  J.1.orderEmbOfFin J.2

def selR {a b : ℕ} (J : {J : Finset (Fin (a + b)) // J.card = a}) : Fin b → Fin (a + b) :=
  J.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, J.2]; simp)

theorem selL_strictMono {a b : ℕ} (J : {J : Finset (Fin (a + b)) // J.card = a}) : StrictMono (selL J) :=
  (J.1.orderEmbOfFin J.2).strictMono

theorem selR_strictMono {a b : ℕ} (J : {J : Finset (Fin (a + b)) // J.card = a}) : StrictMono (selR J) :=
  (J.1ᶜ.orderEmbOfFin _).strictMono

theorem map_orderEmbOfFin {n k : ℕ} (s : Finset (Fin n)) (h : s.card = k) (F : Fin n → ℂ) :
    (Finset.univ.val.map fun i : Fin k => F (s.orderEmbOfFin h i)) = s.val.map F := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ s h]
  rw [Finset.map_val, Multiset.map_map]
  rfl

theorem val_add_compl {n : ℕ} (s : Finset (Fin n)) : s.val + sᶜ.val = (Finset.univ : Finset (Fin n)).val := by
  rw [← Finset.union_compl s, ← Finset.disjUnion_eq_union s sᶜ disjoint_compl_right]
  rfl

end GlobalTheory.LaplaceChar

open GlobalTheory.LaplaceChar ReciprocityTheory.ChartRestriction.TR.Weyl in

theorem GlobalTheory.character_laplace_factorisation : ∀ (a b : ℕ) (lam : DomWeight (a + b)) (e : ℤ), Odd e → ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → DomWeight a) (l₂ : ι → DomWeight b) (ε : ι → ℂ), (∀ j, (infOfWeight (l₁ j)).map (· + (b : ℂ) * e / 2) + (infOfWeight (l₂ j)).map (· + (a : ℂ) * e / 2) = infOfWeight lam) ∧ ∀ Q₁ Q₂ : ℂ[X], Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → (∀ z ∈ (Q₁ * Q₂).roots, ‖z‖ = 1) → ((resultant Q₁ Q₂ / (‖resultant Q₁ Q₂‖ : ℂ)) ^ e * ‖resultant Q₁ Q₂‖) * (starRingEnd ℂ) (chAt lam (Q₁ * Q₂)) = ∑ j, ε j * (starRingEnd ℂ) (chAt (l₁ j) Q₁) * (starRingEnd ℂ) (chAt (l₂ j) Q₂) := by
  intro a b lam e he
  obtain ⟨m, rfl⟩ := he
  set K : ℤ := m + 1 with hK
  refine ⟨{J : Finset (Fin (a + b)) // J.card = a}, inferInstance,
    fun J => selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K),
    fun J => selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K),
    fun J => (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) * ((-1 : ℂ) ^ (a * b)) ^ K, ?_, ?_⟩
  · intro J
    beta_reduce
    let F : Fin (a + b) → ℂ := fun j => (lam.w j : ℂ) + ((((a + b : ℕ) : ℂ) - 1) / 2 - ((j : ℕ) : ℂ))
    have hL : (infOfWeight (selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K))).map
        (· + (b : ℂ) * ((2 * m + 1 : ℤ) : ℂ) / 2) = J.1.val.map F := by
      rw [← map_orderEmbOfFin J.1 J.2 F]
      unfold infOfWeight
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun k _ => ?_
      simp only [Function.comp_apply, selW, selL, F, Pi.add_apply, delta_apply, hK]
      push_cast
      ring
    have hR : (infOfWeight (selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K))).map
        (· + (a : ℂ) * ((2 * m + 1 : ℤ) : ℂ) / 2) = J.1ᶜ.val.map F := by
      rw [← map_orderEmbOfFin J.1ᶜ (k := b) (by rw [Finset.card_compl, J.2]; simp) F]
      unfold infOfWeight
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun k _ => ?_
      simp only [Function.comp_apply, selW, selR, F, Pi.add_apply, delta_apply, hK]
      push_cast
      ring
    rw [hL, hR, ← Multiset.map_add, val_add_compl]
    rfl
  · intro Q₁ Q₂ h1 h2 hd1 hd2 hsep hroot
    beta_reduce
    obtain ⟨α, rfl⟩ := exists_eq_prod_X_sub_C a Q₁ h1 hd1
    obtain ⟨β, rfl⟩ := exists_eq_prod_X_sub_C b Q₂ h2 hd2
    have hprod : (∏ i, (X - C (α i))) * ∏ j, (X - C (β j)) = ∏ i, (X - C (Fin.addCases α β i)) := by
      rw [Fin.prod_univ_add]; simp
    rw [hprod] at hsep hroot ⊢
    have htinj : Function.Injective (Fin.addCases α β : Fin (a + b) → ℂ) := separable_prod_X_sub_C_iff.mp hsep
    have hmon : (∏ i, (X - C ((Fin.addCases α β : Fin (a + b) → ℂ) i))).Monic :=
      monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
    have htn : ∀ i, ‖(Fin.addCases α β : Fin (a + b) → ℂ) i‖ = 1 := fun i => hroot _ (by
      rw [mem_roots hmon.ne_zero, IsRoot, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
    have ht0 : ∀ i, (Fin.addCases α β : Fin (a + b) → ℂ) i ≠ 0 := fun i h => by simpa [h] using htn i
    have hα : ∀ i, ‖α i‖ = 1 := fun i => by simpa using htn (Fin.castAdd b i)
    have hβ : ∀ j, ‖β j‖ = 1 := fun j => by simpa using htn (Fin.natAdd a j)
    have hα0 : ∀ i, α i ≠ 0 := fun i h => by simpa [h] using hα i
    have hβ0 : ∀ j, β j ≠ 0 := fun j h => by simpa [h] using hβ j
    have hαinj : Function.Injective α := fun i j h =>
      Fin.castAdd_injective _ _ (htinj (by simpa using h))
    have hβinj : Function.Injective β := fun i j h =>
      Fin.natAdd_injective _ _ (htinj (by simpa using h))
    have hne : ∀ i j, α i ≠ β j := fun i j h => by
      have := htinj (show (Fin.addCases α β : Fin (a + b) → ℂ) (Fin.castAdd b i) = Fin.addCases α β (Fin.natAdd a j) by
        simpa using h)
      have := congrArg Fin.val this
      simp at this
      omega
    rw [chAt_prod_eq_gtChar lam _ htinj ht0]
    simp only [chAt_prod_eq_gtChar _ α hαinj hα0, chAt_prod_eq_gtChar _ β hβinj hβ0]
    rw [resultant_prod α β]
    have hph := GlobalTheory.resultant_phase_unit_circle a b α β hα hβ hne K
    simp only at hph
    rw [show (2 * m + 1 : ℤ) = 2 * K - 1 by rw [hK]; ring, hph]
    set R := ∏ i, ∏ j, (α i - β j) with hRdef

    have hW := weylGT ℂ (a + b) lam.w lam.anti _ ht0
    rw [wden_addCases] at hW
    let α' : Fin a → ℂˣ := fun i => Units.mk0 (α i) (hα0 i)
    let β' : Fin b → ℂˣ := fun j => Units.mk0 (β j) (hβ0 j)
    have hLap := GlobalTheory.weylNumerator_laplace a b α' β' (lam.w + delta (a + b))
    have hLHS : alt (a + b) (lam.w + delta (a + b)) (Fin.addCases α β) =
        (Matrix.of fun i j : Fin (a + b) => (((Fin.addCases α' β' i : ℂˣ) ^ (lam.w + delta (a + b)) j : ℂˣ) : ℂ)).det := by
      unfold alt
      congr 1
      ext i j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [α', β', Units.val_zpow_eq_zpow_val]
    have hA : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        (Matrix.of fun i k : Fin a => ((α' i ^ (lam.w + delta (a + b)) (J.1.orderEmbOfFin J.2 k) : ℂˣ) : ℂ)).det =
          wden a α * gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α := by
      intro J
      rw [weylGT ℂ a _ (antitone_select lam (selL J) (selL_strictMono J)) α hα0]
      unfold alt
      congr 1
      ext i k
      simp [α', Units.val_zpow_eq_zpow_val, selL]
    have hB : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        (Matrix.of fun i k : Fin b => ((β' i ^ (lam.w + delta (a + b))
            (J.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, J.2]; simp) k) : ℂˣ) : ℂ)).det =
          wden b β * gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β := by
      intro J
      rw [weylGT ℂ b _ (antitone_select lam (selR J) (selR_strictMono J)) β hβ0]
      unfold alt
      congr 1
      ext i k
      simp [β', Units.val_zpow_eq_zpow_val, selR]
    rw [hLHS, hLap] at hW
    simp only [hA, hB] at hW
    rw [← hRdef] at hW
    have hwden : ∀ {c : ℕ} (x : Fin c → ℂ), Function.Injective x → wden c x ≠ 0 := by
      intro c x hx
      unfold wden
      refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
      split_ifs with h
      · exact sub_ne_zero.mpr (hx.ne h.ne)
      · exact one_ne_zero
    have key : R * gtChar (a + b) lam.w (fun i => Fin.addCases α β i) =
        ∑ J : {J : Finset (Fin (a + b)) // J.card = a}, (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) *
          gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α *
          gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β := by
      apply mul_left_cancel₀ (mul_ne_zero (hwden α hαinj) (hwden β hβinj))
      rw [← mul_assoc, hW, Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring
    have hc := congrArg (starRingEnd ℂ) key
    simp only [map_mul, map_sum, map_pow, map_neg, map_one] at hc
    have hsA : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        gtChar a (selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K)).w α =
          (∏ i, α i) ^ (-(b : ℤ) * K) * gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α :=
      fun J => sq_gt_shift a _ _ α hα0
    have hsB : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        gtChar b (selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K)).w β =
          (∏ j, β j) ^ (-(a : ℤ) * K) * gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β :=
      fun J => sq_gt_shift b _ _ β hβ0
    have hPα : ‖∏ i, α i‖ = 1 := by rw [norm_prod]; simp [hα]
    have hPβ : ‖∏ j, β j‖ = 1 := by rw [norm_prod]; simp [hβ]
    have cA : (starRingEnd ℂ) ((∏ i, α i) ^ (-(b : ℤ) * K)) = ((∏ i, α i) ^ b) ^ K := by
      rw [map_zpow₀, conj_eq_inv_of_norm_one hPα, _root_.inv_zpow', neg_mul, neg_neg, _root_.zpow_mul, zpow_natCast]
    have cB : (starRingEnd ℂ) ((∏ j, β j) ^ (-(a : ℤ) * K)) = ((∏ j, β j) ^ a) ^ K := by
      rw [map_zpow₀, conj_eq_inv_of_norm_one hPβ, _root_.inv_zpow', neg_mul, neg_neg, _root_.zpow_mul, zpow_natCast]
    simp only [hsA, hsB, map_mul, cA, cB]
    calc (starRingEnd ℂ) R * ((-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ K *
          (starRingEnd ℂ) (gtChar (a + b) lam.w fun i => Fin.addCases α β i)
        = ((-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ K *
          ((starRingEnd ℂ) R * (starRingEnd ℂ) (gtChar (a + b) lam.w fun i => Fin.addCases α β i)) := by ring
      _ = _ := by
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [_root_.mul_zpow, _root_.mul_zpow]
        ring
