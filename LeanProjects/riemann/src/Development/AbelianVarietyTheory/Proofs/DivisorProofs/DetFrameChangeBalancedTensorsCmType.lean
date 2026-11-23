import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogKSDiv.DetChange

open GlobalTheory.LogKSDiv
open Classical

theorem sandwich {ι κ K : Type} [Fintype ι] [DecidableEq ι] [CommRing K] (B : Matrix ι κ K) (a b : ι) (x y : κ) :
    (Matrix.transpose B * Matrix.of (fun u v => (if u = a ∧ v = b then (1 : K) else 0) + (if u = b ∧ v = a then 1 else 0)) * B) x y =
      B a x * B b y + B b x * B a y := by
  simp [Matrix.mul_apply, add_mul, mul_add, Finset.sum_add_distrib, ite_and, Finset.sum_mul, Finset.mul_sum]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hostRoot_conj_eq_neg_and_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hre0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨Complex.ext (by simp [hre0]) (by simp), ?_⟩
  intro h0
  rw [h0] at hre
  simp at hre
  exact H.d_prime.ne_zero hre

theorem emb_rt_cases (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [H.sqrt_neg_disc_sq, ← map_pow]
  have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  rw [this]; simp

theorem conj_off (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) ≠ H.rt0 := by
  obtain ⟨h1, h2⟩ := hostRoot_conj_eq_neg_and_ne_zero H
  rw [RingHom.comp_apply, h, h1]
  intro h3
  exact h2 (by linear_combination (-1/2 : ℂ) * h3)

theorem conj_on (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) = H.rt0 := by
  rcases emb_rt_cases H τ with h' | h'
  · exact absurd h' h
  · rw [RingHom.comp_apply, h', map_neg, (hostRoot_conj_eq_neg_and_ne_zero H).1, neg_neg]

theorem conj_conj_emb (τ : E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ := by
  ext x; simp

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {K : Type} [Field K]

theorem flatFrame_eq (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (a b : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    flatFrame A e e' (e a) (e' b) = Matrix.blockDiagonal' A a b := by
  simp [flatFrame]

def kronBlocks (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    Matrix (PairIx H Dw) (PairIx H Dw) K :=
  Matrix.blockDiagonal' fun τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} =>
    Matrix.kroneckerMap (· * ·) (A τ.1).transpose (A ((starRingEnd ℂ).comp τ.1)).transpose

theorem lhs_entry (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (P Q : PairIx H Dw) :
    (Matrix.transpose (flatFrame A e e') * symPair (R := K) e P * flatFrame A e e')
      (e' ⟨Q.1.1, Q.2.1⟩) (e' ⟨(starRingEnd ℂ).comp Q.1.1, Q.2.2⟩) = kronBlocks A Q P := by
  unfold symPair
  rw [sandwich, flatFrame_eq, flatFrame_eq, flatFrame_eq, flatFrame_eq]
  obtain ⟨⟨τ, hτ⟩, i, k⟩ := P
  obtain ⟨⟨σ, hσ⟩, i', k'⟩ := Q
  have hne : (starRingEnd ℂ).comp τ ≠ σ := fun h => conj_off H τ hτ (h ▸ hσ)
  dsimp only
  rw [Matrix.blockDiagonal'_apply_ne A _ _ hne, zero_mul, add_zero]
  by_cases h : τ = σ
  · subst h
    simp [kronBlocks, Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply]
  · have h' : (⟨σ, hσ⟩ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) ≠ ⟨τ, hτ⟩ := fun h2 => h (congrArg Subtype.val h2).symm
    simp [kronBlocks, Matrix.blockDiagonal'_apply_ne _ _ _ h', Matrix.blockDiagonal'_apply_ne A _ _ h]

theorem sym_entry {n' : ℕ} (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (P Q : PairIx H Dw) :
    symPair (R := K) e' P (e' ⟨Q.1.1, Q.2.1⟩) (e' ⟨(starRingEnd ℂ).comp Q.1.1, Q.2.2⟩) = if P = Q then 1 else 0 := by
  obtain ⟨⟨τ, hτ⟩, i, k⟩ := P
  obtain ⟨⟨σ, hσ⟩, i', k'⟩ := Q
  have h2 : ¬ (e' ⟨σ, i'⟩ = e' ⟨(starRingEnd ℂ).comp τ, k⟩ ∧
      e' ⟨(starRingEnd ℂ).comp σ, k'⟩ = e' ⟨τ, i⟩) := by
    rintro ⟨h, -⟩
    have h5 : σ = (starRingEnd ℂ).comp τ := congrArg Sigma.fst (e'.injective h)
    exact conj_off H τ hτ (h5 ▸ hσ)
  simp only [symPair, Matrix.of_apply, if_neg h2, add_zero, e'.apply_eq_iff_eq]
  by_cases h : τ = σ
  · subst h
    simp [Sigma.mk.inj_iff, eq_comm]
    intro h5
    exact (conj_off H τ hτ (by rw [← h5]; exact hτ)).elim
  · have h3 : ¬ (σ = τ) := Ne.symm h
    simp [h, h3]
    intro h5
    exact (conj_off H τ hτ (by rw [← h5]; exact hσ)).elim

theorem L_eq_submatrix (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K)
    (hL : ∀ j, Matrix.transpose (flatFrame A e e') * symPair (R := K) e (ε j) * flatFrame A e e' =
      ∑ k, L k j • symPair (R := K) e' (ε' k)) :
    L = (kronBlocks A).submatrix ε' ε := by
  ext a j
  have h := congrFun (congrFun (hL j) (e' ⟨(ε' a).1.1, (ε' a).2.1⟩)) (e' ⟨(starRingEnd ℂ).comp (ε' a).1.1, (ε' a).2.2⟩)
  rw [lhs_entry, Matrix.sum_apply] at h
  simp only [Matrix.smul_apply, sym_entry, smul_eq_mul, mul_ite, mul_one, mul_zero, ε'.apply_eq_iff_eq] at h
  rw [Finset.sum_ite_eq' Finset.univ a] at h
  simpa using h.symm

theorem det_kronBlocks (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    (kronBlocks A).det = ∏ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
      ((A τ.1).det ^ Dw.mult ((starRingEnd ℂ).comp τ.1) * (A ((starRingEnd ℂ).comp τ.1)).det ^ Dw.mult τ.1) := by
  rw [kronBlocks, GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod]
  simp [Matrix.det_kronecker, Matrix.det_transpose]

theorem prod_pairs (f : (E →+* ℂ) → K) :
    ∏ τ : E →+* ℂ, f τ ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) =
      ∏ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
        (f τ.1 ^ Dw.mult ((starRingEnd ℂ).comp τ.1) * f ((starRingEnd ℂ).comp τ.1) ^ Dw.mult τ.1) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0), Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr (by convert rfl) fun τ _ => ?_
    rw [if_pos τ.2, Datum.mult, if_neg (conj_off H τ.1 τ.2)]
  · symm
    refine Fintype.prod_equiv
      { toFun := fun τ => ⟨(starRingEnd ℂ).comp τ.1, conj_off H τ.1 τ.2⟩
        invFun := fun σ => ⟨(starRingEnd ℂ).comp σ.1, conj_on H σ.1 σ.2⟩
        left_inv := fun τ => Subtype.ext (conj_conj_emb τ.1)
        right_inv := fun σ => Subtype.ext (conj_conj_emb σ.1) } _ _ (fun τ => ?_)
    simp only [Equiv.coe_fn_mk]
    rw [if_neg (conj_off H τ.1 τ.2), Datum.mult, if_pos τ.2]

end GlobalTheory.LogKSDiv.DetChange

theorem GlobalTheory.LogKSDiv.det_frameChange_balanced :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (K : Type) [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (n n' : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K),
    (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := K) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
      ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := K) e' (ε' k)) →
    ∃ u : K, (u = 1 ∨ u = -1) ∧
      L.det = u * ∏ τ : E →+* ℂ, (A τ).det ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) := by
  intro E _ _ _ H Dw K _ A n n' e e' ε ε' L hL
  classical
  rw [GlobalTheory.LogKSDiv.DetChange.L_eq_submatrix A e e' ε ε' L hL]
  have hs : (GlobalTheory.LogKSDiv.DetChange.kronBlocks A).submatrix ε' ε =
      ((GlobalTheory.LogKSDiv.DetChange.kronBlocks A).submatrix ε ε).submatrix (ε'.trans ε.symm) id := by
    ext a b; simp
  refine ⟨((Equiv.Perm.sign (ε'.trans ε.symm) : ℤ) : K), ?_, ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (ε'.trans ε.symm)) with h | h <;> simp [h]
  · rw [hs, Matrix.det_permute, Matrix.det_submatrix_equiv_self, GlobalTheory.LogKSDiv.DetChange.det_kronBlocks,
      GlobalTheory.LogKSDiv.DetChange.prod_pairs]
