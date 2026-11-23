import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg.NF

theorem exists_radical_basis {K : Type*} [Field K] {r : ℕ} (B : Matrix (Fin r) (Fin r) K)
    (hd : B.det = 0) :
    ∃ (t k : ℕ) (e : Module.Basis (Fin t ⊕ Fin k) K (Fin r → K)), 0 < k ∧
      (∀ j, B *ᵥ e (Sum.inr j) = 0) ∧
      (∀ w : Fin t → K, B *ᵥ (∑ j, w j • e (Sum.inl j)) = 0 → w = 0) := by
  obtain ⟨N, hN⟩ : ∃ N : Submodule K (Fin r → K), N = LinearMap.ker B.mulVecLin := ⟨_, rfl⟩
  have hmemN : ∀ v, v ∈ N ↔ B *ᵥ v = 0 := fun v => by
    rw [hN, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl N
  obtain ⟨bN⟩ : Nonempty (Module.Basis (Fin (Module.finrank K N)) K N) := ⟨Module.finBasis K N⟩
  obtain ⟨bC⟩ : Nonempty (Module.Basis (Fin (Module.finrank K C)) K C) := ⟨Module.finBasis K C⟩
  obtain ⟨e, he⟩ : ∃ e : Module.Basis (Fin (Module.finrank K C) ⊕ Fin (Module.finrank K N)) K (Fin r → K),
      e = (bC.prod bN).map (Submodule.prodEquivOfIsCompl C N hC.symm) := ⟨_, rfl⟩
  have he_inl : ∀ j, e (Sum.inl j) = (bC j : Fin r → K) := fun j => by
    rw [he, Module.Basis.map_apply, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  have he_inr : ∀ j, e (Sum.inr j) = (bN j : Fin r → K) := fun j => by
    rw [he, Module.Basis.map_apply, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  refine ⟨Module.finrank K C, Module.finrank K N, e, ?_, ?_, ?_⟩
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨v, (hmemN v).mpr hv⟩, fun h => hv0 ?_⟩
    simpa using congrArg Subtype.val h
  · intro j
    rw [he_inr]
    exact (hmemN _).mp (bN j).2
  · intro w hw
    simp only [he_inl] at hw
    have hc : ((∑ j, w j • bC j : C) : Fin r → K) = ∑ j, w j • (bC j : Fin r → K) := by
      simp
    have hNmem : ((∑ j, w j • bC j : C) : Fin r → K) ∈ N := by
      rw [hmemN, hc]
      exact hw
    have h0 : ((∑ j, w j • bC j : C) : Fin r → K) = 0 :=
      Submodule.disjoint_def.mp hC.disjoint _ hNmem (Submodule.coe_mem _)
    funext j
    exact Fintype.linearIndependent_iff.mp bC.linearIndependent w (Submodule.coe_eq_zero.mp h0) j

theorem exists_blockNF {K : Type*} [Field K] (s : K →+* K) (hs : ∀ x, s (s x) = x) {r : ℕ}
    (B : Matrix (Fin r) (Fin r) K) (hB : (B.map s)ᵀ = B) (hd : B.det = 0) :
    ∃ (P : Matrix (Fin r) (Fin r) K) (t : ℕ) (h : t < r), P.det ≠ 0 ∧
      (∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → ((P.map s)ᵀ * B * P) i j = 0) ∧
      (((P.map s)ᵀ * B * P).submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0 := by
  obtain ⟨t, k, e, hk, hker, hinj⟩ := exists_radical_basis B hd
  have hcard : t + k = r := by
    have h1 := Module.finrank_eq_card_basis e
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
    exact h1.symm
  subst hcard
  have ht : t < t + k := Nat.lt_add_of_pos_right hk
  have hsplit : ∀ c : Fin t ⊕ Fin k, (∃ i', c = Sum.inl i') ∨ ∃ i', c = Sum.inr i' := by
    rintro (i' | i')
    · exact Or.inl ⟨i', rfl⟩
    · exact Or.inr ⟨i', rfl⟩
  have hinr : ∀ i : Fin (t + k), t ≤ i.1 → ∃ i', finSumFinEquiv.symm i = Sum.inr i' := by
    intro i hi
    rcases hsplit (finSumFinEquiv.symm i) with ⟨i', hc⟩ | ⟨i', hc⟩
    · exfalso
      have h1 : finSumFinEquiv (finSumFinEquiv.symm i) = i := finSumFinEquiv.apply_symm_apply i
      rw [hc, finSumFinEquiv_apply_left] at h1
      have h2 : i.1 = i'.1 := (congrArg Fin.val h1).symm
      have h3 := i'.isLt
      omega
    · exact ⟨i', hc⟩
  have hcast : ∀ j : Fin t, finSumFinEquiv.symm (Fin.castLE ht.le j) = Sum.inl j := by
    intro j
    have h1 : Fin.castLE ht.le j = Fin.castAdd k j := Fin.ext rfl
    rw [h1, finSumFinEquiv_symm_apply_castAdd]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin (t + k)) (Fin (t + k)) K,
      ∀ a b, P a b = e (finSumFinEquiv.symm b) a :=
    ⟨Matrix.of fun a b => e (finSumFinEquiv.symm b) a, fun _ _ => rfl⟩
  have hBab : ∀ a b, s (B b a) = B a b := fun a b => by
    simpa using congrFun (congrFun hB a) b
  have hentry : ∀ i j, ((P.map s)ᵀ * B * P) i j =
      (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ (B *ᵥ e (finSumFinEquiv.symm j)) := by
    intro i j
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
      Matrix.map_apply, hP]
  have hrow : ∀ i' : Fin k, Matrix.vecMul (fun a => s (e (Sum.inr i') a)) B = 0 := by
    intro i'
    ext b
    have h0 : (B *ᵥ e (Sum.inr i')) b = 0 := by rw [hker i', Pi.zero_apply]
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    calc ∑ a, s (e (Sum.inr i') a) * B a b = ∑ a, s (B b a * e (Sum.inr i') a) :=
          Finset.sum_congr rfl fun a _ => by rw [map_mul, hBab, mul_comm]
      _ = s (∑ a, B b a * e (Sum.inr i') a) := (map_sum s _ _).symm
      _ = s ((B *ᵥ e (Sum.inr i')) b) := rfl
      _ = 0 := by rw [h0, map_zero]
  have hzero : ∀ i j : Fin (t + k), (t ≤ i.1 ∨ t ≤ j.1) → ((P.map s)ᵀ * B * P) i j = 0 := by
    intro i j hij
    rw [hentry]
    rcases hij with hi | hj
    · obtain ⟨i', hi'⟩ := hinr i hi
      rw [hi', Matrix.dotProduct_mulVec, hrow i', zero_dotProduct]
    · obtain ⟨j', hj'⟩ := hinr j hj
      rw [hj', hker j', dotProduct_zero]
  have hli : LinearIndependent K (fun b => e (finSumFinEquiv.symm b)) :=
    e.linearIndependent.comp _ finSumFinEquiv.symm.injective
  have hmv : ∀ v : Fin (t + k) → K, P *ᵥ v = ∑ b, v b • e (finSumFinEquiv.symm b) := by
    intro v
    ext a
    simp [Matrix.mulVec, dotProduct, hP, Finset.sum_apply, mul_comm]
  have hPdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv0
    funext b
    exact Fintype.linearIndependent_iff.mp hli v (by rw [← hmv v]; exact hv) b
  have hPs : ((P.map s)ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero s).mpr hPdet
  have hTy : ∀ i (y : Fin (t + k) → K),
      ((P.map s)ᵀ *ᵥ y) i = (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ y := by
    intro i y
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, hP]
  refine ⟨P, t, ht, hPdet, hzero, ?_⟩
  intro hB0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hB0
  apply hw0
  apply hinj w
  obtain ⟨u, hu⟩ : ∃ u : Fin (t + k) → K, u = ∑ j, w j • e (Sum.inl j) := ⟨_, rfl⟩
  rw [← hu]
  have hexp : ∀ i, (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ (B *ᵥ u) =
      ∑ j, ((P.map s)ᵀ * B * P) i (Fin.castLE ht.le j) * w j := by
    intro i
    rw [hu, Matrix.mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, hentry, hcast, mul_comm]
  by_contra hBu
  apply hPs
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨B *ᵥ u, hBu, ?_⟩
  funext i
  rw [hTy, Pi.zero_apply]
  rcases hsplit (finSumFinEquiv.symm i) with ⟨i', hc⟩ | ⟨i', hc⟩
  · have h1 : finSumFinEquiv (finSumFinEquiv.symm i) = i := finSumFinEquiv.apply_symm_apply i
    rw [hc, finSumFinEquiv_apply_left] at h1
    have hi : i = Fin.castLE ht.le i' := h1.symm.trans (Fin.ext rfl)
    rw [hexp, hi]
    have h2 := congrFun hw i'
    first
    | exact h2
    | (simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply] at h2; exact h2)
  · rw [hc, Matrix.dotProduct_mulVec, hrow i', zero_dotProduct]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg.NF

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem exists_congrH_isBlockNF (D : D7) (r : ℕ) (β : HermE D r) (hd : β.1.det = 0) :
    ∃ (a : Matrix (Fin r) (Fin r) D.host.E) (t : ℕ) (γ : HermE D r),
      a.det ≠ 0 ∧ IsBlockNF t γ ∧ β = congrH a γ := by
  obtain ⟨P, t, ht, hP, hzero, hblock⟩ := NF.exists_blockNF (D.sp.cm.sig : D.host.E →+* D.host.E)
    (fun x => star_star x) β.1 β.2 hd
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  refine ⟨P⁻¹, t, congrH P β, ?_, ⟨ht, hzero, hblock⟩, ?_⟩
  · intro h0
    have h1 := congrArg Matrix.det (Matrix.nonsing_inv_mul P hu)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  · apply Subtype.ext
    change β.1 = ((P⁻¹).map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ *
      ((P.map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ * β.1 * P) * P⁻¹
    have h1 : ((P⁻¹).map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ *
        (P.map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv P hu,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P hu, Matrix.mul_one]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
