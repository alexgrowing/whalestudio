import Formalism.LocalToGlobal.InertKernelTheory.DefsMM
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntTens

noncomputable section

namespace Formalism.L2.KerInert.MMFour

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC Formalism.L2.KerInert.IntTens

section Mat

variable {n n' r : ℕ} {R : Type*} [CommRing R]

def AB (A : Matrix (Fin r) (Fin r) R) : Matrix (Fin (n' * n * r)) (Fin (n' * n * r)) R :=
  fun q q' => if ((eIdx n' n r).symm q).1 = ((eIdx n' n r).symm q').1 then
    A ((eIdx n' n r).symm q).2 ((eIdx n' n r).symm q').2 else 0

theorem AB_eIdx (A : Matrix (Fin r) (Fin r) R) (P P' : Fin n' × Fin n) (x y : Fin r) :
    AB (n' := n') (n := n) A (eIdx n' n r (P, x)) (eIdx n' n r (P', y)) = if P = P' then A x y else 0 := by
  simp [AB]

def eSw (n' n r : ℕ) : Fin r × (Fin n' × Fin n) ≃ Fin (n' * n * r) :=
  (Equiv.prodComm _ _).trans (eIdx n' n r)

theorem AB_eq_reindex (A : Matrix (Fin r) (Fin r) R) :
    AB (n' := n') (n := n) A =
      Matrix.reindex (eSw n' n r) (eSw n' n r) (Matrix.blockDiagonal fun _ : Fin n' × Fin n => A) := by
  ext q q'
  obtain ⟨⟨P, x⟩, rfl⟩ := (eIdx n' n r).surjective q
  obtain ⟨⟨P', y⟩, rfl⟩ := (eIdx n' n r).surjective q'
  rw [AB_eIdx]
  simp [eSw, Matrix.blockDiagonal_apply]

theorem det_AB (A : Matrix (Fin r) (Fin r) R) :
    (AB (n' := n') (n := n) A).det = A.det ^ (n' * n) := by
  rw [AB_eq_reindex, Matrix.det_reindex_self, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

theorem sum_eIdx {M : Type*} [AddCommMonoid M] (F : Fin (n' * n * r) → M) :
    ∑ q, F q = ∑ P : Fin n' × Fin n, ∑ x : Fin r, F (eIdx n' n r (P, x)) := by
  rw [← (eIdx n' n r).sum_comp, Fintype.sum_prod_type]

theorem gram_AB (A : Matrix (Fin r) (Fin r) R) (g : Fin (n' * n * r) → Fin (n' * n * r) → R) (g0 : Fin r → Fin r → R)
    (hg : ∀ P x P' y, g (eIdx n' n r (P, x)) (eIdx n' n r (P', y)) = if P = P' then g0 x y else 0)
    (σ : R →+* R) (hA : ∀ a c, ∑ x, ∑ y, A a x * g0 x y * σ (A c y) = if a = c then 1 else 0) :
    ∀ i j, ∑ m, ∑ k, AB (n' := n') (n := n) A i m * g m k * σ (AB (n' := n') (n := n) A j k) =
      if i = j then 1 else 0 := by
  classical
  intro i j
  obtain ⟨⟨P, a⟩, rfl⟩ := (eIdx n' n r).surjective i
  obtain ⟨⟨P', c⟩, rfl⟩ := (eIdx n' n r).surjective j
  have hσ : ∀ (c : Prop) [Decidable c] (x : R), σ (if c then x else 0) = if c then σ x else 0 := by
    intro c _ x; split_ifs <;> simp
  rw [sum_eIdx]
  simp_rw [sum_eIdx (fun k => _ * g _ k * σ (AB A _ k)), AB_eIdx, hg, hσ]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, (eIdx n' n r).injective.eq_iff, Prod.mk.injEq]
  by_cases h : P = P'
  · subst h; simp [hA]
  · simp [h]

end Mat

section GlobalTheory

variable {D : D7} {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)
variable {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])

def atLogVA {r : ℕ} {NN NN' : ℕ} (v : Fin r → (D.what₂.Tau × Fin NN' × Fin NN → ℂ_[p])) :
    D.what₂.Tau × Fin NN' × Fin NN → MvPowerSeries (Fin r) ℂ_[p] :=
  fun k => ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i k) *
      PowerSeries.subst (MvPowerSeries.X i) (flog (C • wModel lam Λ) wq)

theorem atLogVA_hasSubst {r NN NN' : ℕ} (v : Fin r → (D.what₂.Tau × Fin NN' × Fin NN → ℂ_[p])) :
    MvPowerSeries.HasSubst (atLogVA lam Λ C wq v) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro k
  simp only [atLogVA, map_sum, map_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cc_psubst' (MvPowerSeries.constantCoeff_X i) (cc_flog _ wq), mul_zero]

theorem atLogV_eq {r NN NN' : ℕ} (v : Fin r → (D.what₂.Tau × Fin NN' × Fin NN → ℂ_[p]))
    (F : MvPowerSeries (D.what₂.Tau × Fin NN' × Fin NN) ℂ_[p]) :
    atLogV D lam Λ C wq v F = MvPowerSeries.substAlgHom (atLogVA_hasSubst lam Λ C wq v) F := by
  rw [MvPowerSeries.coe_substAlgHom]; rfl

theorem atLogV_prod {r NN NN' : ℕ} (v : Fin r → (D.what₂.Tau × Fin NN' × Fin NN → ℂ_[p]))
    (F : Fin n' → Fin n → MvPowerSeries (D.what₂.Tau × Fin NN' × Fin NN) ℂ_[p]) :
    atLogV D lam Λ C wq v (∏ I, ∏ J, F I J) = ∏ I, ∏ J, atLogV D lam Λ C wq v (F I J) := by
  simp only [atLogV_eq, map_prod]

theorem atLogVA_blk {r : ℕ} (v : Fin r → (D.what₂.Tau × Fin m' × Fin m → ℂ_[p]))
    (v₄ : Fin (n' * n * r) → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p]))
    (hv₄ : ∀ P i I J k, v₄ (eIdx n' n r (P, i)) (blkIdx D eR eC I J k) = if P = (I, J) then v i k else 0)
    (I : Fin n') (J : Fin n) (k : D.what₂.Tau × Fin m' × Fin m) :
    atLogVA lam Λ C wq v₄ (blkIdx D eR eC I J k) =
      MvPowerSeries.rename (idxK r I J) (atLogVA lam Λ C wq v k) := by
  classical
  simp only [atLogVA, map_sum, map_mul, AlgHom.commutes]
  rw [sum_eIdx, Finset.sum_eq_single (I, J)]
  · refine Finset.sum_congr rfl fun k' _ => ?_
    rw [rename_psubst _ (MvPowerSeries.constantCoeff_X k'), MvPowerSeries.rename_X, hv₄, if_pos rfl]
    rfl
  · intro P _ hne
    refine Finset.sum_eq_zero fun k' _ => ?_
    rw [hv₄, if_neg hne]
    simp
  · simp

theorem atLogV_rename {r : ℕ} (v : Fin r → (D.what₂.Tau × Fin m' × Fin m → ℂ_[p]))
    (v₄ : Fin (n' * n * r) → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p]))
    (hv₄ : ∀ P i I J k, v₄ (eIdx n' n r (P, i)) (blkIdx D eR eC I J k) = if P = (I, J) then v i k else 0)
    (I : Fin n') (J : Fin n) (F : MvPowerSeries (D.what₂.Tau × Fin m' × Fin m) ℂ_[p]) :
    atLogV D lam Λ C wq v₄ (MvPowerSeries.rename (blkIdx D eR eC I J) F) =
      MvPowerSeries.rename (idxK r I J) (atLogV D lam Λ C wq v F) := by
  show MvPowerSeries.subst (atLogVA lam Λ C wq v₄) _ =
    MvPowerSeries.rename (idxK r I J) (MvPowerSeries.subst (atLogVA lam Λ C wq v) F)
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) (atLogVA_hasSubst lam Λ C wq _),
    MvPowerSeries.subst_comp_subst_apply (atLogVA_hasSubst lam Λ C wq v) (MvPowerSeries.HasSubst.X_comp _)]
  congr 1
  funext k
  rw [Function.comp_apply, MvPowerSeries.subst_X (atLogVA_hasSubst lam Λ C wq _), ← MvPowerSeries.rename_eq_subst]
  exact atLogVA_blk eR eC lam Λ C wq v v₄ hv₄ I J k

def v4 {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ_[p]) (b : Fin r → Matrix (Fin m') (Fin m) D.host.E)
    (q : Fin (n' * n * r)) (k : D.what₂.Tau × Fin N' × Fin N) : ℂ_[p] :=
  ∑ j, AB (n' := n') (n := n) A q j * lamC lam (embT D k.1 (bB (D := D) eR eC b j k.2.1 k.2.2))

theorem four_block_vector_entry {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ_[p]) (b : Fin r → Matrix (Fin m') (Fin m) D.host.E)
    (v : Fin r → (D.what₂.Tau × Fin m' × Fin m → ℂ_[p]))
    (hv : ∀ i k, v i k = ∑ j, A i j * lamC lam (embT D k.1 (b j k.2.1 k.2.2)))
    (P : Fin n' × Fin n) (i : Fin r) (I : Fin n') (J : Fin n) (k : D.what₂.Tau × Fin m' × Fin m) :
    v4 eR eC lam A b (eIdx n' n r (P, i)) (blkIdx D eR eC I J k) = if P = (I, J) then v i k else 0 := by
  classical
  have hb : ∀ P' x, bB (D := D) eR eC b (eIdx n' n r (P', x)) = sglB eR eC P'.1 P'.2 (b x) := fun P' x => by
    simp [bB]
  unfold v4
  rw [sum_eIdx]
  simp only [AB_eIdx, hb, blkIdx, sglB_apply, Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single (I, J)]
  · by_cases h : P = (I, J)
    · simp [h, hv]
    · simp [h]
  · intro P' _ hne
    refine Finset.sum_eq_zero fun x _ => ?_
    have : ¬ (I = P'.1 ∧ J = P'.2) := fun h => hne (by rw [h.1, h.2])
    simp [this, lamC_zero]
  · simp

end GlobalTheory

def eOne (k : ℕ) : Fin k ≃ Fin k × Fin 1 := (finCongr (Nat.mul_one k).symm).trans finProdFinEquiv.symm

theorem lamC_phi_zero (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) :
    lamC lam (D.host.φ₀ (((0 : D.host.K)) : D.host.E)) = 0 := by
  simp [lamC_zero]

theorem isLocONB_blk (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : ℂ_[p] →+* ℂ_[p]) {r : ℕ}
    (v : Fin r → (D.what₂.Tau × Fin 1 × Fin 1 → ℂ_[p]))
    (hv : IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) σ v) :
    ∃ (A : Matrix (Fin r) (Fin r) ℂ_[p]) (b : Fin r → Matrix (Fin 1) (Fin 1) D.host.E),
      (∀ i k, v i k = ∑ j, A i j * lamC lam (embT D k.1 (b j k.2.1 k.2.2))) ∧
      IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) σ
        (v4 (eOne 2) (eOne 2) lam A b) := by
  classical
  obtain ⟨b, A, hloc, hAint, hdet, hgram, hvb⟩ := hv
  refine ⟨A, b, hvb, bB (eOne 2) (eOne 2) b, AB A, locBasis_bB (eOne 2) (eOne 2) p b hloc, ?_, ?_, ?_,
    fun i k => rfl⟩
  · intro i j
    unfold AB
    split_ifs
    · exact hAint _ _
    · exact ⟨by unfold IsIntP; simp, subset_closure ⟨0, lamC_phi_zero D lam⟩⟩
  · rw [det_AB, norm_pow, hdet, one_pow]
  · refine gram_AB A _ (fun x y => lamC lam (D.host.φ₀ ((hYY D (b x) (b y) : D.host.K) : D.host.E))) ?_ σ hgram
    intro P x P' y
    rw [bB_eIdx, bB_eIdx, hYY_sglB]
    by_cases h : P = P'
    · subst h; simp
    · have : ¬ (P.1 = P'.1 ∧ P.2 = P'.2) := fun h' => h (Prod.ext h'.1 h'.2)
      rw [if_neg this, if_neg h, lamC_phi_zero]

theorem fourProd_main : FourProd := by
  intro D cc δ B hcc hδ p _ hp5 hin lam σ r v hσ hv H
  have hp2 : p ≠ 2 := by omega
  obtain ⟨A, b, hvb, hv₄⟩ := isLocONB_blk D lam σ v hv
  refine ⟨2 * 2 * r, v4 (eOne 2) (eOne 2) lam A b, hv₄, ?_⟩
  intro s hs C wq hC hW
  have hfun : U D B.tor s (B.thZero 2 2) = fun z => ∏ I, ∏ J,
      U D B.tor (prjB (eOne 2) (eOne 2) I J s) (B.thZero 1 1) (blkPt D (eOne 2) (eOne 2) I J z) :=
    funext (U_tensPow (eOne 2) (eOne 2) B.tor B.thMM s)
  have hH := fun I J => H _ (torsB (eOne 2) (eOne 2) B.tor p I J s hs)
  rw [hfun, pSer_blk (eOne 2) (eOne 2) lam taylor_product_over_blocks _ (fun I J => (hH I J).1), atLogV_prod]
  simp_rw [atLogV_rename (eOne 2) (eOne 2) lam _ C wq v _ (four_block_vector_entry (eOne 2) (eOne 2) lam A b v hvb)]
  rw [ePh_blk lam _ C wq hp2 r]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib, ← map_mul]
  exact integralMv_prod _ _ fun I _ => integralMv_prod _ _ fun J _ =>
    integralMv_rename _ ((hH I J).2 C wq hC hW)

end Formalism.L2.KerInert.MMFour

namespace Formalism.L2.KerInert

theorem four_products_from_one : FourProd := MMFour.fourProd_main

end Formalism.L2.KerInert
