import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRescaleEigenSeriesZero

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen TensorProduct

namespace GlobalTheory.TruncDiag

theorem exists_comb {S : Type} [CommRing S] (h : ℕ → S⟦X⟧) (hh : ∀ n, IsUnit (h n)) (m : ℕ) (y : S⟦X⟧) :
    ∃ c : ℕ → S, (X : S⟦X⟧) ^ m ∣ y - ∑ n ∈ Finset.range m, c n • (X ^ n * h n) := by
  induction m with
  | zero => exact ⟨fun _ => 0, by simp⟩
  | succ m ih =>
    obtain ⟨c, z, hz⟩ := ih
    have hu : IsUnit (constantCoeff (h m)) := (hh m).map constantCoeff
    refine ⟨fun n => if n = m then constantCoeff z * ↑hu.unit⁻¹ else c n, ?_⟩
    rw [Finset.sum_range_succ]
    beta_reduce
    rw [if_pos rfl]
    have hsum : ∑ n ∈ Finset.range m,
        (if n = m then constantCoeff z * ↑hu.unit⁻¹ else c n) • ((X : S⟦X⟧) ^ n * h n)
          = ∑ n ∈ Finset.range m, c n • ((X : S⟦X⟧) ^ n * h n) :=
      Finset.sum_congr rfl fun n hn => by rw [if_neg (Finset.mem_range.mp hn).ne]
    rw [hsum]
    have hX : (X : S⟦X⟧) ∣ z - (constantCoeff z * ↑hu.unit⁻¹) • h m := by
      rw [X_dvd_iff, smul_eq_C_mul, map_sub, map_mul, constantCoeff_C, mul_assoc,
        IsUnit.val_inv_mul, mul_one, sub_self]
    obtain ⟨d, hd⟩ := hX
    refine ⟨d, ?_⟩
    simp only [smul_eq_C_mul] at hz hd ⊢
    linear_combination hz + (X : S⟦X⟧) ^ m * hd

theorem mem_of_gens {S : Type} [CommRing S] {r : ℕ} (m : ℕ) (h : Fin r → ℕ → S⟦X⟧) (hh : ∀ k n, IsUnit (h k n))
    (N : Submodule S (Fin r → S⟦X⟧)) (h0 : ∀ y : Fin r → S⟦X⟧, (∀ k, (X : S⟦X⟧) ^ m ∣ y k) → y ∈ N)
    (h1 : ∀ k n, n < m → (Pi.single k (X ^ n * h k n) : Fin r → S⟦X⟧) ∈ N) (y : Fin r → S⟦X⟧) : y ∈ N := by
  classical
  have key : ∀ k, (Pi.single k (y k) : Fin r → S⟦X⟧) ∈ N := by
    intro k
    obtain ⟨c, hc⟩ := exists_comb (h k) (hh k) m (y k)
    have hmem : (Pi.single k (y k) : Fin r → S⟦X⟧)
        - ∑ n ∈ Finset.range m, c n • (Pi.single k ((X : S⟦X⟧) ^ n * h k n) : Fin r → S⟦X⟧) ∈ N := by
      apply h0
      intro j
      by_cases hj : j = k
      · subst hj
        simpa [Finset.sum_apply] using hc
      · simp [Finset.sum_apply, Pi.single_eq_of_ne hj]
    have hsum : ∑ n ∈ Finset.range m, c n • (Pi.single k ((X : S⟦X⟧) ^ n * h k n) : Fin r → S⟦X⟧) ∈ N :=
      N.sum_mem fun n hn => N.smul_mem _ (h1 k n (Finset.mem_range.mp hn))
    simpa using N.add_mem hmem hsum
  rw [← Finset.univ_sum_single y]
  exact N.sum_mem fun k _ => key k

theorem pow_dvd_of_map {O F : Type} [CommRing O] [Field F] [Algebra O F] (Λ : O⟦X⟧ →ₐ[O] F⟦X⟧) (η : F⟦X⟧)
    (hinj : Function.Injective (algebraMap O F)) (hX : Λ X = X * η) (hη : IsUnit η) (m : ℕ) (c : O⟦X⟧)
    (hc : (X : F⟦X⟧) ^ m ∣ Λ c) : (X : O⟦X⟧) ^ m ∣ c := by
  have hcc : ∀ d : O⟦X⟧, constantCoeff (Λ d) = algebraMap O F (constantCoeff d) := by
    intro d
    obtain ⟨e, he⟩ : (X : O⟦X⟧) ∣ d - C (constantCoeff d) := by
      rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
    have hd : d = C (constantCoeff d) + X * e := by rw [← he]; ring
    have hC : Λ (C (constantCoeff d)) = C (algebraMap O F (constantCoeff d)) := by
      have h1 : (C (constantCoeff d) : O⟦X⟧) = algebraMap O O⟦X⟧ (constantCoeff d) := by
        rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [h1, AlgHom.commutes, PowerSeries.algebraMap_apply]
    conv_lhs => rw [hd]
    rw [map_add, map_mul, hC, hX, map_add, constantCoeff_C, map_mul, map_mul, constantCoeff_X,
      zero_mul, zero_mul, add_zero]
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    have h0 : constantCoeff c = 0 := by
      apply hinj
      rw [← hcc, map_zero]
      exact X_dvd_iff.mp (dvd_trans (dvd_pow_self X (Nat.succ_ne_zero m)) hc)
    obtain ⟨d, rfl⟩ := X_dvd_iff.mpr h0
    rw [map_mul, hX, pow_succ', mul_assoc] at hc
    have hc' : (X : F⟦X⟧) ^ m ∣ Λ d :=
      hη.dvd_mul_left.mp ((mul_dvd_mul_iff_left (X_ne_zero (R := F))).mp hc)
    rw [pow_succ']
    exact mul_dvd_mul_left X (ih d hc')

theorem map_pow_dvd {O F : Type} [CommRing O] [Field F] [Algebra O F] (Λ : O⟦X⟧ →ₐ[O] F⟦X⟧) (η : F⟦X⟧)
    (hX : Λ X = X * η) (m : ℕ) (c : O⟦X⟧) (hc : (X : O⟦X⟧) ^ m ∣ c) : (X : F⟦X⟧) ^ m ∣ Λ c := by
  obtain ⟨d, rfl⟩ := hc
  rw [map_mul, map_pow, hX, mul_pow, mul_assoc]
  exact dvd_mul_right _ _

theorem mulVec_dvd {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (a : R) (y : Fin r → R)
    (hy : ∀ k, a ∣ y k) (u : Fin r) : a ∣ M.mulVec y u := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (hy k) _

theorem rescale_dvd {F : Type} [Field F] (χ : F) (m : ℕ) (y : F⟦X⟧) (hy : (X : F⟦X⟧) ^ m ∣ y) :
    (X : F⟦X⟧) ^ m ∣ rescale χ y := by
  obtain ⟨d, rfl⟩ := hy
  exact ⟨C χ ^ m * rescale χ d, by rw [map_mul, map_pow, rescale_X]; ring⟩

def tr (F : Type) [Field F] (r m : ℕ) : (Fin r → F⟦X⟧) →ₗ[F] (Fin r × Fin m → F) :=
  LinearMap.pi fun x => (coeff (x.2 : ℕ)) ∘ₗ LinearMap.proj x.1

theorem tr_eq_zero {F : Type} [Field F] {r m : ℕ} (y : Fin r → F⟦X⟧) :
    tr F r m y = 0 ↔ ∀ k, (X : F⟦X⟧) ^ m ∣ y k := by
  constructor
  · intro h k
    rw [X_pow_dvd_iff]
    intro n hn
    have := congrFun h (k, ⟨n, hn⟩)
    simpa [tr] using this
  · intro h
    funext x
    simpa [tr] using X_pow_dvd_iff.mp (h x.1) x.2 x.2.isLt

theorem tr_surjective (F : Type) [Field F] (r m : ℕ) : Function.Surjective (tr F r m) := by
  intro w
  refine ⟨fun k => PowerSeries.mk fun n => if hn : n < m then w (k, ⟨n, hn⟩) else 0, ?_⟩
  funext x
  simp [tr, coeff_mk, x.2.isLt]

def opD {F : Type} [Field F] {r : ℕ} (p : F⟦X⟧) (χ : F) (κ : Fin r → F) :
    (Fin r → F⟦X⟧) →ₗ[F] (Fin r → F⟦X⟧) where
  toFun y := fun u => p⁻¹ * (C (κ u) * rescale χ (y u) - y u)
  map_add' y z := by funext u; simp only [Pi.add_apply, map_add]; ring
  map_smul' a y := by
    funext u
    have : rescale χ (C a : F⟦X⟧) = C a := by
      ext n; simp only [coeff_rescale, coeff_C]; split_ifs with h <;> simp [h]
    simp only [Pi.smul_apply, smul_eq_C_mul, map_mul, this, RingHom.id_apply]; ring

theorem tr_opD_congr {F : Type} [Field F] {r m : ℕ} (p : F⟦X⟧) (χ : F) (κ : Fin r → F) (y z : Fin r → F⟦X⟧)
    (h : tr F r m y = tr F r m z) : tr F r m (opD p χ κ y) = tr F r m (opD p χ κ z) := by
  have h' : tr F r m (y - z) = 0 := by rw [map_sub, h, sub_self]
  rw [tr_eq_zero] at h'
  rw [← sub_eq_zero, ← map_sub, ← map_sub, tr_eq_zero]
  intro u
  show (X : F⟦X⟧) ^ m ∣ p⁻¹ * (C (κ u) * rescale χ ((y - z) u) - (y - z) u)
  exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right (rescale_dvd χ m _ (h' u)) _) (h' u)) _

theorem injective_of_span {F Q W ι : Type} [Field F] [AddCommGroup Q] [Module F Q] [AddCommGroup W] [Module F W]
    [Fintype ι] (hW : Module.finrank F W = Fintype.card ι) (Ψ : Q →ₗ[F] W) (g : ι → Q)
    (hg : Submodule.span F (Set.range g) = ⊤) (hΨ : Function.Surjective Ψ) : Function.Injective Ψ := by
  have hQ : Module.Finite F Q := ⟨by rw [← hg]; exact Submodule.fg_span (Set.finite_range g)⟩
  have hWf : Module.Finite F W := Module.Finite.of_surjective Ψ hΨ
  have h1 : Module.finrank F Q ≤ Fintype.card ι := by
    have := finrank_range_le_card (R := F) g
    simp only [Set.finrank] at this
    rw [hg, finrank_top] at this
    exact this
  have h2 : Module.finrank F W ≤ Module.finrank F Q := by
    have := LinearMap.finrank_range_le Ψ
    rwa [LinearMap.range_eq_top.mpr hΨ, finrank_top] at this
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by omega)).mpr hΨ

theorem diag_of_model {F Q : Type} [Field F] [AddCommGroup Q] [Module F Q] (r m : ℕ) (p : F⟦X⟧) (χ : F)
    (κ : Fin r → F) (hp : constantCoeff p ≠ 0) (hχ0 : χ ≠ 0) (hχ : ∀ k : ℕ, 0 < k → χ ^ k ≠ 1)
    (hκ : ∀ u, κ u ≠ 0) (f : Q →ₗ[F] Q) (Ψ : Q →ₗ[F] (Fin r × Fin m → F)) (hΨ : Function.Bijective Ψ)
    (hI : ∀ q, ∃ y, Ψ q = tr F r m y ∧ Ψ (f q) = tr F r m (opD p χ κ y)) :
    DiagWith f ((Finset.univ : Finset (Fin r × Fin m)).val.map
      fun x => (κ x.1 * χ ^ (x.2 : ℕ) - 1) / constantCoeff p) := by
  classical
  choose hs hs0 hseq using fun (u : Fin r) (n : ℕ) =>
    GlobalTheory.exists_rescale_eigen_series p χ (κ u) n hp (hκ u) hχ0 hχ
  have hsu : ∀ u n, IsUnit (hs u n) := fun u n => by
    rw [isUnit_iff_constantCoeff, hs0]; exact isUnit_one
  obtain ⟨ys, hys⟩ : ∃ ys : Fin r × Fin m → (Fin r → F⟦X⟧),
      ys = fun x => Pi.single x.1 ((X : F⟦X⟧) ^ (x.2 : ℕ) * hs x.1 x.2) := ⟨_, rfl⟩
  have hopD : ∀ x, opD p χ κ (ys x) = ((κ x.1 * χ ^ (x.2 : ℕ) - 1) / constantCoeff p) • ys x := by
    intro x
    funext v
    show p⁻¹ * (C (κ v) * rescale χ (ys x v) - ys x v)
      = ((κ x.1 * χ ^ (x.2 : ℕ) - 1) / constantCoeff p) • ys x v
    rw [hys]
    by_cases hv : v = x.1
    · subst hv
      simp only [Pi.single_eq_same]
      rw [hseq, smul_eq_C_mul]
      linear_combination (C ((κ x.1 * χ ^ (x.2 : ℕ) - 1) / constantCoeff p) *
        ((X : F⟦X⟧) ^ (x.2 : ℕ) * hs x.1 x.2)) * PowerSeries.inv_mul_cancel p hp
    · simp only [Pi.single_eq_of_ne hv, map_zero, mul_zero, sub_zero, smul_zero]
  have hspan : ⊤ ≤ Submodule.span F (Set.range fun x => tr F r m (ys x)) := by
    intro t _
    obtain ⟨y, rfl⟩ := tr_surjective F r m t
    refine mem_of_gens (S := F) m hs hsu
      ((Submodule.span F (Set.range fun x => tr F r m (ys x))).comap (tr F r m)) ?_ ?_ y
    · intro y hy
      rw [Submodule.mem_comap, (tr_eq_zero y).mpr hy]
      exact Submodule.zero_mem _
    · intro k n hn
      rw [Submodule.mem_comap]
      exact Submodule.subset_span ⟨(k, ⟨n, hn⟩), by rw [hys]⟩
  have hcard : Fintype.card (Fin r × Fin m) = Module.finrank F (Fin r × Fin m → F) :=
    (Module.finrank_fintype_fun_eq_card F).symm
  obtain ⟨bW, hbW⟩ : ∃ bW : Module.Basis (Fin r × Fin m) F (Fin r × Fin m → F),
      ⇑bW = fun x => tr F r m (ys x) :=
    ⟨basisOfTopLeSpanOfCardEqFinrank _ hspan hcard, coe_basisOfTopLeSpanOfCardEqFinrank _ _ _⟩
  obtain ⟨Ψe, hΨe⟩ : ∃ Ψe : Q ≃ₗ[F] (Fin r × Fin m → F), ⇑Ψe = ⇑Ψ :=
    ⟨LinearEquiv.ofBijective Ψ hΨ, rfl⟩
  refine ⟨r * m, (bW.map Ψe.symm).reindex finProdFinEquiv,
    fun j => (κ (finProdFinEquiv.symm j).1 * χ ^ ((finProdFinEquiv.symm j).2 : ℕ) - 1) / constantCoeff p,
    ?_, ?_⟩
  · intro j
    simp only [Module.Basis.reindex_apply, Module.Basis.map_apply, hbW]
    apply hΨ.1
    obtain ⟨y, hy1, hy2⟩ := hI (Ψe.symm (tr F r m (ys (finProdFinEquiv.symm j))))
    have hq : Ψ (Ψe.symm (tr F r m (ys (finProdFinEquiv.symm j))))
        = tr F r m (ys (finProdFinEquiv.symm j)) := by
      rw [← hΨe]; exact Ψe.apply_symm_apply _
    rw [hy2, map_smul, hq, tr_opD_congr p χ κ y _ (hy1.symm.trans hq), hopD, map_smul]
  · have he : (Finset.univ : Finset (Fin (r * m))).val.map finProdFinEquiv.symm
        = (Finset.univ : Finset (Fin r × Fin m)).val := by
      exact Multiset.map_univ_val_equiv (finProdFinEquiv (m := r) (n := m)).symm
    rw [← he, Multiset.map_map]
    rfl

theorem diagWith_trunc : ∀ {O F P : Type} [CommRing O] [Field F] [Algebra O F] [AddCommGroup P] [Module O P] (P' : Submodule O P) (r m : ℕ) (θ : (Fin r → O⟦X⟧) ≃ₗ[O] P) (Λ : O⟦X⟧ →ₐ[O] F⟦X⟧) (η p : F⟦X⟧) (M : Matrix (Fin r) (Fin r) F⟦X⟧) (χ : F) (κ : Fin r → F) (nb : P →ₗ[O] P), Function.Injective (algebraMap O F) → (∀ c, θ c ∈ P' ↔ ∀ k, (X : O⟦X⟧) ^ m ∣ c k) → Λ X = X * η → IsUnit η → IsUnit M.det → constantCoeff p ≠ 0 → χ ≠ 0 → (∀ k : ℕ, 0 < k → χ ^ k ≠ 1) → (∀ u, κ u ≠ 0) → (∀ c c', nb (θ c) = θ c' → ∀ u, p * M.mulVec (fun k => Λ (c' k)) u = C (κ u) * rescale χ (M.mulVec (fun k => Λ (c k)) u) - M.mulVec (fun k => Λ (c k)) u) → ∃ hs : P' ≤ P'.comap nb, DiagWith ((Submodule.mapQ P' P' nb hs).baseChange F) ((Finset.univ : Finset (Fin r × Fin m)).val.map fun x => (κ x.1 * χ ^ (x.2 : ℕ) - 1) / constantCoeff p) := by
  intro O F P _ _ _ _ _ P' r m θ Λ η p M χ κ nb hinj hP' hX hη hM hp hχ0 hχ hκ hnb
  classical
  have hsolve : ∀ c c', nb (θ c) = θ c' →
      M.mulVec (fun k => Λ (c' k)) = opD p χ κ (M.mulVec (fun k => Λ (c k))) := by
    intro c c' hcc
    funext u
    show _ = p⁻¹ * (C (κ u) * rescale χ (M.mulVec (fun k => Λ (c k)) u) - M.mulVec (fun k => Λ (c k)) u)
    rw [← hnb c c' hcc u, ← mul_assoc, PowerSeries.inv_mul_cancel p hp, one_mul]
  have hdiv : ∀ c : Fin r → O⟦X⟧, (∀ k, (X : O⟦X⟧) ^ m ∣ c k) →
      ∀ u, (X : F⟦X⟧) ^ m ∣ M.mulVec (fun k => Λ (c k)) u := fun c hc =>
    mulVec_dvd M _ _ fun k => map_pow_dvd Λ η hX m (c k) (hc k)
  have hs : P' ≤ P'.comap nb := by
    intro x hx
    rw [Submodule.mem_comap]
    obtain ⟨c, rfl⟩ := θ.surjective x
    have hcc : nb (θ c) = θ (θ.symm (nb (θ c))) := (θ.apply_symm_apply _).symm
    rw [hcc, hP']
    have hdc := (hP' c).mp hx
    have h1 : ∀ u, (X : F⟦X⟧) ^ m ∣ M.mulVec (fun k => Λ (θ.symm (nb (θ c)) k)) u := by
      intro u
      rw [hsolve c _ hcc]
      exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right
        (rescale_dvd χ m _ (hdiv c hdc u)) _) (hdiv c hdc u)) _
    intro k
    apply pow_dvd_of_map Λ η hinj hX hη m
    have h2 := mulVec_dvd M⁻¹ _ _ h1 k
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec] at h2
  refine ⟨hs, ?_⟩
  have hΛs : ∀ (a : O) (c : O⟦X⟧), Λ (a • c) = algebraMap O F a • Λ c := by
    intro a c
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, PowerSeries.algebraMap_apply, smul_eq_C_mul]
  obtain ⟨L, hL⟩ : ∃ L : (Fin r → F⟦X⟧) →ₗ[F] (Fin r × Fin m → F),
      ∀ y, L y = tr F r m (M.mulVec y) :=
    ⟨{ toFun := fun y => tr F r m (M.mulVec y)
       map_add' := fun y z => by simp only [Matrix.mulVec_add, map_add]
       map_smul' := fun b y => by simp only [Matrix.mulVec_smul, map_smul, RingHom.id_apply] },
     fun _ => rfl⟩
  obtain ⟨Ψ0, hΨ0⟩ : ∃ Ψ0 : P →ₗ[O] (Fin r × Fin m → F),
      ∀ x, Ψ0 x = L (fun k => Λ (θ.symm x k)) :=
    ⟨{ toFun := fun x => L (fun k => Λ (θ.symm x k))
       map_add' := fun x y => by
         simp only [map_add, Pi.add_apply]
         rw [← map_add]
         rfl
       map_smul' := fun a x => by
         simp only [RingHom.id_apply]
         have : (fun k => Λ (θ.symm (a • x) k)) = algebraMap O F a • (fun k => Λ (θ.symm x k)) := by
           funext k
           rw [map_smul, Pi.smul_apply, hΛs, Pi.smul_apply]
         rw [this, map_smul, algebraMap_smul] },
     fun _ => rfl⟩
  have hker : P' ≤ LinearMap.ker Ψ0 := by
    intro x hx
    rw [LinearMap.mem_ker]
    obtain ⟨c, rfl⟩ := θ.surjective x
    rw [hΨ0, hL, LinearEquiv.symm_apply_apply, tr_eq_zero]
    exact hdiv c ((hP' c).mp hx)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : F ⊗[O] (P ⧸ P') →ₗ[F] (Fin r × Fin m → F),
      ∀ (a : F) (x : P), Ψ (a ⊗ₜ Submodule.Quotient.mk x) = a • Ψ0 x :=
    ⟨(P'.liftQ Ψ0 hker).liftBaseChange F, fun a x => by
      rw [LinearMap.liftBaseChange_tmul, Submodule.liftQ_apply]⟩
  have hsurj : Function.Surjective Ψ := by
    intro t
    have hN : ∀ y : Fin r → F⟦X⟧, L y ∈ LinearMap.range Ψ := fun y =>
      mem_of_gens (S := F) m (fun _ n => η ^ n) (fun _ n => hη.pow n)
        ((LinearMap.range Ψ).comap L)
        (fun y hy => by
          rw [Submodule.mem_comap, hL, (tr_eq_zero _).mpr (mulVec_dvd M _ _ hy)]
          exact Submodule.zero_mem _)
        (fun k n _ => by
          rw [Submodule.mem_comap, LinearMap.mem_range]
          refine ⟨1 ⊗ₜ Submodule.Quotient.mk (θ (Pi.single k ((X : O⟦X⟧) ^ n))), ?_⟩
          rw [hΨ, one_smul, hΨ0, LinearEquiv.symm_apply_apply]
          congr 1
          funext j
          by_cases hj : j = k
          · subst hj
            simp [map_pow, hX, mul_pow]
          · simp [Pi.single_eq_of_ne hj])
        y
    obtain ⟨y, rfl⟩ := tr_surjective F r m t
    obtain ⟨q, hq⟩ := LinearMap.mem_range.mp (hN (M⁻¹.mulVec y))
    refine ⟨q, ?_⟩
    rw [hq, hL, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec]
  obtain ⟨g0, hg0⟩ : ∃ g0 : Fin r × Fin m → P ⧸ P',
      g0 = fun x => Submodule.Quotient.mk (θ (Pi.single x.1 ((X : O⟦X⟧) ^ (x.2 : ℕ)))) := ⟨_, rfl⟩
  have hspanO : ∀ z : P ⧸ P', z ∈ Submodule.span O (Set.range g0) := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P' z
    obtain ⟨c, rfl⟩ := θ.surjective x
    exact mem_of_gens (S := O) m (fun _ _ => 1) (fun _ _ => isUnit_one)
      ((Submodule.span O (Set.range g0)).comap (P'.mkQ ∘ₗ θ.toLinearMap))
      (fun y hy => by
        rw [Submodule.mem_comap, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero P').mpr ((hP' y).mpr hy)]
        exact Submodule.zero_mem _)
      (fun k n hn => by
        rw [Submodule.mem_comap]
        exact Submodule.subset_span ⟨(k, ⟨n, hn⟩), by rw [hg0]; simp⟩)
      c
  have hspanF : Submodule.span F (Set.range fun x => (1 : F) ⊗ₜ[O] g0 x) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    induction q using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul a z =>
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp (hspanO z)
      rw [← hc, TensorProduct.tmul_sum]
      refine Submodule.sum_mem _ fun x _ => ?_
      have : a ⊗ₜ[O] (c x • g0 x) = (c x • a) • ((1 : F) ⊗ₜ[O] g0 x) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)
  have hinjΨ : Function.Injective Ψ :=
    injective_of_span (ι := Fin r × Fin m) (Module.finrank_fintype_fun_eq_card F) Ψ _ hspanF hsurj
  have hI : ∀ q, ∃ y, Ψ q = tr F r m y ∧
      Ψ (((Submodule.mapQ P' P' nb hs).baseChange F) q) = tr F r m (opD p χ κ y) := by
    intro q
    induction q using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul a z =>
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P' z
      obtain ⟨c, rfl⟩ := θ.surjective x
      refine ⟨a • M.mulVec (fun k => Λ (c k)), ?_, ?_⟩
      · rw [hΨ, hΨ0, hL, LinearEquiv.symm_apply_apply, map_smul]
      · rw [LinearMap.baseChange_tmul, Submodule.mapQ_apply, hΨ, hΨ0, hL,
          hsolve c _ (θ.apply_symm_apply _).symm, map_smul, map_smul]
    | add x y hx hy =>
      obtain ⟨y1, h1, h2⟩ := hx
      obtain ⟨y2, h3, h4⟩ := hy
      exact ⟨y1 + y2, by rw [map_add, h1, h3, map_add],
        by rw [map_add, map_add, h2, h4, map_add, map_add]⟩
  exact diag_of_model r m p χ κ hp hχ0 hχ hκ _ Ψ ⟨hinjΨ, hsurj⟩ hI

end GlobalTheory.TruncDiag
