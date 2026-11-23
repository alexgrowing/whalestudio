import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AlgebraMapInvFf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IsInLieAlgebraISmulAddConjTranspose

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem sum_plus_kk {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (c j : Fin n)
    (h : ε c = true ∨ ε j = true) :
    ∑ i ∈ plusIdx ε, k c i * star (k j i) = if c = j then 1 else 0 := by
  have hkk : k * kᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at this
    exact this
  rw [Finset.sum_subset (Finset.subset_univ _)]
  · have := congrFun (congrFun hkk c) j
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] at this
    exact this
  · intro i _ hi
    have hi' : ε i = false := by simpa [plusIdx] using hi
    rcases h with h | h
    · rw [kset_entry_zero hk (by rw [h, hi']; decide), zero_mul]
    · rw [kset_entry_zero hk (i := j) (by rw [h, hi']; decide), star_zero, mul_zero]

theorem sum_minus_kk {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (c b : Fin n)
    (h : ε c = false ∨ ε b = false) :
    ∑ a ∈ minusIdx ε, k c a * star (k b a) = if c = b then 1 else 0 := by
  have hkk : k * kᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at this
    exact this
  rw [Finset.sum_subset (Finset.subset_univ _)]
  · have := congrFun (congrFun hkk c) b
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] at this
    exact this
  · intro a _ ha
    have ha' : ε a = true := by simpa [minusIdx] using ha
    rcases h with h | h
    · rw [kset_entry_zero hk (by rw [h, ha']; decide), zero_mul]
    · rw [kset_entry_zero hk (i := b) (by rw [h, ha']; decide), star_zero, mul_zero]

theorem conj_single_apply (k : Matrix (Fin n) (Fin n) ℂ) (a i c d : Fin n) :
    (k * Matrix.single a i (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d = k c a * star (k d i) := by
  simp [Matrix.mul_apply, Matrix.single_apply, conjTranspose_apply, ite_and, ite_mul, Finset.sum_ite_eq,
]

theorem coef_d {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (c d : Fin n) (x : Fin n × Fin n) :
    ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, (k * Matrix.single a i (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * adMat ε k x (i, a) =
      if x = (d, c) ∧ ε d = true ∧ ε c = false then 1 else 0 := by
  by_cases hx : IsPhys ε x
  · obtain ⟨j, b⟩ := x
    have hj : ε j = true := hx.1
    have hb : ε b = false := hx.2
    have hterm : ∀ i ∈ plusIdx ε, ∀ a ∈ minusIdx ε,
        (k * Matrix.single a i (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * adMat ε k (j, b) (i, a) =
          (k j i * star (k d i)) * (k c a * star (k b a)) := by
      intro i hi a ha
      have hia : IsPhys ε (i, a) := ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp ha).2⟩
      rw [conj_single_apply]
      simp only [adMat, hx, hia, if_true]
      ring
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a ha => hterm i hi a ha,
      ← Finset.sum_mul_sum, sum_plus_kk hk j d (Or.inl hj), sum_minus_kk hk c b (Or.inr hb)]
    rcases eq_or_ne j d with h1 | h1 <;> rcases eq_or_ne c b with h2 | h2
    · subst h1
      subst h2
      simp [hj, hb]
    · rw [if_neg h2, mul_zero, if_neg]
      rintro ⟨h, -⟩
      exact h2 (Prod.ext_iff.mp h).2.symm
    · rw [if_neg h1, zero_mul, if_neg]
      rintro ⟨h, -⟩
      exact h1 (Prod.ext_iff.mp h).1
    · rw [if_neg h1, zero_mul, if_neg]
      rintro ⟨h, -⟩
      exact h1 (Prod.ext_iff.mp h).1
  · rw [if_neg]
    · refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun a ha => ?_
      have hia : IsPhys ε (i, a) := ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp ha).2⟩
      have hne : x ≠ (i, a) := fun h => hx (h ▸ hia)
      simp [adMat, hx, hne]
    · rintro ⟨rfl, h1, h2⟩
      exact hx ⟨h1, h2⟩

theorem coef_d' {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (c d : Fin n) (x : Fin n × Fin n) :
    ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, (k * Matrix.single i a (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * star (adMat ε k x (i, a)) =
      if x = (c, d) ∧ ε c = true ∧ ε d = false then 1 else 0 := by
  by_cases hx : IsPhys ε x
  · obtain ⟨j, b⟩ := x
    have hj : ε j = true := hx.1
    have hb : ε b = false := hx.2
    have hterm : ∀ i ∈ plusIdx ε, ∀ a ∈ minusIdx ε,
        (k * Matrix.single i a (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * star (adMat ε k (j, b) (i, a)) =
          (k c i * star (k j i)) * (k b a * star (k d a)) := by
      intro i hi a ha
      have hia : IsPhys ε (i, a) := ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp ha).2⟩
      rw [conj_single_apply]
      simp only [adMat, hx, hia, if_true, star_mul', star_star]
      ring
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a ha => hterm i hi a ha,
      ← Finset.sum_mul_sum, sum_plus_kk hk c j (Or.inr hj), sum_minus_kk hk b d (Or.inl hb)]
    rcases eq_or_ne c j with h1 | h1 <;> rcases eq_or_ne b d with h2 | h2
    · subst h1
      subst h2
      simp [hj, hb]
    · rw [if_neg h2, mul_zero, if_neg]
      rintro ⟨h, -⟩
      exact h2 (Prod.ext_iff.mp h).2
    · rw [if_neg h1, zero_mul, if_neg]
      rintro ⟨h, -⟩
      exact h1 (Prod.ext_iff.mp h).1.symm
    · rw [if_neg h1, zero_mul, if_neg]
      rintro ⟨h, -⟩
      exact h1 (Prod.ext_iff.mp h).1.symm
  · rw [if_neg]
    · refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun a ha => ?_
      have hia : IsPhys ε (i, a) := ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp ha).2⟩
      have hne : x ≠ (i, a) := fun h => hx (h ▸ hia)
      simp [adMat, hx, hne]
    · rintro ⟨rfl, h1, h2⟩
      exact hx ⟨h1, h2⟩

theorem sum_comm_2_3 {M α β γ δ ζ : Type*} [AddCommMonoid M] [Fintype γ] [Fintype δ] [Fintype ζ]
    (s : Finset α) (t : Finset β) (F : α → β → γ → δ → ζ → M) :
    ∑ i ∈ s, ∑ a ∈ t, ∑ c, ∑ d, ∑ x, F i a c d x = ∑ c, ∑ d, ∑ x, ∑ i ∈ s, ∑ a ∈ t, F i a c d x := by
  calc ∑ i ∈ s, ∑ a ∈ t, ∑ c, ∑ d, ∑ x, F i a c d x
      = ∑ i ∈ s, ∑ c, ∑ a ∈ t, ∑ d, ∑ x, F i a c d x := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ c, ∑ i ∈ s, ∑ a ∈ t, ∑ d, ∑ x, F i a c d x := Finset.sum_comm
    _ = ∑ c, ∑ i ∈ s, ∑ d, ∑ a ∈ t, ∑ x, F i a c d x :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ i ∈ s, ∑ a ∈ t, ∑ x, F i a c d x := Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ i ∈ s, ∑ x, ∑ a ∈ t, F i a c d x :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ x, ∑ i ∈ s, ∑ a ∈ t, F i a c d x :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm

section Rep

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

def sigD (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : Module.End ℂ D where
  toFun v := ⟨σ k v, hD.kStable k hk v v.2⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

def wK (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    Module.End ℂ (TensorProduct ℂ D (Fock n)) :=
  TensorProduct.map (sigD hD hk) (ff ε k).toLinearMap

theorem actM_single' {M : Type*} [AddCommGroup M] [Module ℂ M] (F : Fin n → Fin n → Module.End ℂ M)
    (a i : Fin n) : actM F (Matrix.single a i (1 : ℂ)) = F a i := by
  simp [actM, Matrix.single_apply, ite_and, ite_smul, Finset.sum_ite_eq]

theorem sigD_E (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) (a i : Fin n) (v : D) :
    sigD hD hk (E a i v) = actM E (k * Matrix.single a i (1 : ℂ) * kᴴ) (sigD hD hk v) := by
  apply Subtype.ext
  have h := derived_adK hσ hD hk (Matrix.single a i (1 : ℂ)) v
  rw [actM_single'] at h
  exact h

theorem adPhys_apply_single (k : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n × Fin n) :
    adPhys ε k (Pi.single y 1) x = adMat ε k x y := by
  simp [adPhys, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem ff_cpFock_apply (k : Matrix (Fin n) (Fin n) ℂ) (i a : Fin n) (f : Fock n) :
    ff ε k (cpFock i a f) = ∑ x, adMat ε k x (i, a) • cpFock x.1 x.2 (ff ε k f) := by
  have h := LinearMap.congr_fun (ff_cpV (ε := ε) k (Pi.single (i, a) 1)) f
  simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply] at h
  rw [cpFock_eq_cpV i a, h, cpV_eq_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [LinearMap.smul_apply, adPhys_apply_single]

theorem ff_cmFock_apply {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (i a : Fin n) (f : Fock n) :
    ff ε k (cmFock i a f) = ∑ x, star (adMat ε k x (i, a)) • cmFock x.1 x.2 (ff ε k f) := by
  have h := LinearMap.congr_fun (ff_cmV hk (Pi.single (i, a) 1)) f
  simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply] at h
  rw [cmFock_eq_cmV i a, h, cmV_eq_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [LinearMap.smul_apply, adPhys_apply_single]

theorem wK_dOp (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) :
    wK hD hk * dOp ε (eT E) cpT = dOp ε (eT E) cpT * wK hD hk := by
  apply TensorProduct.ext'
  intro v f
  simp only [Module.End.mul_apply, dOp, LinearMap.sum_apply, map_sum, eT, cpT, TensorProduct.map_tmul,
    LinearMap.id_apply, wK, AlgHom.toLinearMap_apply]
  have key : ∀ i a, sigD hD hk (E a i v) ⊗ₜ[ℂ] ff ε k (cpFock i a f) =
      ∑ c, ∑ d, ∑ x : Fin n × Fin n,
        ((k * Matrix.single a i (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * adMat ε k x (i, a)) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cpFock x.1 x.2 (ff ε k f)) := by
    intro i a
    rw [sigD_E hσ hD hk, ff_cpFock_apply, actM, LinearMap.sum_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [LinearMap.sum_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [LinearMap.smul_apply, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  simp only [key]
  rw [sum_comm_2_3]
  have hcoef : ∀ c d (x : Fin n × Fin n),
      ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε,
        ((k * Matrix.single a i (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * adMat ε k x (i, a)) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cpFock x.1 x.2 (ff ε k f)) =
        (if x = (d, c) ∧ ε d = true ∧ ε c = false then (1 : ℂ) else 0) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cpFock x.1 x.2 (ff ε k f)) := by
    intro c d x
    rw [← coef_d hk c d x, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_smul ..).symm
  simp only [hcoef]
  simp only [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [plusIdx, minusIdx, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : ε d = true <;> simp [hd]

theorem wK_dOp' (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) :
    wK hD hk * dOp' ε (eT E) cmT = dOp' ε (eT E) cmT * wK hD hk := by
  apply TensorProduct.ext'
  intro v f
  simp only [Module.End.mul_apply, dOp', LinearMap.neg_apply, map_neg, LinearMap.sum_apply, map_sum, eT, cmT,
    TensorProduct.map_tmul, LinearMap.id_apply, wK, AlgHom.toLinearMap_apply]
  congr 1
  have key : ∀ i a, sigD hD hk (E i a v) ⊗ₜ[ℂ] ff ε k (cmFock i a f) =
      ∑ c, ∑ d, ∑ x : Fin n × Fin n,
        ((k * Matrix.single i a (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * star (adMat ε k x (i, a))) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cmFock x.1 x.2 (ff ε k f)) := by
    intro i a
    rw [sigD_E hσ hD hk, ff_cmFock_apply hk, actM, LinearMap.sum_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [LinearMap.sum_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [LinearMap.smul_apply, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  simp only [key]
  rw [sum_comm_2_3]
  have hcoef : ∀ c d (x : Fin n × Fin n),
      ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε,
        ((k * Matrix.single i a (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * star (adMat ε k x (i, a))) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cmFock x.1 x.2 (ff ε k f)) =
        (if x = (c, d) ∧ ε c = true ∧ ε d = false then (1 : ℂ) else 0) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cmFock x.1 x.2 (ff ε k f)) := by
    intro c d x
    rw [← coef_d' hk c d x, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_smul ..).symm
  simp only [hcoef]
  simp only [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [plusIdx, minusIdx, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : ε c = true <;> simp [hc]

end Rep

end ReciprocityTheory.ChartRestriction.DS.TRGap
