import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasis

open Matrix PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.TfLoc.Descent

theorem exists_free_gens {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ι : Type*} [Finite ι] {n : ℕ}
    (w : ι → Fin n → K) :
    ∃ (r : ℕ) (b : Fin r → Fin n → K), LinearIndependent K b ∧
      (∀ s, b s ∈ Submodule.span R (Set.range w)) ∧
      (∀ i, w i ∈ Submodule.span R (Set.range b)) := by
  classical
  set M : Submodule R (Fin n → K) := Submodule.span R (Set.range w) with hM
  haveI : Module.Finite R M := Module.Finite.span_of_finite R (Set.finite_range w)
  haveI : Module.Free R M := Module.free_of_finite_type_torsion_free'
  let e := Module.finBasis R M
  refine ⟨_, fun s => (e s : Fin n → K), ?_, fun s => (e s).2, fun i => ?_⟩
  · rw [← LinearIndependent.iff_fractionRing R K]
    exact e.linearIndependent.map' M.subtype M.ker_subtype
  · have h : (⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩ : M) ∈ Submodule.span R (Set.range e) := by
      rw [e.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := M.subtype) h
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2

theorem coset_of_factor {k E : Type*} [Field k] [Field E] [ValuativeRel E] [Algebra k E] {n r : ℕ}
    (g : GL (Fin n) E) (Y : Matrix (Fin n) (Fin r) k)
    (hY : LinearIndependent k (fun s p => Y p s))
    (A : Matrix (Fin r) (Fin n) E) (B : Matrix (Fin n) (Fin r) E)
    (hA : ∀ i j, A i j ∈ intO E) (hB : ∀ i j, B i j ∈ intO E)
    (h1 : Y.map (algebraMap k E) = (g : Matrix (Fin n) (Fin n) E) * B)
    (h2 : (g : Matrix (Fin n) (Fin n) E) = Y.map (algebraMap k E) * A) :
    ∃ y : GL (Fin n) k, (incl y)⁻¹ * g ∈ unitGL (n := Fin n) E := by
  have hBA : B * A = 1 := by
    have h3 : (g : Matrix (Fin n) (Fin n) E) * (B * A) = (g : Matrix (Fin n) (Fin n) E) * 1 := by
      rw [← Matrix.mul_assoc, ← h1, ← h2, Matrix.mul_one]
    have h4 := congrArg (fun M => ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * M) h3
    simpa [← Matrix.mul_assoc] using h4
  have hr1 : r ≤ n := by simpa using hY.fintype_card_le_finrank
  have hr2 : n ≤ r := by
    have h3 := Matrix.rank_mul_le_left B A
    rw [hBA, Matrix.rank_one] at h3
    simpa using h3.trans (Matrix.rank_le_width B)
  obtain rfl : r = n := le_antisymm hr1 hr2
  have hAB : A * B = 1 := mul_eq_one_comm.1 hBA
  have hdetY : Y.det ≠ 0 := by
    intro h0
    have h3 : Y.map (algebraMap k E) * (A * ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) = 1 := by
      rw [← Matrix.mul_assoc, ← h2]; simp
    have h4 := Matrix.det_ne_zero_of_right_inverse h3
    apply h4
    have h5 := RingHom.map_det (algebraMap k E) Y
    rw [h0, map_zero] at h5
    exact h5.symm
  refine ⟨GeneralLinearGroup.mkOfDetNeZero Y hdetY, ?_⟩
  let A' : Matrix (Fin r) (Fin r) (intO E) := fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix (Fin r) (Fin r) (intO E) := fun i j => ⟨B i j, hB i j⟩
  have hinj : ∀ P Q : Matrix (Fin r) (Fin r) (intO E),
      P.map (intO E).subtype = Q.map (intO E).subtype → P = Q := fun P Q h =>
    Matrix.map_injective Subtype.val_injective h
  have hmap : ∀ P Q : Matrix (Fin r) (Fin r) (intO E),
      (P * Q).map (intO E).subtype = P.map (intO E).subtype * Q.map (intO E).subtype :=
    fun P Q => Matrix.map_mul
  have hA' : A'.map (intO E).subtype = A := by ext i j; rfl
  have hB' : B'.map (intO E).subtype = B := by ext i j; rfl
  have hone : (1 : Matrix (Fin r) (Fin r) (intO E)).map (intO E).subtype = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have e1 : A' * B' = 1 := hinj _ _ (by rw [hmap, hA', hB', hAB, hone])
  have e2 : B' * A' = 1 := hinj _ _ (by rw [hmap, hA', hB', hBA, hone])
  refine ⟨⟨A', B', e1, e2⟩, ?_⟩
  rw [eq_inv_mul_iff_mul_eq]
  apply Units.ext
  exact h2.symm

section Galois

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

theorem exists_of_fixed [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hσ : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) (z : E) (hz : σ z = z) :
    ∃ a : k, algebraMap k E a = z := by
  have h : z ∈ (⊥ : IntermediateField k E) := by
    rw [IsGalois.mem_bot_iff_fixed]
    intro τ
    obtain ⟨m, rfl⟩ := (mem_powers_iff_mem_zpowers).2 (hσ τ)
    induction m with
    | zero => simp
    | succ m ih =>
      show (σ ^ (m + 1)) z = z
      have ih' : (σ ^ m) z = z := ih
      rw [pow_succ, AlgEquiv.mul_apply, hz, ih']
  exact IntermediateField.mem_bot.1 h

theorem sum_pow_fixed (σ : E ≃ₐ[k] E) {ℓ : ℕ} (hℓ : σ ^ ℓ = 1) (z : E) :
    σ (∑ j ∈ Finset.range ℓ, (σ ^ j) z) = ∑ j ∈ Finset.range ℓ, (σ ^ j) z := by
  rw [map_sum]
  have h : ∀ j, σ ((σ ^ j) z) = (σ ^ (j + 1)) z := fun j => by
    rw [pow_succ', AlgEquiv.mul_apply]
  simp_rw [h]
  have h1 := Finset.sum_range_succ (fun j => (σ ^ j) z) ℓ
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) z) ℓ
  have h3 : (σ ^ ℓ) z = (σ ^ 0) z := by rw [hℓ]; simp
  rw [h1, h3] at h2
  exact (add_right_cancel h2).symm

theorem pow_mem_int [ValuativeRel E] (σ : E ≃ₐ[k] E) (hint : ∀ x ∈ intO E, σ x ∈ intO E) (j : ℕ) :
    ∀ x ∈ intO E, (σ ^ j) x ∈ intO E := by
  induction j with
  | zero => intro x hx; simpa using hx
  | succ j ih =>
    intro x hx
    rw [pow_succ', AlgEquiv.mul_apply]
    exact hint _ (ih x hx)

theorem exists_pow_factor [ValuativeRel E] {n : ℕ} (σ : E ≃ₐ[k] E)
    (hint : ∀ x ∈ intO E, σ x ∈ intO E) (G H : Matrix (Fin n) (Fin n) E)
    (hH : ∀ a b, H a b ∈ intO E) (h : G.map σ = G * H) (j : ℕ) :
    ∃ Hj : Matrix (Fin n) (Fin n) E, (∀ a b, Hj a b ∈ intO E) ∧ G.map (σ ^ j) = G * Hj := by
  induction j with
  | zero => exact ⟨1, fun a b => by
      rw [Matrix.one_apply]; split_ifs
      · exact (intO E).one_mem
      · exact (intO E).zero_mem, by ext a b; simp⟩
  | succ j ih =>
    obtain ⟨Hj, h1, h2⟩ := ih
    refine ⟨H * Hj.map σ, fun a b => ?_, ?_⟩
    · rw [Matrix.mul_apply]
      exact Subring.sum_mem _ fun c _ => (intO E).mul_mem (hH a c) (hint _ (h1 c b))
    · have h3 : G.map (σ ^ (j + 1)) = (G.map (σ ^ j)).map σ := by
        ext a b; simp [pow_succ', AlgEquiv.mul_apply]
      have h4 : (G * Hj).map σ = G.map σ * Hj.map σ := by
        ext a b; simp [Matrix.mul_apply, map_sum]
      rw [h3, h2, h4, h, Matrix.mul_assoc]

end Galois

end GlobalTheory.CompanionTheory.TfLoc.Descent

namespace GlobalTheory.CompanionTheory.TfLoc.Descent

theorem descent_core {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field E] [ValuativeRel E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] {n ℓ : ℕ} (σ : E ≃ₐ[k] E)
    (hσ : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ)
    (hint : ∀ x ∈ intO E, σ x ∈ intO E)
    (hkE : ∀ a ∈ intO k, algebraMap k E a ∈ intO E)
    (hℓ0 : 0 < ℓ) (hℓ : σ ^ ℓ = 1) (x y : Fin ℓ → E)
    (hxy : ∀ i, x i ∈ intO E ∧ y i ∈ intO E)
    (hd : ∀ j < ℓ, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0)
    (g : GL (Fin n) E) (hg : g⁻¹ * sigmaGL σ g ∈ unitGL (n := Fin n) E) :
    ∃ y : GL (Fin n) k, (incl y)⁻¹ * g ∈ unitGL (n := Fin n) E := by
  classical
  obtain ⟨u, hu⟩ := hg
  set G : Matrix (Fin n) (Fin n) E := (g : Matrix (Fin n) (Fin n) E) with hG
  let H : Matrix (Fin n) (Fin n) E := ((g⁻¹ * sigmaGL σ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
  have hHint : ∀ a b, H a b ∈ intO E := by
    intro a b
    have h1 : H a b = ((u : Matrix (Fin n) (Fin n) (intO E)) a b : E) := by
      simp only [H, ← hu]; rfl
    rw [h1]
    exact ((u : Matrix (Fin n) (Fin n) (intO E)) a b).2
  have hGH : G.map σ = G * H := by
    have h1 : g * (g⁻¹ * sigmaGL σ g) = sigmaGL σ g := by group
    exact (congrArg Units.val h1).symm
  choose Hj hHj hGj using exists_pow_factor σ hint G H hHint hGH
  let C : Fin ℓ → Matrix (Fin n) (Fin n) E :=
    fun i => ∑ j ∈ Finset.range ℓ, ((σ ^ j) (y i)) • Hj j
  have hCint : ∀ i a b, C i a b ∈ intO E := by
    intro i a b
    simp only [C, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Subring.sum_mem _ fun j _ =>
      (intO E).mul_mem (pow_mem_int σ hint j _ (hxy i).2) (hHj j a b)
  let T : Fin ℓ → Fin n → Fin n → E := fun i p m => ∑ j ∈ Finset.range ℓ, (σ ^ j) (y i * G p m)
  have hT : ∀ i p m, T i p m = (G * C i) p m := by
    intro i p m
    simp only [T, C, Matrix.mul_sum, Matrix.sum_apply, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hGj j, map_mul]
    rfl
  have hfix : ∀ i p m, ∃ a : k, algebraMap k E a = T i p m := fun i p m =>
    exists_of_fixed σ hσ _ (sum_pow_fixed σ hℓ _)
  choose S hS using hfix
  have hrec : ∀ p m, G p m = ∑ i, x i * T i p m := by
    intro p m
    simp only [T, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h1 : ∀ j ∈ Finset.range ℓ, ∑ i, x i * ((σ ^ j) (y i) * (σ ^ j) (G p m)) =
        if j = 0 then G p m else 0 := by
      intro j hj
      simp only [← mul_assoc]
      rw [← Finset.sum_mul, hd j (Finset.mem_range.1 hj)]
      split_ifs with h0
      · subst h0; simp
      · simp
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' (Finset.range ℓ) 0]
    simp [hℓ0]
  obtain ⟨r, b, hb, hbw, hwb⟩ := exists_free_gens (R := intO k) (K := k)
    (fun (q : Fin ℓ × Fin n) p => S q.1 p q.2)
  choose c hc using fun s => (Submodule.mem_span_range_iff_exists_fun (intO k)).1 (hbw s)
  choose a ha using fun q => (Submodule.mem_span_range_iff_exists_fun (intO k)).1 (hwb q)
  have hbp : ∀ s p, b s p = ∑ q, (c s q : k) * S q.1 p q.2 := by
    intro s p
    rw [← hc s]
    simp [Finset.sum_apply, Subring.smul_def]
  have hwp : ∀ (i : Fin ℓ) (m p : Fin n), S i p m = ∑ s, (a (i, m) s : k) * b s p := by
    intro i m p
    have h1 := congrFun (ha (i, m)) p
    simpa [Finset.sum_apply, Subring.smul_def] using h1.symm
  let Y : Matrix (Fin n) (Fin r) k := fun p s => b s p
  let B : Matrix (Fin n) (Fin r) E :=
    fun m' s => ∑ q : Fin ℓ × Fin n, algebraMap k E (c s q : k) * C q.1 m' q.2
  let A : Matrix (Fin r) (Fin n) E :=
    fun s m => ∑ i, x i * algebraMap k E (a (i, m) s : k)
  have h1 : Y.map (algebraMap k E) = G * B := by
    ext p s
    have e1 : (Y.map (algebraMap k E)) p s =
        ∑ q : Fin ℓ × Fin n, algebraMap k E (c s q : k) * T q.1 p q.2 := by
      show algebraMap k E (b s p) = _
      rw [hbp, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_mul, hS]
    rw [e1, Matrix.mul_apply]
    show _ = ∑ m', G p m' * ∑ q : Fin ℓ × Fin n, algebraMap k E (c s q : k) * C q.1 m' q.2
    simp only [hT, Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun m' _ => ?_
    ring
  have h2 : G = Y.map (algebraMap k E) * A := by
    ext p m
    rw [hrec p m, Matrix.mul_apply]
    show _ = ∑ s, algebraMap k E (b s p) * ∑ i, x i * algebraMap k E (a (i, m) s : k)
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hS i p m, hwp i m p, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_mul]
    ring
  refine coset_of_factor g Y hb A B ?_ ?_ h1 h2
  · intro s m
    exact Subring.sum_mem _ fun i _ => (intO E).mul_mem (hxy i).1 (hkE _ (a (i, m) s).2)
  · intro m' s
    exact Subring.sum_mem _ fun q _ => (intO E).mul_mem (hkE _ (c s q).2) (hCint _ _ _)

theorem unramified_descent_coset : TraceOneIntegralElement → L1 → L3 := by
  intro hc _ k E _ _ _ _ _ _ _ _ _ _ _ _ hU σ hσ n g hg
  obtain ⟨hv, hk, -⟩ := GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a k E hU σ hσ
  obtain ⟨-, x, y, hxy, hd⟩ := hc k E hU σ hσ
  have hint : ∀ z ∈ intO E, σ z ∈ intO E := by
    intro z hz
    rw [Valuation.mem_integer_iff] at hz ⊢
    rw [hv σ z]
    exact hz
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact pow_card_eq_one'
  exact descent_core σ hσ hint (fun a ha => (hk a).2 ha) Module.finrank_pos hℓ x y hxy hd g hg

end GlobalTheory.CompanionTheory.TfLoc.Descent
