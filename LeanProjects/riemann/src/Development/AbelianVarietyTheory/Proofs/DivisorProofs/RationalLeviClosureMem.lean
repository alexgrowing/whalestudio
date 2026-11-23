import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviDecomp

open Matrix GlobalTheory.LeviElem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show ((g⁻¹ * g : UA σ J) : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_mul_inv' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show ((g * g⁻¹ : UA σ J) : GL (Fin n) (AE F E)).1 = 1
  simp

theorem eq_of_mat_eq {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g h : UA σ J} (e : mat g = mat h) : g = h :=
  Subtype.ext (Units.ext e)

theorem fix_of_mem_closure {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x : Fin n → AE F E) {q : UA σ J}
    (hq : q ∈ Subgroup.closure {g : UA σ J | mat g *ᵥ x = x}) : mat q *ᵥ x = x := by
  induction hq using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one => simp [mat_one']
  | mul g h _ _ hg hh => rw [mat_mul', ← mulVec_mulVec, hh, hg]
  | inv g _ hg =>
    calc mat g⁻¹ *ᵥ x = mat g⁻¹ *ᵥ (mat g *ᵥ x) := by rw [hg]
      _ = x := by rw [mulVec_mulVec, mat_inv_mul', one_mulVec]

theorem prop_of_mem_unip {n n₁ : ℕ} {W : Spc F E n} (H : Plane E n n₁) {u : UA σ W.J} (hu : u ∈ unip σ W H) :
    mat u *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x := by
  induction hu using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one => exact ⟨by simp [mat_one'], fun z => ⟨0, by simp [mat_one']⟩⟩
  | mul g h _ _ hg hh =>
    refine ⟨by rw [mat_mul', ← mulVec_mulVec, hh.1, hg.1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hh.2 z
    obtain ⟨c, hc⟩ := hg.2 z
    exact ⟨c + a, by rw [mat_mul', ← mulVec_mulVec, ha, mulVec_add, mulVec_smul, hg.1, hc, add_smul, add_assoc]⟩
  | inv g _ hg =>
    have hx : mat g⁻¹ *ᵥ incV F H.x = incV F H.x := by
      calc mat g⁻¹ *ᵥ incV F H.x = mat g⁻¹ *ᵥ (mat g *ᵥ incV F H.x) := by rw [hg.1]
        _ = incV F H.x := by rw [mulVec_mulVec, mat_inv_mul', one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hg.2 z
    refine ⟨-a, ?_⟩
    have h1 : mat g⁻¹ *ᵥ (mat g *ᵥ (incM F H.ι *ᵥ z)) = incM F H.ι *ᵥ z := by
      rw [mulVec_mulVec, mat_inv_mul', one_mulVec]
    rw [ha, mulVec_add, mulVec_smul, hx] at h1
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, h1]

theorem inv_intertwine {R : Type} [CommRing R] {k l : ℕ} {A A' : Matrix (Fin k) (Fin k) R} {B B' : Matrix (Fin l) (Fin l) R}
    {I : Matrix (Fin k) (Fin l) R} (hA : A' * A = 1) (hB : B * B' = 1) (h : A * I = I * B) : A' * I = I * B' := by
  calc A' * I = A' * I * (B * B') := by rw [hB, Matrix.mul_one]
    _ = A' * (I * B) * B' := by simp only [Matrix.mul_assoc]
    _ = A' * (A * I) * B' := by rw [h]
    _ = I * B' := by rw [← Matrix.mul_assoc A' A, hA, Matrix.one_mul]

theorem two_cols_mulVec {R : Type} [CommRing R] {n : ℕ} (x y : Fin n → R) (c d : R) :
    cols2 x y *ᵥ ![c, d] = c • x + d • y := by
  ext i; simp [cols2, mulVec, dotProduct, Fin.sum_univ_two]; ring

theorem map_mul_alg {k l o : Type} [Fintype l] (σ : E →ₐ[F] E) (A : Matrix k l E) (B : Matrix l o E) :
    (A * B).map σ = A.map σ * B.map σ := Matrix.map_mul (f := σ.toRingHom)

theorem decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∀ q ∈ (ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}), ∃! γ : ratU σ G₁.V.J, (m 1 γ)⁻¹ * q ∈ unip σ G.V H := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ m hm q hq
  obtain ⟨hqr, hqc⟩ := Subgroup.mem_inf.1 hq
  have hqx : mat q *ᵥ incV F H.x = incV F H.x := fix_of_mem_closure _ hqc
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hfi : Function.Injective f := Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  have hcf : ∀ e, cA σ (f e) = f (σ e) := fun e => by simp [cA, hf, inclR]
  have hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hmapσ : ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) E), (A.map f).map (cA σ) = (A.map σ).map f := fun A => by
    ext i j; simp [hcf]

  have hinj : ∀ (z z' : Fin b → AE F E) (a : AE F E), incM F H.ι *ᵥ z' = incM F H.ι *ᵥ z + a • incV F H.x → z' = z := by
    intro z z' a h
    set v : Fin b ⊕ Fin 2 → AE F E := Sum.elim (z' - z) ![-a, 0] with hv
    have h1 : fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) *ᵥ v = 0 := by
      rw [fromCols_mulVec]
      have e1 : v ∘ Sum.inl = z' - z := rfl
      have e2 : v ∘ Sum.inr = ![-a, 0] := rfl
      rw [e1, e2, two_cols_mulVec, mulVec_sub, h]
      simp
    have h2 : v = 0 := by
      rw [← Matrix.one_mulVec v, ← hQP', ← mulVec_mulVec, h1, mulVec_zero]
    funext i
    have := congrFun h2 (Sum.inl i)
    simpa [hv, sub_eq_zero] using this

  obtain ⟨g, hg⟩ := (Subgroup.mem_subgroupOf).1 hqr
  have hmq : mat q = (g : Matrix (Fin (b + 2)) (Fin (b + 2)) E).map f := by
    show ((q : GL (Fin (b + 2)) (AE F E)) : Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E)) = _
    rw [← hg]; rfl

  set g' : Matrix (Fin (b + 2)) (Fin (b + 2)) E := (g : Matrix (Fin (b + 2)) (Fin (b + 2)) E) with hg'
  have hgx : g' *ᵥ H.x = H.x := by
    funext i
    apply hfi
    have := congrFun hqx i
    rw [hmq] at this
    rw [RingHom.map_mulVec]
    exact this
  have hgu : g'ᵀ * G.V.J * g'.map σ = G.V.J := by
    have h2 : (mat q)ᵀ * incM F G.V.J * (mat q).map (cA σ) = incM F G.V.J := q.2
    rw [hmq, hmapσ] at h2
    have h3 : (g'ᵀ * G.V.J * g'.map σ).map f = G.V.J.map f := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]; exact h2
    exact Matrix.map_injective hfi h3
  set C := Q * g' * P with hCdef
  have hgP : g' * P = P * C := by
    rw [hCdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hCu : Cᵀ * K * C.map σ = K := by
    rw [← hK]
    calc Cᵀ * (Pᵀ * G.V.J * P.map σ) * C.map σ = (P * C)ᵀ * G.V.J * (P * C).map σ := by
          simp only [Matrix.transpose_mul, map_mul_alg, Matrix.mul_assoc]
      _ = (g' * P)ᵀ * G.V.J * (g' * P).map σ := by rw [hgP]
      _ = Pᵀ * (g'ᵀ * G.V.J * g'.map σ) * P.map σ := by
          simp only [Matrix.transpose_mul, map_mul_alg, Matrix.mul_assoc]
      _ = Pᵀ * G.V.J * P.map σ := by rw [hgu]
  have hPx : P *ᵥ Pi.single (Sum.inr 0) 1 = H.x := by
    rw [mulVec_single_one]; ext i; simp [P, cols2]
  have hC0 : C *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1 := by
    rw [hCdef, ← mulVec_mulVec, ← mulVec_mulVec, hPx, hgx, ← hPx, mulVec_mulVec, hQP, one_mulVec]
  have hCc : ∀ a, C a (Sum.inr 0) = (Pi.single (Sum.inr 0) 1 : Fin b ⊕ Fin 2 → E) a := fun a => by
    simpa [mulVec_single_one] using congrFun hC0 a
  have hc1 : ∀ j, C (Sum.inr 1) (Sum.inl j) = 0 := by
    intro j
    have h := congrFun (congrFun hCu (Sum.inl j)) (Sum.inr 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hKdef, swap2, hCc] at h
    exact h
  set g₀ : Matrix (Fin b) (Fin b) E := Matrix.of fun i j => C (Sum.inl i) (Sum.inl j) with hg₀
  set a₀ : Fin b → E := fun j => C (Sum.inr 0) (Sum.inl j) with ha₀
  have hgι : g' * H.ι = H.ι * g₀ + vecMulVec H.x a₀ := by
    ext r j
    have h := congrFun (congrFun hgP r) (Sum.inl j)
    simp [Matrix.mul_apply, hP, Fintype.sum_sum_type, Fin.sum_univ_two, cols2, hc1, vecMulVec, hg₀, ha₀] at h ⊢
    linear_combination h
  have hg₀u : g₀ᵀ * G₁.V.J * g₀.map σ = G₁.V.J := by
    ext i j
    have h := congrFun (congrFun hCu (Sum.inl i)) (Sum.inl j)
    simp [Matrix.mul_apply, hKdef, Fintype.sum_sum_type, Fin.sum_univ_two, swap2, hc1, hg₀] at h ⊢
    linear_combination h

  have hdet0 : g₀.det ≠ 0 := by
    intro h0; apply hdet
    have := congrArg Matrix.det hg₀u
    rw [det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul] at this
    exact this.symm
  set G0 : GL (Fin b) E := Matrix.GeneralLinearGroup.mkOfDetNeZero g₀ hdet0 with hG0
  have hG0v : (G0 : Matrix (Fin b) (Fin b) E) = g₀ := rfl
  have hγmem : Matrix.GeneralLinearGroup.map f G0 ∈ UG (cA σ) (incM F G₁.V.J) := by
    show ((G0 : Matrix (Fin b) (Fin b) E).map f)ᵀ * incM F G₁.V.J * ((G0 : Matrix (Fin b) (Fin b) E).map f).map (cA σ) = incM F G₁.V.J
    rw [hG0v, hmapσ, show incM F G₁.V.J = G₁.V.J.map f from rfl, ← Matrix.transpose_map, ← Matrix.map_mul,
      ← Matrix.map_mul, hg₀u]
  set γU : UA σ G₁.V.J := ⟨Matrix.GeneralLinearGroup.map f G0, hγmem⟩ with hγU
  have hmatγ : mat γU = g₀.map f := rfl
  have hγr : γU ∈ ratU σ G₁.V.J := Subgroup.mem_subgroupOf.2 ⟨G0, rfl⟩
  have hqι : mat q * incM F H.ι = incM F H.ι * mat γU + vecMulVec (incV F H.x) (fun j => f (a₀ j)) := by
    rw [hmq, hmatγ]
    show g'.map f * H.ι.map f = H.ι.map f * g₀.map f + _
    rw [← Matrix.map_mul, ← Matrix.map_mul, hgι]
    ext r j
    rw [Matrix.map_apply, Matrix.add_apply, map_add, Matrix.add_apply, Matrix.map_apply, vecMulVec_apply, vecMulVec_apply,
      map_mul]
    rfl
  obtain ⟨hmx, -, hmι⟩ := hm 1 γU
  simp only [Units.val_one, one_smul] at hmx
  have hmix : mat (m 1 γU)⁻¹ *ᵥ incV F H.x = incV F H.x := by
    calc mat (m 1 γU)⁻¹ *ᵥ incV F H.x = mat (m 1 γU)⁻¹ *ᵥ (mat (m 1 γU) *ᵥ incV F H.x) := by rw [hmx]
      _ = incV F H.x := by rw [mulVec_mulVec, mat_inv_mul', one_mulVec]
  have hγN : (m 1 γU)⁻¹ * q ∈ unip σ G.V H := by
    apply Subgroup.subset_closure
    refine ⟨?_, fun z => ⟨(fun j => f (a₀ j)) ⬝ᵥ z, ?_⟩⟩
    · rw [mat_mul', ← mulVec_mulVec, hqx, hmix]
    · have e : mat ((m 1 γU)⁻¹ * q) * incM F H.ι = incM F H.ι + vecMulVec (incV F H.x) (fun j => f (a₀ j)) := by
        rw [mat_mul', Matrix.mul_assoc, hqι, ← hmι, Matrix.mul_add, ← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul,
          Matrix.mul_vecMulVec, hmix]
      rw [mulVec_mulVec, e, add_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  refine ⟨⟨γU, hγr⟩, hγN, ?_⟩
  intro γ' hγ'
  have hd := (unip σ G.V H).mul_mem hγ' ((unip σ G.V H).inv_mem hγN)
  have hde : (m 1 (γ' : UA σ G₁.V.J))⁻¹ * q * ((m 1 γU)⁻¹ * q)⁻¹ = (m 1 (γ' : UA σ G₁.V.J))⁻¹ * m 1 γU := by group
  rw [hde] at hd
  obtain ⟨-, hdz⟩ := prop_of_mem_unip H hd
  obtain ⟨-, -, hmι'⟩ := hm 1 (γ' : UA σ G₁.V.J)
  have hinv' : mat (m 1 (γ' : UA σ G₁.V.J))⁻¹ * incM F H.ι = incM F H.ι * mat (γ' : UA σ G₁.V.J)⁻¹ :=
    inv_intertwine (mat_inv_mul' _) (mat_mul_inv' _) hmι'
  have hdι : mat ((m 1 (γ' : UA σ G₁.V.J))⁻¹ * m 1 γU) * incM F H.ι = incM F H.ι * mat ((γ' : UA σ G₁.V.J)⁻¹ * γU) := by
    rw [mat_mul', mat_mul', Matrix.mul_assoc, hmι, ← Matrix.mul_assoc, hinv', Matrix.mul_assoc]
  have hfix : ∀ z, mat ((γ' : UA σ G₁.V.J)⁻¹ * γU) *ᵥ z = z := by
    intro z
    obtain ⟨a, ha⟩ := hdz z
    rw [mulVec_mulVec, hdι, ← mulVec_mulVec] at ha
    exact hinj z _ a ha
  have h1 : (γ' : UA σ G₁.V.J)⁻¹ * γU = 1 := by
    apply eq_of_mat_eq
    ext i j
    have := congrFun (hfix (Pi.single j 1)) i
    rw [mulVec_single_one] at this
    simpa [mat_one', Matrix.one_apply, Pi.single_apply, eq_comm] using this
  exact Subtype.ext (inv_mul_eq_one.1 h1)

end GlobalTheory.LeviDecomp
