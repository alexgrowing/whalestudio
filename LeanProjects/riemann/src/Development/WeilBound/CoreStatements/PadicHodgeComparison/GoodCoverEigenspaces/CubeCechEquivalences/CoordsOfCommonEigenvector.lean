import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.MemRangeOfSol

open Matrix TensorProduct

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

theorem coords_of_common_eigenvector {k k' M M' I J : Type*} [Field k] [Field k'] [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k' M']
    [Fintype I] [DecidableEq I] (φ : k →+* k') (β : M →ₛₗ[φ] M') (c : Module.Basis I k M) (c' : Module.Basis I k' M')
    (hc : ∀ i, c' i = β (c i)) (T : J → Module.End k M) (S : J → Module.End k' M') (h : ∀ j x, β (T j x) = S j (β x))
    (θ : J → k') (x : M') (hx0 : x ≠ 0) (hx : ∀ j, S j x = θ j • x) :
    ∃ y : I → k', y ≠ 0 ∧ ∀ j, (LinearMap.toMatrix c c (T j)).map φ *ᵥ y = θ j • y := by
  have hm : ∀ j, (LinearMap.toMatrix c c (T j)).map φ = LinearMap.toMatrix c' c' (S j) := fun j => by
    ext p q
    rw [map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hc, ← h]
    conv_rhs => rw [← c.sum_repr (T j (c q)), map_sum]
    simp [LinearMap.map_smulₛₗ, ← hc, Finsupp.single_apply]
  refine ⟨c'.repr x, fun h0 => hx0 (c'.repr.injective (by ext p; simpa using congrFun h0 p)), fun j => ?_⟩
  rw [hm, LinearMap.toMatrix_mulVec_repr, hx, map_smul]
  rfl

theorem exists_emb {k L M U I : Type*} [Field k] [Field L] [Algebra k L] [AddCommGroup M] [Module k M] [AddCommGroup U]
    [Module k U] [Fintype I] [DecidableEq I] (b : Module.Basis I k M) (f : M →ₗ[k] U) (hf : Function.Injective f) :
    ∃ E : (I → L) →ₗ[L] L ⊗[k] U, Function.Injective E ∧ ∀ (T : M →ₗ[k] M) (S : U →ₗ[k] U), (∀ x, S (f x) = f (T x)) →
      ∀ v, S.baseChange L (E v) = E ((LinearMap.toMatrix b b T).map (algebraMap k L) *ᵥ v) := by
  let c := Algebra.TensorProduct.basis L b
  refine ⟨f.baseChange L ∘ₗ c.equivFun.symm.toLinearMap, ?_, fun T S h v => ?_⟩
  · exact (Module.Flat.lTensor_preserves_injective_linearMap (M := L) f hf).comp c.equivFun.symm.injective
  · have h1 : S ∘ₗ f = f ∘ₗ T := LinearMap.ext h
    have h2 : T.baseChange L (c.equivFun.symm v) = c.equivFun.symm ((LinearMap.toMatrix b b T).map (algebraMap k L) *ᵥ v) := by
      rw [← LinearMap.toMatrix_baseChange, LinearEquiv.eq_symm_apply, Module.Basis.equivFun_apply,
        ← LinearMap.toMatrix_mulVec_repr c c]
      exact congrArg _ (c.equivFun.apply_symm_apply v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h2, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h1, LinearMap.baseChange_comp, LinearMap.comp_apply]

theorem block_eig {k o : Type*} [Field k] [Fintype o] [DecidableEq o] {e : o → Type*} [∀ r, Fintype (e r)] [∀ r, DecidableEq (e r)]
    (M : ∀ r, Matrix (e r) (e r) k) (r₀ : o) (y : e r₀ → k) (t : k) (h : M r₀ *ᵥ y = t • y) :
    ∃ Y : (Σ r, e r) → k, (∀ i, Y ⟨r₀, i⟩ = y i) ∧ (∀ p, Y p ≠ 0 → p.1 = r₀) ∧
      ∀ (M' : ∀ r, Matrix (e r) (e r) k) (t' : k), M' r₀ *ᵥ y = t' • y →
        (blockDiagonal' M' - t' • (1 : Matrix (Σ r, e r) (Σ r, e r) k)) ^ 1 *ᵥ Y = 0 := by
  let Y : (Σ r, e r) → k := fun p => if h : p.1 = r₀ then y (h ▸ p.2) else 0
  have h1 : ∀ i, Y ⟨r₀, i⟩ = y i := fun i => dif_pos rfl
  have h2 : ∀ p, p.1 ≠ r₀ → Y p = 0 := fun p hp => dif_neg hp
  refine ⟨Y, h1, fun p hp => by_contra fun hn => hp (h2 p hn), fun M' t' h' => funext fun ⟨r, i⟩ => ?_⟩
  rw [pow_one, sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero, mulVec, dotProduct,
    Fintype.sum_sigma, Finset.sum_eq_single r]
  · by_cases hr : r = r₀
    · subst hr
      simp only [blockDiagonal'_apply_eq, h1, Pi.smul_apply]
      exact congrFun h' i
    · simp [h2 _ (show (⟨r, _⟩ : Σ r, e r).1 ≠ r₀ from hr)]
  · intro r' _ hr'
    exact Finset.sum_eq_zero fun q _ => by rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hr'), zero_mul]
  · simp

variable {k C : Type*} [Field k] [Field C] [Algebra k C]

theorem occ1 {Γ m n d J : Type*} [Fintype m] [Fintype n] [Fintype d] [DecidableEq m] [DecidableEq n]
    (a : Γ → C →+* C) (R : Γ → Matrix m m k) (Φ : Matrix m n C) (hΦi : Function.Injective Φ.mulVec) (w : Γ → n → C)
    (hΦ : ∀ σ, (R σ).map (algebraMap k C) * Φ.map (a σ) = Φ * diagonal (w σ))
    (TV : J → Matrix m m k) (TH : J → Matrix n n k)
    (hT : ∀ j, (TV j).map (algebraMap k C) * Φ = Φ * (TH j).map (algebraMap k C)) (θ : J → k)
    (y : n → k) (hy : y ≠ 0) (c : Γ → C) (hw : ∀ σ p, y p ≠ 0 → w σ p = c σ)
    (he : ∀ j, (TH j - θ j • (1 : Matrix n n k)) ^ 1 *ᵥ y = 0)
    (B : Matrix m d k) (hBi : Function.Injective B.mulVec)
    (hB : ∀ v : m → k, (∀ j, (TV j - θ j • (1 : Matrix m m k)) ^ 1 *ᵥ v = 0) → ∃ u, B *ᵥ u = v)
    (ρ : Γ → Matrix d d k) (hρ : ∀ σ, R σ * B = B * ρ σ) :
    ∃ z : d → C, z ≠ 0 ∧ ∀ σ, (∀ p, a σ (algebraMap k C (y p)) = algebraMap k C (y p)) →
      (∀ p q, a σ (algebraMap k C (B p q)) = algebraMap k C (B p q)) →
      (ρ σ).map (algebraMap k C) *ᵥ (fun q => a σ (z q)) = c σ • z := by
  classical
  have hN := he
  set i := algebraMap k C
  let yC : n → C := fun p => i (y p)
  have hpow : ∀ j r, ((TV j - θ j • (1 : Matrix m m k)) ^ r).map i * Φ = Φ * ((TH j - θ j • (1 : Matrix n n k)) ^ r).map i := by
    intro j r
    have h1 : (TV j - θ j • (1 : Matrix m m k)).map i * Φ = Φ * (TH j - θ j • (1 : Matrix n n k)).map i := by
      have e1 : (TV j - θ j • (1 : Matrix m m k)).map i = (TV j).map i - i (θ j) • (1 : Matrix m m C) := by
        ext p q; by_cases h : p = q <;> simp [h, one_apply]
      have e2 : (TH j - θ j • (1 : Matrix n n k)).map i = (TH j).map i - i (θ j) • (1 : Matrix n n C) := by
        ext p q; by_cases h : p = q <;> simp [h, one_apply]
      rw [e1, e2, Matrix.sub_mul, Matrix.mul_sub, hT, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    induction r with
    | zero => simp [Matrix.map_one _ (map_zero i) (map_one i)]
    | succ r ih => rw [pow_succ, pow_succ, Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  obtain ⟨z, hz⟩ := mem_range_of_sol (C := C) (fun j => (TV j - θ j • (1 : Matrix m m k)) ^ 1) B
    (fun v hv => hB v hv) (Φ *ᵥ yC) fun j => by
      rw [mulVec_mulVec, hpow, ← mulVec_mulVec]
      have : ((TH j - θ j • (1 : Matrix n n k)) ^ 1).map i *ᵥ yC = 0 := funext fun p => by
        have := congrArg i (congrFun (hN j) p)
        rw [RingHom.map_mulVec] at this
        exact this.trans (map_zero i)
      rw [this, mulVec_zero]
  refine ⟨z, fun h0 => hy (funext fun p => ?_), fun σ h1 h2 => map_injective (C := C) B hBi ?_⟩
  · have : yC = 0 := hΦi (by rw [← hz, h0, mulVec_zero, mulVec_zero])
    exact (map_eq_zero i).1 (congrFun this p)
  · have hBσ : (B.map i).map (a σ) = B.map i := by ext p q; exact h2 p q
    have hx : B.map i *ᵥ (fun q => a σ (z q)) = Φ.map (a σ) *ᵥ yC := funext fun p => by
      have e1 := (RingHom.map_mulVec (a σ) (B.map i) z p).symm
      have e2 := RingHom.map_mulVec (a σ) Φ yC p
      have e3 : (⇑(a σ) ∘ yC) = yC := funext h1
      rw [hBσ, hz, e2, e3] at e1
      exact e1
    change B.map i *ᵥ _ = B.map i *ᵥ _
    rw [mulVec_mulVec, ← Matrix.map_mul, ← hρ, Matrix.map_mul, ← mulVec_mulVec, hx, mulVec_mulVec, hΦ, ← mulVec_mulVec,
      mulVec_smul, hz, ← mulVec_smul]
    congr 1
    funext p
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hp : y p = 0
    · simp [yC, hp]
    · rw [hw σ p hp]

theorem occE {U : Type*} [AddCommGroup U] [Module k U]
    {Γ m n d J : Type*} [Fintype m] [Fintype n] [Fintype d] [DecidableEq m] [DecidableEq n]
    (a : Γ → C →+* C) (R : Γ → Matrix m m k) (Φ : Matrix m n C) (hΦi : Function.Injective Φ.mulVec) (w : Γ → n → C)
    (hΦ : ∀ σ, (R σ).map (algebraMap k C) * Φ.map (a σ) = Φ * diagonal (w σ))
    (TV : J → Matrix m m k) (TH : J → Matrix n n k)
    (hT : ∀ j, (TV j).map (algebraMap k C) * Φ = Φ * (TH j).map (algebraMap k C)) (θ : J → k)
    (y : n → k) (hy : y ≠ 0) (c : Γ → C) (hw : ∀ σ p, y p ≠ 0 → w σ p = c σ)
    (he : ∀ j, (TH j - θ j • (1 : Matrix n n k)) ^ 1 *ᵥ y = 0)
    (E : (m → k) →ₗ[k] U) (hE : Function.Injective E) (op : J → Module.End k U) (hop : ∀ j v, op j (E v) = E (TV j *ᵥ v))
    (g : Γ → Module.End k U) (hg : ∀ σ v, g σ (E v) = E (R σ *ᵥ v))
    (V : Submodule k U) (hV : V = ⨅ j, Module.End.eigenspace (op j) (θ j)) (b : Module.Basis d k V) (ρ : Γ → Matrix d d k)
    (hρ : ∀ σ q, g σ (b q) = ∑ p, ρ σ p q • (b p).1) :
    ∃ (S : Finset k) (z : d → C), z ≠ 0 ∧ ∀ σ, (∀ x ∈ S, a σ (algebraMap k C x) = algebraMap k C x) →
      (ρ σ).map (algebraMap k C) *ᵥ (fun q => a σ (z q)) = c σ • z := by
  classical
  have hpow : ∀ j (N : ℕ) v, ((op j - θ j • 1) ^ N) (E v) = E ((TV j - θ j • (1 : Matrix m m k)) ^ N *ᵥ v) := by
    intro j N
    induction N with
    | zero => intro v; simp
    | succ N ih =>
      intro v
      rw [pow_succ, pow_succ, Module.End.mul_apply, ← mulVec_mulVec, ← ih]
      congr 1
      simp [hop, sub_mulVec, smul_mulVec]
  have hmem : ∀ v, E v ∈ V ↔ ∀ j, (TV j - θ j • (1 : Matrix m m k)) ^ 1 *ᵥ v = 0 := fun v => by
    rw [hV, Submodule.mem_iInf]
    refine forall_congr' fun j => ?_
    rw [Module.End.mem_eigenspace_iff, ← map_eq_zero_iff _ hE, ← hpow, pow_one, LinearMap.sub_apply, sub_eq_zero]
    rfl
  have hst : ∀ σ (u : V), g σ u ∈ V ∧ ∀ h : g σ u ∈ V, ⇑(b.repr ⟨g σ u, h⟩) = ρ σ *ᵥ ⇑(b.repr u) := by
    intro σ u
    have h1 : g σ u = ((∑ p, (ρ σ *ᵥ ⇑(b.repr u)) p • b p : V) : U) := by
      have h0 : (u : U) = ∑ q, b.repr u q • (b q).1 := by
        conv_lhs => rw [← b.sum_repr u]
        simp only [Submodule.coe_sum, Submodule.coe_smul]
      have hρ' : ∀ q, g σ (b q).1 = ∑ p, ρ σ p q • (b p).1 := hρ σ
      rw [h0, map_sum, Submodule.coe_sum]
      simp only [mulVec, dotProduct, Submodule.coe_smul]
      simp only [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, hρ', Finset.smul_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [smul_smul, mul_comm]
    refine ⟨h1 ▸ Subtype.property _, fun h => ?_⟩
    rw [show (⟨g σ u, h⟩ : V) = ∑ p, (ρ σ *ᵥ ⇑(b.repr u)) p • b p from Subtype.ext h1]
    exact b.repr_sum_self _
  let W : Submodule k (m → k) := V.comap E
  let e := Module.finBasis k W
  let B : Matrix m (Fin (Module.finrank k W)) k := fun p q => (e q).1 p
  have hB : ∀ u, B *ᵥ u = ((∑ q, u q • e q : W) : m → k) := fun u => funext fun p => by
    simp [B, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hR : ∀ σ (v : W), R σ *ᵥ v.1 ∈ W := fun σ v => by
    change E _ ∈ V
    rw [← hg]
    exact (hst σ ⟨E v, v.2⟩).1
  let ρ' : Γ → Matrix (Fin (Module.finrank k W)) (Fin (Module.finrank k W)) k := fun σ p q => e.repr ⟨_, hR σ (e q)⟩ p
  let A : Matrix d (Fin (Module.finrank k W)) k := fun p q => b.repr ⟨E (e q), (e q).2⟩ p
  have hA : ∀ u, A *ᵥ u = ⇑(b.repr ⟨E (∑ q, u q • e q : W), (∑ q, u q • e q : W).2⟩) := fun u => by
    have : (⟨E (∑ q, u q • e q : W), (∑ q, u q • e q : W).2⟩ : V) = ∑ q, u q • (⟨E (e q), (e q).2⟩ : V) :=
      Subtype.ext (by simp)
    rw [this]
    funext p
    simp only [A, mulVec, dotProduct, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  have hinj : ∀ u u' : Fin (Module.finrank k W) → k, (∑ q, u q • e q : W) = ∑ q, u' q • e q → u = u' := fun u u' h => by
    have := congrArg (fun t => ⇑(e.repr t)) h
    simpa only [e.repr_sum_self] using this
  have hcol : ∀ σ q, (∑ p, ρ' σ p q • e p : W) = ⟨_, hR σ (e q)⟩ := fun σ q => e.sum_repr _
  obtain ⟨z, hz, hz'⟩ := occ1 a R Φ hΦi w hΦ TV TH hT θ y hy c hw he B
    (fun u u' h => hinj u u' (Subtype.ext (by rw [← hB, ← hB]; exact h)))
    (fun v hv => ⟨e.repr ⟨v, (hmem v).2 hv⟩, by rw [hB, e.sum_repr]⟩) ρ'
    (fun σ => by
      ext p q
      exact (congrFun ((hB fun r => ρ' σ r q).trans (congrArg Subtype.val (hcol σ q))) p).symm)
  have hAi : Function.Injective A.mulVec := fun u u' h => hinj u u' (by
    rw [hA, hA] at h
    exact Subtype.ext (hE (congrArg Subtype.val (b.repr.injective (DFunLike.coe_injective h)))))
  have hAρ : ∀ σ, ρ σ * A = A * ρ' σ := fun σ => by
    ext p q
    have h1 := congrFun ((hst σ ⟨E (e q), (e q).2⟩).2 (hst σ _).1) p
    have h2 := congrFun (hA fun r => ρ' σ r q) p
    refine h1.symm.trans (Eq.trans ?_ h2.symm)
    congr 2
    exact Subtype.ext (by rw [hcol]; exact hg σ _)
  refine ⟨(Finset.univ.image y ∪ Finset.univ.image fun t : m × _ => B t.1 t.2) ∪ Finset.univ.image fun t : d × _ => A t.1 t.2,
    A.map (algebraMap k C) *ᵥ z, fun h0 => hz (map_injective (C := C) A hAi (by rw [h0, mulVec_zero])), fun σ hS => ?_⟩
  have h3 := hz' σ (fun p => hS _ (by simp)) fun p q => hS _ (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨(p, q), Finset.mem_univ _, rfl⟩)))
  have h4 : (A.map (algebraMap k C)).map (a σ) = A.map (algebraMap k C) := by
    ext p q; exact hS _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(p, q), Finset.mem_univ _, rfl⟩))
  have h5 : (fun q => a σ ((A.map (algebraMap k C) *ᵥ z) q)) = A.map (algebraMap k C) *ᵥ fun q => a σ (z q) := funext fun p => by
    rw [RingHom.map_mulVec, h4]; rfl
  rw [h5, mulVec_mulVec, ← Matrix.map_mul, hAρ, Matrix.map_mul, ← mulVec_mulVec, h3, mulVec_smul]

end PositivityTheory.AutomorphicGaloisHodgeTate.G8
