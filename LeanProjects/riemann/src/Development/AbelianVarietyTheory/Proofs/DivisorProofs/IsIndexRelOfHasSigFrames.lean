import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLatTQuotPure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSigFramesPatPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsPointGaussian

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.IndexIdeal
open scoped TensorProduct NNReal

namespace GlobalTheory.HTIndex

section Algebra

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {v : Valuation C ℝ≥0}

omit [Module O U] [IsScalarTower O C U] in
theorem indep_comb {n : ℕ} {w : Fin n → U} (hw : LinearIndependent C w) {a : Matrix (Fin n) (Fin n) C}
    (ha : a.det ≠ 0) : LinearIndependent C fun i => ∑ j, a i j • w j :=
  (Matrix.linearIndependent_rows_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det a).2 ha.isUnit)).map'
    (Fintype.linearCombination C w)
    (LinearMap.ker_eq_bot.2 fun s t h => funext (Fintype.linearIndependent_iffₛ.1 hw s t h))

omit [Module O U] [IsScalarTower O C U] in
theorem eq_inv_comb {n : ℕ} (w : Fin n → U) {a : Matrix (Fin n) (Fin n) C} (ha : a.det ≠ 0) (i : Fin n) :
    w i = ∑ j, a⁻¹ i j • ∑ k, a j k • w k := by
  have h := comb_comb (x := fun i => ∑ j, a⁻¹ i j • ∑ k, a j k • w k) (y := fun j => ∑ k, a j k • w k) (z := w)
    (fun _ => rfl) (fun _ => rfl) i
  rw [Matrix.nonsing_inv_mul _ ha.isUnit] at h
  simpa [Matrix.one_apply] using h.symm

omit [Module O U] [IsScalarTower O C U] in
theorem span_comb {n : ℕ} (w : Fin n → U) {a : Matrix (Fin n) (Fin n) C} (ha : a.det ≠ 0) :
    Submodule.span C (Set.range fun i => ∑ j, a i j • w j) = Submodule.span C (Set.range w) :=
  le_antisymm
    (Submodule.span_le.2 (Set.range_subset_iff.2 fun _ => Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)))
    (Submodule.span_le.2 (Set.range_subset_iff.2 fun i => (eq_inv_comb w ha i).symm ▸ Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)))

theorem exists_hasIndex {n : ℕ} {w x : Fin n → U} (hw : LinearIndependent C w) {a : Matrix (Fin n) (Fin n) C}
    (ha : a.det ≠ 0) (hx : ∀ i, x i = ∑ j, a i j • w j) (hm : ∀ i, x i ∈ Submodule.span O (Set.range w)) :
    ∃ d : O, algebraMap O C d = a.det ∧
      HasIndex C n (Submodule.span O (Set.range w)) (Submodule.span O (Set.range x)) (Ideal.span {d}) := by
  obtain ⟨g, hg⟩ := exists_matrix (C := C) (Submodule.span_le.2 (Set.range_subset_iff.2 hm))
  have e : algebraMap O C g.det = a.det := by rw [RingHom.map_det, comb_inj hw hx hg]; rfl
  refine ⟨g.det, e, w, g, hw, rfl, ?_, fun h => ha (by rw [← e, h, map_zero]), rfl⟩
  congr 2
  funext i
  simp only [hg i, Matrix.map_apply, algebraMap_smul]

theorem exists_block_basis (hv : v.Integers O) {p q : ℕ} {L : Submodule O U} {u : Fin p → U} {u' : Fin q → U}
    {I : Ideal O} (hI : HasIndex C (p + q) L (Submodule.span O (Set.range u) ⊔ Submodule.span O (Set.range u')) I) :
    ∃ (g₁ : Matrix (Fin p) (Fin p) C) (g' : Matrix (Fin q) (Fin p) C) (g₂ : Matrix (Fin q) (Fin q) C) (d : O),
      LinearIndependent C u ∧ algebraMap O C d * (g₁.det * g₂.det) = 1 ∧ Ideal.span {d} = I ∧
      Submodule.span O (Set.range fun i => ∑ j, g₁ i j • u j) =
        L ⊓ (Submodule.span C (Set.range u)).restrictScalars O ∧
      Submodule.span O (Set.range fun i => ∑ j, g₁ i j • u j) ⊔
        Submodule.span O (Set.range fun i => ∑ j, g' i j • u j + ∑ j, g₂ i j • u' j) = L := by
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  let b : Fin (p + q) → U := Sum.elim u u' ∘ e.symm
  have hb : Submodule.span O (Set.range b) = Submodule.span O (Set.range u) ⊔ Submodule.span O (Set.range u') := by
    rw [e.symm.surjective.range_comp, Set.Sum.elim_range, Submodule.span_union]
  have hle := hI.le
  obtain ⟨w, g₀, hw, hL, hL', hg₀, -⟩ := id hI
  have hd₀ : (g₀.map (algebraMap O C)).det ≠ 0 := fun h =>
    hg₀ (hv.hom_inj (by rw [RingHom.map_det, map_zero]; exact h))
  have hbw : Submodule.span C (Set.range b) = Submodule.span C (Set.range w) := by
    rw [← Submodule.span_span_of_tower O C, hb, ← hL', Submodule.span_span_of_tower, ← span_comb w hd₀]
    simp only [Matrix.map_apply, algebraMap_smul]
  have hbi : LinearIndependent C b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hbw, finrank_span_eq_card hw]
  obtain ⟨g, g1, g2, g3⟩ := FlagBasis.exists_adapted_basis O C U v hv (p + q) L
    (hL ▸ Submodule.fg_span (Set.finite_range w)) b hbi fun j =>
      ⟨1, one_ne_zero, by rw [one_smul]; exact hle (hb ▸ Submodule.subset_span ⟨j, rfl⟩)⟩
  have hg : g.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular _ fun i j hij => g1 i j hij]
    exact Finset.prod_ne_zero_iff.2 fun i _ => g2 i
  have ht : Submodule.span O (Set.range fun i => ∑ j, g i j • b j) = L := by
    rw [g3.2, span_comb b hg, hbw, inf_eq_left, ← hL]
    exact Submodule.span_le_restrictScalars O C _
  obtain ⟨d, hd, hd'⟩ := hI.det hv.hom_inj ht hb (eq_inv_comb b hg)
  let G := g.submatrix e e
  have h12 : G.toBlocks₁₂ = 0 := Matrix.ext fun i j => g1 _ _ (by
    simp only [e, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega)
  have hdet : g.det = G.toBlocks₁₁.det * G.toBlocks₂₂.det := by
    rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_fromBlocks_zero₁₂ _ G.toBlocks₂₁, ← h12,
      Matrix.fromBlocks_toBlocks]
  have hs : ∀ s, ∑ j, g (e s) j • b j = ∑ j, G s (.inl j) • u j + ∑ j, G s (.inr j) • u' j := fun s => by
    rw [← e.sum_comp, Fintype.sum_sum_type]
    simp [b, G]
  have hl : ∀ i, ∑ j, g (e (.inl i)) j • b j = ∑ j, G.toBlocks₁₁ i j • u j := fun i => by
    have : ∀ j, G (.inl i) (.inr j) = 0 := fun j => congrFun (congrFun h12 i) j
    simp only [hs, this, zero_smul, Finset.sum_const_zero, add_zero]
    rfl
  have hsup : Submodule.span O (Set.range fun i => ∑ j, G.toBlocks₁₁ i j • u j) ⊔
      Submodule.span O (Set.range fun i => ∑ j, G.toBlocks₂₁ i j • u j + ∑ j, G.toBlocks₂₂ i j • u' j) = L := by
    rw [← ht, ← e.surjective.range_comp, ← Submodule.span_union, ← Set.Sum.elim_range]
    congr 2
    funext s
    rcases s with i | i
    exacts [(hl i).symm, (hs (.inr i)).symm]
  have h1 : G.toBlocks₁₁.det ≠ 0 := left_ne_zero_of_mul (hdet ▸ hg)
  refine ⟨G.toBlocks₁₁, G.toBlocks₂₁, G.toBlocks₂₂, d, ?_, ?_, hd', le_antisymm (le_inf (le_sup_left.trans hsup.le) ?_) ?_,
    hsup⟩
  · simpa [b, Function.comp_def] using hbi.comp (e ∘ .inl) (e.injective.comp Sum.inl_injective)
  · rw [hd, ← hdet, Matrix.det_nonsing_inv_mul_det _ hg.isUnit]
  · rw [← span_comb u h1]
    exact Submodule.span_le_restrictScalars O C _
  · rintro x ⟨hx, hx'⟩
    rw [← span_comb u h1] at hx'
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hx'
    have := (g3.sum_mem_iff (Sum.elim c 0 ∘ e.symm)).1 (by
      rw [← e.sum_comp, Fintype.sum_sum_type]
      simpa [hl] using hx)
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨o, ho⟩ := this (e (.inl i))
    have ho' : c i = algebraMap O C o := by simpa using ho.symm
    rw [ho', algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem index_mul_gram [FiniteDimensional C U] (hv : v.Integers O) {p q : ℕ} (B : U →ₗ[C] U →ₗ[C] C)
    {L S : Submodule O U} {W W' : Submodule C U} {u : Fin p → U} {u' z : Fin q → U} {I : Ideal O}
    (hI : HasIndex C (p + q) L (Submodule.span O (Set.range u) ⊔ Submodule.span O (Set.range u')) I)
    (hW : Module.finrank C W = p) (hW' : Module.finrank C W' = q) (hu : ∀ a, u a ∈ W) (hz : ∀ b, z b ∈ W')
    (hzS : ∀ b, z b ∈ S) (hS : ∀ y ∈ W', y ∈ S ↔ ∀ x ∈ L, ∃ c : O, algebraMap O C c = B x y)
    (horth : ∀ a b, B (u a) (z b) = 0) {G : Matrix (Fin q) (Fin q) O} (hG : G.det ≠ 0)
    (hGram : ∀ a b, B (u' a) (z b) = algebraMap O C (G a b)) :
    ∃ I₁ I₂ : Ideal O, HasIndex C p (L ⊓ W.restrictScalars O) (Submodule.span O (Set.range u)) I₁ ∧
      HasIndex C q (S ⊓ W'.restrictScalars O) (Submodule.span O (Set.range z)) I₂ ∧
      I₁ * Ideal.span {G.det} = I * I₂ := by
  obtain ⟨g₁, g', g₂, d, hui, hd, rfl, h₁, h₂⟩ := exists_block_basis hv hI
  have hne : g₁.det * g₂.det ≠ 0 := right_ne_zero_of_mul (hd ▸ one_ne_zero)
  have hg₁ := left_ne_zero_of_mul hne
  have hspan : ∀ {n : ℕ} {x : Fin n → U} {F : Submodule C U}, LinearIndependent C x → (∀ a, x a ∈ F) →
      Module.finrank C F = n → Submodule.span C (Set.range x) = F := fun hx hF hn =>
    Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 (Set.range_subset_iff.2 hF))
      (by rw [finrank_span_eq_card hx, Fintype.card_fin, hn])
  rw [hspan hui hu hW] at h₁
  obtain ⟨d₁, hd₁, hI₁⟩ := exists_hasIndex (O := O) (indep_comb hui hg₁) (Matrix.isUnit_nonsing_inv_det _ hg₁.isUnit).ne_zero
    (eq_inv_comb u hg₁) fun i => h₁.ge ⟨hI.le (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)), hu i⟩
  rw [h₁] at hI₁
  have hGC : (G.map (algebraMap O C)).det = algebraMap O C G.det := (RingHom.map_det _ _).symm
  let Q := (g₂ * G.map (algebraMap O C)).transpose
  have hQd : Q.det = g₂.det * algebraMap O C G.det := by rw [Matrix.det_transpose, Matrix.det_mul, hGC]
  have hQ : Q.det ≠ 0 := hQd ▸ mul_ne_zero (right_ne_zero_of_mul hne) fun h => hG (hv.hom_inj (by rw [h, map_zero]))
  let t : Fin q → U := fun i => ∑ j, g' i j • u j + ∑ j, g₂ i j • u' j
  let x : Fin q → U := fun k => ∑ b, Q⁻¹ k b • z b
  have htz : ∀ j b, B (t j) (z b) = Q b j := fun j b => by
    simp only [t, map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, horth, hGram,
      smul_zero, Finset.sum_const_zero, zero_add]
    rfl
  have htx : ∀ j (c : Fin q → C), B (t j) (∑ k, c k • x k) = c j := fun j c => by
    have : ∀ k, B (t j) (x k) = (1 : Matrix _ _ C) k j := fun k => by
      rw [← Matrix.nonsing_inv_mul _ hQ.isUnit]
      simp [x, htz, Matrix.mul_apply]
    simp [this, Matrix.one_apply]
  have hxi : LinearIndependent C x := Fintype.linearIndependent_iff.2 fun c hc j => by rw [← htx j c, hc, map_zero]
  have hxW : ∀ k, x k ∈ W' := fun k => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hz b)
  have hzx : ∀ b, z b = ∑ k, Q b k • x k := fun b => by
    have := eq_inv_comb z (Matrix.isUnit_nonsing_inv_det _ hQ.isUnit).ne_zero b
    rwa [Matrix.nonsing_inv_nonsing_inv _ hQ.isUnit] at this
  have hx : Submodule.span O (Set.range x) = S ⊓ W'.restrictScalars O := by
    refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 fun k => ⟨(hS _ (hxW k)).2 fun l hl => ?_, hxW k⟩)) ?_
    · have : L ≤ (LinearMap.range (Algebra.linearMap O C)).comap ((B.flip (x k)).restrictScalars O) := by
        rw [← h₂]
        refine sup_le (Submodule.span_le.2 (Set.range_subset_iff.2 fun i => ⟨0, ?_⟩))
          (Submodule.span_le.2 (Set.range_subset_iff.2 fun i => ⟨(Pi.single k 1 : Fin q → O) i, ?_⟩))
        · simp [x, horth]
        · have := htx i (Pi.single k 1)
          simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
          exact Eq.trans (by simp [Pi.single_apply, apply_ite]) this.symm
      exact this hl
    · rintro y ⟨hy, hy'⟩
      have hy'' : y ∈ Submodule.span C (Set.range x) := (hspan hxi hxW hW').ge hy'
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hy''
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨o, ho⟩ := (hS _ hy').1 hy (t i) (h₂.le (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)))
      rw [htx] at ho
      rw [← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨d₂, hd₂, hI₂⟩ := exists_hasIndex (O := O) hxi hQ hzx fun b => hx.ge ⟨hzS b, hz b⟩
  rw [hx] at hI₂
  refine ⟨_, _, hI₁, hI₂, ?_⟩
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
  congr 2
  refine hv.hom_inj ?_
  rw [map_mul, map_mul, hd₁, hd₂, hQd, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, eq_inv_of_mul_eq_one_left hd]
  field_simp [right_ne_zero_of_mul hne]

theorem iSup_map_span {U U' : Type} [AddCommGroup U] [Module O U] [AddCommGroup U'] [Module O U'] {n : ℕ}
    (f : Fin n → (U →ₗ[O] U')) (y : U) :
    ⨆ a, (Submodule.span O {y}).map (f a) = Submodule.span O (Set.range fun a => f a y) := by
  simp only [Submodule.map_span, Set.image_singleton, Submodule.span_range_eq_iSup]

theorem val_det_frame (hv : v.Integers O) {U' : Type} [AddCommGroup U'] [Module C U'] [Module O U']
    [IsScalarTower O C U'] {n : ℕ} {La : Submodule O U} {F : Submodule C U} {La' : Submodule O U'} {F' : Submodule C U'}
    {f : Fin n → (U' →ₗ[C] U)} {d : O} (h : HasIndex C n (La ⊓ F.restrictScalars O)
      (⨆ a, (La' ⊓ F'.restrictScalars O).map ((f a).restrictScalars O)) (Ideal.span {d}))
    {x : Fin n → U} {g : Matrix (Fin n) (Fin n) C} (hg : g.det ≠ 0) (hx : Submodule.span C (Set.range x) = F)
    (hb : IsLatBasis C La fun i => ∑ j, g i j • x j) {y : Fin 1 → U'} {c : Matrix (Fin 1) (Fin 1) C} (hc : c.det ≠ 0)
    (hy : Submodule.span C (Set.range y) = F') (hb' : IsLatBasis C La' fun i => ∑ j, c i j • y j)
    {m : Matrix (Fin n) (Fin n) C} (hm : ∀ a, f a (y 0) = ∑ k, m a k • x k) :
    v c.det ^ n * v m.det = v g.det * v (algebraMap O C d) := by
  have e := hb.2
  have e' := hb'.2
  rw [span_comb x hg, hx] at e
  rw [span_comb y hc, hy, Set.range_unique] at e'
  rw [← e', iSup_map_span] at h
  have := h.val_det hv e rfl (a := c.det • (m * g⁻¹)) fun a => by
    have h1 := comb_comb hm (eq_inv_comb x hg) a
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← h1]
    simp
  rw [← this, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Fintype.card_fin, ← map_pow,
    ← map_mul, ← map_mul]
  congr 1
  field_simp

end Algebra

section Points

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C] {Λ : Type} [CommRing Λ] [StarRing Λ]
  {J : Type} [DecidableEq J] {σ : J → Λ →+* O} (hs : IsSplitting (embC C σ)) (k : J)

theorem wHT_eq_of_rank_one (P : Point ℓ v O Λ) {y : P.V} (hy : Submodule.span O {y} = P.latTQuot hs k)
    (hW : Module.finrank C (P.eigW (σ k)) = 1) : y ∈ P.eigW (σ k) ∧ P.wHT hs k = Submodule.span O {y} := by
  have hle : P.eigW (σ k) ≤ Submodule.span C {y} := fun x hx => by
    obtain ⟨a, ha, h⟩ := P.exists_smul_mem_latT x
    have ha' : algebraMap O C a ≠ 0 := fun h0 => ha (P.integers.hom_inj (by rw [h0, map_zero]))
    have h1 : a • x ∈ Submodule.span O {y} := hy.ge (P.latTSub_le_latTQuot hs k
      ⟨h, by rw [← algebraMap_smul C]; exact (P.eigV (σ k)).smul_mem _ hx.2⟩)
    have h2 := Submodule.span_le_restrictScalars O C _ h1
    rw [← algebraMap_smul C] at h2
    exact (Submodule.smul_mem_iff _ ha').1 h2
  have he : P.eigW (σ k) = Submodule.span C {y} := Submodule.eq_of_le_of_finrank_le hle
    (hW ▸ (finrank_span_le_card _).trans (by simp))
  refine ⟨he.ge (Submodule.mem_span_singleton_self y), ?_⟩
  rw [Point.wHT, ← hy, he, inf_eq_left]
  exact Submodule.span_le_restrictScalars O C _

theorem exists_dual_of_rank_one (P : Point ℓ v O Λ) {y : P.V} (hy : Submodule.span O {y} = P.latTQuot hs k)
    (hW : Module.finrank C (P.eigW ((σ k).comp (starRingEnd Λ))) = 1) :
    ∃ z ∈ P.eigW ((σ k).comp (starRingEnd Λ)), P.pairV y z = 1 ∧
      P.latTSub ((σ k).comp (starRingEnd Λ)) ⊓ (P.eigW ((σ k).comp (starRingEnd Λ))).restrictScalars O =
        Submodule.span O {z} := by
  obtain ⟨⟨z₀, hz₀⟩, h0, hgen⟩ := finrank_eq_one_iff'.1 hW
  have hne : P.pairV y z₀ ≠ 0 := fun h => h0 (Subtype.ext (P.eq_of_pairV fun t => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hy.ge ⟨_, P.one_tmul_mem_latT t, rfl⟩)
    have e := Model.pairV_proj P hs k (1 ⊗ₜ t) hz₀.2
    change _ = proj hs P.actV k (1 ⊗ₜ t) at hc
    rw [← hc, ← algebraMap_smul C, map_smul, LinearMap.smul_apply, h, smul_zero] at e
    change P.pairV z₀ _ = P.pairV 0 _
    rw [P.pairV_swap, ← e, neg_zero, map_zero, LinearMap.zero_apply]))
  have hz := (P.eigW _).smul_mem (P.pairV y z₀)⁻¹ hz₀
  have h1 : P.pairV y ((P.pairV y z₀)⁻¹ • z₀) = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne]
  have hgen' : ∀ x ∈ P.eigW ((σ k).comp (starRingEnd Λ)), ∃ c : C, c • (P.pairV y z₀)⁻¹ • z₀ = x := fun x hx => by
    obtain ⟨c, hc⟩ := hgen ⟨x, hx⟩
    exact ⟨c * P.pairV y z₀, by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hne, mul_one]; exact congrArg Subtype.val hc⟩
  generalize (P.pairV y z₀)⁻¹ • z₀ = z at hz h1 hgen'
  refine ⟨z, hz, h1, le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨?_, hz⟩)⟩
  · rintro x ⟨hx, hx'⟩
    obtain ⟨c, rfl⟩ := hgen' x hx'
    obtain ⟨o, ho⟩ := (Model.mem_latTSub_iff P hs k hx'.2).1 hx y (hy.le (Submodule.mem_span_singleton_self y))
    rw [map_smul, h1, smul_eq_mul, mul_one] at ho
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
  · refine (Model.mem_latTSub_iff P hs k hz.2).2 fun x hx => ?_
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 (hy.ge hx)
    exact ⟨o, by rw [← algebraMap_smul C, map_smul, LinearMap.smul_apply, h1, smul_eq_mul, mul_one]⟩

theorem index_points {A A' B : Point ℓ v O Λ} {p q : ℕ} (φ : Fin p → (A.V →ₗ[C] B.V)) (φ' : Fin q → (A'.V →ₗ[C] B.V))
    {I : Ideal O} (hI : HasIndex C (p + q) (B.latTQuot hs k)
      ((⨆ a, (A.latTQuot hs k).map ((φ a).restrictScalars O)) ⊔
        ⨆ b, (A'.latTQuot hs k).map ((φ' b).restrictScalars O)) I)
    {y : A.V} (hy : Submodule.span O {y} = A.latTQuot hs k) {y' : A'.V} (hy' : Submodule.span O {y'} = A'.latTQuot hs k)
    (hA : Module.finrank C (A.eigW (σ k)) = 1) (hA' : Module.finrank C (A'.eigW ((σ k).comp (starRingEnd Λ))) = 1)
    (hB : Module.finrank C (B.eigW (σ k)) = p) (hB' : Module.finrank C (B.eigW ((σ k).comp (starRingEnd Λ))) = q)
    (hφ : ∀ a, ∀ x ∈ A.eigW (σ k), φ a x ∈ B.eigW (σ k))
    (hφ' : ∀ b, ∀ x ∈ A'.eigW ((σ k).comp (starRingEnd Λ)), φ' b x ∈ B.eigW ((σ k).comp (starRingEnd Λ)))
    (hT : ∀ b, ∀ x ∈ A'.latTSub ((σ k).comp (starRingEnd Λ)), φ' b x ∈ B.latTSub ((σ k).comp (starRingEnd Λ)))
    {g : Matrix (Fin q) (Fin q) Λ} (hg : σ k g.det ≠ 0)
    (hGram : ∀ a b x z, B.pairV (φ' a x) (φ' b z) = A'.pairV (A'.actV (g a b) x) z)
    (horth : ∀ a b x z, B.pairV (φ a x) (φ' b z) = 0) :
    ∃ I₁ I₂ : Ideal O, HasIndex C p (B.wHT hs k) (⨆ a, (A.wHT hs k).map ((φ a).restrictScalars O)) I₁ ∧
      HasIndex C q
        (B.latTSub ((σ k).comp (starRingEnd Λ)) ⊓ (B.eigW ((σ k).comp (starRingEnd Λ))).restrictScalars O)
        (⨆ b, (A'.latTSub ((σ k).comp (starRingEnd Λ)) ⊓
          (A'.eigW ((σ k).comp (starRingEnd Λ))).restrictScalars O).map ((φ' b).restrictScalars O)) I₂ ∧
      I₁ * Ideal.span {σ k g.det} = I * I₂ := by
  obtain ⟨h1, h2⟩ := wHT_eq_of_rank_one hs k A hy hA
  obtain ⟨z, h3, h4, h5⟩ := exists_dual_of_rank_one hs k A' hy' hA'
  have h6 : y' ∈ A'.eigV (σ k) := eigQuotLat_le A'.actV hs k A'.latT (hy'.le (Submodule.mem_span_singleton_self y'))
  rw [← hy, ← hy', iSup_map_span, iSup_map_span] at hI
  rw [h2, h5, iSup_map_span, iSup_map_span, RingHom.map_det]
  refine index_mul_gram B.integers B.pairV hI hB hB' (fun a => hφ a y h1) (fun b => hφ' b z h3)
    (fun b => hT b z (h5.ge (Submodule.mem_span_singleton_self z)).1)
    (fun x hx => Model.mem_latTSub_iff B hs k hx.2) (fun a b => horth a b y z) (by rwa [← RingHom.map_det])
    fun a b => (hGram a b y' z).trans ?_
  rw [mem_eigenSub.1 h6, map_smul, LinearMap.smul_apply, h4, smul_eq_mul, mul_one]
  rfl

end Points

section Object

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap GlobalTheory.GramAt GlobalTheory.PointSig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C]

omit [IsCMField E] in

theorem eigW_of_hasSigFrames [StarRing (𝓞 E)] {P : Point ℓ v O (𝓞 E)} {rt : 𝓞 E} {τ : E →+* C} {p q : ℕ}
    (h : HasSigFrames P rt τ p q) :
    (Module.finrank C (P.eigW (embO P.integers τ)) = p ∧
      P.eigW (embO P.integers τ) = Submodule.span C (P.wRec (embO P.integers τ))) ∧
    Module.finrank C (P.eigW ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) = q ∧
      P.eigW ((embO P.integers τ).comp (starRingEnd (𝓞 E))) =
        Submodule.span C (P.wRec ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) := by
  obtain ⟨-, x, x', g, g', h1, h2, -, -, -, -, -, -, h3, h4, h5, h6⟩ := h
  rw [← h1, ← h2, ← h5, ← h6, finrank_span_eq_card h3, finrank_span_eq_card h4, Submodule.span_span_of_tower,
    Submodule.span_span_of_tower]
  simp

omit [IsCMField E] [NumberField E] in
theorem map_mem_eigW [StarRing (𝓞 E)] {P P' : Point ℓ v O (𝓞 E)} {χ : 𝓞 E →+* O} (f : P.V →ₗ[C] P'.V)
    (h : P.eigW χ = Submodule.span C (P.wRec χ)) (h' : P'.eigW χ = Submodule.span C (P'.wRec χ))
    (hf : ∀ x ∈ P.wRec χ, f x ∈ P'.wRec χ) : ∀ x ∈ P.eigW χ, f x ∈ P'.eigW χ := by
  rw [h, h']
  exact fun x hx => (Submodule.span_le (p := (Submodule.span C (P'.wRec χ : Set P'.V)).comap f)).2
    (fun y hy => Submodule.subset_span (hf y hy)) hx

variable (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q)

open Classical in

def IsIndexRel (τ : E →+* C) (I : Ideal O) (δ : O) : Prop :=
  letI := H.starRing
  ∃ I₁ I₂ : Ideal O,
    HasIndex C p ((pointB hv ε i X).wHT (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ)
      (⨆ a, ((pointA hv ε i X true).wHT (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ).map
        ((phiVP hv ε i X a).restrictScalars O)) I₁ ∧
    HasIndex C q ((pointB hv ε i X).latTSub ((embO hv τ).comp (starRingEnd (𝓞 E))) ⊓
        ((pointB hv ε i X).eigW ((embO hv τ).comp (starRingEnd (𝓞 E)))).restrictScalars O)
      (⨆ b, ((pointA hv ε i X false).latTSub ((embO hv τ).comp (starRingEnd (𝓞 E))) ⊓
        ((pointA hv ε i X false).eigW ((embO hv τ).comp (starRingEnd (𝓞 E)))).restrictScalars O).map
          ((phiVQ hv ε i X b).restrictScalars O)) I₂ ∧
    I₁ * Ideal.span {δ} = I * I₂

variable {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)}

open Classical in

theorem isIndexRel_of_hasSigFrames (h : IsGram X gP gQ) (τ : E →+* C) : letI := H.starRing
    HasSigFrames (pointB hv ε i X) H.rt τ p q → HasSigFrames (pointA hv ε i X true) H.rt τ 1 0 →
    HasSigFrames (pointA hv ε i X false) H.rt τ 0 1 → ∀ I : Ideal O,
    HasIndex C (p + q) ((pointB hv ε i X).latTQuot (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ)
      (quotImage hv ε i X (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ) I →
    IsIndexRel hv ε i X τ I (embO hv τ gQ.det) := by
  letI := H.starRing
  intro hB hP hQ I hI
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := eigW_of_hasSigFrames hB
  obtain ⟨⟨p1, p2⟩, -⟩ := eigW_of_hasSigFrames hP
  obtain ⟨-, q1, q2⟩ := eigW_of_hasSigFrames hQ
  obtain ⟨y, -, hy⟩ := exists_basis_latTQuot_pure hv ε i X (σ := fun φ : E →+* C => embO hv φ)
    (isSplitting_embO hv) τ true
  obtain ⟨y', -, hy'⟩ := exists_basis_latTQuot_pure hv ε i X (σ := fun φ : E →+* C => embO hv φ)
    (isSplitting_embO hv) τ false
  rw [Set.range_unique] at hy hy'
  refine index_points (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ (A := pointA hv ε i X true)
    (A' := pointA hv ε i X false) (B := pointB hv ε i X) (phiVP hv ε i X) (phiVQ hv ε i X) hI hy hy' p1 q1 b1 b3
    (fun a => map_mem_eigW _ p2 b2 (patV_mem_wRec (T := X.A true) hv ε i (X.lin (.inl a)) _))
    (fun a => map_mem_eigW _ q2 b4 (patV_mem_wRec (T := X.A false) hv ε i (X.lin (.inr a)) _))
    (fun a => patV_mem_latTSub (T := X.A false) hv ε i (X.lin (.inr a)) _) (fun h0 => (gram_det X h).2.1 ?_)
    (gram_V hv ε i X h).2.1 (gram_V hv ε i X h).2.2
  have h1 := algebraMap_embO hv τ gQ.det
  rw [show embO hv τ gQ.det = 0 from h0, map_zero, eq_comm, map_eq_zero] at h1
  exact RingOfIntegers.coe_injective h1

variable {hv ε i X} in
open Classical in

theorem IsIndexRel.val_det {τ : E →+* C} {n δ : O} (h : IsIndexRel hv ε i X τ (Ideal.span {n}) δ) : letI := H.starRing
    ∀ (x : Fin p → LieG (pointB hv ε i X).Gt) (x' : Fin q → LieG (pointB hv ε i X).Gt)
      (y : Fin 1 → LieG (pointA hv ε i X true).Gt) (y' : Fin 1 → LieG (pointA hv ε i X false).Gt)
      (g m : Matrix (Fin p) (Fin p) C) (g' m' : Matrix (Fin q) (Fin q) C) (c c' : Matrix (Fin 1) (Fin 1) C),
      g.det ≠ 0 → g'.det ≠ 0 → c.det ≠ 0 → c'.det ≠ 0 →
      Submodule.span C (Set.range fun j => (pointB hv ε i X).bLie (x j)) = (pointB hv ε i X).eigW (embO hv τ) →
      Submodule.span C (Set.range fun j => (pointB hv ε i X).bLie (x' j)) =
        (pointB hv ε i X).eigW ((embO hv τ).comp (starRingEnd (𝓞 E))) →
      Submodule.span C (Set.range fun j => (pointA hv ε i X true).bLie (y j)) =
        (pointA hv ε i X true).eigW (embO hv τ) →
      Submodule.span C (Set.range fun j => (pointA hv ε i X false).bLie (y' j)) =
        (pointA hv ε i X false).eigW ((embO hv τ).comp (starRingEnd (𝓞 E))) →
      IsLatBasis C ((pointB hv ε i X).latTQuot (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ)
        (fun k => ∑ j, g k j • (pointB hv ε i X).bLie (x j)) →
      IsLatBasis C ((pointB hv ε i X).latTSub ((embO hv τ).comp (starRingEnd (𝓞 E))))
        (fun k => ∑ j, g' k j • (pointB hv ε i X).bLie (x' j)) →
      IsLatBasis C ((pointA hv ε i X true).latTQuot (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ)
        (fun k => ∑ j, c k j • (pointA hv ε i X true).bLie (y j)) →
      IsLatBasis C ((pointA hv ε i X false).latTSub ((embO hv τ).comp (starRingEnd (𝓞 E))))
        (fun k => ∑ j, c' k j • (pointA hv ε i X false).bLie (y' j)) →
      (∀ a, phiVP hv ε i X a ((pointA hv ε i X true).bLie (y 0)) = ∑ k, m a k • (pointB hv ε i X).bLie (x k)) →
      (∀ a, phiVQ hv ε i X a ((pointA hv ε i X false).bLie (y' 0)) = ∑ k, m' a k • (pointB hv ε i X).bLie (x' k)) →
      v c.det ^ p * v m.det * v g'.det * v (algebraMap O C δ) =
        v (algebraMap O C n) * (v c'.det ^ q * v m'.det) * v g.det := by
  letI := H.starRing
  intro x x' y y' g m g' m' c c' a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  obtain ⟨I₁, I₂, h₁, h₂, e⟩ := h
  obtain ⟨-, g₁, -, -, -, -, rfl⟩ := id h₁
  obtain ⟨-, g₂, -, -, -, -, rfl⟩ := id h₂
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_span_singleton] at e
  obtain ⟨u, hu⟩ := e
  have e := congrArg (fun z => v (algebraMap O C z)) hu
  simp only [map_mul, hv.one_of_isUnit u.isUnit, mul_one] at e
  rw [val_det_frame hv h₁ a1 b1 c1 a3 b3 c3 d1, val_det_frame hv h₂ a2 b2 c2 a4 b4 c4 d2]
  calc _ = v g.det * v g'.det * (v (algebraMap O C g₁.det) * v (algebraMap O C δ)) := by ring
    _ = _ := by rw [e]; ring

end At

end Object

end GlobalTheory.HTIndex
