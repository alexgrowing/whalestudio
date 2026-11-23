import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Th

private theorem tp_tr {R G : Type} [CommRing R] [Group G] {n : ℕ} (hn : 1 ≤ n) (ρ : G →* Matrix (Fin n) (Fin n) R)
    (z : MonoidAlgebra R G) : (GDet.ofRep ρ).tr z = (GDet.repAlg ρ R z).trace := by
  have h : (GDet.ofRep ρ).chi z = (GDet.repAlg ρ R z).charpoly := by
    change (GDet.repAlg ρ (Polynomial R) _).det = Matrix.det _
    congr 1
    rw [map_sub, Matrix.charmatrix]
    congr 1
    · ext i j : 2
      simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply]
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single g r => ext i j : 2; simp [GDet.repAlg]
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [GDet.tr, GDet.lam, h, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
  simp

private theorem tp_single {R G : Type} [CommRing R] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) R) (g : G) (a : R) :
    GDet.repAlg ρ R (MonoidAlgebra.single g a) = a • ρ g := by
  ext i j; simp [GDet.repAlg]

private theorem tp_lin {R A G : Type} [CommRing R] [CommRing A] [Group G] {n : ℕ} (hn : 1 ≤ n) (D : GDet n R G) (f : R →+* A)
    (M : G →* Matrix (Fin n) (Fin n) A) (hM : ∀ g, f (D.tr (MonoidAlgebra.single g 1)) = (M g).trace)
    (z : MonoidAlgebra R G) : f (D.tr z) = (GDet.repAlg M A (MonoidAlgebra.mapRingHom G f z)).trace := by
  obtain ⟨t, ht⟩ := (UpperTheory.V.CA.d_tr D.toDet).1 hn
  have ht' : ∀ x, D.tr x = t x := fun x => by rw [ht, (UpperTheory.V.CA.d_toDet D x).2.2.1]
  simp only [ht'] at hM ⊢
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, Matrix.trace_add]
  | single g r =>
    have e : MonoidAlgebra.single g r = r • MonoidAlgebra.single g (1 : R) := by simp
    rw [MonoidAlgebra.mapRingHom_single, tp_single, Matrix.trace_smul, ← hM, e, map_smul, smul_eq_mul, map_mul, smul_eq_mul]

private theorem tp_mul {A : Type} [CommRing A] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) A) (hP : P.BlockTriangular id)
    (hQ : Q.BlockTriangular id) (i : Fin n) : (P * Q) i i = P i i * Q i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hP h, zero_mul]
    · rw [hQ h, mul_zero]
  · simp

private theorem tp_list {A : Type} [CommRing A] {n : ℕ} (Q : List (Matrix (Fin n) (Fin n) A))
    (hQ : ∀ q ∈ Q, q.BlockTriangular id) : Q.prod.BlockTriangular id ∧ ∀ i, Q.prod i i = (Q.map fun q => q i i).prod := by
  induction Q with
  | nil => exact ⟨Matrix.blockTriangular_one, fun i => by simp⟩
  | cons q Q ih =>
    obtain ⟨h1, h2⟩ := ih fun a ha => hQ a (List.mem_cons_of_mem _ ha)
    have hq := hQ q List.mem_cons_self
    exact ⟨by rw [List.prod_cons]; exact hq.mul h1, fun i => by rw [List.prod_cons, tp_mul _ _ hq h1, h2]; simp⟩

private theorem tp_trace {A : Type} [CommRing A] {n : ℕ} (P : Matrix (Fin n) (Fin n) A) (Q : Fin n → Matrix (Fin n) (Fin n) A)
    (a : Fin n → A) (hP : P.BlockTriangular id) (hQ : ∀ j, (Q j).BlockTriangular id) :
    (P * (List.ofFn fun j => Q j - a j • (1 : Matrix (Fin n) (Fin n) A)).prod).trace =
      ∑ k, P k k * ∏ j, (Q j k k - a j) := by
  obtain ⟨h1, h2⟩ := tp_list (List.ofFn fun j => Q j - a j • (1 : Matrix (Fin n) (Fin n) A)) (by
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hq
    refine (hQ j).sub fun s t hst => ?_
    rw [Matrix.smul_apply, Matrix.blockTriangular_one hst, smul_zero])
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, tp_mul _ _ hP h1, h2, List.map_ofFn, List.prod_ofFn]
  simp

private theorem tp_vand {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {n : ℕ} (t : Fin n → O) (u : Fin n → X)
    (h : ∀ a : ℕ, ∑ k, t k ^ a • u k = 0) (i : Fin n) : (∏ j ∈ Finset.univ.erase i, (t i - t j)) • u i = 0 := by
  have key : ∀ P : Polynomial O, ∑ k, P.eval (t k) • u k = 0 := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.eval_add, add_smul, Finset.sum_add_distrib, hp, hq, add_zero]
    | monomial a c => simp only [Polynomial.eval_monomial, mul_smul, ← Finset.smul_sum, h, smul_zero]
  have := key (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (t j)))
  rw [Finset.sum_eq_single i] at this
  · simpa [Polynomial.eval_prod] using this
  · intro k _ hk
    rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩) (by simp), zero_smul]
  · simp

private theorem tp_core {O R X G H : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module O X] [Group G]
    [Group H] {n : ℕ} (hn : 1 ≤ n) (D : GDet n R G) (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (hδ : IsDer x δ)
    (M : G →* Matrix (Fin n) (Fin n) O) (hM : ∀ g, x (D.tr (MonoidAlgebra.single g 1)) = (M g).trace)
    (h0 : ∀ g, δ (D.tr (MonoidAlgebra.single g 1)) = 0) (φ : H →* G) (hφ : ∀ g, (M (φ g)).BlockTriangular id)
    (g : Fin n → H) (s : H) (a : Fin n → R) (ha : ∀ j, M (φ (g j)) j j = x (a j))
    (hO : D.tr (MonoidAlgebra.single (φ s) 1 * (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) -
      MonoidAlgebra.single 1 (a i)).prod) = 0) :
    ∑ k, M (φ s) k k • (∏ j ∈ Finset.univ.erase k, (M (φ (g j)) k k - x (a j))) • δ (a k) = 0 := by
  letI : Module Oᵐᵒᵖ X := Module.compHom X ((RingHom.id O).fromOpposite mul_comm)
  haveI : IsCentralScalar O X := ⟨fun _ _ => rfl⟩
  have h1 : δ 1 = 0 := by
    have := hδ 1 1
    simpa using this
  let f : R →+* TrivSqZeroExt O X :=
    { toFun := fun r => TrivSqZeroExt.inl (x r) + TrivSqZeroExt.inr (δ r)
      map_one' := by ext <;> simp [h1]
      map_mul' := fun a b => by ext <;> simp [hδ a b]
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp }
  have hf : ∀ r, f r = TrivSqZeroExt.inl (x r) + TrivSqZeroExt.inr (δ r) := fun _ => rfl
  let ι : O →+* TrivSqZeroExt O X := TrivSqZeroExt.inlHom O X
  let M' : G →* Matrix (Fin n) (Fin n) (TrivSqZeroExt O X) := ι.mapMatrix.toMonoidHom.comp M
  have hM' : ∀ g i j, M' g i j = TrivSqZeroExt.inl (M g i j) := fun _ _ _ => rfl
  have hT : ∀ g, (M' (φ g)).BlockTriangular id := fun g i j hij => by rw [hM', hφ g hij, TrivSqZeroExt.inl_zero]
  have key := tp_lin hn D f M' (fun g => by
    rw [hf, h0, hM, TrivSqZeroExt.inr_zero, add_zero]
    exact map_sum ι _ _) (MonoidAlgebra.single (φ s) 1 * (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) -
      MonoidAlgebra.single 1 (a i)).prod)
  rw [hO, map_zero, map_mul, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn] at key
  have e : (⇑(GDet.repAlg M' (TrivSqZeroExt O X)) ∘ ⇑(MonoidAlgebra.mapRingHom G f) ∘ fun i =>
      MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (a i)) =
      fun j => M' (φ (g j)) - f (a j) • (1 : Matrix (Fin n) (Fin n) (TrivSqZeroExt O X)) := by
    funext j
    simp [tp_single]
  rw [e, MonoidAlgebra.mapRingHom_single, tp_single, map_one, one_smul, tp_trace _ _ _ (hT s) fun j => hT _] at key
  have k2 := congrArg TrivSqZeroExt.snd key
  rw [TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_sum] at k2
  rw [← neg_eq_zero, ← Finset.sum_neg_distrib, k2]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e2 : M' (φ (g k)) k k - f (a k) = TrivSqZeroExt.inr (-δ (a k)) := by
    rw [hM', hf, ha]; ext <;> simp
  have e3 : (∏ j ∈ Finset.univ.erase k, (M' (φ (g j)) k k - f (a j))).fst =
      ∏ j ∈ Finset.univ.erase k, (M (φ (g j)) k k - x (a j)) := by
    refine (map_prod (TrivSqZeroExt.fstHom O O X) _ _).trans (Finset.prod_congr rfl fun j _ => ?_)
    simp [hM', hf]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), e2, hM']
  simp [e3]

theorem UpperTheory.V.Th.trPsi : TrPsi := by
  intro l _ L G0 n O _ _ _ _ y hn
  choose s hs using y.reg
  let d : L.Vl → Fin n → O := fun v i => ∏ j ∈ Finset.univ.erase i, ((y.ψ v i (s v) : O) - (y.ψ v j (s v) : O))
  have hd : ∀ v i, d v i ≠ 0 := fun v i => Finset.prod_ne_zero_iff.2 fun j hj =>
    sub_ne_zero.2 fun e => (Finset.mem_erase.1 hj).1 (hs v (Units.ext e)).symm
  refine ⟨∏ v, ∏ i, d v i * d v i, Finset.prod_ne_zero_iff.2 fun v _ => Finset.prod_ne_zero_iff.2 fun i _ =>
    mul_ne_zero (hd v i) (hd v i), ?_⟩
  intro G h rN R _ _ _ p x hp X _ _ δ hδ h0 v i g
  suffices hh : d v i • d v i • δ (p.ψ v i g : Rˣ) = 0 by
    obtain ⟨e, he⟩ : d v i * d v i ∣ ∏ v, ∏ i, d v i * d v i :=
      (Finset.dvd_prod_of_mem (fun i => d v i * d v i) (Finset.mem_univ i)).trans
        (Finset.dvd_prod_of_mem (fun v => ∏ i, d v i * d v i) (Finset.mem_univ v))
    rw [he, mul_comm, mul_smul, mul_smul, hh, smul_zero]
  let M : G.G₀ →* Matrix (Fin n) (Fin n) O :=
    mat ((MulAut.conj (y.w v)⁻¹).toMonoidHom.comp (y.ρ.comp h.p₀))
  have hM : ∀ g, M g = (((y.w v)⁻¹ * y.ρ (h.p₀ g) * y.w v : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := fun g => by
    simp [M, mat]
  have hφ : ∀ g, h.p₀ (G.φ v g) = G0.φ v g := fun g => Subtype.ext (h.φ v g)
  have hx : ∀ j g, x (p.ψ v j g : Rˣ) = (y.ψ v j g : O) := fun j g => by
    rw [← hp.2 v j]; rfl
  have hdiag : ∀ g k, M (G.φ v g) k k = (y.ψ v k g : O) := fun g k => by
    rw [hM, hφ]; exact (y.tri v g).2 k
  have htr : ∀ g, x (p.D.tr (MonoidAlgebra.single g 1)) = (M g).trace := fun g => by
    have e := ((UpperTheory.V.CA.d_gmap p.D).2.2.1 x.toRingHom (MonoidAlgebra.single g 1)).2 1
    rw [hp.1, MonoidAlgebra.mapRingHom_single, map_one] at e
    have e' : x (p.D.tr (MonoidAlgebra.single g 1)) = (GDet.ofRep (mat (y.ρ.comp h.p₀))).tr (MonoidAlgebra.single g 1) :=
      e.symm
    rw [e', tp_tr hn, tp_single, one_smul, hM, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, Units.mul_inv, one_mul]
    rfl
  let γ : Fin n → L.Gv v := Function.update (fun _ => s v) i g
  have key := tp_vand (fun k => (y.ψ v k (s v) : O))
    (fun k => (∏ j ∈ Finset.univ.erase k, (M (G.φ v (γ j)) k k - x (p.ψ v j (γ j) : Rˣ))) • δ (p.ψ v k (γ k) : Rˣ))
    (fun a => by
      have := tp_core hn p.D x δ hδ M htr h0 (G.φ v) (fun g i j hij => by rw [hM, hφ]; exact (y.tri v g).1 i j hij)
        γ (s v ^ a) (fun j => (p.ψ v j (γ j) : Rˣ)) (fun j => by rw [hdiag, hx]) (p.Ord v γ _)
      simpa only [hdiag, map_pow (y.ψ v _), Units.val_pow_eq_pow_val] using this) i
  have e : ∏ j ∈ Finset.univ.erase i, (M (G.φ v (γ j)) i i - x (p.ψ v j (γ j) : Rˣ)) = d v i :=
    Finset.prod_congr rfl fun j hj => by
      rw [hdiag, hx, show γ j = s v from Function.update_of_ne (Finset.mem_erase.1 hj).1 _ _]
  have e2 : γ i = g := Function.update_self _ _ _
  simp only [e, e2] at key
  exact key
