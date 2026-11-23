import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicKernelFixedBasisWittTensorLatticStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtalePhiMatrixDecompletionToWachStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.EtaleBasis

section Generic

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}

theorem repr_of_fixed (e : Module.Basis (Fin r) R M) (τ : R →+* R) (A : M →+ M)
    (hA : ∀ c x, A (c • x) = τ c • A x) (he : ∀ i, A (e i) = e i) (x : M) (i : Fin r) :
    e.repr (A x) i = τ (e.repr x i) := by
  have h : A x = ∑ k, τ (e.repr x k) • e k := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, hA, he]
  rw [h, e.repr_sum_self]

theorem isUnit_matrix (e : Module.Basis (Fin r) R M) (σ : R →+* R) (Φ : M →+ M)
    (hΦ : ∀ c x, Φ (c • x) = σ c • Φ x) (hs : Submodule.span R (Set.range Φ) = ⊤) :
    IsUnit (Matrix.of fun i j => e.repr (Φ (e j)) i : Matrix (Fin r) (Fin r) R) := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  have hle : Submodule.span R (Set.range Φ) ≤ Submodule.span R (Set.range fun j => Φ (e j)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [hΦ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  intro y
  have hy : e.equivFun.symm y ∈ Submodule.span R (Set.range fun j => Φ (e j)) :=
    hle (hs ▸ Submodule.mem_top)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  refine ⟨c, funext fun i => ?_⟩
  have h1 : e.equivFun (e.equivFun.symm y) i = y i := by rw [LinearEquiv.apply_symm_apply]
  rw [← h1, ← hc]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem change_basis (e : Module.Basis (Fin r) R M) (σ : R →+* R) (Φ : M →+ M)
    (hΦ : ∀ c x, Φ (c • x) = σ c • Φ x) (V F₁ : Matrix (Fin r) (Fin r) R) (hV : IsUnit V)
    (h : (Matrix.of fun i j => e.repr (Φ (e j)) i : Matrix (Fin r) (Fin r) R) * V.map σ = V * F₁) :
    ∃ e' : Module.Basis (Fin r) R M, (∀ j, e' j = ∑ i, V i j • e i) ∧
      ∀ i j, e'.repr (Φ (e' j)) i = F₁ i j := by
  obtain ⟨u, rfl⟩ := hV
  let L : M ≃ₗ[R] M := Matrix.toLinOfInv e e u.mul_inv u.inv_mul
  have hL : ∀ j, (e.map L) j = ∑ i, (u : Matrix (Fin r) (Fin r) R) i j • e i := by
    intro j
    simp [L, Matrix.toLinOfInv, Matrix.toLin_self]
  refine ⟨e.map L, hL, fun i j => ?_⟩
  have key : Φ ((e.map L) j) = ∑ k, F₁ k j • (e.map L) k := by
    apply e.repr.injective
    ext m
    have hm := congrFun (congrFun h m) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply] at hm
    simp only [hL, map_sum, hΦ, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simpa only [mul_comm] using hm
  rw [key, Module.Basis.repr_sum_self]

end Generic

section Tensor

variable {O R N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup N] [Module O N]

theorem map_smul_semi (f : R →ₐ[O] R) (a : N →ₗ[O] N) (c : R) (x : R ⊗[O] N) :
    TensorProduct.map f.toLinearMap a (c • x) = f c • TensorProduct.map f.toLinearMap a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul b t => simp [TensorProduct.smul_tmul']

theorem span_range_map (f : R →ₐ[O] R) :
    Submodule.span R (Set.range (TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N))) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul b t =>
    have : b ⊗ₜ[O] t = b • TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) ((1 : R) ⊗ₜ[O] t) := by
      simp [TensorProduct.smul_tmul']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem map_comm (f g : R →ₐ[O] R) (h : ∀ c, f (g c) = g (f c)) (a : N →ₗ[O] N) (x : R ⊗[O] N) :
    TensorProduct.map g.toLinearMap a (TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) x) =
      TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) (TensorProduct.map g.toLinearMap a x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b t => simp [h]

theorem descend {r : ℕ} {ι : Type} (φ : R →ₐ[O] R) (g : ι → (R →ₐ[O] R)) (a : ι → (N →ₗ[O] N))
    (hc : ∀ s c, φ (g s c) = g s (φ c)) (S : Set R)
    (dec : ∀ F : Matrix (Fin r) (Fin r) R, IsUnit F → (∀ i j s, g s (F i j) = F i j) →
      ∃ V F₁ : Matrix (Fin r) (Fin r) R, IsUnit V ∧ (∀ i j s, g s (V i j) = V i j) ∧
        (∀ i j, F₁ i j ∈ S) ∧ F * V.map φ = V * F₁)
    (e : Module.Basis (Fin r) R (R ⊗[O] N))
    (he : ∀ s i, TensorProduct.map (g s).toLinearMap (a s) (e i) = e i) :
    ∃ e' : Module.Basis (Fin r) R (R ⊗[O] N),
      (∀ s i, TensorProduct.map (g s).toLinearMap (a s) (e' i) = e' i) ∧
      ∀ i j, e'.repr (TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[O] N) (e' j)) i ∈ S := by
  let Φ : R ⊗[O] N →+ R ⊗[O] N :=
    (TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[O] N)).toAddMonoidHom
  have hΦ : ∀ (c : R) x, Φ (c • x) = (φ : R →+* R) c • Φ x := map_smul_semi φ _
  obtain ⟨V, F₁, hV, hVg, hS, hE⟩ := dec _ (isUnit_matrix e φ Φ hΦ (span_range_map φ)) (by
    intro i j s
    have h1 := repr_of_fixed e (g s : R →+* R)
      (TensorProduct.map (g s).toLinearMap (a s)).toAddMonoidHom (map_smul_semi (g s) _) (he s) (Φ (e j)) i
    have h2 : (TensorProduct.map (g s).toLinearMap (a s)).toAddMonoidHom (Φ (e j)) = Φ (e j) := by
      have := map_comm φ (g s) (hc s) (a s) (e j)
      rw [he] at this
      exact this
    rw [h2] at h1
    exact h1.symm)
  obtain ⟨e', h1, h2⟩ := change_basis e φ Φ hΦ V F₁ hV hE
  refine ⟨e', fun s j => ?_, fun i j => ?_⟩
  · rw [h1, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul_semi, hVg, he]
  · have := hS i j
    rw [← h2] at this
    exact this

end Tensor

theorem descend_lat {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (T : LocLat G Qp LL O) {r : ℕ} (φ : R →ₐ[O] R) (g : G → (R →ₐ[O] R)) (H : G → Prop)
    (hc : ∀ s c, φ (g s c) = g s (φ c)) (S : Set R)
    (dec : ∀ F : Matrix (Fin r) (Fin r) R, IsUnit F → (∀ i j s, H s → g s (F i j) = F i j) →
      ∃ V F₁ : Matrix (Fin r) (Fin r) R, IsUnit V ∧ (∀ i j s, H s → g s (V i j) = V i j) ∧
        (∀ i j, F₁ i j ∈ S) ∧ F * V.map φ = V * F₁)
    (e : Module.Basis (Fin r) R (TW R T)) (he : ∀ s, H s → ∀ i, TWact (g s) T s (e i) = e i) :
    ∃ e' : Module.Basis (Fin r) R (TW R T), (∀ s, H s → ∀ i, TWact (g s) T s (e' i) = e' i) ∧
      ∀ i j, e'.repr (TWmap φ T (e' j)) i ∈ S := by
  obtain ⟨e', h1, h2⟩ := descend (ι := {s : G // H s}) φ (fun s => g s.1) (fun s => T.actT s.1)
    (fun s c => hc s.1 c) S
    (fun F hU hfix => by
      obtain ⟨V, F₁, hV, hVf, hS, hE⟩ := dec F hU (fun i j s hs => hfix i j ⟨s, hs⟩)
      exact ⟨V, F₁, hV, fun i j s => hVf i j s.1 s.2, hS, hE⟩)
    e (fun s i => he s.1 s.2 i)
  exact ⟨e', fun s hs i => h1 ⟨s, hs⟩ i, h2⟩

theorem map_id_comm {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f g : W →ₐ[Z] W) (h : ∀ w, f (g w) = g (f w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f (Algebra.TensorProduct.map (AlgHom.id O O) g x) =
    Algebra.TensorProduct.map (AlgHom.id O O) g (Algebra.TensorProduct.map (AlgHom.id O O) f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w => simp [h]

theorem frob_comm_gal {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l)
    (x : RW LL) : φRW LL (AI.gRW LL g x) = AI.gRW LL g (φRW LL x) := by
  refine map_id_comm _ _ (fun w => ?_) x
  ext n
  change (WittVector.map (frobenius (Cb l) l)
      (WittVector.map (autCb l (AI.actT g)).toRingHom w)).coeff n =
    (WittVector.map (autCb l (AI.actT g)).toRingHom (WittVector.map (frobenius (Cb l) l) w)).coeff n
  simp [WittVector.map_coeff, frobenius_def]

theorem fixH_iff {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) {LL : FinExt l}
    (x : RW LL) : FixH AI K x ↔ ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) x = x := by
  unfold FixH
  constructor
  · intro h g hχ
    exact h g.1 g.2 hχ
  · intro h g hg hχ
    have h1 := h ⟨g, hg⟩
    dsimp only at h1
    exact h1 hχ

theorem decomplete {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (hG : Good K s LL) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (hI : IoW I) (r : ℕ)
    (F : Matrix (Fin r) (Fin r) (RW LL)) (hU : IsUnit F)
    (hfix : ∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (F i j) = F i j) :
    ∃ V F₁ : Matrix (Fin r) (Fin r) (RW LL),
      IsUnit V ∧ (∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (V i j) = V i j) ∧
      (∀ i j, F₁ i j ∈ Set.range I.ioE) ∧ F * V.map (φRW LL) = V * F₁ := by
  have h0 : ∀ i j, FixH AI K (F i j) := fun i j => (fixH_iff AI K _).mpr (hfix i j)
  have h1 := GlobalTheory.T.etalePhiMatrix_decompletion_to_wach l P AI K s LL hG Γ R I hI r F hU h0
  obtain ⟨V, F', hV, hVf, hE⟩ := h1
  refine ⟨V, F'.map I.ioE, hV, fun i j => (fixH_iff AI K _).mp (hVf i j), ?_, hE⟩
  intro i j
  rw [Matrix.map_apply]
  exact Set.mem_range_self _

theorem exists_etBasis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ e : Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (RW LL) (TW (RW LL) T), EtBasis I T e := by
  intro l _ P AI hF K s LL hG Γ R I hI T
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_cyclotomicKernelFixedBasis_wittTensorLattice l P AI hF K LL T
  unfold EtBasis FixBasis
  unfold FixBasis at he
  exact descend_lat T (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l)) (fun g => P.χQ (g : GQ l) = 1)
    (fun g c => frob_comm_gal AI LL (g : GQ l) c) (Set.range I.ioE)
    (decomplete AI K s LL hG Γ R I hI _) e he

end GlobalTheory.EtaleBasis
