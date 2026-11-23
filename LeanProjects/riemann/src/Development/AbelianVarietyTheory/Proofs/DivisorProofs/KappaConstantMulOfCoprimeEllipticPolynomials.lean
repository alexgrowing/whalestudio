import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.BCT.KapMul

section Generic
open Topology

theorem card_dc_prod {A B T : Type} [Group A] [Group B] [Group T] (e : A × B ≃* T) (H₁ K₁ : Subgroup A)
    (H₂ K₂ : Subgroup B) (H K : Subgroup T) (hH : ∀ x y, e (x, y) ∈ H ↔ x ∈ H₁ ∧ y ∈ H₂)
    (hK : ∀ x y, e (x, y) ∈ K ↔ x ∈ K₁ ∧ y ∈ K₂) :
    Nat.card (DoubleCoset.Quotient (H : Set T) (K : Set T)) =
      Nat.card (DoubleCoset.Quotient (H₁ : Set A) (K₁ : Set A)) *
        Nat.card (DoubleCoset.Quotient (H₂ : Set B) (K₂ : Set B)) := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr ((Setoid.prodQuotientEquiv (DoubleCoset.setoid (H₁ : Set A) K₁)
    (DoubleCoset.setoid (H₂ : Set B) K₂)).trans (Quotient.congr e.toEquiv ?_))).symm
  rintro ⟨x, y⟩ ⟨x', y'⟩
  change (DoubleCoset.setoid (H₁ : Set A) K₁ x x' ∧ DoubleCoset.setoid (H₂ : Set B) K₂ y y') ↔
    DoubleCoset.setoid (H : Set T) K (e (x, y)) (e (x', y'))
  simp only [DoubleCoset.rel_iff]
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, ⟨c, hc, d, hd, rfl⟩⟩
    exact ⟨e (a, c), (hH _ _).2 ⟨ha, hc⟩, e (b, d), (hK _ _).2 ⟨hb, hd⟩, by rw [← map_mul, ← map_mul]; rfl⟩
  · rintro ⟨s, hs, t, ht, h⟩
    obtain ⟨⟨a, c⟩, rfl⟩ := e.surjective s
    obtain ⟨⟨b, d⟩, rfl⟩ := e.surjective t
    rw [← map_mul, ← map_mul] at h
    have h' := e.injective h
    exact ⟨⟨a, ((hH _ _).1 hs).1, b, ((hK _ _).1 ht).1, congrArg Prod.fst h'⟩,
      ⟨c, ((hH _ _).1 hs).2, d, ((hK _ _).1 ht).2, congrArg Prod.snd h'⟩⟩

variable {G₁ G₂ G : Type} [Group G₁] [Group G₂] [Group G] [TopologicalSpace G₁] [TopologicalSpace G₂]
  [TopologicalSpace G]

theorem isCompact_zpowers_map [T2Space G] (f : G₁ →* G) (hf : Continuous f) {x : G₁}
    (h : IsCompact (closure (Subgroup.zpowers x : Set G₁))) : IsCompact (closure (Subgroup.zpowers (f x) : Set G)) := by
  refine (h.image hf).of_isClosed_subset isClosed_closure (closure_minimal ?_ (h.image hf).isClosed)
  rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
  exact Set.image_mono subset_closure

theorem isCompact_zpowers_prod [T2Space G₁] [T2Space G₂] (x : G₁) (y : G₂) :
    IsCompact (closure (Subgroup.zpowers (x, y) : Set (G₁ × G₂))) ↔
      IsCompact (closure (Subgroup.zpowers x : Set G₁)) ∧ IsCompact (closure (Subgroup.zpowers y : Set G₂)) := by
  refine ⟨fun h => ⟨isCompact_zpowers_map (MonoidHom.fst G₁ G₂) continuous_fst (x := (x, y)) h,
    isCompact_zpowers_map (MonoidHom.snd G₁ G₂) continuous_snd (x := (x, y)) h⟩, fun h => ?_⟩
  refine (h.1.prod h.2).of_isClosed_subset isClosed_closure (closure_minimal ?_ (isClosed_closure.prod isClosed_closure))
  rintro _ ⟨k, rfl⟩
  exact ⟨subset_closure ⟨k, rfl⟩, subset_closure ⟨k, rfl⟩⟩

theorem cptPart_map_closed (ι : G₁ →* G) (hι : IsClosedEmbedding ι) (T : Subgroup G₁) :
    cptPart (T.map ι) = (cptPart T).map ι := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hk : ∀ t, IsCompact (closure (Subgroup.zpowers (ι t) : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers t : Set G₁)) := by
    intro t
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map, hι.closure_image_eq, ← hι.isInducing.isCompact_iff]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩

theorem cptPart_prod [T2Space G₁] [T2Space G₂] (T₁ : Subgroup G₁) (T₂ : Subgroup G₂) :
    cptPart (T₁.prod T₂) = (cptPart T₁).prod (cptPart T₂) := by
  unfold cptPart
  rw [← Subgroup.closure_prod]
  · congr 1
    ext ⟨x, y⟩
    simp only [Set.mem_setOf_eq, Set.mem_prod, isCompact_zpowers_prod, Subgroup.mem_prod]
    tauto
  · exact ⟨T₁.one_mem, by simp⟩
  · exact ⟨T₂.one_mem, by simp⟩

omit [TopologicalSpace G₁] [TopologicalSpace G₂] [TopologicalSpace G] in
theorem mem_map_prod (ι : G₁ × G₂ →* G) (hι : Function.Injective ι) (H₁ : Subgroup G₁) (H₂ : Subgroup G₂)
    (x : G₁) (y : G₂) : ι (x, y) ∈ (H₁.prod H₂).map ι ↔ x ∈ H₁ ∧ y ∈ H₂ := by
  rw [Subgroup.mem_map_iff_mem hι, Subgroup.mem_prod]

theorem mass_prod [T2Space G₁] [T2Space G₂] (ι : G₁ × G₂ →* G) (hι : IsClosedEmbedding ι) (θ₁ : G₁ →* G₁)
    (θ₂ : G₂ →* G₂) (θ : G →* G) (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) (Γ : Subgroup G) (δ₁ : G₁) (δ₂ : G₂) (δ : G)
    (hT : twCent θ δ = ((twCent θ₁ δ₁).prod (twCent θ₂ δ₂)).map ι)
    (hΓ : ∀ x y, ι (x, y) ∈ Γ ↔ x ∈ Γ₁ ∧ y ∈ Γ₂) : mass θ Γ δ = mass θ₁ Γ₁ δ₁ * mass θ₂ Γ₂ δ₂ := by
  unfold mass
  rw [hT]
  generalize twCent θ₁ δ₁ = T₁
  generalize twCent θ₂ δ₂ = T₂
  rw [cptPart_map_closed ι hι, cptPart_prod]
  generalize cptPart T₁ = C₁
  generalize cptPart T₂ = C₂
  let e : T₁ × T₂ ≃* (T₁.prod T₂).map ι :=
    (T₁.prodEquiv T₂).symm.trans ((T₁.prod T₂).equivMapOfInjective ι hι.injective)
  have he : ∀ (x : T₁) (y : T₂), ((e (x, y) : (T₁.prod T₂).map ι) : G) = ι (x.1, y.1) := fun _ _ => rfl
  have h2 : Γ ⊓ (C₁.prod C₂).map ι = ((Γ₁ ⊓ C₁).prod (Γ₂ ⊓ C₂)).map ι := by
    ext z
    constructor
    · rintro ⟨hz, ⟨x, y⟩, hxy, rfl⟩
      exact ⟨(x, y), ⟨⟨((hΓ x y).1 hz).1, hxy.1⟩, ⟨((hΓ x y).1 hz).2, hxy.2⟩⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      exact ⟨(hΓ x y).2 ⟨hxy.1.1, hxy.2.1⟩, (x, y), ⟨hxy.1.2, hxy.2.2⟩, rfl⟩
  rw [card_dc_prod e (Γ₁.subgroupOf T₁) (C₁.subgroupOf T₁) (Γ₂.subgroupOf T₂) (C₂.subgroupOf T₂) _ _
    (fun x y => by simp only [Subgroup.mem_subgroupOf, he, hΓ])
    (fun x y => by simp only [Subgroup.mem_subgroupOf, he, mem_map_prod ι hι.injective]), h2,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ ι hι.injective).toEquiv,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  push_cast
  rw [mul_div_mul_comm]

end Generic

section Torus

variable {R : Type} [CommRing R] {n a b : ℕ}

def NormOne (c : R →+* R) (N : GL (Fin n) R) (g : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ f : R[X], g = aeval N.val f ∧ g * aeval (N⁻¹).val (f.map c) = 1

theorem adj_aeval [StarRing R] (δ : GL (Fin n) R) (f : R[X]) :
    GlobalTheory.Tw.adj δ.val (aeval (GlobalTheory.Tw.nrm δ.val) f) = aeval (GlobalTheory.Tw.nrm δ.val)⁻¹ (f.map (starRingEnd R)) := by
  have hadd : ∀ x y : Matrix (Fin n) (Fin n) R, GlobalTheory.Tw.adj δ.val (x + y) = GlobalTheory.Tw.adj δ.val x + GlobalTheory.Tw.adj δ.val y :=
    fun x y => by simpa using GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ.val 1 x y
  induction f using Polynomial.induction_on with
  | C e => rw [aeval_C, GlobalTheory.Tw.CentralizerAdjoin.adj_algebraMap δ.isUnit, Polynomial.map_C, aeval_C]; rfl
  | add p q hp hq => rw [map_add, hadd, hp, hq, Polynomial.map_add, map_add]
  | monomial k e ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, GlobalTheory.Tw.CentralizerAdjoin.adj_mul' δ.isUnit, ih,
      GlobalTheory.Tw.CentralizerAdjoin.adj_nrm δ.isUnit, mul_comm _ (X : R[X]), Polynomial.map_mul (p := X), Polynomial.map_X, map_mul, aeval_X]

theorem twCent_star [StarRing R] (δ : GL (Fin n) R)
    (hs : (δ * thetaGL n (starRingEnd R) δ).val.charpoly.Separable) :
    (∀ g, g ∈ twCent (thetaGL n (starRingEnd R)) δ ↔
      NormOne (starRingEnd R) (δ * thetaGL n (starRingEnd R) δ) g.val) ∧
    ∀ f : R[X], aeval (δ * thetaGL n (starRingEnd R) δ).val f = 0 →
      aeval ((δ * thetaGL n (starRingEnd R) δ)⁻¹).val (f.map (starRingEnd R)) = 0 := by
  have hN : (δ * thetaGL n (starRingEnd R) δ).val = GlobalTheory.Tw.nrm δ.val := by
    rw [Units.val_mul, thetaGL_val]; rfl
  unfold NormOne
  rw [hN] at hs
  rw [Matrix.coe_units_inv, hN]
  refine ⟨fun g => ?_, fun f hf => ?_⟩
  · have h1 : g ∈ twCent (thetaGL n (starRingEnd R)) δ ↔ g.val ∈ GlobalTheory.Tw.cent δ.val := by
      change g * δ = δ * _ ↔ IsUnit g.val ∧ _
      rw [Units.ext_iff, Units.val_mul, Units.val_mul, thetaGL_val]
      exact (and_iff_right g.isUnit).symm
    rw [h1, GlobalTheory.Tw.CentralizerAdjoin.cent_eq ⟨δ.isUnit, hs⟩]
    simp only [Set.mem_setOf_eq, Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
    constructor
    · rintro ⟨⟨f, hf⟩, h⟩
      exact ⟨f, hf.symm, by rw [← adj_aeval, hf, h]⟩
    · rintro ⟨f, hf, h⟩
      exact ⟨⟨f, hf.symm⟩, by rw [← adj_aeval, ← hf] at h; exact h⟩
  · rw [← adj_aeval, hf]; simp [GlobalTheory.Tw.adj]

theorem twCent_iff (c : R →+* R) (hc : ∀ x, c (c x) = x) (δ : GL (Fin n) R)
    (hs : (δ * thetaGL n c δ).val.charpoly.Separable) :
    (∀ g, g ∈ twCent (thetaGL n c) δ ↔ NormOne c (δ * thetaGL n c δ) g.val) ∧
    ∀ f : R[X], aeval (δ * thetaGL n c δ).val f = 0 → aeval ((δ * thetaGL n c δ)⁻¹).val (f.map c) = 0 := by
  letI : StarRing R :=
    { star := c
      star_involutive := hc
      star_mul := fun x y => by rw [mul_comm y x |>.symm]; exact (map_mul c y x).trans (by rfl) |>.trans rfl
      star_add := map_add c }
  have e : c = starRingEnd R := RingHom.ext fun _ => rfl
  rw [e] at hs ⊢
  exact twCent_star δ hs

def blkHom (h : Matrix (Fin n) (Fin a ⊕ Fin b) R) (h' : Matrix (Fin a ⊕ Fin b) (Fin n) R) (h1 : h * h' = 1)
    (h2 : h' * h = 1) : (Matrix (Fin a) (Fin a) R × Matrix (Fin b) (Fin b) R) →ₐ[R] Matrix (Fin n) (Fin n) R where
  toFun p := h * fromBlocks p.1 0 0 p.2 * h'
  map_one' := by simp [h1]
  map_mul' p q := by
    have : fromBlocks (p * q).1 0 0 (p * q).2 = fromBlocks p.1 0 0 p.2 * fromBlocks q.1 0 0 q.2 := by
      simp [fromBlocks_multiply]
    rw [this]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc h' h, h2, Matrix.one_mul]
  map_zero' := by simp
  map_add' p q := by
    rw [← Matrix.add_mul, ← Matrix.mul_add, fromBlocks_add]; simp
  commutes' r := by
    have : fromBlocks (algebraMap R (Matrix (Fin a) (Fin a) R × Matrix (Fin b) (Fin b) R) r).1 0 0
        (algebraMap R (Matrix (Fin a) (Fin a) R × Matrix (Fin b) (Fin b) R) r).2 = r • 1 := by
      rw [← fromBlocks_one, fromBlocks_smul]; simp [Algebra.algebraMap_eq_smul_one]
    rw [this]; simp [h1, Algebra.algebraMap_eq_smul_one]

variable (h : Matrix (Fin n) (Fin a ⊕ Fin b) R) (h' : Matrix (Fin a ⊕ Fin b) (Fin n) R) (h1 : h * h' = 1)
    (h2 : h' * h = 1)

theorem blkHom_apply (p) : blkHom h h' h1 h2 p = h * fromBlocks p.1 0 0 p.2 * h' := rfl

theorem blkHom_left (p) : h' * blkHom h h' h1 h2 p * h = fromBlocks p.1 0 0 p.2 := by
  rw [blkHom_apply]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem blkHom_leftInverse : Function.LeftInverse
    (fun z : Matrix (Fin n) (Fin n) R => ((h' * z * h).toBlocks₁₁, (h' * z * h).toBlocks₂₂)) (blkHom h h' h1 h2) :=
  fun p => by simp only [blkHom_left, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]

def blkGL : GL (Fin a) R × GL (Fin b) R →* GL (Fin n) R :=
  (Units.map (blkHom h h' h1 h2).toRingHom.toMonoidHom).comp MulEquiv.prodUnits.symm.toMonoidHom

theorem blkGL_val (x y) : (blkGL h h' h1 h2 (x, y)).val = blkHom h h' h1 h2 (x.val, y.val) := rfl

theorem isClosedEmbedding_unitsMap {A B : Type} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]
    [T1Space A] [ContinuousMul A] (f : A →* B) (hf : Topology.IsClosedEmbedding f) :
    Topology.IsClosedEmbedding (Units.map f) := by
  refine Topology.IsClosedEmbedding.of_comp (Units.isEmbedding_embedProduct (M := B)) ?_
  exact (hf.prodMap ((MulOpposite.opHomeomorph.isClosedEmbedding.comp hf).comp
    MulOpposite.opHomeomorph.symm.isClosedEmbedding)).comp Units.isClosedEmbedding_embedProduct

theorem isClosedEmbedding_blkGL [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    Topology.IsClosedEmbedding (blkGL h h' h1 h2) := by
  refine (isClosedEmbedding_unitsMap (blkHom h h' h1 h2).toRingHom.toMonoidHom ?_).comp
    Homeomorph.prodUnits.symm.isClosedEmbedding
  refine (blkHom_leftInverse h h' h1 h2).isClosedEmbedding ?_ ?_
  · have : Continuous fun z : Matrix (Fin n) (Fin n) R => h' * z * h :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact (continuous_matrix fun i j => this.matrix_elem _ _).prodMk (continuous_matrix fun i j => this.matrix_elem _ _)
  · exact (continuous_const.matrix_mul (continuous_fst.matrix_fromBlocks continuous_const continuous_const
      continuous_snd)).matrix_mul continuous_const

theorem aeval_blkGL (x : GL (Fin a) R) (y : GL (Fin b) R) (f : R[X]) :
    aeval (blkGL h h' h1 h2 (x, y)).val f = blkHom h h' h1 h2 (aeval x.val f, aeval y.val f) := by
  rw [blkGL_val, aeval_algHom_apply, aeval_prod_apply]

theorem normOne_blk (c : R →+* R) (N₁ : GL (Fin a) R) (N₂ : GL (Fin b) R) (P₁ P₂ : R[X]) (hP : IsCoprime P₁ P₂)
    (e₁ : aeval N₁.val P₁ = 0) (e₂ : aeval N₂.val P₂ = 0) (e₁' : aeval (N₁⁻¹).val (P₁.map c) = 0)
    (e₂' : aeval (N₂⁻¹).val (P₂.map c) = 0) (g : GL (Fin n) R) :
    NormOne c (blkGL h h' h1 h2 (N₁, N₂)) g.val ↔
      ∃ x y, NormOne c N₁ x.val ∧ NormOne c N₂ y.val ∧ blkGL h h' h1 h2 (x, y) = g := by
  have hinv : (blkGL h h' h1 h2 (N₁, N₂))⁻¹ = blkGL h h' h1 h2 (N₁⁻¹, N₂⁻¹) := (map_inv _ _).symm
  unfold NormOne
  simp only [hinv, aeval_blkGL]
  constructor
  · rintro ⟨f, hf, hg⟩
    rw [hf, ← map_mul, ← map_one (blkHom h h' h1 h2)] at hg
    have hg' := (blkHom_leftInverse h h' h1 h2).injective hg
    have g1 : aeval N₁.val f * aeval (N₁⁻¹).val (f.map c) = 1 := congrArg Prod.fst hg'
    have g2 : aeval N₂.val f * aeval (N₂⁻¹).val (f.map c) = 1 := congrArg Prod.snd hg'
    exact ⟨⟨_, _, g1, mul_eq_one_comm.1 g1⟩, ⟨_, _, g2, mul_eq_one_comm.1 g2⟩, ⟨f, rfl, g1⟩, ⟨f, rfl, g2⟩,
      Units.ext hf.symm⟩
  · rintro ⟨x, y, ⟨f₁, hx, hx'⟩, ⟨f₂, hy, hy'⟩, rfl⟩
    obtain ⟨u, v, huv⟩ := hP
    have k1 : f₁ + (f₂ - f₁) * u * P₁ = f₂ + (f₁ - f₂) * v * P₂ := by linear_combination (f₂ - f₁) * huv
    have a1 : aeval N₁.val (f₁ + (f₂ - f₁) * u * P₁) = x.val := by
      rw [map_add, map_mul, e₁, mul_zero, add_zero, hx]
    have a2 : aeval N₂.val (f₁ + (f₂ - f₁) * u * P₁) = y.val := by
      rw [k1, map_add, map_mul, e₂, mul_zero, add_zero, hy]
    have a3 : aeval (N₁⁻¹).val ((f₁ + (f₂ - f₁) * u * P₁).map c) = aeval (N₁⁻¹).val (f₁.map c) := by
      rw [Polynomial.map_add, Polynomial.map_mul, map_add, map_mul, e₁', mul_zero, add_zero]
    have a4 : aeval (N₂⁻¹).val ((f₁ + (f₂ - f₁) * u * P₁).map c) = aeval (N₂⁻¹).val (f₂.map c) := by
      rw [k1, Polynomial.map_add, Polynomial.map_mul, map_add, map_mul, e₂', mul_zero, add_zero]
    refine ⟨f₁ + (f₂ - f₁) * u * P₁, by rw [a1, a2, blkGL_val], ?_⟩
    rw [a3, a4, blkGL_val, ← map_mul, Prod.mk_mul_mk, hx', hy']
    exact map_one _

end Torus

section Exist

theorem charpoly_inv_conjTranspose_complex {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hs : A.charpoly.Separable)
    (h : ∀ z ∈ A.charpoly.roots, ‖z‖ = 1) : IsUnit A.det ∧ (A⁻¹)ᴴ.charpoly = A.charpoly := by
  have hd : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have : (0 : ℂ) ∈ A.charpoly.roots := by
      rw [mem_roots A.charpoly_monic.ne_zero, IsRoot, Matrix.eval_charpoly, map_zero, zero_sub, Matrix.det_neg, h0,
        mul_zero]
    simpa using h 0 this
  refine ⟨hd, eq_of_monic_of_dvd_of_natDegree_le A.charpoly_monic (Matrix.charpoly_monic _) ?_ (by simp)⟩
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots A.charpoly_monic.ne_zero ?_
  rw [Multiset.le_iff_subset (nodup_roots hs)]
  intro z hz
  have h1 : star z * z = 1 := by
    have := Complex.conj_mul' z
    rw [h z hz] at this
    simpa using this
  rw [mem_roots (Matrix.charpoly_monic _).ne_zero, IsRoot, Matrix.eval_charpoly] at hz ⊢
  have e : Matrix.scalar (Fin n) z - (A⁻¹)ᴴ = ((-star z) • ((Matrix.scalar (Fin n) z - A) * A⁻¹))ᴴ := by
    rw [Matrix.sub_mul, Matrix.mul_nonsing_inv _ hd, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul, neg_mul, h1]
    simp [sub_eq_neg_add, add_comm]
  rw [e, Matrix.det_conjTranspose, Matrix.det_smul, Matrix.det_mul, hz]
  simp

theorem exists_nrm_eq {K : Type} [Field K] [StarRing K] {n : ℕ}
    (hinf : {u : K | ∃ c : K, star c ≠ 0 ∧ u * star c = c}.Infinite) (N : Matrix (Fin n) (Fin n) K)
    (hs : N.charpoly.Separable) (hd : IsUnit N.det) (hN : (N⁻¹)ᴴ.charpoly = N.charpoly) :
    ∃ δ : GL (Fin n) K, GlobalTheory.Tw.nrm δ.val = N := by
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (M := (N⁻¹)ᴴ) (N := N) (by rwa [GlobalTheory.Orb.IsRegSS, hN]) hN.symm
  have h1 : N * x.val * Nᴴ = x.val := by
    rw [hx, Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, conjTranspose_one, Matrix.mul_one]
  obtain ⟨ε, hε⟩ : ∃ ε : K, ε = (-1) ^ (n - 1) := ⟨_, rfl⟩
  have hεs : star ε = ε := by simp [hε]
  have hεε : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  let B := (-ε) • (N * x.valᴴ * (x⁻¹).val)
  obtain ⟨u, ⟨c, hc, huc⟩, hu⟩ := hinf.exists_notMem_finset B.charpoly.roots.toFinset
  rw [Multiset.mem_toFinset, mem_roots B.charpoly_monic.ne_zero, IsRoot, Matrix.eval_charpoly] at hu
  let M := c • x.val + (ε * star c) • (N * x.valᴴ)
  have hM : M = star c • ((Matrix.scalar (Fin n) u - B) * x.val) := by
    simp only [M, B]
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc _ _ x.val, Units.inv_mul, Matrix.mul_one,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul,
      smul_smul, mul_comm (star c) u, huc, mul_neg, neg_smul, sub_neg_eq_add, mul_comm (star c)]
  have hMd : IsUnit M.det := by
    rw [hM, Matrix.det_smul, Matrix.det_mul, isUnit_iff_ne_zero]
    exact mul_ne_zero (pow_ne_zero _ hc) (mul_ne_zero hu ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero)
  have hNM : N * Mᴴ = ε • M := by
    simp only [M, conjTranspose_add, conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, h1, star_mul', star_star, hεs, smul_add, smul_smul]
    rw [add_comm, ← mul_assoc, hεε, one_mul]
  have hPP : GlobalTheory.Tw.Phi n K * (GlobalTheory.Tw.Phi n K)ᵀ = 1 := Phi_mul_transpose n K
  have hPP' : (GlobalTheory.Tw.Phi n K)ᵀ * GlobalTheory.Tw.Phi n K = 1 := mul_eq_one_comm.1 hPP
  have hTT : (GlobalTheory.Tw.Phi n K)ᵀ * (GlobalTheory.Tw.Phi n K)ᵀ = ε • 1 := by
    conv_lhs => lhs; rw [GlobalTheory.Tw.Model.Phi_transpose, ← hε]
    rw [Matrix.smul_mul, hPP]
  have hinv : M * (GlobalTheory.Tw.Phi n K)ᵀ * (GlobalTheory.Tw.Phi n K * M⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ M⁻¹, hPP', Matrix.one_mul, Matrix.mul_nonsing_inv _ hMd]
  refine ⟨⟨_, _, hinv, mul_eq_one_comm.1 hinv⟩, ?_⟩
  change M * (GlobalTheory.Tw.Phi n K)ᵀ * (GlobalTheory.Tw.Phi n K * ((M * (GlobalTheory.Tw.Phi n K)ᵀ)⁻¹)ᴴ * (GlobalTheory.Tw.Phi n K)ᵀ) = N
  rw [Matrix.inv_eq_right_inv hinv, conjTranspose_mul, GlobalTheory.Tw.Model.Phi_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [hTT, ← Matrix.mul_assoc _ (GlobalTheory.Tw.Phi n K), hPP', Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.mul_smul, ← Matrix.smul_mul, ← hNM, Matrix.mul_assoc, ← conjTranspose_mul, Matrix.nonsing_inv_mul _ hMd,
    conjTranspose_one, Matrix.mul_one]

theorem infinite_quot {K : Type} [Field K] [CharZero K] [StarRing K] (z : K) (hz : star z ≠ z) :
    {u : K | ∃ c : K, star c ≠ 0 ∧ u * star c = c}.Infinite := by
  obtain ⟨w, hw⟩ : ∃ w, w = z - star z := ⟨_, rfl⟩
  have h0 : w ≠ 0 := hw ▸ sub_ne_zero.2 hz.symm
  have hs : star w = -w := by simp [hw]
  have hk : ∀ k : ℕ, (k : K) - w ≠ 0 := fun k h => by
    have h1 : w = k := (sub_eq_zero.1 h).symm
    have h2 : star w = w := by rw [h1, star_natCast]
    exact h0 (self_eq_neg.1 (h2.symm.trans hs))
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k + w) / (k - w)) (fun k l h => ?_) fun k => ?_
  · have h1 := (div_eq_div_iff (hk k) (hk l)).1 h
    have h2 : 2 * w * ((l : K) - k) = 0 := by linear_combination h1
    simp only [mul_eq_zero, two_ne_zero, h0, false_or, sub_eq_zero, Nat.cast_inj] at h2
    exact h2.symm
  · have e : star ((k : K) + w) = k - w := by rw [star_add, star_natCast, hs, sub_eq_add_neg]
    exact ⟨k + w, e ▸ hk k, by rw [e, div_mul_cancel₀ _ (hk k)]⟩

theorem exists_charpoly_eq {K : Type} [Field K] (P : K[X]) (hP : P.Monic) :
    ∃ N : Matrix (Fin P.natDegree) (Fin P.natDegree) K, N.charpoly = P :=
  ⟨_, (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hP.ne_zero)).trans
    (AdjoinRoot.minpoly_powerBasis_gen_of_monic hP)⟩

theorem exists_norm (E : Type) [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) :
    ∃ δ : GL (Fin n) E, (δ * thE E n δ).val.charpoly = P := by
  obtain ⟨hm, hn, hs, hr⟩ := hP
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) E, N.charpoly = P := hn ▸ exists_charpoly_eq P hm
  letI : StarRing E :=
    { star := IsCMField.complexConj E
      star_involutive := IsCMField.complexConj_apply_apply E
      star_mul := fun x y => by rw [mul_comm x y]; exact map_mul (IsCMField.complexConj E) y x
      star_add := map_add (IsCMField.complexConj E) }
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hA : (N.map τ).charpoly = P.map τ := by rw [Matrix.charpoly_map, hN]
  obtain ⟨h1, h2⟩ := charpoly_inv_conjTranspose_complex (N.map τ) (by rw [hA]; exact hs.map) (by rw [hA]; exact hr τ)
  have hd : IsUnit N.det := by
    rw [isUnit_iff_ne_zero] at h1 ⊢
    intro h0
    apply h1
    rw [show N.map τ = τ.mapMatrix N from rfl, ← RingHom.map_det, h0, map_zero]
  have hi : (N.map τ)⁻¹ = (N⁻¹).map τ :=
    Matrix.inv_eq_right_inv (by rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hd, Matrix.map_one _ τ.map_zero τ.map_one])
  have h3 : (N⁻¹)ᴴ.charpoly = N.charpoly := by
    apply Polynomial.map_injective τ τ.injective
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, ← h2, hi]
    congr 1
    ext i j
    exact IsCMField.complexEmbedding_complexConj E τ _
  obtain ⟨z, hz⟩ : ∃ z : E, star z ≠ z := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  obtain ⟨δ, hδ⟩ := exists_nrm_eq (infinite_quot z hz) N (by rw [hN]; exact hs) hd h3
  refine ⟨δ, ?_⟩
  have e : thE E n = thetaGL n (starRingEnd E) := rfl
  rw [e, Units.val_mul, thetaGL_val]
  exact (congrArg Matrix.charpoly hδ).trans hN

end Exist

section Main

theorem mem_range_map {K R : Type} [Field K] [CommRing R] [Nontrivial R] {n : ℕ} (p : K →+* R) (x : GL (Fin n) R) :
    x ∈ (GeneralLinearGroup.map p : GL (Fin n) K →* GL (Fin n) R).range ↔ ∃ M : Matrix (Fin n) (Fin n) K, M.map p = x.val := by
  refine ⟨fun ⟨y, hy⟩ => ⟨y.val, hy ▸ rfl⟩, fun ⟨M, hM⟩ => ?_⟩
  have hd : M.det ≠ 0 := fun h0 => by
    have h1 := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
    rw [← hM, show M.map p = p.mapMatrix M from rfl, ← RingHom.map_det, h0, map_zero] at h1
    exact not_isUnit_zero h1
  exact ⟨GeneralLinearGroup.mkOfDetNeZero M hd, Units.ext hM⟩

theorem map_fromBlocks_zero {K R : Type} [CommRing K] [CommRing R] {a b : ℕ} (p : K →+* R)
    (x : Matrix (Fin a) (Fin a) K) (y : Matrix (Fin b) (Fin b) K) :
    (fromBlocks x 0 0 y).map p = fromBlocks (x.map p) 0 0 (y.map p) := by
  rw [fromBlocks_map, Matrix.map_zero _ p.map_zero, Matrix.map_zero _ p.map_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ratF_norm {n : ℕ} (δ : GL (Fin n) E) :
    ratF E n δ * thF E n (ratF E n δ) = ratF E n (δ * thE E n δ) := by
  rw [map_mul]
  congr 1
  exact (GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) δ).symm

theorem charpoly_ratF_norm {n : ℕ} (δ : GL (Fin n) E) :
    (ratF E n δ * thF E n (ratF E n δ)).val.charpoly = (δ * thE E n δ).val.charpoly.map (algebraMap E (Af E)) := by
  rw [ratF_norm, ← Matrix.charpoly_map]; rfl

theorem mass_mul {n a b : ℕ} (hn : a + b = n) (δ : GL (Fin n) E) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E)
    (hc : IsCoprime (δ₁ * thE E a δ₁).val.charpoly (δ₂ * thE E b δ₂).val.charpoly)
    (hs : (δ * thE E n δ).val.charpoly.Separable)
    (h : (δ * thE E n δ).val.charpoly = (δ₁ * thE E a δ₁).val.charpoly * (δ₂ * thE E b δ₂).val.charpoly) :
    mass (thF E n) (ratF E n).range (ratF E n δ) =
      mass (thF E a) (ratF E a).range (ratF E a δ₁) * mass (thF E b) (ratF E b).range (ratF E b δ₂) := by
  haveI : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  haveI : Nontrivial (Af E) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact (pLoc E ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩).domain_nontrivial
  let e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let p := algebraMap E (Af E)
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (M := (δ * thE E n δ).val)
    (N := reindex e e (fromBlocks (δ₁ * thE E a δ₁).val 0 0 (δ₂ * thE E b δ₂).val)) hs
    (by rw [charpoly_reindex, charpoly_fromBlocks_zero₁₂, h])
  obtain ⟨g, hg⟩ : ∃ g, g = (x⁻¹).val.submatrix id e := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g', g' = x.val.submatrix e id := ⟨_, rfl⟩
  have g1 : g * g' = 1 := by rw [hg, hg', submatrix_mul_equiv, Units.inv_mul, submatrix_id_id]
  have g2 : g' * g = 1 := by
    rw [hg, hg', ← submatrix_mul _ _ _ _ _ Function.bijective_id, Units.mul_inv, submatrix_one_equiv]
  have g3 : g * fromBlocks (δ₁ * thE E a δ₁).val 0 0 (δ₂ * thE E b δ₂).val * g' = (δ * thE E n δ).val := by
    have : fromBlocks (δ₁ * thE E a δ₁).val 0 0 (δ₂ * thE E b δ₂).val =
        (reindex e e (fromBlocks (δ₁ * thE E a δ₁).val 0 0 (δ₂ * thE E b δ₂).val)).submatrix e e := by simp
    rw [this, hg, hg', Matrix.mul_assoc, submatrix_mul_equiv, hx, submatrix_mul_equiv, Units.inv_mul_cancel_left,
      submatrix_id_id]
  have h1 : g.map p * g'.map p = 1 := by rw [← Matrix.map_mul, g1, Matrix.map_one _ p.map_zero p.map_one]
  have h2 : g'.map p * g.map p = 1 := by rw [← Matrix.map_mul, g2, Matrix.map_one _ p.map_zero p.map_one]
  have hb : ∀ u v, blkHom _ _ h1 h2 (Matrix.map u p, Matrix.map v p) = (g * fromBlocks u 0 0 v * g').map p := by
    intro u v
    rw [blkHom_apply, Matrix.map_mul, Matrix.map_mul, map_fromBlocks_zero]
  have hN : ratF E n δ * thF E n (ratF E n δ) =
      blkGL _ _ h1 h2 (ratF E a δ₁ * thF E a (ratF E a δ₁), ratF E b δ₂ * thF E b (ratF E b δ₂)) := by
    simp only [ratF_norm]
    exact Units.ext ((congrArg (Matrix.map · p) g3).symm.trans (hb _ _).symm)
  have hs' := hs
  rw [h] at hs'
  obtain ⟨t, -⟩ := twCent_iff _ GlobalTheory.ThetaPull.cFin_cFin (ratF E n δ) (charpoly_ratF_norm δ ▸ hs.map)
  obtain ⟨t₁, s₁⟩ := twCent_iff _ GlobalTheory.ThetaPull.cFin_cFin (ratF E a δ₁)
    (charpoly_ratF_norm δ₁ ▸ hs'.of_mul_left.map)
  obtain ⟨t₂, s₂⟩ := twCent_iff _ GlobalTheory.ThetaPull.cFin_cFin (ratF E b δ₂)
    (charpoly_ratF_norm δ₂ ▸ hs'.of_mul_right.map)
  have hc' := hc.map (Polynomial.mapRingHom p)
  simp only [Polynomial.coe_mapRingHom, p, ← charpoly_ratF_norm] at hc'
  refine mass_prod (blkGL _ _ h1 h2) (isClosedEmbedding_blkGL _ _ h1 h2) _ _ _ _ _ _ _ _ _ ?_ fun u v => ?_
  · ext y
    refine (t y).trans ?_
    change NormOne _ (ratF E n δ * thF E n (ratF E n δ)) _ ↔ _
    rw [hN]
    refine (normOne_blk _ _ h1 h2 _ _ _ _ _ hc' (Matrix.aeval_self_charpoly _) (Matrix.aeval_self_charpoly _)
      (s₁ _ (Matrix.aeval_self_charpoly _)) (s₂ _ (Matrix.aeval_self_charpoly _)) y).trans ?_
    constructor
    · rintro ⟨u, v, hu, hv, rfl⟩
      exact ⟨(u, v), ⟨(t₁ u).2 hu, (t₂ v).2 hv⟩, rfl⟩
    · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
      exact ⟨u, v, (t₁ u).1 hu, (t₂ v).1 hv, rfl⟩
  · simp only [ratF, mem_range_map, blkGL_val]
    constructor
    · rintro ⟨M, hM⟩
      have k := blkHom_leftInverse _ _ h1 h2 (u.val, v.val)
      rw [← hM] at k
      change ((_ * M.map p * _ : Matrix _ _ _).toBlocks₁₁, (_ * M.map p * _ : Matrix _ _ _).toBlocks₂₂) = _ at k
      simp only [← Matrix.map_mul] at k
      exact ⟨⟨(g' * M * g).toBlocks₁₁, congrArg Prod.fst k⟩, ⟨(g' * M * g).toBlocks₂₂, congrArg Prod.snd k⟩⟩
    · rintro ⟨⟨u₀, hu⟩, ⟨v₀, hv⟩⟩
      exact ⟨_, by rw [← hu, ← hv, hb]⟩

omit [NumberField E] [IsCMField E] in
theorem mul_mem_Ell {a b : ℕ} {P₁ P₂ : E[X]} (h₁ : P₁ ∈ Ell E a) (h₂ : P₂ ∈ Ell E b) (hc : IsCoprime P₁ P₂) :
    P₁ * P₂ ∈ Ell E (a + b) := by
  obtain ⟨m₁, d₁, s₁, r₁⟩ := h₁
  obtain ⟨m₂, d₂, s₂, r₂⟩ := h₂
  refine ⟨m₁.mul m₂, by rw [m₁.natDegree_mul m₂, d₁, d₂], s₁.mul s₂ hc, fun τ z hz => ?_⟩
  rw [Polynomial.map_mul, roots_mul ((m₁.map τ).mul (m₂.map τ)).ne_zero, Multiset.mem_add] at hz
  exact hz.elim (r₁ τ z) (r₂ τ z)

theorem kap_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (P₁ P₂ : E[X]), P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCoprime P₁ P₂ → kap (P₁ * P₂) = kap P₁ * kap P₂ ∧ (∃ δ : GL (Fin a) E, (δ * thE E a δ).val.charpoly = P₁) ∧ P₁ * P₂ ∈ Ell E (a + b) := by
  intro E _ _ _ _ a b P₁ P₂ h₁ h₂ hc
  have h := mul_mem_Ell h₁ h₂ hc
  refine ⟨?_, exists_norm E h₁, h⟩
  have hn : P₁.natDegree + P₂.natDegree = (P₁ * P₂).natDegree := (h₁.1.natDegree_mul h₂.1).symm
  have e₁ := exists_norm E (n := P₁.natDegree) ⟨h₁.1, rfl, h₁.2.2⟩
  have e₂ := exists_norm E (n := P₂.natDegree) ⟨h₂.1, rfl, h₂.2.2⟩
  have e := exists_norm E (n := (P₁ * P₂).natDegree) ⟨h.1, rfl, h.2.2⟩
  unfold kap
  rw [dif_pos e, dif_pos e₁, dif_pos e₂, mass_mul hn e.choose e₁.choose e₂.choose
    (by rw [e₁.choose_spec, e₂.choose_spec]; exact hc) (by rw [e.choose_spec]; exact h.2.2.1)
    (by rw [e.choose_spec, e₁.choose_spec, e₂.choose_spec]),
    UniqueFactorizationMonoid.normalizedFactors_mul h₁.1.ne_zero h₂.1.ne_zero, Multiset.card_add, pow_add,
    mul_div_mul_comm]

end Main

end GlobalTheory.BCT.KapMul
