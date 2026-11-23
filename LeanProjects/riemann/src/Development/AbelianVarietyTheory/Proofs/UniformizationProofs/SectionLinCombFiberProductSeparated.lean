import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MemRangeRTensorOfForallDual

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct TopologicalSpace

noncomputable section

namespace GlobalTheory.SectionsProduct

section Algebra
variable {F : Type} [CommRing F]

theorem exists_sum_of_ker (hF : IsField F) {A B A' B' : Type} [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    [AddCommGroup A'] [Module F A'] [AddCommGroup B'] [Module F B'] (d₁ : A →ₗ[F] A') (d₂ : B →ₗ[F] B')
    (t : A ⊗[F] B) (h₁ : d₁.rTensor B t = 0) (h₂ : d₂.lTensor A t = 0) :
    ∃ (n : ℕ) (a : Fin n → A) (b : Fin n → B), (∀ i, d₁ (a i) = 0) ∧ (∀ i, d₂ (b i) = 0) ∧
      t = ∑ i, a i ⊗ₜ[F] b i := by
  letI := hF.toField
  obtain ⟨s, rfl⟩ := (Module.Flat.rTensor_exact B (LinearMap.exact_subtype_ker_map d₁) t).1 h₁
  have h₃ : d₂.lTensor (LinearMap.ker d₁) s = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := B') (LinearMap.ker d₁).subtype
      (Submodule.injective_subtype _)
    rw [map_zero, ← h₂, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]
  obtain ⟨u, rfl⟩ := (Module.Flat.lTensor_exact (LinearMap.ker d₁) (LinearMap.exact_subtype_ker_map d₂) s).1 h₃
  obtain ⟨n, a, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq u
  exact ⟨n, fun i => (a i).1, fun i => (b i).1, fun i => (a i).2, fun i => (b i).2, by simp [map_sum]⟩

section
variable {P Q : Type} [Finite P] [Finite Q] {A : P → Type} {B : Q → Type}
  [∀ p, AddCommGroup (A p)] [∀ p, Module F (A p)] [∀ p, AddCommGroup (B p)] [∀ p, Module F (B p)]

theorem pi_tensor_ext (t : (∀ p, A p) ⊗[F] (∀ q, B q))
    (h : ∀ p q, TensorProduct.map (LinearMap.proj p) (LinearMap.proj q) t = 0) : t = 0 := by
  classical
  cases nonempty_fintype P
  cases nonempty_fintype Q
  have : ∀ t : (∀ p, A p) ⊗[F] (∀ q, B q), t = ∑ p, ∑ q, TensorProduct.map (LinearMap.single F A p) (LinearMap.single F B q)
      (TensorProduct.map (LinearMap.proj p) (LinearMap.proj q) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.proj_apply, LinearMap.single_apply, ← TensorProduct.tmul_sum,
        ← TensorProduct.sum_tmul, Finset.univ_sum_single]
    | add x y hx hy =>
      simp only [map_add, Finset.sum_add_distrib]
      rw [← hx, ← hy]
  rw [this t]
  simp [h]

theorem pi_tensor_surj (c : ∀ p q, A p ⊗[F] B q) : ∃ t : (∀ p, A p) ⊗[F] (∀ q, B q),
    ∀ p q, TensorProduct.map (LinearMap.proj p) (LinearMap.proj q) t = c p q := by
  classical
  cases nonempty_fintype P
  cases nonempty_fintype Q
  refine ⟨∑ p, ∑ q, TensorProduct.map (LinearMap.single F A p) (LinearMap.single F B q) (c p q), fun p q => ?_⟩
  simp only [map_sum, TensorProduct.map_map]
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp [LinearMap.proj_comp_single_same]
  · intro q' _ hq
    rw [LinearMap.proj_comp_single_ne F B q q' hq.symm, TensorProduct.map_zero_right, LinearMap.zero_apply]
  · simp
  · intro p' _ hp
    simp [LinearMap.proj_comp_single_ne F A p p' hp.symm]
  · simp

theorem exists_sum_of_compatible (hF : IsField F) {A' : P → P → Type} {B' : Q → Q → Type}
    [∀ p p', AddCommGroup (A' p p')] [∀ p p', Module F (A' p p')]
    [∀ p p', AddCommGroup (B' p p')] [∀ p p', Module F (B' p p')]
    (ρ₁ : ∀ p p', A p →ₗ[F] A' p p') (ρ₂ : ∀ p p', A p' →ₗ[F] A' p p')
    (σ₁ : ∀ p p', B p →ₗ[F] B' p p') (σ₂ : ∀ p p', B p' →ₗ[F] B' p p')
    (c : ∀ p q, A p ⊗[F] B q)
    (h₁ : ∀ p p' q, (ρ₁ p p').rTensor (B q) (c p q) = (ρ₂ p p').rTensor (B q) (c p' q))
    (h₂ : ∀ p q q', (σ₁ q q').lTensor (A p) (c p q) = (σ₂ q q').lTensor (A p) (c p q')) :
    ∃ (n : ℕ) (a : Fin n → ∀ p, A p) (b : Fin n → ∀ q, B q), (∀ i p p', ρ₁ p p' (a i p) = ρ₂ p p' (a i p')) ∧
      (∀ i q q', σ₁ q q' (b i q) = σ₂ q q' (b i q')) ∧ ∀ p q, c p q = ∑ i, a i p ⊗ₜ[F] b i q := by
  obtain ⟨t, ht⟩ := pi_tensor_surj c
  let d₁ : (∀ p, A p) →ₗ[F] (∀ x : P × P, A' x.1 x.2) :=
    LinearMap.pi fun x => ρ₁ x.1 x.2 ∘ₗ LinearMap.proj x.1 - ρ₂ x.1 x.2 ∘ₗ LinearMap.proj x.2
  let d₂ : (∀ p, B p) →ₗ[F] (∀ x : Q × Q, B' x.1 x.2) :=
    LinearMap.pi fun x => σ₁ x.1 x.2 ∘ₗ LinearMap.proj x.1 - σ₂ x.1 x.2 ∘ₗ LinearMap.proj x.2
  obtain ⟨n, a, b, ha, hb, e⟩ := exists_sum_of_ker hF d₁ d₂ t (pi_tensor_ext _ fun x q => by
      rw [← sub_eq_zero.2 (h₁ x.1 x.2 q), ← ht, ← ht]
      clear ht
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [d₁, TensorProduct.sub_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]; abel)
    (pi_tensor_ext _ fun p x => by
      rw [← sub_eq_zero.2 (h₂ p x.1 x.2), ← ht, ← ht]
      clear ht
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [d₂, TensorProduct.tmul_sub]
      | add x y hx hy => simp only [map_add, hx, hy]; abel)
  refine ⟨n, a, b, fun i p p' => sub_eq_zero.1 (congrFun (ha i) (p, p')),
    fun i p p' => sub_eq_zero.1 (congrFun (hb i) (p, p')), fun p q => ?_⟩
  rw [← ht, e]
  simp [map_sum]

theorem eq_zero_of_linearIndependent (hF : IsField F) {C : Type} [AddCommGroup C] [Module F C] {n : ℕ} (a : Fin n → ∀ p, A p)
    (ha : LinearIndependent F a) (b : Fin n → C) (h : ∀ p, ∑ i, a i p ⊗ₜ[F] b i = 0) (k : Fin n) : b k = 0 := by
  letI := hF.toField
  have e : ∑ i, a i ⊗ₜ[F] (fun _ : Unit => b i) = 0 :=
    pi_tensor_ext (B := fun _ : Unit => C) _ fun p q => by simpa [map_sum] using h p
  obtain ⟨l, hl⟩ := (Finsupp.linearCombination F a).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 ha)
  have hl' : ∀ i, l (a i) = Finsupp.single i 1 := fun i => by
    simpa using LinearMap.congr_fun hl (Finsupp.single i 1)
  have := congrArg (fun t => TensorProduct.lid F (Unit → C) ((Finsupp.lapply k ∘ₗ l).rTensor (Unit → C) t) ()) e
  simpa [map_sum, hl', Finsupp.single_apply, ite_apply] using this

end

end Algebra

open GlobalTheory.KuennethOne

variable {B Y T S X₁ X₂ W : Scheme.{0}} {L : LB B} {K : Type} [Fintype K]

theorem gs_sum' (r : T ⟶ Y) (z : T) (U : Y.Opens) (h : r z ∈ U) {n : ℕ} (a : Fin n → Γ(Y, U)) :
    gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by simp only [gs_eq r z U h, map_sum]

theorem gs_zero' (r : T ⟶ Y) (z : T) (U : Y.Opens) (h : r z ∈ U) : gs r z U 0 = 0 := by
  simp only [gs_eq r z U h, map_zero]

theorem trF_same (hL : L.IsLB) (φ : K → (Y ⟶ B)) (ε : K → ℤ) (r : T ⟶ Y) (z : T) {j : K → L.ι}
    (m : r z ∈ LB.wchart L φ j) : trF φ ε r z j j = 1 := mul_eq_left.1 (trF_trans hL φ ε r z m m m)

theorem gs_g (φ : K → (Y ⟶ B)) (ε : K → ℤ) (r : T ⟶ Y) (z : T) {j j' : K → L.ι}
    (m : r z ∈ LB.wchart L φ j) (m' : r z ∈ LB.wchart L φ j') :
    gs r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val = (trF φ ε r z j j').val :=
  (gs_unit r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ⟨m, m'⟩ _).trans (congrArg Units.val (gm_linComb L φ ε r z j j' m m'))

theorem exists_wchart (hL : L.IsLB) (φ : K → (Y ⟶ B)) (y : Y) : ∃ j, y ∈ LB.wchart L φ j := by
  choose j hj using fun k => exists_chart hL (φ k y)
  exact ⟨j, Set.mem_iInter.2 hj⟩

theorem exists_affine_le {V : Y.Opens} {y : Y} (hy : y ∈ V) : ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U ∧ U ≤ V := by
  obtain ⟨U, hU, h₁, h₂⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hy
  exact ⟨U, hU, h₁, h₂⟩

theorem exists_finite_cover (hL : L.IsLB) [CompactSpace Y] (φ : K → (Y ⟶ B)) :
    ∃ (P : Type) (_ : Finite P) (U : P → Y.Opens) (j : P → K → L.ι), (∀ p, IsAffineOpen (U p)) ∧
      (∀ p, U p ≤ LB.wchart L φ (j p)) ∧ ∀ y, ∃ p, y ∈ U p := by
  choose j hj using exists_wchart hL φ
  choose U h₁ h₂ h₃ using fun y => exists_affine_le (hj y)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set Y)) (fun y => (U y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, h₂ y⟩)
  refine ⟨s, inferInstance, fun p => U p, fun p => j p, fun p => h₁ p, fun p => h₃ p, fun y => ?_⟩
  obtain ⟨p, hp, h⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  exact ⟨⟨p, hp⟩, h⟩

theorem exists_sec_of_cover (hL : L.IsLB) (φ : K → (Y ⟶ B)) (ε : K → ℤ) {P : Type} (U : P → Y.Opens)
    (j : P → K → L.ι) (hU : ∀ p, U p ≤ LB.wchart L φ (j p)) (hc : ∀ y, ∃ p, y ∈ U p) (a : ∀ p, Γ(Y, U p))
    (ha : ∀ p p' y, y ∈ U p → y ∈ U p' → gs (𝟙 Y) y (U p) (a p) =
      (trF φ ε (𝟙 Y) y (j p) (j p')).val * gs (𝟙 Y) y (U p') (a p')) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (T : Scheme.{0}) (r : T ⟶ Y) (z : T) (p : P) (k : K → L.ι), r z ∈ U p →
      r z ∈ LB.wchart L φ k →
      gs r z (LB.wchart L φ k) (s.f k) = (trF φ ε r z k (j p)).val * gs r z (U p) (a p) := by
  have gl : ∀ k : K → L.ι, ∃ b : Γ(Y, LB.wchart L φ k), ∀ (T : Scheme.{0}) (r : T ⟶ Y) (z : T) (p : P), r z ∈ U p →
      r z ∈ LB.wchart L φ k → gs r z (LB.wchart L φ k) b = (trF φ ε r z k (j p)).val * gs r z (U p) (a p) := by
    intro k
    obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(Y, LB.wchart L φ k ⊓ U p), ∀ (T : Scheme.{0}) (r : T ⟶ Y) (z : T) p,
        r z ∈ LB.wchart L φ k ⊓ U p →
        gs r z _ (u p) = (trF φ ε r z k (j p)).val * gs r z (U p) (a p) :=
      ⟨fun p => rs (inf_le_inf le_rfl (hU p) : LB.wchart L φ k ⊓ U p ≤ LB.wchart L φ k ⊓ LB.wchart L φ (j p))
          ((LB.LinComb L φ ε).g k (j p)).val * rs inf_le_right (a p),
        fun T r z p hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_res r z _ hz _).trans (gs_g φ ε r z hz.1 (hU p hz.2))) (gs_res r z _ hz _))⟩
    obtain ⟨b, hb⟩ := glue (LB.wchart L φ k) (fun p => LB.wchart L φ k ⊓ U p) (fun p => inf_le_left)
      (fun y hy => by
        obtain ⟨p, hp⟩ := hc y
        exact Opens.mem_iSup.2 ⟨p, hy, hp⟩) u
      (fun p p' => fn_ext fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y p hy.1, hu _ _ y p' hy.2, ha p p' y hy.1.2 hy.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          trF_trans hL φ ε (𝟙 Y) y hy.1.1 (hU p hy.1.2) (hU p' hy.2.2)])
    refine ⟨b, fun T r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L φ k ⊓ U p := ⟨h₂, h₁⟩
    exact (gs_res r z inf_le_left hz b).symm.trans ((congrArg (gs r z _) (hb p)).trans (hu T r z p hz))
  choose b hb using gl
  refine ⟨⟨b, fun k k' => fn_ext fun y hy => ?_⟩, fun T r z p k => hb k T r z p⟩
  obtain ⟨p, hp⟩ := hc y
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    (gs_g φ ε (𝟙 Y) y hy.1 hy.2) (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hb k _ (𝟙 Y) y p hp hy.1).trans (Eq.trans ?_ (congrArg _ (hb k' _ (𝟙 Y) y p hp hy.2)).symm)
  rw [← trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hU p hp), Units.val_mul, _root_.mul_assoc]

def twist (i : Y ⟶ S) (φ : K → (Y ⟶ B)) (ε : K → ℤ) {U U' : Y.Opens} {j j' : K → L.ι}
    (hU : U ≤ LB.wchart L φ j) (hU' : U' ≤ LB.wchart L φ j') : Fn i U' →ₗ[Γ(S, ⊤)] Fn i (U ⊓ U') :=
  LinearMap.mulLeft Γ(S, ⊤) (show Fn i (U ⊓ U') from rs (inf_le_inf hU hU') ((LB.LinComb L φ ε).g j j').val) ∘ₗ
    (rsA i (inf_le_right : U ⊓ U' ≤ U')).toLinearMap

theorem gs_twist (i : Y ⟶ S) (φ : K → (Y ⟶ B)) (ε : K → ℤ) {U U' : Y.Opens} {j j' : K → L.ι}
    (hU : U ≤ LB.wchart L φ j) (hU' : U' ≤ LB.wchart L φ j') (r : T ⟶ Y) (z : T) (hz : r z ∈ U ⊓ U') (a : Fn i U') :
    gs r z (U ⊓ U') (twist i φ ε hU hU' a) = (trF φ ε r z j j').val * gs r z U' a :=
  (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
    ((gs_res r z _ hz _).trans (gs_g φ ε r z (hU hz.1) (hU' hz.2))) (gs_res r z _ hz _))

variable {p : W ⟶ X₁} {q : W ⟶ X₂} {i₁ : X₁ ⟶ S} {i₂ : X₂ ⟶ S} (H : IsPullback p q i₁ i₂)

def prodFn (U : X₁.Opens) (V : X₂.Opens) (t : Fn i₁ U ⊗[Γ(S, ⊤)] Fn i₂ V) : Γ(W, p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) :=
  mm H U V (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) inf_le_left inf_le_right t

theorem prodFn_bijective [IsAffine S] {U : X₁.Opens} {V : X₂.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Function.Bijective (prodFn H U V) := mm_bijective H hU hV

section
variable {U U' : X₁.Opens} {V V' : X₂.Opens} (r : T ⟶ W) (z : T) (hz : r z ∈ p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V)
include hz

theorem gs_prodFn_tmul (a : Fn i₁ U) (b : Fn i₂ V) :
    gs r z _ (prodFn H U V (a ⊗ₜ b)) = gs (r ≫ p) z U a * gs (r ≫ q) z V b :=
  (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_appLE p U _ inf_le_left r z hz a)
    (gs_appLE q V _ inf_le_right r z hz b))

theorem gs_prodFn_add (s t) :
    gs r z _ (prodFn H U V (s + t)) = gs r z _ (prodFn H U V s) + gs r z _ (prodFn H U V t) :=
  (congrArg (gs r z _) (map_add (mm H U V _ inf_le_left inf_le_right) s t)).trans (gs_add r z _ hz _ _)

theorem gs_prodFn_zero : gs r z _ (prodFn H U V 0) = 0 :=
  (congrArg (gs r z _) (map_zero (mm H U V _ inf_le_left inf_le_right))).trans (gs_zero' r z _ hz)

theorem gs_prodFn_sum {n : ℕ} (a : Fin n → Fn i₁ U) (b : Fin n → Fn i₂ V) :
    gs r z _ (prodFn H U V (∑ i, a i ⊗ₜ b i)) = ∑ i, gs (r ≫ p) z U (a i) * gs (r ≫ q) z V (b i) :=
  (congrArg (gs r z _) (map_sum (mm H U V _ inf_le_left inf_le_right) _ _)).trans ((gs_sum' r z _ hz _).trans
    (Finset.sum_congr rfl fun i _ => gs_prodFn_tmul H r z hz (a i) (b i)))

theorem gs_prodFn_map (hz' : r z ∈ p ⁻¹ᵁ U' ⊓ q ⁻¹ᵁ V') (f : Fn i₁ U →ₗ[Γ(S, ⊤)] Fn i₁ U')
    (g : Fn i₂ V →ₗ[Γ(S, ⊤)] Fn i₂ V') (c d : T.presheaf.stalk z)
    (hf : ∀ a, gs (r ≫ p) z U' (f a) = c * gs (r ≫ p) z U a) (hg : ∀ a, gs (r ≫ q) z V' (g a) = d * gs (r ≫ q) z V a)
    (t) : gs r z _ (prodFn H U' V' (TensorProduct.map f g t)) = c * d * gs r z _ (prodFn H U V t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, gs_prodFn_zero H r z hz, gs_prodFn_zero H r z hz', mul_zero]
  | tmul a b => rw [TensorProduct.map_tmul, gs_prodFn_tmul H r z hz, gs_prodFn_tmul H r z hz', hf, hg]; ring
  | add x y hx hy => rw [map_add, gs_prodFn_add H r z hz, gs_prodFn_add H r z hz', hx, hy, mul_add]

end

variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (X₁ ⟶ B)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (X₂ ⟶ B)) (ε₂ : K₂ → ℤ)

theorem trF_sum (r : T ⟶ W) (z : T) (j j' : K₁ ⊕ K₂ → L.ι) :
    trF (Sum.elim (fun k => p ≫ φ₁ k) (fun k => q ≫ φ₂ k)) (Sum.elim ε₁ ε₂) r z j j' =
      trF φ₁ ε₁ (r ≫ p) z (j ∘ Sum.inl) (j' ∘ Sum.inl) * trF φ₂ ε₂ (r ≫ q) z (j ∘ Sum.inr) (j' ∘ Sum.inr) := by
  simp only [trF, Fintype.prod_sum_type, Category.assoc, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]

theorem le_wchart_sum {U : X₁.Opens} {V : X₂.Opens} {j : K₁ → L.ι} {k : K₂ → L.ι} (hU : U ≤ LB.wchart L φ₁ j)
    (hV : V ≤ LB.wchart L φ₂ k) : p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V ≤
      LB.wchart L (Sum.elim (fun k => p ≫ φ₁ k) (fun k => q ≫ φ₂ k)) (Sum.elim j k) := fun y hy =>
  Set.mem_iInter.2 (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 (hU hy.1) a, Set.mem_iInter.1 (hV hy.2) a])

include H in

theorem exists_sum (hL : L.IsLB) [IsAffine S] (hS : IsField Γ(S, ⊤)) [CompactSpace X₁] [CompactSpace X₂]
    [X₁.IsSeparated] [X₂.IsSeparated]
    (v : LB.Sec (LB.LinComb L (Sum.elim (fun k => p ≫ φ₁ k) (fun k => q ≫ φ₂ k)) (Sum.elim ε₁ ε₂))) :
    ∃ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)),
      ∀ (T : Scheme.{0}) (r : T ⟶ W) (z : T) (J), Good L z J →
        sval v r z J = ∑ i, sval (a i) (r ≫ p) z J * sval (b i) (r ≫ q) z J := by
  obtain ⟨P, _, U, j, aU, hU, cU⟩ := exists_finite_cover hL φ₁
  obtain ⟨Q, _, V, k, aV, hV, cV⟩ := exists_finite_cover hL φ₂
  have le := fun x y => le_wchart_sum (p := p) (q := q) φ₁ φ₂ (hU x) (hV y)
  choose c hc using fun x y => (prodFn_bijective H (aU x) (aV y)).2 (rs (le x y) (v.f (Sum.elim (j x) (k y))))
  have hv : ∀ (T : Scheme.{0}) (r : T ⟶ W) (z : T) x y, r z ∈ p ⁻¹ᵁ U x ⊓ q ⁻¹ᵁ V y →
      gs r z _ (prodFn H (U x) (V y) (c x y)) =
        gs r z (LB.wchart L _ (Sum.elim (j x) (k y))) (v.f (Sum.elim (j x) (k y))) :=
    fun T r z x y hz => (congrArg (gs r z _) (hc x y)).trans (gs_res r z (le x y) hz _)
  obtain ⟨n, a, b, ha, hb, e⟩ := exists_sum_of_compatible hS (A := fun x => Fn i₁ (U x)) (B := fun y => Fn i₂ (V y))
    (fun x x' => (rsA i₁ (inf_le_left : U x ⊓ U x' ≤ U x)).toLinearMap) (fun x x' => twist i₁ φ₁ ε₁ (hU x) (hU x'))
    (fun x x' => (rsA i₂ (inf_le_left : V x ⊓ V x' ≤ V x)).toLinearMap) (fun x x' => twist i₂ φ₂ ε₂ (hV x) (hV x')) c
    (fun x x' y => (prodFn_bijective H ((aU x).inf (aU x')) (aV y)).1 (fn_ext fun z hz => by
      have m : (𝟙 W : W ⟶ W) z ∈ p ⁻¹ᵁ U x ⊓ q ⁻¹ᵁ V y := ⟨hz.1.1, hz.2⟩
      have m' : (𝟙 W : W ⟶ W) z ∈ p ⁻¹ᵁ U x' ⊓ q ⁻¹ᵁ V y := ⟨hz.1.2, hz.2⟩
      refine (gs_prodFn_map H (𝟙 W) z m hz (rsA i₁ (inf_le_left : U x ⊓ U x' ≤ U x)).toLinearMap LinearMap.id 1 1
        (fun a => (gs_res (𝟙 W ≫ p) z (inf_le_left : U x ⊓ U x' ≤ U x) hz.1 a).trans (_root_.one_mul _).symm)
        (fun a => (_root_.one_mul _).symm) _).trans
        (Eq.trans ?_ (gs_prodFn_map H (𝟙 W) z m' hz _ LinearMap.id _ 1
          (gs_twist i₁ φ₁ ε₁ (hU x) (hU x') (𝟙 W ≫ p) z hz.1) (fun a => (_root_.one_mul _).symm) _).symm)
      rw [hv _ _ z x y m, hv _ _ z x' y m', sec_trans v (𝟙 W) z (le x y m) (le x' y m'), trF_sum,
        Sum.elim_comp_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_comp_inr,
        trF_same hL φ₂ ε₂ (𝟙 W ≫ q) z (hV y hz.2)]
      simp))
    (fun x y y' => (prodFn_bijective H (aU x) ((aV y).inf (aV y'))).1 (fn_ext fun z hz => by
      have m : (𝟙 W : W ⟶ W) z ∈ p ⁻¹ᵁ U x ⊓ q ⁻¹ᵁ V y := ⟨hz.1, hz.2.1⟩
      have m' : (𝟙 W : W ⟶ W) z ∈ p ⁻¹ᵁ U x ⊓ q ⁻¹ᵁ V y' := ⟨hz.1, hz.2.2⟩
      refine (gs_prodFn_map H (𝟙 W) z m hz LinearMap.id (rsA i₂ (inf_le_left : V y ⊓ V y' ≤ V y)).toLinearMap 1 1
        (fun a => (_root_.one_mul _).symm)
        (fun a => (gs_res (𝟙 W ≫ q) z (inf_le_left : V y ⊓ V y' ≤ V y) hz.2 a).trans (_root_.one_mul _).symm) _).trans
        (Eq.trans ?_ (gs_prodFn_map H (𝟙 W) z m' hz LinearMap.id _ 1 _ (fun a => (_root_.one_mul _).symm)
          (gs_twist i₂ φ₂ ε₂ (hV y) (hV y') (𝟙 W ≫ q) z hz.2) _).symm)
      rw [hv _ _ z x y m, hv _ _ z x y' m', sec_trans v (𝟙 W) z (le x y m) (le x y' m'), trF_sum,
        Sum.elim_comp_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_comp_inr,
        trF_same hL φ₁ ε₁ (𝟙 W ≫ p) z (hU x hz.1)]
      simp))
  choose s hs using fun i => exists_sec_of_cover hL φ₁ ε₁ U j hU cU (a i) (fun x x' z h h' =>
    (gs_res (𝟙 X₁) z (inf_le_left : U x ⊓ U x' ≤ U x) ⟨h, h'⟩ _).symm.trans
      ((congrArg (gs (𝟙 X₁) z (U x ⊓ U x')) (ha i x x')).trans (gs_twist i₁ φ₁ ε₁ (hU x) (hU x') _ z ⟨h, h'⟩ _)))
  choose t ht using fun i => exists_sec_of_cover hL φ₂ ε₂ V k hV cV (b i) (fun x x' z h h' =>
    (gs_res (𝟙 X₂) z (inf_le_left : V x ⊓ V x' ≤ V x) ⟨h, h'⟩ _).symm.trans
      ((congrArg (gs (𝟙 X₂) z (V x ⊓ V x')) (hb i x x')).trans (gs_twist i₂ φ₂ ε₂ (hV x) (hV x') _ z ⟨h, h'⟩ _)))
  refine ⟨n, s, t, fun T r z J hJ => ?_⟩
  obtain ⟨x, hx⟩ := cU ((r ≫ p) z)
  obtain ⟨y, hy⟩ := cV ((r ≫ q) z)
  have m : r z ∈ p ⁻¹ᵁ U x ⊓ q ⁻¹ᵁ V y := ⟨hx, hy⟩
  have m₁ := hJ.mem φ₁ (r ≫ p)
  have m₂ := hJ.mem φ₂ (r ≫ q)
  rw [sval_of v r z J (Sum.elim (fun κ => J ((r ≫ p) ≫ φ₁ κ)) (fun κ => J ((r ≫ q) ≫ φ₂ κ))) (by
      rintro (κ | κ) <;> simp),
    sec_trans v r z (le_wchart_sum φ₁ φ₂ le_rfl le_rfl ⟨m₁, m₂⟩) (le x y m), ← hv _ r z x y m, e,
    gs_prodFn_sum H r z m, trF_sum, Sum.elim_comp_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_comp_inr,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sval, sval, hs i _ _ z x _ hx m₁, ht i _ _ z y _ hy m₂, Units.val_mul]
  ring

include H in

theorem eq_zero_of_sum (hL : L.IsLB) [IsAffine S] (hS : IsField Γ(S, ⊤)) [CompactSpace X₁] {n : ℕ}
    (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂))
    (ha : ∀ c : Fin n → Γ(S, ⊤), (∀ j, ∑ i, resTop _ (i₁.appTop.hom (c i)) * (a i).f j = 0) → c = 0)
    (h : ∀ (z : W) (J), Good L z J → ∑ i, sval (a i) p z J * sval (b i) q z J = 0) (i : Fin n) (k : K₂ → L.ι) :
    (b i).f k = 0 := by
  obtain ⟨P, _, U, j, aU, hU, cU⟩ := exists_finite_cover hL φ₁
  let a' : Fin n → ∀ x, Fn i₁ (U x) := fun i x => rs (hU x) ((a i).f (j x))
  have cst : ∀ (O : X₁.Opens) (z : X₁) (_ : z ∈ O) (c : Γ(S, ⊤)),
      gs (𝟙 X₁) z O ((i₁.appLE ⊤ O le_top).hom c) = gs (𝟙 X₁ ≫ i₁) z ⊤ c :=
    fun O z hz c => gs_appLE i₁ ⊤ O _ _ z hz c
  have li : LinearIndependent Γ(S, ⊤) a' := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    refine congrFun (ha c fun j' => fn_ext fun z hz => ?_)
    obtain ⟨x, hx⟩ := cU z
    have e : (∑ i, (i₁.appLE ⊤ (U x) le_top).hom (c i) * rs (hU x) ((a i).f (j x)) : Γ(X₁, U x)) = 0 :=
      (Finset.sum_apply x Finset.univ (fun i => c i • a' i)).symm.trans (congrFun hc x)
    have e' := congrArg (gs (𝟙 X₁) z (U x)) e
    rw [gs_sum' _ z _ hx, gs_zero' _ z _ hx] at e'
    rw [gs_sum' _ z _ hz, gs_zero' _ z _ hz, ← mul_zero (trF φ₁ ε₁ (𝟙 X₁) z j' (j x)).val, ← e', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (gs_mul _ z _ hz _ _).trans ((congrArg₂ (· * ·) (cst _ z hz (c i))
      (sec_trans (a i) (𝟙 X₁) z hz (hU x hx))).trans (Eq.trans ?_ (congrArg _ ((gs_mul _ z _ hx _ _).trans
        (congrArg₂ (· * ·) (cst _ z hx (c i)) (gs_res (𝟙 X₁) z (hU x) hx _)))).symm))
    exact mul_left_comm _ _ _
  refine fn_ext fun y hy => ?_
  obtain ⟨V, aV, hyV, hV⟩ := exists_affine_le hy
  have := eq_zero_of_linearIndependent hS a' li (C := Fn i₂ V) (fun i => rs hV ((b i).f k)) (fun x =>
    (prodFn_bijective H (aU x) aV).1 (fn_ext fun z hz => by
      choose J hJ using fun χ : W ⟶ B => exists_chart hL (χ z)
      refine (gs_prodFn_sum H (𝟙 W) z hz (fun i => a' i x) (fun i => rs hV ((b i).f k))).trans ?_
      rw [gs_prodFn_zero H (𝟙 W) z hz, Category.id_comp, Category.id_comp,
        ← mul_zero ((trF φ₁ ε₁ p z (j x) (fun κ => J (p ≫ φ₁ κ))).val *
          (trF φ₂ ε₂ q z k (fun κ => J (q ≫ φ₂ κ))).val), ← h z J hJ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine (congrArg₂ (· * ·)
        ((gs_res p z (hU x) hz.1 _).trans (sec_trans (a i) p z (hU x hz.1) (Good.mem hJ φ₁ p)))
        ((gs_res q z hV hz.2 _).trans (sec_trans (b i) q z (hV hz.2) (Good.mem hJ φ₂ q)))).trans ?_
      exact _root_.mul_mul_mul_comm _ _ _ _)) i
  exact (gs_res (𝟙 X₂) y hV hyV _).symm.trans ((congrArg (gs (𝟙 X₂) y V) this).trans
    ((gs_zero' _ y _ hyV).trans (gs_zero' _ y _ hy).symm))

theorem isSeparated_of_hom (i : Y ⟶ S) [IsAffine S] [IsSeparated i] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from i]; infer_instance⟩

theorem main : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Over (Spec (CommRingCat.of F))) [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁.left ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂.left ⟶ Z)) (ε₂ : K₂ → ℤ), (∀ v : LB.Sec (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim (fun k => (fst Y₁ Y₂).left ≫ φ₁ k) (fun k => (snd Y₁ Y₂).left ≫ φ₂ k)) (Sum.elim ε₁ ε₂)), ∃ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), ∀ (T : Scheme.{0}) (r : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J → sval v r z J = ∑ i, sval (a i) (r ≫ (fst Y₁ Y₂).left) z J * sval (b i) (r ≫ (snd Y₁ Y₂).left) z J) ∧ ∀ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), (∀ c : Fin n → F, (∀ j, ∑ i, resTop _ (scal Y₁.hom (c i)) * (a i).f j = 0) → c = 0) → (∀ (z : (Y₁ ⊗ Y₂).left) (J), Good L z J → ∑ i, sval (a i) (fst Y₁ Y₂).left z J * sval (b i) (snd Y₁ Y₂).left z J = 0) → ∀ i j, (b i).f j = 0 := by
  intro F _ Z L hL Y₁ Y₂ _ _ _ _ K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂
  have H : IsPullback (fst Y₁ Y₂).left (snd Y₁ Y₂).left Y₁.hom Y₂.hom := IsPullback.of_hasPullback _ _
  let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  have hS : IsField Γ(Spec (CommRingCat.of F), ⊤) := e.toMulEquiv.isField (Field.toIsField F)
  have := QuasiCompact.compactSpace_of_compactSpace Y₁.hom
  have := QuasiCompact.compactSpace_of_compactSpace Y₂.hom
  have := isSeparated_of_hom Y₁.hom
  have := isSeparated_of_hom Y₂.hom
  refine ⟨exists_sum H φ₁ ε₁ φ₂ ε₂ hL hS, fun n a b ha => eq_zero_of_sum H φ₁ ε₁ φ₂ ε₂ hL hS a b fun c hc => ?_⟩
  have := ha (fun i => e (c i)) fun j => by
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hc j)
    exact congrArg (fun t => resTop _ (Y₁.hom.appTop.hom t) * (a i).f j) (e.symm_apply_apply (c i))
  exact funext fun i => e.injective ((congrFun this i).trans (map_zero e).symm)

end GlobalTheory.SectionsProduct
