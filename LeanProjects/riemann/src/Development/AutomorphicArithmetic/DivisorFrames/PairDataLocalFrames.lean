import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.DivisorFrames.ValuationRegularFunctionAtPoint
import Development.AutomorphicArithmetic.DivisorFrames.SideDataNonunitOnChart
import Development.AutomorphicArithmetic.DivisorFrames.SideDataGoodOnOpen
import Development.AutomorphicArithmetic.DivisorFrames.JoinedMatrixDetValuationOne
import Development.AutomorphicArithmetic.DivisorFrames.JoinedMatricesValuationCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicPointSpecializingStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

namespace UpperTheory.AdelicLocalFrames

section Val
variable {K : Type} [Field K] {Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral Z]

private theorem liftM {m n : Type} {x : Z} (M : Matrix m n Z.functionField) (h : ∀ k i, RegAt x (M k i)) :
    ∃ S : Matrix m n (Z.presheaf.stalk x), S.map (algebraMap _ Z.functionField) = M := by
  choose S hS using h
  exact ⟨Matrix.of S, Matrix.ext fun i k => hS i k⟩

private theorem map_val {m n : Type} (y : Sp K ⟶ Z) (S : Matrix m n (Z.presheaf.stalk (below y))) :
    (S.map (algebraMap _ Z.functionField)).map (TrueGeo.valAt y) = S.map (Scheme.stalkClosedPointTo y).hom :=
  Matrix.ext fun i k => Res.valAt_algebraMap y (S i k)

private theorem reg_det {n : ℕ} {x : Z} (M : Matrix (Fin n) (Fin n) Z.functionField) (h : ∀ k i, RegAt x (M k i)) :
    RegAt x M.det := by
  obtain ⟨S, rfl⟩ := liftM M h
  exact ⟨S.det, RingHom.map_det _ S⟩

private theorem val_det {n : ℕ} (y : Sp K ⟶ Z) (M : Matrix (Fin n) (Fin n) Z.functionField)
    (h : ∀ k i, RegAt (below y) (M k i)) : TrueGeo.valAt y M.det = (M.map (TrueGeo.valAt y)).det := by
  obtain ⟨S, rfl⟩ := liftM M h
  rw [map_val]
  refine Eq.trans ?_ (RingHom.map_det (Scheme.stalkClosedPointTo y).hom S)
  rw [← Res.valAt_algebraMap]
  exact congrArg _ (RingHom.map_det _ S).symm

private theorem val_one {n s : ℕ} (y : Sp K ⟶ Z) (M L : Matrix (Fin n) (Fin s) Z.functionField)
    (h : ∀ k i, RegAt (below y) (M k i)) (h' : ∀ k i, RegAt (below y) (L k i)) (e : Mᵀ * L = 1) :
    (M.map (TrueGeo.valAt y))ᵀ * L.map (TrueGeo.valAt y) = 1 := by
  obtain ⟨S, rfl⟩ := liftM M h
  obtain ⟨S', rfl⟩ := liftM L h'
  have e' : Sᵀ * S' = 1 := by
    apply Matrix.map_injective (IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField)
    show (Sᵀ * S').map _ = (1 : Matrix _ _ _).map _
    rw [Matrix.map_mul, Matrix.transpose_map, e, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [map_val, map_val, ← Matrix.transpose_map, ← Matrix.map_mul, e', Matrix.map_one _ (map_zero _) (map_one _)]

private theorem val_inv (y : Sp K ⟶ Z) {f : Z.functionField} (h : UnitAt (below y) f) :
    TrueGeo.valAt y f ≠ 0 ∧ TrueGeo.valAt y f⁻¹ = (TrueGeo.valAt y f)⁻¹ := by
  have h1 := Res.valAt_mul h.regAt h.inv.regAt
  rw [mul_inv_cancel₀ h.ne_zero, Res.valAt_one] at h1
  exact ⟨left_ne_zero_of_mul_eq_one h1.symm, eq_inv_of_mul_eq_one_right h1.symm⟩

private theorem exL {n s : ℕ} (M : Matrix (Fin n) (Fin s) Z.functionField) (σ : Fin s → Fin n)
    (hd : (M.submatrix σ id).det = 1) : ∃ L : Matrix (Fin n) (Fin s) Z.functionField, Mᵀ * L = 1 ∧
      ∀ x : Z, (∀ k i, RegAt x (M k i)) → ∀ k i, RegAt x (L k i) := by
  refine ⟨(1 : Matrix (Fin n) (Fin n) Z.functionField).submatrix id σ * (M.submatrix σ id)ᵀ.adjugate, ?_, fun x hx k i => ?_⟩
  · have : Mᵀ * (1 : Matrix (Fin n) (Fin n) Z.functionField).submatrix id σ = (M.submatrix σ id)ᵀ := by
      ext a b
      simp [Matrix.mul_apply, Matrix.one_apply]
    rw [← Matrix.mul_assoc, this, Matrix.mul_adjugate, Matrix.det_transpose, hd, one_smul]
  · obtain ⟨S, rfl⟩ := liftM M hx
    refine ⟨((1 : Matrix (Fin n) (Fin n) (Z.presheaf.stalk x)).submatrix id σ * (S.submatrix σ id)ᵀ.adjugate) k i, ?_⟩
    rw [← Matrix.map_apply (f := algebraMap (Z.presheaf.stalk x) Z.functionField), Matrix.map_mul,
      ← Matrix.submatrix_map, Matrix.map_one _ (map_zero _) (map_one _)]
    have := RingHom.map_adjugate (algebraMap (Z.presheaf.stalk x) Z.functionField) (S.submatrix σ id)ᵀ
    rw [RingHom.mapMatrix_apply] at this
    rw [this]
    rfl

end Val

private theorem joinM_map {A B : Type} {r s N : ℕ} (h : r + s = N) (f : A → B)
    (M₁ : Matrix (Fin N) (Fin r) A) (L : Matrix (Fin N) (Fin s) A) :
    (joinM h M₁ L).map f = joinM h (M₁.map f) (L.map f) := by
  ext a b
  simp only [RootFrame.joinM, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> rfl

private theorem joinM_all {A : Type} {r s N : ℕ} (h : r + s = N) (P : A → Prop)
    (M₁ : Matrix (Fin N) (Fin r) A) (L : Matrix (Fin N) (Fin s) A) (h1 : ∀ k i, P (M₁ k i)) (h2 : ∀ k i, P (L k i)) :
    ∀ k i, P (joinM h M₁ L k i) := by
  intro a b
  simp only [RootFrame.joinM, Matrix.of_apply]
  split_ifs
  · exact h1 _ _
  · exact h2 _ _

private theorem exC {A : Type} {r s N : ℕ} (h : r + s = N) (c₁ : Fin r → A) (c₂ : Fin s → A) :
    ∃ c : Fin N → A, (∀ i, c (lo h i) = c₁ i) ∧ ∀ j, c (hi h j) = c₂ j := by
  refine ⟨fun i => if hi : (i : ℕ) < r then c₁ ⟨i, hi⟩ else c₂ ⟨N - 1 - i, by omega⟩, fun i => ?_, fun j => ?_⟩
  · exact dif_pos (c := ((lo h i : Fin N) : ℕ) < r) i.2
  · have hj := j.2
    have h1 : ¬ ((hi h j : Fin N) : ℕ) < r := by simp only [hi]; omega
    refine (dif_neg h1).trans ?_
    congr 1
    apply Fin.ext
    simp only [hi]; omega

private theorem side {K : Type} [Field K] (w : AbsoluteValue K ℝ) {n r : ℕ} (X₀ X : Matrix (Fin n) (Fin r) K)
    (β₀ β : Matrix (Fin r) (Fin r) K) (g₀ g δ : Fin r → K) (hδ : ∀ i, δ i ≠ 0)
    (t₀ : β₀.BlockTriangular id) (t₁ : β.BlockTriangular id) (e₀ : ∀ i, β₀ i i * g₀ i = δ i) (e₁ : ∀ i, β i i * g i = δ i)
    (hb : ∀ k i, w ((X * β) k i) ≤ 1)
    (hc : ∀ u : Fin r → K, (∀ k, w ((X *ᵥ u) k) ≤ 1) → ∀ k, w ((X₀ *ᵥ u) k - (X *ᵥ u) k) < 1) :
    ∃ t : Matrix (Fin r) (Fin r) K, t.BlockTriangular id ∧ (∀ i, t i i * g i = g₀ i) ∧
      ∀ k i, w ((X * β) k i - (X₀ * β₀ * t) k i) < 1 := by
  have hne : ∀ i, β₀ i i ≠ 0 := fun i h0 => hδ i (by rw [← e₀, h0, zero_mul])
  have hu : IsUnit β₀.det := by
    rw [Matrix.det_of_upperTriangular t₀]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hne i).isUnit
  have hinv : β₀⁻¹.BlockTriangular id := by
    letI := β₀.invertibleOfIsUnitDet hu
    exact Matrix.blockTriangular_inv_of_blockTriangular t₀
  have ht : (β₀⁻¹ * β).BlockTriangular id := hinv.mul t₁
  have hm : β₀ * (β₀⁻¹ * β) = β := Matrix.mul_nonsing_inv_cancel_left _ _ hu
  refine ⟨β₀⁻¹ * β, ht, fun i => ?_, fun k i => ?_⟩
  · have := congrFun (congrFun hm i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at this
    · apply mul_left_cancel₀ (hne i)
      rw [← _root_.mul_assoc, this, e₁, e₀]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with hb | hb
      · rw [t₀ (i := i) (j := b) hb, zero_mul]
      · rw [ht (i := b) (j := i) hb, mul_zero]
    · simp
  · rw [Matrix.mul_assoc, hm, AbsoluteValue.map_sub]
    exact hc (fun j => β j i) (fun k => hb k i) k

section Geo
variable {F : Type} [Field F] [NumberField F] {Y : Var F}

private theorem nonarch {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) : IsNonarchimedean e.w := by
  have key : ∀ a b : AlgebraicClosure F, e.w a ≤ e.w b → e.w (a + b) ≤ e.w b := by
    intro a b hab
    by_cases h0 : b = 0
    · subst h0
      simpa using hab
    have hb0 : 0 < e.w b := e.w.pos h0
    have h1 : a / b ∈ e.O := (e.mem_O _).2 (by rw [map_div₀]; exact (div_le_one hb0).2 hab)
    have h2 : a / b + 1 ∈ e.O := add_mem h1 e.O.one_mem
    have h3 : a + b = (a / b + 1) * b := by field_simp
    rw [h3, map_mul]
    exact (mul_le_mul_of_nonneg_right ((e.mem_O _).1 h2) (e.w.nonneg _)).trans_eq (_root_.one_mul _)
  intro a b
  rcases le_total (e.w a) (e.w b) with h | h
  · exact (key a b h).trans (le_max_right _ _)
  · rw [add_comm]
    exact (key b a h).trans (le_max_left _ _)

private theorem notUnit {X : Scheme.{0}} {p : ℕ} {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) (hv : resP v = p)
    (yt : Sp e.O ⟶ X) : ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (yt (IsLocalRing.closedPoint e.O))) := by
  have hpv : ((p : 𝓞 F)) ∈ v.asIdeal := by
    have h0 : ((p : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := (ringChar.spec _ p).2 (by rw [← hv]; rfl)
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  have hwp : e.w (p : AlgebraicClosure F) < 1 := by
    have h := e.w_alg (p : F)
    rw [map_natCast] at h
    rw [h, ← map_natCast (algebraMap (𝓞 F) F) p, ← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem F v _).2 hpv
  have hpO : ¬ IsUnit ((p : ℕ) : e.O) := by
    intro hu
    obtain ⟨q, hq⟩ := hu.exists_right_inv
    have hq' : ((p : AlgebraicClosure F)) * (q : AlgebraicClosure F) = 1 := by
      have := congrArg (fun x : e.O => (x : AlgebraicClosure F)) hq
      simpa using this
    have hwq : e.w (q : AlgebraicClosure F) ≤ 1 := (e.mem_O _).1 q.2
    have hw1 := congrArg e.w hq'
    rw [map_mul, map_one] at hw1
    nlinarith [e.w.nonneg (q : AlgebraicClosure F), e.w.nonneg (p : AlgebraicClosure F)]
  intro h
  apply hpO
  have := h.map (Scheme.stalkClosedPointTo yt).hom
  rwa [map_natCast] at this

variable {V : Cover Y} {W : Y.X.Opens} {p : ℕ}

private theorem tst_mem {v e y z yt} (h : Tst V W p v e y z yt) {U : V.X.Opens} (hU : ⊤ ≤ yt ⁻¹ᵁ U) :
    V.j (below z) ∈ U := by
  change (z ≫ V.j) _ ∈ U
  rw [← h.2.2.2]
  exact hU (x := spMap e.O.subtype _) trivial

private theorem tst_pi {v e y z yt} (h : Tst V W p v e y z yt) : V.π (below z) = below y.1 := by
  rw [← h.2.2.1]; rfl

private theorem tst_reg {v e y z yt} (h : Tst V W p v e y z yt) {U : V.X.Opens} (hU : ⊤ ≤ yt ⁻¹ᵁ U)
    {g : V.X.functionField} (hg : ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → RegAt x g) :
    RegAt (below (z ≫ V.j)) g ∧ e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1 ∧
      (e.w (TrueGeo.valAt (z ≫ V.j) g) = 1 ↔ UnitAt (yt (IsLocalRing.closedPoint e.O)) g) :=
  UpperTheory.valuation_regular_function_at_point F Y V v e z yt h.2.2.2 g (hg _ (hU trivial) (notUnit e h.1 yt))

private theorem powInv {f : Y.X → Y.Fn} {l : PtFn Y} (h : PowRead V p f l) :
    PowRead V p (fun x => (f x)⁻¹) (fun v e y => -l v e y) := by
  obtain ⟨m, hm, h⟩ := h
  refine ⟨m, hm, fun x hx => ?_⟩
  obtain ⟨U, r, hxU, h1, h2⟩ := h x hx
  have key : ∀ a : Y.Fn, V.φ a⁻¹ ^ m * r⁻¹ = (V.φ a ^ m * r)⁻¹ := fun a => by
    rw [map_inv₀, inv_pow, mul_inv]
  refine ⟨U, r⁻¹, hxU, fun z hz => ?_, fun v e y z yt ht hU => ?_⟩
  · rw [key]
    exact (h1 z hz).inv
  · have u := h1 _ (tst_mem ht hU)
    rw [tst_pi ht] at u
    rw [key, (val_inv z u).2, map_inv₀, Real.log_inv, ← h2 v e y z yt ht hU, mul_neg]

private theorem goodOn_mono {U U' : V.X.Opens} (hU : U' ≤ U) {n r : ℕ}
    {X : Matrix (Fin n) (Fin r) V.G.functionField} {T : Y.X → Matrix (Fin r) (Fin r) Y.Fn} {σ : Fin r → Fin n}
    (h : GoodOn V W p U X T σ) : GoodOn V W p U' X T σ :=
  ⟨fun z hz => h.1 z (hU hz), fun v e y z yt ht hy => h.2 v e y z yt ht fun _ hq => hU (hy hq)⟩

private theorem sideT {J : Type} {U : J → V.X.Opens} {n r : ℕ}
    {X : J → Matrix (Fin n) (Fin r) V.G.functionField} {T : Y.X → Matrix (Fin r) (Fin r) Y.Fn}
    {f : Fin r → Y.X → Y.Fn} {l : Fin r → PtFn Y} (hS : SideData V W p U X T f l) {a₀ a : J} {U₀ U₁ : V.X.Opens}
    (h₀ : U₀ ≤ U a₀) (h₁ : U₁ ≤ U a) {M₀ M₁ c₀ c₁ σ₀ σ₁} (F₀ : FrameOn V W p U₀ (X a₀) T f l M₀ c₀ σ₀)
    (F₁ : FrameOn V W p U₁ (X a) T f l M₁ c₁ σ₁) {v e y z yt} (h : Tst V W p v e y z yt)
    (y₀ : ⊤ ≤ yt ⁻¹ᵁ U₀) (y₁ : ⊤ ≤ yt ⁻¹ᵁ U₁) :
    ∃ t : Matrix (Fin r) (Fin r) (AlgebraicClosure F), t.BlockTriangular id ∧
      (∀ i, t i i * TrueGeo.valAt z (V.φ (f i (below y.1)) * (c₁ i : V.G.functionField)) =
        TrueGeo.valAt z (V.φ (f i (below y.1)) * (c₀ i : V.G.functionField))) ∧
      (∀ i, e.w (TrueGeo.valAt z (V.φ (f i (below y.1)) * (c₁ i : V.G.functionField))) =
        e.w (TrueGeo.valAt z (V.φ (f i (below y.1)) * (c₀ i : V.G.functionField)))) ∧
      ∀ k i, e.w (M₁.map (TrueGeo.valAt (z ≫ V.j)) k i - (M₀.map (TrueGeo.valAt (z ≫ V.j)) * t) k i) < 1 := by
  obtain ⟨l₀, β₀, t₀, m₀, e₀⟩ := F₀.2.2.2 v e y z yt h y₀
  obtain ⟨l₁, β₁, t₁, m₁, e₁⟩ := F₁.2.2.2 v e y z yt h y₁
  obtain ⟨t, ht, hd, hc⟩ := side e.w _ _ β₀ β₁ _ _ _ (fun i => (val_inv y.1 ((hS.1 (below y.1)).2 i)).1) t₀ t₁ e₀ e₁
    (fun k i => by rw [← m₁]; exact (tst_reg h y₁ fun x hx hp => F₁.1 x hx hp k i).2.1)
    ((hS.2.2 v e y z yt h a fun _ hq => h₁ (y₁ hq)).2 a₀ fun _ hq => h₀ (y₀ hq))
  refine ⟨t, ht, hd, fun i => ?_, by rw [m₀, m₁]; exact hc⟩
  have u₀ := F₀.2.2.1 i _ (tst_mem h y₀)
  have u₁ := F₁.2.2.1 i _ (tst_mem h y₁)
  rw [tst_pi h] at u₀ u₁
  exact Real.log_injOn_pos (Set.mem_Ioi.2 (e.w.pos (val_inv z u₁).1)) (Set.mem_Ioi.2 (e.w.pos (val_inv z u₀).1))
    ((l₁ i).symm.trans (l₀ i))

private theorem atTest {J : Type} {U : J → V.X.Opens} {N r s : ℕ} (hN : r + s = N)
    {X : J → Matrix (Fin N) (Fin r) V.G.functionField} {T : Y.X → Matrix (Fin r) (Fin r) Y.Fn}
    {X' : J → Matrix (Fin N) (Fin s) V.G.functionField} {T' : Y.X → Matrix (Fin s) (Fin s) Y.Fn}
    (hO : Orth V W p U X T X' T') {f l f' l'} {a : J} {U₀ : V.X.Opens} (h₀ : U₀ ≤ U a) {M₁ c₁ σ₁ M₂ c₂ σ₂}
    (F₁ : FrameOn V W p U₀ (X a) T f l M₁ c₁ σ₁) (F₂ : FrameOn V W p U₀ (X' a) T' f' l' M₂ c₂ σ₂)
    {L : Matrix (Fin N) (Fin s) V.X.functionField} (hL : M₂ᵀ * L = 1)
    (rL : ∀ x : V.X, (∀ k i, RegAt x (M₂ k i)) → ∀ k i, RegAt x (L k i))
    {v e y z yt} (h : Tst V W p v e y z yt) (y₀ : ⊤ ≤ yt ⁻¹ᵁ U₀) :
    (∀ k i, e.w (M₁.map (TrueGeo.valAt (z ≫ V.j)) k i) ≤ 1) ∧ (∀ k i, e.w (M₂.map (TrueGeo.valAt (z ≫ V.j)) k i) ≤ 1) ∧
    (∀ k i, e.w (L.map (TrueGeo.valAt (z ≫ V.j)) k i) ≤ 1) ∧
    ((M₁.map (TrueGeo.valAt (z ≫ V.j))).submatrix σ₁ id).det = 1 ∧
    ((M₂.map (TrueGeo.valAt (z ≫ V.j))).submatrix σ₂ id).det = 1 ∧
    (M₂.map (TrueGeo.valAt (z ≫ V.j)))ᵀ * L.map (TrueGeo.valAt (z ≫ V.j)) = 1 ∧
    (∀ i j, e.w (((M₁.map (TrueGeo.valAt (z ≫ V.j)))ᵀ * M₂.map (TrueGeo.valAt (z ≫ V.j))) i j) < 1) ∧
    e.w (joinM hN (M₁.map (TrueGeo.valAt (z ≫ V.j))) (L.map (TrueGeo.valAt (z ≫ V.j)))).det = 1 ∧
    UnitAt (yt (IsLocalRing.closedPoint e.O)) (joinM hN M₁ L).det := by
  have r1 := fun k i => tst_reg h y₀ fun x hx hp => F₁.1 x hx hp k i
  have r2 := fun k i => tst_reg h y₀ fun x hx hp => F₂.1 x hx hp k i
  have r3 := fun k i => tst_reg h y₀ fun x hx hp => rL x (F₂.1 x hx hp) k i
  have d1 : ((M₁.map (TrueGeo.valAt (z ≫ V.j))).submatrix σ₁ id).det = 1 := by
    have := val_det (z ≫ V.j) (M₁.submatrix σ₁ id) fun k i => (r1 _ _).1
    rw [F₁.2.1, Res.valAt_one] at this
    exact this.symm
  have d2 : ((M₂.map (TrueGeo.valAt (z ≫ V.j))).submatrix σ₂ id).det = 1 := by
    have := val_det (z ≫ V.j) (M₂.submatrix σ₂ id) fun k i => (r2 _ _).1
    rw [F₂.2.1, Res.valAt_one] at this
    exact this.symm
  have d3 := val_one (z ≫ V.j) M₂ L (fun k i => (r2 k i).1) (fun k i => (r3 k i).1) hL
  have d4 : ∀ i j, e.w (((M₁.map (TrueGeo.valAt (z ≫ V.j)))ᵀ * M₂.map (TrueGeo.valAt (z ≫ V.j))) i j) < 1 := by
    intro i j
    obtain ⟨-, β₁, -, m₁, -⟩ := F₁.2.2.2 v e y z yt h y₀
    obtain ⟨-, β₂, -, m₂, -⟩ := F₂.2.2.2 v e y z yt h y₀
    have b1 : ∀ k, e.w (M₁.map (TrueGeo.valAt (z ≫ V.j)) k i) ≤ 1 := fun k => (r1 k i).2.1
    have b2 : ∀ k, e.w (M₂.map (TrueGeo.valAt (z ≫ V.j)) k j) ≤ 1 := fun k => (r2 k j).2.1
    rw [m₁] at b1
    rw [m₂] at b2
    rw [m₁, m₂]
    exact hO v e y z yt h a (fun _ hq => h₀ (y₀ hq)) (fun k => β₁ k i) (fun k => β₂ k j) b1 b2
  have d5 := UpperTheory.joined_matrix_det_valuation_one _ e.w (nonarch e) r s N hN _ _ _ σ₁ (fun k i => (r1 k i).2.1) (fun k i => (r2 k i).2.1)
    (fun k i => (r3 k i).2.1) d1 d3 d4
  refine ⟨fun k i => (r1 k i).2.1, fun k i => (r2 k i).2.1, fun k i => (r3 k i).2.1, d1, d2, d3, d4, d5, ?_⟩
  refine (tst_reg h y₀ fun x hx hp => reg_det _ (joinM_all hN _ _ _ (F₁.1 x hx hp) (rL x (F₂.1 x hx hp)))).2.2.1 ?_
  rw [val_det _ _ (joinM_all hN _ _ _ (fun k i => (r1 k i).1) fun k i => (r3 k i).1), joinM_map]
  exact d5

end Geo

end UpperTheory.AdelicLocalFrames

open UpperTheory.AdelicLocalFrames in
theorem UpperTheory.pair_data_local_frames :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (N : ℕ) (A : Fin N → Adl C Y) (p : ℕ), p.Prime → PairData A p → LocFrames A p := by
  intro F _ _ Y C N A p hp ⟨V, W, J, U, r, s, hN, X, T, X', T', hW, hcov, hpow, hS, hS', hO⟩
  have charts : ∀ x : {x : V.X // ¬ IsUnit (p : V.X.presheaf.stalk x)}, ∃ (a : J) (U₀ : V.X.Opens)
      (M₁ : Matrix (Fin N) (Fin r) V.X.functionField) (c₁ : Fin r → V.G.functionFieldˣ) (σ₁ : Fin r → Fin N)
      (M₂ : Matrix (Fin N) (Fin s) V.X.functionField) (c₂ : Fin s → V.G.functionFieldˣ) (σ₂ : Fin s → Fin N)
      (L : Matrix (Fin N) (Fin s) V.X.functionField) (c : Fin N → V.G.functionFieldˣ), x.1 ∈ U₀ ∧ U₀ ≤ U a ∧
      FrameOn V W p U₀ (X a) T (fun i => genAt (A (lo hN i)).D) (fun i => (A (lo hN i)).lg) M₁ c₁ σ₁ ∧
      FrameOn V W p U₀ (X' a) T' (fun i x => (genAt (A (hi hN i)).D x)⁻¹) (fun i v e y => -(A (hi hN i)).lg v e y)
        M₂ c₂ σ₂ ∧ M₂ᵀ * L = 1 ∧ (∀ x : V.X, (∀ k i, RegAt x (M₂ k i)) → ∀ k i, RegAt x (L k i)) ∧
      (∀ i, c (lo hN i) = c₁ i) ∧ ∀ j, c (hi hN j) = (c₂ j)⁻¹ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := hcov x hx
    obtain ⟨U₁, σ₁, x₁, l₁, g₁⟩ := UpperTheory.side_data_nonunit_on_chart F Y V W p J U N r X T _ _ hp hW hS (fun i => hpow _) a x ha hx
    obtain ⟨U₂, σ₂, x₂, l₂, g₂⟩ := UpperTheory.side_data_nonunit_on_chart F Y V W p J U N s X' T' _ _ hp hW hS' (fun i => powInv (hpow _)) a x ha hx
    have hl : U₁ ⊓ U₂ ≤ U a := inf_le_left.trans l₁
    obtain ⟨M₁, c₁, F₁⟩ := UpperTheory.side_data_good_on_open F Y V W p J U N r X T _ _ hp hW hS a (U₁ ⊓ U₂) σ₁ x ⟨x₁, x₂⟩ hl
      (goodOn_mono inf_le_left g₁)
    obtain ⟨M₂, c₂, F₂⟩ := UpperTheory.side_data_good_on_open F Y V W p J U N s X' T' _ _ hp hW hS' a (U₁ ⊓ U₂) σ₂ x ⟨x₁, x₂⟩ hl
      (goodOn_mono inf_le_right g₂)
    obtain ⟨L, hL, rL⟩ := exL M₂ σ₂ F₂.2.1
    obtain ⟨c, hc₁, hc₂⟩ := exC hN c₁ fun j => (c₂ j)⁻¹
    exact ⟨a, U₁ ⊓ U₂, M₁, c₁, σ₁, M₂, c₂, σ₂, L, c, ⟨x₁, x₂⟩, hl, F₁, F₂, hL, rL, hc₁, hc₂⟩
  choose a U₀ M₁ c₁ σ₁ M₂ c₂ σ₂ L c hx hle F₁ F₂ hL rL hc₁ hc₂ using charts
  have key : ∀ b j (g : Y.Fn), V.φ g * (c b (hi hN j) : V.G.functionField) = (V.φ g⁻¹ * c₂ b j)⁻¹ := fun b j g => by
    rw [hc₂, map_inv₀, mul_inv, inv_inv, Units.val_inv_eq_inv_val]
  have hunit : ∀ b i (z : V.G), V.j z ∈ U₀ b → UnitAt z (V.φ (genAt (A i).D (V.π z)) * c b i) := by
    intro b i z hz
    rcases lo_or_hi hN i with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [hc₁]
      exact (F₁ b).2.2.1 i z hz
    · rw [key]
      exact ((F₂ b).2.2.1 j z hz).inv
  refine ⟨V, W, _, U₀, fun b => joinM hN (M₁ b) (L b), c, hW, fun x h => ⟨⟨x, h⟩, hx _⟩, fun b x hb h => ⟨?_, ?_⟩,
    hunit, fun v hv e y hy z yt hz hyt => ?_⟩
  · exact joinM_all hN _ _ _ ((F₁ b).1 x hb h) (rL b x ((F₂ b).1 x hb h))
  · obtain ⟨v, e, y, z, yt, hv, hy, hz, hyt, hU, hsp⟩ := GlobalTheory.T.exists_algebraic_point_specializing F Y V p hp W hW (U₀ b) x hb h
    obtain ⟨U', m, hU'⟩ := (atTest hN hO (hle b) (F₁ b) (F₂ b) (hL b) (rL b) ⟨hv, hy, hz, hyt⟩ hU).2.2.2.2.2.2.2.2.exists_nhds
    exact hU' x (hsp.mem_open U'.isOpen m)
  have h : Tst V W p v e y z yt := ⟨hv, hy, hz, hyt⟩
  have hval : ∀ b, ⊤ ≤ yt ⁻¹ᵁ U₀ b → ∀ j,
      TrueGeo.valAt z (V.φ (genAt (A (hi hN j)).D (below y.1)) * (c b (hi hN j) : V.G.functionField)) =
      (TrueGeo.valAt z (V.φ (genAt (A (hi hN j)).D (below y.1))⁻¹ * (c₂ b j : V.G.functionField)))⁻¹ := by
    intro b hb j
    have u := (F₂ b).2.2.1 j _ (tst_mem h hb)
    rw [tst_pi h] at u
    rw [key, (val_inv z u).2]
  have hne : ∀ b, ⊤ ≤ yt ⁻¹ᵁ U₀ b → ∀ i,
      TrueGeo.valAt z (V.φ (genAt (A i).D (below y.1)) * (c b i : V.G.functionField)) ≠ 0 := by
    intro b hb i
    have u := hunit b i _ (tst_mem h hb)
    rw [tst_pi h] at u
    exact (val_inv z u).1
  by_cases hex : ∃ b₀, ⊤ ≤ yt ⁻¹ᵁ U₀ b₀
  swap
  · exact ⟨0, 0, fun b hb => (hex ⟨b, hb⟩).elim⟩
  obtain ⟨b₀, hb₀⟩ := hex
  refine ⟨joinM hN ((M₁ b₀).map (TrueGeo.valAt (z ≫ V.j))) ((L b₀).map (TrueGeo.valAt (z ≫ V.j))),
    fun i => TrueGeo.valAt z (V.φ (genAt (A i).D (below y.1)) * (c b₀ i : V.G.functionField)),
    fun b hb => ⟨fun i => ?_, ?_⟩⟩
  · rcases lo_or_hi hN i with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [hc₁]
      exact ((F₁ b).2.2.2 v e y z yt h hb).1 i
    · rw [hval b hb, map_inv₀, Real.log_inv, ← ((F₂ b).2.2.2 v e y z yt h hb).1 j, neg_neg]
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, -⟩ := atTest hN hO (hle b₀) (F₁ b₀) (F₂ b₀) (hL b₀) (rL b₀) h hb₀
  obtain ⟨q1, q2, q3, -, -, q6, -, q8, -⟩ := atTest hN hO (hle b) (F₁ b) (F₂ b) (hL b) (rL b) h hb
  obtain ⟨t, t1, t2, t3, t4⟩ := sideT hS (hle b₀) (hle b) (F₁ b₀) (F₁ b) h hb₀ hb
  obtain ⟨t', s1, s2, s3, s4⟩ := sideT hS' (hle b₀) (hle b) (F₂ b₀) (F₂ b) h hb₀ hb
  have n0 : ∀ j, TrueGeo.valAt z (V.φ (genAt (A (hi hN j)).D (below y.1))⁻¹ * (c₂ b₀ j : V.G.functionField)) ≠ 0 :=
    fun j => fun h0 => hne b₀ hb₀ _ (by rw [hval b₀ hb₀ j, h0, inv_zero])
  have s5 : ∀ j, e.w (t' j j) = 1 := fun j => by
    have := congrArg e.w (s2 j)
    rw [map_mul, s3 j] at this
    exact (mul_eq_right₀ (e.w.ne_zero (n0 j))).1 this
  obtain ⟨B, B1, B2, B3, B4, B5, B6⟩ := UpperTheory.joined_matrices_valuation_compare _ e.w (nonarch e) r s N hN _ _ _ _ _ _ _ _ t t'
    p1 p2 p3 q1 q2 q3 p4 p5 p6 q6 p7 p8 q8 t1 s1 s5 t4 s4
  refine ⟨B, B1, fun i => ?_, B2, B3, fun i k => ?_⟩
  · have pos := e.w.pos (hne b₀ hb₀ i)
    rcases lo_or_hi hN i with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · simp only [hc₁] at pos ⊢
      have e1 := t2 i
      have e2 := t3 i
      calc _ = e.w (B (lo hN i) (lo hN i) - t i i) * e.w (TrueGeo.valAt z (V.φ (genAt (A (lo hN i)).D (below y.1)) *
            (c₁ b i : V.G.functionField))) := by rw [← map_mul, sub_mul, e1]
        _ < _ := by rw [e2]; exact mul_lt_of_lt_one_left pos (B5 i)
    · simp only [hval b₀ hb₀, hval b hb] at pos ⊢
      have e1 := s2 j
      have e0 := n0 j
      have n1 : TrueGeo.valAt z (V.φ (genAt (A (hi hN j)).D (below y.1))⁻¹ * (c₂ b j : V.G.functionField)) ≠ 0 :=
        fun h0 => hne b hb _ (by rw [hval b hb j, h0, inv_zero])
      beta_reduce at e1
      generalize TrueGeo.valAt z (V.φ (genAt (A (hi hN j)).D (below y.1))⁻¹ * (c₂ b j : V.G.functionField)) = g at *
      generalize TrueGeo.valAt z (V.φ (genAt (A (hi hN j)).D (below y.1))⁻¹ * (c₂ b₀ j : V.G.functionField)) = g₀ at *
      have e3 : g⁻¹ = t' j j * g₀⁻¹ := by
        field_simp
        exact e1.symm.trans (_root_.mul_comm _ _)
      calc _ = e.w (B (hi hN j) (hi hN j) * t' j j - 1) * e.w g₀⁻¹ := by
            rw [← map_mul, e3]; congr 1; ring
        _ < _ := mul_lt_of_lt_one_left pos (B6 j)
  · have := B4 i k
    rw [← joinM_map hN _ (M₁ b)] at this
    exact this
