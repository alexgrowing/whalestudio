import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensRosati

section Transport

variable {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {K₁ : Type} [Fintype K₁] {pr : K₁ → (X' ⟶ X)} {e : K₁ → ℤ}
  {K : Type} [Fintype K]

theorem flat_le (φ' : K → (Y ⟶ X')) (jN : K → K₁ → M.ι) :
    LB.wchart (LB.LinComb M pr e) φ' jN ≤
      LB.wchart M (fun p : K × K₁ => φ' p.1 ≫ pr p.2) (fun p => jN p.1 p.2) := fun _ hy =>
  Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2

def unflatGen (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb M (fun p : K × K₁ => φ' p.1 ≫ pr p.2) (fun p => ε p.1 * e p.2))) :
    LB.Gen (LB.LinComb (LB.LinComb M pr e) φ' ε) :=
  ⟨fun jN : K → K₁ → M.ι => res (flat_le φ' jN) (t.s (fun p => jN p.1 p.2))⟩

theorem unflatGen_isGen (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb M (fun p : K × K₁ => φ' p.1 ≫ pr p.2) (fun p => ε p.1 * e p.2))) (ht : t.IsGen) :
    (unflatGen φ' ε t).IsGen := by
  refine isGen_of_gm _ fun y jN jN' h h' => ?_
  refine (gm_res (𝟙 Y) y _ h _).trans ((gen_trans ht (𝟙 Y) y (flat_le φ' jN h) (flat_le φ' jN' h')).trans
    (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y) y _ h' _).symm))
  unfold trF
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  refine Eq.trans ?_ (congrArg (· ^ ε a) (gm_linComb M pr e (𝟙 Y ≫ φ' a) y (jN a) (jN' a)
    (Set.mem_iInter.1 h a) (Set.mem_iInter.1 h' a))).symm
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp only
  rw [← zpow_mul, mul_comm (e i), Category.assoc]

theorem exists_gen_through (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr e)) (hw : w.IsGen)
    (φ' : K → (Y ⟶ X')) (ε : K → ℤ) {K₀ : Type} [Fintype K₀] {ψ : K₀ → (Y ⟶ X)} {δ : K₀ → ℤ}
    (hF : FormEq ψ δ (fun p : K × K₁ => φ' p.1 ≫ pr p.2) (fun p => ε p.1 * e p.2))
    (t : LB.Gen (LB.LinComb M ψ δ)) (ht : t.IsGen) : ∃ t' : LB.Gen (LB.LinComb M' φ' ε), t'.IsGen := by
  obtain ⟨u, hu, -⟩ := exists_gen hM hF t ht
  obtain ⟨t', ht', -⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_linComb (LB.isLB_linComb hM pr e) φ' ε)
    (LB.isLB_linComb hM' φ' ε) (isoInv (LB.linCombIso w φ' ε)) (isoInv_isGen (DVR.linCombIso_isGen w hw φ' ε))
    (unflatGen φ' ε u) (unflatGen_isGen φ' ε u hu)
  exact ⟨t', ht'⟩

end Transport

end GlobalTheory.TensRosati

namespace GlobalTheory.TensRosati

section Gens

variable {X Y : Scheme.{0}}

def gens (L : LB X) (Y : Scheme.{0}) : AddSubgroup (FreeAbelianGroup (Y ⟶ X)) where
  carrier := {s | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ s = ∑ k, ε k • FreeAbelianGroup.of (φ k)}
  zero_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L, fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    (Fintype.sum_empty _).symm⟩
  add_mem' := by
    rintro _ _ ⟨K, _, φ, ε, t, ht, rfl⟩ ⟨K', _, φ', ε', t', ht', rfl⟩
    refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', ?_⟩
    rw [Fintype.sum_sum_type]
    rfl
  neg_mem' := by
    rintro _ ⟨K, _, φ, ε, t, ht, rfl⟩
    refine ⟨K, inferInstance, φ, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, ?_⟩
    simp only [neg_smul, Finset.sum_neg_distrib]

theorem formEq_of_eq {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)}
    {ε' : K' → ℤ} (H : ∑ k, ε k • FreeAbelianGroup.of (φ k) = ∑ k, ε' k • FreeAbelianGroup.of (φ' k)) :
    FormEq φ ε φ' ε' := by
  intro U _ h
  have := congrArg (FreeAbelianGroup.lift (fun m => Additive.ofMul (h m))) H
  simp only [map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of] at this
  apply Additive.ofMul.injective
  simpa only [ofMul_prod, ofMul_zpow] using this

theorem exists_of_mem {L : LB X} {K' : Type} [Fintype K'] {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : ∑ k, ε' k • FreeAbelianGroup.of (φ' k) ∈ gens L Y) :
    ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
      t.IsGen ∧ FormEq φ ε φ' ε' := by
  obtain ⟨K, _, φ, ε, t, ht, hs⟩ := h
  exact ⟨K, inferInstance, φ, ε, t, ht, formEq_of_eq hs.symm⟩

end Gens

section Cube

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

def lam {T : Over S} (a b : T ⟶ G) : FreeAbelianGroup (T.left ⟶ G.left) :=
  FreeAbelianGroup.of (a * b).left - FreeAbelianGroup.of a.left - FreeAbelianGroup.of b.left +
    FreeAbelianGroup.of (1 : T ⟶ G).left

theorem cube_mem (L : RigLB G) (c : CubicalStr G L) {T : Over S} (a a' b : T ⟶ G) :
    lam (a * a') b - lam a b - lam a' b ∈ gens L.L T.left := by
  refine ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift a' b)).left,
    DVR.pullGen_isGen _ _ _ _ c.isGen _, ?_⟩
  have := prod_cub a a' b (U := Multiplicative (FreeAbelianGroup (T.left ⟶ G.left)))
    (fun m => Multiplicative.ofAdd (FreeAbelianGroup.of m))
  have e := congrArg Multiplicative.toAdd this
  simp only [toAdd_prod, toAdd_zpow, toAdd_mul, toAdd_inv, toAdd_ofAdd] at e
  rw [e, lam, lam, lam]
  abel

end Cube

end GlobalTheory.TensRosati

namespace GlobalTheory.TensRosati

section Alg

variable {Q : Type} [AddCommGroup Q] {r : ℕ}

def pair (L : Fin r → Fin r → Q) (M : Matrix (Fin r) (Fin r) ℤ) : Q := ∑ k, ∑ m, M k m • L k m

theorem pair_add (L : Fin r → Fin r → Q) (M N : Matrix (Fin r) (Fin r) ℤ) :
    pair L (M + N) = pair L M + pair L N := by
  simp only [pair, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem sum_left (L : Fin r → Fin r → Q) (W A : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, W i j • ∑ k, A i k • L k j = pair L (A.transpose * W) := by
  calc ∑ i, ∑ j, W i j • ∑ k, A i k • L k j = ∑ i, ∑ k, ∑ j, A i k • W i j • L k j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.smul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    _ = ∑ k, ∑ i, ∑ j, A i k • W i j • L k j := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.mul_apply, Finset.sum_smul]
        simp only [Matrix.transpose_apply, mul_smul]

theorem sum_left' (L : Fin r → Fin r → Q) (W A : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, W i j • ∑ k, A j k • L k i = pair L (A.transpose * W.transpose) := by
  calc ∑ i, ∑ j, W i j • ∑ k, A j k • L k i = ∑ i, ∑ k, ∑ j, A j k • W i j • L k i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.smul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    _ = ∑ k, ∑ i, ∑ j, A j k • W i j • L k i := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mul_apply, Finset.sum_smul]
        simp only [Matrix.transpose_apply, mul_smul]

theorem sum_right (L : Fin r → Fin r → Q) (W A : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, W i j • ∑ l, A j l • L i l = pair L (W * A) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_smul]
  simp only [mul_smul]

theorem sum_right' (L : Fin r → Fin r → Q) (W A : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, W i j • ∑ l, A i l • L j l = pair L (W.transpose * A) := by
  calc ∑ i, ∑ j, W i j • ∑ l, A i l • L j l = ∑ j, ∑ i, ∑ l, W i j • A i l • L j l := by
        rw [Finset.sum_comm]
        simp only [Finset.smul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Matrix.mul_apply, Finset.sum_smul]
        simp only [Matrix.transpose_apply, mul_smul]

theorem key_sum (L : Fin r → Fin r → Q) (W A A' : Matrix (Fin r) (Fin r) ℤ)
    (h : A.transpose * (W + W.transpose) = (W + W.transpose) * A') :
    ∑ i, ∑ j, W i j • (∑ k, A i k • L k j + ∑ k, A j k • L k i) =
      ∑ i, ∑ j, W i j • (∑ l, A' j l • L i l + ∑ l, A' i l • L j l) := by
  simp only [smul_add, Finset.sum_add_distrib]
  rw [sum_left, sum_left', sum_right, sum_right', ← pair_add, ← pair_add, ← Matrix.mul_add, ← Matrix.add_mul, h]

end Alg

end GlobalTheory.TensRosati

namespace GlobalTheory.TensRosati

section Quot

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S}
  (H : AddSubgroup (FreeAbelianGroup (T.left ⟶ G.left)))

def ell (a b : T ⟶ G) : FreeAbelianGroup (T.left ⟶ G.left) ⧸ H := QuotientAddGroup.mk' H (lam a b)

theorem lam_comm (a b : T ⟶ G) : lam a b = lam b a := by
  simp only [lam, mul_comm a b]
  abel

theorem ell_comm (a b : T ⟶ G) : ell H a b = ell H b a := by rw [ell, ell, lam_comm]

theorem ell_one (b : T ⟶ G) : ell H 1 b = 0 := by
  have e : lam (1 : T ⟶ G) b = 0 := by
    simp only [lam, _root_.one_mul]
    abel
  rw [ell, e, map_zero]

variable {H} (hc : ∀ a a' b : T ⟶ G, lam (a * a') b - lam a b - lam a' b ∈ H)
include hc

theorem ell_mul (a a' b : T ⟶ G) : ell H (a * a') b = ell H a b + ell H a' b := by
  have h := (QuotientAddGroup.eq_zero_iff _).2 (hc a a' b)
  rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_sub, sub_sub, sub_eq_zero] at h
  exact h

theorem ell_mul' (a b b' : T ⟶ G) : ell H a (b * b') = ell H a b + ell H a b' := by
  rw [ell_comm, ell_mul hc, ell_comm H b, ell_comm H b']

def ellHom (b : T ⟶ G) : Additive (T ⟶ G) →+ FreeAbelianGroup (T.left ⟶ G.left) ⧸ H where
  toFun a := ell H a.toMul b
  map_zero' := ell_one H b
  map_add' a a' := ell_mul hc a.toMul a'.toMul b

theorem ell_zpow (a b : T ⟶ G) (n : ℤ) : ell H (a ^ n) b = n • ell H a b :=
  map_zsmul (ellHom hc b) n (Additive.ofMul a)

theorem ell_prod {κ : Type} [Fintype κ] (f : κ → (T ⟶ G)) (n : κ → ℤ) (b : T ⟶ G) :
    ell H (∏ k, f k ^ n k) b = ∑ k, n k • ell H (f k) b := by
  have e := map_sum (ellHom hc b) (fun k => Additive.ofMul (f k ^ n k)) Finset.univ
  rw [← ofMul_prod] at e
  refine e.trans (Finset.sum_congr rfl fun k _ => ell_zpow hc _ _ _)

theorem ell_prod' {κ : Type} [Fintype κ] (a : T ⟶ G) (f : κ → (T ⟶ G)) (n : κ → ℤ) :
    ell H a (∏ k, f k ^ n k) = ∑ k, n k • ell H a (f k) := by
  rw [ell_comm, ell_prod hc]
  exact Finset.sum_congr rfl fun k _ => by rw [ell_comm]

theorem qf_mul {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (a b : Fin r → (T ⟶ G)) :
    ∑ i, ∑ j, W i j • ell H (a i * b i) (a j * b j) = ∑ i, ∑ j, W i j • ell H (a i) (a j) +
      ∑ i, ∑ j, W i j • ell H (b i) (b j) + ∑ i, ∑ j, W i j • (ell H (a i) (b j) + ell H (b i) (a j)) := by
  simp only [ell_mul hc, ell_mul' hc, smul_add, Finset.sum_add_distrib]
  abel

end Quot

end GlobalTheory.TensRosati

namespace GlobalTheory.TensRosati

section Tens

variable {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] {T : Over S}
  {r : ℕ} (pr : Fin r → (A' ⟶ A))

def qf (W : Matrix (Fin r) (Fin r) ℤ) (u : T ⟶ A') : FreeAbelianGroup (T.left ⟶ A.left) :=
  ∑ i, ∑ j, W i j • lam (u ≫ pr i) (u ≫ pr j)

theorem flat_eq (W : Matrix (Fin r) (Fin r) ℤ) (u : T ⟶ A') :
    ∑ k, tensε W k • FreeAbelianGroup.of (u.left ≫ tensφ pr k) = qf pr W u := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e0 : u.left ≫ (pr i * pr j).left = ((u ≫ pr i) * (u ≫ pr j)).left := by
    rw [← Over.comp_left, MonObj.comp_mul]
  have e3 : u.left ≫ (1 : A' ⟶ A).left = (1 : T ⟶ A).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  rw [Fin.sum_univ_four]
  simp only [tensε, tensφ, GlobalTheory.PolDeg.lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, e0, e3, mul_smul, lam, ← Over.comp_left]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, e3, ← Over.comp_left]
  simp only [smul_add, smul_sub, one_smul, neg_smul, smul_neg, mul_one, smul_comm (W i j) (-1 : ℤ)]
  abel

end Tens

end GlobalTheory.TensRosati

namespace GlobalTheory.TensRosati

section Total

variable {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] {T : Over S}
  {r : ℕ} (pr : Fin r → (A' ⟶ A))

theorem mk_qf (H : AddSubgroup (FreeAbelianGroup (T.left ⟶ A.left))) (W : Matrix (Fin r) (Fin r) ℤ) (u : T ⟶ A') :
    QuotientAddGroup.mk' H (qf pr W u) = ∑ i, ∑ j, W i j • ell H (u ≫ pr i) (u ≫ pr j) := by
  simp only [qf, map_sum, map_zsmul]
  rfl

theorem total_mem (hp : ∀ i, IsMonHom (pr i)) (H : AddSubgroup (FreeAbelianGroup (T.left ⟶ A.left)))
    (hc : ∀ a a' b : T ⟶ A, lam (a * a') b - lam a b - lam a' b ∈ H) (W Am Am' : Matrix (Fin r) (Fin r) ℤ)
    (h : Am.transpose * (W + W.transpose) = (W + W.transpose) * Am') (f g : A' ⟶ A')
    (hf : ∀ i, f ≫ pr i = ∏ j, pr j ^ Am i j) (hg : ∀ i, g ≫ pr i = ∏ j, pr j ^ Am' i j) (x y : T ⟶ A') :
    ∑ p : Fin 6 × ((Fin r × Fin r) × Fin 4), (rosatiε p.1 * tensε W p.2) •
      FreeAbelianGroup.of (((![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] : Fin 6 → (T ⟶ A')) p.1).left ≫
        tensφ pr p.2) ∈ H := by
  refine (QuotientAddGroup.eq_zero_iff _).1 ?_
  change QuotientAddGroup.mk' H _ = 0
  rw [Fintype.sum_prod_type]
  simp only [mul_smul, ← Finset.smul_sum, flat_eq, map_sum, map_zsmul, Fin.sum_univ_six]
  have v0 : (![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] : Fin 6 → (T ⟶ A')) 0 = (x ≫ f) * y := rfl
  have v1 : (![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] : Fin 6 → (T ⟶ A')) 1 = x ≫ f := rfl
  have v2 : (![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] : Fin 6 → (T ⟶ A')) 2 = y := rfl
  have v3 : (![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] : Fin 6 → (T ⟶ A')) 3 = x * (y ≫ g) := rfl
  have v4 : (![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] : Fin 6 → (T ⟶ A')) 4 = x := rfl
  have v5 : (![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] : Fin 6 → (T ⟶ A')) 5 = y ≫ g := rfl
  rw [v0, v1, v2, v3, v4, v5, show rosatiε 0 = 1 from rfl, show rosatiε 1 = -1 from rfl,
    show rosatiε 2 = -1 from rfl, show rosatiε 3 = -1 from rfl, show rosatiε 4 = 1 from rfl,
    show rosatiε 5 = 1 from rfl]
  simp only [map_add, map_zsmul, one_smul, neg_smul, map_neg, mk_qf]
  have hm : ∀ (a b : T ⟶ A') (i : Fin r), (a * b) ≫ pr i = (a ≫ pr i) * (b ≫ pr i) := fun a b i => by
    have := hp i
    exact MonObj.mul_comp a b (pr i)
  simp only [hm]
  have q1 := qf_mul hc W (fun i => (x ≫ f) ≫ pr i) (fun i => y ≫ pr i)
  have q2 := qf_mul hc W (fun i => x ≫ pr i) (fun i => (y ≫ g) ≫ pr i)
  rw [q1, q2]
  have hF : ∀ i, (x ≫ f) ≫ pr i = ∏ k, (x ≫ pr k) ^ Am i k := fun i => by
    rw [Category.assoc, hf, GlobalTheory.MatrixAction.comp_finsetProd]
    exact Finset.prod_congr rfl fun k _ => by rw [GrpObj.comp_zpow]
  have hG : ∀ i, (y ≫ g) ≫ pr i = ∏ k, (y ≫ pr k) ^ Am' i k := fun i => by
    rw [Category.assoc, hg, GlobalTheory.MatrixAction.comp_finsetProd]
    exact Finset.prod_congr rfl fun k _ => by rw [GrpObj.comp_zpow]
  have e1 : ∀ i j, ell H ((x ≫ f) ≫ pr i) (y ≫ pr j) = ∑ k, Am i k • ell H (x ≫ pr k) (y ≫ pr j) := fun i j => by
    rw [hF, ell_prod hc]
  have e2 : ∀ i j, ell H (y ≫ pr i) ((x ≫ f) ≫ pr j) = ∑ k, Am j k • ell H (x ≫ pr k) (y ≫ pr i) := fun i j => by
    rw [ell_comm, e1]
  have e3 : ∀ i j, ell H (x ≫ pr i) ((y ≫ g) ≫ pr j) = ∑ l, Am' j l • ell H (x ≫ pr i) (y ≫ pr l) := fun i j => by
    rw [hG, ell_prod' hc]
  have e4 : ∀ i j, ell H ((y ≫ g) ≫ pr i) (x ≫ pr j) = ∑ l, Am' i l • ell H (x ≫ pr j) (y ≫ pr l) := fun i j => by
    rw [ell_comm, e3]
  have hC := key_sum (fun k m => ell H (x ≫ pr k) (y ≫ pr m)) W Am Am' h
  simp only [e1, e2, e3, e4]
  rw [hC]
  abel

end Total

end GlobalTheory.TensRosati

theorem GlobalTheory.TensAct.rosatiAdj_matAct : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ),
    A.transpose * (W + W.transpose) = (W + W.transpose) * A' →
      RosatiAdj D'.P.A D'.P.L (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') := by
  intro R _ _ D D' r W T A A' h
  refine GlobalTheory.IntAct.rosatiAdj_of_points D'.P.isLB _ _ fun _ => ⟨⊤, trivial, fun Tt x y _ => ?_⟩
  obtain ⟨K, _, ψ, δ, t, ht, hF⟩ := GlobalTheory.TensRosati.exists_of_mem (GlobalTheory.TensRosati.total_mem T.pr T.pr_hom
    (GlobalTheory.TensRosati.gens D.P.L Tt.left)
    (fun a a' b => GlobalTheory.TensRosati.cube_mem ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ D.cub a a' b) W A A' h _ _
    (GlobalTheory.TensAct.matAct_pr T A) (GlobalTheory.TensAct.matAct_pr T A') x y)
  obtain ⟨t', ht'⟩ := GlobalTheory.TensRosati.exists_gen_through D.P.isLB D'.P.isLB T.w T.w_gen
    (fun a => ((![(x ≫ GlobalTheory.TensAct.matAct T A) * y, x ≫ GlobalTheory.TensAct.matAct T A, y,
      x * (y ≫ GlobalTheory.TensAct.matAct T A'), x, y ≫ GlobalTheory.TensAct.matAct T A'] : Fin 6 → (Tt ⟶ D'.P.A)) a).left)
    rosatiε hF t ht
  refine ⟨Fin 6, inferInstance, _, _, t', ht', fun V _ k => ?_⟩
  rw [Fin.prod_univ_six]
  show k ((x ≫ _) * y).left ^ (1 : ℤ) * k (x ≫ _).left ^ (-1 : ℤ) * k y.left ^ (-1 : ℤ) *
    k (x * (y ≫ _)).left ^ (-1 : ℤ) * k x.left ^ (1 : ℤ) * k (y ≫ _).left ^ (1 : ℤ) = _
  simp only [zpow_one, zpow_neg_one]
