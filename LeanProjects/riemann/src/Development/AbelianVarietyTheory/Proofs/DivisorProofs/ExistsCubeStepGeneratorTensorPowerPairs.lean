import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeStep

section Gens

variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

def zpowGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℤ) :
    LB.Gen (LB.LinComb L φ (fun k => n * ε k)) where
  s := fun j => t.s j ^ n

theorem zpowGen_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    (zpowGen L φ ε t n).IsGen := fun i j => by
  refine ((map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_zpow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)
  exact (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ =>
    (zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _)))

theorem val_zpowGen {Z : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℤ)
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) : val (zpowGen L φ ε t n) r z J = val t r z J ^ n :=
  map_zpow _ _ _

theorem finProdGen_isGen {I : Type} [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) : (GeneratorPullback.finProdGen L φ ε t).IsGen := by
  intro (j : I × K → L.ι) (j' : I × K → L.ι)
  refine unit_ext fun y hy => ?_
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y (LB.wchart L (fun p : I × K => φ p.1 p.2) j) ((GeneratorPullback.finProdGen L φ ε t).s j) =
        ∏ i, gm (𝟙 Y) y (LB.wchart L (φ i) (fun k => j (i, k))) ((t i).s (fun k => j (i, k))) := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ => gm_res (𝟙 Y) y _ hj _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (𝟙 Y) y
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k)) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (i, k))

theorem val_finProdGen {I : Type} [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (GeneratorPullback.finProdGen L φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Gens

theorem prod_zpow_mul {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) (n : ℤ) :
    ∏ k, f k ^ (n * e k) = (∏ k, f k ^ e k) ^ n := by
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_mul, mul_comm]

theorem prod_finset_fin_two_ulift_expand {U : Type} [CommMonoid U] (f : ULift.{0} (Finset (Fin 2)) → U) :
    ∏ I, f I = f ⟨{0, 1}⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨∅⟩ := by
  refine (Fintype.prod_equiv Equiv.ulift f (fun I => f ⟨I⟩) (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  ac_rfl

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum.CubeStep

variable {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']

theorem groupSchemePartialSum_pair_both : psum B' (x2 B') {0, 1} = fst B' B' * snd B' B' := congrArg (fst B' B' * ·) (_root_.mul_one _)
theorem psum0 : psum B' (x2 B') {0} = fst B' B' := _root_.mul_one _
theorem psum1 : psum B' (x2 B') {1} = snd B' B' := _root_.mul_one _
theorem psumE : psum B' (x2 B') ∅ = 1 := rfl

theorem pair_eq {r : ℕ} (pr : Fin r → (B' ⟶ B)) (hpr : ∀ i, IsMonHom (pr i)) (w : ℤ) (i j : Fin r) {U : Type}
    [CommGroup U] (h : ((G2 B').left ⟶ B.left) → U) :
    ∏ k : thK.{0} ⊕ (thK.{0} ⊕ thK.{0}), h (Sum.elim
      (fun k => (lift (fst B' B' ≫ pr i) (lift (snd B' B' ≫ pr i) ((fst B' B' ≫ pr j) * (snd B' B' ≫ pr j)))).left ≫
        thφ B (x3 B) k)
      (Sum.elim (fun k => (lift (fst B' B' ≫ pr j) (lift (snd B' B' ≫ pr j) (fst B' B' ≫ pr i))).left ≫ thφ B (x3 B) k)
        (fun k => (lift (fst B' B' ≫ pr j) (lift (snd B' B' ≫ pr j) (snd B' B' ≫ pr i))).left ≫ thφ B (x3 B) k)) k) ^
      (-w * Sum.elim thε (Sum.elim thε thε) k) =
    (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr i) (snd B' B' ≫ pr j) k) ^ Oε k) ^ w *
    (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr j) (snd B' B' ≫ pr i) k) ^ Oε k) ^ w *
    (∏ k : Fin 4, ∏ I : ULift.{0} (Finset (Fin 2)),
      h ((psum B' (x2 B') I.down).left ≫ tensφ pr ((i, j), k)) ^ ((-1) ^ (2 - I.down.card) * Oε k)) ^ (-w) := by
  haveI := hpr i
  haveI := hpr j
  refine (prod_zpow_mul (U := U) _ (Sum.elim thε (Sum.elim thε thε)) (-w)).trans ?_
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [prod_cub, prod_cub, prod_cub]
  simp only [prod_finset_fin_two_ulift_expand, Fin.prod_univ_four, GlobalTheory.PolDeg.lamPts, tensφ, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, groupSchemePartialSum_pair_both, psum0, psum1, psumE]
  have q2 : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  have q0 : (-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card) = -1 := by decide
  have q1 : (-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card) = -1 := by decide
  have qe : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  simp only [q2, q0, q1, qe, ← Over.comp_left, MonObj.comp_mul, MonObj.mul_comp, MonObj.one_comp, MonObj.comp_one,
    _root_.mul_one, _root_.one_mul]
  generalize fst B' B' ≫ pr i = a
  generalize snd B' B' ≫ pr i = b
  generalize fst B' B' ≫ pr j = c
  generalize snd B' B' ≫ pr j = d
  rw [mul_comm (c * d) a, mul_comm c a, mul_comm d a, mul_comm (c * d) b, mul_comm d b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum.CubeStep

variable {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']

def lamV {T : Over S} {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) (u v : T ⟶ B) : U :=
  ∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts u v k) ^ Oε k

def pairGen {L : RigLB B} (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B))
    (p : Fin r × Fin r) :=
  zpowGen L.L _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ B (x3 B)) thε cb.t
      (lift (fst B' B' ≫ pr p.1) (lift (snd B' B' ≫ pr p.1) ((fst B' B' ≫ pr p.2) * (snd B' B' ≫ pr p.2)))).left)
    (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ B (x3 B)) thε cb.t (lift (fst B' B' ≫ pr p.2) (lift (snd B' B' ≫ pr p.2) (fst B' B' ≫ pr p.1))).left)
      (LB.pullGen L.L (thφ B (x3 B)) thε cb.t (lift (fst B' B' ≫ pr p.2) (lift (snd B' B' ≫ pr p.2) (snd B' B' ≫ pr p.1))).left)))
    (-W p.1 p.2)

theorem pairGen_isGen {L : RigLB B} (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (pr : Fin r → (B' ⟶ B)) (p : Fin r × Fin r) : (pairGen cb W pr p).IsGen :=
  zpowGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cb.isGen _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cb.isGen _) (DVR.pullGen_isGen _ _ _ _ cb.isGen _))) _

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum

open CubeStep in

theorem cube_step : ∀ {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : RigLB B) (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B)), (∀ i, IsMonHom (pr i)) → ∃ c : LB.Gen (LB.LinComb L.L (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2) (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2)) (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2)))), c.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ G2 B') (z : T.left) (J : (T.left ⟶ B.left) → L.L.ι), Good L.L z J → val c ρ.left z J = ∏ i, ∏ j, (cubV cb z J (ρ ≫ fst B' B' ≫ pr i) (ρ ≫ snd B' B' ≫ pr i) ((ρ ≫ fst B' B' ≫ pr j) * (ρ ≫ snd B' B' ≫ pr j)) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ fst B' B' ≫ pr i) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr i)) ^ (-W i j) := by
  intro S B B' _ _ _ _ L cb r W pr hpr
  have hfe : FormEq (fun q : (Fin r × Fin r) × (thK.{0} ⊕ (thK.{0} ⊕ thK.{0})) => Sum.elim
      (fun k => (lift (fst B' B' ≫ pr q.1.1) (lift (snd B' B' ≫ pr q.1.1)
        ((fst B' B' ≫ pr q.1.2) * (snd B' B' ≫ pr q.1.2)))).left ≫ thφ B (x3 B) k)
      (Sum.elim (fun k => (lift (fst B' B' ≫ pr q.1.2) (lift (snd B' B' ≫ pr q.1.2) (fst B' B' ≫ pr q.1.1))).left ≫
          thφ B (x3 B) k)
        (fun k => (lift (fst B' B' ≫ pr q.1.2) (lift (snd B' B' ≫ pr q.1.2) (snd B' B' ≫ pr q.1.1))).left ≫
          thφ B (x3 B) k)) q.2)
      (fun q => -W q.1.1 q.1.2 * Sum.elim thε (Sum.elim thε thε) q.2)
      (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2)
        (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2))
      (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)
        (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2))) := by
    intro U _ h
    have h1 : ∏ q : (Fin r × Fin r) × Fin 4,
        h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr q.1.1) (snd B' B' ≫ pr q.1.2) q.2) ^ ((W + W.transpose) q.1.1 q.1.2 * Oε q.2) =
        (∏ p : Fin r × Fin r, (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) k) ^ Oε k) ^
          W p.1 p.2) *
        ∏ p : Fin r × Fin r, (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.2) (snd B' B' ≫ pr p.1) k) ^ Oε k) ^
          W p.1 p.2 := by
      calc _ = ∏ p : Fin r × Fin r, ∏ k : Fin 4,
            h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) k) ^ ((W + W.transpose) p.1 p.2 * Oε k) :=
          Fintype.prod_prod_type _
        _ = ∏ p : Fin r × Fin r, (lamV h (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) ^ W p.1 p.2 *
            lamV h (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) ^ W p.2 p.1) :=
          Finset.prod_congr rfl fun p _ => by
            rw [prod_zpow_mul, Matrix.add_apply, Matrix.transpose_apply, zpow_add]; rfl
        _ = _ := by
          rw [Finset.prod_mul_distrib]
          exact congrArg _ (Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl)
    have h2 : ∏ q : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4),
        h ((psum B' (x2 B') q.1.down).left ≫ tensφ pr q.2) ^ (-((-1) ^ (2 - q.1.down.card) * tensε W q.2)) =
        ∏ p : Fin r × Fin r, (∏ k : Fin 4, ∏ I : ULift.{0} (Finset (Fin 2)),
          h ((psum B' (x2 B') I.down).left ≫ tensφ pr (p, k)) ^ ((-1) ^ (2 - I.down.card) * Oε k)) ^ (-W p.1 p.2) := by
      rw [Fintype.prod_prod_type, Finset.prod_comm, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [← zpow_mul]
      congr 1
      simp only [tensε]
      ring
    refine (Fintype.prod_prod_type _).trans (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) h1 h2)).symm)
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => pair_eq pr hpr (W p.1 p.2) p.1 p.2 h
  obtain ⟨t, ht, hv⟩ := exists_gen L.isLB hfe (GeneratorPullback.finProdGen L.L _ _ (pairGen cb W pr))
    (finProdGen_isGen _ _ _ _ (pairGen_isGen cb W pr))
  refine ⟨t, ht, fun T ρ z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_finProdGen _ _ _ (pairGen cb W pr) _ _ hJ).trans
    ((Fintype.prod_prod_type _).trans ?_))
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  dsimp only [pairGen]
  refine (val_zpowGen _ _ _ _ _ _ _ _).trans (congrArg (· ^ (-W i j)) ?_)
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub cb ρ hJ _ _ _) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_cub cb ρ hJ _ _ _) (val_cub cb ρ hJ _ _ _))))).trans ?_
  rw [MonObj.comp_mul, ← _root_.mul_assoc]

end GlobalTheory.Mum
