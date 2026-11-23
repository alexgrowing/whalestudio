import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompPartialSumPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.LamBridge

section Charts

variable {X X' Y : Scheme.{0}}

def cpTrans {A'' A' A : LB Y} (c₁ : ChartPull A'' A' (𝟙 Y)) (c₂ : ChartPull A' A (𝟙 Y)) : ChartPull A'' A (𝟙 Y) where
  idx i := c₂.idx (c₁.idx i)
  le i _ hy := c₂.le _ (c₁.le i hy)
  g y i j hi hj := (c₁.g y i j hi hj).trans (c₂.g y _ _ (c₁.le i hi) (c₁.le j hj))

def cpDiv {A' A B' B : LB Y} (a : ChartPull A' A (𝟙 Y)) (b : ChartPull B' B (𝟙 Y)) :
    ChartPull (LB.div B' A') (LB.div B A) (𝟙 Y) where
  idx p := (b.idx p.1, a.idx p.2)
  le p _ hy := ⟨b.le _ hy.1, a.le _ hy.2⟩
  g y p q hp hq := (gm_div A' B' (𝟙 Y) y p q ⟨hp, hq⟩).trans (Eq.trans (by rw [a.g y _ _ hp.2 hq.2, b.g y _ _ hp.1 hq.1])
    (gm_div A B (𝟙 Y) y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2)
      ⟨⟨b.le _ hp.1, a.le _ hp.2⟩, ⟨b.le _ hq.1, a.le _ hq.2⟩⟩).symm)

def cpEquiv (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (E : K' ≃ K) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (hφ : ∀ k, φ' k = φ (E k)) (hε : ∀ k, ε' k = ε (E k)) :
    ChartPull (LB.LinComb L φ' ε') (LB.LinComb L φ ε) (𝟙 Y) :=
  have le : ∀ j : K' → L.ι, LB.wchart L φ' j ≤ (𝟙 Y) ⁻¹ᵁ LB.wchart L φ (fun k => j (E.symm k)) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have h := Set.mem_iInter.1 hy (E.symm k)
      rw [hφ, E.apply_symm_apply] at h
      exact h
  { idx := fun j k => j (E.symm k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε' (𝟙 Y) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Fintype.prod_equiv E _ _ fun k => ?_
      rw [E.symm_apply_apply, hφ, hε] }

def cpFlat (L : LB X) {I K : Type} [Fintype I] [Fintype K] (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (σ : I → (Y ⟶ X'))
    (e : I → ℤ) : ChartPull (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb (LB.LinComb L ψ δ) σ e) (𝟙 Y) :=
  have le : ∀ j : I × K → L.ι, LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) j ≤
      (𝟙 Y) ⁻¹ᵁ LB.wchart (LB.LinComb L ψ δ) σ (fun i k => j (i, k)) :=
    fun _ _ hy => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  { idx := fun j i k => j (i, k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb (LB.LinComb L ψ δ) σ e (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => congrArg (· ^ e i)
        (gm_linComb L ψ δ (𝟙 Y ≫ σ i) y (fun k => j (i, k)) (fun k => j' (i, k))
          (Set.mem_iInter.1 (le j hj) i) (Set.mem_iInter.1 (le j' hj') i))).symm
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_mul, mul_comm (δ k), Category.assoc] }

end Charts

def e4 : Fin 4 ≃ ULift.{0} (Finset (Fin 2)) where
  toFun k := ⟨(![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k⟩
  invFun I := if I.down = {0, 1} then 0 else if I.down = {0} then 1 else if I.down = {1} then 2 else 3
  left_inv := by intro k; fin_cases k <;> rfl
  right_inv := by intro I; revert I; decide

theorem finFourEquivSubsetsFinTwo_down_eq (k : Fin 4) : (e4 k).down = (![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k := rfl

theorem mumfordSign_finFourEquivSubsetsFinTwo (k : Fin 4) : Oε k = (-1) ^ (2 - (e4 k).down.card) := by
  fin_cases k <;> decide

end GlobalTheory.Mum.LamBridge

namespace GlobalTheory.Mum.LamBridge

theorem lift_psum {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (u v : T ⟶ B) (I : Finset (Fin 2)) :
    (lift u v).left ≫ (psum B (x2 B) I).left = (psum B ![u, v] I).left := by
  rw [← Over.comp_left, comp_psum]
  congr 2
  funext k
  fin_cases k <;> simp [x2]

theorem mumfordBundleFourPoints_eq_lift_comp_partialSum {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (u v : T ⟶ B) (k : Fin 4) :
    lamPts u v k = (lift u v).left ≫ (psum B (x2 B) (e4 k).down).left := by
  rw [lift_psum]
  fin_cases k
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_01 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_0 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_1 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_e B u v).symm

end GlobalTheory.Mum.LamBridge

namespace GlobalTheory.Mum.LamBridge

theorem finFourEquivSubsetsFinTwo_symm_apply (I : ULift.{0} (Finset (Fin 2))) :
    (![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) (e4.symm I) = I.down := by
  rw [← finFourEquivSubsetsFinTwo_down_eq, Equiv.apply_symm_apply]

theorem exists_iso_tens : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (L₀ : LB B₀.left) (M : LB B.left), L₀.IsLB → M.IsLB → ∀ (β₂ : (G2 B₀).left ⟶ (G2 B).left) (wR : LB.Iso (abelian₂ B₀ L₀) ((abelian₂ B M).pull β₂)), wR.IsGen → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (Y : Over S₀) (x : Fin r → (Y ⟶ B₀)) (φ : (Fin r × Fin r) × Fin 4 → (Y.left ⟶ B.left)) (ε : (Fin r × Fin r) × Fin 4 → ℤ), (∀ k, φ k = (lift (x k.1.1) (x k.1.2)).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k.2)).left) → (∀ k, ε k = W k.1.1 k.1.2 * Oε k.2) → ∃ v : LB.Iso (LB.LinComb L₀ (tensφ x) (tensε W)) ((LB.LinComb M φ ε).pull (𝟙 Y.left)), v.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y.left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₀ : (Z ⟶ B₀.left) → L₀.ι), Good M z J → Good L₀ z J₀ → GlobalTheory.Mum.Two.isoVal v q z J J₀ = ∏ a, ∏ b, lamVal wR (q ≫ (lift (x a) (x b)).left) z J J₀ ^ W a b := by
  intro S₀ S B₀ _ _ B _ _ L₀ M hL₀ hM β₂ wR hw r W Y x φ ε hφ hε
  let σ : Fin r × Fin r → (Y.left ⟶ (G2 B₀).left) := fun ab => (lift (x ab.1) (x ab.2)).left
  let e : Fin r × Fin r → ℤ := fun ab => W ab.1 ab.2
  let v₁ := transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1) wR σ e
  have hv₁ : v₁.IsGen := isGen_transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1) hw σ e
  let cA : ChartPull (LB.LinComb L₀ (tensφ x) (tensε W)) (LB.LinComb (abelian₂ B₀ L₀) σ e) (𝟙 Y.left) :=
    cpTrans (cpEquiv L₀ (Equiv.prodCongr (Equiv.refl _) e4)
      (fun p : (Fin r × Fin r) × ULift.{0} (Finset (Fin 2)) => σ p.1 ≫ (psum B₀ (x2 B₀) p.2.down).left)
      (fun p => e p.1 * (-1) ^ (2 - p.2.down.card)) _ _
      (fun k => mumfordBundleFourPoints_eq_lift_comp_partialSum (x k.1.1) (x k.1.2) k.2)
      (fun k => by
        show W k.1.1 k.1.2 * Oε k.2 = W k.1.1 k.1.2 * (-1) ^ (2 - (e4 k.2).down.card)
        rw [mumfordSign_finFourEquivSubsetsFinTwo]))
      (cpFlat L₀ (fun I : ULift.{0} (Finset (Fin 2)) => (psum B₀ (x2 B₀) I.down).left)
        (fun I => (-1) ^ (2 - I.down.card)) σ e)
  let cB : ChartPull ((LB.LinComb M φ ε).pull (𝟙 Y.left))
      (LB.LinComb (abelian₂ B M) (fun p : (Fin r × Fin r) × PUnit => σ p.1 ≫ β₂) (fun p => e p.1 * 1)) (𝟙 Y.left) :=
    cpTrans (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (LB.LinComb M φ ε) (𝟙 Y.left) (𝟙 Y.left) rfl)
      (cpTrans (cpEquiv M (Equiv.prodCongr (Equiv.prodPUnit _).symm e4)
        (fun q : ((Fin r × Fin r) × PUnit) × ULift.{0} (Finset (Fin 2)) =>
          (σ q.1.1 ≫ β₂) ≫ (psum B (x2 B) q.2.down).left)
        (fun q => (e q.1.1 * 1) * (-1) ^ (2 - q.2.down.card)) φ ε
        (fun k => by rw [hφ k]; exact (Category.assoc _ _ _).symm)
        (fun k => by
          show ε k = (W k.1.1 k.1.2 * 1) * (-1) ^ (2 - (e4 k.2).down.card)
          rw [hε k, mumfordSign_finFourEquivSubsetsFinTwo, _root_.mul_one]))
        (cpFlat M (fun I : ULift.{0} (Finset (Fin 2)) => (psum B (x2 B) I.down).left)
          (fun I => (-1) ^ (2 - I.down.card)) (fun p : (Fin r × Fin r) × PUnit => σ p.1 ≫ β₂) (fun p => e p.1 * 1)))
  let c := cpDiv cA cB
  refine ⟨cGen c v₁, cGen_isGen c hv₁, fun Z q z J J₀ hJ hJ₀ => ?_⟩
  have hm : q z ∈ (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y.left)) (LB.LinComb L₀ (tensφ x) (tensε W))).U
      (fun _ k => J (q ≫ 𝟙 Y.left ≫ φ k), fun k => J₀ (q ≫ tensφ x k)) :=
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => hJ (q ≫ 𝟙 Y.left ≫ φ k),
      Set.mem_iInter.2 fun k => hJ₀ (q ≫ tensφ x k)⟩
  refine (gm_res q z _ hm _).trans ((gm_transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1)
    wR σ e q z (c.idx _) (c.le _ hm)).trans ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => congrArg (· ^ W a b) ?_
  unfold GlobalTheory.PolDeg.lamVal
  have key : ∀ P P', P = P' → gm (q ≫ σ (a, b)) z _ (wR.s P) = gm (q ≫ σ (a, b)) z _ (wR.s P') := by
    rintro _ _ rfl; rfl
  refine key _ _ (Prod.ext (funext fun _ => funext fun I => ?_) (funext fun I => ?_))
  · show J _ = J _
    congr 1
    show q ≫ 𝟙 Y.left ≫ φ ((a, b), e4.symm I) = _
    rw [hφ]
    simp only [finFourEquivSubsetsFinTwo_symm_apply, Category.assoc, Category.id_comp]
  · show J₀ _ = J₀ _
    congr 1
    show q ≫ lamPts (x a) (x b) (e4.symm I) = _
    rw [mumfordBundleFourPoints_eq_lift_comp_partialSum, e4.apply_symm_apply, Category.assoc]

end GlobalTheory.Mum.LamBridge
