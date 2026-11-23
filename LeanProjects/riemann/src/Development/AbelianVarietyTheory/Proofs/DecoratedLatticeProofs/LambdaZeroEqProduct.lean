import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawProdLocalCellsDistinctPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevelComb
open GlobalTheory.FinPl (MxAt idAt)

variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

section Red
variable {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

def rho : 𝓞 D.host.E →+* G.k := (G.q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem rho_apply (z : 𝓞 D.host.E) : rho G z = (ofSplit G.q).pr (z : D.host.E) := rfl

theorem rho_int (z : 𝓞 D.host.E) : rho G z ∈ 𝒪[G.k] :=
  GlobalTheory.SplitCharCond.pr_int G.q (AddSubgroup.subset_closure ⟨1, fun v => by simp, z, rfl⟩)

theorem rho_lt {z : 𝓞 D.host.E} (hz : z ∈ PP.asIdeal) : valuation G.k (rho G z) < 1 := by
  by_cases h0 : z = 0
  · subst h0; simp
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  have h1 := (G.idem.2 z h0).1 hz
  rw [← G.q.sec_pr, ← G.q.int_iff] at h1
  change (G.q.pr.comp (incA D)) _ ∉ _ at h1
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le] at h1
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).1 h1

def out (y : Formalism.L2.DIV.kP PP) : 𝓞 D.host.E := Function.surjInv (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem mk_out (y : Formalism.L2.DIV.kP PP) : Ideal.Quotient.mk PP.asIdeal (out y) = y :=
  Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem rho_sub_lt {y : Formalism.L2.DIV.kP PP} {z : 𝓞 D.host.E} (hz : Ideal.Quotient.mk PP.asIdeal z = y) :
    valuation G.k (rho G (out y) - rho G z) < 1 := by
  rw [← map_sub]
  refine rho_lt G (Ideal.Quotient.eq.1 ?_)
  rw [mk_out, hz]

def pos : Fin D.R.k ⊕ Fin (G.s + 1) ≃ Fin D.R.r :=
  finSumFinEquiv.trans (finCongr (by have := G.hs; unfold Ranks.r; omega))

theorem pos_val (a : Fin D.R.k ⊕ Fin (G.s + 1)) : (pos G a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
  rcases a with a | a <;> rfl

def lift (g : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) G.k :=
  fun a b => rho G (out (g (pos G a) (pos G b)))

theorem lift_int (g : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) : IntM (lift G g) :=
  fun a b => rho_int G _

theorem lift_mul (g h : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    MaxM (lift G g * lift G h - lift G (g * h)) := by
  intro a b
  have e : (lift G g * lift G h - lift G (g * h)) a b =
      -(rho G (out ((g * h) (pos G a) (pos G b))) -
        rho G (∑ l, out (g (pos G a) l) * out (h l (pos G b)))) := by
    simp only [Matrix.sub_apply, Matrix.mul_apply, lift, map_sum, map_mul]
    rw [← Equiv.sum_comp (pos G) (fun l => rho G (out (g (pos G a) l)) * rho G (out (h l (pos G b))))]
    ring
  rw [e, Valuation.map_neg]
  refine rho_sub_lt G ?_
  simp only [map_sum, map_mul, mk_out, Matrix.mul_apply]

theorem lift_one : MaxM (lift G 1 - 1) := by
  intro a b
  have e : (lift G 1 - 1) a b = rho G (out ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) (pos G a) (pos G b))) -
      rho G (if a = b then 1 else 0) := by
    simp only [Matrix.sub_apply, lift, Matrix.one_apply]
    split_ifs <;> simp
  rw [e]
  refine rho_sub_lt G ?_
  simp only [Matrix.one_apply, (pos G).injective.eq_iff]
  split_ifs <;> simp

theorem red_iff (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    G.Red x g ↔ MaxM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) := by
  constructor
  · intro h a b
    have := h a b (pos G a) (pos G b) (pos_val G a) (pos_val G b) _ (mk_out _)
    simpa only [Matrix.sub_apply, lift, rho_apply] using this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = pos G a := Fin.ext (ha.trans (pos_val G a).symm)
    obtain rfl : b' = pos G b := Fin.ext (hb.trans (pos_val G b).symm)
    have e : (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E) =
        ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) a b + (rho G (out (g.val (pos G a) (pos G b))) - rho G z) := by
      simp only [Matrix.sub_apply, lift, rho_apply]; ring
    rw [e]
    exact Valuation.map_add_lt _ (h a b) (rho_sub_lt G hz)

theorem intM_J (x : G.S.P.J) : IntM (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val ∧
    IntM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹).val :=
  mem_KO.1 (G.S.P.le_KO x.2)

theorem red_one : G.Red 1 1 := by
  rw [red_iff]
  have := (lift_one G).neg
  simpa using this

theorem red_mul {x y : G.S.P.J} {g h : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)} (hx : G.Red x g) (hy : G.Red y h) :
    G.Red (x * y) (g * h) := by
  rw [red_iff] at hx hy ⊢
  have e : ((x * y : G.S.P.J) : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G (g * h).val =
      ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) * (y : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val +
      lift G g.val * ((y : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G h.val) +
      (lift G g.val * lift G h.val - lift G (g.val * h.val)) := by
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [e]
  exact ((hx.mul_intM (intM_J G y).1).add ((lift_int G _).mul_maxM hy)).add (lift_mul G _ _)

theorem red_inv {x : G.S.P.J} {g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)} (hx : G.Red x g) : G.Red x⁻¹ g⁻¹ := by
  rw [red_iff] at hx ⊢
  set X := (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k) with hX
  have e : ((x⁻¹ : G.S.P.J) : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G (g⁻¹).val =
      (X⁻¹).val * -((X.val - lift G g.val) * lift G (g⁻¹).val + (lift G g.val * lift G (g⁻¹).val - lift G (g.val * (g⁻¹).val)) +
        (lift G 1 - 1)) := by
    rw [Units.mul_inv]
    simp only [Subgroup.coe_inv, Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, Units.inv_mul,
      Matrix.one_mul, Matrix.mul_one]
    abel
  rw [e]
  exact (intM_J G x).2.mul_maxM (((hx.mul_intM (lift_int G _)).add (lift_mul G _ _)).add (lift_one G)).neg

theorem lam_congr {x x' : G.S.P.J} {g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)} (hx : G.Red x g) (hx' : G.Red x' g) :
    G.S.P.lam x = G.S.P.lam x' := by
  rw [red_iff] at hx hx'
  have h1 : (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹ * x' ∈ KOne G.k _ := by
    refine inv_mul_mem_KOne (G.S.P.le_KO x.2) ?_
    have e : (x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val =
        ((x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) -
          ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) := by abel
    rw [e, sub_eq_add_neg]
    exact hx'.add hx.neg
  have h2 := G.S.P.lam_eq_one (x⁻¹ * x') (by simpa using h1)
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2

end Red

section Grp
variable (G : ∀ PP : d.c.Pg, GAt d τ PP.1)

def grp : Subgroup (Formalism.L2.DIV.G0 d.c.Pg D.R.r) where
  carrier := {g | ∀ PP, ∃ x, (G PP).Red x (g PP)}
  one_mem' := fun PP => ⟨1, red_one _⟩
  mul_mem' := fun {_ _} hg hh PP =>
    let ⟨x, hx⟩ := hg PP
    let ⟨y, hy⟩ := hh PP
    ⟨x * y, red_mul _ hx hy⟩
  inv_mem' := fun {_} hg PP =>
    let ⟨x, hx⟩ := hg PP
    ⟨x⁻¹, red_inv _ hx⟩

def lam0 (g : grp G) : ℂˣ := ∏ PP, (G PP).S.P.lam (Classical.choose (g.2 PP))

theorem lambda_zero_eq_product (g : grp G) (x : ∀ PP, (G PP).S.P.J) (hx : ∀ PP, (G PP).Red (x PP) (g.1 PP)) :
    lam0 G g = ∏ PP, (G PP).S.P.lam (x PP) :=
  Finset.prod_congr rfl fun PP _ => lam_congr _ (Classical.choose_spec (g.2 PP)) (hx PP)

def chi : grp G →* ℂˣ where
  toFun := lam0 G
  map_one' := by
    rw [lambda_zero_eq_product G 1 (fun _ => 1) (fun PP => red_one _)]
    simp
  map_mul' g h := by
    rw [lambda_zero_eq_product G (g * h) (fun PP => Classical.choose (g.2 PP) * Classical.choose (h.2 PP))
      (fun PP => red_mul _ (Classical.choose_spec (g.2 PP)) (Classical.choose_spec (h.2 PP)))]
    simp only [map_mul, Finset.prod_mul_distrib]
    rfl

end Grp

end GlobalTheory.LevelComb

noncomputable section
namespace GlobalTheory.LevelComb
open GlobalTheory.FinPl (MxAt idAt)

section Comb
variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D}

theorem comb_single_zero (f : WO S T → ℂ) : comb ψ S T (Finsupp.single 0 1) f = f := by
  funext w
  simp [comb, Finsupp.support_single_ne_zero, heisO, symplOH, symplO, hO]

theorem exists_prod {ι : Type} (c : ι → (WO S T →₀ ℂ)) (P : WO S T → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hc : ∀ i, ∀ w ∈ (c i).support, P w) (l : List ι) :
    ∃ c' : WO S T →₀ ℂ, (∀ w ∈ c'.support, P w) ∧ ∀ f, comb ψ S T c' f = l.foldr (fun i f' => comb ψ S T (c i) f') f := by
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, fun w hw => ?_, fun f => comb_single_zero ψ f⟩
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hw
    exact hw ▸ h0
  | cons i l ih =>
    obtain ⟨c₁, h₁, e₁⟩ := ih
    obtain ⟨c'', hs, he⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (c i) c₁
    refine ⟨c'', fun w hw => ?_, fun f => ?_⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := hs w hw
      exact hadd x y (hc i x hx) (h₁ y hy)
    · rw [he, e₁, List.foldr_cons]

end Comb

variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

theorem v_mem_S {PP : d.c.Pg} (G : GAt d τ PP.1) : G.q.v ∈ d.c.S := by
  classical
  obtain ⟨ε, hε, hs⟩ := G.q.above
  have h := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP.1 _ ε G.idem hε hs
  unfold GlobalTheory.ChainOnto.Com.S
  exact Finset.mem_image.2 ⟨PP.1, PP.2, h⟩

theorem cg_supp {PP : d.c.Pg} (G : GAt d τ PP.1) {j : ℕ} (hj : j < D.R.m) :
    ∀ w ∈ (G.cg j).support, MxAt (· ∈ d.c.S) w := by
  have hs := G.hs
  have h : ∀ w ∈ (G.cg j).support, IsHalf (G.q.e + cA D G.q.e) w := by
    rcases (by omega : j + 1 ≤ G.s ∨ j = G.s ∨ j = G.s + 1) with h | rfl | rfl
    · exact (G.cg_mid j (G.s - (j + 1)) (by omega)).1
    · exact G.cg_pen.1
    · exact G.cg_top.1
  exact fun w hw a b => GlobalTheory.SeeSaw.CellProd.idAt_le (fun v (hv : v = G.q.v) => hv ▸ v_mem_S G)
    (GlobalTheory.SeeSaw.CellProd.mem_idAt G.q (h w hw a b))

end GlobalTheory.LevelComb

namespace GlobalTheory.LevelComb

theorem main : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) τ (G : ∀ PP : d.c.Pg, GAt d τ PP.1), d.c.Is → (∃ P : Formalism.L2.DIV.LevelP d.c.Pg D.R.r ℂ, (∀ g, g ∈ P.H ↔ ∀ PP, ∃ x, (G PP).Red x (g PP)) ∧ ∀ (g : P.H) (x : ∀ PP, (G PP).S.P.J), (∀ PP, (G PP).Red (x PP) (g.1 PP)) → P.chi g = ∏ PP, (G PP).S.P.lam (x PP)) ∧ ∃ cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ j, ∀ w ∈ (cG j).support, GlobalTheory.FinPl.MxAt (· ∈ d.c.S) w) ∧ ∀ j, j < D.R.m → ∀ f, IsThetaFunO d.c.ψ _ _ f → comb d.c.ψ _ _ (cG j) f = d.c.Pg.attach.toList.foldr (fun PP f' => comb d.c.ψ _ _ ((G PP).cg j) f') f := by
  intro D u d τ G _
  refine ⟨⟨⟨grp G, chi G⟩, fun g => Iff.rfl, fun g x hx => lambda_zero_eq_product G g x hx⟩, ?_⟩
  have key : ∀ j, ∃ c : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ w ∈ c.support, GlobalTheory.FinPl.MxAt (· ∈ d.c.S) w) ∧
      (j < D.R.m → ∀ f, comb d.c.ψ _ _ c f = d.c.Pg.attach.toList.foldr (fun PP f' => comb d.c.ψ _ _ ((G PP).cg j) f') f) := by
    intro j
    by_cases hj : j < D.R.m
    · obtain ⟨c, hc, he⟩ := exists_prod d.c.ψ (fun PP : d.c.Pg => (G PP).cg j) (GlobalTheory.FinPl.MxAt (· ∈ d.c.S))
        (fun a b => zero_mem _) (fun x y hx hy a b => add_mem (hx a b) (hy a b)) (fun PP => cg_supp (G PP) hj) d.c.Pg.attach.toList
      exact ⟨c, hc, fun _ => he⟩
    · exact ⟨0, by simp, fun h => absurd h hj⟩
  choose cG h1 h2 using key
  exact ⟨cG, h1, fun j hj f _ => h2 j hj f⟩

end GlobalTheory.LevelComb
