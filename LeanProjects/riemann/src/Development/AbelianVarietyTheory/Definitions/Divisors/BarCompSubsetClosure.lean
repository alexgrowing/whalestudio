import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.TableDegreeElevenProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsResolProjSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinrankLineBundleSectionsFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LeastOrderBoundOfOrdTieTriv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.HermTools GlobalTheory.HilbertSamuel
open GlobalTheory.AllWt (Psi secZ exOf wtOf cuspOn latOn normOn petOn GoodOn suppOn LiesOn LiesOff)
open GlobalTheory.FlagMod (FlagCover FlagModel Frames frX ev)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.CompHt (hodgeWt uPrime)

theorem LatFrame.mem_span_iff {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] {Nm : (F →+* ℂ) → V → ℝ} {M : Submodule (𝓞 F) V} (f : LatFrame Nm M) (x : V) :
    f.b.equivFun x ∈ Submodule.span (𝓞 F) (Set.range f.w.col) ↔ x ∈ M := by
  have e : (fun k => ∑ j, f.w j k • f.b j) = (f.b.equivFun.symm.restrictScalars (𝓞 F)) ∘ f.w.col :=
    funext fun k => (f.b.equivFun_symm_apply _).symm
  conv_rhs => rw [← f.isFrame.span, e, Set.range_comp]
  rw [Submodule.span_image_linearEquiv, Submodule.mem_map_equiv]
  rfl

section Gaps

variable {N : ℕ}

def gap (v : Fin N → ℤ) (k : ℕ) : ℤ := if h : k + 1 < N then v ⟨k, by omega⟩ - v ⟨k + 1, h⟩ else 0

def ofGaps (a : ℕ) (g : ℕ → ℤ) : Fin N → ℤ := fun i => ∑ k ∈ Finset.range a, g k - ∑ k ∈ Finset.range i, g k

def floorGaps (a : ℕ) (n : ℤ) (v : Fin N → ℤ) : Fin N → ℤ := ofGaps a fun k => gap v k / n

def remGaps (a : ℕ) (n : ℤ) (v : Fin N → ℤ) : Fin N → ℤ := ofGaps a fun k => gap v k - n * (gap v k / n)

theorem gap_eq (v : Fin N → ℤ) {i j : Fin N} (h : (j : ℕ) = i + 1) : gap v i = v i - v j := by
  have := j.2
  rw [gap, dif_pos (by omega)]
  exact congrArg (fun x => v i - v x) (Fin.ext h.symm)

theorem ofGaps_anchor (g : ℕ → ℤ) (i : Fin N) : ofGaps i g i = 0 := sub_self _

theorem gap_ofGaps (a : ℕ) (g : ℕ → ℤ) {k : ℕ} (h : k + 1 < N) : gap (ofGaps a g : Fin N → ℤ) k = g k := by
  simp [gap, h, ofGaps, Finset.sum_range_succ]

theorem ofGaps_gap (v : Fin N → ℤ) (a i : Fin N) : ofGaps a (gap v) i = v i - v a := by
  have key : ∀ (n : ℕ) (h : n < N), ∑ k ∈ Finset.range n, gap v k = v ⟨0, by omega⟩ - v ⟨n, h⟩ := fun n => by
    induction n with
    | zero => simp
    | succ n ih => intro h; rw [Finset.sum_range_succ, ih (by omega), gap, dif_pos h]; ring
  rw [ofGaps, key a a.2, key i i.2]
  ring

theorem floorGaps_add_remGaps (n : ℤ) (v : Fin N → ℤ) (a i : Fin N) :
    n * floorGaps a n v i + remGaps a n v i = v i - v a := by
  rw [← ofGaps_gap]
  simp only [floorGaps, remGaps, ofGaps, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem gap_remGaps (a : ℕ) {n : ℤ} (hn : 0 < n) (v : Fin N → ℤ) (k : ℕ) :
    0 ≤ gap (remGaps a n v) k ∧ gap (remGaps a n v) k < n := by
  by_cases h : k + 1 < N
  · rw [remGaps, gap_ofGaps _ _ h, ← Int.emod_def]
    exact ⟨Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩
  · rw [gap, dif_neg h]; exact ⟨le_rfl, hn⟩

example : floorGaps 1 3 ![7, 0, -8] = ![2, 0, -2] ∧ remGaps 1 3 ![7, 0, -8] = ![1, 0, -2] ∧
    floorGaps 0 3 ![0, 1] = ![0, 1] := by decide

end Gaps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

structure WtPar (Dw : Datum H) where

  u : AllWt.Weight Dw

  c₀ : ℤ

  a : ℕ

  T : ℕ

namespace WtPar

variable (P : WtPar Dw)

def T₁ : ℤ := P.T + dimFlag Dw + 1

def uMinus : AllWt.Weight Dw := P.u - P.c₀ • hodgeWt Dw

def u₁ : AllWt.Weight Dw := fun τ => floorGaps P.a P.T₁ ((P.uMinus - FlagTan.kap Dw) τ)

def rem : AllWt.Weight Dw := fun τ => remGaps P.a P.T₁ ((P.uMinus - FlagTan.kap Dw) τ)

def u₂ : AllWt.Weight Dw := P.u₁ + P.rem

def uc : AllWt.Weight Dw := FlagTan.kap Dw + P.u₂ + dimFlag Dw • P.u₁

def u' : AllWt.Weight Dw := uPrime Dw P.u₁

def ub : AllWt.Weight Dw := fun τ => floorGaps P.a (dimFlag Dw + 3) (P.u₁ τ)

def wt (j : ℕ) : AllWt.Weight Dw := P.uc + j • P.u₁

theorem kap_add (j : ℕ) : FlagTan.kap Dw + (P.u₂ + dimFlag Dw • P.u₁ + j • P.u₁) = P.wt j := by
  rw [wt, uc]; abel

theorem u₁_add_wt (j : ℕ) : P.u₁ + P.wt j = P.wt (j + 1) := by
  rw [wt, wt, succ_nsmul]; abel

theorem gap_u₁ (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) :
    gap (P.u₁ τ) k = gap ((P.uMinus - FlagTan.kap Dw) τ) k / P.T₁ := gap_ofGaps _ _ h

theorem gap_rem (τ : Psi H) (k : ℕ) : 0 ≤ gap (P.rem τ) k ∧ gap (P.rem τ) k ≤ P.T + dimFlag Dw :=
  (gap_remGaps P.a (n := P.T₁) (by unfold T₁; positivity) _ k).imp_right Int.lt_add_one_iff.1

theorem gap_ub (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) :
    gap (P.ub τ) k = gap (P.u₁ τ) k / (dimFlag Dw + 3) := gap_ofGaps _ _ h

theorem anchored (τ : Psi H) {i : Fin (Dw.p + Dw.q)} (h : (i : ℕ) = P.a) :
    P.u₁ τ i = 0 ∧ P.rem τ i = 0 ∧ P.u₂ τ i = 0 ∧ P.ub τ i = 0 := by
  simp [u₂, u₁, rem, ub, floorGaps, remGaps, ← h, ofGaps_anchor]

theorem uMinus_eq (τ : Psi H) {a : Fin (Dw.p + Dw.q)} (h : (a : ℕ) = P.a) (i : Fin (Dw.p + Dw.q)) :
    P.uMinus τ i = P.wt P.T τ i + (P.uMinus τ a - FlagTan.kap Dw τ a) := by
  have := floorGaps_add_remGaps P.T₁ ((P.uMinus - FlagTan.kap Dw) τ) a i
  rw [h] at this
  simp only [wt, uc, u₂, u₁, rem, T₁, Pi.add_apply, Pi.smul_apply, Pi.sub_apply] at this ⊢
  simp only [nsmul_eq_mul]
  linear_combination -this

theorem gap_uMinus_sub_kap (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) : gap ((P.uMinus - FlagTan.kap Dw) τ) k =
    gap (P.u τ) k + if k + 1 = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2 := by
  simp only [gap, dif_pos h, uMinus, hodgeWt, CompHt.barWt, FlagTan.kap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> omega

end WtPar

theorem dimFlag_eq (Dw : Datum H) : CompHt.dimFlag Dw = dimFlag Dw := by
  classical
  rw [CompHt.dimFlag, Formalism.DegreeFormula.dimFl, dimFlag, Nat.choose_two_right, ← (FlagTan.isHalf_psiSet H).card]
  congr 1
  exact Fintype.card_of_subtype _ fun τ => by simp [psiSet]

structure TorFlag (Xo : Moduli Dw l) (c : Coeff l) where

  Y : Model Xo c (RingHom.id c.F)

  smooth : SmoothOfRelativeDimension Dw.dim Y.s

  snc : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (LogKS.boundary Y)

  logKS : LogKS.HasLogKS Y.t Y.s (LogKS.interior Y)

  flag : FlagModel Y

abbrev TorFlag.X (T : TorFlag Xo c) : FlagCover T.Y := T.flag.toFlagCover

section Flag

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)

abbrev flagStr : X.YY ⟶ Sp c.F := X.π ≫ Y.s

def flagOpen : X.YY.Opens := X.π ⁻¹ᵁ LogKS.interior Y

instance isOpenImmersion_inc : IsOpenImmersion X.inc := inferInstanceAs (IsOpenImmersion (pullback.fst X.π Y.j))

theorem opensRange_inc : X.inc.opensRange = flagOpen X := Scheme.Hom.opensRange_pullbackFst _ _

theorem top_le_inc : ⊤ ≤ X.inc ⁻¹ᵁ flagOpen X := fun z _ => (opensRange_inc X).le ⟨z, rfl⟩

instance isReduced_flag : IsReduced X.YY :=
  have : ∀ x : X.YY, _root_.IsReduced (X.YY.presheaf.stalk x) := fun x => have := (X.normal x).1; inferInstance
  isReduced_of_isReduced_stalk _

theorem dense_flagOpen : Dense (flagOpen X : Set X.YY) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (𝟙 _))
    infer_instance
  let r := pullback.fst (X.π ≫ Y.s) (spMap (RingHom.id c.F))
  refine (r.surjective.denseRange.dense_image r.continuous X.dense).mono ?_
  rintro _ ⟨z, ⟨x, hx⟩, rfl⟩
  refine ⟨x, ?_⟩
  rw [Model.j, Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, FlagMod.genMap,
    pullback.lift_fst]

theorem ptY_str {S : Type} [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) :
    X.ptY P ≫ flagStr X = spMap (algebraMap c.F S) := by
  rw [← Category.assoc, (X.lies_ptY P).1, Category.assoc, Model.j, Category.assoc, pullback.condition,
    ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, FlagMod.frX_snd]
  exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)

def commonLL : Common X.F.LL where
  isLB := X.F.isLB_LL
  J := X.F.J
  U := X.F.U
  cover y := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ y))
  idx _ k := k
  mem _ _ _ := Iff.rfl
  add a b y k k' h h' := Units.ext <| by
    rw [Units.val_mul]
    refine (val_tr _ y (memInf h h')).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (val_tr _ y (memInf h h')) (val_tr _ y (memInf h h'))).symm)
    exact (congrArg (fun u => ger y (memInf h h') u.val) (X.F.LL_add_g a b k k')).trans (map_mul _ _ _)

variable {X} {e : Ix Dw → ℤ}

def toSecO (m : H0 (flagStr X) (X.LL e) (flagOpen X)) : X.SecO e := toSec (H0.pull X.inc (top_le_inc X) m)

theorem coef_toSecO {S : Type} [CommRing S] (m : H0 (flagStr X) (X.LL e) (flagOpen X)) (k : X.F.J) (w : Sp S ⟶ X.Yo)
    (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k) (hO : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ flagOpen X) :
    FlagCover.coef (toSecO m) k w hz = H0.val (B := X.LL e) (w ≫ X.inc) k hO hz m :=
  (val_ofSec (p := X.inc ≫ flagStr X) (O := ⊤) w (pIdx (X.LL e) X.inc k) le_top (FlagCover.le_pull hz) _).symm.trans
    ((congrArg _ (ofSec_toSec _)).trans (val_pull _ _ _ _ _ _ hO hz m))

theorem bijective_toSecO : Function.Bijective (toSecO : H0 (flagStr X) (X.LL e) (flagOpen X) → X.SecO e) :=
  (Equiv.ofBijective _ bijective_ofSec_top).symm.bijective.comp
    ((isoOver_of_isOpenImmersion X.inc (opensRange_inc X).ge).bijective_pull (X.F.isLB_LL e) _ le_top)

variable (X e) in

def ruleOf : H0 (flagStr X) (X.LL e) (flagOpen X) →ₗ[c.F] secZ Xo c e where
  toFun m := ⟨FlagCover.toRule (toSecO m), FlagCover.toRule_mem_secZ _⟩
  map_add' m m' := Subtype.ext <| funext₂ fun p P => by
    refine (FlagCover.IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
    have hO := FlagMod.le_preimage_map (z := X.pt P') X.inc (top_le_inc X) le_top
    change ψ (FlagCover.val _ P + FlagCover.val _ P) = _
    rw [map_add, FlagCover.isVal_val _ P S' ψ P' hP k hz Q t hQ ht, FlagCover.isVal_val _ P S' ψ P' hP k hz Q t hQ ht,
      coef_toSecO _ _ _ _ hO, coef_toSecO _ _ _ _ hO, coef_toSecO _ _ _ _ hO, map_add, mul_add]
  map_smul' a m := Subtype.ext <| funext₂ fun p P => by
    refine (FlagCover.IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
    have hO := FlagMod.le_preimage_map (z := X.pt P') X.inc (top_le_inc X) le_top
    change ψ (a • FlagCover.val _ P) = _
    rw [map_smul, FlagCover.isVal_val _ P S' ψ P' hP k hz Q t hQ ht, coef_toSecO _ _ _ _ hO, coef_toSecO _ _ _ _ hO,
      Algebra.smul_def, mul_left_comm]
    refine congrArg (_ * ·) (Eq.symm ((val_fun_smul (B := X.LL e) _ k hO hz _ m).trans (congrArg (· * _) ?_)))
    exact evalPt_algX_of_eq _ _ (by rw [X.pt_inc]; exact ptY_str X P') _ _ a

theorem bijective_ruleOf : Function.Bijective (ruleOf X e) := by
  have := X.isReduced_Yo Function.injective_id fun x => ⟨x, 1, one_ne_zero, mul_one x⟩
  refine ⟨fun m m' h => bijective_toSecO.1 (FlagCover.toRule_injective (congrArg Subtype.val h)), fun f => ?_⟩
  obtain ⟨s, hs⟩ := FlagCover.exists_toRule_eq (X := X) f.2
  obtain ⟨m, rfl⟩ := bijective_toSecO.2 s
  exact ⟨m, Subtype.ext hs⟩

variable (X e) in

def secOf : secZ Xo c e ≃ₗ[c.F] H0 (flagStr X) (X.LL e) (flagOpen X) :=
  (LinearEquiv.ofBijective _ bijective_ruleOf).symm

open Classical in

theorem evR_eq_val_secOf {S : Type} [CommRing S] [Algebra c.F S] [_root_.IsReduced S] (f : secZ Xo c e)
    {P Q : FrPt Xo c S} {k : X.F.J} {z : Sp S ⟶ X.YY} {hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k} (hO : ⊤ ≤ z ⁻¹ᵁ flagOpen X)
    {t : Ix Dw → Sˣ} (hQ : X.F.ChartFr k z hz Q) (ht : FrBor t Q P) :
    evR Xo c f.1 P = (∏ ix, t ix ^ e ix).val * H0.val (B := X.LL e) z k hO hz (secOf X e f) := by
  obtain rfl : z = X.pt P ≫ X.inc := (FlagCover.eq_ptY (hQ.lies.frBor ht)).trans (X.pt_inc P).symm
  obtain ⟨m, rfl⟩ := (secOf X e).symm.surjective f
  rw [LinearEquiv.apply_symm_apply, ← coef_toSecO, ← FlagCover.val_eq _ hQ ht]
  exact FlagCover.evR_toRule_of_isReduced _ P

theorem exists_chartFr {S : Type} [CommRing S] (z : Sp S ⟶ X.YY) (hO : ⊤ ≤ z ⁻¹ᵁ flagOpen X) :
    ∃ _ : Algebra c.F S, ∀ (k : X.F.J) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k), ∃ Q : FrPt Xo c S, X.F.ChartFr k z hz Q := by
  have hr : Set.range z ⊆ Set.range X.inc := by
    rintro _ ⟨s, rfl⟩; exact (opensRange_inc X).ge (hO (Set.mem_univ s))
  obtain ⟨w, rfl⟩ : ∃ w, w ≫ X.inc = z := ⟨_, IsOpenImmersion.lift_fac X.inc z hr⟩
  obtain ⟨a, h⟩ := FlagCover.exists_alg_chartFr w
  exact ⟨a, fun k hz => (h k hz).imp fun _ => And.left⟩

theorem secOf_mul {e₁ e₂ : Ix Dw → ℤ} (h : e₁ + e₂ = e) (f₁ : secZ Xo c e₁) (f₂ : secZ Xo c e₂) (f : secZ Xo c e)
    (hf : f.1 = f₁.1 * f₂.1) : secOf X e f = ((commonLL X).addChart h).mul (secOf X e₁ f₁) (secOf X e₂ f₂) := by
  refine LB.sec_ext fun k => FlagMod.ext_ev_field fun L _ z hz => ?_
  have hO := FlagMod.le_preimage_mono inf_le_left hz
  have hk := FlagMod.le_preimage_mono inf_le_right hz
  obtain ⟨_, hQ⟩ := exists_chartFr z hO
  obtain ⟨Q, hQ⟩ := hQ k hk
  have hb := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).1 Q
  have a := evR_eq_val_secOf f hO hQ hb
  have a₁ := evR_eq_val_secOf f₁ hO hQ hb
  have a₂ := evR_eq_val_secOf f₂ hO hQ hb
  simp only [Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one, one_mul] at a a₁ a₂
  refine a.symm.trans (Eq.trans ?_ (((commonLL X).addChart h).val_mul _ _ k z hO hk hk hk).symm)
  rw [hf]
  exact (evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) _ _ Q).trans
    (congrArg₂ (· * ·) a₁ a₂)

end Flag

section Component

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

variable (Y) in

def barComp : Y.X.Opens := ⟨(closure (Y.j '' (Z : Set (Xo.XF c))ᶜ))ᶜ, isClosed_closure.isOpen_compl⟩

theorem j_mem_barComp (x : Xo.XF c) : Y.j x ∈ barComp Y Z ↔ x ∈ (Z : Set (Xo.XF c)) := by
  have h := Y.j.isOpenEmbedding.isOpenMap.preimage_closure_image Y.j.isOpenEmbedding.injective Y.j.continuous _
    (TrivOrderTieCompare.isClopen_comp Z).compl.isClosed
  exact (not_congr (Set.ext_iff.1 h x)).trans not_not

theorem barComp_subset_closure : (barComp Y Z : Set Y.X) ⊆ closure (Y.j '' (Z : Set (Xo.XF c))) := fun y hy => by
  have h : y ∈ closure (Set.range Y.j) := LogKS.dense_interior Y y
  rw [← Set.image_univ, ← Set.union_compl_self (Z : Set (Xo.XF c)), Set.image_union, closure_union] at h
  exact h.resolve_right hy

abbrev Y₀ : Scheme.{0} := (X.π ⁻¹ᵁ barComp Y Z).toScheme

abbrev inc₀ : Y₀ X Z ⟶ X.YY := (X.π ⁻¹ᵁ barComp Y Z).ι

abbrev str₀ : Y₀ X Z ⟶ Sp c.F := inc₀ X Z ≫ flagStr X

def U₀ : (Y₀ X Z).Opens := inc₀ X Z ⁻¹ᵁ flagOpen X

def bd₀ : Closeds (Y₀ X Z) := (U₀ X Z).compl

instance isReduced_Y₀ : IsReduced (Y₀ X Z) := isReduced_of_isOpenImmersion (inc₀ X Z)

theorem dense_U₀ : Dense (U₀ X Z : Set (Y₀ X Z)) :=
  (dense_flagOpen X).preimage (inc₀ X Z).isOpenEmbedding.isOpenMap

theorem ptY_le_iff {S : Type} [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) :
    ⊤ ≤ X.ptY P ⁻¹ᵁ (X.π ⁻¹ᵁ barComp Y Z) ↔ LiesOn Z P := by
  rw [← Scheme.Hom.comp_preimage, (X.lies_ptY P).1]
  exact ⟨fun h s => (j_mem_barComp Z _).1 (h (Set.mem_univ s)), fun h s _ => (j_mem_barComp Z _).2 (h s)⟩

def IsVariety₀ : Prop :=
  SmoothOfRelativeDimension (dimFlag Dw) (str₀ X Z) ∧ IsProjOver (str₀ X Z) ∧ GeometricallyConnected (str₀ X Z)

abbrev LL₀ (e : Ix Dw → ℤ) : LB (Y₀ X Z) := (X.LL e).pull (inc₀ X Z)

abbrev L₀ (la : AllWt.Weight Dw) : LB (Y₀ X Z) := LL₀ X Z (exOf Dw la 0)

theorem L₀_eq (la : AllWt.Weight Dw) : L₀ X Z la = (X.Llam la).pull (inc₀ X Z) := rfl

theorem exOf_add_zero (a b : AllWt.Weight Dw) : exOf Dw (a + b) 0 = exOf Dw a 0 + exOf Dw b 0 :=
  AllWt.exOf_add a b 0 0

def common₀ : Common (L₀ X Z) := ((commonLL X).pull (inc₀ X Z)).comap (fun la => exOf Dw la 0) exOf_add_zero

theorem isLB_L₀ (la : AllWt.Weight Dw) : (L₀ X Z la).IsLB := (common₀ X Z).isLB la

def sec₀ (e : Ix Dw → ℤ) : secZ Xo c e →ₗ[c.F] H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z) :=
  H0.pull (inc₀ X Z) le_rfl ∘ₗ (secOf X e).toLinearMap

theorem eq_zero_of_sec₀ {e : Ix Dw → ℤ} {f : secZ Xo c e} (hf : f.1 ∈ suppOn Z) (h : sec₀ X Z e f = 0) : f = 0 := by
  refine (secOf X e).map_eq_zero_iff.1 (LB.sec_ext fun k => FlagMod.ext_ev_field fun L _ z hz => ?_)
  have hO := FlagMod.le_preimage_mono inf_le_left hz
  have hk := FlagMod.le_preimage_mono inf_le_right hz
  refine Eq.trans (b := 0) ?_ (map_zero _).symm
  obtain ⟨_, hQ⟩ := exists_chartFr z hO
  obtain ⟨Q, hQ⟩ := hQ k hk
  by_cases hZ : LiesOn Z Q
  · have hY := (ptY_le_iff X Z Q).2 hZ
    rw [← FlagCover.eq_ptY hQ.lies] at hY
    have hr : Set.range z ⊆ Set.range (inc₀ X Z) := by
      rintro _ ⟨s, rfl⟩; exact ⟨⟨_, hY (Set.mem_univ s)⟩, rfl⟩
    obtain ⟨w, rfl⟩ : ∃ w, w ≫ inc₀ X Z = z := ⟨_, IsOpenImmersion.lift_fac _ z hr⟩
    exact (H0.val_pull (O := flagOpen X) (W := U₀ X Z) (inc₀ X Z) le_rfl w (pIdx (X.LL e) _ k) hO (fun s hs => mem_pIdx.2 (hk hs)) hO hk _).symm.trans
      ((congrArg _ h).trans (map_zero _))
  · have a := evR_eq_val_secOf f hO hQ ((GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).1 Q)
    simp only [Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one, one_mul] at a
    exact a.symm.trans (hf L Q ((AllWt.liesOff_iff Z Q).2 hZ))

theorem sec₀_mul {e₁ e₂ e : Ix Dw → ℤ} (h : e₁ + e₂ = e) (f₁ : secZ Xo c e₁) (f₂ : secZ Xo c e₂) (f : secZ Xo c e)
    (hf : f.1 = f₁.1 * f₂.1) : sec₀ X Z e f =
      (((commonLL X).addChart h).pull (inc₀ X Z)).mul (sec₀ X Z e₁ f₁) (sec₀ X Z e₂ f₂) :=
  (congrArg (H0.pull (inc₀ X Z) (le_refl (U₀ X Z))) (secOf_mul h f₁ f₂ f hf)).trans
    (((commonLL X).addChart h).pull_mul (inc₀ X Z) (le_refl (U₀ X Z)) (secOf X e₁ f₁) (secOf X e₂ f₂))

def vanBd (la : AllWt.Weight Dw) : Submodule c.F (H0 (str₀ X Z) (L₀ X Z la) ⊤) where
  carrier := {s | ∀ y ∈ bd₀ X Z, ∀ i hi, germ i y (memTop y) hi s ∈ IsLocalRing.maximalIdeal _}
  zero_mem' y _ i hi := by rw [map_zero]; exact zero_mem _
  add_mem' hs ht y hy i hi := by rw [map_add]; exact add_mem (hs y hy i hi) (ht y hy i hi)
  smul_mem' a s hs y hy i hi := by rw [germ_smul]; exact Ideal.mul_mem_left _ _ (hs y hy i hi)

theorem mem_vanBd {la : AllWt.Weight Dw} {s : H0 (str₀ X Z) (L₀ X Z la) ⊤} :
    s ∈ vanBd X Z la ↔ ∀ y ∈ bd₀ X Z, y ∉ nonzeroLocus (toSec s) := by
  refine forall₂_congr fun y _ => ⟨fun h hy => ?_, fun h i hi hu => h ((isUnit_ger_iff _ hi).1 (by rwa [ger_toSec]))⟩
  obtain ⟨i, hi⟩ := exists_chart (isLB_L₀ X Z la) y
  exact h i hi (by rw [← ger_toSec]; exact (isUnit_ger_iff _ hi).2 hy)

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

abbrev Cusp (la : AllWt.Weight Dw) : Submodule c.F (Rul Xo c) := cuspOn U Z (wtOf Dw la 0)

theorem cusp_le_secZ (la : AllWt.Weight Dw) : Cusp Z U la ≤ secZ Xo c (exOf Dw la 0) :=
  (AllWt.cuspOn_le U Z _).trans (AllWt.cuspW_le_secZ _)

def cuspSec (la : AllWt.Weight Dw) : Cusp Z U la →ₗ[c.F] H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z) :=
  sec₀ X Z _ ∘ₗ Submodule.inclusion (cusp_le_secZ Z U la)

theorem cuspSec_injective (la : AllWt.Weight Dw) : Function.Injective (cuspSec X Z U la) :=
  (injective_iff_map_eq_zero _).2 fun f h =>
    Submodule.inclusion_injective (cusp_le_secZ Z U la) ((eq_zero_of_sec₀ X Z f.2.2 h).trans (map_zero _).symm)

def space (la : AllWt.Weight Dw) : Submodule c.F (H0 (str₀ X Z) (L₀ X Z la) ⊤) :=
  (LinearMap.range (cuspSec X Z U la)).comap (restr le_top)

def Extends (la : AllWt.Weight Dw) : Prop :=
  ∀ f : Cusp Z U la, ∃ s ∈ vanBd X Z la, restr le_top s = cuspSec X Z U la f

abbrev baseId (la : AllWt.Weight Dw) : (Y₀ X Z).IdealSheafData := baseIdeal (isLB_L₀ X Z la) (space X Z U la)

abbrev FreeOnOpen (la : AllWt.Weight Dw) : Prop := NoBase (isLB_L₀ X Z la) (space X Z U la) (U₀ X Z)

def ofSpace (la : AllWt.Weight Dw) : space X Z U la →ₗ[c.F] Cusp Z U la :=
  (LinearEquiv.ofInjective _ (cuspSec_injective X Z U la)).symm.toLinearMap ∘ₗ
    (restr le_top ∘ₗ (space X Z U la).subtype).codRestrict _ fun s => s.2

theorem cuspSec_ofSpace (la : AllWt.Weight Dw) (s : space X Z U la) :
    cuspSec X Z U la (ofSpace X Z U la s) = restr le_top s.1 :=
  congrArg Subtype.val ((LinearEquiv.ofInjective _ (cuspSec_injective X Z U la)).apply_symm_apply ⟨_, s.2⟩)

theorem ofSpace_injective (la : AllWt.Weight Dw) : Function.Injective (ofSpace X Z U la) := fun s s' h =>
  Subtype.ext (restr_injective_of_dense le_top (dense_U₀ X Z) (by rw [← cuspSec_ofSpace, h, cuspSec_ofSpace]))

variable {X Z U} {la : AllWt.Weight Dw}

def Extends.equiv (h : Extends X Z U la) : Cusp Z U la ≃ₗ[c.F] space X Z U la :=
  (LinearEquiv.ofBijective _ ⟨ofSpace_injective X Z U la, fun f => (h f).elim fun s hs =>
    ⟨⟨s, f, hs.2.symm⟩, cuspSec_injective X Z U la ((cuspSec_ofSpace X Z U la _).trans hs.2)⟩⟩).symm

theorem Extends.restr_equiv (h : Extends X Z U la) (f : Cusp Z U la) :
    restr le_top (h.equiv f).1 = cuspSec X Z U la f :=
  (cuspSec_ofSpace X Z U la _).symm.trans (congrArg _ (h.equiv.symm_apply_apply f))

theorem Extends.space_le (h : Extends X Z U la) : space X Z U la ≤ vanBd X Z la := by
  rintro s ⟨f, hf⟩
  obtain ⟨s', hs', e⟩ := h f
  exact restr_injective_of_dense le_top (dense_U₀ X Z) (e.trans hf) ▸ hs'

def Extends.toVanBd (h : Extends X Z U la) : Cusp Z U la →ₗ[c.F] vanBd X Z la :=
  Submodule.inclusion h.space_le ∘ₗ h.equiv.toLinearMap

theorem Extends.toVanBd_injective (h : Extends X Z U la) : Function.Injective h.toVanBd :=
  (Submodule.inclusion_injective h.space_le).comp h.equiv.injective

end Component

end GlobalTheory.CompHS
