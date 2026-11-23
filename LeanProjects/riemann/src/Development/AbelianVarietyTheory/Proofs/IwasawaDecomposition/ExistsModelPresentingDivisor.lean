import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAddStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelZeroLogConstantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMaxStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.LineNorm

section Closure

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Good (Y : Var F) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (φ : PtFn Y) : Prop :=
  (∀ y, Δ.IsEqn y (t y)) ∧ FromModel Y Δ t φ

theorem Good.congr {Δ Δ' : Y.Dv} {t t' : Y.X → Y.Fnˣ} {φ φ' : PtFn Y} (h : Good Y Δ t φ) (h₁ : Δ = Δ')
    (h₂ : ∀ y, t y = t' y) (h₃ : ∀ v e y, φ v e y = φ' v e y) : Good Y Δ' t' φ' := by
  obtain rfl : t = t' := funext h₂
  obtain rfl : φ = φ' := funext fun v => funext fun e => funext (h₃ v e)
  exact h₁ ▸ h

theorem Good.add {Δ Δ' : Y.Dv} {t t' : Y.X → Y.Fnˣ} {φ φ' : PtFn Y} (h : Good Y Δ t φ) (h' : Good Y Δ' t' φ') :
    Good Y (Δ + Δ') (fun y => t y * t' y) (fun v e y => φ v e y + φ' v e y) :=
  ⟨fun y => (h.1 y).add (h'.1 y), GlobalTheory.T.fromModel_add' F Y _ _ _ _ _ _ h.1 h'.1 h.2 h'.2⟩

theorem Good.neg {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y} (h : Good Y Δ t φ) :
    Good Y (-Δ) (fun y => (t y)⁻¹) (fun v e y => -φ v e y) :=
  ⟨fun y => (h.1 y).neg, GlobalTheory.T.fromModel_neg' F Y _ _ _ h.1 h.2⟩

theorem good_const (a : F) (n : ℕ) (ha : a ≠ 0) (hn : n ≠ 0) :
    Good Y 0 (fun _ => 1) (fun _ e _ => Real.log (e.w (algebraMap F (AlgebraicClosure F) a)) / n) :=
  ⟨fun y => CartierDiv.isEqn_zero y, GlobalTheory.T.fromModel_zero_log_constant F Y a n ha hn⟩

theorem good_zero : Good Y 0 (fun _ => 1) (fun _ _ _ => 0) :=
  (good_const 1 1 one_ne_zero one_ne_zero).congr rfl (fun _ => rfl) (fun _ _ _ => by simp)

omit [NumberField F] in
theorem isEqn_sum {α : Type} (s : Finset α) {Δ : α → Y.Dv} {t : α → Y.Fnˣ} (y : Y.X)
    (h : ∀ a, (Δ a).IsEqn y (t a)) : (∑ a ∈ s, Δ a).IsEqn y (∏ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact CartierDiv.isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a).add ih

theorem good_sum {α : Type} (s : Finset α) {Δ : α → Y.Dv} {t : α → Y.X → Y.Fnˣ} {φ : α → PtFn Y}
    (h : ∀ a ∈ s, Good Y (Δ a) (t a) (φ a)) :
    Good Y (∑ a ∈ s, Δ a) (fun y => ∏ a ∈ s, t a y) (fun v e y => ∑ a ∈ s, φ a v e y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | insert a s ha ih =>
    refine ((h a (Finset.mem_insert_self _ _)).add (ih fun b hb => h b (Finset.mem_insert_of_mem hb))).congr
      (Finset.sum_insert ha).symm (fun _ => by rw [Finset.prod_insert ha]) (fun _ _ _ => by rw [Finset.sum_insert ha])

theorem Good.nsmul {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y} (h : Good Y Δ t φ) (n : ℕ) :
    Good Y (n • Δ) (fun y => t y ^ n) (fun v e y => (n : ℝ) * φ v e y) :=
  (good_sum (Finset.range n) (fun _ _ => h)).congr (by simp) (by simp) (by simp)

theorem Good.zsmul {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y} (h : Good Y Δ t φ) (n : ℤ) :
    Good Y (n • Δ) (fun y => t y ^ n) (fun v e y => (n : ℝ) * φ v e y) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact (h.nsmul m).congr (by simp) (by simp) (by simp)
  · exact (h.nsmul m).neg.congr (by simp) (by simp) (by simp)

theorem Good.change {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y} (h : Good Y Δ t φ) {t' : Y.X → Y.Fnˣ}
    (h' : ∀ y, Δ.IsEqn y (t' y)) :
    FromModel Y Δ t' (fun v e y =>
      Real.log (e.w (valAt y.1 ((t (below y.1) * (t' (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn))) + φ v e y) := by
  obtain ⟨h₁, M, L, m, r, hL, hP, hv⟩ := h
  refine ⟨M, L, m, r, hL, hP, fun v e y yt i hy hU => ?_⟩
  have hmem : below y.1 ∈ (L.pull M.j).U i := by
    have h2 : ∀ U : M.X.Opens, ⊤ ≤ yt ⁻¹ᵁ U → M.j (below y.1) ∈ U := fun U hU => by
      have e₀ : M.j (below y.1) = yt (spMap e.O.subtype (IsLocalRing.closedPoint _)) :=
        (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun q : Sp (AlgebraicClosure F) ⟶ M.X => q (IsLocalRing.closedPoint _)) hy.symm).trans (Scheme.Hom.comp_apply _ _ _))
      exact e₀ ▸ hU (Set.mem_univ _)
    exact Set.mem_iInter.2 fun _ => h2 _ hU
  have u₁ : UnitAt (below y.1) ((t (below y.1) * (t' (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn) := by
    simpa [div_eq_mul_inv] using (h' (below y.1)).iff_unitAt.1 (h₁ _)
  have u₂ : UnitAt (below y.1) (((t (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn) := by
    simpa [div_eq_mul_inv, mul_comm] using ((h₁ (below y.1)).nsmul m).iff_unitAt.1 (hP.isEqn i _ hmem)
  have e₁ : (((t' (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn) =
      ((t (below y.1) * (t' (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn) ^ (m : ℕ) *
        (((t (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul]
    congr 1
    rw [mul_pow, mul_comm (t _ ^ _), mul_assoc, ← mul_assoc (t _ ^ _), ← mul_pow, mul_inv_cancel, one_pow, one_mul]
  have n₁ := SmallSec.valAt_ne_zero u₁
  have n₂ := SmallSec.valAt_ne_zero u₂
  rw [e₁, SmallSec.valAt_mul (SmallSec.regAt_pow u₁.regAt _) u₂.regAt, SmallSec.valAt_pow u₁.regAt, map_mul, map_pow,
    Real.log_mul (pow_ne_zero _ (e.w.ne_zero n₁)) (e.w.ne_zero n₂), Real.log_pow, mul_add, hv v e y yt i hy hU]

end Closure

section Steps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem good_step (hB : HTBoundSt) [IsLocallyNoetherian X] (hX : X.IsSeparated) (M : GlobalTheory.TrueGeo.Model Y)
    (ρ' : M.X ⟶ X) {ρ : Y.X ⟶ X} (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) (hρ : M.j ≫ ρ' = ρ) {m : ℕ}
    {u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)}
    {f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)} {d : Y.X → Fin m → Y.Fnˣ}
    (h : IsFlagFrame t ρ u₀ f d) {Δ : Fin m → Y.Dv} (hΔ : ∀ y i, (Δ i).IsEqn y (d y i)) (q : ℕ) (i : Fin m) :
    Good Y (Δ i) (fun y => d y i) (stepLog t ρ f q i) := by
  have key : ∀ (k : ℕ) (hk : k ≤ m), Good Y (∑ l : Fin k, Δ (Fin.castLE hk l))
      (fun y => ∏ l : Fin k, d y (Fin.castLE hk l))
      (fun v e y => ∑ l : Fin k, stepLog t ρ f q (Fin.castLE hk l) v e y) := fun k hk => by
    have he : ∀ y, (∑ l : Fin k, Δ (Fin.castLE hk l)).IsEqn y (∏ l : Fin k, d y (Fin.castLE hk l)) := fun y =>
      isEqn_sum _ y fun l => hΔ y _
    exact ⟨he, GlobalTheory.T.fromModel_of_locMax' F Y M _ _ _ he (GlobalTheory.T.tangent_sections_on_normal_model hB E H X t hX F Y M ρ' ρ hM hρ m u₀ f d h q k hk)⟩
  have hi : Fin.castLE (Nat.succ_le_of_lt i.2) (Fin.last i) = i := rfl
  refine ((key (i + 1) i.2).add (key i i.2.le).neg).congr ?_ (fun y => ?_) (fun v e y => ?_)
  · rw [Fin.sum_univ_castSucc, hi]
    exact add_neg_cancel_comm _ _
  · rw [Fin.prod_univ_castSucc, hi]
    exact mul_inv_cancel_comm _ _
  · rw [Fin.sum_univ_castSucc, hi]
    exact add_neg_cancel_comm _ _

variable (t) in
open Classical in

def mixLog (ρ : Y.X ⟶ X) {m : ℕ}
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (b : ℕ → Bool) (i : Fin m) : PtFn Y :=
  fun v ε y =>
    if hp : (resP v).Prime then
      haveI := Fact.mk hp
      let ψ : Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ)
          (lat t (resP v) (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ) (b (resP v)))
          (fun l => spMap (dualMap ψ) ≫ f (below y.1) l) i)
    else 0

theorem mixLog_eq {ρ : Y.X ⟶ X} {m : ℕ}
    {f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)} {b : ℕ → Bool} {i : Fin m}
    {v : HeightOneSpectrum (𝓞 F)} {ε : Ext v} {y : AlgPt Y} {q : ℕ} (h : decide (resP v = q) = b (resP v)) :
    stepLog t ρ f q i v ε y = mixLog t ρ f b i v ε y := by
  unfold stepLog mixLog
  rw [← h]

theorem good_mix {ρ : Y.X ⟶ X} {m : ℕ}
    {f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)} {i : Fin m} {Δ : Y.Dv}
    {d : Y.X → Y.Fnˣ} (h : ∀ q, Good Y Δ d (stepLog t ρ f q i)) {b : ℕ → Bool} (hb : {q | b q = true}.Finite) :
    Good Y Δ d (mixLog t ρ f b i) := by
  refine ((h 0).add (good_sum hb.toFinset fun q _ => (h q).add (h 0).neg)).congr (by simp) (by simp) fun v e y => ?_
  obtain ⟨hp, -⟩ := GlobalTheory.ShFam.Pad.ioOf_spec F v e
  have h0 : ∀ q, q ≠ resP v → stepLog t ρ f q i v e y = stepLog t ρ f 0 i v e y := fun q hq =>
    (mixLog_eq (b := fun _ => false) (by simpa using hq.symm)).trans
      (mixLog_eq (b := fun _ => false) (by simpa using hp.ne_zero)).symm
  by_cases hv : b (resP v) = true
  · rw [Finset.sum_eq_single (resP v) (fun q _ hq => by rw [h0 q hq, add_neg_cancel])
      (fun hn => absurd (hb.mem_toFinset.2 hv) hn), ← mixLog_eq (q := resP v) (by simp [hv])]
    ring
  · rw [Finset.sum_eq_zero fun q hq => by
      rw [h0 q (fun e => hv (e ▸ hb.mem_toFinset.1 hq)), add_neg_cancel], add_zero]
    exact mixLog_eq (by simpa [hp.ne_zero] using hv)

theorem good_diff (Y : Var F) (E : Type) [Field E] [NumberField E] {b : ℕ → Bool} (hb : {q | b q = true}.Finite) :
    Good Y 0 (fun _ => 1) (fun v e _ => if b (resP v) = true then vDiff E (resP v) * Real.log (e.w (resP v)) else 0) := by
  classical
  refine (good_sum (hb.toFinset.filter Nat.Prime) fun q hq =>
    good_const ((q : F) ^ padicValNat q (NumberField.discr E).natAbs) (Module.finrank ℚ E)
      (pow_ne_zero _ (Nat.cast_ne_zero.2 (Finset.mem_filter.1 hq).2.ne_zero)) Module.finrank_pos.ne').congr
    (by simp) (by simp) fun v e y => ?_
  obtain ⟨hp, -, hw⟩ := GlobalTheory.ShFam.Pad.ioOf_spec F v e
  have := Fact.mk hp
  have h0 : ∀ q : ℕ, q.Prime → q ≠ resP v → Real.log (e.w (q : AlgebraicClosure F)) = 0 := fun q hq hne => by
    have h1 : ‖(q : ℂ_[resP v])‖ = 1 := by
      rw [← map_natCast (algebraMap ℚ_[resP v] ℂ_[resP v]), norm_algebraMap']
      exact Padic.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes hp hq).2 hne.symm)
    rw [hw, map_natCast (ioOf (resP v) e), h1, Real.log_one, mul_zero]
  simp only [map_pow, map_natCast, Real.log_pow]
  split_ifs with hv
  · rw [Finset.sum_eq_single (resP v) (fun q hq hne => by rw [h0 q (Finset.mem_filter.1 hq).2 hne]; simp)
      (fun hn => absurd (Finset.mem_filter.2 ⟨hb.mem_toFinset.2 hv, hp⟩) hn), vDiff]
    ring
  · refine Finset.sum_eq_zero fun q hq => ?_
    rw [h0 q (Finset.mem_filter.1 hq).2 (fun e => hv (e ▸ hb.mem_toFinset.1 (Finset.mem_filter.1 hq).1))]
    simp

end Steps

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e)

abbrev fr (y : C.Y.X) := (C.gr_spec y).choose_spec.choose

abbrev dg (y : C.Y.X) : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ := (C.gr_spec y).choose_spec.choose_spec.choose

omit [NumberField F] in
theorem fr_spec (y : C.Y.X) : (fr C y).Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 (dg C y) ∧
    ∀ τ i, (C.gr τ i).IsEqn y (dg C y τ i) := (C.gr_spec y).choose_spec.choose_spec.choose_spec

omit [NumberField F] in
theorem isFrame_fr (y : C.Y.X) {k : Type} [CommRing k] (ψ : C.Y.X.presheaf.stalk y →+* k) :
    GlobalTheory.LocM.IsFrame Z.t (ψ.comp (C.gr_spec y).choose) (spMap ψ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z)
      (Vecs.bc ψ (fr C y).v) :=
  GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw l c Z.X Z.t _ k _ ψ _ (fr C y).v
    ⟨fun τ i => ⟨(fr C y).tan τ i, (fr C y).eig τ i⟩, (fr C y).basis⟩

attribute [local instance] Over.cartesianMonoidalCategory in
omit [NumberField F] in

theorem isFlagFrame_eig (τ : E →+* ℂ) :
    IsFlagFrame Z.t (C.π ≫ genι Z) (C.f0.v τ) (fun y => (fr C y).v τ) (fun y => dg C y τ) where
  tan y := (fr C y).tan τ
  tri y := (fr_spec C y).1.2.2 τ
  indep y k _ ψ cf cf' w h h' := by
    have hF := isFrame_fr C y ψ
    have e₁ := (isCombAtG_iff Z.t _ (fun j => ovT (hF.1 τ j).1) cf w).1 h
    have ht : IsTanAtG Z.t (spMap ψ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z) w := by
      rw [← e₁]
      exact isTanAtG_of _ (combT_tan _ (fun j => ovT (hF.1 τ j).1) (fun j => smT_zero_ovT _) cf)
    refine (hF.2 τ w ht fun a => ?_).unique h h'
    have := Z.t.act.hom a
    rw [← e₁]
    exact congrArg (fun q => q.left) (combT_eig _ (fun j => ovT (hF.1 τ j).1) (Z.t.act.act a) _
      (fun j => Over.OverMorphism.ext ((hF.1 τ j).2 a)) cf)

omit [NumberField F] in

theorem isFlagFrame_concat :
    IsFlagFrame Z.t (C.π ≫ genι Z)
      (fun i : Fin (letters Dw).length => C.f0.v ((letters Dw).get i).1 ((letters Dw).get i).2)
      (fun y i => (fr C y).v ((letters Dw).get i).1 ((letters Dw).get i).2)
      (fun y i => dg C y ((letters Dw).get i).1 ((letters Dw).get i).2) where
  tan y i := (fr C y).tan _ _
  tri y i := by
    obtain ⟨hx, -, h⟩ := (fr_spec C y).1
    obtain ⟨cf, h₁, h₂, h₃⟩ := h ((letters Dw).get i).1 ((letters Dw).get i).2
    replace h₃ := (congrArg (fun x => IsCombAtG Z.t x _ cf _) hx).mp h₃
    obtain ⟨cg, g₁, g₂, g₃⟩ := (GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame E H Dw l c Z.X Z.t _ _ _ _
      (isFrame_fr C y (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField))).2 i cf _ h₂ h₃
    exact ⟨cg, g₂.trans h₁, g₁, (congrArg (fun x => IsCombAtG Z.t x _ cg _) hx).mpr g₃⟩
  indep y k _ ψ := (GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame E H Dw l c Z.X Z.t _ _ _ _ (isFrame_fr C y ψ)).1

open Classical in

def symLog (b : ℕ → Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : PtFn C.Y := fun v ε y =>
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let ψ : C.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
      lnStep Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
        (fun τ i => spMap (dualMap ψ) ≫ (C.gr_spec (below y.1)).choose_spec.choose.v τ i) (resP v) (b (resP v)) st
  else 0

theorem good_sym (hB : HTBoundSt) [IsLocallyNoetherian Z.X] (hX : Z.X.IsSeparated) (M : GlobalTheory.TrueGeo.Model C.Y)
    (ρ' : M.X ⟶ Z.X) (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) (hρ : M.j ≫ ρ' = C.π ≫ genι Z)
    {b : ℕ → Bool} (hb : {q | b q = true}.Finite) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) :
    Good C.Y ((letterOf Dw st).elim 0 fun x => C.gr x.1 x.2)
      (fun y => (letterOf Dw st).elim 1 fun x => dg C y x.1 x.2) (symLog C b st) := by
  rcases st with ⟨τ, k⟩ | k
  · by_cases h : k < Dw.mult τ
    · have h₁ := good_mix (fun q => good_step hB hX M ρ' hM hρ (isFlagFrame_eig C τ)
        (fun y i => (fr_spec C y).2 τ i) q ⟨k, h⟩) hb
      by_cases hτ : τ (H.rt : E) = H.rt0
      · refine (h₁.add (good_diff C.Y E hb)).congr (by simp [letterOf, h]) (by simp [letterOf, h]) fun v ε y => ?_
        obtain ⟨hp, -⟩ := GlobalTheory.ShFam.Pad.ioOf_spec F v ε
        have hl : Real.log (resP v) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
        simp only [symLog, mixLog, lnStep, dif_pos hp, dif_pos h, hτ, and_true]
        split_ifs
        · field_simp
          ring
        · simp
      · refine h₁.congr (by simp [letterOf, h]) (by simp [letterOf, h]) fun v ε y => ?_
        simp only [symLog, mixLog, lnStep, dif_pos h, hτ, and_false, if_false, sub_zero]
    · exact good_zero.congr (by simp [letterOf, h]) (by simp [letterOf, h]) fun v ε y => by
        simp [symLog, lnStep, h]
  · by_cases h : k < (letters Dw).length
    · have h₁ := good_mix (fun q => good_step hB hX M ρ' hM hρ (isFlagFrame_concat C)
        (Δ := fun i => C.gr ((letters Dw).get i).1 ((letters Dw).get i).2)
        (fun y i => (fr_spec C y).2 _ _) q ⟨k, h⟩) hb
      refine h₁.congr (by simp [letterOf, h]) (by simp [letterOf, h]) fun v ε y => ?_
      simp only [symLog, mixLog, lnStep, dif_pos h]
    · exact good_zero.congr (by simp [letterOf, not_lt.1 h]) (by simp [letterOf, not_lt.1 h]) fun v ε y => by
        simp [symLog, lnStep, h]

open Classical in

def lgCopy (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt C.Y) : ℝ :=
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let f := (C.gr_spec (below y.1)).choose_spec.choose
    let t := (C.gr_spec (below y.1)).choose_spec.choose_spec.choose
    let ψ : C.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf C (expo Dw w)) (below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
          (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2
  else 0

theorem lgOf_eq_lgCopy : @lgOf = @lgCopy := rfl

theorem mul_finsupp_sum {α : Type} (w : α →₀ ℤ) (c : ℝ) (g : α → ℝ) :
    c * w.sum (fun a n => (n : ℝ) * g a) = ∑ a ∈ w.support, (w a : ℝ) * (c * g a) := by
  simp only [Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_left_comm _ _ _

theorem lgCopy_eq (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt C.Y) :
    lgCopy C w v ε y = Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, dg C (below y.1) x.1 x.2 ^ expo Dw w x) *
      (eqn (divOf C (expo Dw w)) (below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) +
      ∑ a ∈ w.support, (w a : ℝ) * symLog C a.1 a.2.2 v ε y := by
  obtain ⟨hp, -⟩ := GlobalTheory.ShFam.Pad.ioOf_spec F v ε
  simp only [lgCopy, symLog, dif_pos hp]
  refine congrArg₂ (fun a b : ℝ => a + b) rfl ?_
  refine (mul_finsupp_sum _ _ _).trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine congrArg _ (congrArg _ ?_)
  rfl

omit [NumberField F] in
theorem sum_expo {G : Type} [AddCommGroup G] (g : Letter Dw → G) (w : Sym E →₀ ℤ) :
    ∑ a ∈ w.support, w a • ((letterOf Dw a.2.2).elim 0 g) = ∑ x, expo Dw w x • g x := by
  classical
  simp only [expo, Finsupp.sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases letterOf Dw a.2.2 <;> simp

theorem fromModel_lgOf (hB : HTBoundSt) [IsLocallyNoetherian Z.X] (hX : Z.X.IsSeparated) (M : GlobalTheory.TrueGeo.Model C.Y)
    (ρ' : M.X ⟶ Z.X) (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) (hρ : M.j ≫ ρ' = C.π ≫ genι Z)
    (w : Sym E →₀ ℤ) (hw : ∀ a ∈ w.support, {q | a.1 q = true}.Finite) :
    FromModel C.Y (divOf C (expo Dw w)) (eqn (divOf C (expo Dw w))) (lgOf C w) := by
  have h₁ := good_sum w.support fun a ha => (good_sym C hB hX M ρ' hM hρ (hw a ha) a.2.2).zsmul (w a)
  have h₂ : Good C.Y (divOf C (expo Dw w)) (fun y => ∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw w x) _ :=
    h₁.congr (sum_expo (fun x => C.gr x.1 x.2) w)
      (fun y => sum_expo (G := Additive C.Y.Fnˣ) (fun x => Additive.ofMul (dg C y x.1 x.2)) w) (fun _ _ _ => rfl)
  have h₃ := h₂.change (t' := eqn (divOf C (expo Dw w))) fun y => (CartierDiv.exists_isEqn _ y).choose_spec
  have e₀ : lgCopy C w = _ := funext fun v => funext fun ε => funext fun y => lgCopy_eq C w v ε y
  rw [lgOf_eq_lgCopy, e₀]
  exact h₃

end Flags

theorem exists_model_lgOf : HTBoundSt → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag), AdmEx S κ → ∀ (k : s.Comp) (w : Sym D.host.E →₀ ℤ), (∀ a ∈ w.support, {q | a.1 q = true}.Finite) → ∃ (M : GlobalTheory.TrueGeo.Model (fl.C k).Y) (L : LB M.X) (m : ℕ+) (r : (L.pull M.j).ι → (fl.C k).Y.Fnˣ), L.IsLB ∧ Presents ((m : ℕ) • divOf (fl.C k) (expo S.Dw w)) (L.pull M.j) r ∧ ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (fl.C k).Y) (yt : Sp e.O ⟶ M.X) (i : (L.pull M.j).ι), spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) → ((m : ℕ) : ℝ) * lgOf (fl.C k) w v e y = Real.log (e.w (valAt y.1 (((eqn (divOf (fl.C k) (expo S.Dw w)) (below y.1))⁻¹ ^ (m : ℕ) * r i : (fl.C k).Y.Fnˣ) : (fl.C k).Y.Fn))) := by
  intro hB D A N j S κ s fl _ k w hw
  obtain ⟨hX, hN, M, ρ', hM, hρ⟩ := GlobalTheory.T.exists_normal_model_over_projective D.what₂.LL (fl.C k).Y (𝓞 κ.c.F) (RingOfIntegers.mapRingEquiv κ.e)
    s.T.Z.X s.T.Z.s ((fl.C k).π ≫ genι s.T.Z) s.T.Z.proj (by
      rw [← (fl.C k).π_str]
      simp only [Category.assoc]
      rw [pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl)
  exact fromModel_lgOf (fl.C k) hB hX M ρ' hM hρ w hw

end GlobalTheory.LineNorm
