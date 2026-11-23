import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)

namespace GlobalTheory

namespace Twist

variable {X : Scheme.{0}} {F : X.Modules} {L : LB X} {m n : ℤ}

def zpowSec (σ : LB.Sec (lbZPow L m)) (k : ℕ) : LB.Sec (lbZPow L (k * m)) :=
  zmkGlobal (fun i => zfun σ i ^ k) fun i j => by
    have e : res (le_refl (L.U i ⊓ L.U j)) (L.g i j) = L.g i j := Units.ext (resG_self _ _)
    rw [map_pow, map_pow, zfun_rel σ i j _ inf_le_right le_rfl, e, mul_pow, mul_comm (k : ℤ),
      zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val]

@[simp] theorem zfun_zpowSec (σ : LB.Sec (lbZPow L m)) (k : ℕ) (i : L.ι) :
    zfun (zpowSec σ k) i = zfun σ i ^ k := zfun_zmkGlobal _ _ i

theorem basicOpen_resG_zfun (σ : LB.Sec (lbZPow L m)) (i : L.ι) {W : X.Opens} (h : W ≤ L.U i) :
    X.basicOpen (resG X h (zfun σ i)) = W ⊓ Out.nonzeroLocus σ := by
  rw [zfun, resG_resG]
  refine (X.basicOpen_res _ (homOfLE (h.trans (le_zidx_U m i))).op).trans ?_
  rw [← nonzeroLocus_inf_chart σ (zidx L m i), inf_comm (Out.nonzeroLocus σ), ← inf_assoc]
  exact congrArg (· ⊓ _) (inf_eq_left.2 (h.trans (le_zidx_U m i)))

theorem basicOpen_zfun (σ : LB.Sec (lbZPow L m)) (i : L.ι) :
    X.basicOpen (zfun σ i) = L.U i ⊓ Out.nonzeroLocus σ := by
  rw [← basicOpen_resG_zfun σ i le_rfl, resG_self]

theorem nonzeroLocus_eq_of_zfun (hL : L.IsLB) (σ : LB.Sec (lbZPow L m)) {V : X.Opens}
    (h : ∀ i, X.basicOpen (zfun σ i) = L.U i ⊓ V) : Out.nonzeroLocus σ = V := by
  ext x
  obtain ⟨i, hi⟩ := exists_chart hL x
  have e := (basicOpen_zfun σ i).symm.trans (h i)
  exact ⟨fun hx => (e.le ⟨hi, hx⟩).2, fun hx => (e.ge ⟨hi, hx⟩).2⟩

theorem nonzeroLocus_zofSec (hL : L.IsLB) (s : LB.Sec L) :
    Out.nonzeroLocus (zofSec s) = Out.nonzeroLocus s :=
  nonzeroLocus_eq_of_zfun hL _ fun i => by rw [zfun_zofSec, ← nonzeroLocus_inf_chart, inf_comm]

theorem nonzeroLocus_le_zpowSec (hL : L.IsLB) (σ : LB.Sec (lbZPow L m)) (k : ℕ) :
    Out.nonzeroLocus σ ≤ Out.nonzeroLocus (zpowSec σ k) := fun x hx => by
  obtain ⟨i, hi⟩ := exists_chart hL x
  refine ((basicOpen_zfun (zpowSec σ k) i).le ?_).2
  rw [zfun_zpowSec]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, Scheme.basicOpen_one]
    exact hi
  · rw [Scheme.basicOpen_pow _ _ hk, basicOpen_zfun]
    exact ⟨hi, hx⟩

theorem exists_finite_affine_chart_cover (hL : L.IsLB) {W : X.Opens} (hW : IsCompact (W : Set X)) :
    ∃ (κ : Type) (_ : Finite κ) (T : κ → X.Opens) (c : κ → L.ι),
      (∀ a, IsAffineOpen (T a)) ∧ (∀ a, T a ≤ W) ∧ (∀ a, T a ≤ L.U (c a)) ∧ W ≤ iSup T := by
  have h : ∀ x : W, ∃ (T : X.Opens) (c : L.ι), IsAffineOpen T ∧ x.1 ∈ T ∧ T ≤ W ⊓ L.U c := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hL x.1
    obtain ⟨T, hT, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := W ⊓ L.U i) (x := x.1) ⟨x.2, hi⟩
    exact ⟨T, i, hT, hx, hle⟩
  choose T c hT hx hle using h
  obtain ⟨S, hS⟩ := hW.elim_finite_subcover (fun x => (T x : Set X)) (fun x => (T x).isOpen)
    fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hx _⟩
  refine ⟨S, inferInstance, fun a => T a, fun a => c a, fun a => hT a,
    fun a => (hle a).trans inf_le_left, fun a => (hle a).trans inf_le_right, fun y hy => ?_⟩
  obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (hS hy)
  exact Opens.mem_iSup.2 ⟨⟨a, ha⟩, h⟩

theorem mulSecOfEq_zpowSec_app (σ : LB.Sec (lbZPow L m)) {a b c : ℕ} (hc : c = a + b) {d e : ℤ}
    (h₁ : n + a * m = d) (h₂ : d + b * m = e) (h₃ : n + c * m = e) {V : X.Opens}
    (t : Γ(twistZ F L n, V)) :
    (mulSecOfEq F (zpowSec σ b) h₂).app V ((mulSecOfEq F (zpowSec σ a) h₁).app V t) =
      (mulSecOfEq F (zpowSec σ c) h₃).app V t :=
  zsec_ext fun i => by
    simp only [zcoord_mulSecOfEq_app, zfun_zpowSec, hc, smul_smul, pow_add, map_mul, mul_comm]

variable [F.IsQuasicoherent]

theorem eventually_mulSecOfEq_zpowSec_eq_zero (hL : L.IsLB) (σ : LB.Sec (lbZPow L m))
    {W V : X.Opens} (hW : IsCompact (W : Set X)) (h : V ≤ W) (hV : W ⊓ Out.nonzeroLocus σ ≤ V)
    (a : Γ(twistZ F L n, W)) (ha : resM _ h a = 0) :
    ∀ᶠ k : ℕ in atTop, ∀ (d : ℤ) (hd : n + k * m = d),
      (mulSecOfEq F (zpowSec σ k) hd).app W a = 0 := by
  obtain ⟨κ, _, T, c, hT, hTW, hTc, hc⟩ := exists_finite_affine_chart_cover hL hW
  have key : ∀ α, ∀ᶠ k : ℕ in atTop,
      resG X (hTc α) (zfun σ (c α)) ^ k • zchartEquiv hL n (c α) (hTc α) (resM _ (hTW α) a) = 0 := by
    intro α
    obtain ⟨k, hk⟩ := QCoh.Qcqs.exists_pow_smul_eq_zero_of_isCompact F (hT α).isCompact
      (resG X (hTc α) (zfun σ (c α))) inf_le_left (basicOpen_resG_zfun σ _ (hTc α)).symm
      (zchartEquiv hL n (c α) (hTc α) (resM _ (hTW α) a)) (by
        have hle : T α ⊓ Out.nonzeroLocus σ ≤ V := (inf_le_inf_right _ (hTW α)).trans hV
        refine (zchartEquiv_resM hL (c α) (hTc α) inf_le_left _).symm.trans ?_
        rw [resM_resM, ← resM_resM h hle, ha, map_zero, map_zero])
    refine eventually_atTop.2 ⟨k, fun j hj => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
    rw [pow_add, mul_smul, hk, smul_zero]
  refine (eventually_all.2 key).mono fun k hk d hd => sec_ext_of_cover T hTW hc fun α => ?_
  apply (zchartEquiv hL d (c α) (hTc α)).injective
  rw [← app_resM, zchartEquiv_mulSecOfEq_app, zfun_zpowSec, map_pow, hk, map_zero, map_zero]

theorem eventually_exists_resM_eq_mulSecOfEq_zpowSec (hL : L.IsLB) (σ : LB.Sec (lbZPow L m))
    {W V : X.Opens} (hW : IsCompact (W : Set X)) (hW' : IsQuasiSeparated (W : Set X)) (h : V ≤ W)
    (hV : V = W ⊓ Out.nonzeroLocus σ) (b : Γ(twistZ F L n, V)) :
    ∀ᶠ k : ℕ in atTop, ∀ (d : ℤ) (hd : n + k * m = d), ∃ a : Γ(twistZ F L d, W),
      resM _ h a = (mulSecOfEq F (zpowSec σ k) hd).app V b := by
  obtain ⟨κ, _, T, c, hT, hTW, hTc, hc⟩ := exists_finite_affine_chart_cover hL hW
  have hTV : ∀ α, T α ⊓ V = T α ⊓ Out.nonzeroLocus σ := fun α => by
    rw [hV, ← inf_assoc, inf_eq_left.2 (hTW α)]
  have key : ∀ α, ∀ᶠ k : ℕ in atTop, ∃ a : Γ(twistZ F L (n + k * m), T α),
      resM _ (inf_le_left : T α ⊓ V ≤ T α) a =
        (mulSec F (zpowSec σ k) n).app _ (resM _ inf_le_right b) := by
    intro α
    have hc' : T α ⊓ V ≤ L.U (c α) := inf_le_left.trans (hTc α)
    obtain ⟨k, t, hk⟩ := QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs F (hT α).isCompact
      (hT α).isQuasiSeparated (resG X (hTc α) (zfun σ (c α))) (V := T α ⊓ V) inf_le_left
      ((hTV α).trans (basicOpen_resG_zfun σ _ (hTc α)).symm)
      (zchartEquiv hL n (c α) hc' (resM _ inf_le_right b))
    have hk' : resG X hc' (zfun σ (c α)) ^ k • zchartEquiv hL n (c α) hc' (resM _ inf_le_right b) =
        resM F inf_le_left t := by
      rw [← resG_resG (hTc α) inf_le_left]
      exact hk
    refine eventually_atTop.2 ⟨k, fun j hj => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
    refine ⟨(zchartEquiv hL _ (c α) (hTc α)).symm (resG X (hTc α) (zfun σ (c α)) ^ j • t), ?_⟩
    apply (zchartEquiv hL _ (c α) hc').injective
    rw [zchartEquiv_resM hL (c α) (hTc α), LinearEquiv.apply_symm_apply, zchartEquiv_mulSecOfEq_app,
      zfun_zpowSec, resM_smul, map_pow, map_pow, resG_resG, pow_add, mul_smul, hk']
  obtain ⟨k, hk⟩ := (eventually_all.2 key).exists
  choose a ha using hk
  have key₂ : ∀ p : κ × κ, ∀ᶠ j : ℕ in atTop, ∀ (d : ℤ) (hd : n + k * m + j * m = d),
      (mulSecOfEq F (zpowSec σ j) hd).app (T p.1 ⊓ T p.2)
        (resM _ inf_le_left (a p.1) - resM _ inf_le_right (a p.2)) = 0 := fun p => by
    refine eventually_mulSecOfEq_zpowSec_eq_zero hL σ
      (hW' _ _ (hTW p.1) (T p.1).isOpen (hT p.1).isCompact (hTW p.2) (T p.2).isOpen
        (hT p.2).isCompact) (V := T p.1 ⊓ T p.2 ⊓ V) inf_le_left
      (le_inf inf_le_left (hV.ge.trans' (inf_le_inf_right _ (inf_le_left.trans (hTW p.1))))) _ ?_
    have h₁ : T p.1 ⊓ T p.2 ⊓ V ≤ T p.1 ⊓ V := inf_le_inf_right _ inf_le_left
    have h₂ : T p.1 ⊓ T p.2 ⊓ V ≤ T p.2 ⊓ V := inf_le_inf_right _ inf_le_right
    rw [map_sub, resM_resM, resM_resM, ← resM_resM inf_le_left h₁, ← resM_resM inf_le_left h₂,
      ha, ha, ← app_resM, ← app_resM, resM_resM, resM_resM, sub_self]
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (eventually_all.2 key₂)
  refine eventually_atTop.2 ⟨k + j₀, fun l hl d hd => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (le_of_add_le_left hl)
  have hd' : n + k * m + j * m = d := by rw [← hd]; push_cast; ring
  obtain ⟨t, ht⟩ := exists_sec_of_cover T hTW hc
    (fun α => (mulSecOfEq F (zpowSec σ j) hd').app _ (a α)) fun α β => by
      have := hj₀ j (by omega) (α, β) d hd'
      rw [map_sub, sub_eq_zero] at this
      rw [← app_resM, ← app_resM]
      exact this
  refine ⟨t, sec_ext_of_cover (fun α => T α ⊓ V) (fun _ => inf_le_right)
    ((le_inf (h.trans hc) le_rfl).trans (iSup_inf_eq _ _).le) fun α => ?_⟩
  rw [resM_resM, ← resM_resM (hTW α) inf_le_left, ht, ← app_resM, ha, ← app_resM,
    mulSecOfEq_zpowSec_app σ rfl]

end Twist

end GlobalTheory
