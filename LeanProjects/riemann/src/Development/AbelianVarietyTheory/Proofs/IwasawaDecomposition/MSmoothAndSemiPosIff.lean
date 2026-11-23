import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMulFderivOfTsupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open Set Filter Topology GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.ChartGlue

namespace GlobalTheory.TrueGeo.InducedSemiPos

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {ρ : k →+* k'} {X Z : Scheme.{0}} {p : X ⟶ Sp k}
  {q : Z ⟶ Sp k'} {j : Z ⟶ X} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D : ℕ} {m : CxPts q τ → CxPts p σ}

theorem exists_chart_levi (H : IsPullback j q p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ j)
    (c : AlgChart p σ D) {z : CxPts q τ} (hz : m z ∈ c.e.source) :
    ∃ c' : AlgChart q τ D, z ∈ c'.e.source ∧
      ∀ (f : CxPts p σ → ℝ) (ξ : Fin D → ℂ), c'.levi (fun w => f (m w)) z ξ = c.levi f (m z) ξ := by
  obtain ⟨c', hz', h, hx⟩ := c.exists_baseChange H hm hz
  have he (w) (h₁ : w ∈ c'.e.source) (h₂ : m w ∈ c.e.source) : c.e (m w) = c'.e w := by
    ext a
    rw [c.apply_eq _ h₂, c'.apply_eq _ h₁, hx, ev_appLE_of_comp hm h _ (c'.source_subset h₁)]
  have ho := isOpen_over c'.e (c.e.open_source.preimage (continuous_of_comp hm))
  refine ⟨c', hz', fun f ξ => ?_⟩
  rw [AlgChart.levi, AlgChart.levi, he z hz' hz]
  refine congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.leviV_congr
    (eventually_of_mem (ho.mem_nhds (mem_over c'.e hz' hz)) fun v hv => ?_) ξ)
  have e := he _ (c'.e.map_target hv.1) hv.2
  rw [c'.e.right_inv hv.1] at e
  have e' : c.e.symm v = m (c'.e.symm v) := by
    conv_lhs => rw [← e]
    exact c.e.left_inv hv.2
  simp only [e']

theorem semiPos_pull_iff (H : IsPullback j q p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ j)
    (hs : Function.Surjective m) (R : AnRead p σ D) (R' : AnRead q τ D) {B : LB X} {φ : Weight p σ B}
    {φ' : Weight q τ (B.pull j)} (hφ' : φ'.IsSmooth R')
    (e : ∀ i z, φ'.φ i z = φ.φ (i PUnit.unit) (m z)) :
    φ'.SemiPos R' ↔ φ.SemiPosReg D := by
  have hi {a : B.ι} {z : CxPts q τ} (h : m z ∈ ptsIn p σ (B.U a)) : z ∈ ptsIn q τ ((B.pull j).U fun _ => a) :=
    ptsIn_mono (fun _ hx => mem_iInter.2 fun _ => hx) ((mem_ptsIn_preimage hm).2 h)
  refine ⟨fun h a c y hy ξ => ?_, fun h => hφ'.semiPos_of_exists fun z => ?_⟩
  · obtain ⟨z, rfl⟩ := hs y
    obtain ⟨c', hz', hl⟩ := exists_chart_levi H hm c hy.1
    exact (h.chart hφ' hz' (hi hy.2) ξ).trans_eq
      ((congrArg (c'.levi · z ξ) (funext (e _))).trans (hl _ ξ))
  · obtain ⟨a, ha⟩ := R.cover (m z)
    obtain ⟨c', hz', hl⟩ := exists_chart_levi H hm (R.chart a) ha
    refine ⟨c', _, hz', hi (mem_pick φ.isLB (m z)), fun ξ => ?_⟩
    have h₁ : c'.levi (φ'.φ fun _ => pick φ.isLB (m z)) z ξ = (R.chart a).levi (φ.φ (pick φ.isLB (m z))) (m z) ξ :=
      (congrArg (c'.levi · z ξ) (funext (e _))).trans (hl _ ξ)
    exact le_of_le_of_eq (h _ (R.chart a) _ ⟨ha, mem_pick φ.isLB (m z)⟩ ξ) h₁.symm

end BaseChange

section Power

open Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv} {m : Met Y σ Δ} {k : ℕ}

theorem mSmooth_of_mPow (hk : k ≠ 0) (h : mSmooth Y σ _ (mPow Y σ Δ k m)) : mSmooth Y σ Δ m := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  refine ⟨fun y hy => ?_, fun g => ?_⟩
  · have h₁ := mem_eqnSet Δ y
    have h₂ := (Met.mem_posSet_iff (CartierDiv.IsEqn.nsmul h₁ k)).1 (h.1 hy)
    rw [mPow_h h₁] at h₂
    exact lt_of_le_of_ne (m.nonneg _ _) fun e => h₂.ne' (by rw [← e, zero_pow hk])
  · refine AnRead.SmoothOn.congr (f := fun y => (k : ℝ)⁻¹ * (mPow Y σ Δ k m).wt (g ^ k) y)
      (fun c => contDiffOn_const.mul ((h.2 (g ^ k)).mono
        (fun _ hz => ⟨trivial, CartierDiv.IsEqn.nsmul hz.2 k⟩) c)) fun y hy => ?_
    rw [wt_mPow hy.2, inv_mul_cancel_left₀ hk']

theorem mPsh_mPow_iff (hk : k ≠ 0) (h : mSmooth Y σ Δ m) :
    mPsh Y σ _ (mPow Y σ Δ k m) 0 ↔ mPsh Y σ Δ m 0 := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have h' : mSmooth Y σ _ (mPow Y σ Δ k m) := Met.SmoothOn.mPow isOpen_univ h k
  have key (c : AlgChart Y.str σ Y.dim) (g : Y.Fnˣ) (y : Y.pts σ) (hy : y ∈ c.e.source) (hg : y ∈ eqnSet σ Δ g) (ξ) :
      c.levi (fun z => (mPow Y σ Δ k m).wt (g ^ k) z + (0 : Y.pts σ → ℝ) z) y ξ =
        k * c.levi (fun z => m.wt g z + (0 : Y.pts σ → ℝ) z) y ξ := by
    simp only [Pi.zero_apply, add_zero]
    rw [AlgChart.levi_congr (isOpen_eqnSet Δ g) hy hg fun z hz => wt_mPow hz k]
    exact AlgChart.levi_const_mul _ (((h.2 g).mono fun _ hz => ⟨trivial, hz⟩).contDiffAt_two
      (isOpen_eqnSet Δ g) hy hg) ξ
  rw [h.mPsh_iff_levi smoothOn_zero, h'.mPsh_iff_levi smoothOn_zero]
  refine ⟨fun H c g y hy hg ξ => ?_, fun H c g y hy hg ξ => ?_⟩
  · have := H c (g ^ k) y hy (CartierDiv.IsEqn.nsmul hg k) ξ
    rw [key c g y hy hg] at this
    exact nonneg_of_mul_nonneg_right this hk'
  · have h₁ := mem_eqnSet Δ y
    rw [h'.levi_frame smoothOn_zero hy (CartierDiv.IsEqn.nsmul h₁ k) hg, key c _ y hy h₁]
    exact mul_nonneg hk'.le (H c _ y hy h₁ ξ)

theorem smooth_psh_of_weight {L : LB Y.X} {r : L.ι → Y.Fnˣ} (hp : Presents Δ L r) {φ : Weight Y.str σ L}
    (hφ : φ.IsSmooth (Y.an σ)) (t : ℝ)
    (h : ∀ i, ∀ y ∈ ptsIn Y.str σ (L.U i), Real.exp (-t) * m.h (r i) y = Real.exp (-φ.φ i y)) :
    mSmooth Y σ Δ m ∧ (mPsh Y σ Δ m 0 ↔ φ.SemiPos (Y.an σ)) := by
  have h₁ (i y) (hy : y ∈ ptsIn Y.str σ (L.U i)) : m.h (r i) y = Real.exp (t - φ.φ i y) := by
    rw [sub_eq_add_neg, Real.exp_add, ← h i y hy, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have h₂ (i y) (hy : y ∈ ptsIn Y.str σ (L.U i)) : m.wt (r i) y = 1 * φ.φ i y + -t := by
    rw [Met.wt, h₁ i y hy, Real.log_exp]
    ring
  have hs : mSmooth Y σ Δ m := Met.smoothOn_of_cover isOpen_univ
    (fun y _ => by
      have hi := mem_pick φ.isLB y
      rw [Met.mem_posSet_iff (ptsIn_subset_eqnSet hp _ hi), h₁ _ y hi]
      exact Real.exp_pos _)
    (fun i => isOpen_ptsIn (L.U i)) (fun y => ⟨_, mem_pick φ.isLB y⟩) (ptsIn_subset_eqnSet hp) fun i =>
    AnRead.SmoothOn.congr (f := fun y => 1 * φ.φ i y + -t)
      (fun c => (contDiffOn_const.mul ((hφ i).mono inter_subset_right c)).add contDiffOn_const)
      fun y hy => h₂ i y hy.2
  refine ⟨hs, ?_⟩
  rw [hs.mPsh_iff_semiPos smoothOn_zero hp]
  refine forall₂_congr fun i c => forall₂_congr fun y hy => forall_congr' fun ξ => ?_
  refine iff_of_eq (congrArg (0 ≤ ·) ((AlgChart.levi_congr (c := (Y.an σ).chart c) (isOpen_ptsIn (L.U i))
    hy.1 hy.2 (g := fun z => 1 * φ.φ i z + -t) (fun z hz => (add_zero _).trans (h₂ i z hz)) ξ).trans ?_))
  refine (congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul (hφ.contDiffAt_two hy.1 hy.2) 1 (-t) ξ)).trans ?_
  rw [Complex.ofReal_one, one_mul]
  rfl

end Power

theorem mSmooth_and_semiPos_iff : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → (∀ σ, C.mSmooth Y σ A.D (A.m σ)) ∧ (A.SemiPos ↔ L.SemiPos Y.dim) := by
  intro F _ _ C Y A M L k cf ⟨_, r, hr, hi, _⟩
  obtain rfl := C.eq_std
  have key (σ : F →+* ℂ) : Var.mSmooth Y σ A.D (A.m σ) ∧
      (Var.mPsh Y σ A.D (A.m σ) 0 ↔ (L.φ (σ.comp (algebraMap (𝓞 F) F))).SemiPosReg Y.dim) := by
    obtain ⟨R⟩ := ModelCharts.genSmooth_model F Y M (σ.comp (algebraMap (𝓞 F) F))
    have hm : ∀ z, (bcMap M.pb.w σ z).1 = z.1 ≫ M.j := fun _ => rfl
    let φ : Weight Y.str σ (L.B.pull M.j) :=
      (L.φ (σ.comp (algebraMap (𝓞 F) F))).linComb _ _ (fun _ => bcMap M.pb.w σ) fun _ => hm
    have hφ : φ.IsSmooth (Y.an σ) := ((Weight.isCInf_iff_isSmooth R).1 (L.cInf _)).linComb _ _ _ _ _
    have e (i z) : φ.φ i z = (L.φ _).φ (i PUnit.unit) (bcMap M.pb.w σ z) :=
      (Fintype.sum_unique fun a : PUnit.{1} =>
        ((1 : ℤ) : ℝ) * (L.φ _).φ (i a) (bcMap M.pb.w σ z)).trans (by simp)
    obtain ⟨h₁, h₂⟩ := smooth_psh_of_weight (m := Var.mPow Y σ A.D k (A.m σ)) hr hφ
      (2 * (k : ℕ) * (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) fun i y hy => by
        have h₃ := Var.ptsIn_subset_eqnSet hr i hy
        have h₄ := hi σ y _ i (((r i)⁻¹ : Y.Fnˣ) : Y.Fn) (hm y) (mem_ptsIn.1 hy) (by
          rw [Units.val_inv_eq_inv_val]
          exact (CartierDiv.isEqn_iff_generatesAt_inv.1 h₃).regularAt)
        rw [Units.inv_mul, Base.ratVal_one, norm_one, one_pow, one_mul] at h₄
        rw [e, ← h₄, ← Var.pn_frame h₃]
    have h₅ := mSmooth_of_mPow k.ne_zero h₁
    exact ⟨h₅, (mPsh_mPow_iff k.ne_zero h₅).symm.trans (h₂.trans
      (semiPos_pull_iff M.pb hm (bijective_bcMap M.pb σ).2 R _ hφ e))⟩
  refine ⟨fun σ => (key σ).1, fun h τ => ?_, fun h σ => ⟨(key σ).1, (key σ).2.2 (h _)⟩⟩
  obtain ⟨σ, rfl⟩ : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ :=
    ⟨IsFractionRing.lift (K := F) (ModelCharts.injective_emb τ),
      RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) (ModelCharts.injective_emb τ) x⟩
  exact (key σ).2.1 (h σ).2

end GlobalTheory.TrueGeo.InducedSemiPos
