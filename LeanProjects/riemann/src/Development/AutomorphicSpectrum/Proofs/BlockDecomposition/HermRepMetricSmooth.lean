import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueComplexPointUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

open scoped ContDiff Topology

namespace GlobalTheory.CompanionTheory.MPDict.SmoothRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def rt (c : ∀ k, Bk n k) (q : Σ k, Bk n k) : Γ(MP ℤ m n, mchart c) :=
  resG _ (mchart_le c q.1) (pullRatio (prB n q.1) _ (c q.1) le_rfl q.2)

def rtOn (c : ∀ k, Bk n k) (W : (MP ℤ m n).Opens) (h : ∀ k, W ≤ blockChart n k (c k)) (q : Σ k, Bk n k) :
    Γ(MP ℤ m n, W) :=
  pullRatio (prB n q.1) W (c q.1) (h q.1) q.2

theorem closure_ratio (N : ℕ) (i : Fin (N + 1)) : Subring.closure (Set.range (ratio ℤ N i)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨p, rfl⟩ := aeval_ratio_surjective ℤ N i v
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [aeval_C]
    simpa using intCast_mem (Subring.closure (Set.range (ratio ℤ N i))) r
  | add p q hp hq => rw [map_add]; exact add_mem (hp trivial) (hq trivial)
  | mul_X p j hp =>
    rw [map_mul, aeval_X]
    exact mul_mem (hp trivial) (Subring.subset_closure ⟨j, rfl⟩)

theorem eq_top_of_isPushout {R A B C : CommRingCat.{0}} {a : R ⟶ A} {b : R ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (H : IsPushout a b f g) (S : Subring C) (hf : ∀ x, f x ∈ S) (hg : ∀ x, g x ∈ S) : S = ⊤ := by
  let ι : CommRingCat.of S ⟶ C := CommRingCat.ofHom S.subtype
  let f' : A ⟶ .of S := CommRingCat.ofHom (f.hom.codRestrict S hf)
  let g' : B ⟶ .of S := CommRingCat.ofHom (g.hom.codRestrict S hg)
  have w : a ≫ f' = b ≫ g' := by
    ext x
    exact congr($(H.w) x)
  let d := H.desc f' g' w
  have e : d ≫ ι = 𝟙 C := H.hom_ext (by rw [H.inl_desc_assoc]; rfl) (by rw [H.inr_desc_assoc]; rfl)
  rw [eq_top_iff]
  intro x _
  have h : ι (d x) = x := congr($e x)
  exact h ▸ (d x).2

theorem mchart_succ {m : ℕ} {n : Fin (m + 2) → ℕ} (c : ∀ k, Bk n k) :
    mchart c = pullback.fst (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓
      pullback.snd (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ
        mchart (n := Fin.tail n) (fun k => c k.succ) := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ⟨fun hx => ?_, ?_⟩)
  · exact ⟨Set.mem_iInter.1 hx 0, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k.succ⟩
  · rintro ⟨h0, h1⟩
    refine Set.mem_iInter.2 fun k => ?_
    induction k using Fin.cases with
    | zero => exact h0
    | succ k => exact Set.mem_iInter.1 h1 k

theorem add_one_pow_eq_ringHom_image_add_prime_mul_zero : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (W : (MP ℤ m n).Opens), W = mchart c →
    ∀ h : ∀ k, W ≤ blockChart n k (c k),
      IsAffineOpen W ∧ Subring.closure (Set.range (rtOn c W h)) = ⊤
  | 0, n, c, W, hW, h => by
    have e : W = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) := by
      rw [hW]
      refine TopologicalSpace.Opens.ext (Set.ext fun x => ⟨fun hx => Set.mem_iInter.1 hx 0, fun hx => ?_⟩)
      refine Set.mem_iInter.2 fun k => ?_
      obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact hx
    subst e
    refine ⟨isAffineOpen_chart ℤ (n 0) (c 0), ?_⟩
    refine eq_top_iff.2 fun x _ => ?_
    have hx : (x : Γ(PSpace ℤ (n 0), chart ℤ (n 0) (c 0))) ∈
        Subring.closure (Set.range (ratio ℤ (n 0) (c 0))) := by
      rw [closure_ratio]
      trivial
    refine Subring.closure_mono ?_ hx
    rintro _ ⟨j, rfl⟩
    exact ⟨⟨0, j⟩, (resG_self _ _)⟩
  | m + 1, n, c, W, hW, h => by
    obtain ⟨ha, hc⟩ := add_one_pow_eq_ringHom_image_add_prime_mul_zero m (Fin.tail n) (fun k => c k.succ) _ rfl (mchart_le _)
    have H := IsPullback.of_hasPullback (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n))
    obtain ⟨h1, h2⟩ := GlobalTheory.Conormal.isAffineOpen_and_isPushout H (U := ⊤) (isAffineOpen_top _) ha
      (isAffineOpen_chart ℤ (n 0) (c 0)) le_top le_top
    obtain rfl := hW.trans (mchart_succ c)
    refine ⟨h1, eq_top_of_isPushout h2 _ (fun x => ?_) (fun x => ?_)⟩
    · have hle : Subring.closure (Set.range (ratio ℤ (n 0) (c 0))) ≤
          (Subring.closure (Set.range (rtOn c _ h))).comap (Scheme.Hom.appLE
            (pullback.fst (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n))) (chart ℤ (n 0) (c 0)) _ inf_le_left).hom := by
        rw [Subring.closure_le]
        rintro _ ⟨j, rfl⟩
        exact Subring.subset_closure ⟨⟨0, j⟩, rfl⟩
      exact hle (closure_ratio (n 0) (c 0) ▸ Subring.mem_top x)
    · have hle : Subring.closure (Set.range (rtOn (n := Fin.tail n) (fun k => c k.succ) _ (mchart_le _))) ≤
          (Subring.closure (Set.range (rtOn c _ h))).comap (Scheme.Hom.appLE
            (pullback.snd (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)))
            (mchart (n := Fin.tail n) (fun k => c k.succ)) _ inf_le_right).hom := by
        rw [Subring.closure_le]
        rintro _ ⟨⟨k, j⟩, rfl⟩
        refine Subring.subset_closure ⟨⟨k.succ, j⟩, ?_⟩
        exact (appLE_pullRatio _ _).symm
      exact hle (hc ▸ Subring.mem_top x)

theorem gen (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) :
    IsAffineOpen (mchart c) ∧ Subring.closure (Set.range (rt c)) = ⊤ := by
  obtain ⟨h₁, h₂⟩ := add_one_pow_eq_ringHom_image_add_prime_mul_zero m n c _ rfl (mchart_le c)
  refine ⟨h₁, ?_⟩
  rw [← h₂]
  congr 2
  funext q
  exact resG_pullRatio _

theorem contDiffAt_zpow_of_ne' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (h0 : f x ≠ 0) (a : ℤ) : ContDiffAt ℝ ∞ (fun y => f y ^ a) x := by
  obtain ⟨b, rfl | rfl⟩ := a.eq_nat_or_neg
  · simpa only [zpow_natCast] using hf.pow b
  · simp only [zpow_neg, zpow_natCast]
    exact (hf.pow b).inv (pow_ne_zero b h0)

theorem contDiffOn_of_holo {ι : Type} [Fintype ι] {B : Set (ι → ℂ)} (hB : IsOpen B) {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f B) : ContDiffOn ℝ ∞ f B := by
  let e : (ι → ℂ) ≃L[ℂ] (Fin (Module.finrank ℂ (ι → ℂ)) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have ha : AnalyticOnNhd ℂ f B := by
    intro z hz
    have h := ReciprocityTheory.AnForm.Osgood.osgood _ (e.symm ⁻¹' B) (f ∘ e.symm)
      (hB.preimage e.symm.continuous)
      (hf.comp e.symm.differentiableOn (fun _ h => h)) (e z) (by simpa using hz)
    have h2 := h.comp (e.analyticAt z)
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hc : ContDiffOn ℂ ∞ f B := (ha.contDiffOn hB.uniqueDiffOn).of_le le_top
  exact hc.restrict_scalars ℝ

theorem mem_mchart {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : IsUnder y z)
    {c : ∀ k, Bk n k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) : y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  refine mem_ptsIn.2 (Set.mem_iInter.2 fun k => ?_)
  exact mem_ptsIn.1 ((H k (c k)).1.2 (hc k))

theorem ev_rt {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : IsUnder y z)
    {c : ∀ k, Bk n k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (q : Σ k, Bk n k) :
    CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) (rt c q) y = z q / z ⟨q.1, c q.1⟩ := by
  rw [rt, CxPts.ev_res _ (mem_mchart H hc)]
  exact (H q.1 (c q.1)).2 q.2 ((H q.1 (c q.1)).1.2 (hc q.1))

theorem differentiableOn_ev {c : ∀ k, Bk n k} {s : ((Σ k, Bk n k) → ℂ) → CxPts (mpStr ℤ m n) σ₀}
    (hs : ∀ z, (∀ k, z ⟨k, c k⟩ ≠ 0) → IsUnder (s z) z) (a : Γ(MP ℤ m n, mchart c)) :
    DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ s) {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
  have hin : ∀ z, (∀ k, z ⟨k, c k⟩ ≠ 0) → s z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    fun z hz => mem_mchart (hs z hz) hz
  have ha : a ∈ Subring.closure (Set.range (rt c)) := by
    rw [(gen m n c).2]; trivial
  induction ha using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    have hd : DifferentiableOn ℂ (fun z : (Σ k, Bk n k) → ℂ => z q * (z ⟨q.1, c q.1⟩)⁻¹)
        {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := fun z hz =>
      ((differentiableAt_apply (𝕜 := ℂ) q z).mul
        ((differentiableAt_apply (𝕜 := ℂ) _ z).inv (hz q.1))).differentiableWithinAt
    exact hd.congr fun z hz => (ev_rt (hs z hz) hz q).trans (div_eq_mul_inv _ _)
  | zero =>
    exact (differentiableOn_const 0).congr fun z hz => by
      simp only [Function.comp_apply, ev_eq (hin z hz), map_zero]
  | one =>
    exact (differentiableOn_const 1).congr fun z hz => by
      simp only [Function.comp_apply, ev_eq (hin z hz), map_one]
  | add x y _ _ hx hy =>
    exact (hx.add hy).congr fun z hz => by
      simp only [Function.comp_apply, Pi.add_apply, ev_add]
  | neg x _ hx =>
    exact hx.neg.congr fun z hz => by
      simp only [Function.comp_apply, Pi.neg_apply, ev_eq (hin z hz), map_neg]
  | mul x y _ _ hx hy =>
    exact (hx.mul hy).congr fun z hz => by
      simp only [Function.comp_apply, Pi.mul_apply, ev_mul]

theorem isSmoothHerm_of_isHermRep (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n))
    (A : Geo.HermLine (Bk n)) (hA : IsHermRep M A) : Geo.IsSmoothHerm A := by
  obtain ⟨u, -, -, hu⟩ := hA
  intro z₀ hz₀
  refine ContDiffAt.contDiffWithinAt ?_
  choose c hc using hz₀
  let T : Set ((Σ k, Bk n k) → ℂ) := {z | ∀ k, z ⟨k, c k⟩ ≠ 0}
  have hT : IsOpen T := by
    have : T = ⋂ k, {z | z ⟨k, c k⟩ ≠ 0} := by ext z; simp [T]
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
  have hmc : ∀ z ∈ T, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun z hz k => ⟨c k, hz k⟩
  haveI : Nonempty (CxPts (mpStr ℤ m n) σ₀) :=
    ⟨(Under.existsUnique_isUnder m n z₀ (hmc z₀ hc)).exists.choose⟩
  let s : ((Σ k, Bk n k) → ℂ) → CxPts (mpStr ℤ m n) σ₀ := fun z => Classical.epsilon fun y => IsUnder y z
  have hs : ∀ z, (∀ k, z ⟨k, c k⟩ ≠ 0) → IsUnder (s z) z := fun z hz =>
    Classical.epsilon_spec (Under.existsUnique_isUnder m n z (hmc z hz)).exists
  obtain ⟨hcont, hhol⟩ := holo_of_affine (gen m n c).1 hT (fun z hz => mem_mchart (hs z hz) hz)
    (differentiableOn_ev hs)
  have hsc : ContinuousAt s z₀ := hcont.continuousAt (hT.mem_nhds hc)
  obtain ⟨i, hi⟩ := exists_mem_ptsIn M.isLB.cover (s z₀)

  have hev : ∀ (W : (MP ℤ m n).Opens) (f : Γ(MP ℤ m n, W)), s z₀ ∈ ptsIn (mpStr ℤ m n) σ₀ W →
      ContDiffAt ℝ ∞ (fun z => CxPts.ev (mpStr ℤ m n) σ₀ W f (s z)) z₀ := by
    intro W f hW
    have hO : T ∩ s ⁻¹' ptsIn (mpStr ℤ m n) σ₀ W ∈ 𝓝 z₀ :=
      Filter.inter_mem (hT.mem_nhds hc) (hsc.preimage_mem_nhds ((isOpen_ptsIn W).mem_nhds hW))
    obtain ⟨B, hBs, hBo, hzB⟩ := mem_nhds_iff.1 hO
    exact (contDiffOn_of_holo hBo ((hhol W f).mono hBs)).contDiffAt (hBo.mem_nhds hzB)

  have hφ : ContDiffAt ℝ ∞ (fun z => (M.φ σ₀).φ i (s z)) z₀ := by
    obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := M.cInf σ₀ i (s z₀) hi
    have hg : ContDiffAt ℝ ∞ (fun z a => CxPts.ev (mpStr ℤ m n) σ₀ W (g a) (s z)) z₀ :=
      contDiffAt_pi.2 fun a => hev W (g a) h₁
    exact ((h₄.contDiffAt (h₂.mem_nhds h₃)).comp z₀ hg).congr_of_eventuallyEq (hsc.eventually h₅)
  have hiU : s z₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) :=
    mem_ptsIn_inf.2 ⟨hi, mem_mchart (hs z₀ hc) hc⟩
  have hU : ContDiffAt ℝ ∞ (fun z => ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)
      (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) (s z)‖) z₀ :=
    (hev _ _ hiU).norm ℝ (ev_ne_zero hiU (u i c).isUnit)
  have hP : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) z₀ := by
    refine contDiffAt_prod fun k _ => ?_
    have hn : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ‖z ⟨k, c k⟩‖) z₀ :=
      (contDiff_apply ℝ ℂ (⟨k, c k⟩ : Σ k, Bk n k)).contDiffAt.norm ℝ (hc k)
    exact contDiffAt_zpow_of_ne' hn (norm_ne_zero_iff.2 (hc k)) (A.a k)
  have hE : ContDiffAt ℝ ∞ (fun z => Real.exp ((M.φ σ₀).φ i (s z) / 2)) z₀ :=
    (hφ.div_const 2).exp
  refine ((hP.mul hU).mul hE).congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ z in 𝓝 z₀, z ∈ T ∧ s z ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i) :=
    (hT.eventually_mem hc).and (hsc.eventually ((isOpen_ptsIn _).eventually_mem hi))
  filter_upwards [hmem] with z hz
  exact hu i c (s z) z (hs z hz.1) (mem_ptsIn_inf.2 ⟨hz.2, mem_mchart (hs z hz.1) hz.1⟩)

end GlobalTheory.CompanionTheory.MPDict.SmoothRep
