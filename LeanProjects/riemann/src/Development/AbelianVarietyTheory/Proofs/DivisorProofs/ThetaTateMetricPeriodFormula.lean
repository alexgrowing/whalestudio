import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open GlobalTheory.Points (PtsOver)
open MonObj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ThetaDoubling

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k}

theorem ex_dbl (P : PPAS S) {h : VMetric p (omega P.A) P.g} {σ : k →+* ℂ} {c : AlgChart p σ 1}
    {τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ} {ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ}
    (hc : IsPeriodChart h c τ ex) {v : V 1} (hv : v ∈ c.e.target) (z : Fin P.g → ℂ) :
    ex (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 (v, z)) = PtsOver.map (dbl P) (dbl_comp P p) _ (ex (v, z)) := by
  obtain ⟨-, -, H⟩ := hc
  obtain ⟨h1, h2, -, -, -⟩ := H v hv
  let x : Over.mk (c.e.symm v).1 ⟶ P.A := Over.homMk (ex (v, z)).1 (h1 z)
  have e := h2 z z x x rfl rfl
  have e2 : x ≫ ReciprocityTheory.ChartRestriction.G.Out.mulA P.A 2 = x * x := by
    rw [ReciprocityTheory.ChartRestriction.G.Out.mulA, MonObj.comp_pow, Category.comp_id, pow_two]
  apply Subtype.ext
  change (ex (v, (2:ℤ) • z)).1 = (ex (v, z)).1 ≫ dbl P
  have : (2:ℤ) • z = z + z := by rw [two_zsmul]
  rw [this, ← e, ← e2]
  rfl

theorem ex_transl (P : PPAS S) {h : VMetric p (omega P.A) P.g} {σ : k →+* ℂ} {c : AlgChart p σ 1}
    {τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ} {ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ}
    (hc : IsPeriodChart h c τ ex) {v : V 1} (hv : v ∈ c.e.target) (z : Fin P.g → ℂ)
    {l : Fl P.g} (hl : l ∈ stdLat P.g) :
    ex (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ l (v, z)) = ex (v, z) := by
  obtain ⟨-, -, H⟩ := hc
  obtain ⟨h1, h2, -, h4, -⟩ := H v hv
  let x : Over.mk (c.e.symm v).1 ⟶ P.A := Over.homMk (ex (v, z)).1 (h1 z)
  have hy : (1 : Over.mk (c.e.symm v).1 ⟶ P.A).left = (ex (v, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.per (τ v) l)).1 := by
    rw [(h4 _).2 ⟨l, hl, rfl⟩]
    rfl
  have e := h2 z _ x 1 rfl hy
  apply Subtype.ext
  change (ex (v, z + GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.per (τ v) l)).1 = (ex (v, z)).1
  rw [← e, _root_.mul_one]
  rfl

theorem alg4 {x y g G F F' : ℂ} (hg : g ≠ 0) (h : x * G = g ^ 4 * y) :
    x * (G * F) / (g * F') ^ 4 = y * F / F' ^ 4 := by
  calc x * (G * F) / (g * F') ^ 4 = (x * G) * F / (g ^ 4 * F' ^ 4) := by ring
    _ = g ^ 4 * (y * F) / (g ^ 4 * F' ^ 4) := by rw [h]; ring
    _ = y * F / F' ^ 4 := mul_div_mul_left _ _ (pow_ne_zero 4 hg)

theorem alg5 {x A B J J2 : ℂ} (hJ : J ≠ 0) :
    x * A / B ^ 4 * J2 = J ^ 4 * (x * (J2 * A) / (J * B) ^ 4) := by
  rw [mul_pow, ← mul_div_assoc, mul_div_mul_left _ _ (pow_ne_zero 4 hJ)]
  ring

theorem alg6 {Fa Fb Xv : ℂ} {φa φb ua ub : ℝ} (hX : Xv ≠ 0) (hFa : Fa ≠ 0)
    (h : 4 * φa + 4 * ua = φb + ub + Real.log (‖Xv‖ ^ 2)) :
    ‖Fb‖ ^ 2 * Real.exp (-φb) * Real.exp (-ub) =
      (‖Fa‖ ^ 2 * Real.exp (-φa) * Real.exp (-ua)) ^ 4 * ‖Xv * Fb / Fa ^ 4‖ ^ 2 := by
  have hX2 : 0 < ‖Xv‖ ^ 2 := by positivity
  have key : Real.exp (-φb) * Real.exp (-ub) = Real.exp (-φa) ^ 4 * Real.exp (-ua) ^ 4 * ‖Xv‖ ^ 2 := by
    rw [← Real.exp_log hX2, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    push_cast
    linarith
  have hFa' : ‖Fa‖ ≠ 0 := norm_ne_zero_iff.2 hFa
  calc ‖Fb‖ ^ 2 * Real.exp (-φb) * Real.exp (-ub) = ‖Fb‖ ^ 2 * (Real.exp (-φb) * Real.exp (-ub)) := by ring
    _ = ‖Fb‖ ^ 2 * (Real.exp (-φa) ^ 4 * Real.exp (-ua) ^ 4 * ‖Xv‖ ^ 2) := by rw [key]
    _ = _ := by
      rw [norm_div, norm_mul, norm_pow]
      field_simp

theorem mulN_transl {g : ℕ} (τ : V 1 → Matrix (Fin g) (Fin g) ℂ) (l : Fl g) (Q : Pt (V 1) g) :
    GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ l Q) =
      GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ ((2:ℤ) • l) (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 Q) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.per, smul_add]
  refine Prod.ext rfl ?_
  simp only [add_right_inj]
  ext i
  simp [Matrix.vecMul, dotProduct, Finset.mul_sum]
  ring_nf

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (mulN transl per mulPullFactor IsBundleIso) in

theorem exists_bundleIso_doubling : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S), IsArithVar (P.A.hom ≫ p) (P.g + 1) → ∀ (h : VMetric p (omega P.A) P.g) (L : HermLB (P.A.hom ≫ p)), IsTheta P L.B → ∀ (w : LB.Iso (L.pull (dbl P) (dbl_comp P p)).B (L.pow 4).B), w.IsGen → ∀ u : ∀ σ : k →+* ℂ, CxPts (P.A.hom ≫ p) σ → ℝ, IsTate (dbl P) (dbl_comp P p) L w u → ∀ (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ) (m : Pt (V 1) P.g → ℝ), IsPeriodChart h c τ ex → IsFramed L c.e.target τ ex j m → IsDatum c.e.target τ (stdLat P.g) j m → ∀ v ∈ c.e.target, ∃ B' ⊆ c.e.target, IsOpen B' ∧ v ∈ B' ∧ ∃ φ, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsBundleIso B' τ (stdLat P.g) (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulPullFactor 2 j) (fun l Q => j l Q ^ 4) φ ∧ ∀ Q ∈ cov B' P.g, m (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 Q) * Real.exp (-u σ (ex (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 Q))) = (m Q * Real.exp (-u σ (ex Q))) ^ 4 * ‖φ Q‖ ^ 2 := by
  intro k _ S p _ P _ h L _ w hw u hT σ c τ ex j m hc hF _ v hv
  refine ⟨c.e.target, subset_rfl, hc.1.1, hv, ?_⟩
  obtain ⟨fr, hfr⟩ := hF
  set dm : CxPts (P.A.hom ≫ p) σ → CxPts (P.A.hom ≫ p) σ :=
    PtsOver.map (dbl P) (dbl_comp P p) _ with hdm
  have hcov : ∀ Q : Pt (V 1) P.g, Q ∈ cov c.e.target P.g ↔ Q.1 ∈ c.e.target := fun Q => by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.cov]
  have ex2 : ∀ Q ∈ cov c.e.target P.g, ex (mulN 2 Q) = dm (ex Q) := fun Q hQ =>
    ex_dbl P hc ((hcov Q).1 hQ) Q.2
  have mp4 : ∀ (y : CxPts (P.A.hom ≫ p) σ) (a : L.B.ι),
      y ∈ ptsIn _ σ ((L.pow 4).B.U (fun _ => a)) ↔ y ∈ ptsIn _ σ (L.B.U a) := fun y a => mem_pow_iff
  have mpl : ∀ (y : CxPts (P.A.hom ≫ p) σ) (b : L.B.ι),
      y ∈ ptsIn _ σ ((L.pull (dbl P) (dbl_comp P p)).B.U (fun _ => b)) ↔ dm y ∈ ptsIn _ σ (L.B.U b) := by
    intro y b
    refine ⟨fun hy => mem_of_mem_linComb (m := fun _ => dm y) (fun _ => rfl) hy PUnit.unit, fun hy => ?_⟩
    intro z hz
    exact Set.mem_iInter.2 fun _ => hy hz
  let X : (PUnit → L.B.ι) → (PUnit → L.B.ι) → CxPts (P.A.hom ≫ p) σ → ℂ := fun a b y =>
    ev (P.A.hom ≫ p) σ _ (w.s (a, b)).val y
  have K : ∀ Q ∈ cov c.e.target P.g, ∀ a b a' b', ex Q ∈ ptsIn _ σ (L.B.U a) →
      ex Q ∈ ptsIn _ σ (L.B.U a') → dm (ex Q) ∈ ptsIn _ σ (L.B.U b) → dm (ex Q) ∈ ptsIn _ σ (L.B.U b') →
      X (fun _ => a) (fun _ => b) (ex Q) * fr b (mulN 2 Q) / fr a Q ^ 4 =
        X (fun _ => a') (fun _ => b') (ex Q) * fr b' (mulN 2 Q) / fr a' Q ^ 4 := by
    intro Q hQ a b a' b' ha ha' hb hb'
    have hQ2 : mulN 2 Q ∈ cov c.e.target P.g := (hcov _).2 ((hcov _).1 hQ)
    have e2 := ex2 Q hQ
    have rel := ev_iso_rel hw ((mpl _ b).2 hb) ((mpl _ b').2 hb') ((mp4 _ a).2 ha) ((mp4 _ a').2 ha')
    have g1 : gv (P.A.hom ≫ p) σ (L.pull (dbl P) (dbl_comp P p)).B (fun _ => b) (fun _ => b') (ex Q) =
        gv (P.A.hom ≫ p) σ L.B b b' (dm (ex Q)) :=
      (gv_linComb (m := fun _ => dm (ex Q)) (fun _ => rfl) ((mpl _ b).2 hb) ((mpl _ b').2 hb')).trans
        (by simp)
    have g4 : gv (P.A.hom ≫ p) σ (L.pow 4).B (fun _ => a) (fun _ => a') (ex Q) =
        gv (P.A.hom ≫ p) σ L.B a a' (ex Q) ^ 4 := (gv_pow ha ha').trans (by simp)
    rw [g1, g4] at rel
    have hfa := ((hfr a).2 Q hQ ha).2.1 a' ha'
    have hfb := ((hfr b).2 _ hQ2 (e2 ▸ hb)).2.1 b' (e2 ▸ hb')
    rw [e2] at hfb
    have hga := gv_ne_zero ha ha'
    have hfa' := ((hfr a').2 Q hQ ha').1
    have rel' : X (fun _ => a) (fun _ => b) (ex Q) * gv (P.A.hom ≫ p) σ L.B b b' (dm (ex Q)) =
        gv (P.A.hom ≫ p) σ L.B a a' (ex Q) ^ 4 * X (fun _ => a') (fun _ => b') (ex Q) := rel
    rw [hfa, hfb]
    exact alg4 hga rel'
  have hpk : ∀ y : CxPts (P.A.hom ≫ p) σ, y ∈ ptsIn _ σ (L.B.U (pick L.isLB y)) := fun y => mem_pick L.isLB y
  let F : Pt (V 1) P.g → ℂ := fun Q =>
    X (fun _ => pick L.isLB (ex Q)) (fun _ => pick L.isLB (dm (ex Q))) (ex Q) *
      fr (pick L.isLB (dm (ex Q))) (mulN 2 Q) / fr (pick L.isLB (ex Q)) Q ^ 4
  have KF : ∀ Q ∈ cov c.e.target P.g, ∀ a b, ex Q ∈ ptsIn _ σ (L.B.U a) →
      dm (ex Q) ∈ ptsIn _ σ (L.B.U b) →
      F Q = X (fun _ => a) (fun _ => b) (ex Q) * fr b (mulN 2 Q) / fr a Q ^ 4 := fun Q hQ a b ha hb =>
    K Q hQ _ _ a b (hpk _) ha (hpk _) hb
  have hXne : ∀ (y : CxPts (P.A.hom ≫ p) σ) a b, y ∈ ptsIn _ σ (L.B.U a) → dm y ∈ ptsIn _ σ (L.B.U b) →
      X (fun _ => a) (fun _ => b) y ≠ 0 :=
    fun y a b ha hb => ev_iso_ne_zero w ((mpl _ b).2 hb) ((mp4 _ a).2 ha)
  have hQ2 : ∀ Q ∈ cov c.e.target P.g, mulN 2 Q ∈ cov c.e.target P.g := fun Q hQ =>
    (hcov _).2 ((hcov _).1 hQ)
  have hmd : Differentiable ℂ (mulN 2 : Pt (V 1) P.g → Pt (V 1) P.g) := by
    show Differentiable ℂ (fun Q : Pt (V 1) P.g => (Q.1, (2:ℤ) • Q.2))
    exact differentiable_fst.prodMk (differentiable_snd.const_smul (2:ℤ))
  refine ⟨F, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro Q0 hQ0
    obtain ⟨hO, hXd⟩ := hc.2.1
      (((L.pow 4).B.div (L.pull (dbl P) (dbl_comp P p)).B).U
        ((fun _ => pick L.isLB (ex Q0)), (fun _ => pick L.isLB (dm (ex Q0)))))
      (w.s ((fun _ => pick L.isLB (ex Q0)), (fun _ => pick L.isLB (dm (ex Q0))))).val
    set a := pick L.isLB (ex Q0)
    set b := pick L.isLB (dm (ex Q0))
    set O := {Q ∈ cov c.e.target P.g | ⊤ ≤ (ex Q).1 ⁻¹ᵁ
      (((L.pow 4).B.div (L.pull (dbl P) (dbl_comp P p)).B).U ((fun _ => a), (fun _ => b)))} with hOdef
    have hmem : ∀ Q ∈ O, Q ∈ cov c.e.target P.g ∧ ex Q ∈ ptsIn _ σ (L.B.U a) ∧
        dm (ex Q) ∈ ptsIn _ σ (L.B.U b) := by
      intro Q hQ
      have h2 : ex Q ∈ ptsIn _ σ (((L.pow 4).B.div (L.pull (dbl P) (dbl_comp P p)).B).U
        ((fun _ => a), (fun _ => b))) := hQ.2
      have h3 := mem_ptsIn_inf.1 h2
      exact ⟨hQ.1, (mp4 _ a).1 h3.1, (mpl _ b).1 h3.2⟩
    have hQ0O : Q0 ∈ O := by
      refine ⟨hQ0, ?_⟩
      show ex Q0 ∈ ptsIn _ σ (((L.pow 4).B.div (L.pull (dbl P) (dbl_comp P p)).B).U
        ((fun _ => a), (fun _ => b)))
      exact mem_ptsIn_inf.2 ⟨(mp4 _ a).2 (hpk _), (mpl _ b).2 (hpk _)⟩
    have hXd' : DifferentiableOn ℂ (fun Q => X (fun _ => a) (fun _ => b) (ex Q)) O := hXd
    have hfb : DifferentiableOn ℂ (fun Q => fr b (mulN 2 Q)) O := by
      refine (hfr b).1.comp hmd.differentiableOn fun Q hQ => ?_
      obtain ⟨h1, -, h3⟩ := hmem Q hQ
      refine ⟨hQ2 Q h1, ?_⟩
      show ex (mulN 2 Q) ∈ ptsIn _ σ (L.B.U b)
      rw [ex2 Q h1]
      exact h3
    have hfa : DifferentiableOn ℂ (fun Q => fr a Q) O :=
      (hfr a).1.mono fun Q hQ => ⟨(hmem Q hQ).1, (hmem Q hQ).2.1⟩
    have hG : DifferentiableOn ℂ (fun Q => X (fun _ => a) (fun _ => b) (ex Q) * fr b (mulN 2 Q) / fr a Q ^ 4) O :=
      ((hXd'.mul hfb).mul ((hfa.fun_pow 4).inv fun Q hQ =>
        pow_ne_zero 4 ((hfr a).2 Q (hmem Q hQ).1 (hmem Q hQ).2.1).1)).congr fun Q _ => div_eq_mul_inv _ _
    refine ((hG.differentiableAt (hO.mem_nhds hQ0O)).congr_of_eventuallyEq ?_).differentiableWithinAt
    exact Filter.eventually_of_mem (hO.mem_nhds hQ0O) fun Q hQ =>
      KF Q (hmem Q hQ).1 a b (hmem Q hQ).2.1 (hmem Q hQ).2.2
  · intro Q hQ
    have hb : ex (mulN 2 Q) ∈ ptsIn _ σ (L.B.U (pick L.isLB (dm (ex Q)))) := by
      rw [ex2 Q hQ]; exact hpk _
    exact div_ne_zero (mul_ne_zero (hXne _ _ _ (hpk _) (hpk _)) ((hfr _).2 _ (hQ2 Q hQ) hb).1)
      (pow_ne_zero 4 ((hfr _).2 Q hQ (hpk _)).1)
  · intro l hl Q hQ
    have et : ex (transl τ l Q) = ex Q := ex_transl P hc ((hcov Q).1 hQ) Q.2 hl
    have hQt : transl τ l Q ∈ cov c.e.target P.g := (hcov _).2 ((hcov _).1 hQ)
    have ha : ex Q ∈ ptsIn _ σ (L.B.U (pick L.isLB (ex Q))) := hpk _
    have hb : dm (ex Q) ∈ ptsIn _ σ (L.B.U (pick L.isLB (dm (ex Q)))) := hpk _
    have hb2 : ex (mulN 2 Q) ∈ ptsIn _ σ (L.B.U (pick L.isLB (dm (ex Q)))) := by
      rw [ex2 Q hQ]; exact hb
    rw [KF (transl τ l Q) hQt (pick L.isLB (ex Q)) (pick L.isLB (dm (ex Q))) (by rw [et]; exact ha)
      (by rw [et]; exact hb), et, mulN_transl τ l Q]
    have e2l := ((hfr _).2 _ (hQ2 Q hQ) hb2).2.2.2 _ ((stdLat P.g).smul_mem (2:ℤ) hl)
    have e1l := ((hfr _).2 Q hQ ha).2.2.2 l hl
    have hne := ((hfr _).2 Q hQ ha).1
    rw [e1l] at hne
    show _ = j l Q ^ 4 * (X _ _ (ex Q) * fr (pick L.isLB (dm (ex Q))) (mulN 2 Q) /
      fr (pick L.isLB (ex Q)) Q ^ 4)
    rw [e2l, e1l]
    exact alg5 (left_ne_zero_of_mul hne)
  · intro Q hQ
    have ha : ex Q ∈ ptsIn _ σ (L.B.U (pick L.isLB (ex Q))) := hpk _
    have hb : dm (ex Q) ∈ ptsIn _ σ (L.B.U (pick L.isLB (dm (ex Q)))) := hpk _
    have hb2 : ex (mulN 2 Q) ∈ ptsIn _ σ (L.B.U (pick L.isLB (dm (ex Q)))) := by
      rw [ex2 Q hQ]; exact hb
    have hm2 := ((hfr _).2 _ (hQ2 Q hQ) hb2).2.2.1
    have hm1 := ((hfr _).2 Q hQ ha).2.2.1
    have ht := hT σ (fun _ => pick L.isLB (ex Q)) (fun _ => pick L.isLB (dm (ex Q))) (ex Q)
      ((mp4 _ _).2 ha) ((mpl _ _).2 hb)
    have e1 : ((L.pow 4).φ σ).φ (fun _ => pick L.isLB (ex Q)) (ex Q) =
        4 * (L.φ σ).φ (pick L.isLB (ex Q)) (ex Q) :=
      ((L.φ σ).zpow_φ _ _ (ex Q)).trans (by push_cast; ring)
    have e2 : ((L.pull (dbl P) (dbl_comp P p)).φ σ).φ (fun _ => pick L.isLB (dm (ex Q))) (ex Q) =
        (L.φ σ).φ (pick L.isLB (dm (ex Q))) (dm (ex Q)) := (L.φ σ).pull_φ _ _ _ _
    rw [e1, e2] at ht
    rw [hm2, hm1, ex2 Q hQ]
    exact alg6 (hXne _ _ _ ha hb) ((hfr _).2 Q hQ ha).1 ht

end GlobalTheory.ThetaDoubling
