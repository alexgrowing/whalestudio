import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodChartDualRiemannStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicLogOnConvex
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormFderivLeOfClosedBallSubset
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat IsMetric cov IsFactor IsPeriodMap transl per)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

namespace GlobalTheory.DoublingFrame

section Analysis

open Metric Asymptotics

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [FiniteDimensional ℂ F]

theorem exists_sub_le_cube {O : Set (E × F)} {v₀ : E} {φ : E × F → ℂ} (hO : IsOpen O) (h0 : (v₀, (0 : F)) ∈ O)
    (hφ : DifferentiableOn ℂ φ O) : ∃ (r : ℝ) (q : E × F → ℂ), 0 < r ∧ ball v₀ r ×ˢ ball (0 : F) r ⊆ O ∧
      DifferentiableOn ℂ q (ball v₀ r ×ˢ univ) ∧
      ∀ P ∈ ball v₀ r ×ˢ ball (0 : F) r, ‖φ P - q P‖ ≤ (‖P.2‖ / r) ^ 3 := by
  have ha := SCV.analyticOnNhd_of_differentiableOn hO hφ
  let q : E × F → ℂ := fun P => ∑ n ∈ Finset.range 3,
    (n.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ n φ (P.1, 0) fun _ => (0, P.2)
  have hq (P : E × F) (hP : (P.1, (0 : F)) ∈ O) : DifferentiableAt ℂ q P := by
    refine DifferentiableAt.fun_sum fun n _ => DifferentiableAt.const_mul ?_ _
    have h1 : DifferentiableAt ℂ (fun P : E × F => iteratedFDeriv ℂ n φ (P.1, 0)) P :=
      DifferentiableAt.comp (g := iteratedFDeriv ℂ n φ) P (ha.iteratedFDeriv n _ hP).differentiableAt
        (by fun_prop)
    have h2 : DifferentiableAt ℂ (fun (P : E × F) (_ : Fin n) => ((0 : E), P.2)) P := by fun_prop
    exact ((ContinuousLinearMap.id ℂ _).analyticAt_uncurry_of_multilinear.differentiableAt).comp P
      (h1.prodMk h2)
  have hO3 (v : E) (hv : (v, (0 : F)) ∈ O) :
      (fun z : F => φ (v, z) - q (v, z)) =O[𝓝 0] fun z => ‖z‖ ^ 3 := by
    obtain ⟨p, ρ, hp⟩ := ha _ hv
    have ht : Tendsto (fun z : F => ((0 : E), z)) (𝓝 0) (𝓝 0) := Continuous.tendsto' (by fun_prop) _ _ rfl
    refine ((hp.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 3).comp_tendsto ht).congr (fun z => ?_) fun z => ?_
    · simp only [Function.comp_apply, Prod.mk_add_mk, add_zero, zero_add, FormalMultilinearSeries.partialSum, q]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← hp.factorial_smul, nsmul_eq_mul, inv_mul_cancel_left₀ (by exact_mod_cast n.factorial_ne_zero)]
    · simp
  have hz (v : E) (hv : (v, (0 : F)) ∈ O) : φ (v, 0) - q (v, 0) = 0 := by
    simpa using (hO3 v hv).eq_zero_imp.self_of_nhds
  have hc : ContinuousAt (fun P => φ P - q P) (v₀, 0) :=
    (hφ.continuousOn.continuousAt (hO.mem_nhds h0)).sub (hq _ h0).continuousAt
  have hev : ∀ᶠ P in 𝓝 (v₀, (0 : F)), P ∈ O ∧ φ P - q P ∈ closedBall (0 : ℂ) 1 :=
    (show ∀ᶠ P in 𝓝 (v₀, (0 : F)), P ∈ O from hO.mem_nhds h0).and
      (hc.eventually (show ∀ᶠ t in 𝓝 (φ (v₀, 0) - q (v₀, 0)), t ∈ closedBall (0 : ℂ) 1 by
        rw [hz v₀ h0]; exact closedBall_mem_nhds _ one_pos))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 hev
  rw [← ball_prod_same] at hb
  have hv0 {v : E} (hv : v ∈ ball v₀ r) : (v, (0 : F)) ∈ O := (hb _ ⟨hv, mem_ball_self hr⟩).1
  refine ⟨r, q, hr, fun P hP => (hb P hP).1, fun P hP => (hq P (hv0 hP.1)).differentiableWithinAt,
    fun P hP => ?_⟩
  have := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (f := fun z => φ (P.1, z) - q (P.1, z))
    (c := 0) (z := P.2) (R₁ := r) (R₂ := 1) (n := 2) (fun z hz' => ?_) (fun z hz' => ?_) ?_ hP.2
  · simpa [hz _ (hv0 hP.1)] using this
  · have hzO := (hb (P.1, z) ⟨hP.1, hz'⟩).1
    exact (((hφ.differentiableAt (hO.mem_nhds hzO)).sub (hq (P.1, z) (hv0 hP.1))).comp z
      (by fun_prop : DifferentiableAt ℂ (fun z : F => (P.1, z)) z)).differentiableWithinAt
  · simpa only [hz _ (hv0 hP.1)] using (hb (P.1, z) ⟨hP.1, hz'⟩).2
  · simpa only [hz _ (hv0 hP.1), sub_zero] using
      (hO3 _ (hv0 hP.1)).trans_isLittleO (isLittleO_norm_pow_norm_pow (Nat.lt_succ_self 2))

theorem exists_half_solution {O : Set (E × F)} {v₀ : E} {φ : E × F → ℂ} (hO : IsOpen O) (h0 : (v₀, (0 : F)) ∈ O)
    (hφ : DifferentiableOn ℂ φ O) : ∃ (r : ℝ) (ψ q : E × F → ℂ), 0 < r ∧ ball v₀ r ×ˢ ball (0 : F) r ⊆ O ∧
      DifferentiableOn ℂ ψ (ball v₀ r ×ˢ ball (0 : F) r) ∧ DifferentiableOn ℂ q (ball v₀ r ×ˢ univ) ∧
      ∀ P ∈ ball v₀ r ×ˢ ball (0 : F) r, ψ P + q P = 4 * ψ (P.1, (2 : ℂ)⁻¹ • P.2) + φ P := by
  obtain ⟨r, q, hr, hs, hq, hb⟩ := exists_sub_le_cube hO h0 hφ
  let t : ℕ → E × F → ℂ := fun n P => 4 ^ n * (φ (P.1, (2 : ℂ)⁻¹ ^ n • P.2) - q (P.1, (2 : ℂ)⁻¹ ^ n • P.2))
  have hn (n : ℕ) (z : F) : ‖(2 : ℂ)⁻¹ ^ n • z‖ = 2⁻¹ ^ n * ‖z‖ := by simp [norm_smul]
  have hm (n : ℕ) : MapsTo (fun P : E × F => (P.1, (2 : ℂ)⁻¹ ^ n • P.2)) (ball v₀ r ×ˢ ball 0 r)
      (ball v₀ r ×ˢ ball 0 r) := fun P hP => ⟨hP.1, by
    rw [mem_ball_zero_iff, hn]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))).trans_lt
      (mem_ball_zero_iff.1 hP.2)⟩
  have hle (n : ℕ) (P) (hP : P ∈ ball v₀ r ×ˢ ball (0 : F) r) : ‖t n P‖ ≤ (1 / 2) ^ n := by
    have h1 : ‖P.2‖ / r ≤ 1 := (div_le_one hr).2 (mem_ball_zero_iff.1 hP.2).le
    calc ‖t n P‖ ≤ 4 ^ n * (2⁻¹ ^ n * (‖P.2‖ / r)) ^ 3 := by
          have := hb _ (hm n hP)
          rw [hn, mul_div_assoc] at this
          simp only [t, norm_mul, norm_pow, Complex.norm_ofNat]
          gcongr
      _ ≤ 4 ^ n * (2⁻¹ ^ n * 1) ^ 3 := by gcongr
      _ = (1 / 2) ^ n := by rw [mul_one, ← pow_mul, mul_comm n, pow_mul, ← mul_pow]; norm_num
  refine ⟨r, fun P => ∑' n, t n P, q, hr, hs, differentiableOn_tsum_of_norm_le _ _ _ t _
    (isOpen_ball.prod isOpen_ball) (fun n => ?_) summable_geometric_two hle, hq, fun P hP => ?_⟩
  · exact (((hφ.mono hs).sub (hq.mono (prod_mono le_rfl (subset_univ _)))).comp (by fun_prop) (hm n)).const_mul _
  · have hsum := Summable.of_norm_bounded summable_geometric_two fun n => hle n P hP
    have e (n : ℕ) : t (n + 1) P = 4 * t n (P.1, (2 : ℂ)⁻¹ • P.2) := by
      simp only [t, smul_smul, pow_succ]; ring
    simp only
    rw [hsum.tsum_eq_zero_add, ← tsum_mul_left, tsum_congr e]
    simp only [t, pow_zero, one_smul]
    ring

end Analysis

theorem exists_frame_iUnion {X J : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {Ω : Set X} (S : ℕ → Set X)
    (U : J → Set X) (c G : J → J → X → ℂ) (h : X → X) (f₀ : J → X → ℂ) (hS : ∀ n, IsOpen (S n))
    (hmono : Monotone S) (hΩ : Ω = ⋃ n, S n) (hU : ∀ i, IsOpen (Ω ∩ U i)) (hcov : ∀ P ∈ Ω, ∃ i, P ∈ U i)
    (hd : Differentiable ℂ h) (hm : ∀ n, MapsTo h (S (n + 1)) (S n)) (hm0 : MapsTo h (S 0) (S 0))
    (hc : ∀ i, ∀ P ∈ Ω ∩ U i, c i i P = 1)
    (hG : ∀ b a, DifferentiableOn ℂ (G b a) (Ω ∩ U b ∩ h ⁻¹' U a) ∧ ∀ Q ∈ Ω ∩ U b ∩ h ⁻¹' U a, G b a Q ≠ 0)
    (hGc : ∀ b a b' a', ∀ Q ∈ Ω, Q ∈ U b → Q ∈ U b' → h Q ∈ U a → h Q ∈ U a' →
      G b a Q * c a a' (h Q) ^ 4 = c b b' Q * G b' a' Q)
    (hf₀ : ∀ i, DifferentiableOn ℂ (f₀ i) (S 0 ∩ U i) ∧ ∀ P ∈ S 0 ∩ U i, f₀ i P ≠ 0 ∧
      (∀ j, P ∈ U j → f₀ i P = c i j P * f₀ j P) ∧ ∀ a, h P ∈ U a → f₀ i P = G i a P * f₀ a (h P) ^ 4) :
    ∃ f : J → X → ℂ, ∀ i, DifferentiableOn ℂ (f i) (Ω ∩ U i) ∧
      ∀ P ∈ Ω ∩ U i, f i P ≠ 0 ∧ ∀ j, P ∈ U j → f i P = c i j P * f j P := by
  classical
  have hSΩ (n) : S n ⊆ Ω := hΩ ▸ subset_iUnion S n
  have hSU (n i) : IsOpen (S n ∩ U i) := by
    have := (hS n).inter (hU i)
    rwa [← inter_assoc, inter_eq_left.2 (hSΩ n)] at this
  choose a ha using hcov
  let T : (J → X → ℂ) → J → X → ℂ := fun f b Q =>
    if hQ : h Q ∈ Ω then G b (a _ hQ) Q * f (a _ hQ) (h Q) ^ 4 else 0
  let f : ℕ → J → X → ℂ := fun n => T^[n] f₀
  have hf (n b Q) (hQ : h Q ∈ Ω) : f (n + 1) b Q = G b (a _ hQ) Q * f n (a _ hQ) (h Q) ^ 4 := by
    simp only [f, Function.iterate_succ_apply', T, dif_pos hQ]
  have key (n) : ∀ i, DifferentiableOn ℂ (f n i) (S n ∩ U i) ∧
      ∀ P ∈ S n ∩ U i, f n i P ≠ 0 ∧ ∀ j, P ∈ U j → f n i P = c i j P * f n j P := by
    induction n with
    | zero => exact fun i => ⟨(hf₀ i).1, fun P hP => ⟨((hf₀ i).2 P hP).1, ((hf₀ i).2 P hP).2.1⟩⟩
    | succ n ih =>
      intro b
      refine ⟨fun Q hQ => ?_, fun Q hQ => ?_⟩
      · have hQ' := hm n hQ.1
        set a' := a _ (hSΩ n hQ')
        have ho : IsOpen (S (n + 1) ∩ U b ∩ h ⁻¹' (S n ∩ U a')) :=
          (hSU _ _).inter ((hSU _ _).preimage hd.continuous)
        have hd' : DifferentiableOn ℂ (fun R => G b a' R * f n a' (h R) ^ 4)
            (S (n + 1) ∩ U b ∩ h ⁻¹' (S n ∩ U a')) :=
          ((hG b a').1.mono fun R hR => ⟨⟨hSΩ _ hR.1.1, hR.1.2⟩, hR.2.2⟩).mul
            (((ih a').1.comp hd.differentiableOn fun R hR => hR.2).pow 4)
        refine ((hd'.congr fun R hR => ?_).differentiableAt
          (ho.mem_nhds ⟨hQ, hQ', ha _ _⟩)).differentiableWithinAt
        have hR' := hSΩ n hR.2.1
        have e := hGc b _ b a' R (hSΩ _ hR.1.1) hR.1.2 hR.1.2 (ha _ hR') hR.2.2
        rw [hc b R ⟨hSΩ _ hR.1.1, hR.1.2⟩, one_mul] at e
        rw [hf n b R hR', (((ih _).2 _ ⟨hR.2.1, ha _ hR'⟩).2 a' hR.2.2), mul_pow, ← mul_assoc, e]
      · have hQ' := hm n hQ.1
        have hQ'' := hSΩ n hQ'
        refine ⟨?_, fun j hj => ?_⟩
        · rw [hf n b Q hQ'']
          exact mul_ne_zero ((hG _ _).2 Q ⟨⟨hSΩ _ hQ.1, hQ.2⟩, ha _ hQ''⟩)
            (pow_ne_zero _ ((ih _).2 _ ⟨hQ', ha _ hQ''⟩).1)
        · have e := hGc b _ j _ Q (hSΩ _ hQ.1) hQ.2 hj (ha _ hQ'') (ha _ hQ'')
          rw [hc _ _ ⟨hQ'', ha _ hQ''⟩, one_pow, mul_one] at e
          rw [hf n b Q hQ'', hf n j Q hQ'', e, mul_assoc]
  have step (n) : ∀ i, ∀ P ∈ S n ∩ U i, f (n + 1) i P = f n i P := by
    induction n with
    | zero =>
      intro i P hP
      rw [hf 0 i P (hSΩ 0 (hm0 hP.1))]
      exact (((hf₀ i).2 P hP).2.2 _ (ha _ _)).symm
    | succ n ih =>
      intro i P hP
      have hP' := hSΩ n (hm n hP.1)
      rw [hf _ i P hP', hf _ i P hP', ih _ _ ⟨hm n hP.1, ha _ _⟩]
  have agree {n m} (hnm : n ≤ m) (i P) (hP : P ∈ S n ∩ U i) : f m i P = f n i P := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih => rw [step m i P ⟨hmono hnm hP.1, hP.2⟩, ih]
  have hN : ∀ P ∈ Ω, ∃ n, P ∈ S n := fun P hP => mem_iUnion.1 (hΩ ▸ hP)
  choose! N hN using hN
  refine ⟨fun i P => f (N P) i P, fun i => ⟨fun P hP => ?_, fun P hP => (key _ i).2 P ⟨hN P hP.1, hP.2⟩⟩⟩
  refine (((key (N P) i).1.congr fun R hR => ?_).differentiableAt
    ((hSU _ _).mem_nhds ⟨hN P hP.1, hP.2⟩)).differentiableWithinAt
  rcases le_total (N R) (N P) with hle | hle
  · exact (agree hle i R ⟨hN R (hSΩ _ hR.1), hR.2⟩).symm
  · exact agree hle i R hR

end GlobalTheory.DoublingFrame

namespace GlobalTheory.DoublingFrame

section Datum

theorem transl_transl {g : ℕ} {E : Type} (τ : E → Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) (P : Pt E g) :
    transl τ x (transl τ y P) = transl τ (x + y) P := by
  refine Prod.ext rfl (funext fun i => ?_)
  simp only [transl, per, Pi.add_apply, Matrix.vecMul, dotProduct, Complex.ofReal_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem differentiableOn_transl {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap U τ) (x : Fl g) :
    DifferentiableOn ℂ (transl τ x) (cov U g) := by
  have hd : ∀ i k, DifferentiableOn ℂ (fun P : Pt E g => τ P.1 i k) (cov U g) := fun i k =>
    (hτ.2.1 i k).comp differentiableOn_fst fun P hP => hP.1
  refine differentiableOn_fst.prodMk (differentiableOn_snd.add ?_)
  refine differentiableOn_pi.2 fun i => ?_
  simp only [per, Pi.add_apply, Matrix.vecMul, dotProduct]
  exact (DifferentiableOn.fun_sum fun k _ => (hd k i).const_mul _).add_const _

theorem contDiffAt_comp {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {W : Type}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {B : Set W} (hB : IsOpen B)
    {y : W → CxPts p σ} (h : IsHolTo B fun b => (y b).1) {u : CxPts p σ → ℝ} {b : W} (hb : b ∈ B)
    (hu : CInfAt u (y b)) : ContDiffAt ℝ ∞ (fun b => u (y b)) b := by
  have hc : ContinuousOn y B := by
    rw [continuousOn_iff_continuous_domRestrict, CxPts.continuous_iff]
    intro U
    refine ⟨?_, fun f => ?_⟩
    · convert (h U 0).1.preimage (continuous_subtype_val (p := (· ∈ B))) using 1
      ext b
      exact ⟨fun hb => ⟨b.2, hb⟩, fun hb => hb.2⟩
    · exact (h U f).2.continuousOn.comp continuous_subtype_val.continuousOn fun b hb => ⟨b.2, hb⟩
  obtain ⟨U, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := hu
  have hg : ContDiffAt ℝ ∞ (fun w a => ev p σ U (g a) (y w)) b := contDiffAt_pi.2 fun a =>
    (SCV.contDiffAt_of_differentiableOn (h U (g a)).2 ((h U (g a)).1.mem_nhds ⟨hb, h₁⟩) ∞).restrict_scalars ℝ
  exact ((h₄.contDiffAt (h₂.mem_nhds h₃)).comp b hg).congr_of_eventuallyEq
    ((hc.continuousAt (hB.mem_nhds hb)).eventually h₅)

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} {P : PPAS S}
  {h : VMetric p (omega P.A) P.g} {c : AlgChart p σ 1} {τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ}
  {ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ}

open scoped CategoryTheory.Obj MonObj in

theorem ex_transl (H : IsPeriodChart h c τ ex) {Q : Pt (V 1) P.g} (hQ : Q ∈ cov c.e.target P.g) {l : Fl P.g}
    (hl : l ∈ stdLat P.g) : ex (transl τ l Q) = ex Q := by
  obtain ⟨h1, h2, -, h4, -⟩ := H.2.2 Q.1 hQ.1
  let x : Over.mk (c.e.symm Q.1).1 ⟶ P.A := Over.homMk (ex (Q.1, Q.2)).1 (h1 _)
  have e := h2 Q.2 (per (τ Q.1) l) x 1 rfl (Eq.trans rfl ((h4 _).2 ⟨l, hl, rfl⟩).symm)
  rw [mul_one] at e
  exact Subtype.ext e.symm

theorem exists_isFramed_isDatum (H : IsPeriodChart h c τ ex) (L : HermLB (P.A.hom ≫ p))
    (fr : L.B.ι → Pt (V 1) P.g → ℂ)
    (hfr : ∀ i, DifferentiableOn ℂ (fr i) (cov c.e.target P.g ∩ ex ⁻¹' ptsIn _ σ (L.B.U i)) ∧
      ∀ Q ∈ cov c.e.target P.g ∩ ex ⁻¹' ptsIn _ σ (L.B.U i), fr i Q ≠ 0 ∧
        ∀ i', ex Q ∈ ptsIn _ σ (L.B.U i') → fr i Q = CxPts.gv _ σ L.B i i' (ex Q) * fr i' Q) :
    ∃ (j : Fl P.g → Pt (V 1) P.g → ℂ) (m : Pt (V 1) P.g → ℝ),
      IsFramed L c.e.target τ ex j m ∧ IsDatum c.e.target τ (stdLat P.g) j m := by
  choose a ha using fun Q => exists_mem_ptsIn (σ := σ) (p := P.A.hom ≫ p) L.isLB.cover (ex Q)
  let j : Fl P.g → Pt (V 1) P.g → ℂ := fun l Q => fr (a Q) Q / fr (a Q) (transl τ l Q)
  let m : Pt (V 1) P.g → ℝ := fun Q => ‖fr (a Q) Q‖ ^ 2 * Real.exp (-(L.φ σ).φ (a Q) (ex Q))
  have ht {l : Fl P.g} (hl : l ∈ stdLat P.g) {i} {Q}
      (hQ : Q ∈ cov c.e.target P.g ∩ ex ⁻¹' ptsIn _ σ (L.B.U i)) :
      transl τ l Q ∈ cov c.e.target P.g ∩ ex ⁻¹' ptsIn _ σ (L.B.U i) :=
    ⟨⟨hQ.1.1, trivial⟩, by rw [mem_preimage, ex_transl H hQ.1 hl]; exact hQ.2⟩
  have hj {l : Fl P.g} (hl : l ∈ stdLat P.g) {i} {Q}
      (hQ : Q ∈ cov c.e.target P.g ∩ ex ⁻¹' ptsIn _ σ (L.B.U i)) : j l Q = fr i Q / fr i (transl τ l Q) := by
    have e1 := ((hfr (a Q)).2 Q ⟨hQ.1, ha Q⟩).2 i hQ.2
    have e2 := ((hfr (a Q)).2 _ (ht hl ⟨hQ.1, ha Q⟩)).2 i (ht hl hQ).2
    rw [ex_transl H hQ.1 hl] at e2
    simp only [j]
    rw [e1, e2, mul_div_mul_left _ _ (gv_ne_zero (ha Q) hQ.2)]
  have hm {i} {Q} (hQ : Q ∈ cov c.e.target P.g ∩ ex ⁻¹' ptsIn _ σ (L.B.U i)) :
      m Q = ‖fr i Q‖ ^ 2 * Real.exp (-(L.φ σ).φ i (ex Q)) := by
    have e1 := ((hfr (a Q)).2 Q ⟨hQ.1, ha Q⟩).2 i hQ.2
    simp only [m]
    rw [e1, (L.φ σ).trans (a Q) i _ (ha Q) hQ.2, neg_sub, sub_eq_add_neg, Real.exp_add,
      Real.exp_log (pow_pos (norm_pos_iff.2 (gv_ne_zero (ha Q) hQ.2)) 2), norm_mul]
    ring
  have ho (i) : IsOpen (cov c.e.target P.g ∩ ex ⁻¹' ptsIn _ σ (L.B.U i)) := (H.2.1 _ 1).1
  refine ⟨j, m, ⟨fr, fun i => ⟨(hfr i).1, fun Q hQ hi => ⟨((hfr i).2 Q ⟨hQ, hi⟩).1, ((hfr i).2 Q ⟨hQ, hi⟩).2,
    hm ⟨hQ, hi⟩, fun l hl => ?_⟩⟩⟩, H.1, ⟨?_, ?_⟩, ⟨fun l hl => ⟨fun Q hQ => ?_, fun Q hQ => ?_⟩,
    fun l hl l' hl' Q hQ => ?_⟩, fun Q hQ => ?_, fun Q hQ => ?_, fun l hl Q hQ => ?_⟩
  · rw [hj hl ⟨hQ, hi⟩, div_mul_cancel₀ _ ((hfr i).2 _ (ht hl ⟨hQ, hi⟩)).1]
  · unfold stdLat; infer_instance
  · unfold stdLat; infer_instance
  · have hd' : DifferentiableOn ℂ (fun R => fr (a Q) (transl τ l R))
        (cov c.e.target P.g ∩ ex ⁻¹' ptsIn _ σ (L.B.U (a Q))) :=
      (hfr (a Q)).1.comp ((differentiableOn_transl H.1 l).mono inter_subset_left) fun R hR => ht hl hR
    have hd := (hfr (a Q)).1.mul (hd'.inv fun R hR => ((hfr _).2 _ (ht hl hR)).1)
    exact ((hd.congr fun R hR => (hj hl hR).trans (div_eq_mul_inv _ _)).differentiableAt ((ho _).mem_nhds ⟨hQ, ha Q⟩)).differentiableWithinAt
  · exact div_ne_zero ((hfr _).2 Q ⟨hQ, ha Q⟩).1 ((hfr _).2 _ (ht hl ⟨hQ, ha Q⟩)).1
  · have n1 := ((hfr _).2 _ (ht hl' ⟨hQ, ha Q⟩)).1
    rw [hj hl (ht hl' ⟨hQ, ha Q⟩), hj hl' ⟨hQ, ha Q⟩, hj (add_mem hl hl') ⟨hQ, ha Q⟩, transl_transl,
      mul_comm, div_mul_div_cancel₀ n1]
  · have hn := (ho _).mem_nhds ⟨hQ, ha Q⟩
    have h1 : ContDiffAt ℝ ∞ (fr (a Q)) Q :=
      (SCV.contDiffAt_of_differentiableOn (hfr _).1 hn ∞).restrict_scalars ℝ
    have h2 := contDiffAt_comp (H.1.1.prod isOpen_univ) H.2.1 hQ (L.cInf σ _ _ (ha Q))
    exact (((h1.norm_sq ℝ).mul h2.neg.exp).congr_of_eventuallyEq
      (mem_of_superset hn fun R hR => hm hR)).contDiffWithinAt
  · exact mul_pos (pow_pos (norm_pos_iff.2 ((hfr _).2 Q ⟨hQ, ha Q⟩).1) 2) (Real.exp_pos _)
  · have n1 := norm_ne_zero_iff.2 ((hfr _).2 _ (ht hl ⟨hQ, ha Q⟩)).1
    rw [hm (ht hl ⟨hQ, ha Q⟩), hm ⟨hQ, ha Q⟩, hj hl ⟨hQ, ha Q⟩, ex_transl H hQ hl, norm_div]
    field_simp

end Datum

end GlobalTheory.DoublingFrame

namespace GlobalTheory.DoublingFrame

open Metric in

theorem exists_frame_of_half {E F J : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] {B : Set E} {v₀ : E} (hv : v₀ ∈ B)
    (U : J → Set (E × F)) (c G : J → J → E × F → ℂ) (h : E × F → E × F)
    (hh : h = fun P => (P.1, (2 : ℂ)⁻¹ • P.2)) (hU : ∀ i, IsOpen (B ×ˢ univ ∩ U i))
    (hcov : ∀ P ∈ B ×ˢ (univ : Set F), ∃ i, P ∈ U i)
    (hc : ∀ i j, DifferentiableOn ℂ (c i j) (B ×ˢ univ ∩ U i ∩ U j))
    (hc0 : ∀ i j, ∀ P ∈ B ×ˢ (univ : Set F), P ∈ U i → P ∈ U j → c i j P ≠ 0)
    (hcm : ∀ i j l, ∀ P ∈ B ×ˢ (univ : Set F), P ∈ U i → P ∈ U j → P ∈ U l → c i j P * c j l P = c i l P)
    (hG : ∀ b a, DifferentiableOn ℂ (G b a) (B ×ˢ univ ∩ U b ∩ h ⁻¹' U a) ∧
      ∀ Q ∈ B ×ˢ univ ∩ U b ∩ h ⁻¹' U a, G b a Q ≠ 0)
    (hGc : ∀ b a b' a', ∀ Q ∈ B ×ˢ (univ : Set F), Q ∈ U b → Q ∈ U b' → h Q ∈ U a → h Q ∈ U a' →
      G b a Q * c a a' (h Q) ^ 4 = c b b' Q * G b' a' Q) :
    ∃ r > 0, ball v₀ r ⊆ B ∧ ∃ f : J → E × F → ℂ, ∀ i,
      DifferentiableOn ℂ (f i) (ball v₀ r ×ˢ univ ∩ U i) ∧
      ∀ P ∈ ball v₀ r ×ˢ univ ∩ U i, f i P ≠ 0 ∧ ∀ j, P ∈ U j → f i P = c i j P * f j P := by
  have hd : Differentiable ℂ h := by rw [hh]; fun_prop
  have h0 : h (v₀, 0) = (v₀, 0) := by simp [hh]
  obtain ⟨o, ho⟩ := hcov (v₀, 0) ⟨hv, trivial⟩
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 ((hU o).inter ((hU o).preimage hd.continuous)) (v₀, 0)
    ⟨⟨⟨hv, trivial⟩, ho⟩, by rw [mem_preimage, h0]; exact ⟨⟨hv, trivial⟩, ho⟩⟩
  have hεs' : ball (v₀, (0 : F)) ε ⊆ B ×ˢ univ ∩ U o ∩ h ⁻¹' U o := fun P hP => ⟨(hεs hP).1, (hεs hP).2.2⟩
  obtain ⟨φ, hφ, hφe⟩ := ConvexHolLog.exists_differentiableOn_log (convex_ball _ _) isOpen_ball (G o o)
    ((hG o o).1.mono hεs') fun P hP => (hG o o).2 P (hεs' hP)
  obtain ⟨r, ψ, q, hr, hrs, hψ, hq, he⟩ := exists_half_solution isOpen_ball (mem_ball_self hε) hφ
  have hrB : ball v₀ r ⊆ B := fun v hv' => (hεs' (hrs (a := (v, 0)) ⟨hv', mem_ball_self hr⟩)).1.1.1
  have hΩ : ball v₀ r ×ˢ (univ : Set F) ⊆ B ×ˢ univ := prod_mono hrB le_rfl
  have hS0 : ball v₀ r ×ˢ ball (0 : F) (2 ^ 0 * r) = ball v₀ r ×ˢ ball 0 r := by simp
  have hhalf (s : ℝ) : MapsTo h (ball v₀ r ×ˢ ball 0 (2 * s)) (ball v₀ r ×ˢ ball 0 s) := fun P hP => by
    have := hP.2
    rw [hh]
    refine ⟨hP.1, ?_⟩
    simp only [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_ofNat] at this ⊢
    linarith
  have hh0 : MapsTo h (ball v₀ r ×ˢ ball 0 r) (ball v₀ r ×ˢ ball 0 r) :=
    (hhalf r).mono_left (prod_mono le_rfl (ball_subset_ball (by linarith)))
  refine ⟨r, hr, hrB, exists_frame_iUnion (fun n => ball v₀ r ×ˢ ball 0 (2 ^ n * r)) U c
    (fun b a P => G b a P * Complex.exp (-q P)) h (fun i P => c i o P * Complex.exp (ψ P))
    (fun n => isOpen_ball.prod isOpen_ball) (fun n m hnm => prod_mono le_rfl (ball_subset_ball ?_)) ?_
    (fun i => ?_) (fun P hP => hcov P (hΩ hP)) hd (fun n => ?_) (hS0 ▸ hh0) (fun i P hP => ?_)
    (fun b a => ⟨?_, fun Q hQ => ?_⟩) (fun b a b' a' Q hQ h1 h2 h3 h4 => ?_) fun i => ?_⟩
  · gcongr; norm_num
  · refine subset_antisymm (fun P hP => ?_) (iUnion_subset fun n => prod_mono le_rfl (subset_univ _))
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖P.2‖ / r) (one_lt_two (α := ℝ))
    exact mem_iUnion.2 ⟨n, hP.1, mem_ball_zero_iff.2 ((div_lt_iff₀ hr).1 hn)⟩
  · have := ((isOpen_ball (x := v₀) (ε := r)).prod isOpen_univ).inter (hU i)
    rwa [← inter_assoc, inter_eq_left.2 hΩ] at this
  · simpa only [pow_succ', mul_assoc] using hhalf (2 ^ n * r)
  · exact mul_left_cancel₀ (hc0 i i P (hΩ hP.1) hP.2 hP.2)
      ((hcm i i i P (hΩ hP.1) hP.2 hP.2 hP.2).trans (mul_one _).symm)
  · exact ((hG b a).1.mono fun Q hQ => ⟨⟨hΩ hQ.1.1, hQ.1.2⟩, hQ.2⟩).mul (hq.mono fun Q hQ => hQ.1.1).neg.cexp
  · exact mul_ne_zero ((hG b a).2 Q ⟨⟨hΩ hQ.1.1, hQ.1.2⟩, hQ.2⟩) (Complex.exp_ne_zero _)
  · linear_combination Complex.exp (-q Q) * hGc b a b' a' Q (hΩ hQ) h1 h2 h3 h4
  · simp only [hS0]
    refine ⟨((hc i o).mono fun P hP => ?_).mul (hψ.mono inter_subset_left).cexp, fun P hP => ?_⟩
    · exact ⟨⟨(hεs' (hrs hP.1)).1.1, hP.2⟩, (hεs' (hrs hP.1)).1.2⟩
    · have hP' := hεs' (hrs hP.1)
      refine ⟨mul_ne_zero (hc0 i o P hP'.1.1 hP.2 hP'.1.2) (Complex.exp_ne_zero _), fun j hj => ?_,
        fun a ha => ?_⟩
      · rw [← mul_assoc, hcm i j o P hP'.1.1 hP.2 hj hP'.1.2]
      · have e1 := hGc i a o o P hP'.1.1 hP.2 hP'.1.2 ha hP'.2
        have e2 : Complex.exp (ψ P) = G o o P * Complex.exp (-q P) * Complex.exp (ψ (h P)) ^ 4 := by
          rw [hφe P (hrs hP.1), ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, hh]
          congr 1
          linear_combination he P hP.1
        rw [e2]
        linear_combination (-(Complex.exp (-q P) * Complex.exp (ψ (h P)) ^ 4)) * e1

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} {P : PPAS S}
  {h : VMetric p (omega P.A) P.g} {c : AlgChart p σ 1} {τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ}
  {ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ}

open scoped CategoryTheory.Obj MonObj in

theorem ex_double (H : IsPeriodChart h c τ ex) {v : V 1} (hv : v ∈ c.e.target) (z : Fin P.g → ℂ) :
    (ex (v, z)).1 = (ex (v, (2 : ℂ)⁻¹ • z)).1 ≫ dbl P := by
  obtain ⟨h1, h2, -⟩ := H.2.2 v hv
  let x : Over.mk (c.e.symm v).1 ⟶ P.A := Over.homMk (ex (v, (2 : ℂ)⁻¹ • z)).1 (h1 _)
  have e := h2 _ _ x x rfl rfl
  rw [← add_smul, show (2 : ℂ)⁻¹ + 2⁻¹ = 1 by norm_num, one_smul] at e
  rw [← e]
  change _ = (x ≫ Out.mulA P.A 2).left
  rw [Out.mulA, MonObj.comp_pow, Category.comp_id, sq]

theorem exists_restr (H : IsPeriodChart h c τ ex) {B : Set (V 1)} (hB : IsOpen B) (hBc : B ⊆ c.e.target) :
    ∃ c' : AlgChart p σ 1, c'.e.target = B ∧ c'.e.source = c.e.source ∩ c.e ⁻¹' B ∧
      IsPeriodChart h c' τ ex := by
  let c' := c.restr _ (c.e.isOpen_inter_preimage hB)
  have ht : c'.e.target = B := by
    refine subset_antisymm (fun v hv => ?_) fun v hv => ⟨hBc hv, c.e.map_target (hBc hv), ?_⟩
    · have := hv.2.2
      rwa [mem_preimage, show c.e _ = v from c.e.right_inv hv.1] at this
    · rwa [mem_preimage, show c.e _ = v from c.e.right_inv (hBc hv)]
  refine ⟨c', ht, by simp [c'], ?_, ?_, fun v hv => H.2.2 v hv.1⟩
  · rw [ht]
    exact ⟨hB, fun i j => (H.1.2.1 i j).mono hBc, fun b hb => H.1.2.2 b (hBc hb)⟩
  · rw [ht]
    intro W f
    obtain ⟨h1, h2⟩ := H.2.1 W f
    refine ⟨?_, h2.mono fun Q hQ => ⟨⟨hBc hQ.1.1, trivial⟩, hQ.2⟩⟩
    refine (congrArg IsOpen ?_).mp ((hB.prod isOpen_univ).inter h1)
    exact subset_antisymm (fun Q hQ => ⟨hQ.1, hQ.2.2⟩) fun Q hQ => ⟨hQ.1, ⟨hBc hQ.1.1, trivial⟩, hQ.2⟩

theorem framedCharts_of_double : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p →
    ∀ (P : PPAS S) (h : VMetric p (omega P.A) P.g), P.IsDualRiemann (1 / 2) h →
    ∀ L : HermLB (P.A.hom ≫ p), ∀ (w : LB.Iso (L.pull (dbl P) (dbl_comp P p)).B (L.pow 4).B), w.IsGen →
    FramedCharts P h L := by
  intro k _ S p hp P h hh L w hw σ y
  obtain ⟨c, τ, ex, hy, -, H⟩ := T.exists_period_chart_dual_riemann k S p hp P h hh σ y
  set hf : Pt (V 1) P.g → Pt (V 1) P.g := fun Q => (Q.1, (2 : ℂ)⁻¹ • Q.2) with hhf
  have hd : Differentiable ℂ hf := by rw [hhf]; fun_prop
  have hm {Q : Pt (V 1) P.g} (hQ : Q ∈ cov c.e.target P.g) : (ex Q).1 = (ex (hf Q)).1 ≫ dbl P :=
    ex_double H hQ.1 Q.2
  have hpull {Q : Pt (V 1) P.g} (hQ : Q ∈ cov c.e.target P.g) {b : L.B.ι} (hb : ex Q ∈ ptsIn _ σ (L.B.U b)) :
      ex (hf Q) ∈ ptsIn _ σ ((L.pull (dbl P) (dbl_comp P p)).B.U fun _ => b) := fun x _ => by
    have := hb (show x ∈ ⊤ from trivial)
    rw [hm hQ] at this
    exact mem_iInter.2 fun _ => this
  have hpow {y : CxPts (P.A.hom ≫ p) σ} {a : L.B.ι} (ha : y ∈ ptsIn _ σ (L.B.U a)) :
      y ∈ ptsIn _ σ ((L.pow 4).B.U fun _ => a) := mem_pow_iff.2 ha
  obtain ⟨r, hr, hrB, f, hfr⟩ := exists_frame_of_half (c.e.map_source hy)
    (fun i => ex ⁻¹' ptsIn _ σ (L.B.U i)) (fun i j Q => CxPts.gv _ σ L.B i j (ex Q))
    (fun b a Q => (ev _ σ _ (w.s (fun _ => a, fun _ => b)).val (ex (hf Q)))⁻¹) hf rfl
    (fun i => (H.2.1 _ 1).1) (fun Q _ => exists_mem_ptsIn L.isLB.cover _)
    (fun i j => (H.2.1 _ (L.B.g i j).val).2.mono fun Q hQ => ⟨hQ.1.1, mem_ptsIn_inf.2 ⟨hQ.1.2, hQ.2⟩⟩)
    (fun i j Q _ => gv_ne_zero) (fun i j l Q _ => gv_mul L.isLB)
    (fun b a => by
      have h0 : ∀ Q ∈ c.e.target ×ˢ univ ∩ ex ⁻¹' ptsIn _ σ (L.B.U b) ∩ hf ⁻¹' (ex ⁻¹' ptsIn _ σ (L.B.U a)),
          ev _ σ _ (w.s (fun _ => a, fun _ => b)).val (ex (hf Q)) ≠ 0 := fun Q hQ =>
        ev_iso_ne_zero w (hpull hQ.1.1 hQ.1.2) (hpow hQ.2)
      refine ⟨DifferentiableOn.inv ?_ h0, fun Q hQ => inv_ne_zero (h0 Q hQ)⟩
      exact (H.2.1 _ (w.s (fun _ => a, fun _ => b)).val).2.comp hd.differentiableOn fun Q hQ =>
        ⟨⟨hQ.1.1.1, trivial⟩, mem_ptsIn_inf.2 ⟨hpow hQ.2, hpull hQ.1.1 hQ.1.2⟩⟩)
    (fun b a b' a' Q hQ h1 h2 h3 h4 => by
      have e := ev_iso_rel hw (hpull hQ h1) (hpull hQ h2) (hpow h3) (hpow h4)
      have e1 : CxPts.gv _ σ (L.pull (dbl P) (dbl_comp P p)).B (fun _ => b) (fun _ => b') (ex (hf Q)) =
          CxPts.gv _ σ L.B b b' (ex Q) :=
        (gv_linComb (m := fun _ => ex Q) (fun _ => hm hQ) (hpull hQ h1) (hpull hQ h2)).trans (by simp)
      have e2 : CxPts.gv _ σ (L.pow 4).B (fun _ => a) (fun _ => a') (ex (hf Q)) =
          CxPts.gv _ σ L.B a a' (ex (hf Q)) ^ 4 := (gv_pow h3 h4).trans (zpow_natCast _ _)
      rw [e1, e2] at e
      have n1 := ev_iso_ne_zero w (hpull hQ h1) (hpow h3)
      have n2 := ev_iso_ne_zero w (hpull hQ h2) (hpow h4)
      field_simp
      linear_combination -e)
  obtain ⟨c', ht, hs, H'⟩ := exists_restr H Metric.isOpen_ball hrB
  obtain ⟨j, m, h1, h2⟩ := exists_isFramed_isDatum H' L f (by rw [ht]; exact hfr)
  exact ⟨c', τ, ex, j, m, hs ▸ ⟨hy, Metric.mem_ball_self hr⟩, ht ▸ convex_ball _ _, H', h1, h2⟩

end GlobalTheory.DoublingFrame
