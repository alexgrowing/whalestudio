import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceRead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameOfRealizationModels
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaComparisonIffForall

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HeckeGenConst

open ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Formalism.IndefR.Datum

theorem eq_zero_of_rat_span {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Module ℚ V] (M : Submodule ℚ V)
    (hM : Submodule.span ℝ (M : Set V) = ⊤) {f : V → ℂ} (hf : Continuous f) (h0 : ∀ z ∈ M, f z = 0) (z : V) : f z = 0 := by
  have hcl : ∀ z, z ∈ closure (M : Set V) := by
    intro z
    have hz : z ∈ Submodule.span ℝ (M : Set V) := hM ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact subset_closure hx
    | zero => exact subset_closure M.zero_mem
    | add x y _ _ hx hy => exact M.toAddSubgroup.topologicalClosure.add_mem hx hy
    | smul c x _ hx =>
      have h1 : ∀ q : ℚ, (q : ℝ) • x ∈ closure (M : Set V) := fun q =>
        map_mem_closure (f := fun y : V => (q : ℝ) • y) (continuous_const_smul _) hx fun y hy => by
          beta_reduce; rw [Rat.cast_smul_eq_qsmul]; exact M.smul_mem q hy
      exact (Rat.denseRange_cast (𝕜 := ℝ)).induction_on (p := fun c : ℝ => c • x ∈ closure (M : Set V)) c
        (isClosed_closure.preimage (continuous_id.smul continuous_const)) h1
  exact (isClosed_eq hf continuous_const).closure_subset_iff.2 h0 (hcl z)

variable {D : D7}

section Period

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

theorem perVec_add (Wt : UnfAt U k x) (v w : Fin r → D.host.E) : perVec Wt (v + w) = perVec Wt v + perVec Wt w := by
  have he : ∀ τ : D.host.E →+* ℂ, Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := fun τ => by
    funext a; simp [Data.emb]
  funext j
  simp only [perVec, Pi.add_apply]
  unfold perFr
  split_ifs <;> simp [he, Matrix.mulVec_add, hermC, map_add, mul_add, Finset.sum_add_distrib]

theorem perVec_smul (Wt : UnfAt U k x) (q : ℚ) (v : Fin r → D.host.E) : perVec Wt (q • v) = q • perVec Wt v := by
  have he : ∀ τ : D.host.E →+* ℂ, Data.emb τ (q • v) = (q : ℂ) • Data.emb τ v := fun τ => by
    funext a; simp [Data.emb, Rat.smul_def]
  funext j
  simp only [perVec, Pi.smul_apply, Rat.smul_def]
  unfold perFr
  split_ifs
  · rw [he, Matrix.mulVec_smul]; rfl
  · simp
  · simp only [he, hermC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul, map_ratCast]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · simp
  · simp

theorem exists_theta_perVec_ne_zero {Wt : UnfAt U k x} (Y : UnitAt Wt) :
    ∃ v : Fin r → D.host.E, Y.θ (perVec Wt v) ≠ 0 := by
  by_contra hne
  push Not at hne
  let L : (Fin r → D.host.E) →ₗ[ℚ] (Fin Wt.g → ℂ) := ⟨⟨perVec Wt, perVec_add Wt⟩, perVec_smul Wt⟩
  have h0 := eq_zero_of_rat_span (LinearMap.range L) (by
    rw [eq_top_iff, ← Wt.per.2.2.2.1]
    refine Submodule.span_mono ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨_, perVec_lat Wt a⟩) (GlobalTheory.EtaPinnedCompare.theta_entire Y).continuous (by
    rintro _ ⟨v, rfl⟩
    exact hne v)
  have h9 := Y.c9
  simp [h0] at h9

end Period

theorem exists_const_of_orth {K : Type} [CommRing K] {n m : ℕ} {b b' g : Fin n → Fin n → K}
    (hb : ∀ a a', ∑ i, ∑ j, b' i a * g i j * b j a' = if a = a' then 1 else 0) (v : Fin m → K) :
    ∃ X : Matrix (Fin m) (Fin n) K, ∀ j a, ∑ n, X j n * b n a = v j := by
  refine ⟨fun j n => v j * ∑ a', ∑ i, b' i a' * g i n, fun j a => ?_⟩
  have h : ∑ n, (∑ a', ∑ i, b' i a' * g i n) * b n a = 1 := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun a' _ => Finset.sum_comm.trans (hb a' a)]
    simp
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [h, mul_one]

theorem exists_map_const {V : HSp D} {b : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (hb : IsONLatBasis V b) {m : ℕ}
    (v : Fin m → D.host.E) : ∃ X : Matrix (Fin m) (Fin V.rank) D.host.E, ∀ j a, ∑ n, X j n * b n a = v j :=
  exists_const_of_orth (b' := fun i a => star (b i a)) (g := V.gram) hb.1 v

theorem exists_frAt {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (hM : R.IsModels) (ht : TieIn T R κ v₀) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hσ : σ = T.σ₀)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (h : GA D (Wc D i)) :
    ∃ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ h := by
  have e : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]
    exact res_embLL T ht.alg ht.laws.pins.2.2.1
  have hg : GoodEmb T.Q.c (res T (sg0 D A)) := e ▸ T.toCore.good_σ₀
  obtain rfl : σ = res T (sg0 D A) := hσ.trans e.symm
  obtain ⟨γ, h1, h2, -⟩ := (GlobalTheory.HolDict.BaseFrame.baseFrT_of_tieIn D G Pl0 T0 A T R κ v₀ hM ht i _ hg hV).2.2 h
  exact ⟨γ, h1, h2⟩

theorem cancel {ι : Type} [Fintype ι] {u ph K K' μ q w : ℂ} {e θ : ι → ℂ} (hph : ph ≠ 0) (hμ : μ ≠ 0) (hθ : ∀ a, θ a ≠ 0)
    (h1 : Complex.exp (Real.pi / 2 * ∑ a, e a) * (μ * q * w) = ph * K' * ∏ a, θ a)
    (h2 : u * (ph * K) * ∏ a, (Complex.exp (-(Real.pi / 2 * e a)) * θ a) = w) : u * (K * q) = μ⁻¹ * K' := by
  have h3 : Complex.exp (Real.pi / 2 * ∑ a, e a) * ∏ a, Complex.exp (-(Real.pi / 2 * e a)) = 1 := by
    rw [← Complex.exp_sum, ← Complex.exp_add, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel, Complex.exp_zero]
  have h4 : ∏ a, θ a ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hθ a
  rw [← h2, Finset.prod_mul_distrib] at h1
  rw [eq_inv_mul_iff_mul_eq₀ hμ]
  refine mul_left_cancel₀ (mul_ne_zero hph h4) ?_
  linear_combination h1 - μ * q * u * ph * K * (∏ a, θ a) * h3

end GlobalTheory.HeckeGenConst

open GlobalTheory.HeckeGenConst GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues in

theorem GlobalTheory.HeckeGenConst.generator_constant : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ a ∈ Rc, ∀ (C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          (∀ j, j ≠ none → t j = 1) → FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z →
          toC (t none : CAt σ) ^ (κ i).n *
              ((T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
                σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV)) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) (h * a)) := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hpin P p k α Rc hS h hx
    a ha C z hz hx' t ht hb
  obtain ⟨ph, b, hph, hbON, hpin⟩ := hpin
  obtain ⟨γ', hγ', hfr'⟩ := exists_frAt hMod hTie i σ hσ hV (h * a)
  obtain ⟨_, Wt', ⟨Y'⟩⟩ := exists_witness T i σ hV hTie.laws.toLawsM (hσ ▸ T.toCore.good_σ₀) (h * a)
  obtain ⟨rV, e, he, ⟨Δ, hΔ⟩, hall⟩ :=
    GlobalTheory.HeckeVacuum.omega_vacuum_hecke D G Pl0 T0 A T R hLev hFam hThP i P p k α Rc hS a ha
  obtain ⟨-, -, hom⟩ := hall Δ hΔ
  obtain ⟨v, hv⟩ := exists_theta_perVec_ne_zero Y'
  obtain ⟨X, hX⟩ := exists_map_const hbON fun j => v (Fin.cast (rank_Wc i) j)
  have hz' : ∀ a : Fin (Vc D i).rank,
      perVec Wt' v = perVec Wt' fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a := fun a => by
    congr 1
    funext m
    rw [hX]
    rfl
  have h2 := GlobalTheory.HeckeGeoRead.theta_trace_read D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV
    P p k α Rc hS h hx a ha C z hz hx' t ht hb ph b hph hbON hpin γ' hγ' hfr' Wt' Y' e he Δ hΔ X (fun _ => perVec Wt' v) hz'
  have h1 := hpin (h * a) γ' hγ' hfr' hx' Wt' Y' X (fun _ => perVec Wt' v) hz'
  rw [thetaAt_eq, show ((1 : GA D (Vc D i)), γ' * (h * a)) = (1, γ' * h) * (1, a) by simp [mul_assoc], map_mul,
    Module.End.mul_apply, hom, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at h1
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have h3 := cancel (fun h0 => by simp [h0] at hph) (pow_ne_zero k (Units.ne_zero _)) (fun _ => hv) h1 h2
  rw [(hTie.kap i τ).2.2, hkScal, one_mul, map_pow, map_inv₀, map_natCast, inv_pow (muAt T R i P)]
  rw [rV] at h3
  exact h3
