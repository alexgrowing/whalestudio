import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeRowMulVecMemModulusScaledCompletion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualModulusShiftHalfMemCompletedModulusHom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.AscFin.DepthColumn

open GlobalTheory.FinPl (SplitPt Frame latMul)
open GlobalTheory.FinPl.FrameLat
open scoped Pointwise

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pow_mem_pow {K : Type} [Field K] [NumberField K] {I : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ I) :
    ∀ n : ℕ, x ^ n ∈ I ^ n
  | 0 => by rw [pow_zero, pow_zero]; exact FractionalIdeal.one_mem_one _
  | n + 1 => by rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul (pow_mem_pow hx n) hx

theorem exists_mem_pow {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) (e : ℕ) {x : k} (hx : valuation k x ≤ valuation k (ϖ : k) ^ e) :
    ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e, (z : k) = x := by
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hv : valuation k ((ϖ : k) ^ e) ≠ 0 := (Valuation.ne_zero_iff _).2 (pow_ne_zero _ h0)
  have h1 : x / (ϖ : k) ^ e ∈ 𝒪[k] := by
    change valuation k _ ≤ 1
    rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hv), map_pow]
    exact hx
  refine ⟨⟨_, h1⟩ * ϖ ^ e, Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow ?_ _), ?_⟩
  · rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self _
  · push_cast
    field_simp

theorem val_unif_eq {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) (q : GlobalTheory.LatPair.Unif k) :
    valuation k ((q.1 : 𝒪[k]) : k) = valuation k (ϖ : k) :=
  le_antisymm (SplitPt.val_le_unif ⟨ϖ, hϖ⟩ (SplitPt.val_unif_lt_one q))
    (SplitPt.val_le_unif q (SplitPt.val_unif_lt_one ⟨ϖ, hϖ⟩))

theorem val_unit (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w)
    {t : 𝓞 D.host.E} (ht : t ∉ w.asIdeal) : valuation k (p.pr (incA D (t : D.host.E))) = 1 := by
  obtain ⟨u, hu, hu2⟩ := Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top 1
  exact (SplitPt.val_eq_unif_and_unit D k p w hw u t (by rwa [pow_one] at hu) hu2 ht).2

theorem exists_unif (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w)
    {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) :
    ∃ t ∈ w.asIdeal, valuation k (p.pr (incA D (t : D.host.E))) = valuation k (ϖ : k) := by
  obtain ⟨u, hu, hu2⟩ := Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top 1
  rw [pow_one] at hu
  obtain ⟨q, hq⟩ := (SplitPt.val_eq_unif_and_unit D k p w hw u 1 hu hu2
    ((Ideal.ne_top_iff_one _).1 w.isPrime.ne_top)).1
  exact ⟨u, hu, hq.trans (val_unif_eq hϖ q)⟩

theorem val_le_of_mem_pow (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w)
    {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) (n : ℕ) :
    ∀ t ∈ w.asIdeal ^ n, valuation k (p.pr (incA D (t : D.host.E))) ≤ valuation k (ϖ : k) ^ n := by
  have hf' : ∀ x : 𝓞 D.host.E, p.pr (incA D (x : D.host.E)) =
      p.prF hw (Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.IndefR.Lev.EAf D) := fun x =>
    (p.prF_toEAf hw (incA D (x : D.host.E))).symm
  induction n with
  | zero => intro t _; rw [pow_zero, hf']; exact p.val_prF_le_one hw _
  | succ n ih =>
    intro t ht
    rw [pow_succ] at ht
    refine Submodule.mul_induction_on ht (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · have h1 : valuation k (p.pr (incA D (y : D.host.E))) < 1 := by
        rw [hf']; exact (p.mem_iff_val_lt hw y).1 hy
      have e1 : ((x * y : 𝓞 D.host.E) : D.host.E) = x * y := rfl
      rw [e1, map_mul, map_mul, map_mul, pow_succ]
      exact mul_le_mul' (ih x hx) (SplitPt.val_le_unif ⟨ϖ, hϖ⟩ h1)
    · have e1 : ((x + y : 𝓞 D.host.E) : D.host.E) = x + y := rfl
      rw [e1, map_add, map_add]
      exact Valuation.map_add_le _ hx hy

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem exists_modul (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) (p : SplitPt D k)
    (hw : Formalism.L2.NTheta.IsIdemAt p.e (P.w v)) {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) :
    ∃ m ∈ P.modul sc, valuation k (p.pr (incA D (m : D.host.E))) = valuation k (ϖ : k) ^ P.depth sc v := by
  classical
  have hu : ∀ u ∈ P.S0, ∃ a ∈ (P.w u).asIdeal,
      valuation k (p.pr (incA D (a : D.host.E))) = if u = v then valuation k (ϖ : k) else 1 := by
    intro u hu
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl]
      exact exists_unif p hw hϖ
    · rw [if_neg huv]
      have hne : ¬ (P.w u).asIdeal ≤ (P.w v).asIdeal := fun hle => huv (by
        rw [← P.under_w hu, ← P.under_w hv,
          HeightOneSpectrum.ext ((P.w u).isMaximal.eq_of_le (P.w v).isPrime.ne_top hle)])
      obtain ⟨t, htu, htv⟩ := Set.not_subset.1 hne
      exact ⟨t, htu, val_unit p hw htv⟩
  choose! a ha hb using hu
  refine ⟨∏ u ∈ P.S0, a u ^ P.depth sc u, Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow (ha u hu) _, ?_⟩
  change valuation k (p.pr (incA D (algebraMap (𝓞 D.host.E) D.host.E _))) = _
  rw [map_prod, map_prod, map_prod, map_prod, Finset.prod_eq_single v]
  · rw [map_pow, map_pow, map_pow, map_pow]
    exact congrArg (· ^ P.depth sc v) ((hb v hv).trans (if_pos rfl))
  · intro u hu huv
    rw [map_pow, map_pow, map_pow, map_pow]
    exact (congrArg (· ^ P.depth sc u) ((hb u hu).trans (if_neg huv))).trans (one_pow _)
  · intro h; exact absurd hv h

theorem val_le_of_mem_modul (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) (p : SplitPt D k)
    (hw : Formalism.L2.NTheta.IsIdemAt p.e (P.w v)) {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {m : 𝓞 D.host.E} (hm : m ∈ P.modul sc) :
    valuation k (p.pr (incA D (m : D.host.E))) ≤ valuation k (ϖ : k) ^ P.depth sc v :=
  val_le_of_mem_pow p hw hϖ _ m (Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv) hm)

theorem exists_mem_AAbar_inv {w : HeightOneSpectrum (𝓞 D.host.E)} (h : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) :
    ∃ n : 𝓞 D.host.E, n ∉ w.asIdeal ∧ (n : D.host.E) ∈ D.host.AAbar⁻¹ := by
  refine ⟨((Ideal.absNorm D.host.𝔟 : ℕ) : 𝓞 D.host.E), fun hm => ?_, ?_⟩
  · obtain ⟨p, hp, hP⟩ := GlobalTheory.HalfCompare.exists_prime_under w
    exact h ((hP _).2 ((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hP _).1 hm)))
  · rw [FractionalIdeal.mem_inv_iff (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D)]
    intro a ha
    obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _)
      (((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.2 a).1 ha)
    refine (FractionalIdeal.mem_one_iff _).2 ⟨GlobalTheory.IdemSupport.cO D c, ?_⟩
    change star (algebraMap _ D.host.E c) = _
    rw [hc, star_mul', star_star, star_natCast, mul_comm]
    rfl

theorem exists_stair (hO : OffQ D) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0) (p : SplitPt D k)
    (hw : Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v)) {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {c : ℕ} (q : Fin c) :
    ∃ g ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) c q,
      valuation k (p.pr (incA D g)) = valuation k (ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)) := by
  classical
  have hW : G.pl.w v ∈ G.pl.W0 := by
    unfold Places.W0
    convert Finset.mem_image_of_mem G.pl.w hv
  obtain ⟨m, hm, hmv⟩ := exists_modul G.pl sc hv p hw hϖ
  obtain ⟨n, hn, hn'⟩ := exists_mem_AAbar_inv (GlobalTheory.HalfOut.two_q_notMem hO G hW)
  have hb : G.pl.modulBar sc ≠ ⊥ := by
    unfold Places.modulBar
    intro h
    apply G.pl.modul_ne_bot sc
    have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
    simpa [smul_smul] using this
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal := fun h =>
    GlobalTheory.AAUnit.absNorm_cmIdeal_not_mem_gridPlaces G.pl hv (by
      rw [← G.pl.under_w hv]
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ (G.pl.w v).asIdeal
      rwa [map_natCast])
  have h1 : (Ideal.absNorm D.host.ccK : D.host.E) ∈ G.pl.stA sc := by
    have := FractionalIdeal.mul_mem_mul (GlobalTheory.HostClear.absNorm_mem_AA D)
      (FractionalIdeal.one_mem_inv_coe_ideal (K := D.host.E) hb)
    rwa [mul_one] at this
  have h2 : (n : D.host.E) * (m : D.host.E) ∈ (G.pl.stAbar sc)⁻¹ := by
    unfold Places.stAbar
    rw [mul_inv, inv_inv]
    exact FractionalIdeal.mul_mem_mul hn' ((FractionalIdeal.mem_coeIdeal _).2 ⟨m, hm, rfl⟩)
  refine ⟨(Ideal.absNorm D.host.ccK : D.host.E) ^ (c - q.1) * ((n : D.host.E) * (m : D.host.E)) ^ (q.1 + 1), ?_, ?_⟩
  · unfold stairId
    rw [← inv_pow]
    exact FractionalIdeal.mul_mem_mul (pow_mem_pow h1 _) (pow_mem_pow h2 _)
  · have h3 : valuation k (p.pr (incA D (Ideal.absNorm D.host.ccK : D.host.E))) = 1 := val_unit p hw hN
    simp only [map_mul, map_pow]
    rw [h3, val_unit p hw hn, hmv, one_pow, one_mul, one_mul, ← pow_mul]

theorem val_coord_le {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) {Λ : Lat S}
    (hβ : β.IsLat Λ (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k))) {𝔪 : Set D.host.E} {γ : ValueGroupWithZero k}
    (h𝔪 : ∀ a ∈ 𝔪, valuation k (p.pr (incA D a)) ≤ γ) {P : GlobalTheory.FinPl.Pl D → Prop} {Z : Fin S.rank → AE D}
    (hZ : Z ∈ latMul S 𝔪 Λ P) (i : n) : valuation k ((β.b' *ᵥ fun j => p.pr (Z j)) i) ≤ γ := by
  induction hZ using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hy
    have e1 : (fun j => p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x j))) =
        (p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * p.pr (incA D a)) • fun j => p.pr (incA D (x j)) := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul, ← map_mul, ← map_mul]
      congr 1
      change _ = _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x j)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul]
    have h1 : valuation k (p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E))) ≤ 1 := by
      change _ ∈ 𝒪[k]
      rw [p.int_iff, p.sec_pr, map_mul]
      exact mul_mem_intAE (e_mem_intAt p).2 (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩)
    have h2 : valuation k ((β.b' *ᵥ fun j => p.pr (incA D (x j))) i) ≤ 1 := by
      have h3 := (hβ (β.b' *ᵥ fun j => p.pr (incA D (x j)))).2 (by
        rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
        exact sec_inc_mem hx)
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 (h3 i (Set.mem_univ _))
      rw [← hc]
      exact c.2
    rw [e1, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, map_mul]
    calc _ ≤ 1 * γ * 1 := mul_le_mul' (mul_le_mul' h1 (h𝔪 a ha)) h2
      _ = γ := by rw [one_mul, mul_one]
  | zero =>
    have e1 : (fun j => p.pr ((0 : Fin S.rank → AE D) j)) = 0 := funext fun j => map_zero _
    rw [e1, Matrix.mulVec_zero, Pi.zero_apply, map_zero]
    exact zero_le'
  | add x y _ _ hx hy =>
    have e1 : (fun j => p.pr ((x + y) j)) = (fun j => p.pr (x j)) + fun j => p.pr (y j) := funext fun j => map_add _ _ _
    rw [e1, Matrix.mulVec_add, Pi.add_apply]
    exact Valuation.map_add_le _ hx hy
  | neg x _ hx =>
    have e1 : (fun j => p.pr ((-x) j)) = -fun j => p.pr (x j) := funext fun j => map_neg _ _
    rw [e1, Matrix.mulVec_neg, Pi.neg_apply, Valuation.map_neg]
    exact hx

theorem ideal_smul_auxiliary_vector_mem_lattice {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Lat A)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (q : Fin c) {g : D.host.E} (hg : g ∈ 𝔟 q) :
    (fun i => g * d.a i q) ∈ d.lat Λ 𝔟 := by
  refine ⟨0, Λ.zero_mem, Pi.single q g, fun r => ?_, ?_⟩
  · by_cases h : r = q
    · subst h; rwa [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h]; exact (𝔟 r).zero_mem
  · funext i
    rw [Matrix.mulVec_zero, zero_add, Matrix.mulVec_single, ]
    simp [mul_comm]

end GlobalTheory.AscFin.DepthColumn

set_option maxHeartbeats 1000000 in
open GlobalTheory.AscFin.DepthColumn GlobalTheory.FinPl.FrameLat in

theorem GlobalTheory.AscFin.DepthColumn.scaled_column_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v →
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  Irreducible ϖ →
  Function.Injective κ →
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) →
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) →
  ∀ s : Fin (σ + 1) → k, (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (κ ⟨q.1, by omega⟩) 1) →
  ∀ a ∈ (pcBF W F (σ + 1) h).A₁, ∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v,
    (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i := by
  intro D hO T L μ0 hL sc G W M hM F hF σ h v hv k _ _ _ _ p β ϖ κ hpv hw hβ hϖ hκ hb _ s hs a ha q i
  classical
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hW : G.pl.w v ∈ G.pl.W0 := by
    unfold Places.W0
    convert Finset.mem_image_of_mem G.pl.w hv
  obtain ⟨e₀, he₀, -⟩ := W.cosVec_is
  have hpe : p.pr e₀ = 1 := by
    have := congrArg p.pr (GlobalTheory.DiagLiftFix.idemSum_mul he₀ hW hw)
    rwa [map_mul, GlobalTheory.FrameAt.pr_e, mul_one] at this
  obtain ⟨h2B, heB, -⟩ := hF.hB (σ + 1) h
  obtain ⟨h2J, heJ, -⟩ := hF.hJ (σ + 1) h
  set ξ : k := p.pr (incA D ((-D.host.xi0) ^ (q.1 + 1))) with hξ
  set π : k := (ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)) with hπ

  have hsq : s q * ξ = π := by
    have e1 : π • (fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = ξ • (β.b *ᵥ Pi.single (κ ⟨q.1, by omega⟩) 1) := by
      funext j
      rw [Matrix.mulVec_single_one, Pi.smul_apply, Pi.smul_apply, Matrix.col_apply, hb]
      change π * p.pr (incA D ((F.dJ (σ + 1) h).e j q)) = _
      rw [heJ]
      simp only [colsOf, map_mul, smul_eq_mul]
      rw [mul_left_comm]
      rfl
    have e2 := congrFun (congrArg (β.b' *ᵥ ·) e1) (κ ⟨q.1, by omega⟩)
    simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one] at e2
    have e3 := congrFun (hs q) (κ ⟨q.1, by omega⟩)
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul] at e3
    rw [← e2, mul_left_comm, e3, mul_one]

  let q' : Fin (2 * (σ + 1) + 2 - 1) := Fin.castLE (by omega) q
  obtain ⟨g, hg, hgv⟩ := exists_stair hO G hv p hw hϖ q'
  have hgv' : valuation k (p.pr (incA D g)) = valuation k π := by rw [hgv, hπ, map_pow]; rfl
  have hg0 : p.pr (incA D g) ≠ 0 := by
    rw [← (valuation k).ne_zero_iff, hgv', (valuation k).ne_zero_iff]
    exact pow_ne_zero _ h0
  have hc : π / p.pr (incA D g) ∈ 𝒪[k] := by
    change valuation k _ ≤ 1
    rw [map_div₀, hgv', div_self ((valuation k).ne_zero_iff.2 (pow_ne_zero _ h0))]
  have hx : (fun j => g * (G.colDec (2 * (σ + 1) + 2) (by omega) h).a j q') ∈ G.Λ (.grid (2 * (σ + 1) + 2) 0) := by
    have hlat := G.sp.colLat (2 * (σ + 1) + 2) (by omega) h
    have := ideal_smul_auxiliary_vector_mem_lattice (G.colDec (2 * (σ + 1) + 2) (by omega) h) (G.sp.P (2 * (σ + 1) + 2)).lat _ q' hg
    exact (le_of_eq hlat.symm) this
  have hy := int_mul_mem (sec_mem_intAt p _ hc) hx
  have hZ := GlobalTheory.DepthRowLem.latRow_mulVec D hO T L μ0 hL sc G W M hM (2 * (σ + 1) + 1) (by omega) e₀ he₀ _ ha _ _ hy
  have hval := val_coord_le β hβ (γ := valuation k (ϖ : k) ^ G.pl.depth sc v) (fun b hb => by
    obtain ⟨m, hm, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
    exact val_le_of_mem_modul G.pl sc hv p hw hϖ hm) hZ i
  refine exists_mem_pow hϖ _ (le_of_eq_of_le ?_ hval)
  congr 1
  rw [← smul_eq_mul, ← Pi.smul_apply, ← Matrix.mulVec_smul]
  congr 2
  funext j
  have ha1 : a j q = ∑ l, (F.dB (σ + 1) h).extX _ a j l * (F.dB (σ + 1) h).jX l q := by
    change _ = (a * (F.dB (σ + 1) h).pX * (F.dB (σ + 1) h).jX) j q
    rw [Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
  rw [Pi.smul_apply, smul_eq_mul, ha1, map_sum, Finset.mul_sum]
  change _ = p.pr (∑ l, e₀ * (F.dB (σ + 1) h).extX _ a j l * _)
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e4 : p.pr ((F.dB (σ + 1) h).jX l q) = ξ * p.pr (incA D ((G.colDec (2 * (σ + 1) + 2) (by omega) h).a l q')) := by
    change p.pr (incA D ((F.dB (σ + 1) h).e l q)) = _
    rw [heB]
    simp only [colsOf, map_mul]
    rfl
  simp only [map_mul]
  rw [e4, hpe, p.pr_sec, ← hsq]
  field_simp
