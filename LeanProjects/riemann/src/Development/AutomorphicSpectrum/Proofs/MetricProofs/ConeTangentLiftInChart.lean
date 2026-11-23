import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolution
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.InverseDerivativeContinuity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open MvPolynomial

section Tangent

variable {σ : Type} [Fintype σ]

def tanIdeal (w v : σ → ℂ) : Ideal (MvPolynomial σ ℂ) where
  carrier := {f | eval w f = 0 ∧ ∑ i, eval w (pderiv i f) * v i = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by simp [ha, hb], ?_⟩
    simp only [map_add, add_mul, Finset.sum_add_distrib, ha', hb', add_zero]
  zero_mem' := by simp
  smul_mem' := by
    rintro c f ⟨h, h'⟩
    refine ⟨by simp [h], ?_⟩
    have : ∀ i, eval w (pderiv i (c • f)) * v i = eval w c * (eval w (pderiv i f) * v i) := by
      intro i
      rw [smul_eq_mul, Derivation.leibniz]
      simp [h]
      ring
    simp only [this, ← Finset.mul_sum, h', mul_zero]

theorem mem_tanIdeal {w v : σ → ℂ} {f : MvPolynomial σ ℂ} :
    f ∈ tanIdeal w v ↔ eval w f = 0 ∧ ∑ i, eval w (pderiv i f) * v i = 0 := Iff.rfl

def tanSub (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Submodule ℂ (σ → ℂ) where
  carrier := {v | ∀ f ∈ I, ∑ i, eval z (pderiv i f) * v i = 0}
  add_mem' := fun ha hb f hf => by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha f hf, hb f hf, add_zero]
  zero_mem' := fun f _ => by simp
  smul_mem' := fun c v hv f hf => by
    have h := hv f hf
    calc ∑ i, eval z (pderiv i f) * (c • v) i = c * ∑ i, eval z (pderiv i f) * v i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
      _ = 0 := by rw [h, mul_zero]

theorem eval_bind_scale (l w : σ → ℂ) (F : MvPolynomial σ ℂ) :
    eval w (bind₁ (fun r => C (l r) * X r) F) = eval (fun r => l r * w r) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p r hp => simp [hp]

theorem pderiv_bind_scale (l : σ → ℂ) (q : σ) (F : MvPolynomial σ ℂ) :
    pderiv q (bind₁ (fun r => C (l r) * X r) F) =
      C (l q) * bind₁ (fun r => C (l r) * X r) (pderiv q F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr, mul_add]
  | mul_X p r hp =>
    rw [map_mul, bind₁_X_right, Derivation.leibniz, hp, Derivation.leibniz (pderiv q) p (X r), map_add,
      pderiv_C_mul]
    simp only [smul_eq_mul, map_mul, bind₁_X_right]
    by_cases h : r = q
    · subst h
      simp only [pderiv_X_self, map_one]
      ring
    · simp only [pderiv_X_of_ne h, map_zero]
      ring

end Tangent

section Blocks

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_pderiv_scale {f : MvPolynomial (Σ k, J k) ℂ} {a : K → ℕ}
    (hf : ReciprocityTheory.AnForm.R.IsMultiHomog f a) (c : K → ℂ) (w : (Σ k, J k) → ℂ) (q : Σ k, J k) :
    c q.1 * eval (fun r => c r.1 * w r) (pderiv q f) = (∏ k, c k ^ a k) * eval w (pderiv q f) := by
  have h1 : bind₁ (fun r : Σ k, J k => C (c r.1) * X r) f = C (∏ k, c k ^ a k) * f := by
    apply MvPolynomial.funext
    intro x
    rw [eval_bind_scale (fun r : Σ k, J k => c r.1), ReciprocityTheory.AnForm.R.eval_smul_of_isMultiHomog hf]
    simp
  have h2 := pderiv_bind_scale (fun r : Σ k, J k => c r.1) q f
  rw [h1, pderiv_C_mul] at h2
  have h3 := congrArg (eval w) h2
  simp only [map_mul, eval_C, eval_bind_scale] at h3
  exact h3.symm

theorem sum_pderiv_torus {s : MvPolynomial (Σ k, J k) ℂ} {a : K → ℕ}
    (hs : ReciprocityTheory.AnForm.R.IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, J k) → ℂ) (h0 : eval z s = 0) :
    ∑ q, eval z (pderiv q s) * (c q.1 * z q) = 0 := by
  classical
  have h : ∀ k, ∑ q, (ReciprocityTheory.AnForm.R.blockWt k q : ℂ) * (z q * eval z (pderiv q s)) = 0 := fun k => by
    rw [ReciprocityTheory.AnForm.R.sum_blockWt_eval hs, h0, mul_zero]
  calc ∑ q, eval z (pderiv q s) * (c q.1 * z q)
      = ∑ k, c k * ∑ q, (ReciprocityTheory.AnForm.R.blockWt k q : ℂ) * (z q * eval z (pderiv q s)) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_eq_single q.1]
        · simp [ReciprocityTheory.AnForm.R.blockWt]
          ring
        · intro k _ hk
          simp [ReciprocityTheory.AnForm.R.blockWt, Ne.symm hk]
        · simp
    _ = 0 := by simp [h]

theorem le_tanIdeal_torusSmul {I : Ideal (MvPolynomial (Σ k, J k) ℂ)}
    (hI : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal I) {z : (Σ k, J k) → ℂ} (hz : ∀ f ∈ I, eval z f = 0)
    (c : K → ℂ) : I ≤ tanIdeal z (torusSmul c z) := by
  obtain ⟨S, hS, rfl⟩ := hI
  rw [Ideal.span_le]
  intro s hs
  obtain ⟨a, ha⟩ := hS s hs
  have h0 := hz s (Ideal.subset_span hs)
  exact ⟨h0, sum_pderiv_torus ha c z h0⟩

theorem finrank_tanSub_le {I : Ideal (MvPolynomial (Σ k, J k) ℂ)}
    (hI : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal I) (p : (k : K) → J k) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) (hzI : ∀ f ∈ I, eval z f = 0) (e : ℕ)
    (hcard : Fintype.card (Σ k, J k) ≤
      Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt (ReciprocityTheory.AnForm.R.chartIdeal I p)
        (ReciprocityTheory.AnForm.R.affCoord p z)) + e) :
    Module.finrank ℂ (tanSub I z) ≤ e + Fintype.card K := by
  classical
  obtain ⟨lam, hlam⟩ : ∃ lam : K → ℂ, lam = fun k => z ⟨k, p k⟩ := ⟨_, rfl⟩
  have hl : ∀ k, lam k ≠ 0 := fun k => by rw [hlam]; exact hz k
  obtain ⟨w, hw⟩ : ∃ w, w = ReciprocityTheory.AnForm.R.affCoord p z := ⟨_, rfl⟩
  rw [← hw] at hcard
  have hwq : ∀ q, w q = z q / lam q.1 := fun q => by rw [hw, hlam]; rfl
  have hzw : z = fun q => lam q.1 * w q := by
    funext q
    rw [hwq, mul_div_cancel₀ _ (hl q.1)]
  have hw1 : ∀ k, w ⟨k, p k⟩ = 1 := fun k => by
    have h : lam k = z ⟨k, p k⟩ := by rw [hlam]
    rw [hwq]
    show z ⟨k, p k⟩ / lam k = 1
    rw [← h]
    exact div_self (hl k)
  have hwI : ∀ f ∈ I, eval w f = 0 := by
    have h := ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hI (fun k => (lam k)⁻¹) z hzI
    have hwe : w = fun q => (lam q.1)⁻¹ * z q := by
      funext q
      rw [hwq, div_eq_inv_mul]
    rwa [← hwe] at h
  let V := ReciprocityTheory.AnForm.R.jacSpanAt (ReciprocityTheory.AnForm.R.chartIdeal I p) w
  let E := dotProductEquiv ℂ (Σ k, J k)
  let Vp : Submodule ℂ ((Σ k, J k) → ℂ) := V.dualAnnihilator.map (E.symm : _ →ₗ[ℂ] _)
  have hVp : Module.finrank ℂ V + Module.finrank ℂ Vp = Fintype.card (Σ k, J k) := by
    have h1 : Module.finrank ℂ Vp = Module.finrank ℂ V.dualAnnihilator :=
      LinearEquiv.finrank_map_eq E.symm _
    rw [h1, Subspace.finrank_add_finrank_dualAnnihilator_eq, Module.finrank_fintype_fun_eq_card]
  let Φ₁ : ((Σ k, J k) → ℂ) →ₗ[ℂ] ((Σ k, J k) → ℂ) :=
    { toFun := fun v q => v q / lam q.1 - v ⟨q.1, p q.1⟩ / lam q.1 * w q
      map_add' := fun v v' => by funext q; simp only [Pi.add_apply]; ring
      map_smul' := fun c v => by funext q; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let Φ₂ : ((Σ k, J k) → ℂ) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun v k => v ⟨k, p k⟩ / lam k
      map_add' := fun v v' => by funext q; simp only [Pi.add_apply]; ring
      map_smul' := fun c v => by funext q; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hΦ₁ : ∀ v q, Φ₁ v q = v q / lam q.1 - v ⟨q.1, p q.1⟩ / lam q.1 * w q := fun _ _ => rfl
  have hΦ₂ : ∀ v k, Φ₂ v k = v ⟨k, p k⟩ / lam k := fun _ _ => rfl
  have hmem : ∀ v ∈ tanSub I z, Φ₁ v ∈ Vp := by
    intro v hv
    have hchart : ReciprocityTheory.AnForm.R.chartIdeal I p ≤ tanIdeal w (Φ₁ v) := by
      refine sup_le ?_ ?_
      · have hI' := hI
        obtain ⟨S, hS, hIS⟩ := hI'
        have hle : Ideal.span S ≤ tanIdeal w (Φ₁ v) := by
          rw [Ideal.span_le]
          intro s hs
          obtain ⟨a, ha⟩ := hS s hs
          have hsI : s ∈ I := hIS ▸ Ideal.subset_span hs
          have h0 := hwI s hsI
          refine ⟨h0, ?_⟩
          have htor := sum_pderiv_torus ha (fun k => v ⟨k, p k⟩ / lam k) w h0
          have hgrad := hv s hsI
          have hsc : ∀ q, eval z (pderiv q s) * v q =
              (∏ k, lam k ^ a k) * (eval w (pderiv q s) * (v q / lam q.1)) := by
            intro q
            have h1 := eval_pderiv_scale ha lam w q
            rw [← hzw] at h1
            field_simp [hl q.1]
            linear_combination (v q) * h1
          have hsum : (∏ k, lam k ^ a k) * ∑ q, eval w (pderiv q s) * (v q / lam q.1) = 0 := by
            rw [Finset.mul_sum, ← hgrad]
            exact Finset.sum_congr rfl fun q _ => (hsc q).symm
          have hsum' : ∑ q, eval w (pderiv q s) * (v q / lam q.1) = 0 :=
            (mul_eq_zero.mp hsum).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hl k))
          calc ∑ i, eval w (pderiv i s) * Φ₁ v i
              = ∑ q, eval w (pderiv q s) * (v q / lam q.1) -
                  ∑ q, eval w (pderiv q s) * (v ⟨q.1, p q.1⟩ / lam q.1 * w q) := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun q _ => by rw [hΦ₁]; ring
            _ = 0 := by rw [hsum', htor, sub_zero]
        rwa [← hIS] at hle
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        refine ⟨by simp [hw1], ?_⟩
        have hx : Φ₁ v ⟨k, p k⟩ = 0 := by
          rw [hΦ₁]
          simp only [hw1, _root_.mul_one, sub_self]
        rw [Finset.sum_eq_single ⟨k, p k⟩]
        · rw [hx, mul_zero]
        · intro q _ hq
          simp [pderiv_X_of_ne (Ne.symm hq)]
        · simp
    have hann : E (Φ₁ v) ∈ V.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      have hVle : V ≤ LinearMap.ker (E (Φ₁ v)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨h, hh, rfl⟩
        have h2 := (hchart hh).2
        show (E (Φ₁ v)) _ = 0
        simp only [E, dotProductEquiv_apply_apply, dotProduct]
        rw [← h2]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      exact fun g hg => hVle hg
    exact ⟨_, hann, E.symm_apply_apply _⟩
  let Φ : tanSub I z →ₗ[ℂ] Vp × (K → ℂ) :=
    LinearMap.prod ((Φ₁.comp (tanSub I z).subtype).codRestrict Vp fun v => hmem v v.2)
      (Φ₂.comp (tanSub I z).subtype)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : Φ₁ v = 0 := congrArg Subtype.val (congrArg Prod.fst hv)
    have h2 : Φ₂ v = 0 := congrArg Prod.snd hv
    refine Subtype.ext ?_
    funext q
    have h3 : Φ₁ v q = 0 := congrFun h1 q
    have h4 : Φ₂ v q.1 = 0 := congrFun h2 q.1
    rw [hΦ₁] at h3
    rw [hΦ₂] at h4
    rw [h4, zero_mul, sub_zero] at h3
    exact (div_eq_zero_iff.mp h3).resolve_right (hl q.1)
  have h5 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h5
  have hcard' : Fintype.card (Σ k, J k) ≤ Module.finrank ℂ V + e := hcard
  omega

theorem finrank_tanSub_pC_le (Ω : Type) [Field Ω] [inst : Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ)
    (hP : IsArithVar (mCoordIdeal y) (e + 1)) (hsm : SmoothGenericFibreM y) {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) :
    Module.finrank ℂ (tanSub (pC (mCoordIdeal y)) z) ≤ e + Fintype.card K := by
  classical
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hP.2.1.2.1
  choose p hp using hz.1
  have hzI : ∀ f ∈ pC (mCoordIdeal y), eval z f = 0 := by
    have h := hz
    rw [mcPts_eq_pC] at h
    exact h.2
  have hy : ∀ k, y ⟨k, p k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, p k⟩ : MRing J) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0]
      simp
    have h1 := hz.2 _ hX
    rw [map_X, eval_X] at h1
    exact hp k h1
  have hw := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh p z hp).1 ⟨hz.1, hzI⟩
  exact finrank_tanSub_le hPh p hp hzI e
    (GlobalTheory.CompanionTheory.Ar.PB.SmoothMan.card_le_finrank_jacSpanAt K J Ω y e hP hsm p hy _ hw)

end Blocks

theorem coneTangent_eq_fderiv_add_torusSmul : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts), ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∀ v, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) ((D.chart a).γ t) v → ∃ (u : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) (c : K → ℂ), v = fderiv ℂ (D.chart a).γ t u + torusSmul c ((D.chart a).γ t) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D a t ht v hv
  classical
  have hz := (D.chart a).mem t ht
  have hdim := finrank_tanSub_pC_le Ω D.y _ D.arith D.smoothGeneric hz
  have hzI : ∀ f ∈ pC (mCoordIdeal D.y), eval ((D.chart a).γ t) f = 0 := by
    have h := hz
    rw [mcPts_eq_pC] at h
    exact h.2
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal D.y)) :=
    isMultiHomogIdeal_pC D.arith.2.1.2.1
  have hcone : ∀ x, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) ((D.chart a).γ t) x →
      x ∈ tanSub (pC (mCoordIdeal D.y)) ((D.chart a).γ t) := by
    intro x hx f hf
    have hle : pC (mCoordIdeal D.y) ≤ tanIdeal ((D.chart a).γ t) x := by
      rw [pC, Ideal.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨hz.2 g hg, hx g hg⟩
    exact (hle hf).2
  let L₁ : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ :=
    (fderiv ℂ (D.chart a).γ t).toLinearMap
  let L₂ : (K → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ :=
    { toFun := fun c => torusSmul c ((D.chart a).γ t)
      map_add' := fun c c' => by funext q; simp only [torusSmul, Pi.add_apply]; ring
      map_smul' := fun r c => by
        funext q; simp only [torusSmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let L := L₁.coprod L₂
  have hL : ∀ u c, L (u, c) = fderiv ℂ (D.chart a).γ t u + torusSmul c ((D.chart a).γ t) := fun _ _ => rfl
  have hrange : LinearMap.range L ≤ tanSub (pC (mCoordIdeal D.y)) ((D.chart a).γ t) := by
    rintro _ ⟨⟨u, c⟩, rfl⟩
    rw [hL]
    refine Submodule.add_mem _ (hcone _ ?_) fun f hf => (le_tanIdeal_torusSmul hPh hzI c hf).2
    refine GroundTheory.Heights₂.Heights.HilbertSamuel.G1.isConeTangent_of_sheet le_rfl
      ((D.chart a).analytic t ht) ?_ u
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with t' ht'
    exact (D.chart a).mem t' ht'
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨u, c⟩ h
    rw [hL] at h
    have hu : u = 0 := (D.chart a).immersion t ht u ⟨fun k => -c k, by
      funext q
      have h1 := congrFun h q
      simp only [torusSmul, Pi.add_apply, Pi.zero_apply] at h1 ⊢
      linear_combination h1⟩
    subst hu
    have h2 : torusSmul c ((D.chart a).γ t) = 0 := by simpa using h
    have hc : c = 0 := by
      funext k
      obtain ⟨i, hi⟩ := hz.1 k
      have h3 : c k * (D.chart a).γ t ⟨k, i⟩ = 0 := congrFun h2 ⟨k, i⟩
      exact (mul_eq_zero.mp h3).resolve_right hi
    rw [hc]
    rfl
  have hfr : Module.finrank ℂ (LinearMap.range L) =
      Fintype.card Ψ * D.j * (D.N - D.j) + Fintype.card K := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have heq := Submodule.eq_of_le_of_finrank_le hrange (by rw [hfr]; exact hdim)
  have hvr : v ∈ LinearMap.range L := heq ▸ hcone v hv
  obtain ⟨⟨u, c⟩, huc⟩ := hvr
  exact ⟨u, c, huc.symm⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
