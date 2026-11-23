import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.KappaLatticeEvaluation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOfIsOrtho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BddMemSpanShortGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroEvalFrNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCmPtFrPolyNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsFiniteDimensionalOfGoodEmb
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemHolSubIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongrOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation

namespace GlobalTheory.SupFull

section Generic

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R]

theorem exists_smul_nonneg_of_pow (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (S : Set R)
    (hS : ∀ g ∈ S, ∃ s : K, s ≠ 0 ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v (s • g)) (f : R) (k : ℕ)
    (hf : f ^ (k + 1) ∈ Submodule.span K S) : ∃ s : K, s ≠ 0 ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v (s • f) := by
  have h1 : Submodule.span K S ≤ Submodule.span K (latIn ⊤ Vs hV : Set R) := by
    refine Submodule.span_le.2 fun g hg => ?_
    obtain ⟨s, hs, h⟩ := hS g hg
    rw [← inv_smul_smul₀ hs g]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latIn _ _ _ _).2 ⟨trivial, h⟩))
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ (h1 hf)
  rw [Submodule.span_eq, Submonoid.smul_def, ← algebraMap_smul K] at ht
  have ht0 : algebraMap (𝓞 K) K t ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero t.2
  refine ⟨_, ht0, fun la v hv => ?_⟩
  have h2 := ((mem_latIn _ _ _ _).1 ht).2 la v hv
  have hv' := hV la v hv
  rw [hv'.smul _ _ ht0] at h2 ⊢
  by_cases htop : v f = ⊤
  · rw [htop, EReal.coe_add_top]; exact le_top
  obtain ⟨x, hx⟩ : ∃ x : ℝ, v f = x := ⟨_, (EReal.coe_toReal htop (hv'.ne_bot f)).symm⟩
  have h3 : ∀ m : ℕ, v (f ^ (m + 1)) = ((((m : ℝ) + 1) * x : ℝ) : EReal) := fun m => by
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ, hv'.mul, ih, hx, ← EReal.coe_add]
      congr 1; push_cast; ring
  have h4 : (0 : ℝ) ≤ (vAdd la (algebraMap (𝓞 K) K t) : ℤ) := by exact_mod_cast vAdd_int_nonneg la ht0
  rw [h3, ← EReal.coe_add, EReal.coe_nonneg] at h2
  rw [hx, ← EReal.coe_add, EReal.coe_nonneg]
  rcases le_total 0 x with h | h
  · linarith
  · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (neg_nonneg.2 h)]

theorem fg_latIn (C : Submodule K R) [FiniteDimensional K C] (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (h : ∀ x ∈ C, x ≠ 0 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (φ : R →ₗ[K] K'),
      φ x ≠ 0 ∧ ∀ y ∈ C, (∀ la, ∀ v ∈ Vs la, 0 ≤ v y) → IsIntegral ℤ (φ y)) : (latIn C Vs hV).FG := by
  refine Submodule.FG.map _ (GlobalTheory.fg_of_integral_functionals K C _ fun x hx => ?_)
  obtain ⟨K', _, _, _, φ, h0, h1⟩ := h x.1 x.2 fun e => hx (Subtype.ext e)
  exact ⟨K', inferInstance, inferInstance, inferInstance, φ ∘ₗ C.subtype, h0, fun y hy => h1 y.1 y.2 hy⟩

end Generic

theorem pow_mem_cusp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) (k : ℕ) :
    ∃ a', Dom a' ((k + 1) * n) ∧ f ^ (k + 1) ∈ cusp Xo c U a' ((k + 1) * n) := by
  have hM : CuspMul Xo c U := (Formalism.L2.PjFree.cuspMul_ofPj U).1 (GlobalTheory.CuspProduct.cuspMul_holds E H Dw l Xo c r _)
  induction k with
  | zero => exact ⟨a, by simpa using hd, by simpa using hf⟩
  | succ k ih =>
    obtain ⟨a', h1, h2⟩ := ih
    rw [Nat.succ_mul, pow_succ]
    exact ⟨a' + a, ⟨fun τ => (h1.1 τ).add (hd.1 τ), h1.2.add hd.2⟩, hM _ _ _ _ _ _ h1 hd h2 hf⟩

theorem exists_unf (D : D7) (Q : Par D) (hQ : Q.Pins) (j : ℕ) (hj : InR D j) :
    ∃ U : Formalism.L2.PjFree.Unf (Q.Xo j) Q.c Q.c.F.val.toRingHom D.R.r, Formalism.L2.PjFree.IsUnf U ∧
      (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) ∧ (∀ k, GlobalTheory.Dict.HasPrinc (U.X k) Q.l.M) ∧
      (∀ k la γ, (U.X k).χ la γ = 1) ∧
      ∀ k, ∃ (Xx : DataX D.host.E D.R.r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
        Xx.toData = U.X k ∧ 𝔄 ≠ 0 ∧
        Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  obtain ⟨-, -, hM', -, hx1, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D Q hQ
  obtain ⟨hr, hr1, -⟩ := hnum j hj
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by
    have : cc (-D.host.xi0) = -cc D.host.xi0 := by simp [cc]
    rw [this, GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D]
  have hneg : ∀ τ : D.host.E →+* ℂ, τ (Q.H.rt : D.host.E) = Q.H.rt0 → (τ (-D.host.xi0)).im < 0 := by
    intro τ hτ
    rw [hQ.1.2.1, hQ.1.2.2.1] at hτ
    have h := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
    have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
      rw [h0]
      simpa using d_pos D
    rw [if_pos hpos, Int.cast_one, one_mul] at h
    simpa using h
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum _ Q.H (Q.Dw j) (-(-D.host.xi0))
    (by rw [neg_neg, GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D]) (by rw [neg_neg]; exact cmHost_imaginaryGenerator_ne_zero hP D) _ hr.symm
  obtain ⟨U, hU, hPr, -, hχ, hG, -⟩ := GlobalTheory.FrameUnif.exists_unf_hasPrinc _ Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c
    Q.c.F.val.toRingHom D.R.r (-D.host.xi0) Gm φ (by omega) rfl hξ hneg hφ
  rw [hM'] at hPr
  refine ⟨U, hU, fun k k' => ⟨(hG k).1.trans (hG k').1.symm, (hG k).2.trans (hG k').2.symm⟩,
    fun k ga hga h => ?_, hχ, fun k => ?_⟩
  · refine hPr k ga hga fun x hx => ?_
    obtain ⟨u, hu, e⟩ := h x hx
    exact ⟨u, hu, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  · have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ _ _ U hU k
    have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (U.X k).ξ0 * D.host.AA *
        D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
      rw [(hG k).2, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact hP D.R D.host
    have hM : 0 < Q.l.M := by have := Q.l.three_le; omega
    obtain ⟨Xx, h1, -, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ (U.X k) D.host.AA D.host.AAbar
      (xiR D) Q.l.M
      (fun a => by
        rw [GlobalTheory.LatticeData.cc_eq_conj]
        exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
      hone (fun τ => by rw [(hG k).2, map_neg, norm_neg]; exact xiConst_holds D τ) hx1 hperf.1 hperf.2 hM (hPr k)
    exact ⟨Xx, _, h1, AA_ne_zero hP D, h3⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem fullAt_of_pins (D : D7) (T : Core D) (hQ : T.Q.Pins) (j : ℕ) (hj : InR D j)
    (hU : IsUnf (T.U j T.σ₀)) (w : WeightFamilies.Wt D j) (hn : 0 < w.n) : FullAt T j w := by
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hQ
  obtain ⟨hr, hr1, -⟩ := hnum j hj
  obtain ⟨U', hU', hG, hPr, hχ, hX⟩ := exists_unf D T.Q hQ j hj
  have hbdd : ∀ a n, Dom a n → ∀ f ∈ T.cuspA j a n,
      ∀ k, (U'.X k).IsBddSec (laU U'.toPj a n k) (rdU U'.toPj f k) := fun a n hd f hf =>
    isBddSec_of_isUnf _ _ _ _ (T.Q.Xo j) T.Q.c T.σ₀ _ (T.U j T.σ₀) U'.toPj T.good_σ₀ hU hU' (by omega) a n hd f
      (cusp_le_sec _ _ _ _ _ hf) fun k =>
        (Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds _ _ (((mem_cusp _ _ _ _ _ f).1 hf).2 _ T.good_σ₀) k).1
  constructor
  · haveI : FiniteDimensional T.Q.c.F (cuspW T j w) :=
      GlobalTheory.cuspForms_finiteDimensional_of_goodEmb _ _ _ _ _ _ _ (T.U j) T.σ₀ T.good_σ₀ hU _ _ (dom_wtA w)
    refine fg_latIn _ _ _ fun x hx hx0 => ?_
    letI := T.Q.H.starRing
    have hs := cusp_le_sec _ _ _ _ _ hx
    obtain ⟨z, La, hz, hG0⟩ := GlobalTheory.CMDetect.exists_good_cmPt_frPoly_ne_zero _ _ _ _ (T.Q.Xo j) T.Q.c (fun _ => rfl) _
      U'.toPj hU' hr1 hX _ _ x hs hx0 (hbdd _ _ (dom_wtA w) x hx)
    obtain ⟨y, N, h0, hint⟩ := GlobalTheory.LatFull.CMInt.exists_frame_bounded_denom _ _ _ _ (T.Q.Xo j) T.Q.c z _ La hz _ _ x
      hs hG0
    refine ⟨z.K, inferInstance, inferInstance, inferInstance,
      { toFun := fun F => N * evR (T.Q.Xo j) T.Q.c F y
        map_add' := fun F G => ?_
        map_smul' := fun s F => ?_ }, h0, fun F hF => hint F (cusp_le_sec _ _ _ _ _ hF)⟩
    · rw [← mul_add]
      exact congrArg _ (evalAt_add _ _ F G y)
    · have e : evR (T.Q.Xo j) T.Q.c (s • F) y = algebraMap T.Q.c.F z.K s * evR (T.Q.Xo j) T.Q.c F y :=
        evalAt_smul _ _ s F y
      rw [e, RingHom.id_apply, Algebra.smul_def, mul_left_comm]
  · refine le_antisymm (Submodule.span_le.2 fun f hf => ((mem_latIn _ _ _ f).1 hf).1) fun f hf => ?_
    obtain ⟨a', hd', hf'⟩ := pow_mem_cusp (T.U j) (dom_wtA w) hf (4 * (Module.finrank ℚ D.host.E * D.R.r) + 3)
    obtain ⟨d, nab, hlev, hnab, hroot, hle, hph, hspan⟩ := exists_datum_span _ _ _ _ (T.Q.Xo j) T.Q.c _ _ U' hr1 hA
      T.good_σ₀ hU' hG hPr a' _ hd' (Nat.le_mul_of_pos_right _ hn) fun k ga _ => hχ k _ ga
    have hsf : Squarefree d.l₂.M := by
      rw [hle, hQ.2.1.1,
        Nat.squarefree_mul ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)]
      exact ⟨(D.host.g_prime 0).prime.squarefree, (D.host.g_prime 1).prime.squarefree⟩
    obtain ⟨s, hs, h⟩ := exists_smul_nonneg_of_pow (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) isVal_valSet _
      (exists_smul_short_nonneg D _ _ _ (T.Q.Xo j) T.Q.c _ d hlev hnab hroot hsf hph nab 1 0 a') f _
      (hspan _ (cusp_le_sec _ _ _ _ _ hf') (hbdd _ _ hd' _ hf'))
    rw [← inv_smul_smul₀ hs f]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latIn _ _ _ _).2 ⟨Submodule.smul_mem _ _ hf, h⟩))

end GlobalTheory.SupFull
