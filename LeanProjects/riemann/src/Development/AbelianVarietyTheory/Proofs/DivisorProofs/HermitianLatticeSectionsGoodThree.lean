import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsChowFormIntLineZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteType
import Development.AutomorphicArithmetic.LocalEmbeddings.ModelBound
import Development.AutomorphicArithmetic.LocalEmbeddings.CuspSpan
import Development.AutomorphicArithmetic.DivisorFrames.EvenWeightDictionaryFrame
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

attribute [-instance] GlobalTheory.CompHS.cuspAddCommGroup in

private theorem chart_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
    {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r} {Z : Comp Xo c} {G : WTZ E} (hev : Even G.2)
    (σ : c.F →+* ℂ) (hU : IsUnf (U (goodOf c σ)))
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (hspan : ∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2)
    {τ : ℕ} {t : ℝ} {f : cuspOn U Z (τ • G)} (hfm : f ∈ smallL U x V dict Z G τ t) :
    ∃ (R : Subalgebra c.F (Om Z)) (_ : Algebra.FiniteType c.F R) (d : Om Z) (_ : d ≠ 0)
      (hc : ∀ v, d * genPoint Z (cuspOn U Z G) v ∈ R) (hF : d ^ τ * genVal Z (f : Rul Xo c) ∈ R),
      ∀ (N n : ℕ) (b : Module.Basis (Fin N) c.F (cuspOn U Z G)) (g : Matrix (Fin N) (Fin n) c.F)
        (A : (c.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
        GlobalTheory.CompHt.IsFrame (normOn U x V dict Z G) (latOn U Z G) b g A → ∀ φ : R →+* ℂ,
        φ.comp (algebraMap c.F R) = σ →
        ‖φ ⟨_, hF⟩‖ ^ 2 ≤ Real.exp (2 * τ * t) * (∑ a, ‖∑ m, A σ m a * φ ⟨_, hc (b m)⟩‖ ^ 2) ^ τ := by
  obtain ⟨κ, hκn, hκκ, hκσ⟩ : ∃ κ : ℂ →+* ℂ, (∀ a, ‖κ a‖ = ‖a‖) ∧ (∀ a, κ (κ a) = a) ∧
      κ.comp (goodOf c σ) = σ := by
    by_cases h : GoodEmb c σ
    · exact ⟨RingHom.id ℂ, fun _ => rfl, fun _ => rfl, by rw [goodOf, if_pos h]; rfl⟩
    · exact ⟨starRingEnd ℂ, Complex.norm_conj, Complex.conj_conj, by
        rw [goodOf, if_neg h]; exact RingHom.ext fun a => Complex.conj_conj _⟩
  obtain ⟨R, hR, tt, hmem, hread⟩ := GlobalTheory.DegCmp.exists_chart_read_at_frames _ _ _ _ _ _ _ (goodOf c σ)
    (U (goodOf c σ)) hU Z
  have hex : exZ Dw (τ • G) = fun ix => exZ Dw G ix * τ := by
    funext ix
    cases ix <;> simp [exZ, mul_comm]
  have hfs : (f : Rul Xo c) ∈ secZ Xo c (fun ix => exZ Dw G ix * (τ : ℤ)) := by
    rw [← hex]; exact cuspW_le_secZ _ f.2.1
  have hpow : ∀ {M : Type} [Field M] (a : Formalism.L2.Pj.Ix Dw → Mˣ),
      ((∏ ix, a ix ^ (exZ Dw G ix * (τ : ℤ)) : Mˣ) : M) = ((∏ ix, a ix ^ exZ Dw G ix : Mˣ) : M) ^ τ := fun a => by
    rw [← Units.val_pow_eq_pow_val, ← Finset.prod_pow]
    simp only [zpow_mul, zpow_natCast]
  have hF := hmem _ _ hfs
  rw [hpow] at hF
  have hs : ∀ v : cuspOn U Z G, (v : Rul Xo c) ∈ secZ Xo c (exZ Dw G) := fun v => cuspW_le_secZ _ v.2.1
  have hc : ∀ v, ((∏ ix, tt ix ^ exZ Dw G ix : (Om Z)ˣ) : Om Z) * genPoint Z (cuspOn U Z G) v ∈ R :=
    fun v => hmem _ _ (hs v)
  refine ⟨R, hR, _, Units.ne_zero _, hc, hF, fun N n b g A hfr φ hφ => ?_⟩
  obtain ⟨z, hz, a, ha⟩ := hread (κ.comp φ) (by
    rw [RingHom.comp_assoc, hφ]
    refine RingHom.ext fun x => ?_
    conv_lhs => rw [← hκσ]
    exact hκκ _)
  have hb := UpperTheory.even_weight_dictionary_frame _ _ _ _ _ _ _ U x D V dict Z G hev σ hd hspan N n b g A hfr κ hκn hκσ τ t f hfm z hz
  have e1 := ha _ _ hfs ⟨_, hF⟩ (by rw [hpow])
  rw [hpow] at e1
  have e2 := fun m => congrArg κ (ha _ _ (hs (b m)) ⟨_, hc (b m)⟩ rfl)
  simp only [RingHom.comp_apply, hκκ, map_mul] at e1 e2
  generalize ((∏ ix, a ix ^ exZ Dw G ix : ℂˣ) : ℂ) = S at e1 e2
  have e3 : ∑ a, ‖∑ m, A σ m a * φ ⟨_, hc (b m)⟩‖ ^ 2 =
      (∑ a, ‖∑ m, A σ m a * κ (rdU (U (goodOf c σ)) (b m : Rul Xo c) z.1 z.2)‖ ^ 2) * ‖S‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hκn S, ← mul_pow, ← norm_mul, Finset.sum_mul]
    exact congrArg (fun q : ℂ => ‖q‖ ^ 2) (Finset.sum_congr rfl fun m _ => by rw [e2]; ring)
  rw [e3, ← hκn, e1, norm_mul, mul_pow, mul_pow, norm_pow, ← pow_mul, ← pow_mul, mul_comm τ 2, ← mul_assoc, mul_comm]
  exact mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg _) _)

attribute [-instance] GlobalTheory.CompHS.cuspAddCommGroup in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_sections_good_three : Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → ∀ (σ : 𝓞 Y.d.c₂.F →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ (L.B.U k)), GlobalTheory.Cartier.RegAt (GlobalTheory.Cartier.under y) (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) → ‖GlobalTheory.Cartier.ratVal (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) y‖ ^ 2 * Real.exp (-(((8 * i : ℕ) : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * ((8 * i : ℕ) : ℝ) * t) := by
  intro hP D T j Y e o hG hf Z u X _ p L ψ s t _ _ _ _ hM i hi f hfm w hw σ' y k hy hreg
  obtain ⟨σ, rfl⟩ : ∃ σ : Y.d.c₂.F →+* ℂ, σ.comp (algebraMap (𝓞 Y.d.c₂.F) Y.d.c₂.F) = σ' := by
    have hinj : Function.Injective σ' := by
      rw [RingHom.injective_iff_ker_eq_bot]
      by_contra h
      have := Ideal.absNorm_mem (RingHom.ker σ')
      rw [RingHom.mem_ker, map_natCast, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at this
      exact h this
    exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩
  have hσ₀ := goodEmb_goodOf Y.d.c₂ σ
  have hw0 : ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 := fun h => hw (by rw [h, map_zero])
  obtain ⟨th, hrk, -, hdU⟩ := hG.dictU _ hσ₀
  obtain ⟨R, hR, d, hd, hc, hF, hb⟩ := chart_bound (even_wtOf u 0) σ (hG.unf _ hσ₀) hdU.2.2.2.1
    (GlobalTheory.CuspSpan.exists_mem_span hP hG hf Z u w.1.2 hw0 hσ₀) hfm
  exact hM.bound R hR hd (by omega) (Real.exp_pos _).le hc hF σ hb w hw y k hy hreg
