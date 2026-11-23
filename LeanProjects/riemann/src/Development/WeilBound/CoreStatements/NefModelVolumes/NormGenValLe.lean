import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemSpanCuspOn
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
import Development.WeilBound.CoreStatements.ProjectiveValuations.NonemptyToroidalFlagBundle
import Development.WeilBound.CoreStatements.NefModelVolumes.Nvuonto
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExtVanSectionHasCuspFormMatchStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace PositivityTheory.Xj7N

open GlobalTheory GlobalTheory.CompHS GlobalTheory.Adelic

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem fac_nsmul {K : Type} [Field K] [Algebra c.F K] {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {y : FrPt Xo c K}
    {ρ : K →+* ℂ} (F : InfFr U y ρ) (x : ℝ) {G : WTZ E} (hG : Even G.2) (n : ℕ) :
    F.fac x (n • G) = F.fac x G ^ n := by
  have hev : ∀ m : ℕ, Even (m • G).2 := fun m => by
    rw [Prod.smul_snd, nsmul_eq_mul]; exact hG.mul_left _
  induction n with
  | zero =>
    have h0 : Even ((0 : WTZ E).2) := by simp
    have e := F.fac_add x h0 h0
    rw [add_zero] at e
    have hp := F.fac_pos x (0 : WTZ E)
    rw [zero_smul, pow_zero]
    exact mul_left_cancel₀ hp.ne' (by rw [mul_one, ← e])
  | succ n ih =>
    rw [succ_nsmul, F.fac_add x (hev n) hG, ih, pow_succ]

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}

theorem norm_genVal_le {Z : Comp Xo c} {G : WTZ E} {N m : ℕ} {b : Module.Basis (Fin N) c.F (cuspOn U Z G)}
    {g : Matrix (Fin N) (Fin m) c.F} {A : (c.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hF : IsFrame (normOn U x V dict Z G) (latOn U Z G) b g A) (ρ : Om Z →+* ℂ) (f : cuspOn U Z G) :
    ‖ρ (genVal Z (f : Rul Xo c))‖ ≤ petOn U x V dict Z G (ρ.comp (algebraMap c.F (Om Z))) f *
      archSize (A (ρ.comp (algebraMap c.F (Om Z)))) (fun i => ρ (genVal Z ((b i : cuspOn U Z G) : Rul Xo c))) := by
  have e : ρ (genVal Z (f : Rul Xo c)) = ∑ j, (ρ.comp (algebraMap c.F (Om Z))) (b.repr f j) *
      ρ (genVal Z ((b j : cuspOn U Z G) : Rul Xo c)) := by
    conv_lhs => rw [← b.sum_repr f]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Algebra.smul_def, map_mul, RingHom.comp_apply, AlgHom.commutes]
  rw [e]
  have h := norm_pairing_le (hF.herm (ρ.comp (algebraMap c.F (Om Z))))
    (fun j => (ρ.comp (algebraMap c.F (Om Z))) (b.repr f j)) (fun i => ρ (genVal Z ((b i : cuspOn U Z G) : Rul Xo c)))
  rwa [hF.norm] at h

end Generic

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}

theorem norm_small_le (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hd : ∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom) {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2)
    (hspan : ∀ σ, GoodEmb c σ → ∀ P ∈ holSub (U σ).X (modelWt (U σ) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U σ) Z, P w.1 w.2 = Q w.1 w.2)
    {N m : ℕ} {b : Module.Basis (Fin N) c.F (cuspOn U Z G)}
    {g : Matrix (Fin N) (Fin m) c.F} {A : (c.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hF : IsFrame (normOn U x V dict Z G) (latOn U Z G) b g A) (σ : c.F →+* ℂ) (ρ : Om Z →+* ℂ)
    (hρ : ρ.comp (algebraMap c.F (Om Z)) = σ) (τ : ℕ) (t : ℝ) (f : cuspOn U Z (τ • G))
    (hf : f ∈ smallL U x V dict Z G τ t) :
    ‖ρ (genVal Z (f : Rul Xo c))‖ ≤ Real.exp (τ * t) *
      archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn U Z G) : Rul Xo c))) ^ τ := by
  subst hρ
  set σ := ρ.comp (algebraMap c.F (Om Z)) with hσdef
  set S := archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn U Z G) : Rul Xo c))) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hgen : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨F⟩ := InfFr.nonempty hU (genFr hgen Z) ρ
  have hgood : GoodEmb c (goodOf c σ) := goodEmb_goodOf c σ
  have hmem : F.pt ∈ framesOn (U (goodOf c σ)) Z := F.mem_framesOn (liesOn_genFr hgen Z)
  have hval : ∀ (G' : WTZ E) (f' : Rul Xo c), f' ∈ secZ Xo c (exZ Dw G') →
      homN (U (goodOf c σ)) x G' f' F.pt = F.fac x G' * ‖ρ (genVal Z f')‖ := fun G' f' h => F.nrm_eq x h
  have hc := F.fac_pos x G
  have hcusp : ∀ f' ∈ cuspOn U Z G, homN (U (goodOf c σ)) x G f' F.pt ^ 2 ≤
      (F.fac x G * S) ^ 2 * petOn U x V dict Z G σ f' ^ 2 := fun f' hf' => by
    rw [hval G f' (cuspW_le_secZ G hf'.1)]
    have h1 := norm_genVal_le hF ρ ⟨f', hf'⟩
    have h2 : F.fac x G * ‖ρ (genVal Z f')‖ ≤ F.fac x G * S * petOn U x V dict Z G σ f' := by
      have := mul_le_mul_of_nonneg_left h1 hc.le
      simp only at this
      linarith
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg _)) h2 2
  have hB : bergCusp U x V dict Z G σ F.pt ≤ ENNReal.ofReal ((F.fac x G * S) ^ 2) :=
    (bergCusp_le_iff (sq_nonneg _)).2 hcusp
  have hBO : bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G ⟨F.k, F.z⟩ ≤
      ENNReal.ofReal ((F.fac x G * S) ^ 2) := by
    rw [← bergCusp_eq_bergOn (hd _ hgood) (hspan _ hgood) ⟨F.k, F.z⟩ hmem]
    exact hB
  have hsm := hf.2 _ hgood ⟨F.k, F.z⟩ hmem
  have hfs : (f : Rul Xo c) ∈ secZ Xo c (exZ Dw (τ • G)) := cuspW_le_secZ _ f.2.1
  have e1 : homN (U (goodOf c σ)) x (τ • G) f ⟨F.k, F.z.1⟩ = F.fac x G ^ τ * ‖ρ (genVal Z (f : Rul Xo c))‖ := by
    rw [← fac_nsmul F x hG τ]
    exact hval _ _ hfs
  rw [e1] at hsm
  have h3 := hsm.trans (mul_le_mul_right (pow_le_pow_left' hBO τ) _)
  have hn := norm_nonneg (ρ (genVal Z (f : Rul Xo c)))
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (sq_nonneg _), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  have h4 : (F.fac x G ^ τ * ‖ρ (genVal Z (f : Rul Xo c))‖) ^ 2 ≤
      (F.fac x G ^ τ * (Real.exp (τ * t) * S ^ τ)) ^ 2 := by
    refine h3.trans_eq ?_
    have : Real.exp (2 * τ * t) = Real.exp (τ * t) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    ring
  have h5 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h4
  exact le_of_mul_le_mul_left h5 (pow_pos hc τ)

end Main

theorem arch' : NV → Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → ∀ (N m : ℕ) (b : Module.Basis (Fin N) Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (g : Matrix (Fin N) (Fin m) Y.d.c₂.F) (A : (Y.d.c₂.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) b g A → ∀ (σ : Y.d.c₂.F →+* ℂ) (ρ : Om Z →+* ℂ), ρ.comp (algebraMap Y.d.c₂.F (Om Z)) = σ → ∀ τ : ℕ, 0 < τ → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t, ‖ρ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂))‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂))) ^ τ := by
  intro hNV hP D T j Y e o hY hf Z u t hG hB _ _ N m b g A hF σ ρ hρ τ _ f hfs
  have hd : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ g, (Y.dict σ g).2 ∈ ((Y.U σ).X (Y.dict σ g).1).dom := fun σ hσ => by
    obtain ⟨th, hr, hth, hdU⟩ := hY.dictU σ hσ
    exact hdU.2.2.2.1
  have hD : 1 ≤ GlobalTheory.FlagTan.dimFlag (T.Q.Dw j) := by
    have h2 : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q :=
      (hY.unf _ (goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom)).1
    have hm := D.R.two_le_m
    have hk := D.R.m_add_three_le_k
    have h3 : 2 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
      rw [← h2]; unfold Formalism.BasicNotions.Ranks.r; omega
    exact Nat.mul_pos (by omega) (Nat.choose_pos h3)
  obtain ⟨TF⟩ := DifferentiableLines.nonempty_toroidal_flag_bundle hP.p1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.CompHS.TorFlagEx.one_le_of_dimFlag hD)
  have hspan : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ P ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) u 0)),
      ∃ Q ∈ Submodule.span ℂ (rdU (Y.U σ) '' (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0) : Set (Rul Y.d.Xo₂ Y.d.c₂))),
        ∀ w ∈ framesOn (Y.U σ) Z, P w.1 w.2 = Q w.1 w.2 := fun σ hσ P hPh => by
    obtain ⟨m', as, fs, hfs', hPQ⟩ := vuonto' hNV hP D T j Y e o hY hf Z TF u hG hB σ hσ P hPh
    choose g' hg hgf using fun i => GlobalTheory.T.extVan_section_has_cusp_form_match D T j Y e o hY hf Z TF u (fs i) (hfs' i)
    refine ⟨∑ i, as i • rdU (Y.U σ) (g' i), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨g' i, hg i, rfl⟩), fun w hw => ?_⟩
    rw [hPQ w hw]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hgf i σ hσ w hw]
  exact norm_small_le hY.unf hd (AllWt.even_wtOf u 0) hspan hF σ ρ hρ τ t f hfs

end PositivityTheory.Xj7N
