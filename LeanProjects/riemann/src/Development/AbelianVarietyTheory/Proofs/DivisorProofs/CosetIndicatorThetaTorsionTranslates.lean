import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexOfLeNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeTransportPreservesSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ColNorms.IndPres

open Formalism.L2.Th1.H

def Sm (x : ℂ) : Prop := x ∈ TaylorLogMetric.Qbar ∧ ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ x‖ ≤ 1

theorem cj_coe (ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ) (x : ℂ) (hx : x ∈ TaylorLogMetric.Qbar) : StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ x = ρ ⟨x, hx⟩ := by
  simp only [StandardLatticesGL3.cj, TaylorLogMetric.liftM, dif_pos hx]

theorem sm_iff (x : ℂ) : Sm x ↔ ∃ y : TaylorLogMetric.Qbar, (y : ℂ) = x ∧ ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ‖ρ y‖ ≤ 1 := by
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨⟨x, h⟩, rfl, fun ρ => by rw [← cj_coe]; exact h' ρ⟩
  · rintro ⟨y, rfl, h⟩
    exact ⟨y.2, fun ρ => by rw [cj_coe ρ _ y.2]; exact h ρ⟩

theorem sm_zero : Sm 0 := (sm_iff _).2 ⟨0, rfl, fun ρ => by simp⟩

theorem sm_one : Sm 1 := (sm_iff _).2 ⟨1, rfl, fun ρ => by simp⟩

theorem Sm.mul {x y : ℂ} (hx : Sm x) (hy : Sm y) : Sm (x * y) := by
  obtain ⟨u, rfl, hu⟩ := (sm_iff _).1 hx
  obtain ⟨v, rfl, hv⟩ := (sm_iff _).1 hy
  refine (sm_iff _).2 ⟨u * v, rfl, fun ρ => ?_⟩
  rw [map_mul, norm_mul]
  exact mul_le_one₀ (hu ρ) (norm_nonneg _) (hv ρ)

theorem sm_avg {α : Type} (R : Finset α) (f : α → ℂ) (hf : ∀ x ∈ R, Sm (f x)) : Sm ((R.card : ℂ)⁻¹ * ∑ x ∈ R, f x) := by
  classical
  choose! g hg using fun x hx => (sm_iff _).1 (hf x hx)
  refine (sm_iff _).2 ⟨(R.card : TaylorLogMetric.Qbar)⁻¹ * ∑ x ∈ R, g x, ?_, fun ρ => ?_⟩
  · push_cast
    congr 1
    exact Finset.sum_congr rfl fun x hx => (hg x hx).1
  · rw [map_mul, map_inv₀, map_natCast, map_sum, norm_mul, norm_inv, Complex.norm_natCast]
    have h1 : ‖∑ x ∈ R, ρ (g x)‖ ≤ R.card := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun x hx => (hg x hx).2 ρ).trans ?_
      simp
    calc (R.card : ℝ)⁻¹ * ‖∑ x ∈ R, ρ (g x)‖ ≤ (R.card : ℝ)⁻¹ * R.card := by gcongr
      _ ≤ 1 := inv_mul_le_one

theorem sm_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n = 1) : Sm x := by
  have hx : x ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff]
    exact IsAlgebraic.of_pow hn (h ▸ isAlgebraic_one)
  refine (sm_iff _).2 ⟨⟨x, hx⟩, rfl, fun ρ => ?_⟩
  have h1 : (⟨x, hx⟩ : TaylorLogMetric.Qbar) ^ n = 1 := Subtype.ext (by simpa using h)
  have h2 : ‖ρ ⟨x, hx⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2).le

theorem sm_exp (q : ℚ) : Sm (Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ))) := by
  refine sm_of_pow (n := 2 * q.den) (by have := q.den_pos; omega) ?_
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨q.num, ?_⟩
  have : (q : ℂ) * q.den = q.num := by exact_mod_cast q.mul_den_eq_num
  push_cast
  rw [← this]; ring

theorem sm_vol (v : ℝ) : Sm (((Real.sqrt v : ℝ) : ℂ)⁻¹ * ((Real.sqrt v : ℝ) : ℂ)⁻¹ * (v : ℂ)) := by
  rcases le_or_gt v 0 with h | h
  · rw [Real.sqrt_eq_zero_of_nonpos h]; simpa using sm_zero
  · have : ((Real.sqrt v : ℝ) : ℂ)⁻¹ * ((Real.sqrt v : ℝ) : ℂ)⁻¹ * (v : ℂ) = 1 := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt h.le]
      exact inv_mul_cancel₀ (by exact_mod_cast h.ne')
    rw [this]; exact sm_one

theorem sm_inv_mul (x : ℂ) : Sm (x⁻¹ * x) := by
  by_cases h : x = 0
  · simpa [h] using sm_zero
  · rw [inv_mul_cancel₀ h]; exact sm_one

section Gen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem opU_neg_opU (H : Sesq V) (hH : IsHerm H) (s y : V) (e : V → ℂ) (z : V) :
    opU H y e (z + -s) * Complex.exp (-(Real.pi : ℂ) * H z (-s) - (Real.pi : ℂ) * H (-s) (-s) / 2) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H s y : ℂ)) * opU H (y - s) e z := by
  unfold opU
  have h1 : z + -s + y = z + (y - s) := by abel
  rw [h1, mul_assoc, mul_left_comm (Complex.exp _), ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  have h2 : Complex.I * (altE H s y : ℂ) = (H s y - H y s) / 2 := by
    rw [hH s y, Complex.sub_conj]; unfold altE; push_cast; ring
  rw [mul_assoc, h2]
  simp only [map_add, map_neg, map_sub, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.sub_apply]
  ring

theorem xiInd_expand (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (vol : ℝ) (M : AddSubgroup V) (SA SB : Finset V) (e : V → ℂ) (s z : V) :
    ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiInd H α vol M SA SB e s z =
      ∑ y ∈ SB, ((((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (vol : ℂ)) *
        ((SA.card : ℂ)⁻¹ * ∑ t ∈ SA, indL M t * (brk H y t)⁻¹) *
        (α s * α y * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H s y : ℂ)))) * opU H (y - s) e z := by
  unfold xiInd xiS
  rw [opU]
  unfold sumU
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_assoc (hatS _ _ _ _ _ * _), opU_neg_opU H hH]
  unfold hatS
  ring

end Gen

theorem pres_of_finset (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (G F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ) {α : Type} (R : Finset α) (r : α → ℂ)
    (y : α → TaylorLogMetric.VC D a b) (hr : ∀ x ∈ R, Sm (r x)) (hy : ∀ x ∈ R, StandardLatticesGL3.LaQ D T L L' (y x)) (hn : (R.card : ℝ) ≤ n)
    (hF : ∀ w, F w = ∑ x ∈ R, r x * TaylorLogMetric.U D T (y x) G w) : Pres D T L L' G F n := by
  refine ⟨R.card, fun i => r (R.equivFin.symm i), fun i => y (R.equivFin.symm i), fun i => (hr _ (R.equivFin.symm i).2).1,
    fun i => hy _ (R.equivFin.symm i).2, fun ρ => ?_, ?_⟩
  · refine le_trans ?_ hn
    refine (Finset.sum_le_sum fun i _ => (hr _ (R.equivFin.symm i).2).2 ρ).trans ?_
    simp
  · funext w
    rw [hF, StandardLatticesGL3.comb, ← Finset.sum_coe_sort R]
    exact (R.equivFin.symm.sum_comp (fun x : R => r x * TaylorLogMetric.U D T (y x) G w)).symm

theorem HV_herm {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) : IsHerm (Formalism.L2.Ker.HV sc : Sesq (Formalism.L2.Ker.VV ι a b)) := by
  intro x y
  simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  simp only [mul_comm]

section Host

variable {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ}

def rel (z : VCx X.Tau a b) : TaylorLogMetric.VC D a b := fun τ => z (s.iT.symm τ)

theorem HV_eq (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (z w : VCx X.Tau a b) :
    Formalism.L2.Ker.HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc dl))⁻¹ z w = TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc dl) (rel s z) (rel s w) := by
  simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply, TaylorLogMetric.Hf, TaylorLogMetric.tor0, rel]
  rw [s.iT.symm.sum_comp (fun τ => ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j))]
  push_cast
  ring

theorem rel_host (w : TaylorLogMetric.VC D a b) : rel s (fun τ => w (s.iT τ)) = w := by
  funext τ; simp [rel]

theorem rel_embH (hs : s.Ok) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (x : HomE X.E a b) :
    rel s (embH (X.embC s.σ₀) dl x) =
      dl • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc dl) (Matrix.of fun i j => s.iE (x (Pi.single j 1) i)) := by
  funext τ i j
  change dl * s.σ₀ (X.emb (s.iT.symm τ) (x (Pi.single j 1) i)) = dl * TaylorLogMetric.embT D τ (s.iE (x (Pi.single j 1) i))
  rw [hs.1, Equiv.apply_symm_apply]

theorem AA_fg (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    (ambOf s B χ cD).AA.FG := by
  obtain ⟨d, hd, hint⟩ := D.host.AA0.isFractional
  have hd0 : (d : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hd
    exact fun h => this (Subtype.ext h)
  refine Submodule.FG.of_le (Submodule.fg_span_singleton (s.iE.symm (d : D.host.E))⁻¹) ?_
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, -, t, ht, rfl⟩
  obtain ⟨u, hu⟩ := hint t ht
  have hu' : (u : D.host.E) = (d : D.host.E) * t := hu
  have hc : IsIntegral ℤ ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe c).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
  have hi : IsIntegral ℤ (s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * (u : D.host.E))) :=
    (hc.mul (RingOfIntegers.isIntegral_coe u)).map s.iE.symm.toRingHom.toIntAlgHom
  refine Submodule.mem_span_singleton.2 ⟨⟨_, hi⟩, ?_⟩
  change s.iE.symm _ * _ = _
  rw [← map_inv₀, ← map_mul, hu']
  congr 1
  field_simp

end Host

theorem pres_thInd : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → StandardLatticesGL3.Crv D cc dl → ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), IsSdLat L → IsSdLat L' → 0 < c → Pres D (TaylorLogMetric.tor0 D cc dl) (s.lat L) (s.lat L') (B.thMoved a b (s.lat L) (s.lat L')) (toHost s fun z => ((ambOf s B χ cD).chiF a b L L')⁻¹ * (ambOf s B χ cD).thInd S L L' c x z) ((c : ℝ) ^ (Module.finrank ℚ X.E * a * b)) := by
  intro D X s cc dl B χ cD hX hs hC a b S L L' c x hL hL' hc
  have hdl : dl ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc dl hC).2.1
  have : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos
  obtain ⟨hA, hB, hcard⟩ := GlobalTheory.ColNorms.HalfReps.half_reps X.E X.Tau a b (X.embC s.σ₀) dl (ambOf s B χ cD).AA S L L' c hdl (AA_fg s cc dl B χ cD) hL.1 hL'.1 hc
  obtain ⟨hQ, hrat⟩ := GlobalTheory.RationalPoints.rational_points D cc dl hC a b _ _ ((GlobalTheory.SeamSelfDual.seam_selfDual D X s hs a).2 L hL) ((GlobalTheory.SeamSelfDual.seam_selfDual D X s hs b).2 L' hL')
  set Hh : Sesq (Formalism.L2.Ker.VV X.Tau a b) := Formalism.L2.Ker.HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc dl))⁻¹ with hHh
  have hQ' : ∀ u : HomE X.E a b, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) (s.lat L) (s.lat L') (rel s (embH (X.embC s.σ₀) dl u)) := fun u => by
    rw [rel_embH s hs cc]; exact hQ _
  have hE : ∀ u u' : HomE X.E a b, ∃ q : ℚ, altE Hh (embH (X.embC s.σ₀) dl u) (embH (X.embC s.σ₀) dl u') = q := fun u u' => by
    rw [altE, hHh, HV_eq s]
    exact (hrat _ _ (hQ' u) (hQ' u')).1
  have hα : ∀ u : HomE X.E a b, Sm (alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc dl))⁻¹ (embH (X.embC s.σ₀) dl u)) := fun u => by
    obtain ⟨q, hq⟩ := (hrat _ _ (hQ' u) (hQ' u)).2
    have h1 := congrArg Complex.re hq
    rw [Complex.re_ofReal_mul, Complex.ofReal_re] at h1
    rw [alV, alphaQ, Formalism.L2.Th1.H.qOf, HV_eq s, h1]
    exact sm_exp q
  set SA := repsOf (BC (X.embC s.σ₀) dl (ambOf s B χ cD).AA S L L' c)
    (LamC (X.embC s.σ₀) dl (ambOf s B χ cD).AA L L' ⊓ AC (X.embC s.σ₀) dl (ambOf s B χ cD).AA S L L' c) with hSA
  set SB := repsOf (LamC (X.embC s.σ₀) dl (ambOf s B χ cD).AA L L') (BC (X.embC s.σ₀) dl (ambOf s B χ cD).AA S L L' c) with hSB
  set v := volC (ambOf s B χ cD).AA S L L' with hv
  set p := embH (X.embC s.σ₀) dl ((ambOf s B χ cD).liftW S L L' c x) with hp
  set k := (ambOf s B χ cD).chiF a b L L' with hk
  refine pres_of_finset D _ _ _ _ _ _ SB (fun y => (k⁻¹ * k) * ((((Real.sqrt v : ℝ) : ℂ)⁻¹ * ((Real.sqrt v : ℝ) : ℂ)⁻¹ * (v : ℂ)) *
        ((SA.card : ℂ)⁻¹ * ∑ t ∈ SA, indL (BC (X.embC s.σ₀) dl (ambOf s B χ cD).AA S L L' c) t * (brk Hh y t)⁻¹) *
        (alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc dl))⁻¹ p * alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc dl))⁻¹ y *
          Complex.exp ((Real.pi : ℂ) * Complex.I * (altE Hh p y : ℂ))))) (fun y => rel s (y - p)) ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨u, -, rfl⟩ := hB.1 y hy
    refine (sm_inv_mul k).mul (((sm_vol v).mul (sm_avg _ _ fun t ht => ?_)).mul (((hα _).mul (hα _)).mul ?_))
    · obtain ⟨⟨u', -, rfl⟩, -⟩ := hA.1 t ht
      refine Sm.mul ?_ ?_
      · unfold indL
        split_ifs
        exacts [sm_one, sm_zero]
      · obtain ⟨q, hq⟩ := hE u' u
        rw [brk, hq, ← Complex.exp_neg]
        convert sm_exp (2 * q) using 2
        push_cast; ring
    · obtain ⟨q, hq⟩ := hE ((ambOf s B χ cD).liftW S L L' c x) u
      rw [hq]
      exact sm_exp q
  · intro y hy
    obtain ⟨u, -, rfl⟩ := hB.1 y hy
    rw [hp, ← map_sub]
    exact hQ' _
  · exact_mod_cast hcard
  · intro w
    have h1 := xiInd_expand Hh (HV_herm _) (alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc dl))⁻¹) v
      (BC (X.embC s.σ₀) dl (ambOf s B χ cD).AA S L L' c) SA SB ((ambOf s B χ cD).e a b L L') p (fun τ => w (s.iT τ))
    have h2 : toHost s (fun z => k⁻¹ * (ambOf s B χ cD).thInd S L L' c x z) w = k⁻¹ * (((Real.sqrt v : ℝ) : ℂ)⁻¹ *
      xiInd Hh (alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc dl))⁻¹) v
      (BC (X.embC s.σ₀) dl (ambOf s B χ cD).AA S L L' c) SA SB ((ambOf s B χ cD).e a b L L') p (fun τ => w (s.iT τ))) := rfl
    rw [h2, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h3 : opU Hh (y - p) ((ambOf s B χ cD).e a b L L') (fun τ => w (s.iT τ)) =
        k * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) (rel s (y - p)) (B.thMoved a b (s.lat L) (s.lat L')) w := by
      rw [opU, TaylorLogMetric.U, hHh, HV_eq s, HV_eq s, rel_host, ← mul_assoc]
      congr 1
      change k * B.thMoved a b (s.lat L) (s.lat L') (rel s ((fun τ => w (s.iT τ)) + (y - p))) = _
      congr 2
      rw [← rel_host s w]
      funext τ
      simp [rel]
    rw [h3]
    ring

end GlobalTheory.ColNorms.IndPres
