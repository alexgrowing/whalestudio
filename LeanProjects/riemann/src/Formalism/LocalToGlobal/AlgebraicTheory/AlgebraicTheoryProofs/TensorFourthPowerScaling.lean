import Formalism.LocalToGlobal.AlgebraicTheory.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.HasSubstBlock
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.GramFrameCompositionMvExpFact
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.IntOpTwoFreeOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Inertia
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.AgreeOnAdjoin
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenCompatOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenFrameEOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Tensor
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenFinal

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4 opU taylorMv)
open Formalism.L2.Th1.Top (IsLatH thetaZ)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.G (linSub)
open Formalism.L2.Th1.GD (LocNorm InMul thetaLin frameM hOK)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

namespace LocalJetRescaling

theorem norm_natCast (p : ℕ) [Fact p.Prime] {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  rw [ReciprocityTheory.ChartRestriction.L1.norm_natCast_Cl]
  have e : ((N : ℚ) : ℚ_[p]) = (N : ℚ_[p]) := by push_cast; rfl
  rw [← e, Padic.eq_padicNorm]
  exact_mod_cast (padicNorm.nat_eq_one_iff N).2 h

private theorem linSub_scl_eq_rescale {K : Type} [Field K] (m : Type) [Fintype m] [DecidableEq m] (c : K)
    (f : MvPowerSeries m K) : linSub (scl m c) f = MvPowerSeries.rescale (fun _ => c) f := by
  rw [MvPowerSeries.rescale_eq_subst]
  unfold linSub
  congr 1
  funext i
  rw [Finset.sum_eq_single i]
  · simp [scl, MvPowerSeries.smul_eq_C_mul]
  · intro b _ hb
    simp [scl, Ne.symm hb]
  · simp

theorem jets_rescale (hS : LinScale) (p : ℕ) [Fact p.Prime] (m : Type) [Fintype m] [DecidableEq m]
    (N' M : ℕ) (hN' : ¬ p ∣ N') (f : MvPowerSeries m ℂ_[p])
    (hf : JetsIntegral (linSub (scl m ((N' * M : ℕ) : ℂ_[p])) f)) :
    JetsIntegral (linSub (scl m (M : ℂ_[p])) f) := by
  intro κ
  have h1 := hf κ
  rw [linSub_scl_eq_rescale, MvPowerSeries.coeff_rescale] at h1 ⊢
  have hsplit : (κ.prod fun _ e => (((N' * M : ℕ) : ℂ_[p])) ^ e)
      = (κ.prod fun _ e => ((N' : ℂ_[p])) ^ e) * (κ.prod fun _ e => ((M : ℕ) : ℂ_[p]) ^ e) := by
    rw [← Finsupp.prod_mul]
    congr 1
    funext _ e
    push_cast
    exact mul_pow _ _ _
  have hn : ‖κ.prod fun _ e => ((N' : ℂ_[p])) ^ e‖ = 1 := by
    rw [Finsupp.prod, norm_prod]
    apply Finset.prod_eq_one
    intro i _
    rw [norm_pow, norm_natCast p hN', one_pow]
  rw [hsplit] at h1
  have eq : ∀ a b c d : ℂ_[p], a * (b * c * d) = b * (a * (c * d)) := by intros; ring
  rw [eq, norm_mul, hn, one_mul] at h1
  exact h1

end LocalJetRescaling

open LocalJetRescaling

private theorem exists_quadratic_of_mul_mem_lattice (L : PeriodPair) (c : ℂ) (hc : ∀ ω ∈ L.lattice, c * ω ∈ L.lattice) :
    ∃ s t : ℤ, c ^ 2 + s * c + t = 0 := by
  have h1 := hc L.ω₁ (Submodule.subset_span (by simp))
  have h2 := hc L.ω₂ (Submodule.subset_span (by simp))
  rw [PeriodPair.lattice, Submodule.mem_span_pair] at h1 h2
  obtain ⟨a, b, hab⟩ := h1
  obtain ⟨e, f, hef⟩ := h2
  simp only [zsmul_eq_mul] at hab hef
  have n1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have n2 : L.ω₂ ≠ 0 := by simpa using L.indep.ne_zero 1
  refine ⟨-(a + f), a * f - b * e, ?_⟩
  have key : ((c - a) * (c - f) - b * e) * (L.ω₁ * L.ω₂) = 0 := by
    linear_combination (-(c - f) * L.ω₂) * hab + (-(b:ℂ) * L.ω₂) * hef
  rcases mul_eq_zero.1 key with h | h
  · push_cast
    linear_combination h
  · exact absurd h (mul_ne_zero n1 n2)
private theorem norm_le_one_of_monic_int_quadratic {K : Type} [NormedField K] [IsUltrametricDist K] (x : K) (s t : ℤ)
    (h : x ^ 2 + s * x + t = 0) : ‖x‖ ≤ 1 := by
  by_contra hx
  push_neg at hx
  have hs : ‖(s : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K s
  have ht : ‖(t : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K t
  have e : x ^ 2 = -((s : K) * x + t) := by linear_combination h
  have h3 : ‖x ^ 2‖ ≤ max ‖(s : K) * x‖ ‖(t : K)‖ := by
    rw [e, norm_neg]; exact IsUltrametricDist.norm_add_le_max _ _
  rw [norm_pow, norm_mul] at h3
  have : ‖(s : K)‖ * ‖x‖ ≤ ‖x‖ := by nlinarith [norm_nonneg x]
  rcases le_max_iff.1 h3 with h4 | h4 <;> nlinarith
private theorem cmL_squarefree_and_lattice_mem (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (hok : CmOK a₀ b₀ c₀ dK) :
    Squarefree dK ∧ dK % 4 = 3 ∧ Formalism.L2.Th1.CM.HasCMBy dK (cmL a₀ b₀ dK ha hdK lam hlam) ∧
    lam * (a₀ : ℂ) ∈ (cmL a₀ b₀ dK ha hdK lam hlam).lattice ∧
    lam * (a₀ : ℂ) / 2 ∉ (cmL a₀ b₀ dK ha hdK lam hlam).lattice := by
  obtain ⟨hE, _, h8, hp⟩ := hok
  have hodd : Odd b₀ := by
    rcases Int.even_or_odd b₀ with ⟨k, hk⟩ | h
    · exfalso
      subst hk
      have e : (dK : ℤ) = 4 * ((a₀ : ℤ) * c₀ - k * k) := by
        linear_combination -hE
      generalize (a₀ : ℤ) * c₀ - k * k = X at e
      omega
    · exact h
  have hCM0 := Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ dK ha hdK hE hodd
  have hlift : ∀ z ∈ (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK).lattice,
      lam * z ∈ (cmL a₀ b₀ dK ha hdK lam hlam).lattice := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      apply Submodule.subset_span
      rcases hx with rfl | rfl
      · left; rfl
      · right; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul k x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ k hx
  refine ⟨hp.squarefree, by omega, ?_, Submodule.subset_span (by left; rfl), ?_⟩
  · intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · have := hlift _ (hCM0 _ (Submodule.subset_span (by left; rfl)))
        convert this using 1
        simp only [cmL, Formalism.L2.Th1.F.scalePair]; ring
      · have := hlift _ (hCM0 _ (Submodule.subset_span (by right; rfl)))
        convert this using 1
        simp only [cmL, Formalism.L2.Th1.F.scalePair]; ring
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul k x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ k hx
  · intro hmem
    rw [PeriodPair.lattice, Submodule.mem_span_pair] at hmem
    obtain ⟨x, y, hxy⟩ := hmem
    simp only [cmL, Formalism.L2.Th1.F.scalePair, Formalism.L2.Th1.F.cmPair, zsmul_eq_mul] at hxy
    have h' : (a₀ : ℂ) / 2 = x * a₀ + y * Formalism.L2.Th1.F.cmTheta b₀ dK := by
      apply mul_left_cancel₀ hlam
      linear_combination -hxy
    have him := congrArg Complex.im h'
    have hre := congrArg Complex.re h'
    simp [Formalism.L2.Th1.F.cmTheta] at him hre
    have hy : (y : ℝ) = 0 := by
      rcases him with h | h
      · exact_mod_cast h
      · omega
    rw [hy] at hre
    have ha' : (0 : ℝ) < a₀ := by exact_mod_cast ha
    have h2 : (2 * x : ℝ) = 1 := by nlinarith
    have h3 : (2 * x : ℤ) = 1 := by exact_mod_cast h2
    omega
private theorem norm_apply_le_one_of_not_dvd_relIdx (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (hidx : ¬ p ∣ relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)))
    (u : n → ℂ) (hu : InMul L Λ u) (b : Fin 4) (w : Fin 4 × n) :
    ‖ι (g (fun z => if z.1 = b then u z.2 else 0) w)‖ ≤ 1 := by
  set D := relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) with hD
  set y := g (fun z => if z.1 = b then u z.2 else 0) with hy
  have hmul : ∀ ω ∈ L.lattice, ((D : ℂ) * y w) * ω ∈ L.lattice := by
    intro ω hω
    have hin : ω • (fun z : Fin 4 × n => if z.1 = b then u z.2 else 0) ∈ pow4 Λ := by
      intro a
      by_cases hab : a = b
      · subst hab
        have := hu ω hω
        convert this using 1
        funext i
        simp [Formalism.L2.Th1.H.slice]
      · convert Λ.zero_mem using 1
        funext i
        simp [Formalism.L2.Th1.H.slice, hab]
    have himg : ω • y ∈ imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := by
      refine AddSubgroup.mem_map.2 ⟨_, hin, ?_⟩
      simp [hy]
    have hstd := Formalism.L2.Th1.H.relIdx_smul_mem (stdLat L (Fin 4 × n)) _ himg
    have := ((AddSubgroup.mem_pi _).1 hstd) w (Set.mem_univ _)
    have e : ((D : ℂ) * y w) * ω = ((D : ℂ) • ω • y) w := by
      simp
      ring
    rw [e]
    simpa [hD] using this
  obtain ⟨s, t, hst⟩ := exists_quadratic_of_mul_mem_lattice L _ hmul
  have h1 : ‖ι ((D : ℂ) * y w)‖ ≤ 1 := by
    apply norm_le_one_of_monic_int_quadratic _ s t
    have := congrArg ι hst
    simpa using this
  rw [map_mul, norm_mul, map_natCast] at h1
  have hD1 : ‖(D : ℂ_[p])‖ = 1 := LocalJetRescaling.norm_natCast p hidx
  rw [hD1, one_mul] at h1
  exact h1

private theorem sum_inverse_mul_sum_eq_ite_frameM {n ν J : Type} [Fintype n] [DecidableEq n] [Fintype ν] [Fintype J] (p : ℕ) [Fact p.Prime]
    (ι : ℂ ≃+* ℂ_[p]) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (v : J → n → ℂ) (A : J → ν → ℂ_[p])
    (c : ℂ_[p]) (hc : c ≠ 0) (a : Fin 4) (i : n) (b : Fin 4) (x : ν) :
    ∑ w : Fin 4 × n, (c * ι (g.symm (Pi.single w 1) (a, i))) *
        (∑ j : J, ι (g (fun z => if z.1 = b then v j z.2 else 0) w) * (A j x / c))
      = if a = b then frameM (ι : ℂ →+* ℂ_[p]) v A i x else 0 := by
  have key : ∀ u : Fin 4 × n → ℂ, ∑ w, g.symm (Pi.single w 1) (a, i) * g u w = u (a, i) := by
    intro u
    have h : ∑ w, g u w • g.symm (Pi.single w 1) = u := by
      simp_rw [← LinearEquiv.map_smul]
      rw [← map_sum]
      have : ∑ w, g u w • (Pi.single w (1 : ℂ) : Fin 4 × n → ℂ) = g u := by
        ext z
        simp [Finset.sum_apply, Pi.single_apply]
      rw [this]
      simp
    have := congrFun h (a, i)
    rw [Finset.sum_apply] at this
    simpa [mul_comm] using this
  have step : ∀ w : Fin 4 × n, (c * ι (g.symm (Pi.single w 1) (a, i))) *
        (∑ j : J, ι (g (fun z => if z.1 = b then v j z.2 else 0) w) * (A j x / c))
      = ∑ j : J, A j x * ι (g.symm (Pi.single w 1) (a, i) * g (fun z => if z.1 = b then v j z.2 else 0) w) := by
    intro w
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul]
    field_simp
  rw [Finset.sum_congr rfl (fun w _ => step w), Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← map_sum, key]
  unfold frameM
  split_ifs with hab
  · subst hab
    simp [mul_comm]
  · simp [hab]

private theorem jetsIntegral_sum_C_mul {p : ℕ} [Fact p.Prime] {X κ : Type} [Fintype κ] (r : κ → ℂ_[p])
    (f : κ → MvPowerSeries X ℂ_[p]) (hr : ∀ k, ‖r k‖ ≤ 1) (hf : ∀ k, JetsIntegral (f k)) :
    JetsIntegral (∑ k, MvPowerSeries.C (r k) * f k) := by
  intro e
  rw [map_sum, Finset.mul_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro k _
  rw [MvPowerSeries.coeff_C_mul]
  calc ‖(Formalism.DworkPowerSeriesWeights.mfact e : ℂ_[p]) * (r k * MvPowerSeries.coeff e (f k))‖
        = ‖r k‖ * ‖(Formalism.DworkPowerSeriesWeights.mfact e : ℂ_[p]) * MvPowerSeries.coeff e (f k)‖ := by
          rw [← norm_mul]; ring_nf
    _ ≤ 1 * 1 := mul_le_mul (hr k) (hf k e) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1
private theorem norm_jetPair_le_one {p : ℕ} [Fact p.Prime] {X : Type} (P : MvPolynomial X ℂ_[p]) (T : MvPowerSeries X ℂ_[p])
    (hP : ∀ k, ‖MvPolynomial.coeff k P‖ ≤ 1) (hT : JetsIntegral T) : ‖jetPair P T‖ ≤ 1 := by
  unfold jetPair
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro e _
  rw [mul_assoc, norm_mul]
  exact mul_le_one₀ (hP e) (norm_nonneg _) (hT e)

theorem etLoc_of (h1 : TensZEt) (h2 : EtThetaZ) (h3 : LinScale) : EtLoc := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hok n _ _ h Λ hsd hcm θ hθ p _ hp2 hpd ι hcur hloc κx _ r t α M hr hα
    hια hM hαt hMt J _ v hv ν _ A hA
  obtain ⟨g₁, ε, hiso, hidx, hidx0, hε, htens⟩ := hloc
  obtain ⟨hsq, h43, hCM, hω0, hω2⟩ := cmL_squarefree_and_lattice_mem a₀ b₀ c₀ dK ha hdK lam hlam hok
  have hMne : (M : ℂ_[p]) ≠ 0 := by exact_mod_cast hM.ne'
  have hk : ∀ k, JetsIntegral (linSub (frameM (ι : ℂ →+* ℂ_[p]) v A)
      ((MvPowerSeries.map (ι : ℂ →+* ℂ_[p])) (taylorMv (opU (matH h) (t k) θ)))) := by
    intro k
    obtain ⟨κ, hκ, r', s, N', hr', hN'0, hN'p, hsα, hsM, heq⟩ :=
      h1 a₀ b₀ c₀ dK ha hdK lam hlam hok n h Λ hsd hcm θ hθ p ι g₁ ε hiso hidx hidx0 hε htens
        (t k) α M hα hM (hαt k) (hMt k)
    have hq : IsQInt dK ((N' : ℂ) * α) := by
      obtain ⟨m1, m2, hm⟩ := hα
      exact ⟨N' * m1, N' * m2, by rw [hm]; push_cast; ring⟩
    have hn : ‖ι ((N' : ℂ) * α)‖ = 1 := by
      rw [map_mul, norm_mul, map_natCast, LocalJetRescaling.norm_natCast p hN'p, hια, one_mul]
    have hz := h2 dK (cmL a₀ b₀ dK ha hdK lam hlam) hsq h43 hCM p ι hp2 hpd hcur (lam * a₀) hω0 hω2
      κ (Fin 4 × n) r' s ((N' : ℂ) * α) (N' * M) hq hn (Nat.mul_pos hN'0 hM) hr' hsα hsM
    have hz2 := jets_rescale h3 p (Fin 4 × n) N' M hN'p _ hz
    rw [← heq, (h3 ℂ_[p] (Fin 4 × n) (Fin 4 × n) (M : ℂ_[p]) _ _).1] at hz2
    refine Formalism.L2.Th1.GD.JetsLinZ_proof ℂ_[p] n _ _ hz2 ν (frameM (ι : ℂ →+* ℂ_[p]) v A)
      (fun w y => ∑ j : J, ι (g₁ (fun z => if z.1 = y.1 then v j z.2 else 0) w) * (A j y.2 / (M : ℂ_[p])))
      ?_ ?_
    · intro w y
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      intro j _
      rw [norm_mul, norm_div]
      have e1 := norm_apply_le_one_of_not_dvd_relIdx (cmL a₀ b₀ dK ha hdK lam hlam) Λ g₁ p ι hidx (v j) (hv j) y.1 w
      have e2 : ‖A j y.2‖ / ‖(M : ℂ_[p])‖ ≤ 1 := by
        rw [div_le_one (norm_pos_iff.2 hMne)]
        exact hA j y.2
      exact mul_le_one₀ e1 (by positivity) e2
    · intro a i b x
      exact sum_inverse_mul_sum_eq_ite_frameM p ι g₁ v A _ hMne a i b x
  have hJ : JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) := by
    unfold thetaLin
    exact jetsIntegral_sum_C_mul r _ hr hk
  exact ⟨hJ, fun P hP => norm_jetPair_le_one P _ hP hJ⟩

end Formalism.L2.AlgTh
