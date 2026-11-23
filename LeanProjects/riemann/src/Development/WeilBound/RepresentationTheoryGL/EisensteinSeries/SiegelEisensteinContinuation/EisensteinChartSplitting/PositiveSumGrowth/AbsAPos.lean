import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.ExistsNotEisContinues
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSiegelEisensteinModerateGrowthConvergenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.PositiveSumGrowth.GrowPf
import GroundTheory.PAdicHodge.NormalizedTrace

noncomputable section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.AutomorphicL2Unitary
open PositivityTheory.RgEis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ResidueKilled.Tr

theorem ext_mul' {G : Type} [Group G] (K P : Subgroup G) (f : G → ℝ) (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q)
    (h0 : ∀ r ∈ P, r ∈ K → f r = 0) {p k : G} (hp : p ∈ P) (hk : k ∈ K) : ext K P f (p * k) = f p := by
  have h : ∃ k' : K, p * k * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  unfold ext
  rw [dif_pos h]
  have hs := h.choose_spec
  have hr : k * (h.choose : G)⁻¹ ∈ K := K.mul_mem hk (K.inv_mem h.choose.2)
  have e : p * k * (h.choose : G)⁻¹ = p * (k * (h.choose : G)⁻¹) := by group
  rw [e] at hs ⊢
  have hrP : k * (h.choose : G)⁻¹ ∈ P := by
    have := P.mul_mem (P.inv_mem hp) hs
    simpa using this
  rw [hadd p hp _ hrP, h0 _ hrP hr, add_zero]

theorem absA_pos (D : D7) (x : (AE D)ˣ) : 0 < absA D x := by
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have h1 := map_mul (absA D) x x⁻¹
  rw [mul_inv_cancel, map_one, h0, zero_mul] at h1
  exact one_ne_zero h1

set_option maxHeartbeats 4000000 in
theorem tTop : TTop := by
  intro hG hT hB hE hP hS hC hSc hDv D V hV a ha hI μ b hμ hb s₁ φ hφ
  have hCM := isCMExt_host D
  have hUn := GlobalTheory.HeckeAdjoint.unramified_host D
  have hHk : GlobalTheory.LFun.IsHecke D.host.F D.host.E μ := hμ
  have hRes := GlobalTheory.LFun.resEtaPow_of_resEta D.host.F D.host.E hCM.2.2.1 μ b hb
  have hgood := hG D.host.F D.host.E D.sp.cm.sig μ b hCM hUn hHk hRes
  obtain ⟨Φ, p, hΓ, hPs, hK, hbd, hlg⟩ := hC D μ V a ha
  obtain ⟨-, -, -, ht2, hlc, -, hKc⟩ := hT D.host.E (AE D) (adCM D.sp.cm.sig μ) hgood (Fin V.rank) (-1)
  have := ht2
  have := hlc
  have hiwa : Iwa ((adCM D.sp.cm.sig μ).uQ (-1) (Set.univ : Set (Fin V.rank))) ((adCM D.sp.cm.sig μ).uK (-1) (Fin V.rank)) := by
    intro y
    obtain ⟨q, k, hk, e⟩ := hI (Φ.symm y * (p : GA D (dblSp V))⁻¹)
    refine ⟨Φ ((q : GA D (dblSp V)) * p), (hPs _).1 (mul_mem q.2 p.2), Φ ((p : GA D (dblSp V))⁻¹ * k * p), (hK k).1 hk, ?_⟩
    have e2 : Φ.symm y = (q : GA D (dblSp V)) * k * p := by rw [← e]; group
    calc y = Φ (Φ.symm y) := (Φ.apply_symm_apply y).symm
      _ = Φ ((q : GA D (dblSp V)) * p * ((p : GA D (dblSp V))⁻¹ * k * p)) := by rw [e2]; congr 1; group
      _ = _ := map_mul Φ _ _
  have hW := hS D.host.F D.host.E D.sp.cm.sig μ b hCM hUn hHk hRes (-1) (Fin V.rank) (by rw [Fintype.card_fin]; exact hV) hiwa
  obtain ⟨-, hparU⟩ := hP D.host.E (AE D) (adCM D.sp.cm.sig μ) hgood (Fin V.rank) (-1) Set.univ
  obtain ⟨hIP', hIH, -⟩ := hparU (by rwa [inf_idem])
  rw [inf_idem] at hIP'
  obtain ⟨-, hmul, -, -, hzero, -⟩ := hB D.host.E (AE D) (adCM D.sp.cm.sig μ) hgood.toGoodL (Fin V.rank ⊕ Fin V.rank)
    (Sum.inl '' (Set.univ : Set (Fin V.rank)))
  set A := adCM D.sp.cm.sig μ with hAdef
  set η : A.U (-1) (Fin V.rank) → ℝ := A.uH (-1) (Set.univ : Set (Fin V.rank)) with hηdef
  set c : ℝ≥0 := absA D (aP V p) with hcdef
  have hc : 0 < c := absA_pos D _
  have hηQ : ∀ y ∈ A.uQ (-1) (Set.univ : Set (Fin V.rank)), ∀ k ∈ A.uK (-1) (Fin V.rank),
      η (y * k) = A.lg (bdet (Sum.inl '' (Set.univ : Set (Fin V.rank))) y.1) := by
    intro y hy k hk
    refine ext_mul' _ _ (fun q : A.U (-1) (Fin V.rank) => A.lg (bdet (Sum.inl '' (Set.univ : Set (Fin V.rank))) q.1)) ?_ ?_ hy hk
    · intro q₁ h₁ q₂ h₂
      show A.lg (bdet _ (q₁.1 * q₂.1)) = _
      rw [hmul q₁.1 h₁ q₂.1 h₂, hgood.lgmul]
    · intro r h₁ h₂
      exact hzero _ h₁ h₂
  have hηP : ∀ q : siegel V, η (Φ q) = Real.log (absA D (aP V q)) := by
    intro q
    have := hηQ (Φ q) ((hPs q).1 q.2) 1 (one_mem _)
    rw [mul_one] at this
    rw [this, hbd q, hlg]
  have hηx : ∀ x : GA D (dblSp V), η (Φ x) = Real.log (hgt V a (x * (p : GA D (dblSp V))⁻¹)) + Real.log c := by
    intro x
    obtain ⟨q, k, hk, e⟩ := hI (x * (p : GA D (dblSp V))⁻¹)
    have e2 : x = (q : GA D (dblSp V)) * p * ((p : GA D (dblSp V))⁻¹ * k * p) := by
      have : x = x * (p : GA D (dblSp V))⁻¹ * p := by group
      rw [this, e]; group
    have h1 : hgt V a (x * (p : GA D (dblSp V))⁻¹) = absA D (aP V q) := by rw [e, hgt_mul V a q hk]
    have h2 : η (Φ x) = Real.log (absA D (aP V (q * p))) := by
      rw [e2, map_mul, hηQ _ ((hPs _).1 (mul_mem q.2 p.2)) _ ((hK k).1 hk), ← Subgroup.coe_mul, hbd (q * p), hlg]
    rw [h1, h2, map_mul, map_mul, NNReal.coe_mul, Real.log_mul (NNReal.coe_pos.2 (absA_pos D _)).ne'
      (NNReal.coe_pos.2 (absA_pos D _)).ne']
  set u : ℂ := s₁ + (V.rank : ℂ) / 2 with hu
  set f : GA D (dblSp V) → ℂ := fun x => φ (x * (p : GA D (dblSp V))⁻¹) * Complex.exp (-u * η (Φ x)) with hf
  obtain ⟨hlaw, hφc, hφK⟩ := (mem_degPS V a).1 hφ
  have hflaw : ∀ q ∈ siegel V, ∀ g, f (q * g) = A.uC (-1) (Fin V.rank) (Φ q) * f g := by
    intro q hq g
    have h1 : φ (q * g * (p : GA D (dblSp V))⁻¹) = μ (aP V ⟨q, hq⟩) * npow (absA D (aP V ⟨q, hq⟩)) u *
        φ (g * (p : GA D (dblSp V))⁻¹) := by
      rw [mul_assoc]; exact hlaw ⟨q, hq⟩ (g * (p : GA D (dblSp V))⁻¹)
    have h2 : η (Φ (q * g)) = η (Φ q) + η (Φ g) := by rw [map_mul]; exact hIH.left _ ((hPs q).1 hq) _
    have h3 := hηP ⟨q, hq⟩
    have h4 : A.uC (-1) (Fin V.rank) (Φ q) = (μ (aP V ⟨q, hq⟩) : ℂ) := by
      show ((A.χ (bdet (Sum.inl '' (Set.univ : Set (Fin V.rank))) (Φ q).1) : Circle) : ℂ) = _
      rw [hbd ⟨q, hq⟩]; rfl
    have e5 : npow (absA D (aP V ⟨q, hq⟩)) u *
        Complex.exp (-u * ((Real.log (absA D (aP V ⟨q, hq⟩)) + η (Φ g) : ℝ) : ℂ)) = Complex.exp (-u * (η (Φ g) : ℂ)) := by
      rw [npow_eq_exp (absA_pos D _), ← Complex.exp_add]; congr 1; push_cast; ring
    simp only [hf]
    rw [h1, h2, h4, show η (Φ q) = Real.log (absA D (aP V ⟨q, hq⟩)) from h3, ← e5]
    ring
  have hfc : Continuous f :=
    (hφc.comp (continuous_id.mul continuous_const)).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (hIH.cont.comp (map_continuous Φ)))))
  have hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : A.uK (-1) (Fin V.rank) => fun x => f (x * Φ.symm k))) := by
    let T : (GA D (dblSp V) → ℂ) →ₗ[ℂ] (GA D (dblSp V) → ℂ) :=
      { toFun := fun ψ x => ψ (x * (p : GA D (dblSp V))⁻¹) * Complex.exp (-u * η (Φ x))
        map_add' := fun ψ ψ' => by funext x; simp [add_mul]
        map_smul' := fun z ψ => by funext x; simp [mul_assoc] }
    have : FiniteDimensional ℂ (kSpan (Khat V a) φ) := hφK
    refine Submodule.finiteDimensional_of_le (S₂ := (kSpan (Khat V a) φ).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have hk' : (p : GA D (dblSp V)) * Φ.symm k * (p : GA D (dblSp V))⁻¹ ∈ Khat V a := by
      refine (hK _).2 ?_
      have e : (p : GA D (dblSp V))⁻¹ * ((p : GA D (dblSp V)) * Φ.symm k * (p : GA D (dblSp V))⁻¹) * p = Φ.symm k := by group
      rw [e, Φ.apply_symm_apply]; exact k.2
    refine ⟨fun g => φ (g * ((p : GA D (dblSp V)) * Φ.symm k * (p : GA D (dblSp V))⁻¹)),
      Submodule.subset_span ⟨_, hk', rfl⟩, ?_⟩
    funext x
    show φ (x * (p : GA D (dblSp V))⁻¹ * ((p : GA D (dblSp V)) * Φ.symm k * (p : GA D (dblSp V))⁻¹)) *
      Complex.exp (-u * η (Φ x)) = φ (x * Φ.symm k * (p : GA D (dblSp V))⁻¹) * Complex.exp (-u * η (Φ (x * Φ.symm k)))
    have e1 : x * (p : GA D (dblSp V))⁻¹ * ((p : GA D (dblSp V)) * Φ.symm k * (p : GA D (dblSp V))⁻¹) =
        x * Φ.symm k * (p : GA D (dblSp V))⁻¹ := by group
    have e2 : η (Φ (x * Φ.symm k)) = η (Φ x) := by rw [map_mul, Φ.apply_symm_apply]; exact hIH.right _ _ k.2
    rw [e1, e2]
  obtain ⟨Am, H, R, hAd, hAne, hHd, hHc, hHe, hHb⟩ := hSc (GA D (dblSp V)) (A.U (-1) (Fin V.rank)) Φ (GQ (dblSp V))
    (siegel V) (A.uΓ (-1) (Fin V.rank)) (A.uK (-1) (Fin V.rank)) (A.uQ (-1) Set.univ) (A.uC (-1) (Fin V.rank)) η
    (Fintype.card (Fin V.rank) : ℝ) hKc hIP' hIH hΓ hPs hW f hfc hflaw hfin
  have hgrow : ∀ r : ℝ, ∃ (C : ℝ) (N : ℕ), ∀ z : ℂ, ‖z‖ ≤ r → ∀ g,
      ‖H z g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N := by
    intro r
    set A₁ : ℝ := max (R + 1) (max (r + 1) ((V.rank : ℝ) + 1)) with hA₁
    set B₁ : ℝ := min (-R - 1) (min (-r - 1) (-1)) with hB₁
    have a1 := le_max_left (R + 1) (max (r + 1) ((V.rank : ℝ) + 1))
    have a2 := le_max_left (r + 1) ((V.rank : ℝ) + 1)
    have a3 := le_max_right (r + 1) ((V.rank : ℝ) + 1)
    have a4 := le_max_right (R + 1) (max (r + 1) ((V.rank : ℝ) + 1))
    have b1 := min_le_left (-R - 1) (min (-r - 1) (-1))
    have b2 := min_le_left (-r - 1) (-1)
    have b3 := min_le_right (-r - 1) (-1)
    have b4 := min_le_right (-R - 1) (min (-r - 1) (-1))
    obtain ⟨M, hM⟩ := hHb A₁ B₁ (by linarith) (by linarith)
    obtain ⟨C₁, N₁, h₁⟩ := posSum_growth' D V hV a ha hI (p : GA D (dblSp V)) c hc (fun x => η (Φ x)) hηx A₁
      (by linarith)
    obtain ⟨C₂, N₂, h₂⟩ := posSum_growth' D V hV a ha hI (p : GA D (dblSp V)) c hc (fun x => η (Φ x)) hηx
      ((Fintype.card (Fin V.rank) : ℝ) - B₁) (by rw [Fintype.card_fin]; linarith)
    refine ⟨|M| * (|C₁| + |C₂|), N₁ + N₂, fun z hz g => ?_⟩
    have hre := abs_le.1 ((Complex.abs_re_le_norm z).trans hz)
    have h₃ := hM z (by linarith) (by linarith) g
    have q₁ := h₁ g
    have q₂ := h₂ g
    beta_reduce at q₁ q₂
    have hone : (1 : ℝ) ≤ GlobalTheory.Grow.height (dblSp V) g := GlobalTheory.Grow.one_le_height _ g
    have w₁ : GlobalTheory.Grow.height (dblSp V) g ^ N₁ ≤ GlobalTheory.Grow.height (dblSp V) g ^ (N₁ + N₂) :=
      pow_le_pow_right₀ hone (by omega)
    have w₂ : GlobalTheory.Grow.height (dblSp V) g ^ N₂ ≤ GlobalTheory.Grow.height (dblSp V) g ^ (N₁ + N₂) :=
      pow_le_pow_right₀ hone (by omega)
    have w₀ : (0 : ℝ) ≤ GlobalTheory.Grow.height (dblSp V) g ^ N₁ := by positivity
    have w₀' : (0 : ℝ) ≤ GlobalTheory.Grow.height (dblSp V) g ^ N₂ := by positivity
    have r₁ : C₁ * GlobalTheory.Grow.height (dblSp V) g ^ N₁ ≤ |C₁| * GlobalTheory.Grow.height (dblSp V) g ^ (N₁ + N₂) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) w₀).trans (mul_le_mul_of_nonneg_left w₁ (abs_nonneg _))
    have r₂ : C₂ * GlobalTheory.Grow.height (dblSp V) g ^ N₂ ≤ |C₂| * GlobalTheory.Grow.height (dblSp V) g ^ (N₁ + N₂) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) w₀').trans (mul_le_mul_of_nonneg_left w₂ (abs_nonneg _))
    calc ‖H z g‖ ≤ M * _ := h₃
      _ ≤ |M| * _ := mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
      _ ≤ |M| * ((|C₁| + |C₂|) * GlobalTheory.Grow.height (dblSp V) g ^ (N₁ + N₂)) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = _ := by ring
  have hCont := hDv D (dblSp V)
    (fun z g => GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (fun x => Complex.exp (z * η (Φ x)) * f x) g) H Am R hAd
    hAne hHd hHc hHe hgrow
  have hflat := GlobalTheory.T.continuesWithModerateGrowth_shift_translate_pow D (dblSp V) _ (fun s g => GlobalTheory.Eis.eis V (flat V a φ s₁ s) g) (p : GA D (dblSp V)) c s₁
    ((V.rank : ℂ) / 2) hc (fun s g => ?_) hCont
  · exact ⟨⟨GlobalTheory.Eis.ContModel.isEisFamily_flat ha hμ hφ, hflat.1⟩, hflat.2⟩
  show GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (flat V a φ s₁ s) g = npow c (s₁ - s) *
    GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (fun x => Complex.exp ((s + (V.rank : ℂ) / 2) * η (Φ x)) * f x)
      (g * (p : GA D (dblSp V)))
  have e4 : GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (fun x => Complex.exp ((s + (V.rank : ℂ) / 2) * η (Φ x)) * f x)
      (g * (p : GA D (dblSp V))) = npow c (s - s₁) * GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (flat V a φ s₁ s) g := by
    rw [← GlobalTheory.Eis.cosetSum_mul_right, ← GlobalTheory.Eis.cosetSum_smul]
    congr 1
    funext x
    simp only [hf, Pi.smul_apply, smul_eq_mul, flatH_apply]
    have hh := hηx (x * (p : GA D (dblSp V)))
    rw [show x * (p : GA D (dblSp V)) * (p : GA D (dblSp V))⁻¹ = x by group] at hh
    rw [hh, npow_eq_exp hc, npow_eq_exp (hgtH_pos _), show x * (p : GA D (dblSp V)) * (p : GA D (dblSp V))⁻¹ = x by group]
    calc _ = φ x * Complex.exp ((s + (V.rank : ℂ) / 2) * ((Real.log (hgt V a x) + Real.log c : ℝ) : ℂ) +
          -u * ((Real.log (hgt V a x) + Real.log c : ℝ) : ℂ)) := by rw [Complex.exp_add]; ring
      _ = φ x * Complex.exp ((Real.log c : ℂ) * (s - s₁) + (Real.log (hgt V a x) : ℂ) * (s - s₁)) := by
          congr 2; rw [hu]; push_cast; ring
      _ = _ := by rw [Complex.exp_add]; ring
  rw [e4, ← mul_assoc, ← npow_add hc, show s₁ - s + (s - s₁) = 0 by ring]
  simp [npow]

end ResidueKilled.Tr
