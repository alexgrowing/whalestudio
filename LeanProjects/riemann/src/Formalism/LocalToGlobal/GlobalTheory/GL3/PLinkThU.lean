import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrderOfSignGroupDvdTwo
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric MeasureTheory
open scoped Pointwise

instance instHaarMat (N N' : ℕ) : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

instance instHaarVC (D : D7) (N N' : ℕ) : (volume : Measure (VC D N N')).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

variable {D : D7} {N N' : ℕ}

private def sS (z w : VC D N N') : ℂ := ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)

private theorem Hf_eq (T : Tor D) (z w : VC D N N') : Hf D T z w = sS z w / (area T.abelian₂ : ℂ) := rfl

private theorem sS_swap (z w : VC D N N') : sS w z = (starRingEnd ℂ) (sS z w) := by
  simp only [sS, map_sum, map_mul, starRingEnd_self_apply]
  exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem sS_add (z x : VC D N N') :
    sS (z + x) (z + x) = sS z z + sS z x + sS x z + sS x x := by
  simp only [sS, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
  ring

private theorem re_Hf_add (T : Tor D) (z x : VC D N N') :
    (Hf D T (z + x) (z + x)).re =
      (Hf D T z z).re + 2 * (Hf D T z x).re + (Hf D T x x).re := by
  rw [Hf_eq, Hf_eq, Hf_eq, Hf_eq, sS_add, sS_swap z x]
  simp only [Complex.div_ofReal_re, Complex.add_re, Complex.conj_re]
  ring

def dens (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) (z : VC D N N') : ℝ :=
  ‖G z‖ ^ 2 * Real.exp (-Real.pi * (Hf D T z z).re)

theorem dens_U (T : Tor D) (G : VC D N N' → ℂ) (x z : VC D N N') :
    dens D T (U D T x G) z = dens D T G (z + x) := by
  have h := re_Hf_add T z x
  simp only [dens, U, norm_mul, Complex.norm_exp, mul_pow]
  rw [h, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  congr 1
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_ofNat_re, zero_mul, sub_zero, Complex.neg_im, neg_zero]
  push_cast
  ring

theorem norm_al (T : Tor D) (x : VC D N N') : ‖al D T x‖ = 1 := by
  simp [al, norm_zpow]

theorem dens_periodic (T : Tor D) (La' : AddSubgroup (VC D N N')) (G : VC D N N' → ℂ)
    (hG : G ∈ ThSp D T La') (y : VC D N N') (hy : y ∈ La') (z : VC D N N') :
    dens D T G (z + y) = dens D T G z := by
  rw [← dens_U]
  simp only [dens]
  rw [← hG.2 y hy z, norm_mul, norm_al, one_mul]

theorem normSq_U_of_fd (T : Tor D) (La' : AddSubgroup (VC D N N')) [Countable La']
    (hfd : ∃ Fd : Set (VC D N N'), IsAddFundamentalDomain La' Fd volume)
    (G : VC D N N' → ℂ) (hG : G ∈ ThSp D T La') (x : VC D N N') :
    normSq D T La' (U D T x G) = normSq D T La' G := by
  have hF := Classical.epsilon_spec hfd
  show (⨍ z in _, dens D T (U D T x G) z) = ⨍ z in _, dens D T G z
  simp_rw [dens_U]
  set F := Classical.epsilon fun Fd : Set (VC D N N') => IsAddFundamentalDomain La' Fd volume
  have hper : ∀ (g : La') (z : VC D N N'), dens D T G ((g +ᵥ z) + x) = dens D T G (z + x) := by
    intro g z
    show dens D T G ((g : VC D N N') + z + x) = dens D T G (z + x)
    rw [show (g : VC D N N') + z + x = z + x + g by abel]
    exact dens_periodic T La' G hG g g.2 (z + x)
  have h1 : ∫ z in F, dens D T G (z + x) = ∫ z in (-x) +ᵥ F, dens D T G (z + x) :=
    hF.setIntegral_eq (hF.vadd_of_comm (-x)) hper
  have h2 : ∫ z in (-x) +ᵥ F, dens D T G (z + x) = ∫ z in F, dens D T G z := by
    rw [← Set.preimage_vadd]
    simp_rw [add_comm _ x]
    exact (measurePreserving_vadd x volume).setIntegral_preimage_emb
      (MeasurableEquiv.vadd x).measurableEmbedding (dens D T G) F
  rw [setAverage_eq, setAverage_eq, h1, h2]

def FullLat {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (La' : AddSubgroup V) : Prop :=
  DiscreteTopology La' ∧ Submodule.span ℝ (La' : Set V) = ⊤

theorem normSq_U_of_full (T : Tor D) (La' : AddSubgroup (VC D N N')) (hL : FullLat La')
    (G : VC D N N' → ℂ) (hG : G ∈ ThSp D T La') (x : VC D N N') :
    normSq D T La' (U D T x G) = normSq D T La' G := by
  obtain ⟨hd, hs⟩ := hL
  haveI := hd
  haveI : Countable La' := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : DiscreteTopology (AddSubgroup.toIntSubmodule La') := hd
  haveI : IsZLattice ℝ (AddSubgroup.toIntSubmodule La') := ⟨hs⟩
  refine normSq_U_of_fd T La' ⟨_, ZLattice.isAddFundamentalDomain
    (Module.Free.chooseBasis ℤ (AddSubgroup.toIntSubmodule La')) volume⟩ G hG x

theorem LinkThU_of_fd
    (hfd : ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ N N' L L', admitted D N N' L L' →
        Countable (La D (tor0 D cc δ) (N := N) (N' := N') L L') ∧
        ∃ Fd : Set (VC D N N'), IsAddFundamentalDomain (La D (tor0 D cc δ) L L') Fd volume) :
    LinkThU := by
  intro D cc hcc δ hδ N N' L L' hA G hG x
  obtain ⟨hc, hfd'⟩ := hfd D cc hcc δ hδ N N' L L' hA
  haveI := hc
  exact normSq_U_of_fd (tor0 D cc δ) _ hfd' G hG x

theorem LinkThU_of_full
    (hfull : ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ N N' L L', admitted D N N' L L' → FullLat (La D (tor0 D cc δ) (N := N) (N' := N') L L')) :
    LinkThU := by
  intro D cc hcc δ hδ N N' L L' hA G hG x
  exact normSq_U_of_full (tor0 D cc δ) _ (hfull D cc hcc δ hδ N N' L L' hA) G hG x

theorem LinkThUFam_of_ThU (h : LinkThU) : LinkThUFam := by
  intro D cc hcc δ hδ e he N N' L L' hA x
  exact h D cc hcc δ hδ N N' L L' hA _ (he N N' L L' hA).1 x

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

theorem galE_sigmaOf (g : D.R.GG) :
    D.host.galE (D.host.sigmaOf g) = g := by
  exact D.host.gal.apply_symm_apply g

theorem sigmaOf_galE (σ : D.host.E ≃ₐ[ℚ] D.host.E) :
    D.host.sigmaOf (D.host.galE σ) = σ := by
  exact D.host.gal.symm_apply_apply σ

theorem embT_K (τ : D.what₂.Tau) (x : D.host.E) (hx : x ∈ D.host.K) :
    embT D τ x = D.host.φ₀ x := by
  set σ := D.host.sigmaOf ((D.eTau τ : D.R.Psi) : D.R.GG)
  have hb : σ (D.host.sqd) = D.host.sqd := by
    rw [← D.host.galE_mem_Psi_iff]
    rw [galE_sigmaOf]
    exact (D.eTau τ).2
  have hfix : σ x = x := by
    have hx' : x ∈ IntermediateField.adjoin ℚ {D.host.sqd} := hx
    clear hx
    induction hx' using IntermediateField.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hb
    | algebraMap r => rw [eq_ratCast (algebraMap ℚ D.host.E) r]; exact map_ratCast σ r
    | add y z _ _ h1 h2 => rw [map_add, h1, h2]
    | inv y _ h1 => rw [map_inv₀, h1]
    | mul y z _ _ h1 h2 => rw [map_mul, h1, h2]
  show D.host.φ₀ (σ x) = _
  rw [hfix]

theorem emb_cases (φ : D.host.E →+* ℂ) :
    ∃ τ : D.what₂.Tau, φ = embT D τ ∨ φ = (starRingEnd ℂ).comp (embT D τ) := by
  obtain ⟨ρ, hρ⟩ := (D.host.hostEmb D.host.φ₀).2 φ
  set g := D.host.galE ρ
  by_cases hg : g ∈ D.R.Psi
  · refine ⟨D.eTau.symm ⟨g, hg⟩, Or.inl ?_⟩
    rw [← hρ]
    ext x
    simp only [embT, Equiv.apply_symm_apply, Host.emb]
    rw [show g = D.host.galE ρ from rfl, sigmaOf_galE]
  · have hg' : g * D.R.cc ∈ D.R.Psi := by
      rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
      have : g.1.2 = -1 := by
        rcases Int.units_eq_one_or g.1.2 with h | h
        · exact absurd h hg
        · exact h
      show g.1.2 * (D.R.cc).1.2 = 1
      rw [this]; rfl
    set c := D.host.conj
    have hgc : g * D.R.cc = D.host.galE (ρ * c) := by
      rw [D.host.galE_mul, D.host.galE_conjE]
    refine ⟨D.eTau.symm ⟨g * D.R.cc, hg'⟩, Or.inr ?_⟩
    rw [← hρ]
    ext x
    simp only [embT, Equiv.apply_symm_apply, Host.emb, RingHom.comp_apply]
    rw [hgc, sigmaOf_galE]
    have h1 := D.host.conjE_apply
      (D.host.φ₀.comp (ρ : D.host.E →+* D.host.E)) x
    have h2 : D.host.φ₀ (ρ (c x)) = starRingEnd ℂ (D.host.φ₀ (ρ x)) := h1
    show D.host.φ₀ (ρ x) = starRingEnd ℂ (D.host.φ₀ (ρ (c x)))
    rw [h2, Complex.conj_conj]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

def embP (x : D.host.E) : D.what₂.Tau → ℂ := fun τ => embT D τ x

theorem sum_emb_zero {ι : Type*} [Fintype ι] (b : ι → D.host.E) (g : ι → ℝ)
    (h : ∀ τ, ∑ i, (g i : ℂ) * embT D τ (b i) = 0) (φ : D.host.E →+* ℂ) :
    ∑ i, (g i : ℂ) * φ (b i) = 0 := by
  obtain ⟨τ, rfl | rfl⟩ := emb_cases D φ
  · exact h τ
  · have h1 := congrArg (starRingEnd ℂ) (h τ)
    simpa [map_sum, map_mul, Complex.conj_ofReal] using h1

theorem card_tau : Fintype.card D.what₂.Tau = 2 * D.R.ord := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr D.eTau, Formalism.HC.Frame.natCard_Psi]

theorem linInd_embP :
    LinearIndependent ℝ (fun i => embP D (integralBasis D.host.E i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hτ : ∀ τ, ∑ i, (g i : ℂ) * embT D τ (integralBasis D.host.E i) = 0 := by
    intro τ
    have := congrFun hg τ
    simpa [embP, Finset.sum_apply, Complex.real_smul] using this
  have hcard : Fintype.card (D.host.E →ₐ[ℚ] ℂ) =
      Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis (integralBasis D.host.E)]
  let e := (Fintype.equivOfCardEq hcard).symm
  set M := Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => integralBasis D.host.E i) e
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
      (fun i => integralBasis D.host.E i) e
    change _ = M.det ^ 2 at h1
    rw [h0, zero_pow two_ne_zero] at h1
    exact Algebra.discr_not_zero_of_basis ℚ (integralBasis D.host.E)
      ((map_eq_zero_iff (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective).mp h1)
  have hv : Matrix.vecMul (fun i => (g i : ℂ)) M = 0 := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, M, Algebra.embeddingsMatrixReindex,
      Algebra.embeddingsMatrix, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Equiv.refl_symm, Equiv.coe_refl, id, Equiv.symm_symm]
    exact sum_emb_zero D _ g hτ (e j : D.host.E →+* ℂ)
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  intro i
  have := congrFun h0 i
  simpa using this

theorem span_embP :
    Submodule.span ℝ (Set.range (fun b : 𝓞 D.host.E => embP D (b : D.host.E))) = ⊤ := by
  have hne : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)) := by
    rw [← Fintype.card_pos_iff, ← Module.finrank_eq_card_basis (integralBasis D.host.E)]
    exact Module.finrank_pos
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)) =
      Module.finrank ℝ (D.what₂.Tau → ℂ) := by
    rw [← Module.finrank_eq_card_basis (integralBasis D.host.E),
      D.host.finrank_cmField, Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, card_tau,
      smul_eq_mul]
    ring
  have htop := (linInd_embP D).span_eq_top_of_card_eq_finrank hc
  rw [eq_top_iff, ← htop]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨RingOfIntegers.basis D.host.E i, by simp [integralBasis_apply]⟩

theorem finite_ball (r : ℝ) : {x : 𝓞 D.host.E | ∀ τ, ‖embT D τ (x : D.host.E)‖ ≤ r}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le D.host.E ℂ r
  refine Set.Finite.of_finite_image (hfin.subset ?_)
    NumberField.RingOfIntegers.coe_injective.injOn
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨NumberField.RingOfIntegers.isIntegral_coe x, fun φ => ?_⟩
  obtain ⟨τ, rfl | rfl⟩ := emb_cases D φ
  · exact hx τ
  · simpa using hx τ

theorem finite_mat (N N' : ℕ) (r : ℝ) :
    {A : Fin N' → Fin N → 𝓞 D.host.E | ∀ τ i j, ‖embT D τ (A i j : D.host.E)‖ ≤ r}.Finite := by
  have hF := finite_ball D r
  have h2 : {A : Fin N' → Fin N → 𝓞 D.host.E | ∀ τ i j, ‖embT D τ (A i j : D.host.E)‖ ≤ r} =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
        {x : 𝓞 D.host.E | ∀ τ, ‖embT D τ (x : D.host.E)‖ ≤ r} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_pi]
    exact ⟨fun h i _ j _ τ => h τ i j, fun h τ i j => h i (Set.mem_univ _) j (Set.mem_univ _) τ⟩
  rw [h2]
  exact Set.Finite.pi fun _ => Set.Finite.pi fun _ => hF

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

theorem isIntegral_iff_mem (x : D.host.E) :
    x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ x := by
  rw [RingHom.mem_range]
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm

theorem natMul_of (b : 𝓞 D.host.E) (hb : b ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ t : 𝓞 D.host.E, (n : 𝓞 D.host.E) = t * b := by
  have hI : (Ideal.span {b}).comap (algebraMap ℤ (𝓞 D.host.E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hb (Ideal.mem_span_singleton_self b)
      (Algebra.IsIntegral.isIntegral b)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hm
  obtain ⟨a, ha⟩ := hm
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · refine ⟨n, by exact_mod_cast hm0, a, ?_⟩
    rw [ha]
    simp
  · refine ⟨n, by simpa using hm0, -a, ?_⟩
    rw [neg_mul, ha]
    simp

theorem exists_int_mul (T : Finset D.host.E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ T, IsIntegral ℤ ((m : D.host.E) * x) := by
  classical
  have h1 : ∀ x : D.host.E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : D.host.E) * x) := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
    obtain ⟨n, hn, t, ht⟩ := natMul_of D b (nonZeroDivisors.ne_zero hb)
    refine ⟨n, by exact_mod_cast hn, ?_⟩
    have hb' : algebraMap (𝓞 D.host.E) D.host.E b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have h2 : ((n : ℤ) : D.host.E) * (algebraMap (𝓞 D.host.E) D.host.E a /
        algebraMap (𝓞 D.host.E) D.host.E b) = algebraMap (𝓞 D.host.E) D.host.E (t * a) := by
      rw [map_mul, Int.cast_natCast, ← map_natCast (algebraMap (𝓞 D.host.E) D.host.E), ht, map_mul]
      field_simp
    rw [h2]
    exact NumberField.RingOfIntegers.isIntegral_coe _
  have hcast : ∀ m : ℤ, IsIntegral ℤ (m : D.host.E) := fun m => by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ D.host.E m))
  refine Finset.induction_on T ⟨1, one_ne_zero, by simp⟩ ?_
  intro a s _ ih
  obtain ⟨m, hm, hs⟩ := ih
  obtain ⟨k, hk, ha'⟩ := h1 a
  refine ⟨m * k, mul_ne_zero hm hk, fun x hx => ?_⟩
  rcases Finset.mem_insert.1 hx with rfl | hx
  · have h3 : ((m * k : ℤ) : D.host.E) * x = (m : D.host.E) * ((k : D.host.E) * x) := by
      push_cast; ring
    rw [h3]
    exact (hcast m).mul ha'
  · have h3 : ((m * k : ℤ) : D.host.E) * x = (k : D.host.E) * ((m : D.host.E) * x) := by
      push_cast; ring
    rw [h3]
    exact (hcast k).mul (hs x hx)

theorem sd_bounds {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    ∃ m : ℤ, m ≠ 0 ∧ (∀ x ∈ L, ∀ i, IsIntegral ℤ ((m : D.host.E) * x i)) ∧
      (∀ z : Fin N → D.host.E, (∀ i, IsIntegral ℤ (z i)) → (fun i => (m : D.host.E) * z i) ∈ L) := by
  letI := D.host.cmStar
  obtain ⟨⟨s, hs⟩, -, hdual⟩ := hL
  classical
  obtain ⟨m, hm, hmT⟩ := exists_int_mul D (Finset.univ.biUnion fun i => s.image fun g => g i)
  have h1 : ∀ x ∈ L, ∀ i, IsIntegral ℤ ((m : D.host.E) * x i) := by
    let S : Submodule (𝓞 D.host.E) (Fin N → D.host.E) :=
      { carrier := {x | ∀ i, IsIntegral ℤ ((m : D.host.E) * x i)}
        add_mem' := fun {a b} ha hb i => by simpa [mul_add] using (ha i).add (hb i)
        zero_mem' := fun i => by simpa using (isIntegral_zero : IsIntegral ℤ (0 : D.host.E))
        smul_mem' := fun c a ha i => by
          have h2 : (m : D.host.E) * (c • a) i =
              algebraMap (𝓞 D.host.E) D.host.E c * ((m : D.host.E) * a i) := by
            rw [Pi.smul_apply, Algebra.smul_def]
            ring
          rw [h2]
          exact (NumberField.RingOfIntegers.isIntegral_coe c).mul (ha i) }
    have hle : L ≤ S := by
      rw [← hs, Submodule.span_le]
      intro g hg i
      exact hmT _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image.2 ⟨g, hg, rfl⟩⟩)
    exact fun x hx => hle hx
  refine ⟨m, hm, h1, fun z hz => ?_⟩
  rw [hdual]
  intro x hx
  rw [isIntegral_iff_mem D]
  show IsIntegral ℤ (∑ i, star (x i) * ((m : D.host.E) * z i))
  refine IsIntegral.sum _ fun i _ => ?_
  have h3 : star (x i) * ((m : D.host.E) * z i) =
      starRingEnd D.host.E ((m : D.host.E) * x i) * z i := by
    rw [map_mul, map_intCast, starRingEnd_apply]
    ring
  rw [h3]
  exact ((h1 x hx i).map (starRingEnd D.host.E).toIntAlgHom).mul (hz i)

theorem one_mem_inverse_halfDifferent : (1 : D.host.E) ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have := D.host.𝔟_spec.2
    rw [h] at this
    simp at this
  have hle : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤ D.host.AA0 := by
    have := FractionalIdeal.inv_anti_mono
      (I := (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) (J := 1)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hb) one_ne_zero FractionalIdeal.coeIdeal_le_one
    rwa [inv_one] at this
  exact hle (FractionalIdeal.one_mem_one _)

theorem exists_int_clearing_order_denominators : ∃ k : ℤ, k ≠ 0 ∧ ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
    IsIntegral ℤ ((k : D.host.E) * a) := by
  obtain ⟨a, ha, hint⟩ := (D.host.AA0).isFractional
  obtain ⟨n, hn, t, ht⟩ := natMul_of D a (nonZeroDivisors.ne_zero ha)
  refine ⟨n, by exact_mod_cast hn, fun b hb => ?_⟩
  obtain ⟨y, hy⟩ := hint b hb
  have h1 : ((n : ℤ) : D.host.E) * b = algebraMap (𝓞 D.host.E) D.host.E (t * y) := by
    rw [map_mul, hy, Algebra.smul_def, ← mul_assoc, ← map_mul, ← ht]
    simp
  rw [h1]
  exact NumberField.RingOfIntegers.isIntegral_coe _

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits MeasureTheory

variable (D : D7)

theorem hom_upper {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L') :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ A ∈ homL D L L', ∀ i j, IsIntegral ℤ ((M : D.host.E) * A i j) := by
  obtain ⟨m, hm, hLi, hLo⟩ := sd_bounds D L hL
  obtain ⟨m', hm', hL'i, hL'o⟩ := sd_bounds D L' hL'
  refine ⟨m' * m, mul_ne_zero hm' hm, fun A hA => ?_⟩
  let S : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
    { carrier := {A | ∀ i j, IsIntegral ℤ (((m' * m : ℤ) : D.host.E) * A i j)}
      add_mem' := fun {a b} ha hb i j => by
        simpa [mul_add] using (ha i j).add (hb i j)
      zero_mem' := fun i j => by
        simpa using (isIntegral_zero : IsIntegral ℤ (0 : D.host.E))
      smul_mem' := fun c a ha i j => by
        have h2 : ((m' * m : ℤ) : D.host.E) * (c • a) i j =
            algebraMap (𝓞 D.host.E) D.host.E c * (((m' * m : ℤ) : D.host.E) * a i j) := by
          rw [Matrix.smul_apply, Algebra.smul_def]
          ring
        rw [h2]
        exact (NumberField.RingOfIntegers.isIntegral_coe c).mul (ha i j) }
  have hle : homL D L L' ≤ S := by
    refine Submodule.span_le.2 fun A hA => ?_
    show ∀ i j, IsIntegral ℤ (((m' * m : ℤ) : D.host.E) * A i j)
    intro i j
    have hz : ∀ k, IsIntegral ℤ ((Pi.single j (1 : D.host.E) : Fin N → D.host.E) k) := fun k => by
      rcases eq_or_ne k j with rfl | hk
      · simpa using (isIntegral_one : IsIntegral ℤ (1 : D.host.E))
      · simpa [hk] using (isIntegral_zero : IsIntegral ℤ (0 : D.host.E))
    have hx := hLo (Pi.single j (1 : D.host.E) : Fin N → D.host.E) hz
    have he : (A.mulVec (fun k => (m : D.host.E) * (Pi.single j (1 : D.host.E) : Fin N → D.host.E) k)) i =
        (m : D.host.E) * A i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    have h1 := hL'i _ (hA _ hx) i
    rw [he] at h1
    simpa [mul_assoc] using h1
  exact hle hA

theorem hom_lower {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L') :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, IsIntegral ℤ (A i j)) →
      ((M : D.host.E) • A) ∈ homL D L L' := by
  obtain ⟨m, hm, hLi, hLo⟩ := sd_bounds D L hL
  obtain ⟨m', hm', hL'i, hL'o⟩ := sd_bounds D L' hL'
  refine ⟨m * m', mul_ne_zero hm hm', fun A hA => Submodule.subset_span ?_⟩
  intro x hx
  have hz : ∀ i, IsIntegral ℤ ((A.mulVec (fun k => (m : D.host.E) * x k)) i) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact IsIntegral.sum _ fun k _ => (hA i k).mul (hLi x hx k)
  have h1 := hL'o _ hz
  convert h1 using 1
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem YY_upper {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L') :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ B ∈ YYl D L L', ∀ i j, IsIntegral ℤ ((M : D.host.E) * B i j) := by
  obtain ⟨M, hM, hhom⟩ := hom_upper D L L' hL hL'
  obtain ⟨k, hk, hAA⟩ := exists_int_clearing_order_denominators D
  refine ⟨k * M, mul_ne_zero hk hM, fun B hB => ?_⟩
  let S : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
    { carrier := {A | ∀ i j, IsIntegral ℤ (((k * M : ℤ) : D.host.E) * A i j)}
      add_mem' := fun {a b} ha hb i j => by
        simpa [mul_add] using (ha i j).add (hb i j)
      zero_mem' := fun i j => by
        simpa using (isIntegral_zero : IsIntegral ℤ (0 : D.host.E))
      smul_mem' := fun c a ha i j => by
        have h2 : ((k * M : ℤ) : D.host.E) * (c • a) i j =
            algebraMap (𝓞 D.host.E) D.host.E c * (((k * M : ℤ) : D.host.E) * a i j) := by
          rw [Matrix.smul_apply, Algebra.smul_def]
          ring
        rw [h2]
        exact (NumberField.RingOfIntegers.isIntegral_coe c).mul (ha i j) }
  have hle : YYl D L L' ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, A, hA, rfl⟩
    show ∀ i j, IsIntegral ℤ (((k * M : ℤ) : D.host.E) * (a • A) i j)
    intro i j
    have h2 : ((k * M : ℤ) : D.host.E) * (a • A) i j =
        ((k : D.host.E) * a) * ((M : D.host.E) * A i j) := by
      rw [Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [h2]
    exact (hAA a ha).mul (hhom A hA i j)
  exact hle hB

theorem YY_lower {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L') :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, IsIntegral ℤ (A i j)) →
      ((M : D.host.E) • A) ∈ YYl D L L' := by
  obtain ⟨M, hM, hhom⟩ := hom_lower D L L' hL hL'
  exact ⟨M, hM, fun A hA => Submodule.subset_span
    ⟨1, one_mem_inverse_halfDifferent D, (M : D.host.E) • A, hhom A hA, (one_smul _ _).symm⟩⟩

theorem intK (c : 𝓞 D.host.K) : IsIntegral ℤ (((c : D.host.K) : D.host.E)) := by
  exact IsIntegral.algebraMap (B := D.host.E) (NumberField.RingOfIntegers.isIntegral_coe c)

theorem lam_mem (cc : Ideal (𝓞 D.host.K)) (δ w : ℂ) (hw : w ∈ lamOf D cc δ) :
    ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  let f : 𝓞 D.host.K →+ ℂ := (AddMonoidHom.mulLeft δ).comp
    ((D.host.φ₀ : D.host.E →+* ℂ).toAddMonoidHom.comp
      ((algebraMap D.host.K D.host.E).toAddMonoidHom.comp
        (algebraMap (𝓞 D.host.K) D.host.K).toAddMonoidHom))
  have hle : lamOf D cc δ ≤ (Submodule.toAddSubgroup cc).map f := by
    show AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  obtain ⟨c, hc, hcw⟩ := hle hw
  exact ⟨c, hc, hcw.symm⟩

def Phi {N N' : ℕ} (u : ℂ) : (Fin N' → Fin N → 𝓞 D.host.E) →+ VC D N N' where
  toFun A := fun τ i j => u * embT D τ (A i j : D.host.E)
  map_zero' := by funext τ i j; simp
  map_add' A B := by funext τ i j; simp [mul_add]

theorem La_upper {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∃ M : ℤ, M ≠ 0 ∧ La D (tor0 D cc δ) L L' ≤ (Phi D (N := N) (N' := N') (δ / M)).range := by
  obtain ⟨M, hM, hY⟩ := YY_upper D L L' hA.2.2.1 hA.2.2.2
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  refine ⟨M, hM, ?_⟩
  show AddSubgroup.closure _ ≤ _
  rw [AddSubgroup.closure_le]
  rintro _ ⟨w, hw, A, hA', rfl⟩
  obtain ⟨c, -, rfl⟩ := lam_mem D cc δ w hw
  have hint : ∀ i j, IsIntegral ℤ ((M : D.host.E) * (((c : D.host.K) : D.host.E) * A i j)) := by
    intro i j
    have h1 := (intK D c).mul (hY A hA' i j)
    rwa [mul_left_comm] at h1
  choose B hB using fun i j => RingHom.mem_range.1 ((isIntegral_iff_mem D _).2 (hint i j))
  refine ⟨B, ?_⟩
  funext τ i j
  have hB' : ((B i j : 𝓞 D.host.E) : D.host.E) =
      (M : D.host.E) * (((c : D.host.K) : D.host.E) * A i j) := hB i j
  show δ / M * embT D τ ((B i j : 𝓞 D.host.E) : D.host.E) =
    δ * D.host.φ₀ ((c : D.host.K) : D.host.E) * embT D τ (A i j)
  rw [hB', map_mul, map_mul, map_intCast, embT_K D τ _ (SetLike.coe_mem (c : D.host.K))]
  field_simp

theorem disc_of_finite {V : Type*} [NormedAddCommGroup V] (S : AddSubgroup V)
    (h : ∀ r : ℝ, {x | x ∈ S ∧ ‖x‖ ≤ r}.Finite) : DiscreteTopology S := by
  apply discreteTopology_of_isOpen_singleton_zero
  have hT : (({x | x ∈ S ∧ ‖x‖ ≤ 1} : Set V) \ {0}).Finite := (h 1).subset fun x hx => hx.1
  refine isOpen_induced_iff.2 ⟨Metric.ball (0 : V) 1 ∩ (({x | x ∈ S ∧ ‖x‖ ≤ 1} : Set V) \ {0})ᶜ,
    Metric.isOpen_ball.inter hT.isClosed.isOpen_compl, ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
    Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    exact h2 ⟨⟨y.2, h1.le⟩, fun h0 => hne (Subtype.ext h0)⟩
  · rintro rfl
    simp

theorem La_finite {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hδ : δ ≠ 0) (r : ℝ) :
    {x | x ∈ La D (tor0 D cc δ) L L' ∧ ‖x‖ ≤ r}.Finite := by
  obtain ⟨M, hM, hle⟩ := La_upper D L L' hA cc δ
  have hu : (δ / M : ℂ) ≠ 0 := div_ne_zero hδ (by exact_mod_cast hM)
  refine ((finite_mat D N N' (r / ‖(δ / M : ℂ)‖)).image
    (Phi D (N := N) (N' := N') (δ / M))).subset ?_
  rintro x ⟨hx, hxr⟩
  obtain ⟨A, rfl⟩ := hle hx
  refine ⟨A, fun τ i j => ?_, rfl⟩
  have h2 : ‖Phi D (N := N) (N' := N') (δ / M) A τ i j‖ ≤ r :=
    ((norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans (norm_le_pi_norm _ τ))).trans hxr
  change ‖(δ / M : ℂ) * embT D τ (A i j : D.host.E)‖ ≤ r at h2
  rw [norm_mul] at h2
  rw [le_div_iff₀ (norm_pos_iff.2 hu), mul_comm]
  exact h2

def ins {N N' : ℕ} (i0 : Fin N') (j0 : Fin N) (w : D.what₂.Tau → ℂ) : VC D N N' :=
  fun τ i j => if i = i0 ∧ j = j0 then w τ else 0

theorem La_lower {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ (i0 : Fin N') (j0 : Fin N) (b : 𝓞 D.host.E),
      ins D i0 j0 (fun τ => δ * n * embT D τ (b : D.host.E)) ∈ La D (tor0 D cc δ) L L' := by
  obtain ⟨M, hM, hY⟩ := YY_lower D L L' hA.2.2.1 hA.2.2.2
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc.1
  have hI : cc.comap (algebraMap ℤ (𝓞 D.host.K)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hc0 hc (Algebra.IsIntegral.isIntegral c)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap] at hm
  have hcast : D.host.φ₀ (((algebraMap ℤ (𝓞 D.host.K) m : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      (m : ℂ) := by
    simp
  have key : ∀ (i0 : Fin N') (j0 : Fin N) (b : 𝓞 D.host.E),
      ins D i0 j0 (fun τ => δ * ((m * M : ℤ) : ℂ) * embT D τ (b : D.host.E)) ∈
        La D (tor0 D cc δ) L L' := by
    intro i0 j0 b
    have hAint : ∀ i j, IsIntegral ℤ ((Matrix.of fun i j =>
        if i = i0 ∧ j = j0 then (b : D.host.E) else 0 : Matrix (Fin N') (Fin N) D.host.E) i j) := by
      intro i j
      simp only [Matrix.of_apply]
      split_ifs
      · exact NumberField.RingOfIntegers.isIntegral_coe b
      · exact isIntegral_zero
    have hw : δ * D.host.φ₀ (((algebraMap ℤ (𝓞 D.host.K) m : 𝓞 D.host.K) : D.host.K) : D.host.E) ∈
        (tor0 D cc δ).abelian₂ :=
      AddSubgroup.subset_closure ⟨_, hm, rfl⟩
    have hmem : (δ * D.host.φ₀ (((algebraMap ℤ (𝓞 D.host.K) m : 𝓞 D.host.K) : D.host.K) : D.host.E)) •
        embV D (tor0 D cc δ) ((M : D.host.E) • (Matrix.of fun i j =>
          if i = i0 ∧ j = j0 then (b : D.host.E) else 0 : Matrix (Fin N') (Fin N) D.host.E)) ∈
        La D (tor0 D cc δ) L L' :=
      AddSubgroup.subset_closure ⟨_, hw, _, hY _ hAint, rfl⟩
    convert hmem using 1
    funext τ i j
    simp only [ins, Pi.smul_apply, smul_eq_mul, embV, tor0, Matrix.smul_apply, Matrix.of_apply, hcast]
    split_ifs <;> simp [map_mul] <;> ring
  obtain ⟨n, hn⟩ := Int.eq_nat_or_neg (m * M)
  refine ⟨n, ?_, fun i0 j0 b => ?_⟩
  · rintro rfl
    rcases hn with h | h <;> simp [hm0, hM] at h
  · rcases hn with hn | hn
    · have h1 := key i0 j0 b
      rw [hn] at h1
      simpa using h1
    · have h1 := neg_mem (key i0 j0 b)
      rw [hn] at h1
      convert h1 using 1
      funext τ i j
      simp only [ins, Pi.neg_apply]
      split_ifs <;> simp <;> ring

theorem span_La {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) (hδ : δ ≠ 0) :
    Submodule.span ℝ (La D (tor0 D cc δ) L L' : Set (VC D N N')) = ⊤ := by
  obtain ⟨n, hn, hmem⟩ := La_lower D L L' hA cc hcc δ
  have hc : (δ * n : ℂ) ≠ 0 := mul_ne_zero hδ (by exact_mod_cast hn)
  have key : ∀ (i0 : Fin N') (j0 : Fin N) (w : D.what₂.Tau → ℂ),
      ins D i0 j0 w ∈ Submodule.span ℝ (La D (tor0 D cc δ) L L' : Set (VC D N N')) := by
    intro i0 j0 w
    let Ψ : (D.what₂.Tau → ℂ) →ₗ[ℝ] VC D N N' :=
      { toFun := fun u => ins D i0 j0 (fun τ => δ * n * u τ)
        map_add' := fun u u' => by
          funext τ i j
          simp only [ins, Pi.add_apply]
          split_ifs <;> ring
        map_smul' := fun c u => by
          funext τ i j
          simp only [ins, Pi.smul_apply, RingHom.id_apply]
          split_ifs <;> simp [Complex.real_smul] <;> ring }
    have h1 : Submodule.map Ψ (Submodule.span ℝ
        (Set.range fun b : 𝓞 D.host.E => embP D (b : D.host.E))) ≤
        Submodule.span ℝ (La D (tor0 D cc δ) L L' : Set (VC D N N')) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
      exact hmem i0 j0 b
    have hw : (fun τ => (δ * n)⁻¹ * w τ) ∈ Submodule.span ℝ
        (Set.range fun b : 𝓞 D.host.E => embP D (b : D.host.E)) := by
      rw [span_embP D]
      exact Submodule.mem_top
    have h2 := h1 (Submodule.mem_map_of_mem hw)
    have h3 : Ψ (fun τ => (δ * n)⁻¹ * w τ) = ins D i0 j0 w := by
      show ins D i0 j0 (fun τ => δ * n * ((δ * n)⁻¹ * w τ)) = ins D i0 j0 w
      simp only [mul_inv_cancel_left₀ hc]
    rwa [h3] at h2
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ i0, ∑ j0, ins D i0 j0 (fun τ => v τ i0 j0) := by
    funext τ i j
    simp only [Finset.sum_apply]
    rw [Fintype.sum_eq_single i, Fintype.sum_eq_single j]
    · simp [ins]
    · intro j0 hj
      simp [ins, Ne.symm hj]
    · intro i0 hi
      exact Finset.sum_eq_zero fun j0 _ => by simp [ins, Ne.symm hi]
  rw [hv]
  exact Submodule.sum_mem _ fun i0 _ => Submodule.sum_mem _ fun j0 _ => key i0 j0 _

theorem fullLat {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) (hδ : δ ≠ 0) :
    FullLat (La D (tor0 D cc δ) L L') := by
  exact ⟨disc_of_finite _ (La_finite D L L' hA cc δ hδ), span_La D L L' hA cc hcc δ hδ⟩

theorem La_zero {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (cc : Ideal (𝓞 D.host.K)) :
    La D (tor0 D cc 0) L L' = ⊥ := by
  rw [eq_bot_iff]
  show AddSubgroup.closure _ ≤ ⊥
  rw [AddSubgroup.closure_le]
  rintro z ⟨w, hw, A, -, rfl⟩
  obtain ⟨c, -, rfl⟩ := lam_mem D cc 0 w hw
  simp

theorem fd_bot {V : Type*} [AddGroup V] [MeasurableSpace V] (μ : Measure V) :
    IsAddFundamentalDomain (⊥ : AddSubgroup V) Set.univ μ where
  nullMeasurableSet := nullMeasurableSet_univ
  ae_covers := Filter.Eventually.of_forall fun _ => ⟨0, Set.mem_univ _⟩
  aedisjoint := fun a b hab => absurd (Subtype.ext ((AddSubgroup.mem_bot.mp a.2).trans
    (AddSubgroup.mem_bot.mp b.2).symm)) hab

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric MeasureTheory

theorem theta_unitary_linkage : LinkThU := by
  intro D cc hcc δ hδ N N' L L' hA G hG x
  by_cases h0 : δ = 0
  · subst h0
    have hc : Countable (La D (tor0 D cc 0) L L') := by
      rw [FL.La_zero D L L' cc]
      exact Function.Injective.countable (f := fun _ => (0 : ℕ)) fun a b _ =>
        Subtype.ext ((AddSubgroup.mem_bot.1 a.2).trans (AddSubgroup.mem_bot.1 b.2).symm)
    exact normSq_U_of_fd (tor0 D cc 0) _
      ⟨Set.univ, by rw [FL.La_zero D L L' cc]; exact FL.fd_bot _⟩ G hG x
  · exact normSq_U_of_full (tor0 D cc δ) _ (FL.fullLat D L L' hA cc hcc δ h0) G hG x

theorem theta_unitary_family_linkage : LinkThUFam := by
  exact LinkThUFam_of_ThU theta_unitary_linkage

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
