import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrderOfSignGroupDvdTwo
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions MeasureTheory
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB
open scoped Pointwise

instance instHaarMat (N N' : ℕ) : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

instance instHaarVC (D : Car) (N N' : ℕ) : (volume : Measure (VC D N N')).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

variable {D : Car} {N N' : ℕ}

private def sS (z w : VC D N N') : ℂ := ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)

private theorem Hf_eq (T : Tor D) (z w : VC D N N') : Formalism.L2.Ker.Cd.TaylorLogMetric.Hf D T z w = sS z w / (area T.abelian₂ : ℂ) := rfl

private theorem sS_swap (z w : VC D N N') : sS w z = (starRingEnd ℂ) (sS z w) := by
  simp only [sS, map_sum, map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem sS_add (z x : VC D N N') :
    sS (z + x) (z + x) = sS z z + sS z x + sS x z + sS x x := by
  simp only [sS, Pi.add_apply, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

private theorem re_Hf_add (T : Tor D) (z x : VC D N N') :
    (Formalism.L2.Ker.Cd.TaylorLogMetric.Hf D T (z + x) (z + x)).re =
      (Formalism.L2.Ker.Cd.TaylorLogMetric.Hf D T z z).re + 2 * (Formalism.L2.Ker.Cd.TaylorLogMetric.Hf D T z x).re + (Formalism.L2.Ker.Cd.TaylorLogMetric.Hf D T x x).re := by
  simp only [Hf_eq, Complex.div_ofReal_re, sS_add, Complex.add_re, sS_swap x z, Complex.conj_re]
  ring

def dens (D : Car) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) (z : VC D N N') : ℝ :=
  ‖G z‖ ^ 2 * Real.exp (-Real.pi * (Formalism.L2.Ker.Cd.TaylorLogMetric.Hf D T z z).re)

theorem dens_U (T : Tor D) (G : VC D N N' → ℂ) (x z : VC D N N') :
    dens D T (U D T x G) z = dens D T G (z + x) := by
  simp only [dens, U, norm_mul, Complex.norm_exp, mul_pow]
  rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add, re_Hf_add]
  congr 2
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_re, Complex.normSq_ofNat]
  norm_num
  ring

theorem norm_al (T : Tor D) (x : VC D N N') : ‖al D T x‖ = 1 := by
  simp [al, norm_zpow]

theorem dens_periodic (T : Tor D) (La' : AddSubgroup (VC D N N')) (G : VC D N N' → ℂ)
    (hG : G ∈ ThSp D T La') (y : VC D N N') (hy : y ∈ La') (z : VC D N N') :
    dens D T G (z + y) = dens D T G z := by
  rw [← dens_U]
  have h := hG.2 y hy z
  simp only [dens]
  rw [← h, norm_mul, norm_al, one_mul]

theorem normSq_U_of_fd (T : Tor D) (La' : AddSubgroup (VC D N N')) [Countable La']
    (hfd : ∃ Fd : Set (VC D N N'), IsAddFundamentalDomain La' Fd volume)
    (G : VC D N N' → ℂ) (hG : G ∈ ThSp D T La') (x : VC D N N') :
    normSq D T La' (U D T x G) = normSq D T La' G := by
  have hspec : IsAddFundamentalDomain La'
      (Classical.epsilon (fun Fd => IsAddFundamentalDomain La' Fd volume)) volume :=
    Classical.epsilon_spec hfd
  set Fd := Classical.epsilon (fun Fd : Set (VC D N N') => IsAddFundamentalDomain La' Fd volume)
  change ⨍ z in Fd, dens D T (U D T x G) z = ⨍ z in Fd, dens D T G z
  simp only [dens_U]
  have hFd' : IsAddFundamentalDomain La' (x +ᵥ Fd) volume := hspec.vadd_of_comm x
  have hint : ∫ z in Fd, dens D T G (z + x) = ∫ z in Fd, dens D T G z := by
    have h1 : ∫ z in Fd, dens D T G (z + x) = ∫ z in (fun z => x + z) '' Fd, dens D T G z := by
      have e := (measurePreserving_add_left volume x).setIntegral_image_emb
        (measurableEmbedding_addLeft x) (dens D T G) Fd
      rw [e]
      simp only [add_comm x]
    have himg : (fun z => x + z) '' Fd = x +ᵥ Fd := by rw [← Set.image_vadd]; rfl
    rw [h1, himg]
    refine hFd'.setIntegral_eq hspec fun g z => ?_
    rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
    exact dens_periodic T La' G hG g g.2 z
  rw [setAverage_eq, setAverage_eq, hint]

def FullLat {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (La' : AddSubgroup V) : Prop :=
  DiscreteTopology La' ∧ Submodule.span ℝ (La' : Set V) = ⊤

theorem normSq_U_of_full (T : Tor D) (La' : AddSubgroup (VC D N N')) (hL : FullLat La')
    (G : VC D N N' → ℂ) (hG : G ∈ ThSp D T La') (x : VC D N N') :
    normSq D T La' (U D T x G) = normSq D T La' G := by
  obtain ⟨hd, hs⟩ := hL
  let L : Submodule ℤ (VC D N N') := La'.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI : Countable La' := (inferInstance : Countable L)
  refine normSq_U_of_fd T La' ?_ G hG x
  exact ⟨_, ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) volume⟩

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

theorem galE_sigmaOf (g : D.R.GG) :
    D.host.galE (D.host.sigmaOf g) = g := D.host.gal.apply_symm_apply g

theorem sigmaOf_galE (σ : D.host.E ≃ₐ[ℚ] D.host.E) :
    D.host.sigmaOf (D.host.galE σ) = σ := by
  show (D.host.gal).symm (D.host.gal σ) = σ
  exact MulEquiv.symm_apply_apply _ σ

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

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

def embP (x : D.host.E) : D.what₂.Tau → ℂ := fun τ => embT D τ x

theorem sum_emb_zero {ι : Type*} [Fintype ι] (b : ι → D.host.E) (g : ι → ℝ)
    (h : ∀ τ, ∑ i, (g i : ℂ) * embT D τ (b i) = 0) (φ : D.host.E →+* ℂ) :
    ∑ i, (g i : ℂ) * φ (b i) = 0 := by
  obtain ⟨τ, hτ | hτ⟩ := emb_cases D φ
  · rw [hτ]; exact h τ
  · rw [hτ]
    have := congrArg (starRingEnd ℂ) (h τ)
    simpa [map_sum, map_mul, Complex.conj_ofReal] using this

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
  have hT := NumberField.Embeddings.finite_of_norm_le D.host.E ℂ r
  refine (hT.preimage (Set.injOn_of_injective RingOfIntegers.coe_injective)).subset ?_
  intro x hx
  refine ⟨x.isIntegral_coe, fun φ => ?_⟩
  obtain ⟨τ, hτ | hτ⟩ := emb_cases D φ
  · rw [hτ]; exact hx τ
  · rw [hτ, RingHom.comp_apply, Complex.norm_conj]; exact hx τ

theorem finite_mat (N N' : ℕ) (r : ℝ) :
    {A : Fin N' → Fin N → 𝓞 D.host.E | ∀ τ i j, ‖embT D τ (A i j : D.host.E)‖ ≤ r}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin N' => Set.pi Set.univ (fun _ : Fin N => _))
    (fun _ => Set.Finite.pi (fun _ => finite_ball D r))).subset ?_
  intro A hA
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  exact fun i j τ => hA τ i j

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

theorem isIntegral_iff_mem (x : D.host.E) :
    x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨y, rfl⟩; exact y.isIntegral_coe
  · intro h; exact ⟨⟨x, h⟩, rfl⟩

theorem natMul_of (b : 𝓞 D.host.E) (hb : b ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ t : 𝓞 D.host.E, (n : 𝓞 D.host.E) = t * b := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
    exact ⟨t, ht.symm⟩

theorem exists_int_mul (T : Finset D.host.E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ T, IsIntegral ℤ ((m : D.host.E) * x) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (𝓞 D.host.E)) T
  obtain ⟨n, hn, t, ht⟩ := natMul_of D (b : 𝓞 D.host.E) (nonZeroDivisors.ne_zero b.2)
  refine ⟨n, by exact_mod_cast hn, fun x hx => ?_⟩
  obtain ⟨r, hr⟩ := hb x hx
  have : ((n : ℤ) : D.host.E) * x = ((t * r : 𝓞 D.host.E) : D.host.E) := by
    rw [Algebra.smul_def] at hr
    have h1 : ((n : ℤ) : D.host.E) = (t : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E) := by
      have := congrArg (fun y : 𝓞 D.host.E => (y : D.host.E)) ht
      simpa using this
    rw [h1, mul_assoc]
    push_cast
    exact congrArg ((t : D.host.E) * ·) hr.symm
  rw [this]; exact RingOfIntegers.isIntegral_coe _

theorem sd_bounds {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    ∃ m : ℤ, m ≠ 0 ∧ (∀ x ∈ L, ∀ i, IsIntegral ℤ ((m : D.host.E) * x i)) ∧
      (∀ z : Fin N → D.host.E, (∀ i, IsIntegral ℤ (z i)) → (fun i => (m : D.host.E) * z i) ∈ L) := by
  classical
  letI := D.host.cmStar
  obtain ⟨hfg, -, hsd⟩ := hL
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨m, hm, hmT⟩ := exists_int_mul D (s.biUnion (fun v => Finset.univ.image v))
  have hup : ∀ x ∈ L, ∀ i, IsIntegral ℤ ((m : D.host.E) * x i) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      intro i
      exact hmT _ (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    | zero => intro i; simpa using isIntegral_zero
    | add x y _ _ h1 h2 => intro i; simpa [mul_add] using (h1 i).add (h2 i)
    | smul c x _ h1 =>
      intro i
      have : (m : D.host.E) * (c • x) i = (c : D.host.E) * ((m : D.host.E) * x i) := by
        rw [Pi.smul_apply, Algebra.smul_def,
          show (algebraMap (𝓞 D.host.E) D.host.E) c = (c : D.host.E) from rfl]
        ring
      rw [this]
      exact c.isIntegral_coe.mul (h1 i)
  refine ⟨m, hm, hup, fun z hz => ?_⟩
  rw [hsd]
  intro x hx
  rw [isIntegral_iff_mem]
  unfold stdH
  have hstar : ∀ y : D.host.E, IsIntegral ℤ y → IsIntegral ℤ (star y) := fun y hy =>
    hy.map (starRingEnd D.host.E).toIntAlgHom
  refine IsIntegral.sum _ fun i _ => ?_
  have : star (x i) * ((m : D.host.E) * z i) = star ((m : D.host.E) * x i) * z i := by
    rw [star_mul, star_intCast]; ring
  rw [this]
  exact (hstar _ (hup x hx i)).mul (hz i)

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
  obtain ⟨b, hbS, hb⟩ := D.host.AA0.isFractional
  obtain ⟨n, hn, t, ht⟩ := natMul_of D b (nonZeroDivisors.ne_zero hbS)
  refine ⟨n, by exact_mod_cast hn, fun a ha => ?_⟩
  obtain ⟨r, hr⟩ := hb a ha
  rw [Algebra.smul_def] at hr
  have h1 : ((n : ℤ) : D.host.E) = (t : D.host.E) * (b : D.host.E) := by
    have := congrArg (fun y : 𝓞 D.host.E => (y : D.host.E)) ht
    simpa using this
  rw [h1, mul_assoc, show (b : D.host.E) * a = (r : D.host.E) from hr.symm]
  exact (t * r).isIntegral_coe

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits MeasureTheory
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

theorem hom_upper {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L') :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ A ∈ homL D L L', ∀ i j, IsIntegral ℤ ((M : D.host.E) * A i j) := by
  classical
  obtain ⟨m, hm, -, hlow⟩ := sd_bounds D L hL
  obtain ⟨m', hm', hup', -⟩ := sd_bounds D L' hL'
  refine ⟨m' * m, mul_ne_zero hm' hm, fun A hA => ?_⟩
  induction hA using Submodule.span_induction with
  | mem A hA =>
    intro i j
    let v : Fin N → D.host.E := Pi.single j 1
    have hx := hlow v (fun k => by
      by_cases h : k = j
      · subst h; simpa [v] using isIntegral_one
      · simpa [v, Pi.single_apply, h] using isIntegral_zero)
    have h2 := hup' _ (hA _ hx) i
    have e : A.mulVec (fun k => (m : D.host.E) * v k) i = A i j * m := by
      simp [v, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [e] at h2
    convert h2 using 1
    push_cast; ring
  | zero => intro i j; simpa using isIntegral_zero
  | add A B _ _ h1 h2 => intro i j; simpa [mul_add] using (h1 i j).add (h2 i j)
  | smul c A _ h1 =>
    intro i j
    have : ((m' * m : ℤ) : D.host.E) * (c • A) i j = (c : D.host.E) * (((m' * m : ℤ) : D.host.E) * A i j) := by
      rw [Matrix.smul_apply, Algebra.smul_def,
        show (algebraMap (𝓞 D.host.E) D.host.E) c = (c : D.host.E) from rfl]
      ring
    rw [this]
    exact c.isIntegral_coe.mul (h1 i j)

theorem hom_lower {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L') :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, IsIntegral ℤ (A i j)) →
      ((M : D.host.E) • A) ∈ homL D L L' := by
  obtain ⟨m, hm, hupL, -⟩ := sd_bounds D L hL
  obtain ⟨m', hm', -, hlowL'⟩ := sd_bounds D L' hL'
  refine ⟨m * m', mul_ne_zero hm hm', fun A hA => Submodule.subset_span ?_⟩
  intro x hx
  have hz : ∀ i, IsIntegral ℤ (∑ k, A i k * ((m : D.host.E) * x k)) := fun i =>
    IsIntegral.sum _ fun k _ => (hA i k).mul (hupL x hx k)
  have h2 := hlowL' _ hz
  convert h2 using 1
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

theorem YY_upper {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L') :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ B ∈ YYl D L L', ∀ i j, IsIntegral ℤ ((M : D.host.E) * B i j) := by
  obtain ⟨k, hk, hkA⟩ := exists_int_clearing_order_denominators D
  obtain ⟨M1, hM1, hhom⟩ := hom_upper D L L' hL hL'
  refine ⟨k * M1, mul_ne_zero hk hM1, fun B hB => ?_⟩
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    intro i j
    have : ((k * M1 : ℤ) : D.host.E) * (a • A) i j = ((k : D.host.E) * a) * ((M1 : D.host.E) * A i j) := by
      rw [Matrix.smul_apply, smul_eq_mul]; push_cast; ring
    rw [this]
    exact (hkA a ha).mul (hhom A hA i j)
  | zero => intro i j; simpa using isIntegral_zero
  | add A B _ _ h1 h2 => intro i j; simpa [mul_add] using (h1 i j).add (h2 i j)
  | smul c A _ h1 =>
    intro i j
    have : ((k * M1 : ℤ) : D.host.E) * (c • A) i j = (c : D.host.E) * (((k * M1 : ℤ) : D.host.E) * A i j) := by
      rw [Matrix.smul_apply, Algebra.smul_def,
        show (algebraMap (𝓞 D.host.E) D.host.E) c = (c : D.host.E) from rfl]
      ring
    rw [this]
    exact c.isIntegral_coe.mul (h1 i j)

theorem YY_lower {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L') :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, IsIntegral ℤ (A i j)) →
      ((M : D.host.E) • A) ∈ YYl D L L' := by
  obtain ⟨M, hM, h⟩ := hom_lower D L L' hL hL'
  exact ⟨M, hM, fun A hA => Submodule.subset_span ⟨1, one_mem_inverse_halfDifferent D, _, h A hA, (one_smul _ _).symm⟩⟩

theorem intK (c : 𝓞 D.host.K) : IsIntegral ℤ (((c : D.host.K) : D.host.E)) :=
  c.isIntegral_coe.map (D.host.K.val : D.host.K →+* D.host.E).toIntAlgHom

theorem lam_mem (cc : Ideal (𝓞 D.host.K)) (δ w : ℂ) (hw : w ∈ lamOf D cc δ) :
    ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  induction hw using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, cc.zero_mem, by simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨c1, hc1, rfl⟩ := h1
    obtain ⟨c2, hc2, rfl⟩ := h2
    exact ⟨c1 + c2, cc.add_mem hc1 hc2, by simp [mul_add]⟩
  | neg x _ h1 =>
    obtain ⟨c1, hc1, rfl⟩ := h1
    exact ⟨-c1, cc.neg_mem hc1, by simp⟩

def Phi {N N' : ℕ} (u : ℂ) : (Fin N' → Fin N → 𝓞 D.host.E) →+ VC D N N' where
  toFun A := fun τ i j => u * embT D τ (A i j : D.host.E)
  map_zero' := by funext τ i j; simp
  map_add' A B := by funext τ i j; simp [mul_add]

theorem La_upper {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∃ M : ℤ, M ≠ 0 ∧ La D (tor0 D cc δ) L L' ≤ (Phi D (N := N) (N' := N') (δ / M)).range := by
  obtain ⟨M, hM, hY⟩ := YY_upper D L L' hA.2.2.1 hA.2.2.2
  refine ⟨M, hM, (AddSubgroup.closure_le _).mpr ?_⟩
  rintro z ⟨w, hw, A, hAY, rfl⟩
  obtain ⟨c, hc, rfl⟩ := lam_mem D cc δ w hw
  refine ⟨fun i j => ⟨(M : D.host.E) * ((c : D.host.K) : D.host.E) * A i j, ?_⟩, ?_⟩
  · have := (intK D c).mul (hY A hAY i j)
    have h2 : IsIntegral ℤ ((M : D.host.E) * ((c : D.host.K) : D.host.E) * A i j) := by
      rw [mul_comm (M : D.host.E), mul_assoc]; exact this
    exact h2
  · have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
    funext τ i j
    simp only [Phi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul, embV, tor0]
    change δ / (M : ℂ) * embT D τ ((M : D.host.E) * ((c : D.host.K) : D.host.E) * A i j) =
      δ * D.host.φ₀ ((c : D.host.K) : D.host.E) * embT D τ (A i j)
    rw [map_mul, map_mul, map_intCast, embT_K D τ _ (c : D.host.K).2]
    field_simp

theorem disc_of_finite {V : Type*} [NormedAddCommGroup V] (S : AddSubgroup V)
    (h : ∀ r : ℝ, {x | x ∈ S ∧ ‖x‖ ≤ r}.Finite) : DiscreteTopology S := by
  set F := {x | x ∈ S ∧ ‖x‖ ≤ 1} \ {0}
  have hF : F.Finite := (h 1).subset Set.sdiff_subset
  have h0 : (0 : V) ∉ F := fun h => h.2 rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF.isClosed.isOpen_compl 0 h0
  apply discreteTopology_of_isOpen_singleton_zero
  rw [isOpen_induced_iff]
  refine ⟨Metric.ball 0 (min ε 1), Metric.isOpen_ball, ?_⟩
  ext ⟨x, hx⟩
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
  constructor
  · intro hxb
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hxF : x ∈ F := ⟨⟨hx, le_of_lt (lt_of_lt_of_le hxb (min_le_right _ _))⟩, hne'⟩
    exact hball (by simpa using lt_of_lt_of_le hxb (min_le_left _ _)) hxF
  · intro h
    have : x = 0 := congrArg Subtype.val h
    subst this
    simp [hε]

theorem La_finite {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hδ : δ ≠ 0) (r : ℝ) :
    {x | x ∈ La D (tor0 D cc δ) L L' ∧ ‖x‖ ≤ r}.Finite := by
  obtain ⟨M, hM, hle⟩ := La_upper D L L' hA cc δ
  set u : ℂ := δ / M
  have hu : u ≠ 0 := div_ne_zero hδ (by exact_mod_cast hM)
  refine ((finite_mat D N N' (r / ‖u‖)).image (Phi D u)).subset ?_
  rintro x ⟨hx, hxr⟩
  obtain ⟨A, rfl⟩ := hle hx
  refine ⟨A, fun τ i j => ?_, rfl⟩
  have h1 : ‖(Phi D u A) τ i j‖ ≤ r :=
    le_trans (norm_le_pi_norm _ j) (le_trans (norm_le_pi_norm _ i)
      (le_trans (norm_le_pi_norm _ τ) hxr))
  rw [le_div_iff₀ (norm_pos_iff.mpr hu)]
  simpa [Phi, norm_mul, mul_comm] using h1

def ins {N N' : ℕ} (i0 : Fin N') (j0 : Fin N) (w : D.what₂.Tau → ℂ) : VC D N N' :=
  fun τ i j => if i = i0 ∧ j = j0 then w τ else 0

theorem La_lower {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ (i0 : Fin N') (j0 : Fin N) (b : 𝓞 D.host.E),
      ins D i0 j0 (fun τ => δ * n * embT D τ (b : D.host.E)) ∈ La D (tor0 D cc δ) L L' := by
  classical
  obtain ⟨M1, hM1, hY⟩ := YY_lower D L L' hA.2.2.1 hA.2.2.2
  obtain ⟨c0, hc0, hc0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc.1
  have hcE : ((c0 : D.host.K) : D.host.E) ≠ 0 := by
    intro h
    apply hc0ne
    have h1 : (c0 : D.host.K) = 0 := by exact_mod_cast h
    exact_mod_cast h1
  let b0 : 𝓞 D.host.E := ⟨((c0 : D.host.K) : D.host.E) * M1, (intK D c0).mul isIntegral_algebraMap⟩
  have hb0 : b0 ≠ 0 := by
    intro h
    have : ((c0 : D.host.K) : D.host.E) * M1 = 0 := congrArg (fun y : 𝓞 D.host.E => (y : D.host.E)) h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hcE h1
    · exact hM1 (by exact_mod_cast h1)
  obtain ⟨n, hn, t, ht⟩ := natMul_of D b0 hb0
  have hnE : (n : D.host.E) = (t : D.host.E) * (((c0 : D.host.K) : D.host.E) * M1) := by
    rw [show (n : D.host.E) = ((n : 𝓞 D.host.E) : D.host.E) by norm_cast, ht]
    rfl
  refine ⟨n, hn, fun i0 j0 b => ?_⟩
  let A' : Matrix (Fin N') (Fin N) D.host.E := fun i j => if i = i0 ∧ j = j0 then (t : D.host.E) * b else 0
  have hA' : ∀ i j, IsIntegral ℤ (A' i j) := by
    intro i j
    by_cases h : i = i0 ∧ j = j0
    · simp only [A', if_pos h]; exact (t * b).isIntegral_coe
    · simp only [A', if_neg h]; exact isIntegral_zero
  have hmem : (fun i j => if i = i0 ∧ j = j0 then (M1 : D.host.E) * ((t : D.host.E) * b) else 0 :
      Matrix (Fin N') (Fin N) D.host.E) ∈ YYl D L L' := by
    have e : (fun i j => if i = i0 ∧ j = j0 then (M1 : D.host.E) * ((t : D.host.E) * b) else 0 :
        Matrix (Fin N') (Fin N) D.host.E) = (M1 : D.host.E) • A' := by
      funext i j
      show _ = (M1 : D.host.E) * A' i j
      simp only [A']
      split_ifs <;> simp
    rw [e]; exact hY A' hA'
  apply AddSubgroup.subset_closure
  refine ⟨δ * D.host.φ₀ ((c0 : D.host.K) : D.host.E), AddSubgroup.subset_closure ⟨c0, hc0, rfl⟩,
    _, hmem, ?_⟩
  funext τ i j
  simp only [ins, Pi.smul_apply, smul_eq_mul, embV, tor0]
  split_ifs with h
  · rw [← embT_K D τ _ (c0 : D.host.K).2, mul_assoc, mul_assoc]
    congr 1
    rw [← map_natCast (embT D τ) n, ← map_mul, ← map_mul, hnE]
    congr 1
    ring
  · simp

theorem span_La {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) (hδ : δ ≠ 0) :
    Submodule.span ℝ (La D (tor0 D cc δ) L L' : Set (VC D N N')) = ⊤ := by
  classical
  obtain ⟨n, hn, hlow⟩ := La_lower D L L' hA cc hcc δ
  set u : ℂ := δ * n
  have hu : u ≠ 0 := mul_ne_zero hδ (by exact_mod_cast hn)
  have key : ∀ i0 j0 (w : D.what₂.Tau → ℂ),
      ins D i0 j0 w ∈ Submodule.span ℝ (La D (tor0 D cc δ) L L' : Set (VC D N N')) := by
    intro i0 j0 w
    have hw : (u⁻¹ • w) ∈ Submodule.span ℝ
        (Set.range (fun b : 𝓞 D.host.E => embP D (b : D.host.E))) := by
      rw [span_embP]; trivial
    have hP : ∀ v ∈ Submodule.span ℝ (Set.range (fun b : 𝓞 D.host.E => embP D (b : D.host.E))),
        ins D i0 j0 (u • v) ∈ Submodule.span ℝ (La D (tor0 D cc δ) L L' : Set (VC D N N')) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨b, rfl⟩ := hv
        apply Submodule.subset_span
        have e : ins D i0 j0 (u • embP D (b : D.host.E)) =
            ins D i0 j0 (fun τ => u * embT D τ (b : D.host.E)) := by
          funext τ i j; simp [ins, embP]
        show ins D i0 j0 (u • embP D (b : D.host.E)) ∈ La D (tor0 D cc δ) L L'
        rw [e]; exact hlow i0 j0 b
      | zero =>
        convert Submodule.zero_mem _ using 1
        funext τ i j; simp [ins]
      | add x y _ _ h1 h2 =>
        convert Submodule.add_mem _ h1 h2 using 1
        funext τ i j; simp only [ins, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        split_ifs <;> simp [mul_add]
      | smul r x _ h1 =>
        convert Submodule.smul_mem _ r h1 using 1
        funext τ i j; simp only [ins, Pi.smul_apply, smul_eq_mul]
        split_ifs <;> simp [Complex.real_smul] <;> ring
    convert hP _ hw using 1
    funext τ i j
    simp only [ins, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    · rfl
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ i0, ∑ j0, ins D i0 j0 (fun τ => x τ i0 j0) := by
    funext τ i j
    simp [ins, Finset.sum_apply, ite_and]
  rw [hx]
  exact Submodule.sum_mem _ fun i0 _ => Submodule.sum_mem _ fun j0 _ => key i0 j0 _

theorem fullLat {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) (hδ : δ ≠ 0) :
    FullLat (La D (tor0 D cc δ) L L') :=
  ⟨disc_of_finite _ (La_finite D L L' hA cc δ hδ), span_La D L L' hA cc hcc δ hδ⟩

theorem La_zero {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (cc : Ideal (𝓞 D.host.K)) :
    La D (tor0 D cc 0) L L' = ⊥ := by
  rw [eq_bot_iff]
  unfold La
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

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions MeasureTheory
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

theorem theta_unitary_linkage : LinkThU := by
  intro D cc hcc δ hδ N N' L L' hA G hG x
  by_cases h0 : δ = 0
  · subst h0
    have hb := FL.La_zero D L L' cc
    haveI : Countable (La D (tor0 D cc 0) L L') := by
      rw [hb]
      exact ⟨⟨fun _ => 0, fun a b _ => Subtype.ext ((AddSubgroup.mem_bot.mp a.2).trans
        (AddSubgroup.mem_bot.mp b.2).symm)⟩⟩
    refine normSq_U_of_fd _ _ ?_ G hG x
    rw [hb]
    exact ⟨Set.univ, FL.fd_bot _⟩
  · exact normSq_U_of_full _ _ (FL.fullLat D L L' hA cc hcc δ h0) G hG x

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
