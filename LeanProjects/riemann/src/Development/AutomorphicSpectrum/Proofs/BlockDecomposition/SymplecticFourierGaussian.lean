import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMixedToEuclideanConjSqRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeAbsNormUnitsPrimeIdealUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFourierCosetIndValBall

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 vecAt awayIntegral awayBox)
open GroundTheory.Automorphic.GJMatrix (cosetInd localTensor localFourierPi localMeasurePi)
open Ad3 Ad3.R GlobalTheory.CompanionTheory.RSFT
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap nonZeroDivisors Classical

namespace GlobalTheory.CompanionTheory.RSFT.Assemble

theorem restrictedTensor2_tensor (S : Finset Pl) (g : Fin 2 → ∀ v : S, Qv v.1 → ℂ) :
    restrictedTensor2 S (fun v => localTensor fun i => g i v) =
      Adele2.finiteTensor2 fun i => oneDim S (g i) := by
  funext x
  by_cases hx : x ∈ awayBox S
  · have hi : ∀ i, x i ∈ (awayIntegral S : Set Af) := hx
    rw [restrictedTensor2, Set.indicator_of_mem hx, Adele2.finiteTensor2]
    simp only [oneDim, Set.indicator_of_mem (hi _), localTensor]
    exact Finset.prod_comm
  · have : ∃ i, x i ∉ (awayIntegral S : Set Af) := by
      by_contra h
      push Not at h
      exact hx h
    obtain ⟨i, hi⟩ := this
    rw [restrictedTensor2, Set.indicator_of_notMem hx, Adele2.finiteTensor2]
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    rw [oneDim, Set.indicator_of_notMem hi]

theorem restrictedTensor2_sum (S : Finset Pl) {κ : S → Type} (s : ∀ v, Finset (κ v)) (c : ∀ v, κ v → ℂ)
    (E : ∀ v : S, κ v → (Fin 2 → Qv v.1) → ℂ) :
    restrictedTensor2 S (fun v => ∑ a ∈ s v, c v a • E v a) =
      ∑ p ∈ Fintype.piFinset s, (∏ v, c v (p v)) • restrictedTensor2 S (fun v => E v (p v)) := by
  funext x
  rw [Finset.sum_apply]
  by_cases hx : x ∈ awayBox S
  · simp only [restrictedTensor2, Set.indicator_of_mem hx, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [Finset.prod_univ_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.prod_mul_distrib
  · simp [restrictedTensor2, Set.indicator_of_notMem hx]

theorem count_idl (S : Finset Pl) (N : S → ℤ) (w : Pl) :
    FractionalIdeal.count ℚ w (idl S N : FractionalIdeal (𝓞 ℚ)⁰ ℚ) = if h : w ∈ S then N ⟨w, h⟩ else 0 := by
  refine count_finprod_primeIdealUnit_zpow _ ?_ w
  rw [Filter.eventually_cofinite]
  refine S.finite_toSet.subset fun u hu => ?_
  by_contra huS
  exact hu (dif_neg fun h => huS (Finset.mem_coe.2 h))

theorem sup_apply (S : Finset Pl) (a : ∀ v : S, Qv v.1) (v : S) : (sup S a) v.1 = a v := by
  have : (sup S a) v.1 = ∑ u : S, (finiteAdeleSingleAdd u.1 (a u)) v.1 := by
    rw [sup]
    exact map_sum (adeleAt v.1) _ _
  rw [this, Finset.sum_eq_single v, finiteAdeleSingleAdd_apply_self]
  · intro u _ hu
    exact finiteAdeleSingleAdd_apply_of_ne (fun h => hu (Subtype.ext h.symm)) _
  · simp

theorem sup_apply_notMem (S : Finset Pl) (a : ∀ v : S, Qv v.1) {w : Pl} (hw : w ∉ S) : (sup S a) w = 0 := by
  have : (sup S a) w = ∑ u : S, (finiteAdeleSingleAdd u.1 (a u)) w := by
    rw [sup]
    exact map_sum (adeleAt w) _ _
  rw [this]
  refine Finset.sum_eq_zero fun u _ => finiteAdeleSingleAdd_apply_of_ne (fun h => hw (by rw [h]; exact u.2)) _

theorem char_sup (S : Finset Pl) (a : ∀ v : S, Qv v.1) (y : Af) :
    finiteAdelicChar ℚ (sup S a * y) = ∏ v : S, localAdelicChar ℚ v.1 (a v * y v.1) := by
  rw [sup, Finset.sum_mul, addChar_map_finsetSum]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [finiteAdeleSingleAdd_mul, finiteAdelicChar_finiteAdeleSingleAdd]

end GlobalTheory.CompanionTheory.RSFT.Assemble

namespace GlobalTheory.CompanionTheory.RSFT.Assemble

theorem mem_int {w : Pl} {z : Qv w} : z ∈ w.adicCompletionIntegers ℚ ↔ Valued.v z ≤ 1 :=
  HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem count_different (w : Pl) :
    FractionalIdeal.count ℚ w ((differentIdeal ℤ (𝓞 ℚ) : Ideal (𝓞 ℚ)) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) = 0 := by
  have h1 : Ideal.absNorm (differentIdeal ℤ (𝓞 ℚ)) = 1 := by
    rw [absNorm_differentIdeal ℚ (𝓞 ℚ), Rat.numberField_discr]
    rfl
  rw [Ideal.absNorm_eq_one_iff.1 h1, FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one]

theorem mem_coset_iff (S : Finset Pl) (N : S → ℤ) (a : ∀ v : S, Qv v.1) (x : Af) :
    x - sup S a ∈ idealFiniteAdeles (idl S N) ↔
      x ∈ (awayIntegral S : Set Af) ∧ ∀ v : S, x v.1 - a v ∈ valBall (Qv v.1) (N v) := by
  rw [mem_idealFiniteAdeles]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · have := h w
      rw [count_idl, dif_neg hw] at this
      have e : (x - sup S a) w = x w := by
        have : (x - sup S a) w = x w - (sup S a) w := rfl
        rw [this, sup_apply_notMem S a hw, sub_zero]
      rw [e] at this
      exact mem_int.2 (by simpa using this)
    · have := h v.1
      rw [count_idl, dif_pos v.2] at this
      have e : (x - sup S a) v.1 = x v.1 - a v := by
        have : (x - sup S a) v.1 = x v.1 - (sup S a) v.1 := rfl
        rw [this, sup_apply]
      rw [e] at this
      exact mem_valBall_iff_valued.2 this
  · rintro ⟨h1, h2⟩ w
    rw [count_idl]
    by_cases hw : w ∈ S
    · rw [dif_pos hw]
      have e : (x - sup S a) w = x w - a ⟨w, hw⟩ := by
        have : (x - sup S a) w = x w - (sup S a) w := rfl
        rw [this, sup_apply S a ⟨w, hw⟩]
      rw [e]
      exact mem_valBall_iff_valued.1 (h2 ⟨w, hw⟩)
    · rw [dif_neg hw]
      have e : (x - sup S a) w = x w := by
        have : (x - sup S a) w = x w - (sup S a) w := rfl
        rw [this, sup_apply_notMem S a hw, sub_zero]
      rw [e]
      simpa using mem_int.1 (h1 w hw)

theorem mem_dual_iff (S : Finset Pl) (N : S → ℤ) (y : Af) :
    y ∈ idealFiniteAdeles (traceDualIdeal ℚ (idl S N)) ↔
      y ∈ (awayIntegral S : Set Af) ∧ ∀ v : S, y v.1 ∈ valBall (Qv v.1) (-N v) := by
  rw [mem_idealFiniteAdeles]
  simp only [count_traceDualIdeal, count_different, count_idl, add_zero, neg_neg]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · have := h w
      rw [dif_neg hw] at this
      exact mem_int.2 (by simpa using this)
    · have := h v.1
      rw [dif_pos v.2] at this
      exact mem_valBall_iff_valued.2 (by simpa using this)
  · rintro ⟨h1, h2⟩ w
    by_cases hw : w ∈ S
    · rw [dif_pos hw]
      simpa using mem_valBall_iff_valued.1 (h2 ⟨w, hw⟩)
    · rw [dif_neg hw]
      simpa using mem_int.1 (h1 w hw)

theorem oneDim_coset (S : Finset Pl) (N : S → ℤ) (a : ∀ v : S, Qv v.1) :
    (oneDim S fun v => cosetInd (valBall (Qv v.1) (N v)) (a v)) = cosetIndicator (idl S N) (sup S a) := by
  funext x
  rw [cosetIndicator_apply]
  simp only [mem_coset_iff]
  by_cases hx : x ∈ (awayIntegral S : Set Af)
  · rw [oneDim, Set.indicator_of_mem hx]
    simp only [GroundTheory.Automorphic.GJMatrix.cosetInd_apply, hx, true_and]
    rw [Finset.prod_ite_zero]
    simp
  · rw [oneDim, Set.indicator_of_notMem hx]
    simp [hx]

theorem oneDim_fourier (hB : B0) (S : Finset Pl) (N : S → ℤ) (a : ∀ v : S, Qv v.1) :
    finiteFourier ℚ (oneDim S fun v => cosetInd (valBall (Qv v.1) (N v)) (a v)) =
      oneDim S fun v => localFourier (selfDualMeasure (localAdelicChar ℚ v.1)) (localAdelicChar ℚ v.1)
        (cosetInd (valBall (Qv v.1) (N v)) (a v)) := by
  funext y
  have hl : ∀ v : S, localFourier (selfDualMeasure (localAdelicChar ℚ v.1)) (localAdelicChar ℚ v.1)
      (cosetInd (valBall (Qv v.1) (N v)) (a v)) (y v.1) =
        (localAdelicChar ℚ v.1 (a v * y v.1) : ℂ) * (((pOf v.1 : ℝ) ^ (-N v) : ℝ) : ℂ) *
          (valBall (Qv v.1) (-N v) : Set (Qv v.1)).indicator (fun _ => (1 : ℂ)) (y v.1) := by
    intro v
    have := GlobalTheory.CompanionTheory.RSFT.localFourier_cosetInd_valBall (Qv v.1) (localAdelicChar ℚ v.1) (hB.1 v.1).1 (N v) (a v) (y v.1)
    rwa [(hB.1 v.1).2.1] at this
  rw [oneDim_coset, finiteFourier_cosetIndicator, GlobalTheory.CompanionTheory.RSFT.finiteAdeleMeasure_idl_toReal, char_sup]
  by_cases hy : y ∈ idealFiniteAdeles (traceDualIdeal ℚ (idl S N))
  · obtain ⟨h1, h2⟩ := (mem_dual_iff S N y).1 hy
    rw [Set.indicator_of_mem (SetLike.mem_coe.2 hy), oneDim, Set.indicator_of_mem h1]
    have hcp : ((∏ v : S, localAdelicChar ℚ v.1 (a v * y v.1) : Circle) : ℂ) =
        ∏ v : S, (localAdelicChar ℚ v.1 (a v * y v.1) : ℂ) := map_prod Circle.coeHom _ _
    simp only [hl, Set.indicator_of_mem (SetLike.mem_coe.2 (h2 _)), mul_one, Pi.one_apply,
      Finset.prod_mul_distrib, hcp]
    push_cast
    ring
  · rw [Set.indicator_of_notMem (by simpa using hy), mul_zero, mul_zero]
    by_cases h1 : y ∈ (awayIntegral S : Set Af)
    · have : ∃ v : S, y v.1 ∉ valBall (Qv v.1) (-N v) := by
        by_contra h
        push Not at h
        exact hy ((mem_dual_iff S N y).2 ⟨h1, h⟩)
      obtain ⟨v, hv⟩ := this
      rw [oneDim, Set.indicator_of_mem h1]
      refine (Finset.prod_eq_zero (Finset.mem_univ v) ?_).symm
      rw [hl, Set.indicator_of_notMem (by simpa using hv), mul_zero]
    · rw [oneDim, Set.indicator_of_notMem h1]

end GlobalTheory.CompanionTheory.RSFT.Assemble

namespace GlobalTheory.CompanionTheory.RSFT.Assemble

theorem gauss_step (γ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) (hγ : IsGauss γ) (r : Fin 2 → 𝔸[ℚ]) :
    Adele2.mixedFourier2 ℚ γ (Adele2.infPart ![r 1, -r 0]) = γ (Adele2.infPart r) :=
  GlobalTheory.CompanionTheory.RSFT.GaussPlane.mixedFourier2_gauss_rot γ hγ r

theorem base_step (hB : B0) (S : Finset Pl) (N : S → ℤ) (p : ∀ v : S, Fin 2 → Qv v.1) :
    Adele2.finiteFourier2 ℚ (restrictedTensor2 S fun v => cE (N v) (p v)) =
      restrictedTensor2 S fun v => localFourierPi (localAdelicChar ℚ v.1) (cE (N v) (p v)) := by
  have h1 := restrictedTensor2_tensor S (fun i v => cosetInd (valBall (Qv v.1) (N v)) (p v i))
  have h2 := restrictedTensor2_tensor S (fun i v => localFourier (selfDualMeasure (localAdelicChar ℚ v.1))
    (localAdelicChar ℚ v.1) (cosetInd (valBall (Qv v.1) (N v)) (p v i)))
  simp only [cE, GroundTheory.Automorphic.GJMatrix.localFourierPi_localTensor]
  rw [h1, h2, Adele2.finiteFourier2_finiteTensor2]
  simp only [oneDim_fourier hB]

theorem exists_decomp {v : Pl} {Φ : (Fin 2 → Qv v) → ℂ} (hΦ : SB Φ) :
    ∃ (N : ℤ) (s : Finset (Fin 2 → Qv v)), Φ = ∑ a ∈ s, Φ a • cE N a := by
  have hopen : ∀ H ∈ Set.range (valBall (Qv v)), IsOpen (H : Set (Qv v)) := by
    rintro _ ⟨N, rfl⟩
    exact isOpen_valBall N
  have hbasis : ∀ W ∈ 𝓝 (0 : Qv v), ∃ H ∈ Set.range (valBall (Qv v)), (H : Set (Qv v)) ⊆ W := by
    intro W hW
    obtain ⟨N, -, hN⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp hW
    exact ⟨_, ⟨N, rfl⟩, hN⟩
  obtain ⟨_, ⟨N, rfl⟩, s, hs⟩ := GroundTheory.Automorphic.GJMatrix.exists_eq_sum_prod_cosetInd hopen hbasis hΦ.1 hΦ.2
  exact ⟨N, s, hs⟩

theorem localFourierPi_sum {v : Pl} (hc : Continuous (localAdelicChar ℚ v)) (N : ℤ) (s : Finset (Fin 2 → Qv v)) (c : (Fin 2 → Qv v) → ℂ) :
    localFourierPi (localAdelicChar ℚ v) (∑ a ∈ s, c a • cE N a) =
      ∑ a ∈ s, c a • localFourierPi (localAdelicChar ℚ v) (cE N a) := by
  funext y
  have hi : ∀ a, Integrable (fun x => cE N a x * ((localAdelicChar ℚ v) (∑ i, x i * y i) : ℂ))
      (localMeasurePi (localAdelicChar ℚ v)) := fun a =>
    GroundTheory.Automorphic.GJMatrix.integrable_mul_char_sum hc
      (GroundTheory.Automorphic.GJMatrix.integrable_of_mem_localSchwartzBruhatPi
        (GroundTheory.Automorphic.GJMatrix.localTensor_mem fun i =>
          GroundTheory.Automorphic.GJMatrix.cosetInd_valBall_mem N (a i))) y
  simp only [localFourierPi, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [integral_finset_sum _ fun a _ => (hi a).const_mul (c a)]
  exact Finset.sum_congr rfl fun a _ => integral_const_mul _ _

theorem finiteFourier2_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → (Fin 2 → Af) → ℂ)
    (hf : ∀ i, f i ∈ Adele2.finiteSchwartzBruhat2 ℚ) :
    Adele2.finiteFourier2 ℚ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • Adele2.finiteFourier2 ℚ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [Adele2.finiteFourier2_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Adele2.finiteFourier2_add
      (Adele2.integrable_of_mem_finiteSchwartzBruhat2 (Submodule.smul_mem _ _ (hf a)))
      (Adele2.integrable_of_mem_finiteSchwartzBruhat2 (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hf i))),
      Adele2.finiteFourier2_smul, ih]

theorem cE_mem {v : Pl} (N : ℤ) (a : Fin 2 → Qv v) : SB (cE N a) := by
  have := GroundTheory.Automorphic.GJMatrix.localTensor_mem (ι := Fin 2) (g := fun i => cosetInd (valBall (Qv v) N) (a i))
    fun i => GroundTheory.Automorphic.GJMatrix.cosetInd_valBall_mem N (a i)
  exact this

theorem finite_step (hB : B0) (S : Finset Pl) (Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ) (hΨ : ∀ v, SB (Ψ v)) :
    Adele2.finiteFourier2 ℚ (restrictedTensor2 S Ψ) =
      restrictedTensor2 S fun v => localFourierPi (localAdelicChar ℚ v.1) (Ψ v) := by
  choose N s hs using fun v => exists_decomp (hΨ v)
  have hc : ∀ v : Pl, Continuous (localAdelicChar ℚ v) := fun v => continuous_localAdelicChar v
  have e1 := restrictedTensor2_sum S s (fun v a => Ψ v a) (fun v a => cE (N v) a)
  have e2 := restrictedTensor2_sum S s (fun v a => Ψ v a)
    (fun v a => localFourierPi (localAdelicChar ℚ v.1) (cE (N v) a))
  have h1 : (fun v => ∑ a ∈ s v, Ψ v a • cE (N v) a) = Ψ := funext fun v => (hs v).symm
  have h2 : (fun v => ∑ a ∈ s v, Ψ v a • localFourierPi (localAdelicChar ℚ v.1) (cE (N v) a)) =
      fun v => localFourierPi (localAdelicChar ℚ v.1) (Ψ v) := by
    funext v
    rw [← localFourierPi_sum (hc v.1), ← hs v]
  rw [h1] at e1
  rw [h2] at e2
  rw [e2, e1, finiteFourier2_sum _ _ _ fun p => GodementSection.restrictedTensor2_mem S fun v => cE_mem _ _]
  exact Finset.sum_congr rfl fun p _ => by rw [base_step hB]

theorem sF_eq {v : Pl} (Φ : (Fin 2 → Qv v) → ℂ) (r : Fin 2 → Qv v) :
    sF (localAdelicChar ℚ v) Φ r = localFourierPi (localAdelicChar ℚ v) Φ ![r 1, -r 0] := by
  simp only [sF, localFourierPi, dt, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, m2, localMeasurePi]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [mul_neg, sub_eq_add_neg]

theorem swap_step (S : Finset Pl) (L Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ)
    (h : ∀ v r, Ψ v r = L v ![r 1, -r 0]) (x : Fin 2 → Af) :
    restrictedTensor2 S L ![x 1, -x 0] = restrictedTensor2 S Ψ x := by
  have hbox : ![x 1, -x 0] ∈ awayBox S ↔ x ∈ awayBox S := by
    simp only [awayBox, Set.mem_setOf_eq, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, neg_mem_iff]
    exact and_comm
  have hv : ∀ v : S, vecAt v.1 ![x 1, -x 0] = ![vecAt v.1 x 1, -vecAt v.1 x 0] := by
    intro v
    funext i
    fin_cases i <;> rfl
  by_cases hx : x ∈ awayBox S
  · rw [restrictedTensor2, restrictedTensor2, Set.indicator_of_mem (hbox.2 hx), Set.indicator_of_mem hx]
    exact Finset.prod_congr rfl fun v _ => by rw [hv, h]
  · rw [restrictedTensor2, restrictedTensor2, Set.indicator_of_notMem (mt hbox.1 hx), Set.indicator_of_notMem hx]

theorem fourier_eq (hB : B0) (γ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) (hγ : IsGauss γ) (S : Finset Pl)
    (Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ) (hΨ : ∀ v, SB (Ψ v)) (r : Fin 2 → 𝔸[ℚ]) :
    sFA (tst γ S Ψ) r = tst γ S (fun v => sF (localAdelicChar ℚ v.1) (Ψ v)) r := by
  have hp : Adele2.finPart ![r 1, -r 0] = ![Adele2.finPart r 1, -Adele2.finPart r 0] := by
    funext i
    fin_cases i <;> rfl
  have hs := swap_step S (fun v => localFourierPi (localAdelicChar ℚ v.1) (Ψ v))
    (fun v => sF (localAdelicChar ℚ v.1) (Ψ v)) (fun v r => sF_eq _ _) (Adele2.finPart r)
  have h1 : sFA (tst γ S Ψ) r = Adele2.mixedFourier2 ℚ γ (Adele2.infPart ![r 1, -r 0]) *
      Adele2.finiteFourier2 ℚ (restrictedTensor2 S Ψ) (Adele2.finPart ![r 1, -r 0]) := by
    rw [sFA, tst, Adele2.adelicFourier2_schwartzBruhatTensor2, Adele2.schwartzBruhatTensor2,
      Adele2.mixedFourier2Schwartz_apply]
  rw [h1, gauss_step γ hγ r, finite_step hB S Ψ hΨ, hp, hs]
  rfl

theorem fourier_gaussian_of_basic_facts : B0 → FT := by
  intro hB γ hγ S Ψ hΨ
  have hm : restrictedTensor2 S Ψ ∈ Adele2.finiteSchwartzBruhat2 ℚ := GodementSection.restrictedTensor2_mem S hΨ
  exact ⟨Adele2.schwartzBruhatTensor2_mem γ hm, funext (fourier_eq hB γ hγ S Ψ hΨ)⟩

end GlobalTheory.CompanionTheory.RSFT.Assemble

end
