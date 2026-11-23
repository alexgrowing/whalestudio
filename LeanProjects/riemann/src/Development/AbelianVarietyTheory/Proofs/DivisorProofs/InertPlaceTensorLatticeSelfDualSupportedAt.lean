import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixAdelicDecompositionAtFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHermitianTensorIntegralOfCharTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPlaceDenominatorUnramifiedTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSelfDualLatticeLocalisedAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisWithDualBasisInHermitianLatticeAwayPlStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def contr (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin d) E) (x : Fin n → E) :
    Fin d → E := fun j => ∑ i, X i j * (J *ᵥ fun m => σ (x m)) i

theorem hTens_eq_form (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (X : Matrix (Fin n) (Fin d) E) (x : Fin n → E) (y : Fin d → E) :
    GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec x y) = form σ JB (contr σ JA X x) y := by
  unfold GlobalTheory.WeilM.hTens form contr
  simp only [Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem hTens_smul_vec (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (X : Matrix (Fin n) (Fin d) E) (c : E) (x : Fin n → E) (y : Fin d → E) :
    GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec (c • x) y) = σ c * GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec x y) := by
  unfold GlobalTheory.WeilM.hTens
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem decomp_sum (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin d) E)
    (p f : Fin n → Fin n → E) (h : ∀ k l, form σ J (p k) (f l) = if k = l then 1 else 0) :
    X = ∑ k, Matrix.vecMulVec (p k) (contr σ J X (f k)) := by
  set P : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => p k i with hP
  set Q : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => (J *ᵥ fun m => σ (f k m)) i with hQ
  have h1 : Pᵀ * Q = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply, ← h k l]
    simp [P, Q, form, dotProduct]
  have h2 : Q * Pᵀ = 1 := mul_eq_one_comm.mp h1
  have h3 : P * Qᵀ = 1 := by
    have := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  ext i j
  have e : X i j = ((P * Qᵀ) * X) i j := by rw [h3, Matrix.one_mul]
  rw [e, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, contr, P, Q, Matrix.of_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem incM_smul {m k : Type} (c : F) (Z : Matrix m k E) : incM F (c • Z) = algebraMap F (AF F) c • incM F Z := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply]
  rw [Algebra.smul_def c, Algebra.smul_def (algebraMap F (AF F) c), map_mul]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes c

theorem inv_mem_O {v : Pl F} {t : 𝓞 F} (ht : t ∉ v.asIdeal) :
    algebraMap F (Fv F v) ((t : F))⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (t : F) = 1 := by
    have := (v.valuation_eq_one_iff_notMem (K := F)).2 ht
    simpa using this
  have h2 := v.valuedAdicCompletion_eq_valuation' ((t : F)⁻¹)
  have h3 : v.valuation F (t : F)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  exact (h2.trans h3).le

theorem sigma_surj (σ : E →ₐ[F] E) (o : 𝓞 E) : ∃ o' : 𝓞 E, σ (o' : E) = o := by
  obtain ⟨e, he⟩ := (AlgHom.bijective σ).2 (o : E)
  have hi : IsIntegral ℤ e := by
    have h : IsIntegral ℤ (σ e) := he ▸ NumberField.RingOfIntegers.isIntegral_coe o
    exact (isIntegral_algHom_iff (σ.restrictScalars ℤ) σ.injective).1 h
  exact ⟨⟨e, hi⟩, he⟩

theorem lemD (σ : E →ₐ[F] E) (B : Base F E) {n d r s r' s' : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s') (v : Pl F)
    (X₀ : Matrix (Fin n) (Fin d) E)
    (hint : ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v)
      (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y))) ∈ v.adicCompletionIntegers F) :
    GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  have hloc : ∀ x ∈ X.L, ∀ y ∈ Y.L, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧
      IsIntegral ℤ (algebraMap F E (t : F) * GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)) := by
    intro x hx y hy
    obtain ⟨t, ht, hti⟩ := GlobalTheory.T.exists_prime_to_place_denominator_unramified_trace F E hun v (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)) (fun o => by
      obtain ⟨o', ho'⟩ := sigma_surj σ o
      have hx' : (o' : E) • x ∈ X.L := X.L.smul_mem o' hx
      have h := hint _ hx' y hy
      rw [hTens_smul_vec, ho'] at h
      rwa [mul_neg])
    refine ⟨t, ht, ?_⟩
    have h := hti.neg
    rwa [mul_neg, neg_neg] at h
  obtain ⟨f, p, hf, hp, hpf⟩ := GlobalTheory.T.exists_basis_with_dual_basis_in_hermitian_lattice_away_place F E σ B X hX v
  have hw : ∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • contr σ X.J X₀ (f k) ∈ Y.L := by
    intro k
    obtain ⟨s0, hs0, hsf⟩ := hf k
    refine GlobalTheory.T.skewSelfDual_lattice_localised_at_place F E σ B Y hY v _ fun y hy => ?_
    obtain ⟨t, ht, hti⟩ := hloc _ hsf y hy
    refine ⟨t * s0, fun h => (v.isPrime.mem_or_mem h).elim ht hs0, ?_⟩
    rw [← hTens_eq_form]
    rw [hTens_smul_vec, AlgHom.commutes] at hti
    convert hti using 1
    rw [show ((t * s0 : 𝓞 F) : F) = (t : F) * (s0 : F) from rfl, map_mul]
    ring
  choose tw htw hwY using hw
  choose tp htp hpX using hp
  have hdec := decomp_sum σ X.J X₀ p f hpf
  rw [hdec]
  have hsum : incM F (∑ k, Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k))) =
      ∑ k, incM F (Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k))) := by
    ext i j
    simp [incM, Matrix.sum_apply, map_sum]
  rw [hsum, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ?_
  have hc0 : (tp k * tw k : 𝓞 F) ∉ v.asIdeal := fun h => (v.isPrime.mem_or_mem h).elim (htp k) (htw k)
  have hne : (tp k * tw k : 𝓞 F) ≠ 0 := fun h => hc0 (h ▸ zero_mem _)
  have hcF : ((tp k * tw k : 𝓞 F) : F) ≠ 0 := by
    intro h0
    exact hne (by exact_mod_cast h0)
  have hcE : algebraMap F E ((tp k * tw k : 𝓞 F) : F) ≠ 0 := (map_ne_zero _).2 hcF
  have hvm : Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k)) = ((tp k * tw k : 𝓞 F) : F)⁻¹ •
      Matrix.vecMulVec (algebraMap F E (tp k : F) • p k) (algebraMap F E (tw k : F) • contr σ X.J X₀ (f k)) := by
    ext i j
    rw [show ((tp k * tw k : 𝓞 F) : F) = (tp k : F) * (tw k : F) from rfl] at hcE ⊢
    rw [map_mul] at hcE
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [Algebra.smul_def ((tp k : F) * (tw k : F))⁻¹, map_inv₀, map_mul]
    rw [eq_comm, inv_mul_eq_iff_eq_mul₀ hcE]
    ring
  refine ⟨GlobalTheory.EmbChart.atPlace v (algebraMap F (Fv F v) ((tp k * tw k : 𝓞 F) : F)⁻¹), GlobalTheory.VacAny.at_atPlace _, ?_, _,
    hpX k, _, hwY k, ?_⟩
  · rw [GlobalTheory.EmbChart.evFin_atPlace]
    exact inv_mem_O hc0
  · rw [hvm, incM_smul, smul_smul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul, AlgHom.commutes]

theorem latAtV_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latAtV G.V' G.W v ↔ ∀ γ ∈ latAtV G.V' G.W v,
        B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin z hz
  have hB := hT.base
  have hV' := hT.geo.hV'
  have hW := hT.geo.hW
  have h1v : evFin F v (1 : AF F) ∈ v.adicCompletionIntegers F := by rw [map_one]; exact one_mem _
  constructor
  · intro hzΓ γ hγ
    have h := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hB hV' hW v (-1) 1 h1v z hzΓ γ hγ
    simpa using h
  · intro hc
    obtain ⟨X₀, hX₀⟩ := GlobalTheory.T.matrix_adelic_decomposition_at_finite_place F E G.V' G.W hV'.lat hW.lat v z hz
    have hc₀ : ∀ γ ∈ latAtV G.V' G.W v, B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J)
        (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1 := by
      intro γ hγ
      have h1 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hB hV' hW v (-1) 1 h1v _ hX₀ γ hγ
      have hm : inclR (F := F) (AF F) (((-1 : 𝓞 E)) : E) = -1 := by simp
      rw [hm, one_mul] at h1
      have e : GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ = z + -(z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) := by abel
      rw [e, GlobalTheory.LatVacArith.symp_add_left, GlobalTheory.LatVacArith.symp_neg_left, AddChar.map_add_eq_mul,
        AddChar.map_neg_eq_inv, hc γ hγ, h1, inv_one, one_mul]
    have hint := GlobalTheory.T.trace_hermitianTensor_integral_of_char_trivial F E σ B.ψ G.V' G.W v (hB.inert v w hin).2.2 X₀ hc₀
    have hmem := lemD σ B G.V' G.W hB.unram hV' hW v X₀ hint
    have e : z = (z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) + GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ := by abel
    rw [e]
    exact add_mem hX₀ hmem

end GlobalTheory.InertDual
