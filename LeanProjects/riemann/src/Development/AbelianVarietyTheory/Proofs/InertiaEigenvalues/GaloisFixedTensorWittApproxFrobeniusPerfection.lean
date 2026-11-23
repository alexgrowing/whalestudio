import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantApproxByEpsilonRootsClosureStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootsMemFrobeniusPerfectionModStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.DecomplDense

section Perf

variable {E R : Type} [CommRing E] [CommRing R] (ι : E →+* R) (φ : R →+* R) (p : ℕ)

def InPerf (x : R) : Prop := ∃ (n : ℕ) (e : E) (r : R), φ^[n] x = ι e + (p : R) * r

variable {ι φ p}

theorem perf_persist (hφ : ∀ e, ∃ e', φ (ι e) = ι e') {x : R} {n : ℕ} {e : E} {r : R}
    (h : φ^[n] x = ι e + (p : R) * r) (k : ℕ) :
    ∃ (e' : E) (r' : R), φ^[k + n] x = ι e' + (p : R) * r' := by
  induction k with
  | zero => exact ⟨e, r, by simpa using h⟩
  | succ k ih =>
    obtain ⟨e₁, r₁, h₁⟩ := ih
    obtain ⟨e₂, he₂⟩ := hφ e₁
    refine ⟨e₂, φ r₁, ?_⟩
    rw [show k + 1 + n = (k + n) + 1 by omega, Function.iterate_succ_apply', h₁]
    simp [map_add, map_mul, map_natCast, he₂]

theorem InPerf.of_ι (e : E) : InPerf ι φ p (ι e) := ⟨0, e, 0, by simp⟩

theorem InPerf.add (hφ : ∀ e, ∃ e', φ (ι e) = ι e') {x y : R} (hx : InPerf ι φ p x)
    (hy : InPerf ι φ p y) : InPerf ι φ p (x + y) := by
  obtain ⟨n, e, r, h⟩ := hx
  obtain ⟨m, f, s, h'⟩ := hy
  obtain ⟨e', r', he⟩ := perf_persist hφ h m
  obtain ⟨f', s', hf⟩ := perf_persist hφ h' n
  refine ⟨m + n, e' + f', r' + s', ?_⟩
  have hc : (φ^[m + n]) (x + y) = φ^[m + n] x + φ^[m + n] y := by
    rw [← RingHom.coe_pow]; exact map_add _ _ _
  rw [hc, he, show m + n = n + m by omega, hf]
  simp only [map_add]; ring

theorem InPerf.mul (hφ : ∀ e, ∃ e', φ (ι e) = ι e') {x y : R} (hx : InPerf ι φ p x)
    (hy : InPerf ι φ p y) : InPerf ι φ p (x * y) := by
  obtain ⟨n, e, r, h⟩ := hx
  obtain ⟨m, f, s, h'⟩ := hy
  obtain ⟨e', r', he⟩ := perf_persist hφ h m
  obtain ⟨f', s', hf⟩ := perf_persist hφ h' n
  refine ⟨m + n, e' * f', ι e' * s' + r' * ι f' + (p : R) * r' * s', ?_⟩
  have hc : (φ^[m + n]) (x * y) = φ^[m + n] x * φ^[m + n] y := by
    rw [← RingHom.coe_pow]; exact map_mul _ _ _
  rw [hc, he, show m + n = n + m by omega, hf]
  simp only [map_mul]; ring

theorem InPerf.sum (hφ : ∀ e, ∃ e', φ (ι e) = ι e') {I : Type} (s : Finset I) {f : I → R}
    (h : ∀ i ∈ s, InPerf ι φ p (f i)) : InPerf ι φ p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (InPerf.of_ι (ι := ι) (φ := φ) (p := p) (0 : E))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact InPerf.add hφ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem exists_inPerf_near {A : Type} [CommRing A] {j : A →+* R} {t : R}
    (hφ : ∀ e, ∃ e', φ (ι e) = ι e') {τ : E} (hτ : IsUnit τ) (ht : ι τ = t) {N m : ℕ} {y y1 : R}
    (h1 : InPerf ι φ p y1) (h2 : Near j p t (N + m) (t ^ N * y - y1)) :
    ∃ y0, InPerf ι φ p y0 ∧ Near j p t m (y - y0) := by
  obtain ⟨a, r, har⟩ := h2
  obtain ⟨v, rfl⟩ := hτ
  have hc : ι ((↑v⁻¹ : E) ^ N) * t ^ N = 1 := by
    rw [← ht, ← map_pow, ← map_mul, ← mul_pow, Units.inv_mul, one_pow, map_one]
  refine ⟨ι ((↑v⁻¹ : E) ^ N) * y1, InPerf.mul hφ (InPerf.of_ι _) h1, a,
    ι ((↑v⁻¹ : E) ^ N) * r, ?_⟩
  have key : y - ι ((↑v⁻¹ : E) ^ N) * y1 = ι ((↑v⁻¹ : E) ^ N) * (t ^ N * y - y1) := by
    linear_combination (-y) * hc
  rw [key, har]
  linear_combination (t ^ m * j a) * hc

private theorem sum_crd_lemma {Z O W : Type} [CommRing Z] [CommRing O] [Algebra Z O] [CommRing W]
    [Algebra Z W] {n : ℕ} (b : Module.Basis (Fin n) Z O) (z : O ⊗[Z] W) :
    ∑ i, b i ⊗ₜ[Z] crd b i z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp only [crd, TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lsmul_apply]
    simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← TensorProduct.sum_tmul]
    congr 1
    simpa [Module.Basis.coord_apply] using b.sum_repr o
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

private theorem eq_l_mul_lemma_2 {l : ℕ} [Fact l.Prime] (a : WittVector l (Cb l)) (ha : a.coeff 0 = 0) :
    ∃ r : WittVector l (Cb l), a = (l : WittVector l (Cb l)) * r := by
  by_cases h0 : a = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul a h0
  cases m with
  | zero => simp only [pow_zero, one_mul] at ha; exact absurd ha hb
  | succ m => exact ⟨(l : WittVector l (Cb l)) ^ m * b, by ring⟩

private theorem coeff_step_lemma_4 {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (LL : FinExt l) (s N k : ℕ) (y : RW LL) (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (u v : OCb l)
    (h : algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ N) * (crd (basisO LL) i y).coeff 0 =
      algebraMap (OCb l) (Cb l) (u + (AI.εroot s - 1) ^ k * v)) :
    ∃ r : WittVector l (Cb l),
      inclW l (piW AI s) ^ N * crd (basisO LL) i y - inclW l (WittVector.teichmuller l u) -
        inclW l (piW AI s) ^ k * inclW l (WittVector.teichmuller l v) = (l : WittVector l (Cb l)) * r := by
  have hcc : ∀ z : Ainf l, (WittVector.constantCoeff : WittVector l (Cb l) →+* Cb l) (inclW l z) =
      algebraMap (OCb l) (Cb l) ((WittVector.constantCoeff : WittVector l (OCb l) →+* OCb l) z) := by
    intro z
    simp [inclW, WittVector.map_coeff]
  apply eq_l_mul_lemma_2
  rw [← WittVector.constantCoeff_apply]
  simp only [map_sub, map_mul, map_pow, hcc, piW, map_one, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero] at h ⊢
  simp only [map_add, map_mul, map_pow, map_sub, map_one] at h
  linear_combination h

set_option maxHeartbeats 1000000 in
private theorem nearPi_sum_lemma_5 {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (LL : FinExt l) (s N k : ℕ) (y : RW LL) (u v : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → OCb l)
    (r : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → WittVector l (Cb l))
    (hr : ∀ i, inclW l (piW AI s) ^ N * crd (basisO LL) i y - inclW l (WittVector.teichmuller l (u i)) -
        inclW l (piW AI s) ^ k * inclW l (WittVector.teichmuller l (v i)) = (l : WittVector l (Cb l)) * r i) :
    NearPi AI LL s k (piR AI LL s ^ N * y -
      ∑ i, basisO LL i ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (u i))) := by
  have hR : ∀ (o : ↥(OL LL)) (a : Ainf l), inclR LL (o ⊗ₜ[ℤ_[l]] a) = o ⊗ₜ[ℤ_[l]] inclW l a := by
    intro o a
    unfold inclR
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hl : ((l : ℕ) : RW LL) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] ((l : ℕ) : WCb l) := by
    rw [← map_natCast (Algebra.TensorProduct.includeRight (R := ℤ_[l]) (A := ↥(OL LL)) (B := WCb l)) l]
    rfl
  have hsm : ∀ (o : ↥(OL LL)) (w : WCb l),
      ((l : ℕ) : RW LL) * (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] (((l : ℕ) : WCb l) * w) := by
    intro o w
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.tmul_smul]
  have e1 : inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) ^ N * y =
      ∑ i, basisO LL i ⊗ₜ[ℤ_[l]] (inclW l (piW AI s) ^ N * crd (basisO LL) i y) := by
    conv_lhs => rw [← sum_crd_lemma (basisO LL) y]
    rw [hR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [one_pow, one_mul]
  have e2 : inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) ^ k *
      (inclR LL : RA LL →+* RW LL) (∑ i, basisO LL i ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (v i)) =
      ∑ i, basisO LL i ⊗ₜ[ℤ_[l]] (inclW l (piW AI s) ^ k * inclW l (WittVector.teichmuller l (v i))) := by
    change inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) ^ k *
      inclR LL (∑ i, basisO LL i ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (v i)) = _
    rw [map_sum]
    simp only [hR]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [one_pow, one_mul]
  have e3 : ((l : ℕ) : RW LL) * ∑ i, basisO LL i ⊗ₜ[ℤ_[l]] r i =
      ∑ i, basisO LL i ⊗ₜ[ℤ_[l]] (((l : ℕ) : WCb l) * r i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hsm _ _
  unfold NearPi Near piR
  refine ⟨∑ i, basisO LL i ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (v i), ∑ i, basisO LL i ⊗ₜ[ℤ_[l]] r i, ?_⟩
  rw [e1, e2, e3, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have key : inclW l (piW AI s) ^ N * crd (basisO LL) i y - inclW l (WittVector.teichmuller l (u i)) =
      inclW l (piW AI s) ^ k * inclW l (WittVector.teichmuller l (v i)) + (l : WittVector l (Cb l)) * r i := by
    rw [← hr i]; ring
  rw [← TensorProduct.tmul_sub, ← TensorProduct.tmul_add, key]

end Perf

variable {l : ℕ} [Fact l.Prime]

theorem nearPi_of_coeff {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s N k : ℕ)
    (y : RW LL) (u v : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → OCb l)
    (h : ∀ i, algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ N) * (crd (basisO LL) i y).coeff 0 =
      algebraMap (OCb l) (Cb l) (u i + (AI.εroot s - 1) ^ k * v i)) :
    NearPi AI LL s k (piR AI LL s ^ N * y -
      ∑ i, basisO LL i ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (u i))) := by
  classical
  choose r hr using fun i => coeff_step_lemma_4 AI LL s N k y i (u i) (v i) (h i)
  exact nearPi_sum_lemma_5 AI LL s N k y u v r hr

theorem tmul_eq_algebraMap_mul {Z O W : Type} [CommRing Z] [CommRing O] [Algebra Z O] [CommRing W]
    [Algebra Z W] (o : O) (w : W) :
    o ⊗ₜ[Z] w = algebraMap O (O ⊗[Z] W) o * ((1 : O) ⊗ₜ[Z] w) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  simp

private theorem crd_map_lemma_6 {Z O W : Type} [CommRing Z] [CommRing O] [Algebra Z O] [CommRing W]
    [Algebra Z W] {n : ℕ} (b : Module.Basis (Fin n) Z O) (f : W →ₐ[Z] W) (i : Fin n) (z : O ⊗[Z] W) :
    crd b i (Algebra.TensorProduct.map (AlgHom.id O O) f z) = f (crd b i z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, crd, TensorProduct.lift.tmul,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.lsmul_apply, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 1000000 in

theorem fixSub_approx_perfection (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL)
    (E : EtSit P AI K s LL h W) :
    ∀ y ∈ fixSub AI LL (Hinf K : Set (GQ l)), ∀ m : ℕ,
      ∃ (n : ℕ) (y0 : RW LL) (e : W.EE) (r : RW LL),
        (φRW LL)^[n] y0 = E.tie.ioE e + (l : RW LL) * r ∧ NearPi AI LL s m (y - y0) := by
  intro y hy m
  classical
  have hfix : ∀ g ∈ Hinf K, AI.gRW LL g y = y := by
    intro g hg
    unfold fixSub at hy
    simp only [Subring.mem_iInf, RingHom.mem_eqLocus] at hy
    exact hy g hg
  obtain ⟨hφE, -, hπ, -⟩ := GlobalTheory.T.etaleEmbedding_frobenius_galois_compat l P AI K s LL h W E
  have hφ : ∀ e, ∃ e', φRW LL (E.tie.ioE e) = E.tie.ioE e' := fun e => ⟨W.φE e, (hφE e).symm⟩
  have hcoef : ∀ i, ∀ g ∈ Hinf K, autCb l (AI.actT g) ((crd (basisO LL) i y).coeff 0) =
      (crd (basisO LL) i y).coeff 0 := by
    intro i g hg
    have hc := congrArg (fun z => (crd (basisO LL) i z).coeff 0) (hfix g hg)
    simp only [LocAinf.gRW, LocAinf.actWCbHom, MonoidHom.coe_mk, OneHom.coe_mk] at hc
    rw [crd_map_lemma_6] at hc
    conv_rhs => rw [← hc]
    rfl
  have hφ' : ∀ e, ∃ e', (φRW LL : RW LL →+* RW LL) ((E.tie.ioE : W.EE →+* RW LL) e) =
      (E.tie.ioE : W.EE →+* RW LL) e' := hφ
  have hap : ∀ i, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ u ∈ Subring.closure (Set.range AI.εroot ∪
      {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}),
      ∃ v : OCb l, algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ N) * (crd (basisO LL) i y).coeff 0 =
        algebraMap (OCb l) (Cb l) (u + (AI.εroot s - 1) ^ (N + m) * v) :=
    fun i => GlobalTheory.T.tilt_invariant_approx_by_epsilonRoots_closure l P AI K s ((crd (basisO LL) i y).coeff 0) (hcoef i) m
  choose N₀ hN₀ using hap
  have hall : ∀ i, ∃ u ∈ Subring.closure (Set.range AI.εroot ∪
      {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}),
      ∃ v : OCb l, algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ (∑ j, N₀ j)) *
          (crd (basisO LL) i y).coeff 0 =
        algebraMap (OCb l) (Cb l) (u + (AI.εroot s - 1) ^ ((∑ j, N₀ j) + m) * v) :=
    fun i => hN₀ i _ (Finset.single_le_sum (fun j _ => Nat.zero_le (N₀ j)) (Finset.mem_univ i))
  choose u hu v hv using hall
  have hnear := nearPi_of_coeff AI LL s (∑ j, N₀ j) ((∑ j, N₀ j) + m) y u v hv
  have hy1 : InPerf (E.tie.ioE : W.EE →+* RW LL) (φRW LL : RW LL →+* RW LL) l
      (∑ i, basisO LL i ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (u i))) := by
    apply InPerf.sum hφ'
    intro i _
    rw [tmul_eq_algebraMap_mul (basisO LL i) (inclW l (WittVector.teichmuller l (u i)))]
    apply InPerf.mul hφ'
    · have hb : algebraMap ↥(OL LL) (RW LL) (basisO LL i) =
          (E.tie.ioE : W.EE →+* RW LL) (algebraMap ↥(OL LL) W.EE (basisO LL i)) :=
        (E.tie.ioE.commutes _).symm
      rw [hb]
      exact InPerf.of_ι _
    · exact GlobalTheory.T.teichmullerEpsilonRoots_mem_frobeniusPerfection_mod_l l P AI K s LL h W E (u i) (hu i)
  unfold NearPi at hnear
  obtain ⟨y0, hy0, hn0⟩ := exists_inPerf_near (j := (inclR LL : RA LL →+* RW LL)) hφ' W.EE_π hπ hy1 hnear
  obtain ⟨n, e, r, her⟩ := hy0
  exact ⟨n, y0, e, r, her, hn0⟩

end GlobalTheory.DecomplDense
