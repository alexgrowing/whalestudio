import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SplitAnisotropic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentTarget
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGram
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrixStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeExtendByScalarBlockStatement
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.ZeroBlockCoefficientRankIncreaseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeZeroRankOneOfThreeLeStatement
import Development.WeilBound.CoreStatements.ThetaDilations.ContinuousPm

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_add_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J x (y + z) = hE σ J x y + hE σ J x z := by
  simp [hE, hform, mul_add, Finset.sum_add_distrib]

theorem hE_add_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J (x + y) z = hE σ J x z + hE σ J y z := by
  simp [hE, hform, add_mul, Finset.sum_add_distrib]

theorem hE_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J x (c • y) = c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J (c • x) y = σ c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul,
    AlgHom.coe_toRingHom, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_herm (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (y z : Fin M → E) : σ (hE σ J y z) = hE σ J z y := by
  simp only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

def hLin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    (Fin M → E) →ₗ[E] E where
  toFun y := hE σ J x y
  map_add' := hE_add_right σ J x
  map_smul' c y := by simp [hE_smul_right]

theorem hLin_apply (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hLin σ J x y = hE σ J x y := rfl

theorem hE_sum_right (σ : E →ₐ[F] E) {M : ℕ} {ι : Type} (J : Matrix (Fin M) (Fin M) E)
    (x : Fin M → E) (s : Finset ι) (c : ι → E) (y : ι → Fin M → E) :
    hE σ J x (∑ k ∈ s, c k • y k) = ∑ k ∈ s, c k * hE σ J x (y k) := by
  rw [← hLin_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hLin_apply, hE_smul_right]

theorem cT_mul_apply (σ : E →ₐ[F] E) {M N : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (col : Fin N → Fin M → E) (i j : Fin N) :
    (cT (σ : E →+* E) (Matrix.of fun a b => col b a : Matrix (Fin M) (Fin N) E) * J *
      (Matrix.of fun a b => col b a : Matrix (Fin M) (Fin N) E)) i j = hE σ J (col i) (col j) := by
  simp only [cT, Matrix.mul_apply, hE, hform, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem split_herm (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hT : ∀ a b, σ (T b a) = T a b)
    (s : E) (x : Fin (n + 1) → E) (hs0 : s ≠ 0) (hx : hE σ T x x = s) :
    ∃ (g : GL (Fin (n + 1)) E) (T₁ : Matrix (Fin n) (Fin n) E), (∀ a b, σ (T₁ b a) = T₁ a b) ∧
      blockOne s T₁ = cT (σ : E →+* E) (g : Matrix (Fin (n + 1)) (Fin (n + 1)) E) * T * g := by
  have hherm := hE_herm σ hσ T hT
  have hsurj : Function.Surjective (hLin σ T x) := fun e =>
    ⟨(e / s) • x, by rw [map_smul, hLin_apply, hx, smul_eq_mul]; field_simp⟩
  have hfr : Module.finrank E (LinearMap.ker (hLin σ T x)) = n := by
    have h := LinearMap.finrank_range_add_finrank_ker (hLin σ T x)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
    simp at h
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker (hLin σ T x)) hfr
  have hb : ∀ k, hE σ T x (b k : Fin (n + 1) → E) = 0 := fun k => (b k).2
  let col : Fin (n + 1) → Fin (n + 1) → E := Fin.cons x (fun k => (b k : Fin (n + 1) → E))
  let gm : Matrix (Fin (n + 1)) (Fin (n + 1)) E := Matrix.of fun i j => col j i
  have hG : ∀ i j, (cT (σ : E →+* E) gm * T * gm) i j = hE σ T (col i) (col j) :=
    fun i j => cT_mul_apply σ T col i j
  have hdet : gm.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hsum : v 0 • x + ∑ k : Fin n, v k.succ • (b k : Fin (n + 1) → E) = 0 := by
      rw [← hv]
      ext i
      simp [gm, col, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
    have hv00 : v 0 = 0 := by
      have h1 := congrArg (hLin σ T x) hsum
      rw [map_add, map_smul, map_sum, map_zero, hLin_apply, hx, smul_eq_mul] at h1
      have h2 : ∀ k : Fin n, hLin σ T x (v k.succ • (b k : Fin (n + 1) → E)) = 0 := by
        intro k
        rw [map_smul, hLin_apply, hb, smul_zero]
      simp only [h2, Finset.sum_const_zero, add_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_right hs0
    have hker : ∑ k : Fin n, v k.succ • b k = 0 := by
      apply Subtype.ext
      rw [hv00, zero_smul, zero_add] at hsum
      simpa using hsum
    have hvs := Fintype.linearIndependent_iff.1 b.linearIndependent _ hker
    apply hv0
    ext i
    refine Fin.cases hv00 hvs i
  let T₁ : Matrix (Fin n) (Fin n) E := Matrix.of fun k l =>
    hE σ T (b k : Fin (n + 1) → E) (b l : Fin (n + 1) → E)
  have hblock : blockOne s T₁ = cT (σ : E →+* E) gm * T * gm := by
    ext i j
    rw [hG]
    refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
    · simp [blockOne, col, hx]
    · simp [blockOne, col, hb]
    · have h3 : hE σ T (b k : Fin (n + 1) → E) x = 0 := by
        rw [← hherm, hb, map_zero]
      simp [blockOne, col, h3]
    · simp [blockOne, col, T₁]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero gm hdet, T₁, fun k l => hherm _ _, hblock⟩

variable [NumberField F] [NumberField E]

theorem exists_value (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (h0 : T ≠ 0) :
    ∃ (t : F) (x : Fin n → E), t ≠ 0 ∧ hE σ T x x = algebraMap F E t := by
  obtain ⟨hσ, δ, hδ, hδs⟩ := HaarCoord.conj_facts hCM
  have hherm := hE_herm σ hσ T hT
  have hne : ∃ x, hE σ T x x ≠ 0 := by
    by_contra hall
    push_neg at hall
    have key : ∀ x y, hE σ T x y + hE σ T y x = 0 := by
      intro x y
      have h := hall (x + y)
      rw [hE_add_left, hE_add_right, hE_add_right, hall x, hall y] at h
      simpa using h
    have key2 : ∀ x y, hE σ T x y = 0 := by
      intro x y
      have h1 := key x (δ • y)
      rw [hE_smul_right, hE_smul_left, hδs] at h1
      have h2 := key x y
      have h3 : δ * (hE σ T x y - hE σ T y x) = 0 := by linear_combination h1
      have h4 := (mul_eq_zero.1 h3).resolve_left hδ
      have h5 : (2 : E) * hE σ T x y = 0 := by linear_combination h2 + h4
      exact (mul_eq_zero.1 h5).resolve_left two_ne_zero
    apply h0
    ext a b
    have := key2 (Pi.single a 1) (Pi.single b 1)
    simpa [hE, hform, Pi.single_apply] using this
  obtain ⟨x, hx⟩ := hne
  have hs : σ (hE σ T x x) = hE σ T x x := hherm x x
  obtain ⟨β, hβ, -, -⟩ := GlobalTheory.CompanionTheory.SW.hermOne_eq_scal F E σ hCM (fun _ _ => hE σ T x x) (fun _ _ => hs)
  have hβ' : hE σ T x x = algebraMap F E β := congrFun (congrFun hβ 0) 0
  refine ⟨β, x, ?_, hβ'⟩
  rintro rfl
  exact hx (by simpa using hβ')

theorem hE_hypOne_cons (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a b c d : E)
    (x y : Fin M → E) :
    hE σ (hypOne J) (Fin.cons a (Fin.cons b x) : Fin (M + 2) → E)
        (Fin.cons c (Fin.cons d y) : Fin (M + 2) → E) = σ a * d + σ b * c + hE σ J x y := by
  simp only [hE, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have e00 : hypOne J 0 0 = 0 := rfl
  have e01 : hypOne J 0 (Fin.succ 0) = 1 := rfl
  have e10 : hypOne J (Fin.succ 0) 0 = 1 := rfl
  have e11 : hypOne J (Fin.succ 0) (Fin.succ 0) = 0 := rfl
  have e0r : ∀ j : Fin M, hypOne J 0 j.succ.succ = 0 := fun _ => rfl
  have e1r : ∀ j : Fin M, hypOne J (Fin.succ 0) j.succ.succ = 0 := fun _ => rfl
  have er0 : ∀ i : Fin M, hypOne J i.succ.succ 0 = 0 := fun _ => rfl
  have er1 : ∀ i : Fin M, hypOne J i.succ.succ (Fin.succ 0) = 0 := fun _ => rfl
  have err : ∀ i j : Fin M, hypOne J i.succ.succ j.succ.succ = J i j := fun _ _ => rfl
  simp only [e00, e01, e10, e11, e0r, e1r, er0, er1, err]
  simp
  ring

theorem split_hyp (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin (M + 2)) (Fin (M + 2)) E) (hJ : IsHermND σ J) (x : Fin (M + 2) → E)
    (hx0 : x ≠ 0) (hxx : hE σ J x x = 0) :
    ∃ (g : GL (Fin (M + 2)) E) (J₁ : Matrix (Fin M) (Fin M) E), IsHermND σ J₁ ∧
      hypOne J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M + 2)) (Fin (M + 2)) E) * J * g ∧
      ∀ i, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) E) i 0 = x i := by
  obtain ⟨hσ, -⟩ := HaarCoord.conj_facts hCM
  have hherm := hE_herm σ hσ J hJ.1

  have hex : ∃ y₀, hE σ J x y₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := by
      funext j
      have := hall (Pi.single j 1)
      simpa [hE, hform, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hz : (fun i => σ (x i)) = 0 := by
      have hu : IsUnit J := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hJ.2)
      exact (Matrix.vecMul_injective_of_isUnit hu) (by simpa using hv)
    apply hx0
    funext i
    have := congrFun hz i
    simpa using this
  obtain ⟨y₀, hy₀⟩ := hex
  obtain ⟨y₁, hxy₁⟩ : ∃ y₁, hE σ J x y₁ = 1 :=
    ⟨(hE σ J x y₀)⁻¹ • y₀, by rw [hE_smul_right]; exact inv_mul_cancel₀ hy₀⟩
  have hy₁x : hE σ J y₁ x = 1 := by rw [← hherm, hxy₁, map_one]
  obtain ⟨q, hq⟩ : ∃ q, q = hE σ J y₁ y₁ := ⟨_, rfl⟩
  have hqs : σ q = q := by rw [hq]; exact hherm _ _
  obtain ⟨y, hy⟩ : ∃ y : Fin (M + 2) → E, y = y₁ + (-(q / 2)) • x := ⟨_, rfl⟩
  have hxy : hE σ J x y = 1 := by
    rw [hy, hE_add_right, hE_smul_right, hxy₁, hxx]; simp
  have hyx : hE σ J y x = 1 := by rw [← hherm, hxy, map_one]
  have hyy : hE σ J y y = 0 := by
    have hs2 : σ (-(q / 2)) = -(q / 2) := by
      rw [map_neg, map_div₀, hqs, map_ofNat]
    rw [hy, hE_add_right, hE_add_left, hE_add_left, hE_smul_right, hE_smul_right, hE_smul_left,
      hE_smul_left, hs2, hy₁x, hxy₁, hxx, ← hq]
    field_simp
    ring
  let ψ : (Fin (M + 2) → E) →ₗ[E] (Fin 2 → E) := LinearMap.pi ![hLin σ J x, hLin σ J y]
  have hψ0 : ∀ z, ψ z 0 = hE σ J x z := fun _ => rfl
  have hψ1 : ∀ z, ψ z 1 = hE σ J y z := fun _ => rfl
  have hsurj : Function.Surjective ψ := fun e =>
    ⟨e 0 • y + e 1 • x, by
      funext i
      fin_cases i
      · change ψ _ 0 = e 0
        rw [hψ0, hE_add_right, hE_smul_right, hE_smul_right, hxy, hxx]; simp
      · change ψ _ 1 = e 1
        rw [hψ1, hE_add_right, hE_smul_right, hE_smul_right, hyx, hyy]; simp⟩
  have hfr : Module.finrank E (LinearMap.ker ψ) = M := by
    have h := LinearMap.finrank_range_add_finrank_ker ψ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
    simp at h
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker ψ) hfr
  have hb0 : ∀ k, hE σ J x (b k : Fin (M + 2) → E) = 0 := fun k => by
    rw [← hψ0, LinearMap.mem_ker.1 (b k).2]; rfl
  have hb1 : ∀ k, hE σ J y (b k : Fin (M + 2) → E) = 0 := fun k => by
    rw [← hψ1, LinearMap.mem_ker.1 (b k).2]; rfl
  have hb0' : ∀ k, hE σ J (b k : Fin (M + 2) → E) x = 0 := fun k => by
    rw [← hherm, hb0, map_zero]
  have hb1' : ∀ k, hE σ J (b k : Fin (M + 2) → E) y = 0 := fun k => by
    rw [← hherm, hb1, map_zero]
  let col : Fin (M + 2) → Fin (M + 2) → E :=
    Fin.cons x (Fin.cons y (fun k => (b k : Fin (M + 2) → E)))
  let gm : Matrix (Fin (M + 2)) (Fin (M + 2)) E := Matrix.of fun i j => col j i
  have hG : ∀ i j, (cT (σ : E →+* E) gm * J * gm) i j = hE σ J (col i) (col j) :=
    fun i j => cT_mul_apply σ J col i j
  have hdet : gm.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hsum : v 0 • x + v (Fin.succ 0) • y +
        ∑ k : Fin M, v k.succ.succ • (b k : Fin (M + 2) → E) = 0 := by
      rw [← hv]
      ext i
      simp [gm, col, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm, add_assoc]
    have hsx := congrArg (hE σ J x) hsum
    have hsy := congrArg (hE σ J y) hsum
    have hz0 : hE σ J x 0 = 0 := GlobalTheory.CompanionTheory.SW.BlockAlg.hE_zero_right σ J x
    have hz1 : hE σ J y 0 = 0 := GlobalTheory.CompanionTheory.SW.BlockAlg.hE_zero_right σ J y
    rw [hz0, hE_add_right, hE_add_right, hE_smul_right, hE_smul_right, hE_sum_right, hxx, hxy] at hsx
    rw [hz1, hE_add_right, hE_add_right, hE_smul_right, hE_smul_right, hE_sum_right, hyx, hyy] at hsy
    simp only [hb0, hb1, mul_zero, Finset.sum_const_zero, add_zero, mul_one, zero_add] at hsx hsy
    have hker : ∑ k : Fin M, v k.succ.succ • b k = 0 := by
      apply Subtype.ext
      rw [hsx, hsy, zero_smul, zero_smul, zero_add, zero_add] at hsum
      simpa using hsum
    have hvs := Fintype.linearIndependent_iff.1 b.linearIndependent _ hker
    apply hv0
    ext i
    refine Fin.cases hsy (fun i => Fin.cases hsx hvs i) i
  let J₁ : Matrix (Fin M) (Fin M) E := Matrix.of fun k l =>
    hE σ J (b k : Fin (M + 2) → E) (b l : Fin (M + 2) → E)
  have hblock : hypOne J₁ = cT (σ : E →+* E) gm * J * gm := by
    ext i j
    rw [hG]
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i <;>
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) j
    · simpa [col, hypOne] using hxx.symm
    · simpa [col, hypOne] using hxy.symm
    · simpa [col, hypOne] using (hb0 l).symm
    · simpa [col, hypOne] using hyx.symm
    · simpa [col, hypOne] using hyy.symm
    · simpa [col, hypOne] using (hb1 l).symm
    · simpa [col, hypOne] using (hb0' k).symm
    · simpa [col, hypOne] using (hb1' k).symm
    · simp [col, hypOne, J₁]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero gm hdet, J₁, ⟨fun k l => hherm _ _, ?_⟩, hblock,
    fun i => rfl⟩
  intro hJ0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hJ0
  have hd0 : (hypOne J₁).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨Fin.cons 0 (Fin.cons 0 v), ?_, ?_⟩
    · intro h
      apply hv0
      funext i
      simpa using congrFun h i.succ.succ
    · funext i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hypOne]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hypOne]
      · have := congrFun hv k
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hypOne] using this
  rw [hblock, Matrix.det_mul, Matrix.det_mul] at hd0
  have h5 : (cT (σ : E →+* E) gm).det = σ gm.det := by
    rw [cT, Matrix.det_transpose]
    exact ((σ : E →+* E).map_det gm).symm
  rw [h5] at hd0
  have h6 : σ gm.det ≠ 0 := (map_ne_zero _).2 hdet
  exact mul_ne_zero (mul_ne_zero h6 hJ.2) hdet hd0

theorem frames_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) E) (X : Fin n → Fin M → E)
    (hX : X ∈ framesE σ J T) :
    Scale.rE X (g : Matrix (Fin n) (Fin n) E) ∈
      framesE σ J (cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * (g : Matrix (Fin n) (Fin n) E)) := by
  refine ⟨?_, by rw [Scale.gramE_rE, hX.2]⟩
  have hind := Fintype.linearIndependent_iff.1 hX.1
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  have h1 : ∀ b, ((g : Matrix (Fin n) (Fin n) E).mulVec c) b = 0 := by
    refine hind _ ?_
    funext i
    have := congrFun hc i
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Scale.rE,
      Finset.mul_sum] at this ⊢
    rw [Finset.sum_comm] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  have h2 : (g : Matrix (Fin n) (Fin n) E).mulVec c = 0 := funext h1
  have h3 : c = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).mulVec
      ((g : Matrix (Fin n) (Fin n) E).mulVec c) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]
    simp
  intro a
  rw [h3, h2]
  simp

theorem frames_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) (g : GL (Fin M) E) (X : Fin n → Fin M → E)
    (hX : X ∈ framesE σ J T) :
    SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) X ∈
      framesE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) T := by
  have hgg : ∀ u : Fin M → E, (g : Matrix (Fin M) (Fin M) E).mulVec
      (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
    simp
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective
        (Matrix.mulVecLin ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) := fun u w h => by
      have h' : ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec u =
        ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec w := h
      rw [← hgg u, h', hgg]
    have hfun : SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) X =
        (Matrix.mulVecLin ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) ∘ X := by
      funext a
      rfl
    rw [hfun]
    exact LinearIndependent.map' hX.1
      (Matrix.mulVecLin ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E))
      (LinearMap.ker_eq_bot.2 hinj)
  · have key : ∀ a b, hE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
        (g : Matrix (Fin M) (Fin M) E))
        (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec (X a))
        (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec (X b)) = hE σ J (X a) (X b) := by
      intro a b
      simp only [hE, SWIsom.hform_conj, hgg]
    rw [← hX.2]
    funext a b
    exact key a b

theorem frames_tail_aniso (σ : E →ₐ[F] E) {M n : ℕ} (J₁ : Matrix (Fin M) (Fin M) E)
    (T₁ : Matrix (Fin n) (Fin n) E) (s : E) (hs : s ≠ 0) (X : Fin (n + 1) → Fin (M + 1) → E)
    (hX : X ∈ framesE σ (blockOne s J₁) (blockOne s T₁))
    (h0 : X 0 = Fin.cons 1 (fun _ => 0)) :
    (fun (a : Fin n) (i : Fin M) => X a.succ i.succ) ∈ framesE σ J₁ T₁ := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hgr : ∀ a b, hE σ (blockOne s J₁) (X a) (X b) = blockOne s T₁ a b := fun a b =>
    congrFun (congrFun hX.2 a) b
  have hc : ∀ a, X a = Fin.cons (X a 0) (fun i => X a i.succ) := fun a =>
    (Fin.cons_self_tail (X a)).symm
  have hfirst : ∀ a : Fin n, X a.succ 0 = 0 := by
    intro a
    have h := hgr 0 a.succ
    rw [h0, hc a.succ, BlockAlg.hE_blockOne_cons, hz, BlockAlg.hE_zero_left] at h
    have h2 : blockOne s T₁ 0 a.succ = 0 := rfl
    rw [h2] at h
    simp only [map_one, one_mul, add_zero] at h
    simpa [hs] using h
  refine ⟨?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc' a => ?_
    have h1 := Fintype.linearIndependent_iff.1 hX.1 (Fin.cons 0 c) (by
      rw [Fin.sum_univ_succ]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [hfirst]
      · have := congrFun hc' i
        simpa using this) a.succ
    simpa using h1
  · ext a b
    have h := hgr a.succ b.succ
    rw [hc a.succ, hc b.succ, BlockAlg.hE_blockOne_cons, hfirst, hfirst] at h
    have h2 : blockOne s T₁ a.succ b.succ = T₁ a b := rfl
    rw [h2] at h
    simpa [gramE] using h

theorem frames_tail_hyp (σ : E →ₐ[F] E) {M n : ℕ} (J₁ : Matrix (Fin M) (Fin M) E)
    (X : Fin (n + 1) → Fin (M + 2) → E) (hX : X ∈ framesE σ (hypOne J₁) 0)
    (h0 : X 0 = Fin.cons 1 (Fin.cons 0 (fun _ => 0))) :
    (fun (a : Fin n) (i : Fin M) => X a.succ i.succ.succ) ∈ framesE σ J₁ 0 := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hgr : ∀ a b, hE σ (hypOne J₁) (X a) (X b) = 0 := fun a b =>
    congrFun (congrFun hX.2 a) b
  have hc : ∀ a, X a = Fin.cons (X a 0) (Fin.cons (X a (Fin.succ 0)) (fun i => X a i.succ.succ)) :=
    fun a => by
      funext i
      refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i
  have hsec : ∀ a : Fin n, X a.succ (Fin.succ 0) = 0 := by
    intro a
    have h := hgr 0 a.succ
    rw [h0, hc a.succ, hE_hypOne_cons, hz, BlockAlg.hE_zero_left] at h
    simpa using h
  refine ⟨?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc' a => ?_
    have h1 := Fintype.linearIndependent_iff.1 hX.1
      (Fin.cons (-∑ k, c k * X k.succ 0) c) (by
      rw [Fin.sum_univ_succ, h0]
      funext i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
      · simp [Finset.sum_apply]
      · have hsec' : ∀ a : Fin n, X a.succ 1 = 0 := hsec
        simp [Finset.sum_apply, hsec']
      · have := congrFun hc' k
        simpa [Finset.sum_apply] using this) a.succ
    simpa using h1
  · ext a b
    have h := hgr a.succ b.succ
    rw [hc a.succ, hc b.succ, hE_hypOne_cons, hsec, hsec] at h
    simpa [gramE] using h

end Alg

section Main

theorem swFree_singular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det = 0 → 2 * n < M → (framesE σ J T).Nonempty → SWFree σ J T hT := by
  intro F E _ _ _ _ _ σ hCM n
  obtain ⟨hσ, -⟩ := HaarCoord.conj_facts hCM
  induction n with
  | zero =>
    intro M J hJ T hT hd
    simp at hd
  | succ n ih =>
    intro M J hJ T hT hd hM hfr
    obtain ⟨X, hX⟩ := hfr
    by_cases h0 : T = 0
    · subst h0
      rcases n with _ | n
      · exact GlobalTheory.T.siegelWeilFree_zero_rank_one_of_three_le F E σ hCM M J hJ (by omega) hT ⟨X, hX⟩
      · obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 2 := ⟨M - 2, by omega⟩
        have hx0 : X 0 ≠ 0 := hX.1.ne_zero 0
        have hxx : hE σ J (X 0) (X 0) = 0 := congrFun (congrFun hX.2 0) 0
        obtain ⟨g, J₁, hJ₁, hb, hcol⟩ := split_hyp σ hCM J hJ (X 0) hx0 hxx
        have hX' := frames_left σ J _ g X hX
        rw [← hb] at hX'
        have hfirst : SWIsom.ratAct ((g⁻¹ : GL (Fin (M₁ + 2)) E) : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) X 0 =
            Fin.cons 1 (Fin.cons 0 (fun _ => 0)) := by
          have he : (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E).mulVec
              (Fin.cons 1 (Fin.cons 0 (fun _ => 0))) = X 0 := by
            funext i
            rw [← hcol i]
            simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
          simp only [SWIsom.ratAct]
          rw [← he, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]
          simp
        have hfr₁ := frames_tail_hyp σ J₁ _ hX' hfirst
        have h₀ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) =
            (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b := fun a b => by simp
        have hSW := ih M₁ J₁ hJ₁ 0 h₀ Matrix.det_zero (by omega) ⟨_, hfr₁⟩
        exact GlobalTheory.T.siegelWeilFree_of_congruent_form F E σ hCM (M₁ + 2) J hJ g _ hb (n + 1 + 1) 0 hT
          (GlobalTheory.T.zero_block_coefficient_rank_increase F E σ hCM M₁ J₁ hJ₁ (n + 1) (by omega) (by omega) h₀ hT ⟨_, hfr₁⟩ hSW)
    · obtain ⟨t, x, ht, hx⟩ := exists_value σ hCM T hT h0
      have hta : algebraMap F E t ≠ 0 := by simpa using ht
      obtain ⟨g, T₁, hT₁, hb⟩ := split_herm σ hσ T hT _ x hta hx
      obtain ⟨-, hblk, -, -⟩ := GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM n T₁ t
      have hT' := hblk hT₁
      have hg0 : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) E).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
      have hd₁ : T₁.det = 0 := by
        have h := congrArg Matrix.det hb
        rw [BlockAlg.det_blockOne, Matrix.det_mul, Matrix.det_mul, hd] at h
        simp only [mul_zero, zero_mul] at h
        exact (mul_eq_zero.1 h).resolve_left hta
      have hX₁ := frames_right σ J T g X hX
      rw [← hb] at hX₁
      obtain ⟨Y, hY⟩ : ∃ Y, Y = Scale.rE X (g : Matrix (Fin (n + 1)) (Fin (n + 1)) E) := ⟨_, rfl⟩
      rw [← hY] at hX₁
      have hyy : hE σ J (Y 0) (Y 0) = algebraMap F E t := congrFun (congrFun hX₁.2 0) 0
      obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 1 := ⟨M - 1, by omega⟩
      obtain ⟨g', J₁, hJ₁, hb', hcol⟩ :=
        GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hCM M₁ J hJ t (Y 0) ht hyy
      have hX₂ := frames_left σ J _ g' Y hX₁
      rw [← hb'] at hX₂
      have hfirst : SWIsom.ratAct ((g'⁻¹ : GL (Fin (M₁ + 1)) E) : Matrix (Fin (M₁ + 1)) (Fin (M₁ + 1)) E) Y 0 =
          Fin.cons 1 (fun _ => 0) := by
        have he : (g' : Matrix (Fin (M₁ + 1)) (Fin (M₁ + 1)) E).mulVec
            (Fin.cons 1 (fun _ => 0)) = Y 0 := by
          funext i
          rw [← hcol i]
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        simp only [SWIsom.ratAct]
        rw [← he, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]
        simp
      have hfr₁ := frames_tail_aniso σ J₁ T₁ _ hta _ hX₂ hfirst
      have hSW := ih M₁ J₁ hJ₁ T₁ hT₁ hd₁ (by omega) ⟨_, hfr₁⟩
      refine GlobalTheory.T.siegelWeilFree_of_congruent_matrix F E σ hCM (M₁ + 1) J hJ (n + 1) T hT g _ hT' hb ?_
      exact GlobalTheory.T.siegelWeilFree_of_congruent_form F E σ hCM (M₁ + 1) J hJ g' _ hb' (n + 1) _ hT'
        (GlobalTheory.T.siegelWeilFree_extend_by_scalar_block F E σ hCM M₁ J₁ hJ₁ t ht n (by omega) T₁ hT₁ hT' ⟨_, hfr₁⟩ hSW)

theorem swFree_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n t : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), IsBlockM t T → 2 * n < M → (framesE σ J T).Nonempty → SWFree σ J T hT := by
  intro F E _ _ _ _ _ σ hCM M J hJ n t T hT hB hM hfr
  obtain ⟨h, hz, -⟩ := hB
  exact swFree_singular F E σ hCM n M J hJ T hT
    (Matrix.det_eq_zero_of_row_eq_zero ⟨t, h⟩ fun j => hz _ _ (Or.inl le_rfl)) hM hfr

end Main

end GlobalTheory.CompanionTheory.WeilSiegel.Free
