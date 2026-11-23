import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DetFromColsFrameChange
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FromRowsMulFromColsSplit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DddTriv

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat Matrix

section Alg

variable {Ω : Type} [Field Ω]

def UnitIn (R : Subring Ω) (a : Ω) : Prop := a ≠ 0 ∧ a ∈ R ∧ a⁻¹ ∈ R

def IntM (R : Subring Ω) {m n : Type} (M : Matrix m n Ω) : Prop := ∀ i j, M i j ∈ R

def CongM (R : Subring Ω) (ϖ : Ω) {m n : Type} (M N : Matrix m n Ω) : Prop :=
  ∀ i j, ∃ c ∈ R, M i j - N i j = ϖ * c

def frameDet {p q : ℕ} (J : Matrix (Fin (p + q)) (Fin p) Ω) (T : Matrix (Fin (p + q)) (Fin q) Ω) : Ω :=
  (fromCols (J.submatrix finSumFinEquiv id) (T.submatrix finSumFinEquiv id)).det

theorem IntM.exists_lift {R : Subring Ω} {m n : Type} {M : Matrix m n Ω} (h : IntM R M) :
    ∃ M' : Matrix m n R, M'.map R.subtype = M :=
  ⟨fun i j => ⟨M i j, h i j⟩, by ext i j; rfl⟩

theorem map_quot_eq {R : Subring Ω} {ϖ : Ω} (hϖ : ϖ ∈ R) {m n : Type} {M N : Matrix m n R}
    (h : CongM R ϖ (M.map R.subtype) (N.map R.subtype)) :
    M.map (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : R)})) =
      N.map (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : R)})) := by
  ext i j
  obtain ⟨c, hc, e⟩ := h i j
  simp only [Matrix.map_apply]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
  simp only [Matrix.map_apply, Subring.subtype_apply] at e
  push_cast
  rw [e, mul_comm]

theorem isUnit_of_quot {R : Type} [CommRing R] [IsLocalRing R] {π d : R} (hπ : ¬ IsUnit π)
    (h : IsUnit (Ideal.Quotient.mk (Ideal.span {π}) d)) : IsUnit d := by
  by_contra hd
  obtain ⟨u, hu⟩ := h.exists_right_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton'] at hu
  obtain ⟨c, hc⟩ := hu
  have h1 : d * u ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hd)
  have h2 : c * π ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 hπ)
  have h3 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    have : (1 : R) = d * u - c * π := by rw [hc]; ring
    rw [this]
    exact sub_mem h1 h2
  exact (IsLocalRing.mem_maximalIdeal _).1 h3 isUnit_one

theorem isUnit_sub_iff {R : Subring Ω} {a : Ω} (ha : a ∈ R) : IsUnit (⟨a, ha⟩ : R) ↔ UnitIn R a := by
  constructor
  · intro h
    obtain ⟨⟨u, hu⟩, hv⟩ := h.exists_right_inv
    have e : a * u = 1 := congrArg Subtype.val hv
    have h0 : a ≠ 0 := left_ne_zero_of_mul_eq_one e
    refine ⟨h0, ha, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right e]
    exact hu
  · rintro ⟨h0, h1, h2⟩
    exact IsUnit.of_mul_eq_one (⟨a⁻¹, h2⟩ : R) (Subtype.ext (mul_inv_cancel₀ h0))

section Det

variable {p q : ℕ}

theorem frameDet_map {R : Subring Ω} (J : Matrix (Fin (p + q)) (Fin p) R) (T : Matrix (Fin (p + q)) (Fin q) R) :
    frameDet (J.map R.subtype) (T.map R.subtype) =
      ((fromCols (J.submatrix finSumFinEquiv id) (T.submatrix finSumFinEquiv id)).det : R) := by
  have : fromCols ((J.map R.subtype).submatrix finSumFinEquiv id) ((T.map R.subtype).submatrix finSumFinEquiv id)
      = (fromCols (J.submatrix finSumFinEquiv id) (T.submatrix finSumFinEquiv id)).map R.subtype := by
    ext i (j | j) <;> simp
  rw [frameDet, this]
  exact (RingHom.map_det R.subtype _).symm

theorem quot_of_cong {R : Subring Ω} {ϖ : Ω} (hϖ : ϖ ∈ R) {m n : Type} {M N : Matrix m n R} {M₀ N₀ : Matrix m n Ω}
    (hM : M.map R.subtype = M₀) (hN : N.map R.subtype = N₀) (h : CongM R ϖ M₀ N₀) :
    M.map (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : R)})) =
      N.map (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : R)})) := by
  subst hM hN
  exact map_quot_eq hϖ h

theorem unit_frameDet {R : Subring Ω} [IsLocalRing R] {ϖ : Ω} (hϖ : ϖ ∈ R) (hn : ¬ UnitIn R ϖ)
    {J : Matrix (Fin (p + q)) (Fin p) Ω} {S : Matrix (Fin q) (Fin (p + q)) Ω}
    {T : Matrix (Fin (p + q)) (Fin q) Ω} {P : Matrix (Fin p) (Fin (p + q)) Ω}
    (hJ : IntM R J) (hS : IntM R S) (hT : IntM R T) (hP : IntM R P)
    (h0 : CongM R ϖ (S * J) 0) (h1 : CongM R ϖ (P * J) 1) (h2 : CongM R ϖ (S * T) 1) :
    UnitIn R (frameDet J T) := by
  obtain ⟨J, rfl⟩ := hJ.exists_lift
  obtain ⟨S, rfl⟩ := hS.exists_lift
  obtain ⟨T, rfl⟩ := hT.exists_lift
  obtain ⟨P, rfl⟩ := hP.exists_lift
  have e0 := quot_of_cong hϖ (M := S * J) (N := 0) Matrix.map_mul (Matrix.map_zero _ (map_zero _)) h0
  have e1 := quot_of_cong hϖ (M := P * J) (N := 1) Matrix.map_mul (Matrix.map_one _ (map_zero _) (map_one _)) h1
  have e2 := quot_of_cong hϖ (M := S * T) (N := 1) Matrix.map_mul (Matrix.map_one _ (map_zero _) (map_one _)) h2
  set φ := Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : R)}) with hφ
  rw [Matrix.map_zero _ (map_zero _)] at e0
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at e1 e2
  let e := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))
  have key : ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (M : Matrix m (Fin (p + q)) R) (N : Matrix (Fin (p + q)) n R),
      (M.submatrix id e).map φ * (N.submatrix e id).map φ = (M * N).map φ := by
    intro m n _ _ _ M N
    rw [← Matrix.map_mul, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hu := (splitExact_of_rank _ p q ((J.submatrix e id).map φ) ((S.submatrix id e).map φ)
    (by rw [key, e0]) ⟨(P.submatrix id e).map φ, by rw [key, e1]⟩
    ⟨(T.submatrix e id).map φ, by rw [key, e2]⟩).1 ((T.submatrix e id).map φ) (by rw [key, e2])
  have e3 : fromCols ((J.submatrix e id).map φ) ((T.submatrix e id).map φ) =
      (fromCols (J.submatrix e id) (T.submatrix e id)).map φ := by
    ext i (j | j) <;> simp
  rw [e3, show ∀ M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) R, (M.map φ).det = φ M.det from
    fun M => (RingHom.map_det φ M).symm] at hu
  have hπ : ¬ IsUnit (⟨ϖ, hϖ⟩ : R) := fun h => hn ((isUnit_sub_iff hϖ).1 h)
  have hd := isUnit_of_quot hπ hu
  rw [frameDet_map]
  exact (isUnit_sub_iff (Subtype.coe_prop _)).1 hd

theorem frameDet_cong {R : Subring Ω} {ϖ : Ω} (hϖ : ϖ ∈ R)
    {J J₂ : Matrix (Fin (p + q)) (Fin p) Ω} {S S₂ : Matrix (Fin q) (Fin (p + q)) Ω}
    {T T₂ : Matrix (Fin (p + q)) (Fin q) Ω} {M : Matrix (Fin p) (Fin p) Ω} {B : Matrix (Fin q) (Fin q) Ω}
    (hJ : IntM R J) (hS : IntM R S) (hT : IntM R T) (hJ₂ : IntM R J₂) (hS₂ : IntM R S₂) (hT₂ : IntM R T₂)
    (hM : IntM R M) (hB : IntM R B)
    (h0 : CongM R ϖ (S * J) 0) (h2 : CongM R ϖ (S * T) 1) (hu : UnitIn R (frameDet J T))
    (h2' : CongM R ϖ (S₂ * T₂) 1) (hJM : CongM R ϖ J₂ (J * M)) (hSB : CongM R ϖ S (B * S₂)) :
    ∃ c ∈ R, frameDet J₂ T₂ - frameDet J T * M.det * B.det = ϖ * c := by
  obtain ⟨J, rfl⟩ := hJ.exists_lift
  obtain ⟨S, rfl⟩ := hS.exists_lift
  obtain ⟨T, rfl⟩ := hT.exists_lift
  obtain ⟨J₂, rfl⟩ := hJ₂.exists_lift
  obtain ⟨S₂, rfl⟩ := hS₂.exists_lift
  obtain ⟨T₂, rfl⟩ := hT₂.exists_lift
  obtain ⟨M, rfl⟩ := hM.exists_lift
  obtain ⟨B, rfl⟩ := hB.exists_lift
  have e0 := quot_of_cong hϖ (M := S * J) (N := 0) Matrix.map_mul (Matrix.map_zero _ (map_zero _)) h0
  have e2 := quot_of_cong hϖ (M := S * T) (N := 1) Matrix.map_mul (Matrix.map_one _ (map_zero _) (map_one _)) h2
  have e2' := quot_of_cong hϖ (M := S₂ * T₂) (N := 1) Matrix.map_mul (Matrix.map_one _ (map_zero _) (map_one _)) h2'
  have e4 := quot_of_cong hϖ (M := J₂) (N := J * M) rfl Matrix.map_mul hJM
  have e5 := quot_of_cong hϖ (M := S) (N := B * S₂) rfl Matrix.map_mul hSB
  set φ := Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : R)}) with hφ
  rw [Matrix.map_zero _ (map_zero _)] at e0
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at e2 e2'
  let e := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))
  have key : ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (M : Matrix m (Fin (p + q)) R) (N : Matrix (Fin (p + q)) n R),
      (M.submatrix id e).map φ * (N.submatrix e id).map φ = (M * N).map φ := by
    intro m n _ _ _ M N
    rw [← Matrix.map_mul, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hdet : ∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n R), (M.map φ).det = φ M.det :=
    fun M => (RingHom.map_det φ M).symm
  have e3 : ∀ (J : Matrix (Fin (p + q)) (Fin p) R) (T : Matrix (Fin (p + q)) (Fin q) R),
      (fromCols ((J.submatrix e id).map φ) ((T.submatrix e id).map φ)).det =
      φ (fromCols (J.submatrix e id) (T.submatrix e id)).det := by
    intro J T
    rw [← hdet]
    congr 1
    ext i (j | j) <;> simp
  have hu' : IsUnit (fromCols ((J.submatrix e id).map φ) ((T.submatrix e id).map φ)).det := by
    rw [e3]
    apply IsUnit.map φ
    rw [frameDet_map] at hu
    exact (isUnit_sub_iff (Subtype.coe_prop _)).2 hu
  have s1 : (J * M).submatrix e id = J.submatrix e id * M := by
    ext i j; simp [Matrix.mul_apply]
  have s2 : (B * S₂).submatrix id e = B * S₂.submatrix id e := by
    ext i j; simp [Matrix.mul_apply]
  have main := det_fromCols_frame_change _ p q ((J.submatrix e id).map φ) ((J₂.submatrix e id).map φ)
    ((S.submatrix id e).map φ) ((S₂.submatrix id e).map φ) ((T.submatrix e id).map φ)
    ((T₂.submatrix e id).map φ) (M.map φ) (B.map φ) (by rw [key, e0]) (by rw [key, e2]) hu'
    (by rw [key, e2'])
    (by
      change (J₂.map φ).submatrix e id = _
      rw [e4]
      change ((J * M).submatrix e id).map φ = _
      rw [s1, Matrix.map_mul])
    (by
      change (S.map φ).submatrix id e = _
      rw [e5]
      change ((B * S₂).submatrix id e).map φ = _
      rw [s2, Matrix.map_mul])
  rw [e3, e3, hdet, hdet, ← map_mul, ← map_mul, hφ, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at main
  obtain ⟨c, hc⟩ := main
  refine ⟨c, c.2, ?_⟩
  rw [frameDet_map, frameDet_map,
    show (M.map R.subtype).det = (M.det : R) from (RingHom.map_det R.subtype M).symm,
    show (B.map R.subtype).det = (B.det : R) from (RingHom.map_det R.subtype B).symm]
  have := congrArg Subtype.val hc
  push_cast at this
  rw [← this, mul_comm]

end Det

end Alg

section Lin

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

def Mat {N r : ℕ} (Jl : E →ₗ[Ω] (Fin N → Ω)) (v : Fin r → E) : Matrix (Fin N) (Fin r) Ω :=
  fun k i => Jl (v i) k

theorem exists_coeff {R : Subring Ω} {n : ℕ} {v : Fin n → E} {e : E}
    (h : e ∈ Submodule.span R (Set.range v)) : ∃ c : Fin n → Ω, (∀ i, c i ∈ R) ∧ e = ∑ i, c i • v i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h
  exact ⟨fun i => c i, fun i => (c i).2, rfl⟩

theorem mem_span_self {R : Subring Ω} {n : ℕ} (v : Fin n → E) (i : Fin n) :
    v i ∈ Submodule.span R (Set.range v) := Submodule.subset_span ⟨i, rfl⟩

theorem split_matrix {R : Subring Ω} {ϖ : Ω} {r N : ℕ} (L : Submodule R E) {v : Fin r → E}
    (hv : LinearIndependent Ω v) (hL : L = Submodule.span R (Set.range v)) (Jl : E →ₗ[Ω] (Fin N → Ω))
    (Rm : (Fin N → Ω) →ₗ[Ω] E) (h1 : ∀ k, Rm (Pi.single k 1) ∈ L)
    (h2 : ∀ w ∈ L, ∃ w' ∈ L, Rm (Jl w) = w + ϖ • w') :
    ∃ P : Matrix (Fin r) (Fin N) Ω, IntM R P ∧ CongM R ϖ (P * Mat Jl v) 1 := by
  classical
  have h1' : ∀ k, ∃ c : Fin r → Ω, (∀ i, c i ∈ R) ∧ Rm (Pi.single k 1) = ∑ i, c i • v i := fun k =>
    exists_coeff (hL ▸ h1 k)
  choose C hC hCe using h1'
  have h2' : ∀ i, ∃ d : Fin r → Ω, (∀ l, d l ∈ R) ∧ Rm (Jl (v i)) = v i + ϖ • ∑ l, d l • v l := by
    intro i
    obtain ⟨w', hw', e⟩ := h2 (v i) (hL ▸ mem_span_self v i)
    obtain ⟨d, hd, rfl⟩ := exists_coeff (hL ▸ hw')
    exact ⟨d, hd, e⟩
  choose D hD hDe using h2'
  set P : Matrix (Fin r) (Fin N) Ω := fun i k => C k i with hP
  refine ⟨P, fun i k => hC k i, fun l i => ⟨D i l, hD i l, ?_⟩⟩
  have hx : ∀ x : Fin N → Ω, Rm x = ∑ k, x k • Rm (Pi.single k 1) := by
    intro x
    have : x = ∑ k, x k • (Pi.single k 1 : Fin N → Ω) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp
  have e1 : Rm (Jl (v i)) = ∑ l, (P * Mat Jl v) l i • v l := by
    rw [hx]
    simp only [hCe, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
    rfl
  have e2 := hDe i
  rw [e1] at e2
  have e3 : ∑ l, ((P * Mat Jl v) l i -
      (1 : Matrix (Fin r) (Fin r) Ω) l i - ϖ * D i l) • v l = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, e2, mul_smul, ← Finset.smul_sum]
    simp [Matrix.one_apply, ite_smul]
  have := Fintype.linearIndependent_iff.1 hv _ e3 l
  exact sub_eq_zero.1 this

theorem Mat_comb {N r s : ℕ} (Jl : E →ₗ[Ω] (Fin N → Ω)) (u : Fin s → E) (C : Matrix (Fin s) (Fin r) Ω) :
    Mat Jl (fun i => ∑ l, C l i • u l) = Mat Jl u * C := by
  ext k i
  simp [Mat, Matrix.mul_apply, mul_comm]

theorem CongM.transpose {R : Subring Ω} {ϖ : Ω} {m n : Type} {M N : Matrix m n Ω} (h : CongM R ϖ M N) :
    CongM R ϖ Mᵀ Nᵀ := fun i j => h j i

theorem cong_Mat {R : Subring Ω} {ϖ : Ω} (h0 : ϖ ≠ 0) {N r : ℕ} {J₁ J₂ : E →ₗ[Ω] (Fin N → Ω)} {v : Fin r → E}
    (h : ∀ i k, (J₁ (v i) k - J₂ (v i) k) / ϖ ∈ R) : CongM R ϖ (Mat J₁ v) (Mat J₂ v) := fun k i =>
  ⟨_, h i k, by simp only [Mat]; field_simp⟩

theorem UnitIn.sub_mul {R : Subring Ω} [IsLocalRing R] {ϖ d c : Ω} (hϖ : ϖ ∈ R) (hn : ¬ UnitIn R ϖ)
    (hd : UnitIn R d) (hc : c ∈ R) : UnitIn R (d - ϖ * c) := by
  have h1 : d - ϖ * c ∈ R := sub_mem hd.2.1 (mul_mem hϖ hc)
  have h2 : ϖ * c ∈ R := mul_mem hϖ hc
  have h3 : IsUnit ((⟨d - ϖ * c, h1⟩ : R) + ⟨ϖ * c, h2⟩) := by
    have : (⟨d - ϖ * c, h1⟩ : R) + ⟨ϖ * c, h2⟩ = ⟨d, hd.2.1⟩ := Subtype.ext (by simp)
    rw [this]
    exact (isUnit_sub_iff _).2 hd
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h3 with h | h
  · exact (isUnit_sub_iff _).1 h
  · exfalso
    have : (⟨ϖ * c, h2⟩ : R) = ⟨ϖ, hϖ⟩ * ⟨c, hc⟩ := rfl
    rw [this] at h
    exact hn ((isUnit_sub_iff _).1 (isUnit_of_mul_isUnit_left h))

theorem final_field {R : Subring Ω} [IsLocalRing R] {ϖ : Ω} (hϖ : ϖ ∈ R) (hn : ¬ UnitIn R ϖ) {M : Submodule R Ω}
    {αx βx αy βy dx dy m n c : Ω} (hα : αy / βy ≠ 0) (hM : M = Submodule.span R {αx / βx}) (hg : αx / βx ≠ 0)
    (hdx : UnitIn R dx) (hdy : UnitIn R dy) (hc : c ∈ R) (hm : dx - dy * m * n = ϖ * c)
    (h1 : αx = m * αy) (h2 : βy = n * βx) :
    (αx / βx) / dx ≠ 0 ∧ M = Submodule.span R {(αx / βx) / dx} ∧
      ∃ z ∈ M, (αx / βx) / dx - (αy / βy) / dy = ϖ • z := by
  have hD : UnitIn R (dy * m * n) := by
    have := UnitIn.sub_mul hϖ hn hdx hc
    rwa [← hm, sub_sub_cancel] at this
  have hm0 : m ≠ 0 := fun h => hD.1 (by simp [h])
  have hn0 : n ≠ 0 := fun h => hD.1 (by simp [h])
  have hy0 := hdy.1
  have hx0 := hdx.1
  have hαy : αy ≠ 0 := fun h => hα (by simp [h])
  have hβy : βy ≠ 0 := fun h => hα (by simp [h])
  have hβx : βx ≠ 0 := fun h => hg (by simp [h])
  have hgen : αx / βx / dx = (⟨dx⁻¹, hdx.2.2⟩ : R) • (αx / βx) := by
    change _ = dx⁻¹ * _
    rw [div_eq_mul_inv _ dx, mul_comm]
  have hu : IsUnit (⟨dx⁻¹, hdx.2.2⟩ : R) :=
    (isUnit_sub_iff _).2 ⟨inv_ne_zero hx0, hdx.2.2, by rw [inv_inv]; exact hdx.2.1⟩
  refine ⟨div_ne_zero hg hx0, ?_, (⟨-c * dx⁻¹ * (dy * m * n)⁻¹, ?_⟩ : R) • (αx / βx), ?_, ?_⟩
  · rw [hM, hgen]
    exact (Submodule.span_singleton_smul_eq hu _).symm
  · exact mul_mem (mul_mem (neg_mem hc) hdx.2.2) hD.2.2
  · rw [hM]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · change _ = ϖ * ((-c * dx⁻¹ * (dy * m * n)⁻¹) * (αx / βx))
    have e : ϖ * ((-c * dx⁻¹ * (dy * m * n)⁻¹) * (αx / βx)) =
        -(ϖ * c) * dx⁻¹ * (dy * m * n)⁻¹ * (αx / βx) := by ring
    rw [e, ← hm, h1, h2]
    field_simp
    ring

end Lin

section Pt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

structure Loc (A B : Lat ξ E) (ϖ : Ω) {N p q : ℕ} (J J' : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω))) (x : Cpt ξ)
    (v : Fin p → E) (w : Fin q → E) (T : Matrix (Fin N) (Fin q) Ω) (y : Cpt ξ) : Prop where
  fa : A.IsFrameAt v y
  fb : B.IsFrameAt w y
  sa : SplitModAt A ϖ J x y
  sb : SplitModAt B ϖ J' x y
  orth : ∀ e ∈ A y, ∀ e' ∈ B y, dotProduct (J x e) (J' x e') / ϖ ∈ regAt ξ y
  ti : IntM (regAt ξ y) T
  tc : CongM (regAt ξ y) ϖ ((Mat (J' x) w)ᵀ * T) 1

theorem exists_loc {A B : Lat ξ E} {ϖ : Ω} {N p q : ℕ} {V V' : Submodule Ω E}
    {J J' : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω))} (hA : A.IsVB p V) (hB : B.IsVB q V') {x : Cpt ξ} (hx : ¬ unitAt ξ x ϖ)
    {U₀ : X.Opens} (hU₀ : x.1 ∈ U₀)
    (H : ∀ y : Cpt ξ, y.1 ∈ U₀ → ¬ unitAt ξ y ϖ → SplitModAt A ϖ J x y ∧ SplitModAt B ϖ J' x y ∧
      ∀ w ∈ A y, ∀ w' ∈ B y, dotProduct (J x w) (J' x w') / ϖ ∈ regAt ξ y) :
    ∃ (v : Fin p → E) (w : Fin q → E) (T : Matrix (Fin N) (Fin q) Ω) (U : X.Opens), x.1 ∈ U ∧
      ∀ y : Cpt ξ, y.1 ∈ U → ¬ unitAt ξ y ϖ → Loc A B ϖ J J' x v w T y := by
  obtain ⟨U₁, hU₁, v, -, hv⟩ := hA x trivial
  obtain ⟨U₂, hU₂, w, -, hw⟩ := hB x trivial
  obtain ⟨-, ⟨-, Rm, hR1, hR2⟩, -⟩ := H x hU₀ hx
  have hfb := hw x trivial hU₂
  obtain ⟨P, hP, hPc⟩ := split_matrix (B x) hfb.1 hfb.2 (J' x) Rm hR1 hR2
  have hc := hPc.transpose
  rw [Matrix.transpose_mul, Matrix.transpose_one] at hc
  choose c hc1 hc2 using hc
  obtain ⟨U₃, hU₃, hreg⟩ := EigSplit.exists_open_forall_mem_regAt x
    (Sum.elim (fun ij : Fin N × Fin q => Pᵀ ij.1 ij.2) (fun ij : Fin q × Fin q => c ij.1 ij.2))
    (by rintro (⟨i, j⟩ | ⟨i, j⟩)
        · exact hP j i
        · exact hc1 i j)
  refine ⟨v, w, Pᵀ, U₀ ⊓ U₁ ⊓ U₂ ⊓ U₃, ⟨⟨⟨hU₀, hU₁⟩, hU₂⟩, hU₃⟩, ?_⟩
  rintro y ⟨⟨⟨hy₀, hy₁⟩, hy₂⟩, hy₃⟩ hy
  obtain ⟨s1, s2, s3⟩ := H y hy₀ hy
  exact ⟨hv y trivial hy₁, hw y trivial hy₂, s1, s2, s3, fun i j => hreg y hy₃ (Sum.inl (i, j)),
    fun i j => ⟨c i j, hreg y hy₃ (Sum.inr (i, j)), hc2 i j⟩⟩

section

variable {A B : Lat ξ E} {ϖ : Ω} {p q : ℕ} {J J' : Cpt ξ → (E →ₗ[Ω] (Fin (p + q) → Ω))}
  {x y : Cpt ξ} {v : Fin p → E} {w : Fin q → E} {T : Matrix (Fin (p + q)) (Fin q) Ω}

theorem Loc.mem_a (h : Loc A B ϖ J J' x v w T y) (i : Fin p) : v i ∈ A y := by
  rw [h.fa.2]; exact mem_span_self v i

theorem Loc.mem_b (h : Loc A B ϖ J J' x v w T y) (i : Fin q) : w i ∈ B y := by
  rw [h.fb.2]; exact mem_span_self w i

theorem Loc.intJ (h : Loc A B ϖ J J' x v w T y) : IntM (regAt ξ y) (Mat (J x) v) :=
  fun k i => (h.sa.1 _ (h.mem_a i) k).1

theorem Loc.intS (h : Loc A B ϖ J J' x v w T y) : IntM (regAt ξ y) (Mat (J' x) w)ᵀ :=
  fun i k => (h.sb.1 _ (h.mem_b i) k).1

theorem Loc.orthM (h : Loc A B ϖ J J' x v w T y) (h0 : ϖ ≠ 0) :
    CongM (regAt ξ y) ϖ ((Mat (J' x) w)ᵀ * Mat (J x) v) 0 := by
  intro j i
  refine ⟨_, h.orth _ (h.mem_a i) _ (h.mem_b j), ?_⟩
  simp only [Matrix.zero_apply, sub_zero, Matrix.mul_apply, Matrix.transpose_apply, Mat]
  rw [mul_div_cancel₀ _ h0, dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem Loc.unit (h : Loc A B ϖ J J' x v w T y) (h0 : ϖ ≠ 0) (hϖ : ϖ ∈ regAt ξ y) (hn : ¬ unitAt ξ y ϖ) :
    unitAt ξ y (frameDet (Mat (J x) v) T) := by
  haveI := EigSplit.isLocalRing_regAt y
  obtain ⟨-, Rm, hR1, hR2⟩ := h.sa
  obtain ⟨P, hP, hPc⟩ := split_matrix (A y) h.fa.1 h.fa.2 (J x) Rm hR1 hR2
  exact unit_frameDet hϖ hn h.intJ h.intS h.ti hP (h.orthM h0) hPc h.tc

theorem Loc.compare {vy : Fin p → E} {wy : Fin q → E} {Ty : Matrix (Fin (p + q)) (Fin q) Ω}
    (hx : Loc A B ϖ J J' x v w T y) (hy : Loc A B ϖ J J' y vy wy Ty y) (h0 : ϖ ≠ 0) (hϖ : ϖ ∈ regAt ξ y)
    (hn : ¬ unitAt ξ y ϖ) :
    ∃ m n c : Ω, c ∈ regAt ξ y ∧ exteriorPower.ιMulti Ω p v = m • exteriorPower.ιMulti Ω p vy ∧
      exteriorPower.ιMulti Ω q wy = n • exteriorPower.ιMulti Ω q w ∧
      frameDet (Mat (J x) v) T - frameDet (Mat (J y) vy) Ty * m * n = ϖ * c := by
  have h1 : ∀ i, ∃ c : Fin p → Ω, (∀ l, c l ∈ regAt ξ y) ∧ v i = ∑ l, c l • vy l := fun i =>
    exists_coeff (hy.fa.2 ▸ hx.mem_a i)
  have h2 : ∀ j, ∃ c : Fin q → Ω, (∀ l, c l ∈ regAt ξ y) ∧ wy j = ∑ l, c l • w l := fun j =>
    exists_coeff (hx.fb.2 ▸ hy.mem_b j)
  obtain ⟨C, hC, hCe⟩ : ∃ C : Matrix (Fin p) (Fin p) Ω, (∀ i l, C i l ∈ regAt ξ y) ∧ ∀ i, v i = ∑ l, C i l • vy l := by
    choose C hC hCe using h1
    exact ⟨C, hC, hCe⟩
  obtain ⟨D, hD, hDe⟩ : ∃ D : Matrix (Fin q) (Fin q) Ω, (∀ i l, D i l ∈ regAt ξ y) ∧ ∀ j, wy j = ∑ l, D j l • w l := by
    choose D hD hDe using h2
    exact ⟨D, hD, hDe⟩
  have hvC : v = fun i => ∑ l, (Cᵀ : Matrix (Fin p) (Fin p) Ω) l i • vy l := funext hCe
  have hJ : CongM (regAt ξ y) ϖ (Mat (J x) v) (Mat (J y) vy * Cᵀ) := by
    rw [← Mat_comb, ← hvC]
    exact cong_Mat h0 fun i k => (hx.sa.1 _ (hx.mem_a i) k).2
  have hS : CongM (regAt ξ y) ϖ (Mat (J' y) wy)ᵀ (D * (Mat (J' x) w)ᵀ) := by
    have hwD : wy = fun j => ∑ l, (Dᵀ : Matrix (Fin q) (Fin q) Ω) l j • w l := funext hDe
    have e : D * (Mat (J' x) w)ᵀ = (Mat (J' x) wy)ᵀ := by
      conv_rhs => rw [hwD, Mat_comb, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [e]
    refine CongM.transpose (cong_Mat h0 fun j k => ?_)
    have := (hx.sb.1 _ (hy.mem_b j) k).2
    have e2 : (J' y (wy j) k - J' x (wy j) k) / ϖ = - ((J' x (wy j) k - J' y (wy j) k) / ϖ) := by ring
    rw [e2]
    exact neg_mem this
  have hM : IntM (regAt ξ y) Cᵀ := fun i j => hC j i
  obtain ⟨c, hc, e⟩ := frameDet_cong hϖ hy.intJ hy.intS hy.ti hx.intJ hx.intS hx.ti hM hD (hy.orthM h0) hy.tc
    (hy.unit h0 hϖ hn) hx.tc hJ hS
  refine ⟨Cᵀ.det, D.det, c, hc, ?_, ?_, e⟩
  · have := alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti Ω p (M := E)) C vy
    rw [Matrix.det_transpose, ← this]
    exact congrArg _ (funext hCe)
  · have := alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti Ω q (M := E)) D w
    rw [← this]
    exact congrArg _ (funext hDe)

end

end Pt

section Main

theorem trivMod_lineLat : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (ϖ : Ω), IsCptGen ξ → ϖ ≠ 0 → (∀ x, ϖ ∈ regAt ξ x) → A.IsVB p V → B.IsVB q V' → a ≠ 0 → b ≠ 0 → (∃ x f, IsCoeffAt A B p q a b x f) → ExactModLat A B ϖ (p + q) → TrivMod (lineLat A B p q a b) ϖ := by
  intro X Ω _ ξ E _ _ A B p q V V' a b ϖ _ h0 hϖ hA hB ha hb ⟨x₀, f, hf⟩ ⟨J, J', hE⟩
  obtain ⟨hL, hGen, hFr⟩ := GlobalTheory.T.wedge_line_lattice_vector_bundle X Ω ξ E A B p q V V' Set.univ a b hA hB ha hb ⟨x₀, trivial, f, hf⟩
  have hcoef : ∀ x : Cpt ξ, ∃ α₀ β₀ : Ω, A.wedge p x = Submodule.span (regAt ξ x) {α₀ • a} ∧
      B.wedge q x = Submodule.span (regAt ξ x) {β₀ • b} := by
    intro x
    obtain ⟨e, he, h1, -⟩ := exists_gen_of_isVB_one (L := lineLat A B p q a b) hL x
    obtain ⟨-, α₀, β₀, -, -, h2, h3, -⟩ := (hGen x trivial e).1 ⟨he, h1⟩
    exact ⟨α₀, β₀, h2, h3⟩
  have H : ∀ x : Cpt ξ, ∃ (v : Fin p → E) (w : Fin q → E) (T : Matrix (Fin (p + q)) (Fin q) Ω) (U : X.Opens) (α β : Ω),
      ¬ unitAt ξ x ϖ → x.1 ∈ U ∧ (∀ y : Cpt ξ, y.1 ∈ U → ¬ unitAt ξ y ϖ → Loc A B ϖ J J' x v w T y) ∧
        exteriorPower.ιMulti Ω p v = α • a ∧ exteriorPower.ιMulti Ω q w = β • b := by
    intro x
    by_cases hx : unitAt ξ x ϖ
    · exact ⟨0, 0, 0, ⊤, 0, 0, fun h => absurd hx h⟩
    obtain ⟨U₀, hU₀, H₀⟩ := hE x hx
    obtain ⟨v, w, T, U, hU, hl⟩ := exists_loc hA hB hx hU₀ H₀
    have hxx := hl x hU hx
    obtain ⟨α₀, β₀, h2, h3⟩ := hcoef x
    have m1 : exteriorPower.ιMulti Ω p v ∈ A.wedge p x :=
      Submodule.subset_span ⟨v, fun i => hxx.mem_a i, rfl⟩
    have m2 : exteriorPower.ιMulti Ω q w ∈ B.wedge q x :=
      Submodule.subset_span ⟨w, fun i => hxx.mem_b i, rfl⟩
    rw [h2] at m1
    rw [h3] at m2
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 m1
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 m2
    refine ⟨v, w, T, U, (r : Ω) * α₀, (s : Ω) * β₀, fun _ => ⟨hU, hl, ?_, ?_⟩⟩
    · rw [← hr, mul_smul]; rfl
    · rw [← hs, mul_smul]; rfl
  choose v w T U α β hD using H
  refine ⟨fun x => (α x / β x) / frameDet (Mat (J x) (v x)) (T x), fun x hx => ⟨U x, (hD x hx).1, fun y hy hy' => ?_⟩⟩
  haveI := EigSplit.isLocalRing_regAt y
  have Lx := (hD x hx).2.1 y hy hy'
  have Ly := (hD y hy').2.1 y (hD y hy').1 hy'
  have gx := hFr y trivial (v x) (w x) (α x) (β x) Lx.fa Lx.fb (hD x hx).2.2.1 (hD x hx).2.2.2
  have gy := hFr y trivial (v y) (w y) (α y) (β y) Ly.fa Ly.fb (hD y hy').2.2.1 (hD y hy').2.2.2
  obtain ⟨m, n, c, hc, e1, e2, e3⟩ := Lx.compare Ly h0 (hϖ y) hy'
  have hαy : α y ≠ 0 := fun h => gy.1 (by simp [h])
  have hβx : β x ≠ 0 := fun h => gx.1 (by simp [h])
  have f1 : α x = m * α y := by
    rw [(hD x hx).2.2.1, (hD y hy').2.2.1, smul_smul] at e1
    exact smul_left_injective Ω ha e1
  have f2 : β y = n * β x := by
    rw [(hD x hx).2.2.2, (hD y hy').2.2.2, smul_smul] at e2
    exact smul_left_injective Ω hb e2
  exact final_field (hϖ y) hy' gy.1 gx.2 gx.1 (Lx.unit h0 (hϖ y) hy') (Ly.unit h0 (hϖ y) hy') hc e3 f1 f2

end Main

end GlobalTheory.CompanionTheory.Ar.Flat.DddTriv
