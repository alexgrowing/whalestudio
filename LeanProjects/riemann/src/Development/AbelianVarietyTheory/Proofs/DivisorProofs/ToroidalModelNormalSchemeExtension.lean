import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusCyclotomicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveModuleRankGenericSpread
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliTangentFrameBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisIntegerAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectorEigenDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionOnModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartSectionBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat.GrMinor

open Matrix GlobalTheory.ArLieBase.MaxMinor

theorem pow_mem_span_minors {R : Type} [CommRing R] [IsDomain R] {g M r : ℕ} {D c : R}
    {P : Matrix (Fin g) (Fin g) R} (hD : D ≠ 0) (hP : P * P = D • P)
    (hr : (P.map (algebraMap R (FractionRing R))).rank = r) {X : Matrix (Fin g) (Fin M) R}
    {Y : Matrix (Fin M) (Fin g) R} (h : X * Y = c • P) :
    (c * D) ^ r ∈ Ideal.span (Set.range fun q : (Fin r → Fin M) × (Fin r → Fin g) => (Y.submatrix q.1 q.2).det) := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (pow_mem_span_principal D P hD hP hr)
  rw [mul_pow, ← ha, Finset.mul_sum]
  refine Ideal.sum_mem _ fun q _ => ?_
  have : c ^ r * (a q • (P.submatrix q q).det) = a q * ((X * Y).submatrix q q).det := by
    rw [h, show (c • P).submatrix q q = c • P.submatrix q q from rfl, Matrix.det_smul, Fintype.card_fin, smul_eq_mul]
    ring
  rw [this]
  exact Ideal.mul_mem_left _ _ (minor_mul_mem X Y q q)

theorem dvd_of_mem_span {R ι : Type} [CommRing R] {f : ι → R} {d x : R} (h : ∀ i, d ∣ f i)
    (hx : x ∈ Ideal.span (Set.range f)) : d ∣ x := by
  rw [← Ideal.mem_span_singleton]
  refine (Ideal.span_le.2 ?_ : Ideal.span (Set.range f) ≤ Ideal.span {d}) hx
  rintro _ ⟨i, rfl⟩
  exact Ideal.mem_span_singleton.2 (h i)

theorem split_of_minor {R : Type} [CommRing R] [IsDomain R] {g M r : ℕ} {D N : R}
    {P : Matrix (Fin g) (Fin g) R} (H : Matrix (Fin M) (Fin g) R) (hD : D ≠ 0) (hN : N ≠ 0) (hP : P * P = D • P)
    (hr : (P.map (algebraMap R (FractionRing R))).rank = r) (I : Fin r → Fin M) (K : Fin r → Fin g)
    (hdiv : ∀ I', ((H * P).submatrix I K).det ∣ ((H * P).submatrix I' K).det)
    (hNd : ((H * P).submatrix I K).det ∣ N) :
    ∃ (U : Matrix (Fin g) (Fin r) R) (C : Matrix (Fin M) (Fin r) R), P * U = D • U ∧
      H.submatrix I id * U = N • (1 : Matrix (Fin r) (Fin r) R) ∧ U * H.submatrix I id * P = N • P ∧
      H * P = C * (H.submatrix I id * P) ∧ C.submatrix I id = 1 := by
  classical
  set B : Matrix (Fin r) (Fin r) R := (H * P).submatrix I K with hB
  obtain ⟨cc, hcc⟩ := hNd
  have hIP : H.submatrix I id * P.submatrix id K = B := by
    ext i a; simp [hB, Matrix.mul_apply]
  have hHP : H * P.submatrix id K = (H * P).submatrix id K := by
    ext i a; simp [Matrix.mul_apply]
  have hPP : P * P.submatrix id K = D • P.submatrix id K := by
    have : P * P.submatrix id K = (P * P).submatrix id K := by ext i a; simp [Matrix.mul_apply]
    rw [this, hP]; rfl
  set U : Matrix (Fin g) (Fin r) R := P.submatrix id K * (cc • B.adjugate) with hU
  have hIU : H.submatrix I id * U = N • (1 : Matrix (Fin r) (Fin r) R) := by
    rw [hU, ← Matrix.mul_assoc, hIP, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm, ← hcc]
  have hPU : P * U = D • U := by
    rw [hU, ← Matrix.mul_assoc, hPP, Matrix.smul_mul]
  have hUIP : U * H.submatrix I id * P = N • P := by
    have hinj := IsFractionRing.injective R (FractionRing R)
    set φ := algebraMap R (FractionRing R) with hφ
    have h1 : P.map φ * P.map φ = φ D • P.map φ := by
      rw [← map_mul_rect φ, hP]; ext i j; simp
    have h2 : P.map φ * U.map φ = φ D • U.map φ := by
      rw [← map_mul_rect φ, hPU]; ext i j; simp
    have h3 : (H.submatrix I id).map φ * U.map φ = φ N • (1 : Matrix (Fin r) (Fin r) _) := by
      rw [← map_mul_rect φ, hIU]; ext i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have := mul_mul_eq_smul_of_field (FractionRing R) g r (φ D) (φ N) (P.map φ)
      (U.map φ) ((H.submatrix I id).map φ) ((map_ne_zero_iff _ hinj).2 hD) ((map_ne_zero_iff _ hinj).2 hN) h1 hr h2 h3
    apply Matrix.map_injective hinj
    show (U * H.submatrix I id * P).map φ = (N • P).map φ
    rw [map_mul_rect φ, map_mul_rect φ, this]; ext i j; simp
  have hupd : ∀ j i, B.updateRow i (fun a => (H * P) j (K a)) = (H * P).submatrix (Function.update I i j) K := by
    intro j i
    ext i' a
    by_cases h' : i' = i
    · subst h'; simp [Matrix.updateRow_apply]
    · simp [Matrix.updateRow_apply, h', hB]
  have hdi : ∀ j i, ∃ a, (B.updateRow i (fun a => (H * P) j (K a))).det = B.det * a := fun j i => by
    rw [hupd]; exact hdiv _
  choose a ha using hdi
  have hadj : ∀ y : Fin r → R, Matrix.vecMul y B.adjugate = fun i => (B.updateRow i y).det := by
    intro y
    funext i
    rw [← Matrix.mulVec_transpose, Matrix.adjugate_transpose, ← Matrix.cramer_eq_adjugate_mulVec,
      Matrix.cramer_apply, Matrix.updateCol_transpose, Matrix.det_transpose]
  have hHU : H * U = N • Matrix.of a := by
    rw [hU, ← Matrix.mul_assoc, hHP, Matrix.mul_smul]
    ext j i
    have := congrFun (hadj fun a => (H * P) j (K a)) i
    rw [ha] at this
    have e : ((H * P).submatrix id K * B.adjugate) j i = B.det * a j i := this
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, e, hcc]
    ring
  refine ⟨U, Matrix.of a, hPU, hIU, hUIP, ?_, ?_⟩
  · apply smul_right_injective _ hN
    show N • (H * P) = N • (Matrix.of a * (H.submatrix I id * P))
    rw [← Matrix.smul_mul N (Matrix.of a), ← hHU, ← Matrix.mul_smul, ← hUIP]
    simp only [Matrix.mul_assoc]
  · apply smul_right_injective _ hN
    show N • (Matrix.of a).submatrix I id = N • (1 : Matrix (Fin r) (Fin r) R)
    rw [← hIU, show N • (Matrix.of a).submatrix I id = (N • Matrix.of a).submatrix I id from rfl, ← hHU]
    ext i k; simp [Matrix.mul_apply]

def mnr {R : Type} [CommRing R] {g M s : ℕ} (H : Matrix (Fin M) (Fin g) R) (Q : Matrix (Fin g) (Fin g) R)
    (p : (Fin s → Fin M) × (Fin s → Fin g)) : R := ((H * Q).submatrix p.1 p.2).det

def red {R : Type} [CommRing R] {g M s : ℕ} (H : Matrix (Fin M) (Fin g) R) (Q : Matrix (Fin g) (Fin g) R)
    (p : (Fin s → Fin M) × (Fin s → Fin g)) : Matrix (Fin M) (Fin g) R :=
  mnr H Q p • H - (H * Q).submatrix id p.2 * ((H * Q).submatrix p.1 p.2).adjugate * H.submatrix p.1 id

def fam {R : Type} [CommRing R] {g M : ℕ} (s r : ℕ) (H : Matrix (Fin M) (Fin g) R) (P Q : Matrix (Fin g) (Fin g) R)
    (k : ((Fin s → Fin M) × (Fin s → Fin g)) × ((Fin s → Fin M) × (Fin s → Fin g)) ×
      ((Fin r → Fin M) × (Fin r → Fin g))) : R :=
  mnr H Q k.1 * mnr H Q k.2.1 * mnr (red H Q k.1) P k.2.2

section Map
variable {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') {g M s r : ℕ}

theorem mnr_map (H : Matrix (Fin M) (Fin g) R) (Q : Matrix (Fin g) (Fin g) R)
    (p : (Fin s → Fin M) × (Fin s → Fin g)) : ψ (mnr H Q p) = mnr (H.map ψ) (Q.map ψ) p := by
  rw [mnr, mnr, RingHom.map_det, ← map_mul_rect]
  rfl

theorem red_map (H : Matrix (Fin M) (Fin g) R) (Q : Matrix (Fin g) (Fin g) R)
    (p : (Fin s → Fin M) × (Fin s → Fin g)) : (red H Q p).map ψ = red (H.map ψ) (Q.map ψ) p := by
  have := RingHom.map_adjugate ψ ((H * Q).submatrix p.1 p.2)
  simp only [RingHom.mapMatrix_apply] at this
  rw [red, red, Matrix.map_sub _ (map_sub ψ), map_mul_rect, map_mul_rect, this, ← mnr_map, ← map_mul_rect ψ H Q]
  congr 1
  ext i j; simp

theorem fam_map (H : Matrix (Fin M) (Fin g) R) (P Q : Matrix (Fin g) (Fin g) R) (k) :
    ψ (fam s r H P Q k) = fam s r (H.map ψ) (P.map ψ) (Q.map ψ) k := by
  rw [fam, fam, map_mul, map_mul, mnr_map, mnr_map, mnr_map, red_map]

end Map

theorem red_eq {R : Type} [CommRing R] {g M s : ℕ} {H : Matrix (Fin M) (Fin g) R} {Q : Matrix (Fin g) (Fin g) R}
    {C : Matrix (Fin M) (Fin s) R} {J : Fin s → Fin M} (h : H * Q = C * (H.submatrix J id * Q))
    (p : (Fin s → Fin M) × (Fin s → Fin g)) :
    red H Q p = mnr H Q (J, p.2) • ((C.submatrix p.1 id).det • (H - C * H.submatrix J id) -
      C * (C.submatrix p.1 id).adjugate * (H - C * H.submatrix J id).submatrix p.1 id) := by
  set Wk : Matrix (Fin s) (Fin s) R := (H * Q).submatrix J p.2 with hW
  have hWk : (H.submatrix J id * Q).submatrix id p.2 = Wk := by ext i j; simp [hW, Matrix.mul_apply]
  have h1 : (H * Q).submatrix id p.2 = C * Wk := by
    rw [h, ← hWk]; ext i j; simp [Matrix.mul_apply]
  have h2 : (H * Q).submatrix p.1 p.2 = C.submatrix p.1 id * Wk := by
    rw [h, ← hWk]; ext i j; simp [Matrix.mul_apply]
  have h3 : (H - C * H.submatrix J id).submatrix p.1 id =
      H.submatrix p.1 id - C.submatrix p.1 id * H.submatrix J id := by
    ext i j; simp [Matrix.mul_apply]
  have h4 : C * Wk * (Wk.adjugate * (C.submatrix p.1 id).adjugate) = Wk.det • (C * (C.submatrix p.1 id).adjugate) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Wk, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  have h5 : C * (C.submatrix p.1 id).adjugate * (C.submatrix p.1 id * H.submatrix J id) =
      (C.submatrix p.1 id).det • (C * H.submatrix J id) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (C.submatrix p.1 id), Matrix.adjugate_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul]
  rw [red, mnr, mnr, h1, h2, h3, Matrix.adjugate_mul_distrib, h4, Matrix.mul_sub, h5, Matrix.det_mul,
    Matrix.smul_mul]
  show _ = Wk.det • _
  module

section Domain

variable {R : Type} [CommRing R] [IsDomain R] {g M s r : ℕ} {D n : R} {H : Matrix (Fin M) (Fin g) R}
  {P Q : Matrix (Fin g) (Fin g) R} {Cm : Matrix (Fin g) (Fin M) R}

theorem pow_mem_mnr (hD : D ≠ 0) (hQ : Q * Q = D • Q) (hs : (Q.map (algebraMap R (FractionRing R))).rank = s)
    (hC : Cm * H = n • (1 : Matrix (Fin g) (Fin g) R)) :
    (n * D) ^ s ∈ Ideal.span (Set.range fun p : (Fin s → Fin M) × (Fin s → Fin g) => mnr H Q p) :=
  pow_mem_span_minors hD hQ hs (X := Cm) (by rw [← Matrix.mul_assoc, hC, Matrix.smul_mul, Matrix.one_mul])

theorem pow_mem_red (hD : D ≠ 0) (hP : P * P = D • P) (hr : (P.map (algebraMap R (FractionRing R))).rank = r)
    (hPQ : P * Q = 0) (hC : Cm * H = n • (1 : Matrix (Fin g) (Fin g) R)) (p : (Fin s → Fin M) × (Fin s → Fin g)) :
    (mnr H Q p * (n * D * D)) ^ r ∈
      Ideal.span (Set.range fun q : (Fin r → Fin M) × (Fin r → Fin g) => mnr (red H Q p) P q) := by
  have h0 : P * Cm * (H * Q).submatrix id p.2 = 0 := by
    have : P * Cm * (H * Q).submatrix id p.2 = (P * Cm * (H * Q)).submatrix id p.2 := by
      ext i j; simp [Matrix.mul_apply]
    rw [this, Matrix.mul_assoc, ← Matrix.mul_assoc Cm, hC, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hPQ,
      smul_zero]
    rfl
  have := pow_mem_span_minors hD hP hr (X := P * Cm) (Y := red H Q p * P) (c := mnr H Q p * (n * D)) (by
    rw [← Matrix.mul_assoc, red, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
      Matrix.zero_mul, sub_zero, Matrix.mul_smul, Matrix.mul_assoc P, hC, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.smul_mul, hP, smul_smul, smul_smul, mul_assoc])
  rwa [mul_assoc] at this

theorem mem_radical_fam (hD : D ≠ 0) (hP : P * P = D • P) (hr : (P.map (algebraMap R (FractionRing R))).rank = r)
    (hQ : Q * Q = D • Q) (hs : (Q.map (algebraMap R (FractionRing R))).rank = s)
    (hPQ : P * Q = 0) (hC : Cm * H = n • (1 : Matrix (Fin g) (Fin g) R)) :
    n * D * D ∈ (Ideal.span (Set.range (fam s r H P Q))).radical := by
  have h1 : ∀ p : (Fin s → Fin M) × (Fin s → Fin g),
      mnr H Q p * (n * D * D) ∈ (Ideal.span (Set.range (fam s r H P Q))).radical := by
    intro p
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (pow_mem_red hD hP hr hPQ hC p)
    refine ⟨r + 2, ?_⟩
    have : (mnr H Q p * (n * D * D)) ^ (r + 2) = ∑ q, (a q * (n * D * D) ^ 2) * fam s r H P Q (p, p, q) := by
      rw [pow_add, ← ha, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [fam, smul_eq_mul]
      ring
    rw [this]
    exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (pow_mem_mnr hD hQ hs hC)
  refine Ideal.mem_radical_of_pow_mem (m := s + 1) ?_
  have : (n * D * D) ^ (s + 1) = ∑ p, (a p * D ^ s) * (mnr H Q p * (n * D * D)) := by
    rw [pow_succ, mul_pow (n * D), ← ha, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [smul_eq_mul]
    ring
  rw [this]
  exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (h1 q)

theorem split_of_fam (hD : D ≠ 0) (hn : n ≠ 0) (hP : P * P = D • P)
    (hr : (P.map (algebraMap R (FractionRing R))).rank = r)
    (hQ : Q * Q = D • Q) (hs : (Q.map (algebraMap R (FractionRing R))).rank = s)
    (hPQ : P * Q = 0) (hC : Cm * H = n • (1 : Matrix (Fin g) (Fin g) R))
    (k) (hk : ∀ k', fam s r H P Q k ∣ fam s r H P Q k') :
    ∃ (J : Fin s → Fin M) (U₁ : Matrix (Fin g) (Fin s) R) (C : Matrix (Fin M) (Fin s) R) (I : Fin r → Fin M)
      (U : Matrix (Fin g) (Fin r) R) (C₂ : Matrix (Fin M) (Fin r) R),
      Q * U₁ = D • U₁ ∧ H.submatrix J id * U₁ = (n * D) ^ s • (1 : Matrix (Fin s) (Fin s) R) ∧
      H * Q = C * (H.submatrix J id * Q) ∧ P * U = D • U ∧
      (H - C * H.submatrix J id).submatrix I id * U = (n * D * D) ^ r • (1 : Matrix (Fin r) (Fin r) R) ∧
      U * (H - C * H.submatrix J id).submatrix I id * P = (n * D * D) ^ r • P ∧
      (H - C * H.submatrix J id) * P = C₂ * ((H - C * H.submatrix J id).submatrix I id * P) := by
  classical
  obtain ⟨p, p', q⟩ := k
  have h0 : fam s r H P Q (p, p', q) ≠ 0 := by
    obtain ⟨m, hm⟩ := mem_radical_fam hD hP hr hQ hs hPQ hC
    intro h
    have := dvd_of_mem_span hk hm
    rw [h, zero_dvd_iff] at this
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero hn hD) hD) this
  have ha : mnr H Q p ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h0)
  have ha' : mnr H Q p' ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h0)
  have hb : mnr (red H Q p) P q ≠ 0 := right_ne_zero_of_mul h0
  have hsp : ∀ p₀ : (Fin s → Fin M) × (Fin s → Fin g), (∀ p₁ : (Fin s → Fin M) × (Fin s → Fin g),
      mnr H Q p₀ ∣ mnr H Q p₁) → ∃ (U₁ : Matrix (Fin g) (Fin s) R) (C : Matrix (Fin M) (Fin s) R),
      Q * U₁ = D • U₁ ∧ H.submatrix p₀.1 id * U₁ = (n * D) ^ s • (1 : Matrix (Fin s) (Fin s) R) ∧
      H * Q = C * (H.submatrix p₀.1 id * Q) ∧ red H Q p₀ = mnr H Q p₀ • (H - C * H.submatrix p₀.1 id) := by
    intro p₀ h
    obtain ⟨U₁, C, e₁, e₂, -, e₄, e₅⟩ := split_of_minor H hD (pow_ne_zero s (mul_ne_zero hn hD)) hQ hs p₀.1 p₀.2
      (fun I' => h (I', p₀.2)) (dvd_of_mem_span h (pow_mem_mnr hD hQ hs hC))
    refine ⟨U₁, C, e₁, e₂, e₄, ?_⟩
    have h3 : (H - C * H.submatrix p₀.1 id).submatrix p₀.1 id =
        H.submatrix p₀.1 id - C.submatrix p₀.1 id * H.submatrix p₀.1 id := by
      ext i j; simp [Matrix.mul_apply]
    rw [red_eq e₄ p₀, h3, e₅]
    simp
  have h1 : ∀ p₁, mnr H Q p' ∣ mnr H Q p₁ := fun p₁ =>
    (mul_dvd_mul_iff_left ha).1 ((mul_dvd_mul_iff_right hb).1 (hk (p, p₁, q)))
  have h2 : mnr H Q p ∣ mnr H Q p' := by
    obtain ⟨-, C, -, -, e₄, e₅⟩ := hsp p' h1
    obtain ⟨e, he⟩ := h1 (p'.1, p.2)
    have h3 : ∃ Γ : Matrix (Fin M) (Fin M) R, red H Q p * P = Γ * (red H Q p' * P) := by
      refine ⟨e • ((C.submatrix p.1 id).det • 1 - C * (C.submatrix p.1 id).adjugate *
        (1 : Matrix (Fin M) (Fin M) R).submatrix p.1 id), ?_⟩
      have h4 : ∀ X : Matrix (Fin M) (Fin g) R,
          (1 : Matrix (Fin M) (Fin M) R).submatrix p.1 id * X = X.submatrix p.1 id := fun X => by
        ext i j; simp [Matrix.mul_apply, Matrix.one_apply]
      rw [← Matrix.mul_assoc, e₅, red_eq e₄ p, he, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul e,
        Matrix.sub_mul _ _ (H - _), Matrix.mul_assoc (C * _), h4, Matrix.smul_mul _ 1, Matrix.one_mul, smul_smul,
        Matrix.smul_mul]
    obtain ⟨Γ, hΓ⟩ := h3
    have h5 : mnr (red H Q p) P q ∈
        Ideal.span (Set.range fun q' : (Fin r → Fin M) × (Fin r → Fin g) => mnr (red H Q p') P q') := by
      rw [mnr, hΓ]
      exact minor_mul_mem Γ _ q.1 q.2
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h5
    have h6 : fam s r H P Q (p, p', q) ∣ mnr H Q p' * mnr H Q p' * mnr (red H Q p) P q := by
      rw [← ha, Finset.mul_sum]
      refine Finset.dvd_sum fun q' _ => ?_
      rw [smul_eq_mul, mul_left_comm]
      exact (hk (p', p', q')).mul_left _
    exact (mul_dvd_mul_iff_right ha').1 ((mul_dvd_mul_iff_right hb).1 h6)
  obtain ⟨U₁, C, e₁, e₂, e₄, e₅⟩ := hsp p fun p₁ => h2.trans (h1 p₁)
  have h7 : ∀ q' : (Fin r → Fin M) × (Fin r → Fin g),
      mnr (red H Q p) P q' = mnr H Q p ^ r * mnr (H - C * H.submatrix p.1 id) P q' := fun q' => by
    rw [mnr, e₅, Matrix.smul_mul, Matrix.submatrix_smul, Pi.smul_apply, Pi.smul_apply, Matrix.det_smul,
      Fintype.card_fin]
    rfl
  have h8 : ∀ q', mnr (red H Q p) P q ∣ mnr (red H Q p) P q' := fun q' =>
    (mul_dvd_mul_iff_left (mul_ne_zero ha ha')).1 (hk (p, p', q'))
  have h9 := dvd_of_mem_span h8 (pow_mem_red hD hP hr hPQ hC p)
  rw [h7, mul_pow, mul_dvd_mul_iff_left (pow_ne_zero r ha)] at h9
  obtain ⟨U, C₂, f₁, f₂, f₃, f₄, -⟩ := split_of_minor (H - C * H.submatrix p.1 id) hD
    (pow_ne_zero r (mul_ne_zero (mul_ne_zero hn hD) hD)) hP hr q.1 q.2
    (fun I' => by
      have := h8 (I', q.2)
      rwa [h7, h7, mul_dvd_mul_iff_left (pow_ne_zero r ha)] at this) h9
  exact ⟨p.1, U₁, C, q.1, U, C₂, e₁, e₂, e₄, f₁, f₂, f₃, f₄⟩

end Domain

theorem integral_iff {K : Type} [Field K] (O : Subring K) {g M s r : ℕ} {D N₁ : K} (hD : D ≠ 0) (hN : N₁ ≠ 0)
    {H : Matrix (Fin M) (Fin g) K} {P Q : Matrix (Fin g) (Fin g) K} {J : Fin s → Fin M}
    {U₁ : Matrix (Fin g) (Fin s) K} {C : Matrix (Fin M) (Fin s) K} {I : Fin r → Fin M} {C₂ : Matrix (Fin M) (Fin r) K}
    (hC : ∀ i j, C i j ∈ O) (hC₂ : ∀ i j, C₂ i j ∈ O) (e₁ : Q * U₁ = D • U₁)
    (e₂ : H.submatrix J id * U₁ = N₁ • (1 : Matrix (Fin s) (Fin s) K)) (e₃ : H * Q = C * (H.submatrix J id * Q))
    (e₄ : (H - C * H.submatrix J id) * P = C₂ * ((H - C * H.submatrix J id).submatrix I id * P))
    {w : Fin g → K} (hw : P *ᵥ w = D • w) :
    (∀ i, ((H - C * H.submatrix J id).submatrix I id *ᵥ w) i ∈ O) ↔
      ∃ v, Q *ᵥ v = D • v ∧ ∀ j, (H *ᵥ (w + v)) j ∈ O := by
  have hv0 : ∀ v, Q *ᵥ v = D • v → (H - C * H.submatrix J id) *ᵥ v = 0 := fun v hv => by
    apply smul_right_injective _ hD
    show D • (H - C * H.submatrix J id) *ᵥ v = D • (0 : Fin M → K)
    rw [← Matrix.mulVec_smul, ← hv, Matrix.mulVec_mulVec, Matrix.sub_mul, e₃, Matrix.mul_assoc, sub_self,
      Matrix.zero_mulVec, smul_zero]
  have hint : ∀ {m : ℕ} (A : Matrix (Fin M) (Fin m) K) (y : Fin m → K), (∀ i j, A i j ∈ O) → (∀ i, y i ∈ O) →
      ∀ j, (A *ᵥ y) j ∈ O := fun A y hA hy j => O.sum_mem (t := Finset.univ) fun i _ => O.mul_mem (hA j i) (hy i)
  constructor
  · intro h
    have hw' : (H - C * H.submatrix J id) *ᵥ w = C₂ *ᵥ ((H - C * H.submatrix J id).submatrix I id *ᵥ w) := by
      apply smul_right_injective _ hD
      show D • (H - C * H.submatrix J id) *ᵥ w = D • C₂ *ᵥ ((H - C * H.submatrix J id).submatrix I id *ᵥ w)
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hw, Matrix.mulVec_mulVec, e₄]
      simp only [Matrix.mulVec_mulVec]
    have hv : Q *ᵥ (U₁ *ᵥ (-N₁⁻¹ • H.submatrix J id *ᵥ w)) = D • (U₁ *ᵥ (-N₁⁻¹ • H.submatrix J id *ᵥ w)) := by
      rw [Matrix.mulVec_mulVec, e₁, Matrix.smul_mulVec]
    refine ⟨_, hv, fun j => ?_⟩
    have hJ : H.submatrix J id *ᵥ (w + U₁ *ᵥ (-N₁⁻¹ • H.submatrix J id *ᵥ w)) = 0 := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec _ _ U₁, e₂, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
        mul_neg, mul_inv_cancel₀ hN, neg_smul, one_smul, add_neg_cancel]
    have : H *ᵥ (w + U₁ *ᵥ (-N₁⁻¹ • H.submatrix J id *ᵥ w)) =
        (H - C * H.submatrix J id) *ᵥ (w + U₁ *ᵥ (-N₁⁻¹ • H.submatrix J id *ᵥ w)) := by
      rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec _ C, hJ, Matrix.mulVec_zero, sub_zero]
    rw [this, Matrix.mulVec_add, hv0 _ hv, add_zero, hw']
    exact hint _ _ hC₂ h j
  · rintro ⟨v, hv, h⟩ i
    have : (H - C * H.submatrix J id) *ᵥ w = H *ᵥ (w + v) - C *ᵥ (H.submatrix J id *ᵥ (w + v)) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.sub_mulVec, Matrix.mulVec_add, hv0 v hv, add_zero]
    show ((H - C * H.submatrix J id) *ᵥ w) (I i) ∈ O
    rw [this]
    exact O.sub_mem (h _) (hint C _ hC (fun i => h (J i)) _)

theorem exists_rank {R : Type} [CommRing R] [IsDomain R] [CharZero R] {g D : ℕ} (hD : D ≠ 0)
    {Q : Matrix (Fin g) (Fin g) R} (hQ : Q * Q = (D : R) • Q) :
    ∃ s : ℕ, ∀ (K : Type) [Field K] [CharZero K] (ψ : R →+* K), (Q.map ψ).rank = s := by
  have key : ∀ (K : Type) [Field K] [CharZero K] (ψ : R →+* K), ψ Q.trace = (D : K) * ((Q.map ψ).rank : K) := by
    intro K _ _ ψ
    have hDK : (D : K) ≠ 0 := Nat.cast_ne_zero.2 hD
    have hQK : Q.map ψ * Q.map ψ = (D : K) • Q.map ψ := by
      rw [← map_mul_rect, hQ]; ext i j; simp
    set f : Module.End K (Fin g → K) := (D : K)⁻¹ • Matrix.toLin' (Q.map ψ) with hf
    have hE : IsIdempotentElem f := by
      show f * f = f
      rw [hf, smul_mul_assoc, mul_smul_comm, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hQK, map_smul, smul_smul,
        smul_smul]
      congr 1
      field_simp
    have h1 := (LinearMap.IsIdempotentElem.isProj_range f hE).trace
    rw [hf, LinearMap.range_smul _ _ (inv_ne_zero hDK), map_smul, Matrix.trace_toLin'_eq, smul_eq_mul] at h1
    have h2 : ψ Q.trace = (Q.map ψ).trace := by simp [Matrix.trace]
    rw [h2, show ((Q.map ψ).rank : K) = (D : K)⁻¹ * (Q.map ψ).trace from h1.symm, mul_inv_cancel_left₀ hDK]
  have hinj := IsFractionRing.injective R (FractionRing R)
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap hinj
  refine ⟨(Q.map (algebraMap R (FractionRing R))).rank, fun K _ _ ψ => ?_⟩
  have h1 : Q.trace = (D : R) * ((Q.map (algebraMap R (FractionRing R))).rank : R) :=
    hinj (by rw [key]; simp)
  have h2 := key K ψ
  rw [h1, map_mul, map_natCast, map_natCast] at h2
  exact Nat.cast_injective (mul_left_cancel₀ (Nat.cast_ne_zero.2 hD : (D : K) ≠ 0) h2).symm

theorem exists_family {R : Type} [CommRing R] [IsDomain R] [CharZero R] {g M r D : ℕ} {P Q : Matrix (Fin g) (Fin g) R}
    (h : Fin M → Fin g → R) (hD : D ≠ 0) (hP : P * P = (D : R) • P) (hQ : Q * Q = (D : R) • Q) (hPQ : P * Q = 0)
    (hr : ∀ (K : Type) [Field K] [CharZero K] (ψ : R →+* K), (P.map ψ).rank = r)
    (hspan : ∃ n : ℕ, n ≠ 0 ∧ ∀ i, Pi.single i (n : R) ∈ Submodule.span R (Set.range h)) :
    ∃ (n m : ℕ) (A : Fin m → R), n ≠ 0 ∧ (n : R) ∈ (Ideal.span (Set.range A)).radical ∧
      ∀ (R' : Type) [CommRing R'] [IsDomain R'] [CharZero R'] (ψ : R →+* R'), (∃ k, ∀ k', ψ (A k) ∣ ψ (A k')) →
        ∃ (N : ℕ) (U : Matrix (Fin g) (Fin r) R') (Hi : Matrix (Fin r) (Fin g) R'), N ≠ 0 ∧
          P.map ψ * U = (D : R') • U ∧ Hi * U = (N : R') • (1 : Matrix (Fin r) (Fin r) R') ∧
          U * Hi * P.map ψ = (N : R') • P.map ψ ∧
          ∀ (K : Type) [Field K] [CharZero K] (O : Subring K) (χ : R' →+* O) (w : Fin g → K),
            P.map ((O.subtype.comp χ).comp ψ) *ᵥ w = (D : K) • w →
            ((∀ i, (Hi.map (O.subtype.comp χ) *ᵥ w) i ∈ O) ↔
              ∃ v, Q.map ((O.subtype.comp χ).comp ψ) *ᵥ v = (D : K) • v ∧
                ∀ j, ((Matrix.of h).map ((O.subtype.comp χ).comp ψ) *ᵥ (w + v)) j ∈ O) := by
  classical
  obtain ⟨n₀, hn₀, hspan⟩ := hspan
  obtain ⟨s, hs⟩ := exists_rank hD hQ
  set H : Matrix (Fin M) (Fin g) R := Matrix.of h with hH
  have hc : ∀ i, ∃ c : Fin M → R, ∑ j, c j • h j = Pi.single i (n₀ : R) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (hspan i)
  choose c hc using hc
  set Cm : Matrix (Fin g) (Fin M) R := Matrix.of c with hCm
  have hCH : Cm * H = (n₀ : R) • (1 : Matrix (Fin g) (Fin g) R) := by
    ext i k
    have := congrFun (hc i) k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, hCm, hH, Matrix.of_apply, this, Matrix.smul_apply, Matrix.one_apply,
      Pi.single_apply, smul_eq_mul]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik, Ne.symm hik]
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  let e := Fintype.equivFin (((Fin s → Fin M) × (Fin s → Fin g)) × ((Fin s → Fin M) × (Fin s → Fin g)) ×
      ((Fin r → Fin M) × (Fin r → Fin g)))
  have hsm : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {a b : ℕ} (x : A) (X : Matrix (Fin a) (Fin b) A),
      (x • X).map f = f x • X.map f := fun f _ _ x X => by ext i j; simp
  have h1 : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {a : ℕ},
      (1 : Matrix (Fin a) (Fin a) A).map f = 1 := fun f _ => Matrix.map_one _ (map_zero f) (map_one f)
  refine ⟨n₀ * D * D, _, fam s r H P Q ∘ e.symm, mul_ne_zero (mul_ne_zero hn₀ hD) hD, ?_, ?_⟩
  · rw [e.symm.surjective.range_comp]
    push_cast
    exact mem_radical_fam (Nat.cast_ne_zero.2 hD) hP (hr _ _) hQ (hs _ _) hPQ hCH
  intro R' _ _ _ ψ ⟨k, hk⟩
  haveI : CharZero (FractionRing R') := charZero_of_injective_algebraMap (IsFractionRing.injective R' _)
  obtain ⟨J, U₁, C, I, U, C₂, e₁, e₂, e₃, f₁, f₂, f₃, f₄⟩ := split_of_fam (s := s) (r := r) (D := (D : R'))
    (n := (n₀ : R')) (H := H.map ψ) (P := P.map ψ) (Q := Q.map ψ) (Cm := Cm.map ψ) (Nat.cast_ne_zero.2 hD)
    (Nat.cast_ne_zero.2 hn₀) (by rw [← map_mul_rect, hP, hsm, map_natCast])
    (by rw [Matrix.map_map, ← RingHom.coe_comp]; exact hr _ _) (by rw [← map_mul_rect, hQ, hsm, map_natCast])
    (by rw [Matrix.map_map, ← RingHom.coe_comp]; exact hs _ _)
    (by rw [← map_mul_rect, hPQ, Matrix.map_zero _ (map_zero ψ)])
    (by rw [← map_mul_rect, hCH, hsm, map_natCast, h1]) (e.symm k) (fun k' => by
      have := hk (e k')
      simpa only [Function.comp_apply, Equiv.symm_apply_apply, fam_map] using this)
  refine ⟨(n₀ * D * D) ^ r, U, _, pow_ne_zero _ (mul_ne_zero (mul_ne_zero hn₀ hD) hD), f₁, by push_cast; exact f₂,
    by push_cast; exact f₃, fun K _ _ O χ w hw => ?_⟩
  set θ : R' →+* K := O.subtype.comp χ with hθ
  have hm : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) R), X.map (θ.comp ψ) = (X.map ψ).map θ := fun X => rfl
  have hH' : (H.map ψ - C * (H.map ψ).submatrix J id).map θ =
      (H.map ψ).map θ - C.map θ * ((H.map ψ).map θ).submatrix J id := by
    rw [Matrix.map_sub _ (map_sub θ), map_mul_rect]
    rfl
  have := integral_iff O (D := (D : K)) (N₁ := ((n₀ : K) * D) ^ s) (Nat.cast_ne_zero.2 hD)
    (pow_ne_zero _ (mul_ne_zero (Nat.cast_ne_zero.2 hn₀) (Nat.cast_ne_zero.2 hD)))
    (H := (H.map ψ).map θ) (P := (P.map ψ).map θ) (Q := (Q.map ψ).map θ) (J := J) (U₁ := U₁.map θ) (C := C.map θ)
    (I := I) (C₂ := C₂.map θ) (fun i j => (χ (C i j)).2) (fun i j => (χ (C₂ i j)).2)
    (by rw [← map_mul_rect, e₁, hsm, map_natCast])
    (by
      rw [show ((H.map ψ).map θ).submatrix J id = ((H.map ψ).submatrix J id).map θ from rfl, ← map_mul_rect, e₂, hsm, h1]
      simp)
    (by
      rw [show ((H.map ψ).map θ).submatrix J id = ((H.map ψ).submatrix J id).map θ from rfl, ← map_mul_rect, e₃,
        map_mul_rect, map_mul_rect])
    (by
      rw [← hH', ← map_mul_rect, f₄, map_mul_rect, map_mul_rect]
      rfl) hw
  rw [← hH'] at this
  exact this

end GlobalTheory.TwoLat.GrMinor

namespace GlobalTheory.TwoLat

open GlobalTheory.EigProjPoly in

theorem exists_orth_eigProj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) {R : Type} [CommRing R]
    (κ : 𝓞 c.F →+* R) {g : ℕ} (ρ : 𝓞 E →+* Matrix (Fin g) (Fin g) R) :
    ∃ (D : ℕ) (P : (E →+* ℂ) → Matrix (Fin g) (Fin g) R), D ≠ 0 ∧ (∀ τ, P τ * P τ = (D : R) • P τ) ∧
      (∀ σ τ, σ ≠ τ → P σ * P τ = 0) ∧ ∀ (τ : E →+* ℂ) (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K),
        ψ.comp κ = φ.comp (algebraMap (𝓞 c.F) c.F) → ∀ cf : Fin g → K,
          ((∀ a, ((ρ a).map ψ).mulVec cf = φ (embK c τ a) • cf) ↔ ((P τ).map ψ).mulVec cf = (D : K) • cf) := by
  classical
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have hint : ∀ σ : E →+* ℂ, IsIntegral ℤ (embK c σ α) := fun σ =>
    (NumberField.RingOfIntegers.isIntegral α).map (embK c σ).toIntAlgHom
  let aO : (E →+* ℂ) → 𝓞 c.F := fun σ => ⟨embK c σ α, hint σ⟩
  have haO : ∀ σ, algebraMap (𝓞 c.F) c.F (aO σ) = embK c σ α := fun _ => rfl
  have hinjO : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective (𝓞 c.F) c.F
  let fO : Polynomial (𝓞 c.F) := f.map (Int.castRingHom (𝓞 c.F))
  have hfO : fO = ∏ σ, (Polynomial.X - Polynomial.C (aO σ)) := by
    apply Polynomial.map_injective _ hinjO
    rw [Polynomial.map_map, show (algebraMap (𝓞 c.F) c.F).comp (Int.castRingHom (𝓞 c.F)) = Int.castRingHom c.F
      from RingHom.ext_int _ _, hfs, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, haO]
  let δO : (E →+* ℂ) → 𝓞 c.F := fun τ => ∏ σ ∈ Finset.univ.erase τ, (aO τ - aO σ)
  have hδO : ∀ τ, δO τ ≠ 0 := fun τ => by
    refine Finset.prod_ne_zero_iff.2 fun σ hσ h => (Finset.ne_of_mem_erase hσ) ?_
    have h' : embK c τ α = embK c σ α := by rw [← haO, ← haO, sub_eq_zero.1 h]
    exact (hinj h').symm
  have hδ : ∀ τ, (algebraMap (𝓞 c.F) c.F (δO τ)) ≠ 0 := fun τ h => hδO τ (hinjO (h.trans (map_zero _).symm))
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun τ => (algebraMap (𝓞 c.F) c.F (δO τ))⁻¹ : Finset c.F)
  let c1 : (E →+* ℂ) → 𝓞 c.F := fun τ =>
    ⟨y • (algebraMap (𝓞 c.F) c.F (δO τ))⁻¹, hyi _ (Finset.mem_image_of_mem _ (Finset.mem_univ τ))⟩
  have hc1 : ∀ τ, c1 τ * δO τ = (y : 𝓞 c.F) := fun τ => by
    apply hinjO
    rw [map_mul, map_intCast]
    change y • (algebraMap (𝓞 c.F) c.F (δO τ))⁻¹ * _ = _
    rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ (hδ τ), mul_one]
  let c0 : (E →+* ℂ) → 𝓞 c.F := fun τ => c1 τ * (y.sign : 𝓞 c.F)
  let D : ℕ := y.natAbs
  have hc0 : ∀ τ, c0 τ * δO τ = (D : 𝓞 c.F) := fun τ => by
    rw [mul_right_comm, hc1, ← Int.cast_mul, Int.mul_sign_self, Int.cast_natCast]
  let Q : (E →+* ℂ) → Polynomial (𝓞 c.F) := fun τ =>
    Polynomial.C (c0 τ) * ∏ σ ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (aO σ))
  have hF : ∀ τ, (Polynomial.X - Polynomial.C (aO τ)) * Q τ = Polynomial.C (c0 τ) * fO := fun τ => by
    rw [hfO, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ)]
    ring
  have hD : ∀ τ, (Q τ).eval (aO τ) = (D : 𝓞 c.F) := fun τ => by
    rw [← hc0 τ]
    simp only [Q, δO, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X]
  have h0 : ∀ σ τ, σ ≠ τ → (Q σ).eval (aO τ) = 0 := fun σ τ hne => by
    simp only [Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X]
    rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ τ⟩) (sub_self _), mul_zero]
  have hfz : ∀ {S : Type} [CommRing S] (θ : 𝓞 c.F →+* S) (ρ' : 𝓞 E →+* Matrix (Fin g) (Fin g) S),
      Polynomial.aeval (ρ' α) (fO.map θ) = 0 := by
    intro S _ θ ρ'
    rw [Polynomial.map_map, show θ.comp (Int.castRingHom (𝓞 c.F)) = algebraMap ℤ S from RingHom.ext_int _ _,
      Polynomial.aeval_map_algebraMap]
    exact (Polynomial.aeval_algHom_apply ρ'.toIntAlgHom α f).trans (by rw [hf, map_zero])
  refine ⟨D, fun τ => Polynomial.aeval (ρ α) ((Q τ).map κ), Int.natAbs_ne_zero.2 hy0, fun τ => ?_,
    fun σ τ hne => ?_, ?_⟩
  · rw [(core κ (ρ α) (Q τ) fO (aO τ) (c0 τ) D (hF τ) (hD τ) (hfz κ ρ)).2, map_natCast]
  · rw [aeval_mul_eig _ _ _ (core κ (ρ α) (Q τ) fO (aO τ) (c0 τ) D (hF τ) (hD τ) (hfz κ ρ)).1, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, h0 σ τ hne, map_zero, zero_smul]
  · intro τ K _ ψ φ hcomp cf
    let φ' : 𝓞 c.F →+* K := φ.comp (algebraMap (𝓞 c.F) c.F)
    let ρ' : 𝓞 E →+* Matrix (Fin g) (Fin g) K := ψ.mapMatrix.comp ρ
    have hPm : (Polynomial.aeval (ρ α) ((Q τ).map κ)).map ψ = Polynomial.aeval (ρ' α) ((Q τ).map φ') := by
      rw [aeval_map_matrix, Polynomial.map_map, hcomp]; rfl
    obtain ⟨h1, -⟩ := core φ' (ρ' α) (Q τ) fO (aO τ) (c0 τ) D (hF τ) (hD τ) (hfz φ' ρ')
    have hl : φ' (aO τ) = φ (embK c τ α) := rfl
    have hDK : φ' (D : 𝓞 c.F) = (D : K) := map_natCast _ _
    beta_reduce
    rw [hPm]
    constructor
    · intro h
      have := aeval_mulVec_eig (ρ' α) cf (φ' (aO τ)) (h α) ((Q τ).map φ')
      rw [this, Polynomial.eval_map, Polynomial.eval₂_at_apply, hD, hDK]
    · intro h
      have hu : IsUnit (D : K) := by
        rw [← hDK]
        exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Int.natAbs_ne_zero.2 hy0) : ((D : c.F)) ≠ 0)).map φ
      have hα : (ρ' α).mulVec cf = φ (embK c τ α) • cf := by
        have e : (ρ' α).mulVec ((Polynomial.aeval (ρ' α) ((Q τ).map φ')).mulVec cf) =
            (φ' (aO τ) • Polynomial.aeval (ρ' α) ((Q τ).map φ')).mulVec cf := by
          rw [Matrix.mulVec_mulVec, h1]
        rw [h, Matrix.mulVec_smul, Matrix.smul_mulVec, h, smul_comm (φ' (aO τ)), hl] at e
        exact (hu.smul_left_cancel).1 e
      letI : Algebra c.F K := φ.toAlgebra
      let ρL : 𝓞 E →+* Module.End K (Fin g → K) := (Matrix.toLinAlgEquiv' (R := K) (n := Fin g)).toRingHom.comp ρ'
      have := ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha (K := c.F) ρL (embK c) α hN τ (m := cf) (by
        change Matrix.toLinAlgEquiv' (ρ' α) cf = _
        rw [Matrix.toLinAlgEquiv'_apply]; exact hα)
      intro a
      have e := this a
      change Matrix.toLinAlgEquiv' (ρ' a) cf = _ at e
      rw [Matrix.toLinAlgEquiv'_apply] at e
      exact e

end GlobalTheory.TwoLat

namespace GlobalTheory.TwoLat

open GlobalTheory.ShFam.Pad.Guard Matrix

theorem exists_ext_ringOfIntegers (F : Type) [Field F] [NumberField F] (K : Type) [Field K] [CharZero K]
    (χ : 𝓞 F →+* K) : ∃ φ : F →+* K, φ.comp (algebraMap (𝓞 F) F) = χ := by
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have ha0 : (a : F) ≠ 0 := fun h => h0 (RingOfIntegers.coe_eq_zero_iff.1 h)
    obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ ({((a : F))⁻¹} : Finset F)
    let b : 𝓞 F := ⟨y • (a : F)⁻¹, hyi _ (Finset.mem_singleton_self _)⟩
    have hb : ((y : ℤ) : 𝓞 F) = a * b := by
      apply RingOfIntegers.ext
      show ((y : 𝓞 F) : F) = (a : F) * (y • (a : F)⁻¹)
      rw [zsmul_eq_mul, mul_left_comm, mul_inv_cancel₀ ha0, mul_one]
      push_cast
      rfl
    have h2 := congrArg χ hb
    rw [map_intCast, map_mul, ha, zero_mul] at h2
    exact hy0 (Int.cast_eq_zero.1 h2)
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}

theorem exists_orth_isEigProj (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {R : Type} [CommRing R]
    (x : Sp R ⟶ Z.X) {g : ℕ} {e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)} (he : GlobalTheory.LineNorm.IsTanBasis Z.t x e) :
    ∃ (D : ℕ) (P : (E →+* ℂ) → Matrix (Fin g) (Fin g) R), D ≠ 0 ∧ (∀ τ, IsEigProj Z x τ e D (P τ)) ∧
      (∀ σ τ, σ ≠ τ → P σ * P τ = 0) ∧
      ∀ (τ : E →+* ℂ) (K : Type) [Field K] [CharZero K] (ψ : R →+* K), ((P τ).map ψ).rank = Dw.mult τ := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.TanActMat.exists_actMatrix_bc E H Z.X Z.t R x g e he
  let κ : 𝓞 c.F →+* R := (Spec.preimage (x ≫ Z.s)).hom
  have hκ : spMap κ = x ≫ Z.s := Spec.map_preimage _
  obtain ⟨D, P, hD, hPP, hO, hP⟩ := exists_orth_eigProj c κ ρ
  have hb := fun {K : Type} [CommRing K] (ψ : R →+* K) => GlobalTheory.HTPres.isTanBasis_map Z.t he ψ
  have hcomp : ∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K),
      spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F)) →
      ψ.comp κ = φ.comp (algebraMap (𝓞 c.F) c.F) := by
    intro K _ ψ φ h
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [← h, ← hκ]
    exact Spec.map_comp _ _
  have heig : ∀ (τ : E →+* ℂ) (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K),
      spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F)) → ∀ (cf : Fin g → K) w,
      IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w →
      (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ ((P τ).map ψ).mulVec cf = (D : K) • cf) := by
    intro τ K _ ψ φ hφ cf w hw
    rw [← hP τ K ψ φ (hcomp K ψ φ hφ) cf]
    have hu := (hb ψ).1
    have ht := comb_tan hu hw
    constructor
    · rintro ⟨-, hE⟩ a
      have h1 := hρ K ψ a cf w hw
      have h2 := comb_smul hu hw (φ (embK c τ a))
      rw [← hE a] at h2
      exact (he.2 K ψ _ (comb_tan hu h1)).unique h1 h2
    · intro h
      refine ⟨ht, fun a => ?_⟩
      have h1 := hρ K ψ a cf w hw
      rw [h a] at h1
      exact comb_unique hu h1 (comb_smul hu hw _)
  refine ⟨D, P, hD, fun τ => ⟨hPP τ, heig τ⟩, hO, ?_⟩
  intro τ K _ _ ψ
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  obtain ⟨φ, hφ⟩ := exists_ext_ringOfIntegers c.F K (ψ.comp κ)
  have hφ' : spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [hφ, ← hκ]
    exact (Spec.map_comp _ _).symm
  obtain ⟨V, hV, hVm⟩ := GlobalTheory.ArLieBase.exists_eig_subspace E H Dw l Xo c Z R x τ g e he K ψ φ hφ'
  have hDK : (D : K) ≠ 0 := Nat.cast_ne_zero.2 hD
  have hPK : (P τ).map ψ * (P τ).map ψ = (D : K) • (P τ).map ψ := by
    rw [← Matrix.map_mul, hPP]
    ext i j
    simp
  have hV' : V = LinearMap.range ((P τ).map ψ).mulVecLin := by
    ext cf
    obtain ⟨w, -, hw⟩ := exists_comb (hb ψ).1 cf
    rw [← hVm cf w hw, heig τ K ψ φ hφ' cf w hw]
    constructor
    · intro h
      refine ⟨(D : K)⁻¹ • cf, ?_⟩
      simp [Matrix.mulVec_smul, h, smul_smul, hDK]
    · rintro ⟨y, rfl⟩
      show ((P τ).map ψ).mulVec (((P τ).map ψ).mulVec y) = (D : K) • ((P τ).map ψ).mulVec y
      rw [Matrix.mulVec_mulVec, hPK, Matrix.smul_mulVec]
  rw [Matrix.rank, ← hV', hV]

def before (τ : E →+* ℂ) : Finset (E →+* ℂ) :=
  Finset.univ.filter fun σ => Fintype.equivFin (E →+* ℂ) σ < Fintype.equivFin (E →+* ℂ) τ

omit [IsCMField E] in
theorem mem_before {σ τ : E →+* ℂ} :
    σ ∈ before τ ↔ Fintype.equivFin (E →+* ℂ) σ < Fintype.equivFin (E →+* ℂ) τ := by
  simp [before]

theorem sum_mul_of_mem {ι R : Type} [CommRing R] {g : ℕ} {D : R} {P : ι → Matrix (Fin g) (Fin g) R}
    (hP : ∀ τ, P τ * P τ = D • P τ) (hO : ∀ σ τ, σ ≠ τ → P σ * P τ = 0) {T : Finset ι} {τ : ι} (hτ : τ ∈ T) :
    (∑ σ ∈ T, P σ) * P τ = D • P τ := by
  rw [Finset.sum_mul, Finset.sum_eq_single τ (fun σ _ h => hO σ τ h) (fun h => absurd hτ h), hP]

variable {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

theorem inGr_iff {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) {g : ℕ} {e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)}
    (he : GlobalTheory.LineNorm.IsTanBasis Z.t x e) {D : ℕ} {P : (E →+* ℂ) → Matrix (Fin g) (Fin g) R} (hD : D ≠ 0)
    (hP : ∀ τ, IsEigProj Z x τ e D (P τ)) (hO : ∀ σ τ, σ ≠ τ → P σ * P τ = 0) {K : Type} [Field K] [CharZero K]
    (ψ : R →+* K) (φ : c.F →+* K) (hφ : spMap ψ ≫ x ≫ Z.s = spMap (φ.comp β))
    {Λ : Set (Sp (DualNumber K) ⟶ Z.t.G.left)} {L : (Fin g → K) → Prop}
    (hΛ : ∀ cf w, IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w → (w ∈ Λ ↔ L cf))
    (τ : E →+* ℂ) {cf : Fin g → K} {w : Sp (DualNumber K) ⟶ Z.t.G.left}
    (hw : IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w) :
    InGr Z φ (spMap ψ ≫ x) Λ τ w ↔ ∃ v, (∑ σ ∈ before τ, P σ).map ψ *ᵥ v = (D : K) • v ∧ L (cf + v) := by
  classical
  have hu := (GlobalTheory.HTPres.isTanBasis_map Z.t he ψ).1
  have hDK : (D : K) ≠ 0 := Nat.cast_ne_zero.2 hD
  have hsm : ∀ σ, ((D : R) • P σ).map ψ = (D : K) • (P σ).map ψ := fun σ => by ext i j; simp
  have hlin : ∀ {m : ℕ} (v : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)) (cv : Fin m → Fin g → K),
      (∀ i, IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) (cv i) (v i)) → ∀ w',
      IsCombAtG Z.t (spMap ψ ≫ x) (Fin.cons w v : Fin (m + 1) → _) (fun _ => 1) w' →
      IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) (cf + ∑ i, cv i) w' := by
    intro m v cv hv w' hw'
    have := Formalism.L2.Pj.tanLinG _ hu (Fin.cons w v : Fin (m + 1) → _)
      (Matrix.of fun j i => (Fin.cons cf cv : Fin (m + 1) → Fin g → K) i j) (fun _ => 1) w'
      (fun i => by
        refine Fin.cases ?_ (fun i => ?_) i
        · exact hw
        · exact hv i) hw'
    convert this using 1
    funext j
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Finset.sum_apply]
  constructor
  · rintro ⟨m, ρ, v, hv, w', hw'Λ, hw'⟩
    choose cv hcv _ using fun i => he.2 K ψ (v i) (hv i).2.1
    refine ⟨∑ i, cv i, ?_, (hΛ _ _ (hlin v cv hcv w' hw')).1 hw'Λ⟩
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := ((hP (ρ i)).2 K ψ φ hφ _ _ (hcv i)).1 (hv i).2
    apply smul_right_injective _ hDK
    show (D : K) • _ = (D : K) • (D : K) • cv i
    rw [← Matrix.mulVec_smul, ← h1, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      sum_mul_of_mem (fun σ => (hP σ).1) hO (mem_before.2 (hv i).1), hsm, Matrix.smul_mulVec]
  · rintro ⟨y, hy, hL⟩
    let ε := (before τ).equivFin.symm
    let cv : Fin (before τ).card → Fin g → K := fun i => (D : K)⁻¹ • (P (ε i)).map ψ *ᵥ y
    choose v hvt hv using fun i => exists_comb hu (cv i)
    have hsum : ∑ i, cv i = y := by
      rw [← Finset.smul_sum, ε.sum_comp (fun σ => (P σ).map ψ *ᵥ y),
        Finset.sum_coe_sort (before τ) (fun σ => (P σ).map ψ *ᵥ y), ← Matrix.sum_mulVec]
      have : ∑ σ ∈ before τ, (P σ).map ψ = (∑ σ ∈ before τ, P σ).map ψ := (map_sum ψ.mapMatrix _ _).symm
      rw [this, hy, smul_smul, inv_mul_cancel₀ hDK, one_smul]
    obtain ⟨w', -, hw'⟩ := exists_comb (u := (Fin.cons w v : Fin (_ + 1) → _))
      (fun i => by
        refine Fin.cases ?_ (fun i => ?_) i
        · exact comb_tan hu hw
        · exact hvt i) (fun _ => (1 : K))
    refine ⟨_, fun i => ε i, v, fun i => ⟨mem_before.1 (ε i).2, ((hP _).2 K ψ φ hφ _ _ (hv i)).2 ?_⟩, w',
      (hΛ _ _ (hlin v cv hv w' hw')).2 (hsum ▸ hL), hw'⟩
    simp only [cv]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.map_mul, (hP _).1, hsm, Matrix.smul_mulVec, smul_comm]

theorem grBasis_of_split {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ Z.X) (τ : E →+* ℂ)
    {g M r D N : ℕ} {e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)} {h : Fin M → Fin g → R}
    {P : (E →+* ℂ) → Matrix (Fin g) (Fin g) R} {U : Matrix (Fin g) (Fin r) R'} {Hi : Matrix (Fin r) (Fin g) R'}
    (hD : D ≠ 0) (hN : N ≠ 0) (he : GlobalTheory.LineNorm.IsTanBasis Z.t x e) (hP : ∀ τ, IsEigProj Z x τ e D (P τ))
    (hO : ∀ σ τ, σ ≠ τ → P σ * P τ = 0) (hL : LatPres Z.t x (ArIn.ind ∅) (fun _ => 0) e h)
    (s₁ : (P τ).map ψ * U = (D : R') • U) (s₂ : Hi * U = (N : R') • (1 : Matrix (Fin r) (Fin r) R'))
    (s₃ : U * Hi * (P τ).map ψ = (N : R') • (P τ).map ψ)
    (s₄ : ∀ (K : Type) [Field K] [CharZero K] (O : Subring K) (χ : R' →+* O) (w : Fin g → K),
      (P τ).map ((O.subtype.comp χ).comp ψ) *ᵥ w = (D : K) • w →
      ((∀ i, (Hi.map (O.subtype.comp χ) *ᵥ w) i ∈ O) ↔
        ∃ v, (∑ σ ∈ before τ, P σ).map ((O.subtype.comp χ).comp ψ) *ᵥ v = (D : K) • v ∧
          ∀ j, ((Matrix.of h).map ((O.subtype.comp χ).comp ψ) *ᵥ (w + v)) j ∈ O)) :
    GrBasis Z (spMap ψ ≫ x) τ r := by
  have hunit : ∀ {K : Type} [CommRing K] (_ : c.F →+* K) (n : ℕ), n ≠ 0 → ∃ k : K, k * (n : K) = 1 := by
    intro K _ φ n hn
    have hu : IsUnit ((n : ℕ) : K) := by
      simpa using ((Nat.cast_ne_zero.2 hn : ((n : ℕ) : c.F) ≠ 0).isUnit).map φ
    obtain ⟨k, hk⟩ := hu.exists_left_inv
    exact ⟨k, hk⟩
  have hv0 : ∀ k, IsTanAtG Z.t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ e k) :=
    fun k => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ (he.1 k)
  choose u hu using fun i => exists_comb hv0 (fun k => U k i)
  have hbc : ∀ {K : Type} [CommRing K] (ψ₂ : R' →+* K),
      spMap ψ₂ ≫ spMap ψ ≫ x = spMap (ψ₂.comp ψ) ≫ x ∧
      (∀ i, IsCombAtG Z.t (spMap (ψ₂.comp ψ) ≫ x) (fun k => spMap (dualMap (ψ₂.comp ψ)) ≫ e k)
        (fun k => (U.map ψ₂) k i) (spMap (dualMap ψ₂) ≫ u i)) ∧
      (P τ).map (ψ₂.comp ψ) * U.map ψ₂ = (D : K) • U.map ψ₂ ∧
      Hi.map ψ₂ * U.map ψ₂ = (N : K) • 1 ∧
      U.map ψ₂ * Hi.map ψ₂ * (P τ).map (ψ₂.comp ψ) = (N : K) • (P τ).map (ψ₂.comp ψ) := by
    intro K _ ψ₂
    have hx1 : spMap ψ₂ ≫ spMap ψ ≫ x = spMap (ψ₂.comp ψ) ≫ x := by
      rw [← Category.assoc, sp_comp]
    have hPm : (P τ).map (ψ₂.comp ψ) = ((P τ).map ψ).map ψ₂ := by ext; simp
    refine ⟨hx1, fun i => ?_, ?_, ?_, ?_⟩
    · have := GlobalTheory.LatDRFree.comb_map Z.t ψ₂ (hu i).2
      simp only [GlobalTheory.HTPres.bc_bc] at this
      rw [hx1] at this
      exact this
    · rw [hPm, ← Matrix.map_mul, s₁]; ext; simp
    · rw [← Matrix.map_mul, s₂]; ext i j; simp [Matrix.one_apply]; split_ifs <;> simp
    · rw [hPm, ← Matrix.map_mul, ← Matrix.map_mul, s₃]; ext; simp
  refine ⟨N, u, hN, fun K _ ψ₂ φ hφ => ?_, fun p _ ψ₃ φ hφ w hw => ?_⟩
  · obtain ⟨hx1, hc, S1, S2, S3⟩ := hbc ψ₂
    have hφ' : spMap (ψ₂.comp ψ) ≫ x ≫ Z.s = spMap (φ.comp β) := by
      rw [← Category.assoc, ← hx1]; simpa only [Category.assoc] using hφ
    obtain ⟨dk, hd⟩ := hunit φ D hD
    obtain ⟨nk, hn⟩ := hunit φ N hN
    rw [hx1]
    obtain ⟨h1, h2⟩ := split_basis Z x τ he (hP τ) (ψ₂.comp ψ) φ hφ' hd hn S1 S2 S3 hc
    refine ⟨h1, fun w hw => ?_⟩
    obtain ⟨cf, -, -, hA⟩ := h2 w hw
    exact ⟨_, (hA _).2 rfl, fun a ha => (hA a).1 ha⟩
  · obtain ⟨hx1, hc, S1, S2, S3⟩ := hbc ((intO ℂ_[p]).subtype.comp ψ₃)
    have hφ' : spMap (((intO ℂ_[p]).subtype.comp ψ₃).comp ψ) ≫ x ≫ Z.s = spMap (φ.comp β) := by
      rw [← Category.assoc, ← hx1]; simpa only [Category.assoc] using hφ
    obtain ⟨dk, hd⟩ := hunit φ D hD
    obtain ⟨nk, hn⟩ := hunit φ N hN
    obtain ⟨δ, hδ, hlat⟩ := hL.2 p (ψ₃.comp ψ)
    rw [neg_zero, Real.rpow_zero] at hδ
    have hδ0 : δ ≠ 0 := fun h0 => by simp [h0] at hδ
    rw [hx1] at hw ⊢
    obtain ⟨-, h2⟩ := split_basis Z x τ he (hP τ) _ φ hφ' hd hn S1 S2 S3 hc
    obtain ⟨cf, hcf, hE, hA⟩ := h2 w hw
    have hb := (GlobalTheory.HTPres.isTanBasis_map Z.t he (((intO ℂ_[p]).subtype.comp ψ₃).comp ψ)).1
    rw [inGr_iff Z x he hD hP hO _ φ hφ'
      (L := fun y => ∀ j, ((Matrix.of h).map (((intO ℂ_[p]).subtype.comp ψ₃).comp ψ) *ᵥ y) j ∈ intO ℂ_[p])
      (fun y w₁ hw₁ => by
        obtain ⟨w₀, -, hw₀⟩ := exists_comb hb (fun k => δ⁻¹ * y k)
        have h3 := comb_smul hb hw₀ δ
        simp only [mul_inv_cancel_left₀ hδ0] at h3
        rw [comb_unique hb hw₁ h3]
        refine (hlat _ _ hw₀).trans (forall_congr' fun j => ?_)
        have h4 : ∑ i, (((ψ₃.comp ψ) (h j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * (δ⁻¹ * y i) =
            δ⁻¹ * ((Matrix.of h).map (((intO ℂ_[p]).subtype.comp ψ₃).comp ψ) *ᵥ y) j := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
        rw [h4, norm_mul, norm_inv, hδ, inv_one, one_mul]
        rfl) τ hcf, ← s₄ ℂ_[p] (intO ℂ_[p]) ψ₃ cf hE]
    have hNa : ∀ i, (N : ℂ_[p]) * (nk • Hi.map ((intO ℂ_[p]).subtype.comp ψ₃) *ᵥ cf) i =
        (Hi.map ((intO ℂ_[p]).subtype.comp ψ₃) *ᵥ cf) i := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (N : ℂ_[p]) nk, hn, one_mul]
    constructor
    · rintro ⟨a, ha, hca⟩ i
      rw [(hA a).1 hca] at ha
      rw [← hNa]
      exact ha i
    · intro hj
      refine ⟨_, fun i => ?_, (hA _).2 rfl⟩
      rw [hNa]
      exact hj i

theorem exists_grChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {X : Scheme.{0}} [IsIntegral X],
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ (U : X.Opens) [Nonempty U], CharZero Γ(X, U)) → ∀ (ρ : X ⟶ Z.X),
    GlobalTheory.HtGen.SplitK Z.t (K := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ ρ) 1 → ∀ (x : X) (τ : E →+* ℂ),
    ∃ V : X.affineOpens, x ∈ V.1 ∧ ∃ (n m : ℕ) (A : Fin m → Γ(X, V.1)), n ≠ 0 ∧
      (n : Γ(X, V.1)) ∈ (Ideal.span (Set.range A)).radical ∧
      ∀ (R' : Type) [CommRing R'] [IsDomain R'] [CharZero R'] (ψ : Γ(X, V.1) →+* R'), (∃ k, ∀ k', ψ (A k) ∣ ψ (A k')) →
        GlobalTheory.TwoLat.GrBasis Z (spMap ψ ≫ V.2.fromSpec ≫ ρ) τ (Dw.mult τ) := by
  intro E _ _ _ _ H Dw l Xo c Z X _ hn h0 ρ hs x τ
  obtain ⟨V, g, e, hx, he⟩ := GlobalTheory.LineNorm.exists_affine_isTanBasis E H Z.X Z.t X ρ x
  refine ⟨V, hx, ?_⟩
  have : Nonempty V.1 := ⟨⟨x, hx⟩⟩
  have := h0 V.1
  have : IsProper Z.s := projProper _ _ _ Z.proj
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have hsep : Z.X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from Z.s]; infer_instance⟩
  have : IsFractionRing Γ(X, V.1) X.functionField := functionField_isFractionRing_of_isAffineOpen X V.1 V.2
  have : CharZero X.functionField := charZero_of_injective_algebraMap (IsFractionRing.injective Γ(X, V.1) _)
  have : IsIntegrallyClosed Γ(X, V.1) :=
    haveI : GlobalTheory.IsNormalScheme X := ⟨fun x => (hn x).1, fun x => (hn x).2⟩
    GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen V.2
  have hgen : spMap (algebraMap Γ(X, V.1) X.functionField) ≫ V.2.fromSpec ≫ ρ =
      X.fromSpecStalk (genericPoint X) ≫ ρ := by
    rw [← Category.assoc]
    congr 1
    exact V.2.fromSpecStalk_eq_fromSpecStalk (((genericPoint_spec X).mem_open_set_iff V.1.isOpen).2 ⟨x, trivial, hx⟩)
  obtain ⟨M, h, hL⟩ := latPres_of_splitK E H Z.X Z.t hsep ∅ (by simp) Γ(X, V.1) X.functionField (V.2.fromSpec ≫ ρ)
    ⟨1, by rw [Finset.prod_empty]; exact IsPrimitiveRoot.one⟩ (by rw [Finset.prod_empty]; exact hgen ▸ hs) g e he
  obtain ⟨D, P, hD, hP, hO, hrk⟩ := exists_orth_isEigProj Z _ he
  obtain ⟨n, m, A, hn0, hA, hsp⟩ := GrMinor.exists_family (P := P τ) (Q := ∑ σ ∈ before τ, P σ) h hD (hP τ).1
    (by
      rw [Finset.mul_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun σ hσ => sum_mul_of_mem (fun σ => (hP σ).1) hO hσ)
    (by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun σ hσ => hO _ _ fun h => by
        subst h
        exact lt_irrefl _ (mem_before.1 hσ)) (hrk τ) hL.1
  refine ⟨n, m, A, hn0, hA, fun R' _ _ _ ψ hk => ?_⟩
  obtain ⟨N, U, Hi, hN, s₁, s₂, s₃, s₄⟩ := hsp R' ψ hk
  exact grBasis_of_split Z ψ _ τ hD hN he hP hO hL s₁ s₂ s₃ s₄

end GlobalTheory.TwoLat

end
