import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterWtAnti
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge
import Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices
import Formalism.PolynomialDimension.MultinomialDepth.FockGaussComparisonHolds

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS)
open Formalism.L2.G.Model.TS

def kapFl (p k : ℕ) {S : Type} [Fintype S] (d : S → ℕ) : ℕ := ∑ s, k * Nat.log p (d s)

def MultDiv (O : Type) [CommRing O] (p κ : ℕ) {S : Type} [Fintype S] {k : ℕ} (d : S → ℕ) : Prop :=
  ∀ α : S × Fin k →₀ ℕ, (∀ s, multideg α s = d s) →
    (((∏ s, (d s).factorial : ℕ) : ℕ) : O) ∣ (p : O) ^ κ * ((expFact α : ℕ) : O)

theorem mem_scale {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
    [IsScalarTower O Kf X] {c : Kf} {M : Submodule O X} {x : X} : x ∈ scale c M ↔ ∃ y ∈ M, c • y = x := by
  unfold scale
  rw [Submodule.mem_map]
  rfl

section Contra

variable {S : Type} [Fintype S] [DecidableEq S] {R : Type} [CommRing R] {k : ℕ}

theorem fock_eq_fockR {τ : Type} (F G : MvPolynomial τ R) : fock F G = fockR F G := rfl

theorem Lin_X (N : S → Matrix (Fin k) (Fin k) R) (v : S × Fin k) :
    Lin N (X v) = ∑ b : Fin k, C (N v.1 v.2 b) * X (v.1, b) := by
  simp [Lin]

theorem Lin_coeff_zero (N : S → Matrix (Fin k) (Fin k) R) (h : MvPolynomial (S × Fin k) R) :
    coeff 0 (Lin N h) = coeff 0 h := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [Lin]
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | mul_X p v hp =>
    have e1 : coeff 0 (p * X v) = 0 := by
      rw [← constantCoeff_eq]; simp
    have e2 : coeff 0 (Lin N (p * X v)) = 0 := by
      rw [map_mul, Lin_X, ← constantCoeff_eq]; simp
    rw [e1, e2]

theorem Lin_chain (N : S → Matrix (Fin k) (Fin k) R) (s : S) (b : Fin k) (h : MvPolynomial (S × Fin k) R) :
    pderiv (s, b) (Lin N h) = ∑ a : Fin k, N s a b • Lin N (pderiv (s, a) h) := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a => simp [Lin]
  | add p q hp hq => simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    obtain ⟨t, c⟩ := v
    have hL : pderiv (s, b) (∑ d : Fin k, C (N t c d) * X (t, d) : MvPolynomial (S × Fin k) R)
        = if t = s then C (N t c b) else 0 := by
      rw [map_sum]
      simp only [pderiv_C_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [eq_comm]
      · have hts' : ¬ s = t := fun h => hts h.symm
        simp [hts, hts']
    have hR : ∑ a : Fin k, N s a b • (Lin N p * Lin N (pderiv (s, a) (X (t, c))))
        = Lin N p * (if t = s then C (N t c b) else 0) := by
      simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [apply_ite, Finset.sum_ite_eq, smul_eq_C_mul, mul_comm]
      · have hts' : ¬ s = t := fun h => hts h.symm
        simp [hts, hts']
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, Lin_X, hL, hp]
    simp only [smul_add, Finset.sum_add_distrib]
    rw [hR]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm]

theorem fockR_Lin (N : S → Matrix (Fin k) (Fin k) R) (P : MvPolynomial (S × Fin k) R) :
    ∀ Q : MvPolynomial (S × Fin k) R, fockR (Lin N P) Q = fockR P (Lin (fun s => (N s).transpose) Q) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro Q
    have h1 : Lin N (C a : MvPolynomial (S × Fin k) R) = C a := by simp [Lin]
    rw [h1, C_apply, tsact_monomial_left, tsact_monomial_left, Lin_coeff_zero]
  | add p q hp hq =>
    intro Q
    rw [map_add, tsact_add_left, tsact_add_left, hp, hq]
  | mul_X p v hp =>
    intro Q
    rw [map_mul, Lin_X, Finset.mul_sum, tsact_sum_left, tsact_X_mul, Lin_chain, tsact_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : Lin N p * (C (N v.1 v.2 b) * X (v.1, b)) = N v.1 v.2 b • (Lin N p * X (v.1, b)) := by
      rw [smul_eq_C_mul]; ring
    rw [e, tsact_smul_left, tsact_X_mul, hp, tsact_smul_right, Matrix.transpose_apply]

theorem fockR_Lin_dual (A B : S → Matrix (Fin k) (Fin k) R) (h : ∀ s, B s * (A s).transpose = 1)
    (P Q : MvPolynomial (S × Fin k) R) : fockR (Lin A P) (Lin B Q) = fockR P Q := by
  rw [fockR_Lin, Lin_comp]
  simp only [h]
  rw [Lin_one]

end Contra

theorem Aa_dual {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose)⁻¹ * (Aa vec M⁻¹).transpose = 1 := by
  have hMi : IsUnit (M⁻¹).det := by rw [Matrix.det_nonsing_inv]; exact hM.ringInverse
  have hMt : IsUnit ((M⁻¹).transpose).det := by rw [Matrix.det_transpose]; exact hMi
  cases vec
  · simp only [Aa, Bool.false_eq_true, if_false]
    rw [Matrix.nonsing_inv_nonsing_inv _ hMt, Matrix.nonsing_inv_nonsing_inv _ hM, Matrix.transpose_transpose,
      Matrix.transpose_transpose, Matrix.nonsing_inv_mul _ hM]
  · simp only [Aa, if_true]
    exact Matrix.nonsing_inv_mul _ hMt

theorem multDiv_kapFl (O : Type) [CommRing O] [IsLocalRing O] (p : ℕ) [hp : Fact p.Prime]
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) {S : Type} [Fintype S] {k : ℕ} (d : S → ℕ) :
    MultDiv O p (kapFl p k d) (k := k) d := by
  intro α hα

  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : S, ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  set Mn : ℕ := ∏ s : S, Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) with hMn
  have h3 : (∏ s, (d s).factorial) = Mn * expFact α := by
    rw [h2, hMn, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : Mn ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have h4 : padicValNat p Mn ≤ kapFl p k d := by
    rw [hMn, Formalism.CountingSumsFrames.fock_val_prod p _ _ (fun s _ => (Nat.multinomial_pos _ _).ne')]
    unfold kapFl
    refine Finset.sum_le_sum fun s _ => ?_
    have := Formalism.CountingSumsFrames.fock_mult_val_le p (fun c : Fin k => α (s, c)) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at this
    have e : ∑ c : Fin k, α (s, c) = d s := hα s
    rw [e] at this
    exact this

  have hdv : p ^ padicValNat p Mn ∣ Mn := pow_padicValNat_dvd
  have hnd : ¬ p ^ (padicValNat p Mn + 1) ∣ Mn := pow_succ_padicValNat_not_dvd hMn0
  generalize padicValNat p Mn = v at h4 hdv hnd
  obtain ⟨u, hu⟩ := hdv
  have hpu : ¬ p ∣ u := by
    intro hd
    apply hnd
    rw [hu, pow_succ]
    exact Nat.mul_dvd_mul_left _ hd
  have huO : IsUnit ((u : ℕ) : O) := by
    have hco : Nat.Coprime u p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpu).symm
    by_contra hnu
    have hm : ((u : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have hb := Nat.gcd_eq_gcd_ab u p
    rw [hco] at hb
    have h5 : (1 : O) = (u : O) * ((Nat.gcdA u p : ℤ) : O) + (p : O) * ((Nat.gcdB u p : ℤ) : O) := by
      have := congrArg (fun z : ℤ => (z : O)) hb
      push_cast at this
      exact this
    have h6 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [h5]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm) (Ideal.mul_mem_right _ _ hpO)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h6)
  obtain ⟨uu, huu⟩ := huO
  refine ⟨(p : O) ^ (kapFl p k d - v) * (↑uu⁻¹ : O), ?_⟩
  rw [h3, hu]
  push_cast
  rw [← huu]
  have e1 : (p : O) ^ kapFl p k d = (p : O) ^ v * (p : O) ^ (kapFl p k d - v) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e1]
  have e2 : (uu : O) * (↑uu⁻¹ : O) = 1 := Units.mul_inv uu
  linear_combination (-(p : O) ^ v * (p : O) ^ (kapFl p k d - v) * (expFact α : O)) * e2

def fockL {τ K : Type} [CommRing K] (Q : MvPolynomial τ K) : MvPolynomial τ K →ₗ[K] K where
  toFun P := fockR P Q
  map_add' a b := tsact_add_left a b Q
  map_smul' c a := by simpa using tsact_smul_left c a Q

theorem fockR_add_right {τ K : Type} [CommRing K] (g f f' : MvPolynomial τ K) :
    fockR g (f + f') = fockR g f + fockR g f' := by
  rw [tsact_symm, tsact_add_left, tsact_symm f, tsact_symm f']

section Pair

variable {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] {S : Type} [Fintype S] [DecidableEq S] {m : ℕ}

def LatM (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {S : Type} [Fintype S] {m : ℕ} (vec : S → Bool)
    (d : S → ℕ) (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) :
    Submodule O (MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat O Kf (fun s => nablaLTw O Kf m (letterWt m (d s) (vec s)) (M s))

theorem exists_thK (Kf : Type) [Field Kf] {S : Type} [Fintype S] [DecidableEq S] {m : ℕ} (hm : 1 ≤ m) (vec : S → Bool)
    (d : S → ℕ) :
    ∃ thK : ↥(Pol Kf (ι := S) (m + 1) d) ≃ₗ[Kf] ↥(VS Kf m vec d),
      ∀ P, ((thK P : ↥(VS Kf m vec d)) : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) =
        Th0 Kf m vec (P : MvPolynomial (S × Fin (m + 1)) Kf) := by
  let f : ↥(Pol Kf (ι := S) (m + 1) d) →ₗ[Kf] ↥(VS Kf m vec d) :=
    LinearMap.codRestrict (VS Kf m vec d)
      ((Th0 Kf m vec).toLinearMap.comp (Pol Kf (ι := S) (m + 1) d).subtype)
      (fun P => (mem_tens_dw Kf m hm vec d _).2 ⟨P.1, P.2, rfl⟩)
  have hinj : Function.Injective f := by
    intro P Q hPQ
    apply Subtype.ext
    exact Th0_inj Kf m hm vec d _ _ P.2 Q.2 (congrArg Subtype.val hPQ)
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ VS Kf m vec d := y.2
    obtain ⟨F, hF, hyF⟩ := (mem_tens_dw Kf m hm vec d _).1 hy
    exact ⟨⟨F, hF⟩, Subtype.ext hyF.symm⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun P => rfl⟩

variable {vec : S → Bool} {d : S → ℕ} (thK : ↥(Pol Kf (ι := S) (m + 1) d) ≃ₗ[Kf] ↥(VS Kf m vec d))

def TY (c : Kf) : ↥(VS Kf m vec d) →ₗ[Kf] Module.Dual Kf ↥(VS Kf m vec d) where
  toFun y := c • ((fockL ((thK.symm y : ↥(Pol Kf (ι := S) (m + 1) d)) :
      MvPolynomial (S × Fin (m + 1)) Kf)).comp
    ((Pol Kf (ι := S) (m + 1) d).subtype.comp thK.symm.toLinearMap))
  map_add' y y' := by
    ext u
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply, fockL, LinearMap.coe_mk,
      AddHom.coe_mk, map_add, Submodule.coe_add, smul_eq_mul]
    rw [fockR_add_right, mul_add]
  map_smul' a y := by
    ext u
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, fockL, LinearMap.coe_mk, AddHom.coe_mk, map_smul,
      Submodule.coe_smul, smul_eq_mul, RingHom.id_apply]
    rw [tsact_smul_right]
    ring

theorem TY_apply (c : Kf) (P Q : ↥(Pol Kf (ι := S) (m + 1) d)) :
    TY thK c (thK Q) (thK P) = c * fockR (P : MvPolynomial (S × Fin (m + 1)) Kf)
      (Q : MvPolynomial (S × Fin (m + 1)) Kf) := by
  simp [TY, fockL]

theorem int_pair (p κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d) (G : MvPolynomial (S × Fin (m + 1)) O)
    (hG : G ∈ Pol O (m + 1) d) (E : MvPolynomial (S × Fin (m + 1)) O) :
    ∃ z : O, ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) *
      fockR (map (algebraMap O Kf) G) (map (algebraMap O Kf) E) = algebraMap O Kf z := by
  by_cases hD : (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf) = 0
  · exact ⟨0, by rw [hD, div_zero, zero_mul, map_zero]⟩
  have hdvd : (((∏ s, (d s).factorial : ℕ) : ℕ) : O) ∣ (p : O) ^ κ * fockR G E := by
    unfold fockR
    rw [Finset.mul_sum]
    apply Finset.dvd_sum
    intro α hα
    obtain ⟨q, hq⟩ := hMD α (mem_Pol.1 hG α hα)
    have hq' : (p : O) ^ κ * ((∏ k ∈ α.support, (α k).factorial : ℕ) : O) =
        (((∏ s, (d s).factorial : ℕ) : ℕ) : O) * q := hq
    exact ⟨coeff α G * coeff α E * q, by linear_combination (coeff α G * coeff α E) * hq'⟩
  obtain ⟨z, hz⟩ := hdvd
  refine ⟨z, ?_⟩
  rw [fockR_map, div_mul_eq_mul_div, div_eq_iff hD]
  have := congrArg (algebraMap O Kf) hz
  simp only [map_mul, map_pow, map_natCast] at this
  rw [this]
  ring

theorem sandwich (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(VS Kf m vec d)) : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m vec (P : MvPolynomial (S × Fin (m + 1)) Kf))
    (p κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (u y : ↥(VS Kf m vec d))
    (hu : (u : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ LatM O vec d M)
    (hy : (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ LatM O vec d (fun s => ((M s)⁻¹).transpose)) :
    TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y u ∈ Set.range (algebraMap O Kf) := by
  have hMt : ∀ s, IsUnit (((M s)⁻¹).transpose).det := by
    intro s
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv]
    exact (hM s).ringInverse
  obtain ⟨G, hG, hu'⟩ := (mem_tens_nabla O Kf m hm vec d M hM _).1 hu
  obtain ⟨G', hG', hy'⟩ := (mem_tens_nabla O Kf m hm vec d _ hMt _).1 hy
  let P : ↥(Pol Kf (ι := S) (m + 1) d) :=
    ⟨Lin (fun s => Aa (vec s) (M s)⁻¹) (map (algebraMap O Kf) G), Lin_Pol _ _ (map_Pol _ G hG)⟩
  let Q : ↥(Pol Kf (ι := S) (m + 1) d) :=
    ⟨Lin (fun s => Aa (vec s) (((M s)⁻¹).transpose)⁻¹) (map (algebraMap O Kf) G'), Lin_Pol _ _ (map_Pol _ G' hG')⟩
  have eu : u = thK P := Subtype.ext (by rw [hthK, hu'])
  have ey : y = thK Q := Subtype.ext (by rw [hthK, hy'])
  rw [eu, ey, TY_apply]
  show _ * fockR (Lin _ _) (Lin _ _) ∈ _
  rw [fockR_Lin_dual _ _ (fun s => Aa_dual (vec s) (M s) (hM s))]
  obtain ⟨z, hz⟩ := int_pair (Kf := Kf) p κ hMD G hG G'
  exact ⟨z, hz.symm⟩

end Pair

end Formalism.MainNotions.ColumnSystems.Pf.TF
