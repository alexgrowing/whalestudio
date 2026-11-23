import Mathlib
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Alg

variable {k K : Type} [CommRing k] [Field K]

open Classical in

def xiZ (ξ : kˣ →* Kˣ) (a : k) : K := if h : IsUnit a then ((ξ h.unit : Kˣ) : K) else 0

theorem xiZ_unit (ξ : kˣ →* Kˣ) (u : kˣ) : xiZ ξ (u : k) = ((ξ u : Kˣ) : K) := by
  unfold xiZ
  rw [dif_pos u.isUnit, IsUnit.unit_of_val_units]

theorem xiZ_mul (ξ : kˣ →* Kˣ) (a b : k) : xiZ ξ (a * b) = xiZ ξ a * xiZ ξ b := by
  by_cases ha : IsUnit a
  · by_cases hb : IsUnit b
    · obtain ⟨u, rfl⟩ := ha
      obtain ⟨v, rfl⟩ := hb
      rw [← Units.val_mul, xiZ_unit, xiZ_unit, xiZ_unit, map_mul, Units.val_mul]
    · have h : ¬ IsUnit (a * b) := fun h => hb (isUnit_of_mul_isUnit_right h)
      unfold xiZ
      rw [dif_neg h, dif_neg hb, mul_zero]
  · have h : ¬ IsUnit (a * b) := fun h => ha (isUnit_of_mul_isUnit_left h)
    unfold xiZ
    rw [dif_neg h, dif_neg ha, zero_mul]

def LLz (r : ℕ) {a b : ℕ} (M : Matrix (Fin a) (Fin b) k) : Prop := ∀ i j, r ≤ i.1 → j.1 < r → M i j = 0

theorem mul_colA {r a b c : ℕ} (hb : r ≤ b) (P : Matrix (Fin a) (Fin b) k) (Q : Matrix (Fin b) (Fin c) k) (hQ : LLz r Q)
    (i : Fin a) (j : Fin c) (hj : j.1 < r) :
    (P * Q) i j = ∑ s : Fin r, P i (Fin.castLE hb s) * Q (Fin.castLE hb s) j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  have h0 : ∑ s : Fin d, P i (Fin.natAdd r s) * Q (Fin.natAdd r s) j = 0 :=
    Finset.sum_eq_zero fun s _ => by rw [hQ _ _ (by simp) hj, mul_zero]
  rw [h0, add_zero]
  rfl

theorem LLz.mul {r a b c : ℕ} (hb : r ≤ b) {P : Matrix (Fin a) (Fin b) k} {Q : Matrix (Fin b) (Fin c) k} (hP : LLz r P) (hQ : LLz r Q) :
    LLz r (P * Q) := by
  intro i j hi hj
  rw [mul_colA hb P Q hQ i j hj]
  exact Finset.sum_eq_zero fun s _ => by rw [hP _ _ hi (show (Fin.castLE hb s).1 < r from s.2), zero_mul]

theorem tl_mul {r a b c : ℕ} (ha : r ≤ a) (hb : r ≤ b) (hc : r ≤ c) (P : Matrix (Fin a) (Fin b) k) (Q : Matrix (Fin b) (Fin c) k)
    (hQ : LLz r Q) :
    (P * Q).submatrix (Fin.castLE ha) (Fin.castLE hc) =
      P.submatrix (Fin.castLE ha) (Fin.castLE hb) * Q.submatrix (Fin.castLE hb) (Fin.castLE hc) := by
  ext s t
  rw [Matrix.submatrix_apply, mul_colA hb P Q hQ _ _ (show (Fin.castLE hc t).1 < r from t.2), Matrix.mul_apply]
  rfl

open Classical in

def phiZ (ξ : kˣ →* Kˣ) {r a b : ℕ} (ha : r ≤ a) (hb : r ≤ b) (M : Matrix (Fin a) (Fin b) k) : K :=
  if LLz r M then xiZ ξ (M.submatrix (Fin.castLE ha) (Fin.castLE hb)).det else 0

theorem phiZ_law (ξ : kˣ →* Kˣ) {r a b : ℕ} (ha : r ≤ a) (hb : r ≤ b) (A Ai : Matrix (Fin a) (Fin a) k) (B Bi : Matrix (Fin b) (Fin b) k)
    (hA : LLz r A) (hAi : LLz r Ai) (hB : LLz r B) (hBi : LLz r Bi) (h1 : Ai * A = 1) (h2 : B * Bi = 1) (M : Matrix (Fin a) (Fin b) k) :
    phiZ ξ ha hb (A * M * B) = xiZ ξ (A.submatrix (Fin.castLE ha) (Fin.castLE ha)).det *
      xiZ ξ (B.submatrix (Fin.castLE hb) (Fin.castLE hb)).det * phiZ ξ ha hb M := by
  have hiff : LLz r (A * M * B) ↔ LLz r M := by
    constructor
    · intro h
      have e : M = Ai * (A * M * B) * Bi := by
        have e1 : Ai * (A * M * B) * Bi = (Ai * A) * M * (B * Bi) := by simp only [Matrix.mul_assoc]
        rw [e1, h1, h2, Matrix.one_mul, Matrix.mul_one]
      rw [e]
      exact (hAi.mul ha h).mul hb hBi
    · intro h
      exact (hA.mul ha h).mul hb hB
  unfold phiZ
  by_cases h : LLz r M
  · rw [if_pos h, if_pos (hiff.2 h), tl_mul ha hb hb _ _ hB, tl_mul ha ha hb _ _ h, Matrix.det_mul, Matrix.det_mul, xiZ_mul, xiZ_mul]
    ring
  · rw [if_neg h, if_neg (mt hiff.1 h), mul_zero]

theorem det_LLz {r d : ℕ} (A : Matrix (Fin (r + d)) (Fin (r + d)) k) (hA : LLz r A) :
    A.det = (A.submatrix (Fin.castAdd d) (Fin.castAdd d)).det * (A.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
  have e : A.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (A.submatrix (Fin.castAdd d) (Fin.castAdd d)) (A.submatrix (Fin.castAdd d) (Fin.natAdd r)) 0
        (A.submatrix (Fin.natAdd r) (Fin.natAdd r)) := by
    ext (i | i) (j | j)
    · rfl
    · rfl
    · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply]
      exact hA _ _ (by simp) j.2
    · rfl
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv A, e, Matrix.det_fromBlocks_zero₂₁]

def brI {n r d : ℕ} (hn : n = r + d) (s : Fin d) : Fin n := ⟨r + s.1, by have := s.2; omega⟩

theorem scal_law (ξ : kˣ →* Kˣ) {r n n' d d' : ℕ} (hn : n = r + d) (hn' : n' = r + d') (hr : r ≤ n) (hr' : r ≤ n')
    (A Ai : Matrix (Fin n) (Fin n) k) (B C : Matrix (Fin n') (Fin n') k)
    (hA : LLz r A) (hC : LLz r C) (h1 : Ai * A = 1) (h2 : B * C = 1) :
    xiZ ξ⁻¹ B.det * xiZ ξ Ai.det * (xiZ ξ (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).det *
        xiZ ξ (B.submatrix (Fin.castLE hr') (Fin.castLE hr')).det) =
      (xiZ ξ (A.submatrix (brI hn) (brI hn)).det)⁻¹ * xiZ ξ (C.submatrix (brI hn') (brI hn')).det := by
  subst hn
  subst hn'
  have dA := det_LLz A hA
  have dC := det_LLz C hC
  have e1 : Ai.det * A.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
  have e2 : B.det * C.det = 1 := by rw [← Matrix.det_mul, h2, Matrix.det_one]
  have e3 : (B.submatrix (Fin.castLE hr') (Fin.castLE hr')).det * (C.submatrix (Fin.castLE hr') (Fin.castLE hr')).det = 1 := by
    rw [← Matrix.det_mul, ← tl_mul hr' hr' hr' B C hC, h2, Matrix.submatrix_one _ (Fin.castLE_injective hr'), Matrix.det_one]
  have uA : IsUnit A.det := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact e1)
  have uC : IsUnit C.det := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact e2)
  rw [dA] at uA e1
  rw [dC] at uC e2
  obtain ⟨u₁, hu₁⟩ := isUnit_of_mul_isUnit_left uA
  obtain ⟨u₂, hu₂⟩ := isUnit_of_mul_isUnit_right uA
  obtain ⟨v₁, hv₁⟩ := isUnit_of_mul_isUnit_left uC
  obtain ⟨v₂, hv₂⟩ := isUnit_of_mul_isUnit_right uC
  have f1 : (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).det = u₁ := hu₁.symm
  have f2 : (A.submatrix (brI rfl) (brI rfl)).det = u₂ := hu₂.symm
  have f3 : (C.submatrix (Fin.castLE hr') (Fin.castLE hr')).det = v₁ := hv₁.symm
  have f4 : (C.submatrix (brI rfl) (brI rfl)).det = v₂ := hv₂.symm
  rw [← hu₁, ← hu₂, ← Units.val_mul] at e1
  rw [← hv₁, ← hv₂, ← Units.val_mul] at e2
  rw [f3] at e3
  have g1 : Ai.det = ((u₁ * u₂)⁻¹ : kˣ) := Units.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact e1)
  have g2 : B.det = ((v₁ * v₂)⁻¹ : kˣ) := Units.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact e2)
  have g3 : (B.submatrix (Fin.castLE hr') (Fin.castLE hr')).det = (v₁⁻¹ : kˣ) := Units.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact e3)
  rw [g1, g2, g3, f1, f2, f4]
  simp only [xiZ_unit, map_inv, map_mul, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  have n1 : ((ξ u₁ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have n2 : ((ξ u₂ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have n3 : ((ξ v₁ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp

end Alg

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

def redMQ {a b : ℕ} (x : HomE E a b) : Matrix (Fin b) (Fin a) (𝓞 E ⧸ P.asIdeal) := Matrix.of fun l s => redP P (x (Pi.single s 1) l)

theorem intM_iff {a b : ℕ} (x : HomE E a b) :
    (∀ s l, IntAt P (x (Pi.single s 1) l)) ↔ ∀ v ∈ stdAt E a P, x v ∈ stdAt E b P :=
  ⟨fun h _ hv => map_stdAt3 P x h hv, fun h s l => (ciMem_stdAt P _).1 (h _ (ciSingle_mem s)) l⟩

theorem redV_map {a b : ℕ} (x : HomE E a b) (hx : ∀ s l, IntAt P (x (Pi.single s 1) l)) {v : Sp E a} (hv : v ∈ stdAt E a P) :
    redV P (x v) = (redMQ P x).mulVec (redV P v) := by
  classical
  have hv' := (ciMem_stdAt P v).1 hv
  funext l
  have e : x v l = ∑ s, v s * x (Pi.single s 1) l := by
    have h1 : x v = ∑ s, v s • x (Pi.single s 1) := by
      conv_lhs => rw [pi_eq_sum_univ v]
      rw [map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_smul]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [h1, Finset.sum_apply]
    rfl
  show redP P (x v l) = _
  rw [e, redP_sum _ _ fun s _ => (hv' s).mul (hx s l)]
  simp only [Matrix.mulVec, dotProduct, redMQ, Matrix.of_apply, redV]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [reduction_mul (hv' s) (hx s l), mul_comm]

theorem redMQ_of {a b : ℕ} (x : HomE E a b) (H : Matrix (Fin b) (Fin a) (𝓞 E ⧸ P.asIdeal))
    (hred : ∀ v ∈ stdAt E a P, redV P (x v) = H.mulVec (redV P v)) : redMQ P x = H := by
  ext l s
  have h := congrFun (hred _ (ciSingle_mem s)) l
  rw [ciRedV_single] at h
  show redP P (x (Pi.single s 1) l) = _
  unfold redV at h
  rw [h]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem glint_int {n : ℕ} {f : Sp E n ≃ₗ[E] Sp E n} (hf : f ∈ GLint E n P) : ∀ s l, IntAt P (f.toLinearMap (Pi.single s 1) l) :=
  (intM_iff P f.toLinearMap).2 fun v hv => (hf v).2 hv

theorem redMQ_mul_inv {n : ℕ} {f : Sp E n ≃ₗ[E] Sp E n} (hf : f ∈ GLint E n P) :
    redMQ P (f⁻¹ : Sp E n ≃ₗ[E] Sp E n).toLinearMap * redMQ P f.toLinearMap = 1 := by
  have hfi : (f⁻¹ : Sp E n ≃ₗ[E] Sp E n) ∈ GLint E n P := (GLint E n P).inv_mem hf
  have h1 : redMQ P (LinearMap.id : HomE E n n) = redMQ P (f⁻¹ : Sp E n ≃ₗ[E] Sp E n).toLinearMap * redMQ P f.toLinearMap := by
    refine redMQ_of P _ _ fun v hv => ?_
    have a1 : redV P (f v) = (redMQ P f.toLinearMap).mulVec (redV P v) := redV_map P f.toLinearMap (glint_int P hf) hv
    have a2 : redV P ((f⁻¹ : Sp E n ≃ₗ[E] Sp E n) (f v)) = (redMQ P (f⁻¹ : Sp E n ≃ₗ[E] Sp E n).toLinearMap).mulVec (redV P (f v)) :=
      redV_map P (f⁻¹ : Sp E n ≃ₗ[E] Sp E n).toLinearMap (glint_int P hfi) ((hf v).2 hv)
    rw [← Matrix.mulVec_mulVec, ← a1, ← a2]
    show redV P v = redV P (f.symm (f v))
    rw [LinearEquiv.symm_apply_apply]
  rw [← h1]
  refine redMQ_of P _ _ fun v _ => ?_
  rw [Matrix.one_mulVec]
  rfl

theorem redMQ_sandwich {a b : ℕ} {f : Sp E a ≃ₗ[E] Sp E a} (hf : f ∈ GLint E a P) (g : Sp E b ≃ₗ[E] Sp E b)
    (A : Matrix (Fin b) (Fin b) (𝓞 E ⧸ P.asIdeal))
    (hA : ∀ v ∈ stdAt E b P, redV P (g v) = A.mulVec (redV P v))
    (y : HomE E a b) (hy : ∀ s l, IntAt P (y (Pi.single s 1) l)) :
    redMQ P (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap) = A * redMQ P y * redMQ P f.toLinearMap := by
  refine redMQ_of P _ _ fun v hv => ?_
  have h1 : f v ∈ stdAt E a P := (hf v).2 hv
  have h2 : y (f v) ∈ stdAt E b P := map_stdAt3 P y hy h1
  show redV P (g (y (f v))) = _
  rw [hA _ h2, redV_map P y hy h1]
  have h3 : redV P (f v) = (redMQ P f.toLinearMap).mulVec (redV P v) := redV_map P f.toLinearMap (glint_int P hf) hv
  rw [h3, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem intM_sandwich {a b : ℕ} {f : Sp E a ≃ₗ[E] Sp E a} (hf : f ∈ GLint E a P) {g : Sp E b ≃ₗ[E] Sp E b} (hg : g ∈ GLint E b P)
    (y : HomE E a b) :
    (∀ s l, IntAt P ((g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap) (Pi.single s 1) l)) ↔ ∀ s l, IntAt P (y (Pi.single s 1) l) := by
  rw [intM_iff, intM_iff]
  constructor
  · intro h v hv
    have h1 := h (f.symm v) ((hf _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hv))
    have h2 : g (y v) ∈ stdAt E b P := by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h1
    exact (hg _).1 h2
  · intro h v hv
    exact (hg _).2 (h _ ((hf v).2 hv))

theorem redP_detEquiv {n : ℕ} {f : Sp E n ≃ₗ[E] Sp E n} (hf : f ∈ GLint E n P) :
    redP P ((LinearEquiv.det f : Eˣ) : E) = (redMQ P f.toLinearMap).det := by
  have hM : ∀ i j, LinearMap.toMatrix' f.toLinearMap i j = f.toLinearMap (Pi.single j 1) i := by
    intro i j
    simp [LinearMap.toMatrix'_apply]
  have hN : LinearMap.toMatrix' f.toLinearMap = Matrix.of fun i j => f.toLinearMap (Pi.single j 1) i := by
    ext i j
    exact hM i j
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix', hN,
    redP_det (Matrix.of fun i j => f.toLinearMap (Pi.single j 1) i) fun i j => glint_int P hf j i]
  exact congrArg Matrix.det (Matrix.ext fun _ _ => rfl)

variable {P} {K : Type} [Field K]

theorem unitV_eq (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : LocE.unitV χ a = xiZ χ (redP P a) := rfl

open Classical in

theorem phiQ_eq {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ r n' n : ℕ) (hn' : r ≤ n') (hn : r ≤ n) (x : HomE E (n' + 0) (n + 0)) :
    LocE.PhiQ q ξ k₀ r 0 n' 0 n x = if (∀ s l, IntAt P (x (Pi.single s 1) l)) then phiZ ξ hn hn' (redMQ P x) else 0 := by
  have hq0 := ciQ_ne_zero hu
  have hent : ∀ p p' (hp : p < n + 0) (hp' : p' < n' + 0),
      LocE.entB q k₀ 0 n' 0 n 0 0 x p p' = x (Pi.single ⟨p', hp'⟩ 1) ⟨p, hp⟩ := fun p p' hp hp' => entB_inB q k₀ n' n 0 0 x hp hp'
  unfold LocE.PhiQ
  by_cases hI : ∀ s l, IntAt P (x (Pi.single s 1) l)
  · rw [if_pos hI]
    have hC1 : ∀ p p', p < n + 0 → p' < n' + 0 → IntAt P (LocE.entB q k₀ 0 n' 0 n 0 0 x p p') := fun p p' hp hp' => by
      rw [hent p p' hp hp']
      exact hI _ _
    have hC2 : (∀ p p', r ≤ p → p < n + 0 → p' < r → IntAt P (LocE.entB q k₀ 0 n' 0 n 0 0 x p p' / (q : E))) ↔ LLz r (redMQ P x) := by
      constructor
      · intro h i j hi hj
        have h1 := h i.1 j.1 hi i.2 hj
        rw [hent _ _ i.2 j.2] at h1
        exact (ciRed_of_div hq hq0 h1).2
      · intro h p p' hp1 hp2 hp'
        have hp'' : p' < n' + 0 := lt_of_lt_of_le hp' hn'
        rw [hent p p' hp2 hp'']
        exact ciIntAt_div hq hu (hI _ _) (h ⟨p, hp2⟩ ⟨p', hp''⟩ hp1 hp')
    unfold phiZ
    by_cases hL : LLz r (redMQ P x)
    · rw [if_pos ⟨hC1, hC2.2 hL⟩, if_pos hL]
      have hmat : (Matrix.of fun s t : Fin r => LocE.entB q k₀ 0 n' 0 n 0 0 x s.1 t.1) =
          Matrix.of fun s t : Fin r => x (Pi.single (Fin.castLE hn' t) 1) (Fin.castLE hn s) := by
        ext s t
        exact hent _ _ _ _
      rw [hmat, unitV_eq, redP_det (Matrix.of fun s t : Fin r => x (Pi.single (Fin.castLE hn' t) 1) (Fin.castLE hn s)) fun s t => hI _ _]
      exact congrArg (fun N => xiZ ξ (Matrix.det N)) (Matrix.ext fun _ _ => rfl)
    · rw [if_neg (fun h => hL (hC2.1 h.2)), if_neg hL]
  · rw [if_neg hI, if_neg]
    intro h
    exact hI fun s l => by
      have h1 := h.1 l.1 s.1 l.2 s.2
      rwa [hent _ _ l.2 s.2] at h1

theorem funLeft_zero (n : ℕ) : (LinearMap.funLeft E E (Fin.castAdd 0) : Sp E (n + 0) →ₗ[E] Sp E n) = LinearMap.id :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem phiQ_law {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ r c' n' n : ℕ) (hc' : c' = 0) (hn' : r ≤ n') (hn : r ≤ n)
    {f : Sp E n' ≃ₗ[E] Sp E n'} (hf : f ∈ GLint E n' P) {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ GLint E n P)
    (A Ai : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) (Bi : Matrix (Fin n') (Fin n') (𝓞 E ⧸ P.asIdeal))
    (hA : ∀ v ∈ stdAt E n P, redV P (g v) = A.mulVec (redV P v))
    (lA : LLz r A) (lAi : LLz r Ai) (lB : LLz r (redMQ P f.toLinearMap)) (lBi : LLz r Bi) (h1 : Ai * A = 1) (h2 : redMQ P f.toLinearMap * Bi = 1)
    (y : HomE E n' n) :
    LocE.PhiQ q ξ k₀ r c' n' 0 n (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) =
      xiZ ξ (A.submatrix (Fin.castLE hn) (Fin.castLE hn)).det *
        xiZ ξ ((redMQ P f.toLinearMap).submatrix (Fin.castLE hn') (Fin.castLE hn')).det *
        LocE.PhiQ q ξ k₀ r c' n' 0 n (y ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) := by
  classical
  subst hc'
  rw [funLeft_zero]
  have e1 : (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap ∘ₗ (LinearMap.id : Sp E (n' + 0) →ₗ[E] Sp E (n' + 0)) : HomE E (n' + 0) (n + 0)) =
      g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap := rfl
  have e2 : (y ∘ₗ (LinearMap.id : Sp E (n' + 0) →ₗ[E] Sp E (n' + 0)) : HomE E (n' + 0) (n + 0)) = y := rfl
  rw [e1, e2, phiQ_eq hq hu ξ k₀ r n' n hn' hn, phiQ_eq hq hu ξ k₀ r n' n hn' hn]
  split_ifs with k1 k2 k2
  · exact (congrArg (phiZ ξ hn hn') (redMQ_sandwich P hf g A hA y k2)).trans (phiZ_law ξ hn hn' A Ai _ Bi lA lAi lB lBi h1 h2 _)
  · exact absurd ((intM_sandwich P hf hg y).1 k1) k2
  · exact absurd ((intM_sandwich P hf hg y).2 k2) k1
  · rw [mul_zero]

end Red

section Grp

theorem det_castQ {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (F : ℕ → ℕ → R) :
    (Matrix.of fun s t : Fin a => F s.1 t.1).det = (Matrix.of fun s t : Fin b => F s.1 t.1).det := by
  subst h
  rfl

theorem hq_LLz {k : Type} [CommRing k] {n r d : ℕ} {M : GL (Fin n) k} (hM : M ∈ HQ k n r d) :
    LLz r (M : Matrix (Fin n) (Fin n) k) := by
  intro i j hi hj
  refine (mem_btG.1 hM) i j ?_
  rw [coarse_of_lt hj, coarse_of_le hi]
  omega

theorem blkDet_br {k : Type} [CommRing k] {n r d : ℕ} (hn : n = r + d) (M : ↥(HQ k n r d)) :
    ((blkDet n k (coarse r [d]) 1 M : kˣ) : k) = ((M.1 : Matrix (Fin n) (Fin n) k).submatrix (brI hn) (brI hn)).det := by
  subst hn
  rw [blkDet_val]
  have hc : ∀ i : Fin (r + d), coarse r [d] i.1 = 1 ↔ r ≤ i.1 := by
    intro i
    constructor
    · intro h
      by_contra h'
      rw [coarse_of_lt (Nat.not_le.mp h')] at h
      omega
    · intro h
      rw [coarse_of_le h]
      have h2 : i.1 - r < d := by have := i.2; omega
      simp [blkIdx, h2]
  let e : Fin d ≃ {i : Fin (r + d) // coarse r [d] i.1 = 1} :=
    { toFun := fun s => ⟨brI rfl s, (hc _).2 (Nat.le_add_right _ _)⟩
      invFun := fun i => ⟨i.1.1 - r, by have h1 := i.1.2; have h2 := (hc i.1).1 i.2; omega⟩
      left_inv := fun s => Fin.ext (by simp [brI])
      right_inv := fun i => Subtype.ext (Fin.ext (by
        have h2 := (hc i.1).1 i.2
        show r + (i.1.1 - r) = i.1.1
        omega)) }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem det_padM {k : Type} [CommRing k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) : (padM k n A).det = A.det := by
  have hL : LLz n (padM k n A) := by
    intro i j hi hj
    have hi' : i = Fin.last n := Fin.ext (by have := i.2; show i.1 = n; omega)
    subst hi'
    obtain ⟨j', rfl⟩ : ∃ j' : Fin n, j = Fin.castSucc j' := ⟨⟨j.1, hj⟩, rfl⟩
    simp [padM]
  rw [det_LLz (padM k n A) hL]
  have e1 : (padM k n A).submatrix (Fin.castAdd 1) (Fin.castAdd 1) = A := by
    ext i j
    show padM k n A (Fin.castSucc i) (Fin.castSucc j) = A i j
    simp [padM]
  have e2 : ((padM k n A).submatrix (Fin.natAdd n) (Fin.natAdd n)).det = 1 := by
    rw [Matrix.det_fin_one]
    show padM k n A (Fin.last n) (Fin.last n) = 1
    simp [padM]
  rw [e1, e2, mul_one]

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {K : Type} [Field K]

theorem det_extGH {N n : ℕ} (hN : N = n + 1) {SG : Finset (HeightOneSpectrum (𝓞 E))} (h : GLG E n SG) (w : SG) :
    ((extGH hN h w : GL (Fin N) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin N) (Fin N) (𝓞 E ⧸ w.1.asIdeal)).det =
      ((h w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).det := by
  subst hN
  show ((extG h w : GL (Fin (n + 1)) (𝓞 E ⧸ w.1.asIdeal)).1).det = _
  rw [extG_apply]
  exact det_padM _

theorem red_symmQ {N : ℕ} {κ : Sp E N ≃ₗ[E] Sp E N} (hκ : κ ∈ GLint E N P) {H : GL (Fin N) (𝓞 E ⧸ P.asIdeal)}
    (hred : ∀ x ∈ stdAt E N P, redV P (κ x) = (H⁻¹).1.mulVec (redV P x)) :
    ∀ x ∈ stdAt E N P, redV P (κ.symm x) = H.1.mulVec (redV P x) := by
  intro x hx
  have hx' : κ.symm x ∈ stdAt E N P := (hκ (κ.symm x)).1 (by rw [LinearEquiv.apply_symm_apply]; exact hx)
  have h1 := hred _ hx'
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem jq_LLz {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {kj n c : ℕ} {g : Sp E n ≃ₗ[E] Sp E n}
    {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hr : rr ∈ LocE.JQ P q kj n c)
    (hrg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x)) : LLz kj (redMQ P g.toLinearMap) := by
  intro i j hi hj
  have h1 : Loc.inX E n c (Pi.single j 1) ∈ LocE.parL P q kj n c := by
    unfold LocE.parL
    rw [ciMem_sclLat]
    intro l
    rw [ciInX_apply]
    by_cases hl : l.1 < n
    · rw [dif_pos hl]
      by_cases hlj : (⟨l.1, hl⟩ : Fin n) = j
      · have h2 : ¬ (kj ≤ l.1 ∧ l.1 < n) := by
          have h3 : l.1 = j.1 := congrArg Fin.val hlj
          omega
        rw [if_neg h2, hlj, Pi.single_eq_same, zpow_zero, inv_one, one_mul]
        exact ciIntAt_one
      · rw [Pi.single_eq_of_ne hlj, mul_zero]
        exact ciIntAt_zero
    · rw [dif_neg hl, mul_zero]
      exact ciIntAt_zero
  have h2 := (hr.2 _).2 h1
  rw [hrg] at h2
  unfold LocE.parL at h2
  rw [ciMem_sclLat] at h2
  have h3 := h2 (Fin.castAdd c i)
  beta_reduce at h3
  rw [ciInX_castAdd] at h3
  have h4 : (kj ≤ (Fin.castAdd c i).1 ∧ (Fin.castAdd c i).1 < n) := ⟨hi, i.2⟩
  rw [if_pos h4, zpow_one, inv_mul_eq_div] at h3
  exact (ciRed_of_div hq hq0 h3).2

theorem lamQB_eq (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {kj r n c d : ℕ} (hkj : kj = r) (hn : n = r + d) {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : g ∈ GLint E n P) {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hrg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x)) :
    LocE.lamQB ξ kj n rr.toLinearMap = (xiZ ξ ((redMQ P g.toLinearMap).submatrix (brI hn) (brI hn)).det)⁻¹ := by
  subst hkj
  subst hn
  have hd : kj + d - kj = d := by omega
  have e0 := det_castQ hd (fun s t => Loc.atN (rr.toLinearMap (Loc.eN E (kj + d + c) (kj + t))) (kj + s))
  have hm : (Matrix.of fun s t : Fin d => Loc.atN (rr.toLinearMap (Loc.eN E (kj + d + c) (kj + t.1))) (kj + s.1)) =
      Matrix.of fun s t : Fin d => g.toLinearMap (Pi.single (brI rfl t) 1) (brI rfl s) := by
    ext s t
    have ht : kj + t.1 < kj + d := by have := t.2; omega
    have hs : kj + s.1 < kj + d := by have := s.2; omega
    show Loc.atN (rr (Loc.eN E (kj + d + c) (kj + t.1))) (kj + s.1) = _
    rw [ciEN ht, hrg, ciAtN_inX hs]
    rfl
  have e1 : redP P (Matrix.of fun s t : Fin (kj + d - kj) => Loc.atN (rr.toLinearMap (Loc.eN E (kj + d + c) (kj + t.1))) (kj + s.1)).det =
      ((redMQ P g.toLinearMap).submatrix (brI rfl) (brI rfl)).det := by
    rw [e0, hm, redP_det (Matrix.of fun s t : Fin d => g.toLinearMap (Pi.single (brI rfl t) 1) (brI rfl s)) fun s t => glint_int P hg _ _]
    exact congrArg Matrix.det (Matrix.ext fun _ _ => rfl)
  unfold LocE.lamQB
  rw [unitV_eq]
  exact congrArg (fun z => (xiZ ξ z)⁻¹) e1

end Grp

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem rank_midQ {m2 : ℕ} (hm : R.m = m2 + 2) : R.N (m2 + 1) = R.r + (m2 + 1) * R.t := by
  have h1 : (m2 + 1) * (R.t + 1) = (m2 + 1) * R.t + (m2 + 1) := by ring
  unfold Ranks.N Ranks.r
  omega

theorem kj_midQ {m2 : ℕ} (hm : R.m = m2 + 2) : R.k + (m2 + 1) = R.r := by
  unfold Ranks.r
  omega

open Classical in

theorem rowTy_inv_lamQ (P : LevFam X.E X.K R.r Pr.vGs) (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs)
    (H : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hH : H ∈ ((rowTy Ch sel mu P).inv w).H) :
    ∃ hH' : H ∈ HQ (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.r (R.m * R.t),
      ((rowTy Ch sel mu P).inv w).lam ⟨H, hH⟩ =
        lamQ (resChar (mu : Chr X.F X.E X.K) w.1) (R.N R.m - 1) R.r (R.m * R.t) ⟨H, hH'⟩ := by
  have e : rowTy Ch sel mu P w = rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K))
      ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩ := LevFam.glue_of_not _ _ w hw
  revert hH
  show ∀ hH : H ∈ ((rowTy Ch sel mu P w).inv).H, ∃ hH' : H ∈ HQ (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.r (R.m * R.t),
    ((rowTy Ch sel mu P w).inv).lam ⟨H, hH⟩ = lamQ (resChar (mu : Chr X.F X.E X.K) w.1) (R.N R.m - 1) R.r (R.m * R.t) ⟨H, hH'⟩
  rw [e]
  intro hH
  refine ⟨hH, ?_⟩
  show ((lamQP (mu : Chr X.F X.E X.K) w.1 (R.N R.m - 1) R.r (R.m * R.t))⁻¹)⁻¹ ⟨H, hH⟩ = _
  rw [inv_inv]
  rfl

open Classical in

theorem top_local_law_at_Q_primes {G : ChGlob X R.m} {m2 : ℕ} (hOk : L.Ok Ch sel mu cst G m2) (hU : QUnif sel mu)
    (P : LevFam X.E X.K R.r Pr.vGs) (b : L.β (m2 + 1)) : TopLawQ Ch sel mu cst L P m2 b := by
  intro w hw c h₁ hh₁ κr κt hκr hκt y
  have hm := hOk.hm
  have hwQ : w.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp w.2).resolve_left hw
  have hq : ((qOf w.1 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := qOf_memB w.1
  have hu := hU w.1 hwQ
  have hq0 := ciQ_ne_zero hu
  have hn' := rank_midQ (R := R) hm
  have hn := rank_X'_eq R
  have hkj := kj_midQ (R := R) hm
  have hr' : R.r ≤ R.N (m2 + 1) := by rw [hn']; exact Nat.le_add_right _ _
  have hgrp : ∀ c' : ↥(GLint X.E (R.N (m2 + 1)) w.1), c' ∈ (L.levQ (m2 + 1) b ⟨w.1, hwQ⟩).H →
      ∃ rr : AutY X R (m2 + 1), rr ∈ LocE.JQ w.1 (qOf w.1) (R.k + (m2 + 1)) (R.N (m2 + 1)) (cOf R (m2 + 1)) ∧
        rr ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (m2 + 1) w.1) (L.h (m2 + 1) b ⟨w.1, Finset.mem_union_right _ hwQ⟩) ∧
        ∀ x, rr (Loc.inX X.E (R.N (m2 + 1)) (cOf R (m2 + 1)) x) = Loc.inX X.E (R.N (m2 + 1)) (cOf R (m2 + 1)) (c'.1 x) := by
    intro c' h1
    rw [hOk.grpQ (m2 + 1) b ⟨w.1, hwQ⟩, Subgroup.mem_subgroupOf] at h1
    unfold prCat at h1
    obtain ⟨rr, hrr, hx⟩ := h1
    refine ⟨rr, ?_, hrr, hx⟩
    have h2 := hrr.2
    rw [hOk.last_h] at h2
    have h3 : rr ∈ Jat (Pr := Pr) (R := R) cst.sharp (m2 + 1) w.1 := by simpa [MulAut.conj_apply] using h2
    unfold Jat at h3
    rwa [if_neg hw] at h3
  obtain ⟨rc, hJc, hCc, hxc⟩ := hgrp c.1 c.2
  obtain ⟨ri, hJi, -, hxi⟩ := hgrp c.1⁻¹ (Subgroup.inv_mem _ c.2)
  have lC : LLz R.r (redMQ w.1 c.1.1.toLinearMap) := by
    have := jq_LLz hq hq0 hJc hxc
    rwa [hkj] at this
  have lB : LLz R.r (redMQ w.1 (c.1⁻¹).1.toLinearMap) := by
    have := jq_LLz hq hq0 hJi hxi
    rwa [hkj] at this
  have h2 : redMQ w.1 (c.1⁻¹).1.toLinearMap * redMQ w.1 c.1.1.toLinearMap = 1 := redMQ_mul_inv w.1 c.1.2
  obtain ⟨hH', hlamR⟩ := rowTy_inv_lamQ Ch sel mu P w hw (h₁ w) hh₁
  have lA : LLz R.r ((h₁ w : GL _ _) : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) := hq_LLz hH'
  have lAi : LLz R.r (((h₁ w)⁻¹ : GL _ _) : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) :=
    hq_LLz (Subgroup.inv_mem _ hH')
  have h1 : (((h₁ w)⁻¹ : GL _ _) : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) * ((h₁ w : GL _ _) : Matrix _ _ _) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hA := red_symmQ κr.2 hκr
  have hs1 : rhoS Ch sel mu (m2 + 1) w (LinearEquiv.det (c.1⁻¹).1 : X.Eˣ) =
      xiZ (resChar (mu : Chr X.F X.E X.K) w.1)⁻¹ (redMQ w.1 (c.1⁻¹).1.toLinearMap).det := by
    unfold rhoS
    rw [if_neg hw, unitV_eq, redP_detEquiv w.1 (c.1⁻¹).2]
  have hs2 : rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κt.1 : X.Eˣ) =
      xiZ (resChar (mu : Chr X.F X.E X.K) w.1)
        (((h₁ w)⁻¹ : GL _ _) : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)).det := by
    unfold rhoT
    rw [if_neg hw, unitV_eq, redP_detEquiv w.1 κt.2, redMQ_of w.1 κt.1.toLinearMap _ hκt, ← Pi.inv_apply, ← map_inv, det_extGH]
    rfl
  have hl1 : (((((rowTy Ch sel mu P).inv w).lam ⟨h₁ w, hh₁⟩)⁻¹ : X.Kˣ) : X.K) =
      (xiZ (resChar (mu : Chr X.F X.E X.K) w.1)
        (((h₁ w : GL _ _) : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)).submatrix (brI hn) (brI hn)).det)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hlamR, lamQ_apply, ← xiZ_unit, blkDet_br hn]
  have hl2 : ((((L.levQ (m2 + 1) b ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam c)⁻¹ : X.Kˣ) : X.K) =
      xiZ (resChar (mu : Chr X.F X.E X.K) w.1) ((redMQ w.1 c.1.1.toLinearMap).submatrix (brI hn') (brI hn')).det := by
    rw [Units.val_inv_eq_inv_val, hOk.chrQ (m2 + 1) b ⟨w.1, hwQ⟩ c rc hCc hxc]
    unfold chiInv
    rw [hOk.last_h]
    have hrange : Finset.range (cOf R (m2 + 1) - 1) = ∅ := by
      rw [cOf_topB hm]
      rfl
    have hn1 : Loc.n1Arg rc = 0 := by
      unfold Loc.n1Arg
      rw [hrange, Finset.sum_empty]
    have hone : ((1 : AutY X R (m2 + 1))⁻¹ * rc * 1 : AutY X R (m2 + 1)) = rc := by simp
    rw [hn1, hOk.cst_ok.psi_int _ 0 ciIntAt_zero, inv_one, one_mul, hone]
    unfold lamRow
    rw [if_neg hw, lamQB_eq _ hkj hn' c.1.2 hxc, inv_inv]
  have hP1 : PhiTop Ch mu cst.sharp m2 w.1 (κr.1.symm.toLinearMap ∘ₗ y ∘ₗ (c.1⁻¹).1.toLinearMap ∘ₗ
        LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
      xiZ (resChar (mu : Chr X.F X.E X.K) w.1)
          (((h₁ w : GL _ _) : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)).submatrix
            (Fin.castLE (r_le_X' R)) (Fin.castLE (r_le_X' R))).det *
        xiZ (resChar (mu : Chr X.F X.E X.K) w.1) ((redMQ w.1 (c.1⁻¹).1.toLinearMap).submatrix (Fin.castLE hr') (Fin.castLE hr')).det *
        PhiTop Ch mu cst.sharp m2 w.1 (y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
    unfold PhiTop
    rw [if_neg hw]
    exact phiQ_law hq hu _ R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N R.m - 1) (cOf_topB hm) hr' (r_le_X' R)
      (c.1⁻¹).2 ((GLint X.E (R.N R.m - 1) w.1).inv_mem κr.2) _ _ _ hA lA lAi lB lC h1 h2 y
  have hS := scal_law (resChar (mu : Chr X.F X.E X.K) w.1) hn hn' (r_le_X' R) hr' _ _ _ _ lA lC h1 h2
  rw [hs1, hs2, hl1, hl2, hP1, ← hS]
  ring

end Main

section FtYQ

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

open Classical in

theorem ybSet_diffQ {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N)
    (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) :
    ∀ a ∈ Y, ∀ a' ∈ Y, ((qOf w.1 : X.E) ^ cst.M)⁻¹ • (a - a') ∈ localization₂ w.1.asIdeal N := by
  obtain ⟨y0, hy0, rfl⟩ := hY
  intro a ha a' ha'
  have h1 := (mem_locLat _ _ _ (a - y0)).1 ha w
  have h2 := (mem_locLat _ _ _ (a' - y0)).1 ha' w
  simp only [if_neg hw, zpow_natCast] at h1 h2
  have e : a - a' = (a - y0) - (a' - y0) := by abel
  rw [e, smul_sub]
  exact sub_mem h1 h2

theorem ftY_moveQ (hcst : cst.Ok) (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D w) {n : ℕ} (κ : ↥(GLint X.E n w.1))
    (η : Sp X.E n →ₗ[X.E] X.E) (y y₁ : Sp X.E n) (hδ : ((qOf w.1 : X.E) ^ cst.M)⁻¹ • (κ.1 y₁ - y) ∈ stdAt X.E n w.1)
    (hq : ((qOf w.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n w.1) :
    ftY sel mu cst w (η ∘ₗ κ.1.toLinearMap) y₁ = ftY sel mu cst w η y := by
  have hqn := intAt_qpow3 (X := X) w.1
  have hq0 : (qOf w.1 : X.E) ^ cst.M ≠ 0 := pow_ne_zero _ (by exact_mod_cast (qOf_pos w.1).ne')
  have hk : ∀ v, κ.1 v ∈ stdAt X.E n w.1 ↔ v ∈ stdAt X.E n w.1 := κ.2
  have hiff : (∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * (η ∘ₗ κ.1.toLinearMap) (Pi.single i 1))) ↔
      ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1)) := by
    constructor
    · intro h i
      have hm : κ.1.symm (Pi.single i 1) ∈ stdAt X.E n w.1 :=
        (hk _).1 (by rw [LinearEquiv.apply_symm_apply]; exact ciSingle_mem i)
      have := intAt_linear_form_on_std w.1 (((qOf w.1 : X.E) ^ cst.M) • (η ∘ₗ κ.1.toLinearMap)) (fun j => by
        rw [LinearMap.smul_apply, smul_eq_mul]
        exact h j) hm
      simpa using this
    · intro h i
      have := intAt_linear_form_on_std w.1 (((qOf w.1 : X.E) ^ cst.M) • η) (fun j => by
        rw [LinearMap.smul_apply, smul_eq_mul]
        exact h j) ((hk _).2 (ciSingle_mem i))
      simpa using this
  unfold ftY
  rw [if_neg hw, if_neg hw]
  by_cases hI : ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1))
  · rw [if_pos (hiff.2 hI), if_pos hI]
    have hL : ∀ v ∈ stdAt X.E n w.1, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η v) := by
      intro v hv
      have := intAt_linear_form_on_std w.1 (((qOf w.1 : X.E) ^ cst.M) • η) (fun j => by
        rw [LinearMap.smul_apply, smul_eq_mul]
        exact hI j) hv
      rwa [LinearMap.smul_apply, smul_eq_mul] at this
    have e : (η ∘ₗ κ.1.toLinearMap) y₁ = η y + η (κ.1 y₁ - y) := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub]
      ring
    have heps : IntAt w.1 ((epsSg : ℤ) : X.E) := by
      have : ((epsSg : ℤ) : X.E) = -1 := by simp [epsSg]
      rw [this]
      exact intAt_neg_kernel_local_factors (by simpa using intAt_natCast_kernel_local_factors w.1 1)
    have h1 : IntAt w.1 (η (κ.1 y₁ - y)) := by
      have := hL _ hδ
      rwa [map_smul, smul_eq_mul, mul_inv_cancel_left₀ hq0] at this
    have h2 : IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * η y)) := by
      have := hL _ hq
      rwa [map_smul, smul_eq_mul] at this
    obtain ⟨k, hk'⟩ : ∃ k, cst.D w = k + (cst.M + cst.M) := ⟨cst.D w - 2 * cst.M, by omega⟩
    have hqD : ∀ a : X.E, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * a)) → IntAt w.1 ((qOf w.1 : X.E) ^ cst.D w * a) := by
      intro a ha
      have e' : (qOf w.1 : X.E) ^ cst.D w * a = (qOf w.1 : X.E) ^ k * ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * a)) := by
        rw [hk', pow_add, pow_add]
        ring
      rw [e']
      exact (hqn k).mul ha
    rw [e, mul_add, hcst.psi_add w _ _ ?_ ?_, hcst.psi_int w _ (IntAt.mul heps h1), mul_one]
    · refine hqD _ ?_
      have e' : (qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * (((epsSg : ℤ) : X.E) * η y)) =
          ((epsSg : ℤ) : X.E) * ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * η y)) := by ring
      rw [e']
      exact heps.mul h2
    · refine hqD _ ?_
      exact (hqn _).mul ((hqn _).mul (heps.mul h1))
  · rw [if_neg (mt hiff.1 hI), if_neg hI]

end FtYQ

section ProdU

open Classical in

theorem prod_uSG_dite {α M : Type} [CommMonoid M] {A B : Finset α} (hd : ∀ P ∈ B, P ∉ A) (f : {w // w ∈ A} → M) (g : {P // P ∈ B} → M) :
    ∏ w : {w // w ∈ A ∪ B}, (if h : w.1 ∈ A then f ⟨w.1, h⟩ else g ⟨w.1, (Finset.mem_union.mp w.2).resolve_left h⟩) =
      (∏ w : {w // w ∈ A}, f w) * ∏ P : {P // P ∈ B}, g P := by
  let F : α → M := fun w => if h : w ∈ A then f ⟨w, h⟩ else if h' : w ∈ B then g ⟨w, h'⟩ else 1
  have e0 : ∀ w : {w // w ∈ A ∪ B}, (if h : w.1 ∈ A then f ⟨w.1, h⟩ else g ⟨w.1, (Finset.mem_union.mp w.2).resolve_left h⟩) = F w.1 := by
    intro w
    by_cases h : w.1 ∈ A
    · simp only [F, dif_pos h]
    · simp only [F, dif_neg h, dif_pos ((Finset.mem_union.mp w.2).resolve_left h)]
  have e1 : ∀ w : {w // w ∈ A}, f w = F w.1 := fun w => by simp only [F, dif_pos w.2]
  have e2 : ∀ P : {P // P ∈ B}, g P = F P.1 := fun P => by simp only [F, dif_neg (hd P.1 P.2), dif_pos P.2]
  rw [Fintype.prod_congr _ _ e0, Fintype.prod_congr _ _ e1, Fintype.prod_congr _ _ e2]
  rw [Finset.univ_eq_attach, Finset.univ_eq_attach, Finset.univ_eq_attach, Finset.prod_attach (A ∪ B) F, Finset.prod_attach A F,
    Finset.prod_attach B F]
  exact Finset.prod_union (Finset.disjoint_left.2 fun a ha hb => hd a hb ha)

end ProdU

section InvQ

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word}

open Classical in

theorem xiCpl2_invQ (hPr : Pr.Ok) (hcst : cst.Ok) (hDQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) (hR : PosT sel mu u)
    {m2 : ℕ} (hTI : TopInvAt Ch sel mu cst m2)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu)
    (x z : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (hYm : Y ∈ ybSet sel mu cst p.deco.1.N)
    (hz : z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N (tilQ sel mu u d).1.N)) :
    XiCpl2 Ch sel mu cst m2 p Y d (x + z) = XiCpl2 Ch sel mu cst m2 p Y d x := by
  obtain ⟨w0, hw0, rfl⟩ := (mem_mulLat _ _ _).1 hz
  have hphi : phiT X.K p.deco.1 (tilQ sel mu u d).1 (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) =
      phiT X.K p.deco.1 (tilQ sel mu u d).1 x := by
    refine phiT_add_mul X.K p.deco (tilQ sel mu u d) (Sall sel mu u) (fun P => Finset.mem_union_left _ P.2) (Pr.T u) (fun P => ?_) x _ ?_
    · have h1 : Pr.piT u ∈ P.1.asIdeal := mem_asIdeal_of_mem_divs P.2
      rw [← hPr.piT_norm u]
      exact P.1.asIdeal.mul_mem_right _ h1
    · refine (mem_mulLat _ _ _).2 ⟨(((∏ P : rowSG Pr sel mu, Col.qOf P.1) ^ cst.B : ℕ) : 𝓞 X.E) • w0,
        Submodule.smul_mem _ _ hw0, ?_⟩
      rw [smul_smul]
      unfold cBof
      push_cast
      rfl
  have hoff := offCoupling_top_invariance Ch sel mu cst hTI hPr hcst hDQ hR p Y d hYm x w0 (fun P hP => hw0 P (Finset.mem_union_right _ hP))
  unfold offCpl2 at hoff
  unfold XiCpl2
  rw [hphi, hoff]

end InvQ

section Cp2Q

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

open Classical in

theorem frsF_smulQ {j : ℕ} (p : ChPt (R := R) sel mu u j)
    (Λ : LevFam X.E X.K (R.N j) Pr.vGs) (Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
    (g : FrmG Λ Θ) (w : rowSG Pr sel mu) :
    ∃ κ : ↥(GLint X.E (R.N j) w.1), frsF sel mu (g • p) w = g.1.1 * frsF sel mu p w * κ.1 ∧
      (∀ hw : w.1 ∈ Pr.vGs, ∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (κ.1 x) =
        (((g.2.1 : GLG X.E (R.N j) Pr.vGs) ⟨w.1, hw⟩)⁻¹ : GL _ _).1.mulVec (redV w.1 x)) ∧
      ∀ hw : w.1 ∉ Pr.vGs, κ = ((g.2.2 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩)⁻¹ := by
  by_cases hw : w.1 ∈ Pr.vGs
  · obtain ⟨κ, h1, h2⟩ := frsF_smul sel mu p Λ Θ g w hw
    exact ⟨κ, h1, fun _ => h2, fun h => absurd hw h⟩
  · refine ⟨((g.2.2 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩)⁻¹, ?_,
      fun h => absurd h hw, fun _ => rfl⟩
    unfold frsF
    rw [dif_neg hw, dif_neg hw]
    rfl

open Classical in

theorem coupled_scalar_at_Q_primes (hS : QSep Pr sel mu) (b : L.β (m2 + 1)) (P : LevFam X.E X.K R.r Pr.vGs)
    (g : FrmG (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b)) (g₁ : ↥(rowTy Ch sel mu P).inv.grp) :
    ((((rowTy Ch sel mu P).inv.chr g₁)⁻¹ * (((L.levG (m2 + 1) b).chr g.2.1)⁻¹ * ((L.levQ (m2 + 1) b).chr g.2.2)⁻¹) : X.Kˣ) : X.K) =
      ∏ w : rowSG Pr sel mu,
        (((((rowTy Ch sel mu P).inv w).lam ⟨(g₁.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) w, g₁.2 w (Set.mem_univ w)⟩)⁻¹ : X.Kˣ) : X.K) *
          (if hw : w.1 ∈ Pr.vGs then
            ((((L.levG (m2 + 1) b ⟨w.1, hw⟩).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hw⟩, g.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K)
          else
            ((((L.levQ (m2 + 1) b ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam
              ⟨(g.2.2 : GLQ X.E (R.N (m2 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩,
                g.2.2.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K)) := by
  rw [Finset.prod_mul_distrib, prod_uSG_dite hS
    (fun w => ((((L.levG (m2 + 1) b w).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) w, g.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K))
    (fun Q => ((((L.levQ (m2 + 1) b Q).lam ⟨(g.2.2 : GLQ X.E (R.N (m2 + 1)) (QE sel (mu : Chr X.F X.E X.K))) Q, g.2.2.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K))]
  rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, levFam_chr_apply_coe, levFam_chr_apply_coe]
  have hq : (((L.levQ (m2 + 1) b).chr g.2.2 : X.Kˣ) : X.K) =
      ∏ Q, (((L.levQ (m2 + 1) b Q).lam ⟨(g.2.2 : GLQ X.E (R.N (m2 + 1)) (QE sel (mu : Chr X.F X.E X.K))) Q, g.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) :=
    piChar_apply_coe' _ _ g.2.2
  rw [hq]
  simp only [Units.val_inv_eq_inv_val, Finset.prod_inv_distrib]

variable {u m2}

theorem coupled_kernel_local_identity (w : rowSG Pr sel mu) (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1)) (κr : ↥(GLint X.E (R.N R.m - 1) w.1)) (s c₀ : X.K)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu)
    (γ : UF X.E (R.N (m2 + 1))) (γ₁ : UF X.E (R.N R.m - 1)) (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (hne : Y.Nonempty)
    (key : ∀ y : HomE X.E (R.N (m2 + 1)) (R.N R.m - 1),
      s * PhiTop Ch mu cst.sharp m2 w.1 (κr.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap ∘ₗ
          LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
        c₀ * PhiTop Ch mu cst.sharp m2 w.1 (y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))))
    (hft : ∀ (η : Sp X.E (R.N (m2 + 1)) →ₗ[X.E] X.E), ∀ a ∈ Y,
      ftY sel mu cst w (η ∘ₗ κ.1.toLinearMap) (κ.1.symm ((frsF sel mu p w).symm a)) = ftY sel mu cst w η ((frsF sel mu p w).symm (repY Y))) :
    s * (PhiTop Ch mu cst.sharp m2 w.1
        ((γ₁.1 * d.1.liftFr w * κr.1).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ
          ((extUH (N_m_succ R) γ₁).1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) ∘ₗ
            (γ.1 * frsF sel mu p w * κ.1).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst w ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ
          ((extUH (N_m_succ R) γ₁).1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) ∘ₗ (γ.1 * frsF sel mu p w * κ.1).toLinearMap)
        ((γ.1 * frsF sel mu p w * κ.1).symm (repY ((fun v => γ.1 v) '' Y)))) =
    c₀ * (PhiTop Ch mu cst.sharp m2 w.1 ((d.1.liftFr w).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p w).toLinearMap ∘ₗ
          LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst w ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p w).toLinearMap)
        ((frsF sel mu p w).symm (repY Y))) := by
  obtain ⟨a, ha, hra⟩ : repY ((fun v => γ.1 v) '' Y) ∈ (fun v => γ.1 v) '' Y := representative_mem (hne.image _)
  have hra' : repY ((fun v => γ.1 v) '' Y) = γ.1 a := hra.symm
  have e2 : (γ.1 * frsF sel mu p w * κ.1).symm (γ.1 a) = κ.1.symm ((frsF sel mu p w).symm a) := by
    rw [LinearEquiv.symm_apply_eq]
    simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
  have hA : (γ₁.1 * d.1.liftFr w * κr.1).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ
        ((extUH (N_m_succ R) γ₁).1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) ∘ₗ
          (γ.1 * frsF sel mu p w * κ.1).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) =
      κr.1.symm.toLinearMap ∘ₗ
        ((d.1.liftFr w).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p w).toLinearMap) ∘ₗ κ.1.toLinearMap ∘ₗ
          LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, prXp_extUH2]
  have hη : ((((Pr.piT u : 𝓞 X.E) : X.E))⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ
        ((extUH (N_m_succ R) γ₁).1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) ∘ₗ (γ.1 * frsF sel mu p w * κ.1).toLinearMap =
      (((((Pr.piT u : 𝓞 X.E) : X.E))⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p w).toLinearMap) ∘ₗ
        κ.1.toLinearMap := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply,
      LinearMap.smul_apply, atNL_extUH2]
  rw [hA, hη, hra', e2, hft _ a ha, ← mul_assoc,
    key ((d.1.liftFr w).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p w).toLinearMap), mul_assoc]
  rfl

theorem ftY_frame (hcst : cst.Ok) (hDQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P)
    (w : rowSG Pr sel mu) (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1))
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (hYm : Y ∈ ybSet sel mu cst p.deco.1.N)
    (η : Sp X.E (R.N (m2 + 1)) →ₗ[X.E] X.E) (a : Sp X.E (R.N (m2 + 1))) (ha : a ∈ Y) :
    ftY sel mu cst w (η ∘ₗ κ.1.toLinearMap) (κ.1.symm ((frsF sel mu p w).symm a)) = ftY sel mu cst w η ((frsF sel mu p w).symm (repY Y)) := by
  have hFst : ∀ z, z ∈ localization₂ w.1.asIdeal p.deco.1.N → (frsF sel mu p w).symm z ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
    intro z hz
    apply (frsF_isFr sel mu p w _).1
    rw [LinearEquiv.apply_symm_apply]
    exact hz
  have hr0 : repY Y ∈ Y := representative_mem ⟨a, ha⟩
  by_cases hw : w.1 ∈ Pr.vGs
  · obtain ⟨-, hdiff, hqm⟩ := ybSet_props2 sel mu cst hYm w hw
    refine ftY_move2 sel mu cst hcst w hw κ _ _ _ ?_ ?_
    · rw [LinearEquiv.apply_symm_apply, ← map_sub]
      exact hFst _ (hdiff _ ha _ hr0)
    · rw [← LinearEquiv.map_smul]
      exact hFst _ (hqm _ hr0)
  · obtain ⟨-, hqm⟩ := coupling_index_scaled_mem_local sel mu cst hYm w hw
    refine ftY_moveQ sel mu cst hcst w hw (hDQ w hw) κ _ _ _ ?_ ?_
    · rw [LinearEquiv.apply_symm_apply, ← map_sub, ← LinearEquiv.map_smul]
      exact hFst _ (ybSet_diffQ sel mu cst hYm w hw _ ha _ hr0)
    · rw [← LinearEquiv.map_smul]
      exact hFst _ (hqm _ hr0)

variable (u m2)

open Classical in

theorem cp2EquivOn_ofQ (hS : QSep Pr sel mu) (hR : PosT sel mu u) (hDQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P)
    (hT : 0 < Pr.T u) (hPr : Pr.Ok) (hcst : cst.Ok)
    (hOk : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (hTI : TopInvAt Ch sel mu cst m2)
    (hTop : TopLaw Ch sel mu cst L P m2 b) (hTopQ : TopLawQ Ch sel mu cst L P m2 b) :
    Cp2EquivOn W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY P := by
  intro g g₁ p Y d hYm
  change Y ∈ ybSet sel mu cst p.deco.1.N at hYm
  choose κ hκ hκr hκQ using fun w : rowSG Pr sel mu =>
    frsF_smulQ sel mu u p (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g w
  have hfr : frsF sel mu (g • p) = fun w => g.1.1 * frsF sel mu p w * (κ w).1 := funext hκ
  have hTc : ∀ Q : Pr.vT u, cO X.E (Pr.piT u) ∉ Q.1.asIdeal := conj_piT_notMem hPr u
  have hGc : ∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal := fun w hw =>
    ((hR ⟨w.1, (mem_divs (hPr.piT_ne_zero u) w.1).2 hw⟩).sg w).1 rfl
  have hgd : g₁ • d = ((g₁.1, (g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))) :
      UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) • d := rfl
  have htil : tilQ sel mu u (g₁ • d) = (extUH (N_m_succ R) g₁.1, extGH (N_m_succ R) (g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))) •
      tilQ sel mu u d := by
    rw [hgd]
    exact DecoSet.tilH_smul (N_m_succ R) _ d hTc hGc
  choose κt hκt hκtr using fun w : rowSG Pr sel mu =>
    liftFr_smul (tilQ sel mu u d) (extUH (N_m_succ R) g₁.1, extGH (N_m_succ R) (g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))) w
  have hfrT : frsT sel mu u (g₁ • d) = fun w => (extUH (N_m_succ R) g₁.1).1 * frsT sel mu u d w * (κt w).1 := by
    funext w
    unfold frsT
    rw [htil]
    exact hκt w
  choose κr hκr' hκrr using fun w : rowSG Pr sel mu =>
    liftFr_smul d ((g₁.1, (g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))) :
      UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) w
  have hlr : ∀ w, (g₁ • d).1.liftFr w = g₁.1.1 * d.1.liftFr w * (κr w).1 := fun w => hκr' w
  have hN : IsSdLat p.deco.1.N := ⟨p.deco.2.lat, p.deco.2.uni⟩
  have hN' : IsSdLat (tilQ sel mu u d).1.N := ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩
  have hdeco : (g • p).deco = (g.1, (g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs)) • p.deco := rfl
  have hYm1 : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (gmap g.1.1 p.deco.1.N) :=
    (ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y).2 hYm
  have hne : Y.Nonempty := by
    obtain ⟨y0, -, rfl⟩ := hYm
    exact ⟨y0, by rw [Set.mem_ofPred_eq, sub_self]; exact zero_mem _⟩
  unfold cp2K
  split_ifs with h1 h2 <;> first | exact absurd hYm1 h1 | exact absurd hYm h2 | skip
  rw [hfr, hfrT, htil]
  refine (kerOf_move hOk.top (cBof_pos sel mu cst u hT) hN hN' (frsF sel mu p) (frsT sel mu u d) g.1 (extUH (N_m_succ R) g₁.1) κ κt
    _ _ ((((rowTy Ch sel mu P).inv.chr g₁.2)⁻¹ * (((L.levG (m2 + 1) b).chr g.2.1)⁻¹ * ((L.levQ (m2 + 1) b).chr g.2.2)⁻¹) : X.Kˣ) : X.K)
    (fun x z hz => xiCpl2_invQ Ch sel mu cst hPr hcst hDQ hR hTI p Y d x z hYm hz) ?_).trans ?_
  · intro x
    unfold XiCpl2
    rw [hdeco, htil, phiT_smul]
    simp only [hfr, hlr]
    rw [coupled_scalar_at_Q_primes Ch sel mu L m2 hS b P g g₁.2]
    refine prod_mul_eq_of_forall_cross_mul_eq _ _ _ _ _ fun w => ?_
    refine coupled_kernel_local_identity Ch sel mu cst w (κ w) (κr w) _ _ p Y d g.1 g₁.1 x hne ?_
      (fun η a ha => ftY_frame sel mu cst hcst hDQ w (κ w) p Y hYm η a ha)
    intro y
    by_cases hw : w.1 ∈ Pr.vGs
    · rw [dif_pos hw]
      exact hTop w hw ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hw⟩, g.2.1.2 _ (Set.mem_univ _)⟩
        (g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) (g₁.2.2 w (Set.mem_univ w)) (κ w) (κr w) (κt w) (hκr w hw) (hκrr w) (hκtr w) y
    · have key := hTopQ w hw ⟨(g.2.2 : GLQ X.E (R.N (m2 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩,
          g.2.2.2 _ (Set.mem_univ _)⟩
        (g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) (g₁.2.2 w (Set.mem_univ w)) (κr w) (κt w) (hκrr w) (hκtr w) y
      rw [← hκQ w hw] at key
      rw [dif_neg hw]
      exact key
  · show _ = (evRho W Ch sel mu P u g₁) ∘ₗ _ ∘ₗ (frmRho (colValF W sel mu u (m2 + 1)) (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g⁻¹)
    simp only [evRho, frmRho, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_inv, Prod.snd_inv, map_inv,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    ring

end Cp2Q

section Close

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

theorem cp2EquivOn_of_ok {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) (hS : QSep Pr sel mu) (hU : QUnif sel mu) (hR : PosT sel mu u)
    (hT : 0 < Pr.T u) (hPr : Pr.Ok) (hOk : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (hTop : TopLaw Ch sel mu cst L P m2 b) :
    Cp2EquivOn W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY P :=
  cp2EquivOn_ofQ W Ch sel mu cst L A u m2 hS hR hL.depthQ hT hPr hL.cst_ok hOk b hY P (phiTop_inv Ch sel mu cst hL.hm) hTop
    (top_local_law_at_Q_primes Ch sel mu cst L hL hU P b)

theorem qSep_of (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S) : QSep Pr sel mu :=
  fun P hP hw => QE_disj mu hPr hsel hS P hw hP

open Classical in

theorem qUnif_of (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) : QUnif sel mu :=
  fun P hP => mq_rowSG_unif (Pr := Pr) mu hX hPr hsel ⟨P, Finset.mem_union_right _ hP⟩

end Close

namespace Test

section T1

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {K : Type} [Field K]

def inclQ (E : Type) [Field E] (n' n : ℕ) : HomE E n' n :=
  LinearMap.pi fun l : Fin n => if h : l.1 < n' then LinearMap.proj ⟨l.1, h⟩ else 0

end T1

section T2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end T2

end Test

end Formalism.L2.Ker
