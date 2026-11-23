import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockMatrixMulBlocks
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParahoricSubgroupCompactOpenMeasure
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDetStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParahoricCharacterModulusPropertiesStatement
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Eigen

section Alg

variable {F : Type} [Field F]

theorem unramifiedCharExt_mul (δ : Fˣ →* ℂˣ) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    chi0 δ (x * y) = chi0 δ x * chi0 δ y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  simp only [chi0, dif_neg hx, dif_neg hy, dif_neg hxy]
  rw [show Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy from Units.ext rfl, map_mul,
    Units.val_mul]

theorem unramifiedCharExt_ne_zero (δ : Fˣ →* ℂˣ) {x : F} (hx : x ≠ 0) : chi0 δ x ≠ 0 := by
  simp only [chi0, dif_neg hx]
  exact Units.ne_zero _

theorem extendedCharacter_congr_of_tame (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ)
    (tame : ∀ x : Fˣ, nrm ((x : F) - 1) < 1 → δ x = 1) {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : nrm (u - v) < nrm v) : chi0 δ u = chi0 δ v := by
  have hw : u / v ≠ 0 := div_ne_zero hu hv
  have h1 : chi0 δ (u / v) = 1 := by
    simp only [chi0, dif_neg hw]
    have : δ (Units.mk0 (u / v) hw) = 1 := by
      apply tame
      have e : ((Units.mk0 (u / v) hw : Fˣ) : F) - 1 = (u - v) / v := by
        simp only [Units.val_mk0]; field_simp
      rw [e, map_div₀]
      exact (div_lt_one (nrm.pos hv)).2 h
    rw [this]; rfl
  have h2 : u = (u / v) * v := by field_simp
  calc chi0 δ u = chi0 δ ((u / v) * v) := by rw [← h2]
    _ = chi0 δ v := by rw [unramifiedCharExt_mul δ hw hv, h1, one_mul]

theorem int_mul {O : Subring F} {a b c : ℕ} {X : Matrix (Fin a) (Fin b) F}
    {Y : Matrix (Fin b) (Fin c) F} (hX : X ∈ intMat O a b) (hY : Y ∈ intMat O b c) :
    X * Y ∈ intMat O a c := fun i j => by
  rw [Matrix.mul_apply]; exact O.sum_mem fun k _ => O.mul_mem (hX i k) (hY k j)

theorem int_add {O : Subring F} {a b : ℕ} {X Y : Matrix (Fin a) (Fin b) F}
    (hX : X ∈ intMat O a b) (hY : Y ∈ intMat O a b) : X + Y ∈ intMat O a b :=
  fun i j => O.add_mem (hX i j) (hY i j)

theorem II_add {O : Subring F} {ϖ : F} {a b : ℕ} {X Y : Matrix (Fin a) (Fin b) F}
    (hX : X ∈ IIset O ϖ) (hY : Y ∈ IIset O ϖ) : X + Y ∈ IIset O ϖ := fun i j => by
  obtain ⟨o, ho, e⟩ := hX i j
  obtain ⟨p, hp, f⟩ := hY i j
  exact ⟨o + p, O.add_mem ho hp, by rw [Matrix.add_apply, e, f, mul_add]⟩

theorem II_mul_int {O : Subring F} {ϖ : F} {a b c : ℕ} {X : Matrix (Fin a) (Fin b) F}
    {Y : Matrix (Fin b) (Fin c) F} (hX : X ∈ IIset O ϖ) (hY : Y ∈ intMat O b c) :
    X * Y ∈ IIset O ϖ := fun i j => by
  choose f hf hfe using hX
  refine ⟨∑ k, f i k * Y k j, O.sum_mem fun k _ => O.mul_mem (hf i k) (hY k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hfe, mul_assoc]

theorem int_mul_II {O : Subring F} {ϖ : F} {a b c : ℕ} {X : Matrix (Fin a) (Fin b) F}
    {Y : Matrix (Fin b) (Fin c) F} (hX : X ∈ intMat O a b) (hY : Y ∈ IIset O ϖ) :
    X * Y ∈ IIset O ϖ := fun i j => by
  choose f hf hfe using hY
  refine ⟨∑ k, X i k * f k j, O.sum_mem fun k _ => O.mul_mem (hX i k) (hf k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hfe]; ring

theorem II_int {O : Subring F} {ϖ : F} (hϖ : ϖ ∈ O) {a b : ℕ} {X : Matrix (Fin a) (Fin b) F}
    (hX : X ∈ IIset O ϖ) : X ∈ intMat O a b := fun i j => by
  obtain ⟨o, ho, e⟩ := hX i j
  rw [e]; exact O.mul_mem hϖ ho

theorem det_congr {O : Subring F} {ϖ : F} (hϖ : ϖ ∈ O) {n : ℕ} {P Q : Matrix (Fin n) (Fin n) F}
    (hP : P ∈ intMat O n n) (hQ : Q ∈ intMat O n n) (h : P - Q ∈ IIset O ϖ) :
    ∃ o ∈ O, P.det - Q.det = ϖ * o := by
  let P' : Matrix (Fin n) (Fin n) O := fun i j => ⟨P i j, hP i j⟩
  let Q' : Matrix (Fin n) (Fin n) O := fun i j => ⟨Q i j, hQ i j⟩
  let I : Ideal O := Ideal.span {(⟨ϖ, hϖ⟩ : O)}
  have hm : (Ideal.Quotient.mk I).mapMatrix P' = (Ideal.Quotient.mk I).mapMatrix Q' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ?_)
    obtain ⟨o, ho, e⟩ := h i j
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    show o * ϖ = P i j - Q i j
    rw [mul_comm]; exact e.symm
  have hd : Ideal.Quotient.mk I P'.det = Ideal.Quotient.mk I Q'.det := by
    rw [RingHom.map_det, RingHom.map_det, hm]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hd)
  have hPd : P.det = ((P'.det : O) : F) := by
    have e : O.subtype.mapMatrix P' = P := by ext i j; rfl
    have := RingHom.map_det O.subtype P'
    rw [e] at this
    exact this.symm
  have hQd : Q.det = ((Q'.det : O) : F) := by
    have e : O.subtype.mapMatrix Q' = Q := by ext i j; rfl
    have := RingHom.map_det O.subtype Q'
    rw [e] at this
    exact this.symm
  have hv : (a : F) * ϖ = ((P'.det : O) : F) - ((Q'.det : O) : F) := congrArg Subtype.val ha
  exact ⟨a, a.2, by rw [hPd, hQd, ← hv, mul_comm]⟩

theorem nrm_eq_one_of_close {nrm : AbsoluteValue F ℝ}
    (hna : ∀ x y : F, nrm (x + y) ≤ max (nrm x) (nrm y)) {u v : F} (hv : nrm v = 1)
    (h : nrm (u - v) < 1) : nrm u = 1 := by
  apply le_antisymm
  · have := hna (u - v) v
    rw [sub_add_cancel, hv] at this
    exact this.trans (max_le h.le le_rfl)
  · have := hna u (v - u)
    rw [add_sub_cancel, hv, nrm.map_sub v u] at this
    rcases le_max_iff.1 this with h' | h'
    · exact h'
    · exact absurd h (not_lt.2 h')

end Alg

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

def Supp (O : Subring F) (ϖ : F) {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Prop :=
  bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c

theorem Jset_iff (hLF : LF O ϖ nrm q) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    M ∈ Jset (GLint O n) ↔ M ∈ intMat O n n ∧ nrm M.det = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (GlobalTheory.T.mem_integralGL_iff_integral_unit_det hLF n g).1 hg
  · rintro ⟨h, hd⟩
    have hne : M.det ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hd; exact zero_ne_one hd
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hne, ?_, rfl⟩
    exact (GlobalTheory.T.mem_integralGL_iff_integral_unit_det hLF n _).2 ⟨h, hd⟩

theorem step (hLF : LF O ϖ nrm q) (δ : Fˣ →* ℂˣ) (hδ : Del nrm δ) {r d c : ℕ}
    {k : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) {x : Matrix (Fin (r + d)) (Fin (r + c)) F}
    (hx : Supp O ϖ x) :
    Supp O ϖ (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) ∧
      chi0 δ (bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F))).det =
        chi0 δ (bAA x).det * chi0 δ (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det := by
  obtain ⟨-, hϖ, -, hlt, -, hna, -⟩ := NormalisedValue.main hLF
  obtain ⟨e1, e2, e3, e4⟩ := BlockMul.blocks_mul r d c c x (k : Matrix (Fin (r + c)) (Fin (r + c)) F)
  have kint : ∀ i j, (k : Matrix (Fin (r + c)) (Fin (r + c)) F) i j ∈ O := hk.1.1
  have ka : bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ intMat O r r := fun i j => kint _ _
  have kb : bAD (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ intMat O r c := fun i j => kint _ _
  have kd : bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ intMat O c c := fun i j => kint _ _
  have kc : bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ IIset O ϖ := hk.2
  obtain ⟨hA, hC, hB, hD⟩ := hx
  obtain ⟨hAi, hAd⟩ := (Jset_iff hLF _).1 hA
  have hadet : nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 :=
    ((GlobalTheory.T.parahoric_character_modulus_properties hLF δ hδ r c).2.1 k hk).2.1
  have hV := int_mul hAi ka
  have hW := int_mul_II hB kc
  have hU : bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) ∈ intMat O r r := by
    rw [e1]; exact int_add hV (II_int hϖ hW)
  have hdiff : bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) -
      bAA x * bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ IIset O ϖ := by
    rw [e1, add_sub_cancel_left]; exact hW
  obtain ⟨o, ho, hoe⟩ := det_congr hϖ hU hV hdiff
  have hVd : nrm (bAA x * bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 := by
    rw [Matrix.det_mul, map_mul, hAd, hadet, one_mul]
  have hlt' := (hlt _).2 ⟨o, ho, hoe⟩
  have hUd := nrm_eq_one_of_close hna hVd hlt'
  have hUne : (bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F))).det ≠ 0 := fun h => by
    rw [h, map_zero] at hUd; exact zero_ne_one hUd
  have hVne : (bAA x * bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 := fun h => by
    rw [h, map_zero] at hVd; exact zero_ne_one hVd
  refine ⟨⟨(Jset_iff hLF _).2 ⟨hU, hUd⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [e3]; exact II_add (II_mul_int hC ka) (int_mul_II hD kc)
  · rw [e2]; exact int_add (int_mul hAi kb) (int_mul hB kd)
  · rw [e4]; exact int_add (int_mul (II_int hϖ hC) kb) (int_mul hD kd)
  · rw [extendedCharacter_congr_of_tame nrm δ hδ.tame hUne hVne (by rw [hVd]; exact hlt')]
    rw [Matrix.det_mul] at hVne ⊢
    exact unramifiedCharExt_mul δ (left_ne_zero_of_mul hVne) (right_ne_zero_of_mul hVne)

theorem phiQ_eigen : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ},
    LF O ϖ nrm q → ∀ δ : Fˣ →* ℂˣ, Del nrm δ → ∀ r d c : ℕ, ∀ k ∈ parJ O ϖ r c,
    ∀ x : Matrix (Fin (r + d)) (Fin (r + c)) F,
    ((δ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        phiQ O ϖ δ r d c (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) =
      lamJ δ k * phiQ O ϖ δ r d c x := by
  intro F _ _ _ _ O ϖ nrm q hLF δ hδ r d c k hk x
  by_cases hx : Supp O ϖ x
  · obtain ⟨hs, hc⟩ := step hLF δ hδ hk hx
    have hp1 : phiQ O ϖ δ r d c x = (chi0 δ (bAA x).det)⁻¹ := by
      unfold phiQ; exact if_pos hx
    have hp2 : phiQ O ϖ δ r d c (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) =
        (chi0 δ (bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F))).det)⁻¹ := by
      unfold phiQ; exact if_pos hs
    have hdet := ((GlobalTheory.T.parahoric_character_modulus_properties hLF δ hδ r c).2.1 k hk).2.2.2.1
    have hAd := ((Jset_iff hLF _).1 hx.1).2
    have hadet := ((GlobalTheory.T.parahoric_character_modulus_properties hLF δ hδ r c).2.1 k hk).2.1
    have hAne : (bAA x).det ≠ 0 := fun h => by
      rw [h, map_zero] at hAd; exact zero_ne_one hAd
    have hane : (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 := fun h => by
      rw [h, map_zero] at hadet; exact zero_ne_one hadet
    have h1 := unramifiedCharExt_ne_zero δ hAne
    have h2 := unramifiedCharExt_ne_zero δ hane
    rw [hp1, hp2, hc, hdet]
    field_simp
  · have hinv : k⁻¹ ∈ parJ O ϖ r c := by
      obtain ⟨J, hJ, -⟩ := Par.parJ_compact_open hLF r c
      rw [← hJ] at hk ⊢
      exact J.inv_mem hk
    have hs : ¬ Supp O ϖ (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) := fun h => hx (by
      have := (step hLF δ hδ hinv h).1
      rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this)
    have hp1 : phiQ O ϖ δ r d c x = 0 := by
      unfold phiQ; exact if_neg hx
    have hp2 : phiQ O ϖ δ r d c (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) = 0 := by
      unfold phiQ; exact if_neg hs
    rw [hp1, hp2, mul_zero, mul_zero]

end Local

end GlobalTheory.CompanionTheory.QL.Eigen
