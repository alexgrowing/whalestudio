import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIsCompactParahoricGLCompletionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockUpperTriangularGLMulDetInvStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricTypeRCMulInvMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTameStatement
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section
namespace GlobalTheory.TypeStep

section Gen

variable {F : Type} [Field F] {r c : ℕ}

theorem bDA_mul {p q : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    bDA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 :=
  (GlobalTheory.T.blockUpperTriangular_GL_mul_det_inv F r c p q hp hq).1

theorem bAA_mul {p q : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    bAA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) =
      bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) :=
  (GlobalTheory.T.blockUpperTriangular_GL_mul_det_inv F r c p q hp hq).2.1

theorem bDD_mul {p q : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    bDD ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) =
      bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bDD (q : Matrix (Fin (r + c)) (Fin (r + c)) F) :=
  (GlobalTheory.T.blockUpperTriangular_GL_mul_det_inv F r c p q hp hq).2.2.1

theorem det_blocks {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (p : Matrix (Fin (r + c)) (Fin (r + c)) F).det =
      (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det :=
  (GlobalTheory.T.blockUpperTriangular_GL_mul_det_inv F r c p p hp hp).2.2.2.1

theorem bDA_inv {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 :=
  (GlobalTheory.T.blockUpperTriangular_GL_mul_det_inv F r c p p hp hp).2.2.2.2

theorem detA_ne {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 := fun h =>
  p.det_ne_zero (by rw [det_blocks hp, h, zero_mul])

theorem detD_ne {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 := fun h =>
  p.det_ne_zero (by rw [det_blocks hp, h, mul_zero])

theorem bDA_one : bDA ((1 : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
  ext i j
  simp [bDA, Matrix.one_apply, Fin.ext_iff]
  omega

def levA (p : GL (Fin (r + c)) F) : GL (Fin r) F :=
  open Classical in
  if h : (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 then GeneralLinearGroup.mkOfDetNeZero _ h else 1

def levD (p : GL (Fin (r + c)) F) : GL (Fin c) F :=
  open Classical in
  if h : (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 then GeneralLinearGroup.mkOfDetNeZero _ h else 1

theorem levA_val {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (levA p : Matrix (Fin r) (Fin r) F) = bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) := by
  rw [levA, dif_pos (detA_ne hp)]; rfl

theorem levD_val {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (levD p : Matrix (Fin c) (Fin c) F) = bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) := by
  rw [levD, dif_pos (detD_ne hp)]; rfl

theorem lev_mul {p q : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    ((levA (p * q), levD (p * q)) : GL (Fin r) F × GL (Fin c) F) = (levA p, levD p) * (levA q, levD q) := by
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · simp only [Prod.fst_mul, Units.val_mul]
    rw [levA_val (bDA_mul hp hq), levA_val hp, levA_val hq, bAA_mul hp hq]
  · simp only [Prod.snd_mul, Units.val_mul]
    rw [levD_val (bDA_mul hp hq), levD_val hp, levD_val hq, bDD_mul hp hq]

theorem unitCharExtendedByZero_mul (δ : Fˣ →* ℂˣ) (x y : F) : chi0 δ (x * y) = chi0 δ x * chi0 δ y := by
  by_cases hx : x = 0
  · simp [chi0, hx]
  by_cases hy : y = 0
  · simp [chi0, hy]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  simp only [chi0, dif_neg hx, dif_neg hy, dif_neg hxy]
  rw [← Units.val_mul, ← map_mul]
  congr 3
  ext; simp

def chiP (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ) (p : GL (Fin (r + c)) F) : ℂ :=
  ((nrm (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ^ ((c : ℝ) / 2) *
    nrm (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ^ (-(r : ℝ) / 2) : ℝ) : ℂ) *
    chi0 δ (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det

theorem chiP_mul (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ) {p q : GL (Fin (r + c)) F}
    (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    chiP nrm δ (p * q) = chiP nrm δ p * chiP nrm δ q := by
  unfold chiP
  rw [bAA_mul hp hq, bDD_mul hp hq, det_mul, det_mul, map_mul, map_mul, unitCharExtendedByZero_mul,
    Real.mul_rpow (nrm.nonneg _) (nrm.nonneg _), Real.mul_rpow (nrm.nonneg _) (nrm.nonneg _)]
  push_cast
  ring

end Gen

section Constr

variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ) {r c : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (ρ : GL (Fin r) F × GL (Fin c) F →* (V ≃ₗᵢ[ℂ] V)) (v₀ : V)

def PJset (r c : ℕ) : Set (GL (Fin (r + c)) F) :=
  {g | ∃ p : GL (Fin (r + c)) F, bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 ∧ ∃ k ∈ parJ O ϖ r c, g = p * k}

def fvec (g : GL (Fin (r + c)) F) : V :=
  open Classical in
  if h : g ∈ PJset O ϖ r c then
    (chiP nrm δ h.choose * lamJ δ h.choose_spec.2.choose) • ρ (levA h.choose, levD h.choose) v₀
  else 0

variable {O ϖ nrm δ ρ v₀}

theorem cons (hgrp : ∀ k k' : GL (Fin (r + c)) F, k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c →
      k * k' ∈ parJ O ϖ r c ∧ k⁻¹ ∈ parJ O ϖ r c)
    (hlam : ∀ k k' : GL (Fin (r + c)) F, k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c →
      lamJ δ (k * k') = lamJ δ k * lamJ δ k')
    (hfix : ∀ q : GL (Fin (r + c)) F, q ∈ parJ O ϖ r c → bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 →
      ρ (levA q, levD q) v₀ = v₀ ∧ chiP nrm δ q = lamJ δ q)
    {p p' k k' : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hp' : bDA (p' : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) (hk : k ∈ parJ O ϖ r c) (hk' : k' ∈ parJ O ϖ r c)
    (e : p * k = p' * k') :
    (chiP nrm δ p * lamJ δ k) • ρ (levA p, levD p) v₀ = (chiP nrm δ p' * lamJ δ k') • ρ (levA p', levD p') v₀ := by
  obtain ⟨q, rfl⟩ : ∃ q, p = p' * q := ⟨p'⁻¹ * p, by simp⟩
  have hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
    have := bDA_mul (bDA_inv hp') hp
    simpa using this
  have hkq : k' = q * k := (mul_left_cancel (a := p') (by rw [← mul_assoc]; exact e)).symm
  have hqJ : q ∈ parJ O ϖ r c := by
    have : q = k' * k⁻¹ := by rw [hkq]; simp
    rw [this]
    exact (hgrp _ _ hk' (hgrp _ _ hk hk).2).1
  obtain ⟨h1, h2⟩ := hfix q hqJ hq
  rw [chiP_mul nrm δ hp' hq, lev_mul hp' hq, hkq, hlam _ _ hqJ hk, map_mul]
  show (chiP nrm δ p' * chiP nrm δ q * lamJ δ k) • (ρ (levA p', levD p')) ((ρ (levA q, levD q)) v₀) = _
  rw [h1, h2, mul_assoc]

end Constr

section Mem

variable {F : Type} [Field F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {δ : Fˣ →* ℂˣ} {r c : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ρ : GL (Fin r) F × GL (Fin c) F →* (V ≃ₗᵢ[ℂ] V)} {v₀ : V}
  (hgrp : ∀ k k' : GL (Fin (r + c)) F, k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c →
      k * k' ∈ parJ O ϖ r c ∧ k⁻¹ ∈ parJ O ϖ r c)
  (hlam : ∀ k k' : GL (Fin (r + c)) F, k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c →
      lamJ δ (k * k') = lamJ δ k * lamJ δ k')
  (hfix : ∀ q : GL (Fin (r + c)) F, q ∈ parJ O ϖ r c → bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 →
      ρ (levA q, levD q) v₀ = v₀ ∧ chiP nrm δ q = lamJ δ q)

include hgrp hlam hfix in
theorem fvec_eq {p k : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hk : k ∈ parJ O ϖ r c) :
    fvec O ϖ nrm δ ρ v₀ (p * k) = (chiP nrm δ p * lamJ δ k) • ρ (levA p, levD p) v₀ := by
  have h : p * k ∈ PJset O ϖ r c := ⟨p, hp, k, hk, rfl⟩
  rw [fvec, dif_pos h]
  have h2 := h.choose_spec.2.choose_spec.1
  have h3 := h.choose_spec.2.choose_spec.2
  exact cons hgrp hlam hfix h.choose_spec.1 hp h2 hk h3.symm

include hgrp in
theorem fvec_out {g : GL (Fin (r + c)) F} (hg : g ∉ PJset O ϖ r c) : fvec O ϖ nrm δ ρ v₀ g = 0 := by
  rw [fvec, dif_neg hg]

include hgrp in
theorem mul_mem_PJ_iff {p g : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    p * g ∈ PJset O ϖ r c ↔ g ∈ PJset O ϖ r c := by
  constructor
  · rintro ⟨p₁, hp₁, k₁, hk₁, e⟩
    refine ⟨p⁻¹ * p₁, bDA_mul (bDA_inv hp) hp₁, k₁, hk₁, ?_⟩
    rw [mul_assoc, ← e]; simp
  · rintro ⟨p₁, hp₁, k₁, hk₁, rfl⟩
    exact ⟨p * p₁, bDA_mul hp hp₁, k₁, hk₁, by rw [mul_assoc]⟩

include hgrp in
theorem mul_mem_PJ_iff' {k g : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) :
    g * k ∈ PJset O ϖ r c ↔ g ∈ PJset O ϖ r c := by
  constructor
  · rintro ⟨p₁, hp₁, k₁, hk₁, e⟩
    refine ⟨p₁, hp₁, k₁ * k⁻¹, (hgrp _ _ hk₁ (hgrp _ _ hk hk).2).1, ?_⟩
    rw [← mul_assoc, ← e]; simp
  · rintro ⟨p₁, hp₁, k₁, hk₁, rfl⟩
    exact ⟨p₁, hp₁, k₁ * k, (hgrp _ _ hk₁ hk).1, by rw [mul_assoc]⟩

theorem unitCharExtendedByZero_det_eq_char_det (m : GL (Fin c) F) :
    chi0 δ (m : Matrix (Fin c) (Fin c) F).det = ((δ (Matrix.GeneralLinearGroup.det m) : ℂˣ) : ℂ) := by
  have h : (m : Matrix (Fin c) (Fin c) F).det ≠ 0 := m.det_ne_zero
  rw [chi0, dif_neg h]
  congr 2
  exact Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply])

include hgrp hlam hfix in
theorem fvec_mem : fvec O ϖ nrm δ ρ v₀ ∈ typeSp O ϖ nrm δ r c ρ := by
  refine ⟨fun p m₁ m₂ hp h1 h2 g => ?_, fun k hk g => ?_⟩
  · have e1 : m₁ = levA p := Units.ext ((levA_val hp).trans h1).symm
    have e2 : m₂ = levD p := Units.ext ((levD_val hp).trans h2).symm
    have hs : (((nrm (m₁ : Matrix (Fin r) (Fin r) F).det ^ ((c : ℝ) / 2) *
          nrm (m₂ : Matrix (Fin c) (Fin c) F).det ^ (-(r : ℝ) / 2) : ℝ) : ℂ) *
        ((δ (Matrix.GeneralLinearGroup.det m₂) : ℂˣ) : ℂ)) = chiP nrm δ p := by
      rw [chiP, ← unitCharExtendedByZero_det_eq_char_det, h1, h2]
    rw [hs, e1, e2]
    by_cases hg : g ∈ PJset O ϖ r c
    · obtain ⟨p₀, hp₀, k₀, hk₀, rfl⟩ := hg
      rw [← mul_assoc, fvec_eq hgrp hlam hfix (bDA_mul hp hp₀) hk₀, fvec_eq hgrp hlam hfix hp₀ hk₀,
        chiP_mul nrm δ hp hp₀, lev_mul hp hp₀, map_mul, map_smul, smul_smul]
      rw [mul_assoc]
      rfl
    · rw [fvec_out hgrp hg, fvec_out hgrp (fun h => hg ((mul_mem_PJ_iff hgrp hp).1 h)), map_zero, smul_zero]
  · by_cases hg : g ∈ PJset O ϖ r c
    · obtain ⟨p₀, hp₀, k₀, hk₀, rfl⟩ := hg
      rw [mul_assoc, fvec_eq hgrp hlam hfix hp₀ (hgrp _ _ hk₀ hk).1, fvec_eq hgrp hlam hfix hp₀ hk₀, smul_smul,
        hlam _ _ hk₀ hk]
      congr 1
      ring
    · rw [fvec_out hgrp hg, fvec_out hgrp (fun h => hg ((mul_mem_PJ_iff' hgrp hk).1 h)), smul_zero]

end Mem

section Adic

theorem det_mem_of_int {F : Type} [Field F] {O : Subring F} {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (h : ∀ a b, M a b ∈ O) : M.det ∈ O := by
  let M' : Matrix (Fin n) (Fin n) O := fun i j => ⟨M i j, h i j⟩
  have e : M = O.subtype.mapMatrix M' := rfl
  rw [e, ← RingHom.map_det]
  exact (M'.det).2

theorem bAA_one {F : Type} [Field F] {r c : ℕ} :
    bAA ((1 : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
  ext i j
  simp [bAA, Matrix.one_apply, Fin.ext_iff]

theorem bDD_one {F : Type} [Field F] {r c : ℕ} :
    bDD ((1 : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
  ext i j
  simp [bDD, Matrix.one_apply, Fin.ext_iff]

theorem lev_inv {F : Type} [Field F] {r c : ℕ} {q : GL (Fin (r + c)) F}
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (levA q)⁻¹ = levA q⁻¹ ∧ (levD q)⁻¹ = levD q⁻¹ := by
  have h := lev_mul hq (bDA_inv hq)
  have hA : levA (q * q⁻¹) = 1 := Units.ext (by rw [mul_inv_cancel, levA_val bDA_one, bAA_one]; rfl)
  have hD : levD (q * q⁻¹) = 1 := Units.ext (by rw [mul_inv_cancel, levD_val bDA_one, bDD_one]; rfl)
  rw [hA, hD] at h
  exact ⟨(eq_inv_of_mul_eq_one_right (congrArg Prod.fst h).symm).symm,
    (eq_inv_of_mul_eq_one_right (congrArg Prod.snd h).symm).symm⟩

theorem lev_mem_GLint {F : Type} [Field F] {O : Subring F} {r c : ℕ} {q : GL (Fin (r + c)) F}
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) (hK : q ∈ GLint O (r + c)) :
    levA q ∈ GLint O r ∧ levD q ∈ GLint O c := by
  have hK' : q⁻¹ ∈ GLint O (r + c) := inv_mem hK
  obtain ⟨e1, e2⟩ := lev_inv hq
  refine ⟨⟨fun a b => ?_, fun a b => ?_⟩, ⟨fun a b => ?_, fun a b => ?_⟩⟩
  · rw [levA_val hq]; exact hK.1 _ _
  · rw [e1, levA_val (bDA_inv hq)]; exact hK'.1 _ _
  · rw [levD_val hq]; exact hK.1 _ _
  · rw [e2, levD_val (bDA_inv hq)]; exact hK'.1 _ _

variable {L : Type} [Field L] [NumberField L]

theorem nrm_det_GLint {P : HeightOneSpectrum (𝓞 L)} {nrm : AbsoluteValue (P.adicCompletion L) ℝ} (hn : IsNrm P nrm)
    {n : ℕ} {m : GL (Fin n) (P.adicCompletion L)} (hm : m ∈ GLint (OP P) n) :
    nrm (m : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det = 1 := by
  have h1 : Valued.v (m : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det ≤ 1 := det_mem_of_int hm.1
  have h2 : Valued.v ((m⁻¹ : GL (Fin n) (P.adicCompletion L)) : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det ≤ 1 :=
    det_mem_of_int hm.2
  have e : ((m⁻¹ : GL (Fin n) (P.adicCompletion L)) : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det =
      ((m : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [e, map_inv₀] at h2
  have h0 : Valued.v (m : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det ≠ 0 := by
    simp [m.det_ne_zero]
  have hv : Valued.v (m : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det = 1 :=
    le_antisymm h1 (by
      by_contra hc
      push_neg at hc
      have := one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 h0, hc⟩
      exact absurd h2 (not_le.2 this))
  exact (hn (Units.mk0 _ m.det_ne_zero)).1 hv

end Adic

section Final

variable {L : Type} [Field L] [NumberField L]

theorem norm_unitCharExtendedByZero_eq_one {P : HeightOneSpectrum (𝓞 L)} {δ : (P.adicCompletion L)ˣ →* ℂˣ} (hδ : IsDel P δ)
    {x : P.adicCompletion L} (hx : x ≠ 0) : ‖chi0 δ x‖ = 1 := by
  rw [chi0, dif_neg hx]
  exact hδ.unitary _

theorem piP_mem (P : HeightOneSpectrum (𝓞 L)) : (piP P : P.adicCompletion L) ∈ OP P := by
  show Valued.v (piP P : P.adicCompletion L) ≤ 1
  have h : Valued.v (piP P : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec P
  rw [h, ← WithZero.exp_zero]
  exact WithZero.exp_le_exp.2 (by norm_num)

theorem exists_typeVec (P : HeightOneSpectrum (𝓞 L)) (δ : (P.adicCompletion L)ˣ →* ℂˣ) (hδ : IsDel P δ)
    (nrm : AbsoluteValue (P.adicCompletion L) ℝ) (hn : IsNrm P nrm) (r c : ℕ)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : GL (Fin r) (P.adicCompletion L) × GL (Fin c) (P.adicCompletion L) →* (V ≃ₗᵢ[ℂ] V)) (v₀ : V) (hv : ‖v₀‖ = 1)
    (hfix₀ : ∀ k₁ ∈ GLint (OP P) r, ∀ k₂ ∈ GLint (OP P) c, ρ (k₁, k₂) v₀ = v₀) :
    ∃ f ∈ typeSp (OP P) (piP P : P.adicCompletion L) nrm δ r c ρ, ∃ U : Set (GL (Fin (r + c)) (P.adicCompletion L)),
      IsOpen U ∧ parJ (OP P) (piP P : P.adicCompletion L) r c ⊆ U ∧
      ∀ k ∈ GLint (OP P) (r + c), ‖f k‖ = U.indicator 1 k := by
  have hgrp := GlobalTheory.T.parahoricTypeRC_mul_inv_mem (P.adicCompletion L) (OP P) (piP P : P.adicCompletion L) (piP_mem P) r c
  have hlam := GlobalTheory.T.parahoricCharacter_mul_of_tame L P δ hδ r c
  have hfix : ∀ q : GL (Fin (r + c)) (P.adicCompletion L), q ∈ parJ (OP P) (piP P : P.adicCompletion L) r c →
      bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) = 0 →
      ρ (levA q, levD q) v₀ = v₀ ∧ chiP nrm δ q = lamJ δ q := by
    intro q hq h0
    obtain ⟨h1, h2⟩ := lev_mem_GLint h0 hq.1
    refine ⟨hfix₀ _ h1 _ h2, ?_⟩
    rw [chiP, lamJ, ← levA_val h0, ← levD_val h0, nrm_det_GLint hn h1, nrm_det_GLint hn h2]
    simp
  have hlam1 : lamJ δ (1 : GL (Fin (r + c)) (P.adicCompletion L)) = 1 := by
    rw [lamJ, bDD_one, det_one, chi0, dif_neg one_ne_zero]
    have : Units.mk0 (1 : P.adicCompletion L) one_ne_zero = 1 := Units.ext rfl
    rw [this, map_one, Units.val_one]
  refine ⟨fvec (OP P) (piP P : P.adicCompletion L) nrm δ ρ v₀, fvec_mem hgrp hlam hfix,
    PJset (OP P) (piP P : P.adicCompletion L) r c, ?_, fun k hk => ⟨1, bDA_one, k, hk, (one_mul k).symm⟩,
    fun k hk => ?_⟩
  · have ho := (GlobalTheory.T.isOpen_isCompact_parahoric_GL_completion L P r c).1
    have e : PJset (OP P) (piP P : P.adicCompletion L) r c = ⋃ p : {p : GL (Fin (r + c)) (P.adicCompletion L) //
        bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) = 0},
        (fun g => p.1 * g) '' parJ (OP P) (piP P : P.adicCompletion L) r c := by
      ext g
      simp only [Set.mem_iUnion, Set.mem_image]
      constructor
      · rintro ⟨p, hp, k, hk, rfl⟩; exact ⟨⟨p, hp⟩, k, hk, rfl⟩
      · rintro ⟨⟨p, hp⟩, k, hk, rfl⟩; exact ⟨p, hp, k, hk, rfl⟩
    rw [e]
    exact isOpen_iUnion fun p => (Homeomorph.mulLeft p.1).isOpenMap _ ho
  · by_cases hg : k ∈ PJset (OP P) (piP P : P.adicCompletion L) r c
    · rw [Set.indicator_of_mem hg, Pi.one_apply]
      obtain ⟨p, hp, k₀, hk₀, rfl⟩ := hg
      rw [fvec_eq hgrp hlam hfix hp hk₀, norm_smul, LinearIsometryEquiv.norm_map, hv, mul_one, norm_mul]
      have hpK : p ∈ GLint (OP P) (r + c) := by
        have : p = p * k₀ * k₀⁻¹ := by simp
        rw [this]; exact mul_mem hk (inv_mem hk₀.1)
      obtain ⟨h1, h2⟩ := lev_mem_GLint hp hpK
      have hc : ‖chiP nrm δ p‖ = 1 := by
        rw [chiP, ← levA_val hp, ← levD_val hp, nrm_det_GLint hn h1, nrm_det_GLint hn h2]
        simp only [Real.one_rpow, mul_one, Complex.ofReal_one, one_mul]
        exact norm_unitCharExtendedByZero_eq_one hδ (levD p).det_ne_zero
      have hl : ‖lamJ δ k₀‖ = 1 := by
        have e := hlam _ _ hk₀ (hgrp _ _ hk₀ hk₀).2
        rw [mul_inv_cancel, hlam1] at e
        have hne : (bDD (k₀ : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det ≠ 0 := by
          intro h0
          simp only [lamJ] at e
          rw [h0] at e
          simp [chi0] at e
        exact norm_unitCharExtendedByZero_eq_one hδ hne
      rw [hc, hl, mul_one]
    · rw [Set.indicator_of_notMem hg, fvec_out hgrp hg, norm_zero]

end Final

section Haar

variable {L : Type} [Field L] [NumberField L]

theorem one_mem_parJ (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ) :
    (1 : GL (Fin (r + c)) (P.adicCompletion L)) ∈ parJ (OP P) (piP P : P.adicCompletion L) r c := by
  refine ⟨one_mem _, fun i j => ⟨0, (OP P).zero_mem, ?_⟩⟩
  simp [bDA, Matrix.one_apply, Fin.ext_iff]
  omega
theorem KO_eq_GLint (P : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    letI := GlobalTheory.LocalData.complRel P
    GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin n) = GLint (OP P) n := by
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (P.adicCompletion L))
    (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ)))
  ext g
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  simp only [he.le_one_iff_le_one, Valuation.mem_integer_iff]
  exact Iff.rfl

theorem isCompact_GLint (P : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    IsCompact (GLint (OP P) n : Set (GL (Fin n) (P.adicCompletion L))) := by
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  rw [← KO_eq_GLint]
  exact GlobalTheory.SplitFlip.isCompact_KO

theorem isOpen_GLint (P : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    IsOpen (GLint (OP P) n : Set (GL (Fin n) (P.adicCompletion L))) := by
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  rw [← KO_eq_GLint]
  exact GlobalTheory.SplitFlip.isOpen_KO

theorem exists_haar_parJ (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ) :
    letI : MeasurableSpace (P.adicCompletion L) := borel _
    ∃ μ : Measure (GL (Fin (r + c)) (P.adicCompletion L)), μ.IsMulLeftInvariant ∧
      μ (parJ (OP P) (piP P : P.adicCompletion L) r c) = 1 ∧ μ (GLint (OP P) (r + c)) < ⊤ := by
  letI : MeasurableSpace (P.adicCompletion L) := borel _
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  obtain ⟨ho, hc⟩ := GlobalTheory.T.isOpen_isCompact_parahoric_GL_completion L P r c
  let K₀ : TopologicalSpace.PositiveCompacts (GL (Fin (r + c)) (P.adicCompletion L)) :=
    ⟨⟨_, hc⟩, by
      rw [ho.interior_eq]
      exact ⟨1, one_mem_parJ P r c⟩⟩
  refine ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self, ?_⟩
  exact (isCompact_GLint P _).measure_lt_top

end Haar

theorem exists_typeDim_step : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P → ∀ (δ : (P.adicCompletion L)ˣ →* ℂˣ) (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → (∀ i, IsNu P (ν i)) → ∀ r t j : ℕ, 1 ≤ t → (∃ n, TypeDimAt P δ ν r t j n) ∧ ∃ z, StepAt P δ ν r t j z := by
  intro L _ _ P _ δ ν hδ hν r t j ht
  obtain ⟨nrm, hn⟩ := GlobalTheory.Mem.NrmCompl.exists_isNrm L P
  obtain ⟨V, i1, i2, ρ, hρ⟩ := GlobalTheory.SphCyclic.exists_isUnrM L P nrm hn ν hν r t j ht
  refine ⟨⟨_, nrm, hn, V, i1, i2, ρ, hρ, rfl⟩, ?_⟩
  letI : MeasurableSpace (P.adicCompletion L) := borel _
  obtain ⟨v₀, hv, hfix, -⟩ := hρ.sph
  obtain ⟨f, hf, U, hU, hJU, hfn⟩ := exists_typeVec P δ hδ nrm hn r (j * t) ρ v₀ hv hfix
  obtain ⟨μ, hμ, hμ1, hμK⟩ := exists_haar_parJ P r (j * t)
  obtain ⟨dx, hdx, -, hdx1⟩ := GlobalTheory.HaarMat.exists_haar_intMat L P (r + (j + 1) * t) (r + j * t)
  set K : Set (GL (Fin (r + j * t)) (P.adicCompletion L)) := ((GLint (OP P) (r + j * t) : Subgroup _) : Set (GL (Fin (r + j * t)) (P.adicCompletion L)))
  have hUm : MeasurableSet U := hU.measurableSet
  have hsub : parJ (OP P) (piP P : P.adicCompletion L) r (j * t) ⊆ K ∩ U := fun x hx => ⟨hx.1, hJU hx⟩
  have hc1 : 1 ≤ μ (K ∩ U) := hμ1 ▸ measure_mono hsub
  have hcT : μ (K ∩ U) < ⊤ := (measure_mono Set.inter_subset_left).trans_lt hμK
  set c : ℝ := μ.real (K ∩ U)
  have hcpos : 0 < c := ENNReal.toReal_pos (by positivity) hcT.ne
  have key : ∀ (g : GL (Fin (r + j * t)) (P.adicCompletion L) → V) (a : ℝ),
      (∀ k ∈ K, ‖g k‖ = a * U.indicator 1 k) → mcoef (OP P) μ g 1 = ((a ^ 2 * c : ℝ) : ℂ) := by
    intro g a hg
    unfold mcoef
    have e : ∀ k ∈ K, inner ℂ (g k) (g (k * 1)) =
        ((U.indicator (fun _ => a ^ 2) k : ℝ) : ℂ) := by
      intro k hk
      rw [mul_one, inner_self_eq_norm_sq_to_K, hg k hk]
      by_cases h : k ∈ U <;> simp [h]
    rw [setIntegral_congr_fun (isOpen_GLint P _).measurableSet e, integral_complex_ofReal,
      setIntegral_indicator hUm, setIntegral_const, smul_eq_mul, mul_comm]
  refine ⟨_, nrm, hn, V, i1, i2, ρ, hρ, ((c ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • f, Submodule.smul_mem _ _ hf, μ, dx, hμ, hμ1, ?_,
    hdx, hdx1, rfl⟩
  rw [key _ (c ^ (-(1 / 2 : ℝ))) (fun k hk => ?_)]
  · have h2 : (c ^ (-(1 / 2 : ℝ))) ^ 2 = c⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hcpos.le]
      norm_num
      exact Real.rpow_neg_one c
    rw [h2, inv_mul_cancel₀ hcpos.ne', Complex.ofReal_one]
  · rw [Pi.smul_apply, norm_smul, hfn k hk, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hcpos.le _)]

end GlobalTheory.TypeStep
