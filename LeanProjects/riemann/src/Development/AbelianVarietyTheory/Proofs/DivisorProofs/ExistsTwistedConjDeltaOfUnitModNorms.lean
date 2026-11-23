import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMulLeftGeneratorEqMapSymmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjOfCharpolyEqOfCharpolySeparableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFormOfUnitaryGeneratorInvariantFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormGramAsymmetryForcesBetaRelationStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.ClSurj

section Theta

variable {R : Type} [CommRing R] {n : ℕ}

theorem Phi_transpose' : (GlobalTheory.Tw.Phi n R)ᵀ = (-1 : R) ^ (n + 1) • GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + j + 1 = n
  · rw [if_pos h, if_pos (by omega), ← pow_add, show n + 1 + i = j + 2 * (i + 1) by omega, pow_add, pow_mul]
    simp
  · rw [if_neg h, if_neg (by omega), mul_zero]

theorem PhiU_inv_val : ((PhiU n R)⁻¹ : GL (Fin n) R).val = (GlobalTheory.Tw.Phi n R)ᵀ := rfl

theorem invT_invT (g : GL (Fin n) R) : invT n R (invT n R g) = g := by
  apply Units.ext
  show (((invT n R g)⁻¹ : GL (Fin n) R).val)ᵀ = g.val
  rw [← map_inv]
  show (((g⁻¹)⁻¹ : GL (Fin n) R).val)ᵀᵀ = g.val
  rw [inv_inv, transpose_transpose]

theorem map_invT (c : R →+* R) (g : GL (Fin n) R) :
    GeneralLinearGroup.map c (invT n R g) = invT n R (GeneralLinearGroup.map c g) := by
  apply Units.ext
  show c.mapMatrix (((g⁻¹ : GL (Fin n) R).val)ᵀ) = (((GeneralLinearGroup.map c g)⁻¹ : GL (Fin n) R).val)ᵀ
  rw [← map_inv]
  rfl

theorem map_map_self (c : R →+* R) (hc : ∀ x, c (c x) = x) (g : GL (Fin n) R) :
    GeneralLinearGroup.map c (GeneralLinearGroup.map c g) = g :=
  Units.ext (Matrix.ext fun i j => hc (g.val i j))

theorem map_PhiU' (c : R →+* R) : GeneralLinearGroup.map c (PhiU n R) = PhiU n R := by
  apply Units.ext
  ext i j
  change c (GlobalTheory.Tw.Phi n R i j) = GlobalTheory.Tw.Phi n R i j
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem invT_PhiU : invT n R (PhiU n R) = PhiU n R :=
  Units.ext (Matrix.transpose_transpose _)

theorem PhiU_mul_self_val : (PhiU n R * PhiU n R).val = (-1 : R) ^ (n + 1) • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : GlobalTheory.Tw.Phi n R * (GlobalTheory.Tw.Phi n R)ᵀ = 1 := Phi_mul_transpose n R
  rw [Phi_transpose', Matrix.mul_smul] at h1
  have hs : ((-1 : R) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; simp
  show GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R = _
  calc GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R = ((-1 : R) ^ (n + 1) * (-1) ^ (n + 1)) • (GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R) := by
        rw [hs, one_smul]
    _ = (-1 : R) ^ (n + 1) • (1 : Matrix (Fin n) (Fin n) R) := by rw [mul_smul, h1]

theorem PhiU_sq_central (g : GL (Fin n) R) : g * (PhiU n R * PhiU n R) = (PhiU n R * PhiU n R) * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul _ g, PhiU_mul_self_val]
  simp

theorem mul_inv_mul_cancel_comm {G : Type} [Group G] (a b P : G) (hP : ∀ g : G, g * (P * P) = (P * P) * g) :
    (a * P * b * P⁻¹)⁻¹ * (a * P) * (b * P * a * P⁻¹) = a * P := by
  have h : (a * P * b * P⁻¹)⁻¹ * (a * P) * (b * P * a * P⁻¹) = (P * P) * a * P⁻¹ := by group
  rw [h, ← hP a]
  group

end Theta

theorem normId : ∀ (R : Type) [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ (m : ℕ) (y : GL (Fin m) R),
    ((y * thetaGL m c y).val)ᵀ * (invT m R (y * PhiU m R)).val * c.mapMatrix (y * thetaGL m c y).val =
      (invT m R (y * PhiU m R)).val ∧
    c.mapMatrix (invT m R (y * PhiU m R)).val = (-1 : R) ^ (m - 1) • ((invT m R (y * PhiU m R)).valᵀ * (y * thetaGL m c y).val) := by
  intro R _ c hc m y
  have hth : thetaGL m c y = PhiU m R * invT m R (GeneralLinearGroup.map c y) * (PhiU m R)⁻¹ := rfl
  constructor
  · have ht : ((y * thetaGL m c y).val)ᵀ = (invT m R (y * thetaGL m c y)⁻¹).val := by
      show _ = ((((y * thetaGL m c y)⁻¹)⁻¹ : GL (Fin m) R).val)ᵀ
      rw [inv_inv]
    have hm : c.mapMatrix (y * thetaGL m c y).val = (GeneralLinearGroup.map c (y * thetaGL m c y)).val := rfl
    rw [ht, hm, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [hth]
    simp only [map_mul, map_inv, invT_invT, invT_PhiU, map_PhiU', map_invT, map_map_self c hc]
    have := mul_inv_mul_cancel_comm (invT m R y) (GeneralLinearGroup.map c y) (PhiU m R) PhiU_sq_central
    simpa only [mul_assoc] using this
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Subsingleton.elim _ _
    have h1 : c.mapMatrix (invT m R (y * PhiU m R)).val = (invT m R (GeneralLinearGroup.map c y) * PhiU m R).val := by
      show (GeneralLinearGroup.map c (invT m R (y * PhiU m R))).val = _
      rw [map_invT, map_mul, map_PhiU', map_mul, invT_PhiU]
    have h2 : (invT m R (y * PhiU m R)).valᵀ = ((y * PhiU m R)⁻¹).val := transpose_transpose _
    have h3 : (y * PhiU m R)⁻¹ * (y * thetaGL m c y) = invT m R (GeneralLinearGroup.map c y) * (PhiU m R)⁻¹ := by
      rw [hth]; group
    rw [h1, h2, ← Units.val_mul, h3, Units.val_mul, Units.val_mul, PhiU_inv_val, Phi_transpose', Matrix.mul_smul,
      smul_smul, ← pow_add]
    have : m - 1 + (m + 1) = 2 * m := by omega
    rw [this, pow_mul]
    simp
    rfl

theorem exists_twConj_dlt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (Q : (w.adicCompletion E)[X]), Q.Separable → aeval u (Q.map e.symm.toRingHom) = 0 → Algebra.adjoin K.E {u} = ⊤ → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) → (∀ x : B.Aˣ, IsUnit (GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x))) → ∀ y : GLw m w, (nrmL m w y).val.charpoly = Q → ∃ x : B.Aˣ, B.σ (x : B.A) = x ∧ ∃ g : GLw m w, y = g⁻¹ * GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x) * thL m w g := by
  intro E _ _ _ hE w hw K e he hO hval B m b u Q hQ hu hadj β₀ hβ₀ _ y hy
  have hcc : ∀ z, cj w (cj w z) = z := fun z => by
    obtain ⟨x, rfl⟩ := e.surjective z
    rw [← he, ← he, K.c_c]
  have hth : thL m w = thetaGL m (cj w) := by rw [thL, if_neg hw]
  have hnr : nrmL m w y = y * thetaGL m (cj w) y := by rw [nrmL, if_neg hw]

  have huu : u * B.σ u = 1 := by
    have h := congrArg B.σ hβ₀
    rw [B.σ_σ, map_mul, hβ₀, map_mul, map_pow, map_neg, map_one] at h
    have hε : ((-1 : B.A) ^ (m - 1)) * (-1) ^ (m - 1) = 1 := by rw [← mul_pow]; simp
    have h2 : (β₀ : B.A) * (u * B.σ u) = β₀ * 1 := by
      linear_combination (-1 : B.A) * h - ((β₀ : B.A) * u * B.σ u) * hε
    exact (Units.mul_right_inj β₀).1 h2

  have hQm : Q.Monic := hy ▸ Matrix.charpoly_monic _
  have hQd : Q.natDegree = m := by rw [← hy, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hfin : Module.finrank K.E B.A = Q.natDegree := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin, hQd]
  have hcp := GlobalTheory.T.charpoly_mulLeft_generator_eq_map_symm K B _ e u Q hQm hadj hu hfin
  have hU : (GlobalTheory.TwLat.mulMat e b u).charpoly = Q := by
    have : GlobalTheory.TwLat.mulMat e b u = (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map (e : K.E →+* w.adicCompletion E) := rfl
    rw [this, Matrix.charpoly_map, LinearMap.charpoly_toMatrix, hcp, Polynomial.map_map]
    have hid : (e : K.E →+* w.adicCompletion E).comp e.symm.toRingHom = RingHom.id _ := by
      ext z; simp
    rw [hid, Polynomial.map_id]

  let B' : GlobalTheory.UnitLemma.InvAlg K := { B with g := u }
  have hP' : B'.P.Separable := by
    show (LinearMap.mulLeft K.E u).charpoly.Separable
    rw [hcp]; exact hQ.map
  have hnd : (Algebra.traceForm K.E B.A).Nondegenerate := GlobalTheory.UnitLemma.Sandwich.traceForm_nondegenerate B' hP'

  obtain ⟨P, hP⟩ := GlobalTheory.T.conj_of_charpoly_eq_of_charpoly_separable _ m (nrmL m w y).val (GlobalTheory.TwLat.mulMat e b u) (by rw [hy, hU]) (by rw [hy]; exact hQ)
  rw [hnr] at hP
  obtain ⟨hn1, hn2⟩ := normId _ (cj w) hcc m y
  set N := (y * thetaGL m (cj w) y).val with hN
  set U := GlobalTheory.TwLat.mulMat e b u with hUdef
  set Gy := (invT m _ (y * PhiU m _)).val with hGy
  set cm := (cj w).mapMatrix (m := Fin m) with hcm
  let Gu : GLw m w := invT m _ P⁻¹ * invT m _ (y * PhiU m _) * GeneralLinearGroup.map (cj w) P
  have hPt : (invT m _ P⁻¹).val = P.valᵀ := by
    show ((P⁻¹)⁻¹ : GLw m w).valᵀ = _
    rw [inv_inv]
  have hGu : Gu.val = P.valᵀ * Gy * cm P.val := by
    show (invT m _ P⁻¹).val * Gy * cm P.val = _
    rw [hPt]
  have h1 : Uᵀ * P.valᵀ = P.valᵀ * Nᵀ := by rw [← transpose_mul, ← transpose_mul, hP]
  have h2 : cm P.val * cm U = cm N * cm P.val := by rw [← map_mul, ← map_mul, hP]
  have hinv : Uᵀ * Gu.val * cm U = Gu.val := by
    rw [hGu]
    calc Uᵀ * (P.valᵀ * Gy * cm P.val) * cm U = (Uᵀ * P.valᵀ) * Gy * (cm P.val * cm U) := by
          simp only [Matrix.mul_assoc]
      _ = P.valᵀ * (Nᵀ * Gy * cm N) * cm P.val := by rw [h1, h2]; simp only [Matrix.mul_assoc]
      _ = P.valᵀ * Gy * cm P.val := by rw [hn1]
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_traceForm_of_unitaryGenerator_invariant_form E w K e he B m b u hadj huu hnd Gu.val hinv
  have hsym : cm (GlobalTheory.TwLat.gram e b β) = (-1 : w.adicCompletion E) ^ (m - 1) • ((GlobalTheory.TwLat.gram e b β)ᵀ * U) := by
    rw [hβ, hGu, map_mul, map_mul, hn2]
    have hcP : cm (P.valᵀ) = (cm P.val)ᵀ := rfl
    have hcc' : cm (cm P.val) = P.val := Matrix.ext fun i j => hcc (P.val i j)
    rw [hcP, hcc', transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc, hP]
  have hGunit : IsUnit (GlobalTheory.TwLat.gram e b β) := hβ ▸ Gu.isUnit
  obtain ⟨hσβ, hβu⟩ := GlobalTheory.T.traceFormGram_asymmetry_forces_beta_relation E w K e he B m b u β hnd hGunit hsym
  refine ⟨β₀⁻¹ * hβu.unit, ?_, P⁻¹, ?_⟩
  · have hi : (((β₀⁻¹ : B.Aˣ) : B.A)) * β₀ = 1 := by simp
    have hi' : B.σ (β₀ : B.A) * B.σ ((β₀⁻¹ : B.Aˣ) : B.A) = 1 := by rw [← map_mul]; simp
    rw [hβ₀] at hi'
    simp only [Units.val_mul, IsUnit.unit_spec, map_mul, hσβ]
    linear_combination (β * ((β₀⁻¹ : B.Aˣ) : B.A)) * hi' - (β * B.σ ((β₀⁻¹ : B.Aˣ) : B.A) * ((-1) ^ (m - 1) * u)) * hi
  · have hb : (β₀ : B.A) * ((β₀⁻¹ * hβu.unit : B.Aˣ) : B.A) = β := by simp
    rw [hb, GlobalTheory.TwLat.dlt, dif_pos hGunit, hth]
    have hGe : hGunit.unit = Gu := Units.ext (by rw [IsUnit.unit_spec, hβ])
    rw [hGe]
    have hII : ∀ g : GLw m w, invT m _ (invT m _ g) = g := fun g => by
      apply Units.ext
      show (((invT m _ g)⁻¹ : GLw m w).val)ᵀ = g.val
      rw [← map_inv]
      show (((g⁻¹)⁻¹ : GLw m w).val)ᵀᵀ = g.val
      rw [inv_inv, transpose_transpose]
    have hth' : ∀ g : GLw m w, thetaGL m (cj w) g = PhiU m _ * invT m _ (GeneralLinearGroup.map (cj w) g) * (PhiU m _)⁻¹ :=
      fun g => rfl
    show y = P⁻¹⁻¹ * (invT m _ (invT m _ P⁻¹ * invT m _ (y * PhiU m _) * GeneralLinearGroup.map (cj w) P) * (PhiU m _)⁻¹) *
      thetaGL m (cj w) P⁻¹
    rw [hth', map_mul, map_mul, hII, hII, map_inv, map_inv]
    group

end GlobalTheory.TwLat.ClSurj
