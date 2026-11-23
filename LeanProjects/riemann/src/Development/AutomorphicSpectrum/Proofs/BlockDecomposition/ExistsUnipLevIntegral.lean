import Mathlib
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.AutomorphicForms.Iwasawa
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.CTFin.IwaFin

theorem exists_unip_mul_lev {R : Type} [CommRing R] (r s : ℕ) (P : GL (Fin (r + s)) R)
    (h1 : ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (P : Matrix _ _ R) i j = 0)
    (h2 : ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → ((P⁻¹ : GL _ R) : Matrix _ _ R) i j = 0) :
    ∃ (x : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R), P = unip x * lev R r s m := by
  set e := GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) with he
  set Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R := (P : Matrix _ _ R).submatrix e e with hQd
  set Q' : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R := ((P⁻¹ : GL _ R) : Matrix _ _ R).submatrix e e with hQ'd
  have hQQ : Q * Q' = 1 := by
    rw [hQd, hQ'd, Matrix.submatrix_mul_equiv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.submatrix_one_equiv]
  have hQQ' : Q' * Q = 1 := by
    rw [hQd, hQ'd, Matrix.submatrix_mul_equiv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.submatrix_one_equiv]
  have hz : Q.toBlocks₂₁ = 0 := by
    ext i j
    exact h1 _ _ (by simp [he]) (by simp [he])
  have hz' : Q'.toBlocks₂₁ = 0 := by
    ext i j
    exact h2 _ _ (by simp [he]) (by simp [he])
  have hb : Q = fromBlocks Q.toBlocks₁₁ Q.toBlocks₁₂ 0 Q.toBlocks₂₂ := by
    rw [← hz, fromBlocks_toBlocks]
  have hb' : Q' = fromBlocks Q'.toBlocks₁₁ Q'.toBlocks₁₂ 0 Q'.toBlocks₂₂ := by
    rw [← hz', fromBlocks_toBlocks]
  generalize Q.toBlocks₁₁ = A at hb
  generalize Q.toBlocks₁₂ = B at hb
  generalize Q.toBlocks₂₂ = D at hb
  generalize Q'.toBlocks₁₁ = A' at hb'
  generalize Q'.toBlocks₁₂ = B' at hb'
  generalize Q'.toBlocks₂₂ = D' at hb'
  rw [hb, hb', fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hQQ hQQ'
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hQQ
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hQQ'
  obtain ⟨a1, -, -, d1⟩ := hQQ
  obtain ⟨a2, -, -, d2⟩ := hQQ'
  let X : Matrix (Fin r) (Fin s) R := B * D'
  let x : BlockIx (r + s) r → R := fun p =>
    X ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.1.2.isLt; have := p.2.2; omega⟩
  let m : GL (Fin r) R × GL (Fin s) R := (⟨A, A', a1, a2⟩, ⟨D, D', d1, d2⟩)
  refine ⟨x, m, Units.ext ?_⟩
  have hn : (nilM x : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e = fromBlocks 0 X 0 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [nilM, he]
    · have h : (((e (Sum.inl i) : Fin (r + s)) : ℕ) < r ∧ r ≤ ((e (Sum.inr j) : Fin (r + s)) : ℕ)) := by
        simp [he]
      simp only [submatrix_apply, nilM, of_apply, dif_pos h, fromBlocks_apply₁₂, x]
      congr 1
      exact Fin.ext (by simp [he])
    · simp [nilM, he]
    · simp [nilM, he]
  have hu : ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R).submatrix e e = fromBlocks 1 X 0 1 := by
    change (1 + nilM x : Matrix _ _ R).submatrix e e = _
    have h : (1 + nilM x : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e =
        (1 : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e + (nilM x).submatrix e e := rfl
    rw [h, Matrix.submatrix_one_equiv, hn, ← fromBlocks_one, fromBlocks_add]
    simp
  have hl : ((lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R).submatrix e e = fromBlocks A 0 0 D := by
    rw [lev, GlobalTheory.SmGL.val_emb₂]
    ext i j
    simp [m, ← he]
  have hinj : ∀ M N : Matrix (Fin (r + s)) (Fin (r + s)) R, M.submatrix e e = N.submatrix e e → M = N := by
    intro M N h
    ext i j
    have := congrFun (congrFun h (e.symm i)) (e.symm j)
    simpa using this
  apply hinj
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ e, hu, hl, fromBlocks_multiply, ← hQd, hb]
  simp [X, Matrix.mul_assoc, d2]

theorem exists_unip_lev_integral (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ)
    (k : GL (Fin (r + s)) (Af E)) :
    ∃ (x : BlockIx (r + s) r → Af E) (m : GL (Fin r) (Af E) × GL (Fin s) (Af E)) (c : GL (Fin (r + s)) (Af E)),
      c ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (r + s) ∧ k = unip x * lev (Af E) r s m * c := by
  classical
  let φ := GroundTheory.Automorphic.AdelicGLn.finiteRestrictedEquiv E (r + s)
  let β : Fin (r + s) → ℕ := fun i => if (i : ℕ) < r then 0 else 1
  have hβ : Monotone β := by
    intro i j hij
    have : (i : ℕ) ≤ j := hij
    simp only [β]
    split_ifs <;> omega
  have loc : ∀ v : HeightOneSpectrum (𝓞 E), ∃ p ∈ GroundTheory.Automorphic.Iwasawa.blockUpper (v.adicCompletion E) (r + s) β,
      ∃ c ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s),
        (φ k v : GL (Fin (r + s)) (v.adicCompletion E)) = p * c ∧
        (φ k v ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) → p = 1) := by
    intro v
    by_cases h : φ k v ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s)
    · exact ⟨1, one_mem _, φ k v, h, (one_mul _).symm, fun _ => rfl⟩
    · obtain ⟨p, hp, c, hc, e⟩ := GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL
        (v.adicCompletion E) (r + s) hβ (φ k v)
      exact ⟨p, hp, c, hc, e, fun h' => absurd h' h⟩
  choose p hp c hc hk h1 using loc
  let P' : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => GL (Fin (r + s)) (v.adicCompletion E))
      (fun v => (GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) : Set _)) Filter.cofinite :=
    ⟨p, by
      filter_upwards [(φ k).2] with v hv
      rw [h1 v hv]
      exact one_mem _⟩
  let C' : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => GL (Fin (r + s)) (v.adicCompletion E))
      (fun v => (GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) : Set _)) Filter.cofinite :=
    ⟨c, Filter.Eventually.of_forall hc⟩
  have hs : ∀ y, φ (φ.symm y) = y := fun y => φ.apply_symm_apply y
  have hPC : k = φ.symm P' * φ.symm C' := by
    apply φ.injective
    rw [map_mul, hs, hs]
    ext v : 1
    exact hk v
  have hPv : ∀ v, φ (φ.symm P') v = p v := fun v => by rw [hs]; rfl
  have hzero : ∀ (q : GL (Fin (r + s)) (Af E)),
      (∀ v, φ q v ∈ GroundTheory.Automorphic.Iwasawa.blockUpper (v.adicCompletion E) (r + s) β) →
      ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (q : Matrix _ _ (Af E)) i j = 0 := by
    intro q hq i j hi hj
    refine FiniteAdeleRing.ext _ fun v => ?_
    have hlt : β j < β i := by simp [β, hj, Nat.not_lt.2 hi]
    exact hq v hlt
  obtain ⟨x, m, hxm⟩ := exists_unip_mul_lev r s (φ.symm P')
    (hzero _ fun v => by rw [hPv]; exact hp v)
    (hzero _ fun v => by
      rw [map_inv, RestrictedProduct.inv_apply, hPv]
      exact inv_mem (hp v))
  refine ⟨x, m, φ.symm C', ?_, by rw [hPC, hxm]⟩
  rw [GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff_forall]
  intro v
  have : φ (φ.symm C') v = c v := by rw [hs]; rfl
  change φ (φ.symm C') v ∈ _
  rw [this]
  exact hc v

end GlobalTheory.CompanionTheory.CTFin.IwaFin
