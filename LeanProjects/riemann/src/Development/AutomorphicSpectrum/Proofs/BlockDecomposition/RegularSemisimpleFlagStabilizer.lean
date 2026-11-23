import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyOfIrreduci
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.RestrictRoots
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.LeviConj

open Polynomial

section Idem

variable {E : Type} [Field E] {n : ℕ}

theorem exists_poly_proj {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (f : Module.End E V) (hf : (LinearMap.charpoly f).Separable)
    (W : Submodule E V) (hW : ∀ x ∈ W, f x ∈ W) :
    ∃ p : E[X], (∀ x, aeval f p x ∈ W) ∧ ∀ x ∈ W, aeval f p x = x := by
  have hss : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf.squarefree (LinearMap.aeval_self_charpoly f)
  obtain ⟨W₁, hW₁, hc⟩ := Module.End.isSemisimple_iff.mp hss W ((Module.End.mem_invtSubmodule f).mpr (fun x hx => hW x hx))
  have hW₁' : ∀ x ∈ W₁, f x ∈ W₁ := fun x hx => (Module.End.mem_invtSubmodule f).mp hW₁ hx
  have hcp := Formalism.GaloisIrreducibility.rr_charpoly_compl f W W₁ hc hW hW₁'
  set a := LinearMap.charpoly (f.restrict hW) with ha
  set b := LinearMap.charpoly (f.restrict hW₁') with hb
  rw [hcp] at hf
  obtain ⟨u, v, huv⟩ : IsCoprime a b := hf.isCoprime
  have hzW : ∀ x ∈ W, aeval f a x = 0 := fun x hx => by
    have := GlobalTheory.CuspGL.coe_aeval_restrict_apply f W hW a ⟨x, hx⟩
    rw [ha, LinearMap.aeval_self_charpoly] at this
    simpa [ha] using this.symm
  have hzW₁ : ∀ x ∈ W₁, aeval f b x = 0 := fun x hx => by
    have := GlobalTheory.CuspGL.coe_aeval_restrict_apply f W₁ hW₁' b ⟨x, hx⟩
    rw [hb, LinearMap.aeval_self_charpoly] at this
    simpa [hb] using this.symm
  have hid : ∀ x, aeval f (u * a) x + aeval f (v * b) x = x := fun x => by
    have := congrArg (fun q => aeval f q x) huv
    simpa using this
  have h1 : ∀ x ∈ W, aeval f (v * b) x = x := fun x hx => by
    have h2 : aeval f (u * a) x = 0 := by
      rw [map_mul, Module.End.mul_apply, hzW x hx, map_zero]
    have := hid x
    rwa [h2, zero_add] at this
  have h0 : ∀ x ∈ W₁, aeval f (v * b) x = 0 := fun x hx => by
    rw [map_mul, Module.End.mul_apply, hzW₁ x hx, map_zero]
  refine ⟨v * b, fun x => ?_, h1⟩
  obtain ⟨w, hw, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top (x := x))
  rw [map_add, h1 w hw, h0 w₁ hw₁, add_zero]
  exact hw

theorem exists_poly_proj_matrix {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin n) (Fin n) E) (hM : M.charpoly.Separable) (P : Matrix (Fin n) ι E)
    (C : Matrix ι ι E) (hC : M * P = P * C) :
    ∃ p : E[X], aeval M p * P = P ∧ ∃ B : Matrix ι (Fin n) E, aeval M p = P * B := by
  set f : Module.End E (Fin n → E) := Matrix.toLinAlgEquiv' M with hf
  have hcp : LinearMap.charpoly f = M.charpoly := Matrix.charpoly_toLin' M
  have hae : ∀ (p : E[X]) (x : Fin n → E), aeval f p x = aeval M p *ᵥ x := fun p x => by
    rw [hf, Polynomial.aeval_algHom_apply, Matrix.toLinAlgEquiv'_apply]
  set W : Submodule E (Fin n → E) := LinearMap.range P.mulVecLin with hWd
  have hW : ∀ x ∈ W, f x ∈ W := by
    rintro x ⟨y, rfl⟩
    refine ⟨C *ᵥ y, ?_⟩
    simp only [Matrix.mulVecLin_apply, hf, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_mulVec, hC]
  obtain ⟨p, hp1, hp2⟩ := exists_poly_proj f (hcp ▸ hM) W hW
  refine ⟨p, ?_, ?_⟩
  · apply Matrix.mulVec_injective
    funext y
    have h := hp2 (P *ᵥ y) ⟨y, rfl⟩
    rw [hae, Matrix.mulVec_mulVec] at h
    exact h
  · have hcol : ∀ i : Fin n, ∃ c : ι → E, P *ᵥ c = aeval M p *ᵥ Pi.single i 1 := fun i => by
      obtain ⟨c, hc⟩ := hp1 (Pi.single i 1)
      exact ⟨c, by rw [← hae, ← hc]; rfl⟩
    choose c hc using hcol
    refine ⟨Matrix.of fun l i => c i l, ?_⟩
    ext a i
    have := congrFun (hc i) a
    rw [Matrix.mulVec_single_one] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this.symm

theorem commute_aeval {M T : Matrix (Fin n) (Fin n) E} (h : Commute T M) (p : E[X]) :
    Commute T (aeval M p) := by
  induction p using Polynomial.induction_on with
  | C a => rw [aeval_C]; exact (Algebra.commutes a T).symm
  | add p q hp hq => simpa using hp.add_right hq
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    exact ih.mul_right h

end Idem

section Unip

variable {E : Type} [Field E] (s : E →+* E) {n : ℕ}

theorem cT_mul {a b c : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b c E) :
    cT s (A * B) = cT s B * cT s A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_add {a b : Type} (A B : Matrix a b E) : cT s (A + B) = cT s A + cT s B := by
  ext i j; simp [cT]

theorem cT_sub {a b : Type} (A B : Matrix a b E) : cT s (A - B) = cT s A - cT s B := by
  ext i j; simp [cT]

theorem cT_cT (hs : ∀ x, s (s x) = x) {a b : Type} (A : Matrix a b E) : cT s (cT s A) = A := by
  ext i j; simp [cT, hs]

theorem cT_one {a : Type} [DecidableEq a] : cT s (1 : Matrix a a E) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [cT]
  · simp [cT, Matrix.one_apply, h, Ne.symm h]

theorem gram_cT (hs : ∀ x, s (s x) = x) {J : Matrix (Fin n) (Fin n) E} (hJ : cT s J = J)
    {a b : Type} [Fintype a] [Fintype b] (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) :
    cT s (cT s A * J * B) = cT s B * J * A := by
  rw [cT_mul, cT_mul, cT_cT s hs, hJ, Matrix.mul_assoc]

theorem unip_alg {ι : Type} [Fintype ι] [DecidableEq ι]
    (P D : Matrix (Fin n) ι E) (A A' : Matrix ι (Fin n) E) (B Bc G : Matrix ι ι E)
    (hAP : A * P = 0) (hAD : A * D = 0) (hAP' : A' * P = 0) (hG : A' * D = G) (hsum : B + G + Bc = 0) :
    (1 + P * A' - D * A + P * Bc * A) * (1 + D * A - P * A' + P * B * A) = 1 := by
  have e1 : ∀ T : Matrix ι (Fin n) E, A * (P * T) = 0 := fun T => by
    rw [← Matrix.mul_assoc, hAP, Matrix.zero_mul]
  have e2 : ∀ T : Matrix ι (Fin n) E, A * (D * T) = 0 := fun T => by
    rw [← Matrix.mul_assoc, hAD, Matrix.zero_mul]
  have e3 : ∀ T : Matrix ι (Fin n) E, A' * (P * T) = 0 := fun T => by
    rw [← Matrix.mul_assoc, hAP', Matrix.zero_mul]
  have e4 : ∀ T : Matrix ι (Fin n) E, A' * (D * T) = G * T := fun T => by
    rw [← Matrix.mul_assoc, hG]
  have hB : B = - G - Bc := by
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← hsum]; abel
  subst hB
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc, e1, e2, e3, e4, Matrix.mul_zero, Matrix.neg_mul, Matrix.mul_neg]
  abel

theorem exists_unip {ι : Type} [Fintype ι] [DecidableEq ι] (hs : ∀ x, s (s x) = x)
    (J : Matrix (Fin n) (Fin n) E) (hJ : cT s J = J)
    (P Q Q' : Matrix (Fin n) ι E) (hPP : cT s P * J * P = 0) (hPQ : cT s P * J * Q = 1)
    (hQQ : cT s Q * J * Q = 0) (hPQ' : cT s P * J * Q' = 1) (hQQ' : cT s Q' * J * Q' = 0) :
    ∃ N : Matrix (Fin n) (Fin n) E, cT s N * J * N = J ∧ N * P = P ∧ N * Q = Q' ∧
      ∀ (κ : Type) [Fintype κ] (Z : Matrix (Fin n) κ E), cT s P * J * Z = 0 →
        ∃ K : Matrix ι κ E, N * Z = Z + P * K := by
  obtain ⟨D, hD⟩ : ∃ D, D = Q' - Q := ⟨_, rfl⟩
  have hQ' : Q' = Q + D := by simp [hD]
  have hPD : cT s P * J * D = 0 := by
    rw [hD, Matrix.mul_sub, hPQ, hPQ', sub_self]
  have hDP : cT s D * J * P = 0 := by
    rw [← gram_cT s hs hJ P D, hPD]; ext i j; simp [cT]
  obtain ⟨A, hA⟩ : ∃ A, A = cT s P * J := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A', A' = cT s D * J := ⟨_, rfl⟩
  have cA : cT s A = J * P := by rw [hA, cT_mul, cT_cT s hs, hJ]
  have cA' : cT s A' = J * D := by rw [hA', cT_mul, cT_cT s hs, hJ]
  rw [← hA] at hPP hPQ hPQ' hPD
  rw [← hA'] at hDP
  have hsum : A' * Q + A' * D + cT s (A' * Q) = 0 := by
    have h : cT s (Q + D) * J * (Q + D) = 0 := hQ' ▸ hQQ'
    rw [cT_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hQQ, zero_add, ← hA'] at h
    have h2 : cT s (A' * Q) = cT s Q * J * D := by
      rw [hA', gram_cT s hs hJ]
    rw [h2]
    rw [← h]; abel
  refine ⟨1 + D * A - P * A' + P * (A' * Q) * A, ?_, ?_, ?_, ?_⟩
  · have h1 : cT s (1 + D * A - P * A' + P * (A' * Q) * A) * J
        = J * (1 + P * A' - D * A + P * cT s (A' * Q) * A) := by
      rw [cT_add, cT_sub, cT_add, cT_one, cT_mul, cT_mul, cT_mul, cT_mul, cA, cA']
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_assoc, hA, hA']
    rw [h1, Matrix.mul_assoc, unip_alg P D A A' _ _ _ hPP hPD hDP rfl hsum, Matrix.mul_one]
  · simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPP, hDP, Matrix.mul_zero, add_zero, sub_zero]
  · simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPQ, Matrix.mul_one]
    rw [hQ']; abel
  · intro κ _ Z hZ
    rw [← hA] at hZ
    refine ⟨-(A' * Z), ?_⟩
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hZ, Matrix.mul_zero, add_zero, Matrix.mul_neg]
    abel

end Unip

section Flags

variable {E : Type} [Field E] (s : E →+* E) {n r : ℕ}

abbrev Pj (X : Matrix (Fin n) (Fin r) E) (j : Fin r) : Matrix (Fin n) {l : Fin r // l ≤ j} E :=
  X.submatrix id Subtype.val

def Stab (A : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) (j : Fin r) : Prop :=
  ∃ C : Matrix {l : Fin r // l ≤ j} {l : Fin r // l ≤ j} E, A * Pj X j = Pj X j * C

theorem sum_trunc {j : Fin r} (f : Fin r → E) (hf : ∀ m, j < m → f m = 0) :
    ∑ m, f m = ∑ u : {l : Fin r // l ≤ j}, f u.1 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (· ≤ j)) (by simp) f]
  refine (Finset.sum_filter_of_ne fun x _ hx => ?_).symm
  by_contra h
  exact hx (hf x (not_le.mp h))

theorem stab_iff (A : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) (j : Fin r) :
    (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, A *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0)
      ↔ Stab A X j := by
  constructor
  · intro h
    choose b hb1 hb2 using h
    refine ⟨Matrix.of fun m l => b l.1 l.2 m.1, ?_⟩
    ext a l
    have h1 := congrFun (hb1 l.1 l.2) a
    have h2 := sum_trunc (j := j) (fun m => X a m * b l.1 l.2 m)
      (fun m hm => by simp [hb2 l.1 l.2 m hm])
    calc (A * Pj X j) a l = (A *ᵥ fun a => X a l.1) a := rfl
      _ = ∑ m, X a m * b l.1 l.2 m := h1
      _ = _ := h2
  · rintro ⟨C, hC⟩ l hl
    refine ⟨fun m => if h : m ≤ j then C ⟨m, h⟩ ⟨l, hl⟩ else 0, ?_, fun m hm => dif_neg (not_le.mpr hm)⟩
    funext a
    have h1 := congrFun (congrFun hC a) ⟨l, hl⟩
    have h2 := sum_trunc (j := j) (fun m => X a m * (if h : m ≤ j then C ⟨m, h⟩ ⟨l, hl⟩ else 0))
      (fun m hm => by simp [not_le.mpr hm])
    calc (A *ᵥ fun a => X a l) a = (A * Pj X j) a ⟨l, hl⟩ := rfl
      _ = (Pj X j * C) a ⟨l, hl⟩ := h1
      _ = ∑ u : {l : Fin r // l ≤ j}, X a u.1 * (if h : u.1 ≤ j then C ⟨u.1, h⟩ ⟨l, hl⟩ else 0) := by
        simp only [Matrix.mul_apply, Pj, Matrix.submatrix_apply, id]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [dif_pos u.2]
      _ = _ := h2.symm

theorem exists_sel (X : Matrix (Fin n) (Fin r) E) {i a : Fin r} (h : i ≤ a) :
    ∃ L : Matrix {l : Fin r // l ≤ a} {l : Fin r // l ≤ i} E, Pj X i = Pj X a * L := by
  refine ⟨Matrix.of fun u v => if u.1 = v.1 then 1 else 0, ?_⟩
  ext b v
  simp only [Matrix.mul_apply, Pj, Matrix.submatrix_apply, id, Matrix.of_apply]
  rw [Finset.sum_eq_single (⟨v.1, v.2.trans h⟩ : {l : Fin r // l ≤ a})]
  · simp
  · intro u _ hu
    have : u.1 ≠ v.1 := fun e => hu (Subtype.ext e)
    simp [this]
  · simp

theorem stab_mul {A B : Matrix (Fin n) (Fin n) E} {X : Matrix (Fin n) (Fin r) E} {j : Fin r}
    (hA : Stab A X j) (hB : Stab B X j) : Stab (A * B) X j := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨D, hD⟩ := hB
  exact ⟨C * D, by rw [Matrix.mul_assoc, hD, ← Matrix.mul_assoc, hC, Matrix.mul_assoc]⟩

theorem pj_gram (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (i j : Fin r) :
    cT s (Pj X i) * J * Pj Y j = (cT s X * J * Y).submatrix Subtype.val Subtype.val := by
  ext u v
  rfl

theorem step (hs : ∀ x, s (s x) = x) (J : Matrix (Fin n) (Fin n) E) (hJ : cT s J = J) (hdet : J.det ≠ 0)
    (X Y : Matrix (Fin n) (Fin r) E) (xx : cT s X * J * X = 0) (yy : cT s Y * J * Y = 0)
    (xy : cT s X * J * Y = 1) (M : Matrix (Fin n) (Fin n) E) (hM : M.charpoly.Separable)
    (hMU : cT s M * J * M = J) (a : Fin r) (ha : Stab M X a) (T : Finset (Fin r))
    (hT : ∀ j ∈ T, j ≤ a ∧ Stab M Y j) :
    ∃ N N' : Matrix (Fin n) (Fin n) E, N * N' = 1 ∧ N' * N = 1 ∧ cT s N * J * N = J ∧
      (∀ i, Stab N X i ∧ Stab N' X i) ∧ (∀ j ∈ T, N * Pj Y j = Pj Y j) ∧ Stab (N' * M * N) Y a := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have hJi : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hJi' : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have gram1 : ∀ i j, cT s (Pj X i) * J * Pj Y j = (1 : Matrix _ _ E).submatrix Subtype.val Subtype.val := by
    intro i j; rw [pj_gram, xy]
  have gram1' : ∀ i, cT s (Pj X i) * J * Pj Y i = 1 := by
    intro i; rw [gram1]; exact Matrix.submatrix_one _ Subtype.val_injective
  have gram0 : ∀ i j, cT s (Pj X i) * J * Pj X j = 0 := by
    intro i j; rw [pj_gram, xx]; ext u v; rfl
  have gram0' : ∀ i, cT s (Pj Y i) * J * Pj Y i = 0 := by
    intro i; rw [pj_gram, yy]; ext u v; rfl
  obtain ⟨C, hC⟩ := ha
  obtain ⟨p, hp, B, hB⟩ := exists_poly_proj_matrix M hM (Pj X a) C hC
  set e := aeval M p with he
  set P := Pj X a with hP
  set Q := Pj Y a with hQ
  obtain ⟨f, hf⟩ : ∃ f, f = J⁻¹ * cT s e * J := ⟨_, rfl⟩
  have hPP : cT s P * J * P = 0 := gram0 a a
  have hPQ : cT s P * J * Q = 1 := gram1' a
  have hQQ : cT s Q * J * Q = 0 := gram0' a
  have hJf : J * f = cT s e * J := by
    rw [hf, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJi', Matrix.one_mul]
  have hfJ : cT s f * J = J * e := by
    have := congrArg (cT s) hJf
    rw [cT_mul, cT_mul, cT_cT s hs, hJ] at this
    exact this

  have hNM : (J⁻¹ * cT s M * J) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s M), hMU, hJi]
  have hMN : M * (J⁻¹ * cT s M * J) = 1 := mul_eq_one_comm.mp hNM
  have hcomm : ∀ T' : Matrix (Fin n) (Fin n) E, Commute T' M → Commute (J⁻¹ * cT s T' * J) M := by
    intro T' hT'
    have h1 : (J⁻¹ * cT s M * J) * (J⁻¹ * cT s T' * J) = (J⁻¹ * cT s T' * J) * (J⁻¹ * cT s M * J) := by
      have e1 : ∀ U V : Matrix (Fin n) (Fin n) E, (J⁻¹ * cT s U * J) * (J⁻¹ * cT s V * J) = J⁻¹ * cT s (V * U) * J := by
        intro U V
        rw [cT_mul]
        calc _ = J⁻¹ * cT s U * (J * J⁻¹) * cT s V * J := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hJi', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      rw [e1, e1, hT'.eq]
    show (J⁻¹ * cT s T' * J) * M = M * (J⁻¹ * cT s T' * J)
    calc (J⁻¹ * cT s T' * J) * M = M * (J⁻¹ * cT s M * J) * (J⁻¹ * cT s T' * J) * M := by
          rw [hMN, Matrix.one_mul]
      _ = M * (J⁻¹ * cT s T' * J) * ((J⁻¹ * cT s M * J) * M) := by
          rw [Matrix.mul_assoc M, h1]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hNM, Matrix.mul_one]
  have heM : Commute e M := ((commute_aeval (Commute.refl M) p)).symm
  have hfM : Commute f M := hf ▸ hcomm e heM
  have hfe' : Commute f e := commute_aeval hfM p
  have hfe : f * e = 0 := by
    have h1 : J * (f * e) = 0 := by
      rw [← Matrix.mul_assoc, hJf, hB, cT_mul]
      calc _ = cT s B * (cT s P * J * P) * B := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPP]; simp
    calc f * e = J⁻¹ * (J * (f * e)) := by rw [← Matrix.mul_assoc, hJi, Matrix.one_mul]
      _ = 0 := by rw [h1, Matrix.mul_zero]
  have hef : e * f = 0 := by rw [← hfe'.eq, hfe]

  have hPf : ∀ {κ κ' : Type} [Fintype κ] [Fintype κ'] (R : Matrix (Fin n) κ E) (Z : Matrix (Fin n) κ' E),
      e * R = R → cT s R * J * (f * Z) = cT s R * J * Z := by
    intro κ κ' _ _ R Z hR
    calc _ = cT s R * (J * f) * Z := by simp only [Matrix.mul_assoc]
      _ = cT s (e * R) * J * Z := by rw [hJf, cT_mul s e R]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR]
  have hPQ' : cT s P * J * (f * Q) = 1 := by rw [hPf P Q hp, hPQ]
  have hQQ' : cT s (f * Q) * J * (f * Q) = 0 := by
    rw [cT_mul]
    calc _ = cT s Q * (cT s f * J) * (f * Q) := by simp only [Matrix.mul_assoc]
      _ = cT s Q * J * ((e * f) * Q) := by rw [hfJ]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hef]; simp
  obtain ⟨N, hN, hNP, hNQ, hNZ⟩ := exists_unip s hs J hJ P Q (f * Q) hPP hPQ hQQ hPQ' hQQ'
  have hN'N : (J⁻¹ * cT s N * J) * N = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s N), hN, hJi]
  obtain ⟨N', hN'⟩ : ∃ N', N' = J⁻¹ * cT s N * J := ⟨_, rfl⟩
  rw [← hN'] at hN'N
  have hNN' : N * N' = 1 := mul_eq_one_comm.mp hN'N
  have hN'P : N' * P = P := by
    calc N' * P = N' * (N * P) := by rw [hNP]
      _ = P := by rw [← Matrix.mul_assoc, hN'N, Matrix.one_mul]
  refine ⟨N, N', hNN', hN'N, hN, ?_, ?_, ?_⟩
  · intro i
    rcases le_total i a with h | h
    · obtain ⟨L, hL⟩ := exists_sel X h
      have hL' : Pj X i = P * L := hL
      exact ⟨⟨1, by rw [hL', ← Matrix.mul_assoc, hNP, Matrix.mul_one]⟩,
        ⟨1, by rw [hL', ← Matrix.mul_assoc, hN'P, Matrix.mul_one]⟩⟩
    · obtain ⟨L, hL⟩ := exists_sel X h
      have hL' : P = Pj X i * L := hL
      obtain ⟨K, hK⟩ := hNZ _ (Pj X i) (gram0 a i)
      have h' : N' * Pj X i = Pj X i - P * K := by
        have h1 : Pj X i = N' * Pj X i + P * K := by
          calc Pj X i = N' * (N * Pj X i) := by rw [← Matrix.mul_assoc, hN'N, Matrix.one_mul]
            _ = _ := by rw [hK, Matrix.mul_add, ← Matrix.mul_assoc N', hN'P]
        rw [eq_sub_iff_add_eq]; exact h1.symm
      refine ⟨⟨1 + L * K, ?_⟩, ⟨1 - L * K, ?_⟩⟩
      · rw [hK, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← hL']
      · rw [h', Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← hL']
  · intro j hj
    obtain ⟨hja, C', hC'⟩ := hT j hj
    obtain ⟨L, hL⟩ := exists_sel Y hja
    have hL' : Pj Y j = Q * L := hL
    obtain ⟨LX, hLX⟩ := exists_sel X hja
    have hLX' : Pj X j = P * LX := hLX
    obtain ⟨p', hp', B', hB'⟩ := exists_poly_proj_matrix M hM (Pj Y j) C' hC'
    have hfe2 : Commute f (aeval M p') := commute_aeval hfM p'
    have h1 : f * Pj Y j = Pj Y j * (B' * (f * Pj Y j)) := by
      calc f * Pj Y j = f * (aeval M p' * Pj Y j) := by rw [hp']
        _ = aeval M p' * (f * Pj Y j) := by rw [← Matrix.mul_assoc, hfe2.eq, Matrix.mul_assoc]
        _ = (Pj Y j * B') * (f * Pj Y j) := by rw [hB']
        _ = _ := by rw [Matrix.mul_assoc]
    have hePj : e * Pj X j = Pj X j := by rw [hLX', ← Matrix.mul_assoc, hp]
    have h2 : B' * (f * Pj Y j) = 1 := by
      have h3 := hPf (Pj X j) (Pj Y j) hePj
      rw [gram1' j] at h3
      have h4 : cT s (Pj X j) * J * (Pj Y j * (B' * (f * Pj Y j))) = B' * (f * Pj Y j) := by
        rw [← Matrix.mul_assoc, gram1' j, Matrix.one_mul]
      rw [← h4, ← h1]; exact h3
    calc N * Pj Y j = (N * Q) * L := by rw [hL', Matrix.mul_assoc]
      _ = f * Pj Y j := by rw [hNQ, hL', Matrix.mul_assoc]
      _ = Pj Y j * (B' * (f * Pj Y j)) := h1
      _ = Pj Y j := by rw [h2, Matrix.mul_one]
  · obtain ⟨c, hc⟩ : ∃ c, c = cT s P * J * (M * Q) := ⟨_, rfl⟩
    have hZ : cT s P * J * (M * Q - Q * c) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc (cT s P * J) Q c, hPQ, Matrix.one_mul, hc, sub_self]
    have hfZ : f * (M * Q - Q * c) = 0 := by
      have h1 : J * (f * (M * Q - Q * c)) = 0 := by
        rw [← Matrix.mul_assoc, hJf, hB, cT_mul]
        calc _ = cT s B * (cT s P * J * (M * Q - Q * c)) := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hZ, Matrix.mul_zero]
      calc _ = J⁻¹ * (J * (f * (M * Q - Q * c))) := by rw [← Matrix.mul_assoc, hJi, Matrix.one_mul]
        _ = 0 := by rw [h1, Matrix.mul_zero]
    have hMQ' : M * (f * Q) = (f * Q) * c := by
      have h1 : f * (M * Q) = f * (Q * c) := by
        rw [Matrix.mul_sub, sub_eq_zero] at hfZ; exact hfZ
      calc M * (f * Q) = f * (M * Q) := by rw [← Matrix.mul_assoc, ← hfM.eq, Matrix.mul_assoc]
        _ = f * (Q * c) := h1
        _ = _ := by rw [Matrix.mul_assoc]
    refine ⟨c, ?_⟩
    show N' * M * N * Q = Q * c
    calc N' * M * N * Q = N' * (M * (N * Q)) := by simp only [Matrix.mul_assoc]
      _ = N' * ((N * Q) * c) := by rw [hNQ, hMQ']
      _ = (N' * N) * Q * c := by simp only [Matrix.mul_assoc]
      _ = Q * c := by rw [hN'N, Matrix.one_mul]

theorem sep_conj (A : Matrix (Fin n) (Fin n) E) (u : (Matrix (Fin n) (Fin n) E)ˣ) (h : A.charpoly.Separable) :
    (((u⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) * A * u).charpoly.Separable := by
  rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  exact h

end Flags

theorem conj_into_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (γ : GRat σ J), GlobalTheory.Orb.IsRegSS γ.1.1 → (∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, γ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0)) → ∃ g : GRat σ J, (∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, g.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0)) ∧ ∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, (g⁻¹ * γ * g).1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) ∧ (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, (g⁻¹ * γ * g).1.1 *ᵥ (fun a => Y a l) = Y *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW S γ hreg hγ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => by
    apply τ.injective
    have h1 := hCM.2.2.2 τ (σ x)
    have h2 := hCM.2.2.2 τ x
    show τ (σ (σ x)) = τ x
    rw [h1, h2, star_star]
  have hJc : cT (σ : E →+* E) J = J := by
    ext i j
    exact hJ.1 i j
  have key : ∀ T : Finset (Fin r), T ⊆ S → ∃ g : GRat σ J, (∀ j ∈ S, Stab g.1.1 X j) ∧
      (∀ j ∈ S, Stab (g⁻¹ * γ * g).1.1 X j) ∧ ∀ j ∈ T, Stab (g⁻¹ * γ * g).1.1 Y j := by
    intro T
    refine Finset.induction_on_max T ?_ ?_
    · intro _
      refine ⟨1, fun j _ => ⟨1, by simp⟩, fun j hj => ?_, by simp⟩
      have := (stab_iff _ X j).mp (hγ j hj)
      simpa using this
    · intro a T hlt ih hsub
      obtain ⟨g, h1, h2, h3⟩ := ih ((Finset.subset_insert _ _).trans hsub)
      have haS : a ∈ S := hsub (Finset.mem_insert_self a T)
      have hsep : ((g⁻¹ * γ * g).1.1).charpoly.Separable := by
        have e : (g⁻¹ * γ * g).1.1 = ((g.1⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * γ.1.1 * g.1.1 := by
          simp
        rw [e]
        exact sep_conj _ g.1 hreg
      obtain ⟨N, N', e1, e2, hNU, hNX, hNY, hNa⟩ := step (σ : E →+* E) hs J hJc hJ.2 X Y hW.xx hW.yy hW.xy
        (g⁻¹ * γ * g).1.1 hsep (g⁻¹ * γ * g).2 a (h2 a haS) T (fun j hj => ⟨(hlt j hj).le, h3 j hj⟩)
      let m : GRat σ J := ⟨⟨N, N', e1, e2⟩, hNU⟩
      have hconj : ((g * m)⁻¹ * γ * (g * m)).1.1 = N' * (g⁻¹ * γ * g).1.1 * N := by
        have e : (g * m)⁻¹ * γ * (g * m) = m⁻¹ * (g⁻¹ * γ * g) * m := by group
        rw [e]; rfl
      refine ⟨g * m, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
      · exact stab_mul (h1 j hj) (hNX j).1
      · rw [hconj]
        exact stab_mul (stab_mul (hNX j).2 (h2 j hj)) (hNX j).1
      · rw [hconj]
        rcases Finset.mem_insert.mp hj with rfl | hjT
        · exact hNa
        · obtain ⟨C, hC⟩ := h3 j hjT
          have hN := hNY j hjT
          have hN' : N' * Pj Y j = Pj Y j := by
            calc N' * Pj Y j = N' * (N * Pj Y j) := by rw [hN]
              _ = _ := by rw [← Matrix.mul_assoc, e2, Matrix.one_mul]
          refine ⟨C, ?_⟩
          rw [Matrix.mul_assoc, hN, Matrix.mul_assoc, hC, ← Matrix.mul_assoc, hN']
  obtain ⟨g, h1, h2, h3⟩ := key S (Finset.Subset.refl S)
  exact ⟨g, fun j hj => (stab_iff _ X j).mpr (h1 j hj),
    fun j hj => ⟨(stab_iff _ X j).mpr (h2 j hj), (stab_iff _ Y j).mpr (h3 j hj)⟩⟩

end GlobalTheory.CompanionTheory.LeviConj
