import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ColMeas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LangXRoot

open GlobalTheory.Col PowerSeries

namespace GlobalTheory.LangWitt

open Matrix

section Field

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem exists_frob_eq_mul_field {d : ℕ} (N : Matrix (Fin d) (Fin d) k) (hN : IsUnit N.det) :
    ∃ V : Matrix (Fin d) (Fin d) k, IsUnit V.det ∧ V.map (frobenius k p) = N * V := by
  classical
  let fr : (Fin d → k) →+ (Fin d → k) :=
    { toFun := fun v i => frobenius k p (v i)
      map_zero' := by ext; simp
      map_add' := fun v w => by ext; simp }
  let F : (Fin d → k) →+ (Fin d → k) := (Matrix.mulVecLin N⁻¹).toAddMonoidHom.comp fr
  have hFv : ∀ v, F v = N⁻¹ *ᵥ (fun i => frobenius k p (v i)) := fun v => rfl
  have hF : ∀ (a : k) (v : Fin d → k), F (a • v) = a ^ p • F v := by
    intro a v
    rw [hFv, hFv, ← Matrix.mulVec_smul]
    congr 1
    ext i
    simp [frobenius_def, mul_pow]
  have hinj : Function.Injective F := by
    intro v w h
    rw [hFv, hFv] at h
    have h2 := congrArg (N *ᵥ ·) h
    simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hN, Matrix.one_mulVec] at h2
    funext i
    exact (frobenius_inj k p) (congrFun h2 i)
  obtain ⟨b, hb⟩ := GlobalTheory.PMonE.LangIsogenyConstruction.lang_basis p hp.out.one_lt F hF hinj
  let b' := b.reindex (finCongr (Module.finrank_fin_fun k))
  have hb' : ∀ j, F (b' j) = b' j := fun j => by simp [b', hb]
  refine ⟨(Pi.basisFun k (Fin d)).toMatrix b', ?_, ?_⟩
  · have := (Pi.basisFun k (Fin d)).invertibleToMatrix b'
    exact isUnit_det_of_invertible _
  · ext i j
    have h2 := congrArg (N *ᵥ ·) (hb' j)
    simp only [hFv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hN, Matrix.one_mulVec] at h2
    have h3 := congrFun h2 i
    simp only [Matrix.map_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.mul_apply]
    rw [h3]
    simp [Matrix.mulVec, dotProduct]

end Field

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p]

local notation "𝕎" => WittVector p

theorem constantCoeff_frobenius (x : 𝕎 k) :
    WittVector.constantCoeff (WittVector.frobenius x) = frobenius k p (WittVector.constantCoeff x) := by
  show (WittVector.frobenius x).coeff 0 = frobenius k p (x.coeff 0)
  rw [WittVector.coeff_frobenius_charP, frobenius_def]

theorem constantCoeff_p : WittVector.constantCoeff (p : 𝕎 k) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

variable [IsAlgClosed k]

theorem p_dvd_iff (x : 𝕎 k) : (p : 𝕎 k) ∣ x ↔ WittVector.constantCoeff x = 0 := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker]

theorem map_sub' {R S : Type} [Ring R] [Ring S] (f : R →+* S) {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) R) : (A - B).map f = A.map f - B.map f :=
  map_sub f.mapMatrix A B

theorem map_add' {R S : Type} [Ring R] [Ring S] (f : R →+* S) {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) R) : (A + B).map f = A.map f + B.map f :=
  map_add f.mapMatrix A B

theorem exists_step {d : ℕ} (N V E : Matrix (Fin d) (Fin d) (𝕎 k)) (hN : IsUnit N.det)
    (hV : IsUnit (V.map WittVector.constantCoeff).det) (n : ℕ)
    (hE : V.map WittVector.frobenius - N * V = ((p : 𝕎 k) ^ (n + 1)) • E) :
    ∃ Y E' : Matrix (Fin d) (Fin d) (𝕎 k),
      (V + (p : 𝕎 k) ^ (n + 1) • Y).map WittVector.frobenius - N * (V + (p : 𝕎 k) ^ (n + 1) • Y)
        = ((p : 𝕎 k) ^ (n + 2)) • E' := by
  classical
  set c : 𝕎 k →+* k := WittVector.constantCoeff with hc
  set φ : 𝕎 k →+* 𝕎 k := WittVector.frobenius with hφ
  have hcp : c (p : 𝕎 k) = 0 := constantCoeff_p
  have hcφ : ∀ A : Matrix (Fin d) (Fin d) (𝕎 k), (A.map φ).map c = (A.map c).map (frobenius k p) := by
    intro A; ext i j; exact constantCoeff_frobenius _
  have hmod : (V.map c).map (frobenius k p) = N.map c * V.map c := by
    have h1 := congrArg (fun A => A.map c) hE
    simp only [map_sub', Matrix.map_mul, hcφ] at h1
    rw [← sub_eq_zero, h1]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hcp,
      Matrix.zero_apply]
    simp
  set Vb := V.map c
  set Nb := N.map c
  have hNb : IsUnit Nb.det := by
    show IsUnit (c.mapMatrix N).det
    rw [← RingHom.map_det]; exact hN.map c
  set Mb := Nb * Vb
  have hMb : IsUnit Mb.det := by rw [Matrix.det_mul]; exact hNb.mul hV
  set R := -(Mb⁻¹ * E.map c)
  choose z hz using fun i j => GlobalTheory.PMonE.LangIsogenyConstruction.as_root p hp.out.one_lt (R i j)
  set Z : Matrix (Fin d) (Fin d) k := Matrix.of z
  have hZ : Z.map (frobenius k p) - Z = R := by
    refine Matrix.ext fun i j => ?_
    simp [Z, frobenius_def, hz]
  set Y : Matrix (Fin d) (Fin d) (𝕎 k) := (Vb * Z).map (WittVector.teichmuller p)
  have hYc : Y.map c = Vb * Z := by
    refine Matrix.ext fun i j => ?_
    simp [Y, c, WittVector.teichmuller_coeff_zero]
  set G := E + Y.map φ - N * Y
  have hG : G.map c = 0 := by
    simp only [G, map_sub', map_add', Matrix.map_mul, hcφ, hYc, hmod]
    have : E.map c + Mb * Z.map (frobenius k p) - Nb * (Vb * Z)
        = E.map c + Mb * (Z.map (frobenius k p) - Z) := by
      simp only [Mb, Matrix.mul_sub, Matrix.mul_assoc]; abel
    rw [this, hZ]
    simp only [R, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hMb, Matrix.one_mul]
    abel
  have hGd : ∀ i j, (p : 𝕎 k) ∣ G i j := fun i j => by
    rw [p_dvd_iff]; exact congrFun (congrFun hG i) j
  choose E' hE' using hGd
  refine ⟨Y, Matrix.of E', ?_⟩
  have hexp : (V + (p : 𝕎 k) ^ (n + 1) • Y).map φ - N * (V + (p : 𝕎 k) ^ (n + 1) • Y)
      = (V.map φ - N * V) + (p : 𝕎 k) ^ (n + 1) • (Y.map φ - N * Y) := by
    refine Matrix.ext fun i j => ?_
    simp [Matrix.mul_add, Matrix.mul_smul, map_pow, map_natCast, φ]
    ring
  rw [hexp, hE]
  refine Matrix.ext fun i j => ?_
  have := hE' i j
  simp only [G, Matrix.add_apply, Matrix.sub_apply] at this
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, Matrix.of_apply]
  linear_combination ((p : 𝕎 k) ^ (n + 1)) * this

end Witt

theorem lang_witt : ∀ (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (d : ℕ) (N : GL (Fin d) (WittVector p k)), ∃ V : GL (Fin d) (WittVector p k),
    (V : Matrix (Fin d) (Fin d) (WittVector p k)).map WittVector.frobenius =
      (N : Matrix (Fin d) (Fin d) (WittVector p k)) * V := by
  intro p hp k _ _ _ d N
  classical
  set c : WittVector p k →+* k := WittVector.constantCoeff with hc
  set φ : WittVector p k →+* WittVector p k := WittVector.frobenius with hφ
  set Nm : Matrix (Fin d) (Fin d) (WittVector p k) := (N : Matrix (Fin d) (Fin d) (WittVector p k))
  have hN : IsUnit Nm.det := Matrix.isUnits_det_units N
  have hNc : IsUnit (Nm.map c).det := by
    show IsUnit (c.mapMatrix Nm).det
    rw [← RingHom.map_det]; exact hN.map c
  obtain ⟨V0, hV0, hV0f⟩ := exists_frob_eq_mul_field (p := p) (Nm.map c) hNc
  have hcp : c (p : WittVector p k) = 0 := constantCoeff_p
  have hcsmul : ∀ (n : ℕ) (A : Matrix (Fin d) (Fin d) (WittVector p k)),
      (((p : WittVector p k) ^ (n + 1)) • A).map c = 0 := by
    intro n A
    refine Matrix.ext fun i j => ?_
    simp [Matrix.map_apply, Matrix.smul_apply, hcp]
  let P : ℕ → Matrix (Fin d) (Fin d) (WittVector p k) → Prop := fun n V =>
    V.map c = V0 ∧ ∃ E, V.map φ - Nm * V = ((p : WittVector p k) ^ (n + 1)) • E
  have step : ∀ n V, ∃ Y, P n V → P (n + 1) (V + (p : WittVector p k) ^ (n + 1) • Y) := by
    intro n V
    by_cases h : P n V
    · obtain ⟨hcV, E, hE⟩ := h
      obtain ⟨Y, E', h'⟩ := exists_step Nm V E hN (hcV ▸ hV0) n hE
      refine ⟨Y, fun _ => ⟨?_, E', h'⟩⟩
      rw [map_add', hcsmul, add_zero, hcV]
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Y hY using step
  let sq : ℕ → Matrix (Fin d) (Fin d) (WittVector p k) := fun n =>
    Nat.rec (V0.map (WittVector.teichmuller p)) (fun n V => V + (p : WittVector p k) ^ (n + 1) • Y n V) n
  have hsucc : ∀ n, sq (n + 1) = sq n + (p : WittVector p k) ^ (n + 1) • Y n (sq n) := fun n => rfl
  have hsq0 : P 0 (sq 0) := by
    have h0 : (sq 0).map c = V0 := by
      refine Matrix.ext fun i j => ?_
      simp [sq, c, WittVector.teichmuller_coeff_zero]
    refine ⟨h0, ?_⟩
    have hd : ∀ i j, (p : WittVector p k) ∣ ((sq 0).map φ - Nm * sq 0) i j := by
      intro i j
      rw [p_dvd_iff]
      have h1 : ((sq 0).map φ - Nm * sq 0).map c = 0 := by
        rw [map_sub', Matrix.map_mul]
        have : ((sq 0).map φ).map c = ((sq 0).map c).map (frobenius k p) := by
          refine Matrix.ext fun i j => ?_; exact constantCoeff_frobenius _
        rw [this, h0, hV0f, sub_self]
      exact congrFun (congrFun h1 i) j
    choose E hE using hd
    exact ⟨Matrix.of E, Matrix.ext fun i j => by simp [hE]⟩
  have hsq : ∀ n, P n (sq n) := by
    intro n
    induction n with
    | zero => exact hsq0
    | succ n ih => rw [hsucc]; exact hY n (sq n) ih
  have hcong : ∀ m n, m ≤ n → ∀ i j, (p : WittVector p k) ^ m ∣ (sq n - sq m) i j := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => intro i j; simp
    | succ n hmn ih =>
      intro i j
      have e : (sq (n + 1) - sq m) i j = (sq n - sq m) i j + (p : WittVector p k) ^ (n + 1) * Y n (sq n) i j := by
        rw [hsucc]; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
      rw [e]
      exact dvd_add (ih i j) (dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _)
  have hcompl := WittVector.isAdicCompleteIdealSpanP (p := p) (k := k)
  have hlim : ∀ i j, ∃ L : WittVector p k, ∀ n, (p : WittVector p k) ^ n ∣ L - sq n i j := by
    intro i j
    obtain ⟨L, hL⟩ := hcompl.toIsPrecomplete.prec (f := fun n => sq n i j) (by
      intro m n hmn
      simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
        Ideal.mem_span_singleton]
      have := hcong m n hmn i j
      rw [Matrix.sub_apply] at this
      rw [← dvd_neg, neg_sub]; exact this)
    refine ⟨L, fun n => ?_⟩
    have := hL n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
      Ideal.mem_span_singleton] at this
    rw [← dvd_neg, neg_sub]; exact this
  choose L hL using hlim
  set Lm : Matrix (Fin d) (Fin d) (WittVector p k) := Matrix.of L
  have hD : ∀ n, ∃ D, Lm = sq n + ((p : WittVector p k) ^ n) • D := by
    intro n
    choose D hD using fun i j => hL i j n
    exact ⟨Matrix.of D, Matrix.ext fun i j => by
      simp only [Lm, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [← hD i j]; ring⟩
  have heq : Lm.map φ = Nm * Lm := by
    refine Matrix.ext fun i j => ?_
    rw [← sub_eq_zero]
    apply hcompl.toIsHausdorff.haus
    intro n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
      Ideal.mem_span_singleton, sub_zero]
    obtain ⟨D, hDn⟩ := hD n
    obtain ⟨-, E, hE⟩ := hsq n
    have e : Lm.map φ - Nm * Lm = (sq n).map φ - Nm * sq n + ((p : WittVector p k) ^ n) • (D.map φ - Nm * D) := by
      rw [hDn]
      refine Matrix.ext fun i j => ?_
      simp [Matrix.mul_add, Matrix.mul_smul, map_pow, map_natCast, φ]
      ring
    have e2 := congrFun (congrFun e i) j
    rw [hE] at e2
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at e2
    rw [e2]
    exact dvd_add (dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _) (dvd_mul_right _ _)
  have hcL : Lm.map c = V0 := by
    obtain ⟨D, hDn⟩ := hD 1
    rw [hDn, map_add', hcsmul 0 D, add_zero]
    exact (hsq 1).1
  have hdet : IsUnit Lm.det := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    have : c Lm.det = V0.det := by
      rw [← hcL]; exact RingHom.map_det c Lm
    exact fun h0 => hV0.ne_zero (this ▸ h0)
  refine ⟨((Matrix.isUnit_iff_isUnit_det Lm).2 hdet).unit, ?_⟩
  rw [IsUnit.unit_spec]
  exact heq

end GlobalTheory.LangWitt
