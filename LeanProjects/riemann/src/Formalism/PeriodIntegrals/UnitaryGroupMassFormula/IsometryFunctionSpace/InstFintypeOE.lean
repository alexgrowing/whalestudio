import Mathlib
import Formalism.PeriodIntegrals.IsoFunV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryFunctionSpace.DetSubmatrixNoninj

open Matrix Finset MvPolynomial

noncomputable section

namespace PI.IsoFunVW

open PI.IsoFunV

noncomputable instance instFintypeOE (m n : ℕ) : Fintype (Fin m ↪o Fin n) :=
  @Fintype.ofFinite _ (finite_oe m n)

noncomputable instance instFintypeCC {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) : Fintype (ColChoice N nu) := by
  unfold ColChoice; infer_instance

def linW {σ : Type} (w : (σ →₀ ℕ) → ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun P := ∑ α ∈ P.support, coeff α P * w α
  map_add' P Q := by
    classical
    have key : ∀ (R : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)), R.support ⊆ S →
        ∑ α ∈ R.support, coeff α R * w α = ∑ α ∈ S, coeff α R * w α := by
      intro R S hS
      refine Finset.sum_subset hS (fun α _ hα => ?_)
      rw [MvPolynomial.mem_support_iff, not_not] at hα
      simp [hα]
    rw [key (P + Q) (P.support ∪ Q.support) support_add,
      key P (P.support ∪ Q.support) subset_union_left,
      key Q (P.support ∪ Q.support) subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [coeff_add, add_mul]
  map_smul' c P := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine (Finset.sum_subset support_smul (fun α _ hα => ?_)).trans ?_
    · rw [MvPolynomial.mem_support_iff, not_not] at hα
      simp [hα]
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [coeff_smul, smul_eq_mul, mul_assoc]

theorem linW_apply {σ : Type} (w : (σ →₀ ℕ) → ℂ) (P : MvPolynomial σ ℂ) :
    linW w P = ∑ α ∈ P.support, coeff α P * w α := rfl

def wTh {T : Type} [Fintype T] {N N' : ℕ} (Θ : VC T N N' → ℂ) (α : Mono T N N') : ℂ :=
  (α.prod fun _ n => (n.factorial : ℂ)) * taylor Θ α

theorem applyAt0_eq {T : Type} [Fintype T] {N N' : ℕ} (P : MvPolynomial (Idx T N N') ℂ)
    (Θ : VC T N N' → ℂ) : applyAt0 P Θ = linW (wTh Θ) P := by
  rw [linW_apply, applyAt0]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [wTh, mul_assoc]

theorem minY_map {Lt k k' : Type} [Fintype Lt] [CommRing k] [CommRing k'] (f : k →+* k')
    (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu) (y : Lt → Fin N → ℕ → k) :
    f (minY N nu J y) = minY N nu J (fun z a j => f (y z a j)) := by
  simp only [minY, map_prod, RingHom.map_det]
  rfl

def yfr {Lt T : Type} (tp : Lt → T) {N N' : ℕ} (s : T → ℂ) (x : Lt → Fin N → ℕ → ℂ) :
    Lt → Fin N' → ℕ → MvPolynomial (Idx T N N') ℂ :=
  fun z a j => ∑ b : Fin N, C (s (tp z)) * X ((tp z, a, b) : Idx T N N') * C (x z b j)

theorem prod_sum_cc {Lt : Type} [Fintype Lt] [DecidableEq Lt] {R : Type} [CommRing R] (N : ℕ)
    (nu : Lt → YoungDiagram)
    (F : ∀ (z : Lt) (c : Fin ((nu z).rowLen 0)), (Fin ((nu z).colLen c) ↪o Fin N) → R) :
    ∏ z, ∏ c, ∑ Jc, F z c Jc = ∑ J : ColChoice N nu, ∏ z, ∏ c, F z c (J z c) := by
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)

theorem key_id {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (x : Lt → Fin N → ℕ → ℂ) (I : ColChoice N' nu) :
    ∑ J : ColChoice N nu, PIJ tp nu s I J * C (minY N nu J x) = minY N' nu I (yfr tp s x) := by
  have hR : ∀ J : ColChoice N nu, PIJ tp nu s I J * C (minY N nu J x) =
      ∏ z, ∏ c : Fin ((nu z).rowLen 0),
        (Matrix.of fun i k : Fin ((nu z).colLen c) =>
          C (s (tp z)) * X ((tp z, I z c i, J z c k) : Idx T N N')).det *
        (Matrix.of fun i j : Fin ((nu z).colLen c) =>
          (C (x z (J z c i) (j : ℕ)) : MvPolynomial (Idx T N N') ℂ)).det := by
    intro J
    rw [minY_map]
    simp only [PIJ, minY, ← Finset.prod_mul_distrib]
  have hL : minY N' nu I (yfr tp s x) = ∏ z, ∏ c : Fin ((nu z).rowLen 0),
      ∑ Jc : Fin ((nu z).colLen c) ↪o Fin N,
        (Matrix.of fun i k : Fin ((nu z).colLen c) =>
          C (s (tp z)) * X ((tp z, I z c i, Jc k) : Idx T N N')).det *
        (Matrix.of fun i j : Fin ((nu z).colLen c) =>
          (C (x z (Jc i) (j : ℕ)) : MvPolynomial (Idx T N N') ℂ)).det := by
    simp only [minY]
    refine Finset.prod_congr rfl (fun z _ => Finset.prod_congr rfl (fun c _ => ?_))
    have hcb := det_mul_eq_sum_oe
      (Matrix.of fun (i : Fin ((nu z).colLen c)) (b : Fin N) =>
        C (s (tp z)) * X ((tp z, I z c i, b) : Idx T N N'))
      (Matrix.of fun (b : Fin N) (j : Fin ((nu z).colLen c)) =>
        (C (x z b (j : ℕ)) : MvPolynomial (Idx T N N') ℂ))
    have hm : (Matrix.of fun i j : Fin ((nu z).colLen c) => yfr tp s x z (I z c i) (j : ℕ)) =
        (Matrix.of fun (i : Fin ((nu z).colLen c)) (b : Fin N) =>
          C (s (tp z)) * X ((tp z, I z c i, b) : Idx T N N')) *
        (Matrix.of fun (b : Fin N) (j : Fin ((nu z).colLen c)) =>
          (C (x z b (j : ℕ)) : MvPolynomial (Idx T N N') ℂ)) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.of_apply, yfr]
    rw [hm, hcb]
    rfl
  rw [hL, prod_sum_cc]
  exact Finset.sum_congr rfl (fun J _ => hR J)

theorem AOp_eq {Lt T : Type} [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ) (φ : LaC N nu) (I : ColChoice N' nu) :
    AOp tp nu s Θ φ I = ∑ J : ColChoice N nu, applyAt0 (PIJ tp nu s I J) Θ * φ J := by
  rw [AOp, finsum_eq_sum_of_fintype]

theorem AOp_hv {Lt T : Type} [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ) (x : Lt → Fin N → ℕ → ℂ) :
    AOp tp nu s Θ (hvC N nu x) = fun I => linW (wTh Θ) (minY N' nu I (yfr tp s x)) := by
  funext I
  rw [AOp_eq, ← key_id, map_sum]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [applyAt0_eq, mul_comm (PIJ tp nu s I J), ← MvPolynomial.smul_eq_C_mul, map_smul,
    smul_eq_mul, mul_comm]
  rfl

theorem mem_Vnu_poly {Lt σ : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (y : Lt → Fin N → ℕ → MvPolynomial σ ℂ) :
    (fun I => L (minY N nu I y)) ∈ Vnu N nu := by
  classical
  rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := Vnu N nu),
    Submodule.mem_dualCoannihilator]
  intro f hf
  rw [Submodule.mem_dualAnnihilator] at hf
  rw [LinearMap.pi_apply_eq_sum_univ f]
  set e : ColChoice N nu → ℂ := fun I => f (fun J => if I = J then 1 else 0) with he
  have hQ : (∑ I : ColChoice N nu, e I • minY N nu I y) = 0 := by
    apply MvPolynomial.funext
    intro p
    have hv : hvC N nu (fun z a j => eval p (y z a j)) ∈ Vnu N nu :=
      Submodule.subset_span ⟨_, rfl⟩
    have h0 := hf _ hv
    rw [LinearMap.pi_apply_eq_sum_univ f] at h0
    rw [map_sum, map_zero, ← h0]
    refine Finset.sum_congr rfl (fun I _ => ?_)
    simp only [MvPolynomial.smul_eval, smul_eq_mul]
    rw [mul_comm]
    congr 1
    exact minY_map (eval p) N nu I y
  have := congrArg L hQ
  rw [map_sum, map_zero] at this
  refine Eq.trans (Finset.sum_congr rfl (fun I _ => ?_)) this
  simp only [map_smul, smul_eq_mul, he]
  ring

def AOpLin {Lt T : Type} [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ) : LaC N nu →ₗ[ℂ] LaC N' nu where
  toFun φ := AOp tp nu s Θ φ
  map_add' φ ψ := by
    funext I
    simp only [AOp_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    funext I
    simp only [AOp_eq, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    ring

theorem isoFunV_main : IsoFunV := by
  intro Lt T _ _ _ tp N N' nu s Θ φ hφ
  have hle : Vnu N nu ≤ (Vnu N' nu).comap (AOpLin tp nu s Θ) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    show AOp tp nu s Θ (hvC N nu x) ∈ Vnu N' nu
    rw [AOp_hv]
    exact mem_Vnu_poly N' nu _ _
  exact hle hφ

end PI.IsoFunVW

end
