import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.UnitriangularCoeff

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem sigR_inclR (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

def hRight (x : Fin n → R ⊗[F] E) : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hR R σ J x y
  map_add' y z := by
    simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hRight_apply (x y : Fin n → R ⊗[F] E) : hRight R σ J x y = hR R σ J x y := rfl

theorem hR_add_right (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y + z) = hR R σ J x y + hR R σ J x z := (hRight R σ J x).map_add y z

theorem hR_sub_right (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y - z) = hR R σ J x y - hR R σ J x z := (hRight R σ J x).map_sub y z

theorem hR_smul_right (x y : Fin n → R ⊗[F] E) (c : R ⊗[F] E) :
    hR R σ J x (c • y) = c * hR R σ J x y := (hRight R σ J x).map_smul c y

theorem hR_zero_right (x : Fin n → R ⊗[F] E) : hR R σ J x 0 = 0 := (hRight R σ J x).map_zero

theorem hR_ratV (x y : Fin n → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR R (hE σ J x y) := by
  simp only [hR, hE, Formalism.UG.hform, ratV, JR, Matrix.map_apply, map_sum, map_mul, sigR_inclR,
    AlgHom.coe_toRingHom, RingHom.coe_coe]

theorem hE_symm (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ.1 b a]
  ring

variable {R σ J}

theorem hermitian_flag_dual_basis (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1)) :
    hE σ J (P.f a) (F0 P c) = if c = a.castSucc then 1 else 0 := by
  induction c using Fin.lastCases with
  | last =>
    rw [F0, Fin.snoc_last, hP.2.2.2.2.1 a, if_neg (Fin.castSucc_lt_last a).ne']
  | cast c =>
    rw [F0, Fin.snoc_castSucc, hE_symm σ J hσ hJ, hP.2.2.1 c a]
    by_cases h : c = a
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e)), map_zero]

theorem pairR (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1)) :
    hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R (F0 P c)) = if c = a.castSucc then 1 else 0 := by
  rw [hR_ratV, hermitian_flag_dual_basis hσ hJ hP a c]
  split_ifs <;> simp only [map_one, map_zero]

theorem pair_sum (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1) → R ⊗[F] E) :
    hR R σ J (ratV (F := F) R (P.f a)) (∑ b, c b • ratV (F := F) R (F0 P b)) = c a.castSucc := by
  rw [← hRight_apply, map_sum]
  simp only [map_smul, hRight_apply, pairR hσ hJ hP, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem expand (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (b : Fin (r + 1)) (w : Fin n → R ⊗[F] E)
    (hw : w ∈ spanR (F := F) R (F0 P) {a | a < b}) :
    w = ∑ a, (if h : a < b then hR R σ J (ratV (F := F) R
      (P.f (a.castLT (lt_of_lt_of_le h (Fin.le_last b))))) w else 0) • ratV (F := F) R (F0 P a) := by
  unfold spanR at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    have hc' : c < b := hc
    symm
    rw [Finset.sum_eq_single c]
    · rw [dif_pos hc', pairR hσ hJ hP, Fin.castSucc_castLT, if_pos rfl, one_smul]
    · intro a _ hac
      split_ifs with h
      · rw [pairR hσ hJ hP, Fin.castSucc_castLT, if_neg (fun e => hac e.symm), zero_smul]
      · rw [zero_smul]
    · intro h; exact absurd (Finset.mem_univ c) h
  | zero =>
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs <;> simp [hR_zero_right]
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [hR_add_right, add_smul]
  | smul c x _ hx =>
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [hR_smul_right, smul_smul]

end Alg

theorem combine {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {r : ℕ} (b : Fin (r + 1))
    (G : Fin (r + 1) → M) (y : ∀ a : Fin (r + 1), a < b → A) :
    (∑ a, (if h : a < b then y a h else 0) • G a) + G b =
      ∑ a, (if a = b then 1 else if h : a < b then y a h else 0) • G a := by
  have key : ∀ a, (if a = b then (1 : A) else if h : a < b then y a h else 0) • G a =
      (if h : a < b then y a h else 0) • G a + (if a = b then G a else 0) := by
    intro a
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]

theorem exists_coeff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ ν : Ssub (Fv F v) σ J P → ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), Continuous ν ∧ ∀ (s : Ssub (Fv F v) σ J P) (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), x = ν s ↔ ∀ b, lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a) := by
  intro F E _ _ _ _ _ σ hσ n J hJ v r P T hP
  have hss : ∀ x, σ (σ x) = x := sigma_sigma σ hσ
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have ha : ∀ p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}, (p.1.1 : ℕ) < r :=
    fun p => lt_of_lt_of_le p.2 (Fin.le_last _)
  refine ⟨fun s p => hR (Fv F v) σ J (ratV (F := F) (Fv F v) (P.f (p.1.1.castLT (ha p))))
      (lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P p.1.2))), ?_, ?_⟩
  · refine continuous_pi fun p => ?_
    have hM : Continuous fun s : Ssub (Fv F v) σ J P =>
        ((HA.mat (Fv F v) σ J (s : HA (Fv F v) σ J) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hMij : ∀ i j, Continuous fun s : Ssub (Fv F v) σ J P =>
        ((HA.mat (Fv F v) σ J (s : HA (Fv F v) σ J) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp hM)
    simp only [hR, Formalism.UG.hform, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      continuous_const.mul (continuous_finset_sum _ fun k _ => (hMij j k).mul continuous_const)
  · intro s x
    constructor
    · rintro rfl b
      have hU : lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b)) -
          ratV (F := F) (Fv F v) (F0 P b) ∈ spanR (F := F) (Fv F v) (F0 P) {a | a < b} := s.2 b
      have e1 := sub_eq_iff_eq_add.mp (expand hss hJ hP b _ hU)
      refine e1.trans ((combine b _ _).trans ?_)
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      split_ifs with h1 h2
      · rfl
      · rw [hR_sub_right, pairR hss hJ hP, Fin.castSucc_castLT, if_neg h2.ne', sub_zero]
      · rfl
    · intro H
      funext p
      obtain ⟨⟨a, b⟩, h⟩ := p
      symm
      show hR (Fv F v) σ J (ratV (F := F) (Fv F v) (P.f (a.castLT (lt_of_lt_of_le h (Fin.le_last b)))))
        (lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b))) = x ⟨(a, b), h⟩
      rw [H b, pair_sum hss hJ hP, Fin.castSucc_castLT, if_neg h.ne, dif_pos h]

end GlobalTheory.UnitriangularCoeff
