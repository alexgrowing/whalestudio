import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflectionsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAnisotropicOrthogonalBasisHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.QuasiReflectionEqUnitaryTransvectionMul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidNormalDetOneStatement

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Gen

theorem tv_zero {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
    (x : Fin n → R) : tv σ G x 0 = 1 := by
  ext a b
  simp [tv]

end GlobalTheory.UTrans.Gen

namespace GlobalTheory.UTrans

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private theorem refl_eq_tv_sub_one_div_hf {F E : Type} [Field F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) :
    _root_.GlobalTheory.UnRep.refl c G x u =
      _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x ((u - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, _root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec,
    _root_.GlobalTheory.UTrans.Model.tv_mulVec]
  change v + ((u - 1) * _root_.GlobalTheory.UTrans.hf (c : E →+* E) G v x /
    _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) • x = _
  congr 2
  ring

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private theorem det_refl_eq_of_hermE_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E)
    (hx : _root_.GlobalTheory.UnRep.hermE c G x x ≠ 0) :
    (_root_.GlobalTheory.UnRep.refl c G x u).det = u := by
  unfold _root_.GlobalTheory.UnRep.refl
  have hw : (G.mulVec fun b => c (x b)) ⬝ᵥ x = _root_.GlobalTheory.UnRep.hermE c G x x :=
    (_root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot c G x x).symm
  have hmat : ((u - 1) / _root_.GlobalTheory.UnRep.hermE c G x x) •
      Matrix.vecMulVec x (G.mulVec fun b => c (x b)) =
      Matrix.replicateCol Unit (((u - 1) / _root_.GlobalTheory.UnRep.hermE c G x x) • x) *
        Matrix.replicateRow Unit (G.mulVec fun b => c (x b)) := by
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, mul_assoc]
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hw, smul_eq_mul]
  field_simp
  ring

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

theorem _root_.GlobalTheory.UTrans.isU_eq_tv_mul_tvGen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.UTrans.IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ _root_.GlobalTheory.UTrans.hf (c : E →+* E) G z z = 0) → ∀ γ, _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G γ → (∀ x, _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 → ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G, γ = _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x ((γ.det - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) * m) ∧ (γ.det = 1 → γ ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G) := by
  intro F E _ _ _ _ _ c n G hG hiso γ hγ
  have hG' : _root_.GlobalTheory.UnRep.IsHermForm c G := by
    refine ⟨hG.invol, ?_, hG.herm,
      hG.det_ne⟩
    intro h1
    obtain ⟨a, ha⟩ := hG.ne_id
    apply ha
    rw [h1]
    rfl
  have hγ' : _root_.GlobalTheory.UnRep.IsUnE c G γ := fun v w => hγ v w
  obtain ⟨l, hl, hγl⟩ := _root_.GlobalTheory.UnRep.isUnE_eq_prod_refl F E c n G hG' γ hγ'
  have hnorm := (_root_.GlobalTheory.UTrans.tvGen_normal E n (c : E →+* E) G hG).2
  have main : ∀ x, _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 →
      ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G,
        γ = _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x
          ((γ.det - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) * m := by
    intro x hx
    have hx' : _root_.GlobalTheory.UnRep.hermE c G x x ≠ 0 := hx
    obtain ⟨_, _, hmul, hunit⟩ := _root_.GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG' x hx'

    have key : ∀ l' : List ((Fin n → E) × E),
        (∀ p ∈ l', _root_.GlobalTheory.UnRep.hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) →
        ∃ M ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G, ∃ U : E, U * c U = 1 ∧
          (l'.map fun p => _root_.GlobalTheory.UnRep.refl c G p.1 p.2).prod =
            M * _root_.GlobalTheory.UnRep.refl c G x U := by
      intro l' hl'
      induction l' with
      | nil =>
        refine ⟨1, Submonoid.one_mem _, 1, by simp, ?_⟩
        obtain ⟨_, h1, _, _⟩ := _root_.GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG' x hx'
        simp [h1]
      | cons p l' ih =>
        obtain ⟨M, hM, U, hU, hprod⟩ := ih fun q hq => hl' q (List.mem_cons_of_mem _ hq)
        obtain ⟨hp1, hp2⟩ := hl' p List.mem_cons_self
        obtain ⟨m₁, hm₁, hq₁⟩ := _root_.GlobalTheory.UTrans.quasiReflection_eq_tvGen_mul E n (c : E →+* E) G hG hiso
          p.1 x p.2 hp1 hx hp2
        obtain ⟨M', hM', hcomm, _⟩ := (hnorm M hM).2.2.2 _ ((hunit p.2 hp2) : _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G _)
        refine ⟨m₁ * M', Submonoid.mul_mem _ hm₁ hM', p.2 * U, ?_, ?_⟩
        · rw [map_mul]
          calc p.2 * U * (c p.2 * c U) = (p.2 * c p.2) * (U * c U) := by ring
            _ = 1 := by rw [hp2, hU, one_mul]
        · rw [List.map_cons, List.prod_cons, hprod, refl_eq_tv_sub_one_div_hf, hq₁,
            ← refl_eq_tv_sub_one_div_hf, ← hmul]
          calc m₁ * _root_.GlobalTheory.UnRep.refl c G x p.2 * (M * _root_.GlobalTheory.UnRep.refl c G x U)
              = m₁ * (_root_.GlobalTheory.UnRep.refl c G x p.2 * M) * _root_.GlobalTheory.UnRep.refl c G x U := by
                simp only [mul_assoc]
            _ = m₁ * (M' * _root_.GlobalTheory.UnRep.refl c G x p.2) * _root_.GlobalTheory.UnRep.refl c G x U := by
                rw [hcomm]
            _ = _ := by simp only [mul_assoc]
    obtain ⟨M, hM, U, hU, hprod⟩ := key l hl
    have hγM : γ = M * _root_.GlobalTheory.UnRep.refl c G x U := hγl.trans hprod
    have hdet : γ.det = U := by
      rw [hγM, Matrix.det_mul, (hnorm M hM).2.1, one_mul, det_refl_eq_of_hermE_ne_zero c G x U hx']
    obtain ⟨_, _, _, m'', hm'', hcomm⟩ := (hnorm M hM).2.2.2 _ ((hunit U hU) : _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G _)
    refine ⟨m'', hm'', ?_⟩
    rw [hdet, hγM, hcomm, refl_eq_tv_sub_one_div_hf]
  refine ⟨main, fun h1 => ?_⟩
  obtain ⟨z, hz, _⟩ := hiso
  obtain ⟨i, -⟩ := Function.ne_iff.mp hz
  obtain ⟨y, hyy, -, -⟩ := _root_.GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis F E c n G hG'
  obtain ⟨m, hm, hγm⟩ := main (y i) (hyy i)
  have h0 : _root_.GlobalTheory.UTrans.tv (c : E →+* E) G (y i) 0 = 1 := by
    unfold _root_.GlobalTheory.UTrans.tv
    ext a b
    simp
  rw [h1, sub_self, zero_div, h0, one_mul] at hγm
  rw [hγm]
  exact hm

end GlobalTheory.UTrans
