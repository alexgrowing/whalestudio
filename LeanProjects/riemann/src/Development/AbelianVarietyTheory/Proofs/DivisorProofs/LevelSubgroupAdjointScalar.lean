import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

namespace GlobalTheory.IwasawaTriv

theorem absE_eigen_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (a : GL (Fin n) (AF F ⊗[F] E)) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ k ∈ levelAll σ J L a, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J k).1 * adMat F x = l.1 • adMat F x → absE F E l = 1 := by
  intro F E _ _ _ _ _ σ hσ n J L hL a x pL hpx k hk l hkl
  haveI := hL
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  set X := adMat F x with hX
  set Y := pL.map (inclR (F := F) (AF F)) with hY
  have hYX : Y * X = 1 := by
    rw [hX, hY, adMat, ← Matrix.map_mul, hpx]
    simp
  let M : GAd σ J → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := fun g => (matHom _ σ J g).1
  have hMc : Continuous M := Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous
  have hMmul : ∀ g h, M (g * h) = M g * M h := fun g h => by simp [M]
  have hMinv : ∀ g, M g⁻¹ * M g = 1 := fun g => by simp [M]
  have hM1 : M 1 = 1 := by simp [M]
  let φ : GAd σ J → AF F ⊗[F] E := fun g => (Y * M g * X) 0 0
  have hφc : Continuous φ := by
    have : Continuous fun g => Y * M g * X := (continuous_const.matrix_mul hMc).matrix_mul continuous_const
    exact (continuous_apply 0).comp ((continuous_apply 0).comp this)
  have hdet : ∀ g (c : AF F ⊗[F] E), M g * X = c • X → φ g = c := by
    intro g c h
    simp only [φ, Matrix.mul_assoc, h, Matrix.mul_smul, hYX]
    simp

  have hφ1 : φ 1 = 1 := hdet 1 1 (by rw [hM1, one_smul, Matrix.one_mul])
  have hstep : ∀ g h (c d : AF F ⊗[F] E), M g * X = c • X → M h * X = d • X → M (g * h) * X = (d * c) • X := by
    intro g h c d hg hh
    rw [hMmul, Matrix.mul_assoc, hh, Matrix.mul_smul, hg, smul_smul]
  have hmem : ∀ g, (∃ c : AF F ⊗[F] E, M g * X = c • X) → M g * X = φ g • X := by
    rintro g ⟨c, h⟩
    rw [hdet g c h]; exact h
  let S : Set (GAd σ J) := {g | M g * X = φ g • X ∧ M g⁻¹ * X = φ g⁻¹ • X}
  have hinvφ : ∀ g ∈ S, φ g * φ g⁻¹ = 1 := by
    intro g hg
    have e := hstep g⁻¹ g _ _ hg.2 hg.1
    rw [inv_mul_cancel] at e
    rw [← hdet 1 _ e, hφ1]
  let P : Subgroup (GAd σ J) :=
    { carrier := S
      one_mem' := ⟨by rw [hM1, hφ1, one_smul, Matrix.one_mul], by rw [inv_one, hM1, hφ1, one_smul, Matrix.one_mul]⟩
      mul_mem' := fun {g h} hg hh => ⟨hmem _ ⟨_, hstep _ _ _ _ hg.1 hh.1⟩,
        hmem _ ⟨_, by rw [_root_.mul_inv_rev]; exact hstep _ _ _ _ hh.2 hg.2⟩⟩
      inv_mem' := fun {g} hg => ⟨hg.2, by rw [inv_inv]; exact hg.1⟩ }
  have hP : IsClosed (P : Set (GAd σ J)) := by
    show IsClosed S
    exact (isClosed_eq (hMc.matrix_mul continuous_const) (hφc.smul continuous_const)).inter
      (isClosed_eq ((hMc.comp continuous_inv).matrix_mul continuous_const) ((hφc.comp continuous_inv).smul continuous_const))
  let u : P →* (AF F ⊗[F] E)ˣ :=
    { toFun := fun p => ⟨φ p, φ (p : GAd σ J)⁻¹, hinvφ p p.2, by rw [mul_comm]; exact hinvφ p p.2⟩
      map_one' := Units.ext (by
        change φ ((1 : P) : GAd σ J) = 1
        rw [OneMemClass.coe_one]; exact hφ1)
      map_mul' := fun p q => Units.ext (by
        change φ ((p * q : P) : GAd σ J) = φ p * φ q
        rw [Subgroup.coe_mul, hdet _ _ (hstep _ _ _ _ p.2.1 q.2.1), mul_comm]) }
  have hu : Continuous u := Units.continuous_iff.2
    ⟨hφc.comp continuous_subtype_val, (hφc.comp continuous_inv).comp continuous_subtype_val⟩
  have hδ : Continuous ((absE F E).comp u) := (GlobalTheory.Doubling.continuous_absE (F := F) (E := E)).comp hu
  have h2 : M k⁻¹ * X = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X := by
    have e : M k⁻¹ * (M k * X) = X := by rw [← Matrix.mul_assoc, hMinv, Matrix.one_mul]
    have hkl' : M k * X = (l : AF F ⊗[F] E) • X := hkl
    rw [hkl', Matrix.mul_smul] at e
    conv_rhs => rw [← e]
    rw [smul_smul, Units.inv_mul, one_smul]
  have hkP : k ∈ P := ⟨hmem k ⟨_, hkl⟩, hmem _ ⟨_, h2⟩⟩
  have key := GlobalTheory.Doubling.triv_of_isCompact (δ := (absE F E).comp u) (K := levelAll σ J L a) hP hδ
    (GlobalTheory.Doubling.isCompact_levelAll hσ J L a) ⟨k, hkP⟩ hk
  have hul : u ⟨k, hkP⟩ = l := Units.ext (hdet k l hkl)
  change absE F E (u ⟨k, hkP⟩) = 1 at key
  rwa [hul] at key

end GlobalTheory.IwasawaTriv
