import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplex
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

namespace GlobalTheory.IwArchLine

theorem form_map_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {m k l : Type} [Fintype m] (M : Matrix m k E) (J : Matrix m m E) (N : Matrix m l E) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (M.map (inclR (F := F) R)) * J.map (inclR (F := F) R) * N.map (inclR (F := F) R) =
      (cT (σ : E →+* E) M * J * N).map (inclR (F := F) R) := by
  have h1 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (M.map (inclR (F := F) R)) = (cT (σ : E →+* E) M).map (inclR (F := F) R) := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  rw [h1, Matrix.map_mul, Matrix.map_mul]

theorem exists_q_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (a : GL (Fin n) (AF F ⊗[F] E)), IsMajorantFrame σ J a → ∀ (w : InfinitePlace F) (g : GArch σ J w), ∃ q k : GArch σ J w, k ∈ stabArch σ J w (bc (compInf F E w) a) ∧ g = q * k ∧ ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1 := by
  intro F E _ _ _ _ _ σ hcm n J _ x y hx hxy a ha w g
  obtain ⟨τ⟩ : Nonempty (GlobalTheory.AdelicU.EmbOver E w) := inferInstance
  obtain ⟨ε, hε⟩ := ha w
  have hXiso := form_map_inclR (F := F) w.Completion σ x J x
  rw [hx, Matrix.map_zero _ (map_zero _)] at hXiso
  obtain ⟨K, hK, hK1, β, hβ⟩ := GlobalTheory.Core.Rk.IwArch.iw_iso_cols (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ)
    (GlobalTheory.AdelicU.infEmb τ) (GlobalTheory.AdelicU.infEmb_bijective hcm τ) (fun z => (GlobalTheory.AdelicU.infEmb_sigR hcm τ z).symm)
    (bc (compInf F E w) a) ε hε _ hXiso (GlobalTheory.AdelicU.matHom w.Completion σ J g) g.2
  let kk : GArch σ J w := ⟨K, hK⟩
  have hPX := form_map_inclR (F := F) w.Completion σ y J x
  rw [hxy, Matrix.map_one _ (map_zero _) (map_one _)] at hPX
  set X := x.map (inclR (F := F) w.Completion) with hXdef
  set P := cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (y.map (inclR (F := F) w.Completion)) *
    J.map (inclR (F := F) w.Completion) with hPdef
  set Q : GL (Fin n) (w.Completion ⊗[F] E) := GlobalTheory.AdelicU.matHom w.Completion σ J g * K⁻¹ with hQ
  have hQX : Q.1 * X = X * β := hβ
  have hX' : X = (Q⁻¹).1 * X * β := by
    rw [Matrix.mul_assoc, ← hQX, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hleft : (P * (Q⁻¹).1 * X) * β = 1 := by
    rw [← hPX]; conv_rhs => rw [hX']
    simp only [Matrix.mul_assoc]
  let βu : GL (Fin 1) (w.Completion ⊗[F] E) := ⟨β, P * (Q⁻¹).1 * X, mul_eq_one_comm.1 hleft, hleft⟩
  refine ⟨g * kk⁻¹, kk, GlobalTheory.AdelicU.mem_stabArch.2 hK1, by group, βu, ?_⟩
  have : (GlobalTheory.AdelicU.matHom w.Completion σ J (g * kk⁻¹)) = Q := by
    rw [map_mul, map_inv]; rfl
  rw [this]; exact hQX

end GlobalTheory.IwArchLine
