import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevRestrict

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_hatL {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      (M.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨M *ᵥ y, hM y hy, ?_⟩
    funext i
    exact RingHom.map_mulVec _ M y i
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul s x _ hx =>
    have := Submodule.smul_mem _ s hx
    rw [Subring.smul_def, ← mulVec_smul] at this
    rw [Subring.smul_def]
    exact this

theorem map_smul {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') (𝔪 : Ideal (𝓞 E)) :
    ∀ y ∈ 𝔪 • Λ, M *ᵥ y ∈ 𝔪 • Λ' := by
  have : 𝔪 • Λ ≤ (𝔪 • Λ').comap ((Matrix.mulVecLin M).restrictScalars (𝓞 E)) := by
    rw [Submodule.smul_le]
    intro r hr z hz
    show M *ᵥ (r • z) ∈ 𝔪 • Λ'
    rw [mulVec_smul]
    exact Submodule.smul_mem_smul hr (hM z hz)
  exact fun y hy => this hy

theorem map_hatL_smul {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') (𝔪 : Ideal (𝓞 E)) :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ),
      (M.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ') :=
  map_hatL M (map_smul M hM 𝔪)

end General

open GlobalTheory.UnitaryEmbeddingProperties

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem qM_mul_a (d : HermitianOrthogonalExtensionData A B c ε) : qM d * d.a = 0 := by
  rw [qM, Matrix.mul_assoc, d.perp, Matrix.mul_zero]

theorem qM_lat (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ x ∈ d.lat Λ 𝔟, qM d *ᵥ x ∈ Λ := by
  intro x hx
  obtain ⟨y, hy, u, -, rfl⟩ := hx
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, qM_mul, qM_mul_a, one_mulVec, zero_mulVec, add_zero]
  exact hy

theorem frameMat_lat (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ y ∈ Λ, frameMat B A d.ι *ᵥ y ∈ d.lat Λ 𝔟 :=
  fun y hy => ⟨y, hy, 0, fun p => (𝔟 p).zero_mem, by simp⟩

set_option maxHeartbeats 2000000 in

theorem finE_mem_congLev : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (𝔪 : Ideal (𝓞 D.host.E)) (h : GA D A), Lev.finE B (stabilizerEmbedding d h) ∈ congLev D.sp.cm B.gram (d.lat Λ 𝔟) 𝔪 →
      Lev.finE A h ∈ congLev D.sp.cm A.gram Λ 𝔪 := by
  intro D A B c ε d Λ 𝔟 𝔪 h hg
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin B.rank) (Fin A.rank) (Lev.EAf D),
      P = (frameMat B A d.ι).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin A.rank) (Fin B.rank) (Lev.EAf D),
      Q = (qM d).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g, g = Lev.finE B (stabilizerEmbedding d h) := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = Lev.finE A h := ⟨_, rfl⟩
  rw [← hgdef] at hg
  rw [← hkdef]
  have hQP : HMul.hMul Q P = (1 : Matrix (Fin A.rank) (Fin A.rank) (Lev.EAf D)) := by
    rw [hP, hQ]; exact qM_mul_map _ d
  have e : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E),
      (M.map (incA D)).map (GlobalTheory.LevSplit.finSw D) =
        M.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := fun M => by
    ext i j; exact GlobalTheory.LevSplit.finSw_incA _
  have hG : g.1 = ex P Q k.1 := by
    rw [hgdef, hkdef, GlobalTheory.LevSplit.finE_val, GlobalTheory.LevSplit.finE_val, hP, hQ]
    show ((matHom B (stabilizerEmbedding d h)).1).map _ = ex _ _ (((matHom A h).1).map _)
    rw [unitaryEmbedding_matrix_formula, ex_map, e, e]
  have hGP : HMul.hMul g.1 P = HMul.hMul P k.1 := by rw [hG]; exact ex_mul_P P Q hQP _
  have hk : k.1 = HMul.hMul (HMul.hMul Q g.1) P := by
    rw [Matrix.mul_assoc, hGP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hPl : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, P *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ 𝔟) :=
    by subst hP; exact map_hatL (F := D.host.F) (frameMat B A d.ι) (frameMat_lat d Λ 𝔟)
  have hQl : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ 𝔟), Q *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    by subst hQ; exact map_hatL (F := D.host.F) (qM d) (qM_lat d Λ 𝔟)
  rw [mem_congLev] at hg
  have g2 := hg.2.1
  have g3 := hg.2.2
  rw [mem_congLev]
  refine ⟨?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun x hx => ?_⟩
  · rw [hkdef]; exact GlobalTheory.LevSplit.finE_mem_UA A h
  · rw [hk, ← mulVec_mulVec, ← mulVec_mulVec]; exact hQl _ ((g2 _).1 (hPl x hx))
  · have h1 := hPl _ hx
    rw [mulVec_mulVec, ← hGP, ← mulVec_mulVec] at h1
    have h2 := hQl _ ((g2 _).2 h1)
    rwa [mulVec_mulVec, hQP, one_mulVec] at h2
  · have e2 : k.1 *ᵥ x - x = Q *ᵥ (g.1 *ᵥ (P *ᵥ x) - P *ᵥ x) := by
      rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hQP, one_mulVec, hk]
    rw [e2, hQ]
    exact map_hatL_smul (F := D.host.F) (qM d) (qM_lat d Λ 𝔟) 𝔪 _ (g3 _ (hPl x hx))

end GlobalTheory.LevRestrict
