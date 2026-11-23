import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesFrameCols

theorem cols_pair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ρ : ℕ) (B : BesLev D ρ) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ i : Fin ρ, ∃ m₀ m₁ : n ⊕ Fin c, (∀ r, F.β r m₀ = s * p.xi ^ (ρ - i.val) * p.pr (B.d.e r i)) ∧ (∀ r, F.β r m₁ = s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (B.d.e' r i)) ∧ ∀ m, m ≠ m₁ → ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (B.V.gram r r') * F.β r' m = 0 := by
  intro D k _ _ _ _ p ρ B n _ _ c s FA F hF i
  obtain ⟨hc, h1, h2, h3, h4⟩ := hF
  subst hc
  set G := B.V.gram with hGdef
  have hGh : Gᴴ = G := by
    refine Matrix.ext fun a b => ?_
    simp only [G, Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.gram_star B.V b a
  have heG0 : (B.d.e)ᴴ * G * B.d.i₀ = 0 := by
    have h := congrArg Matrix.conjTranspose B.d.i₀e
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h
    rw [← hGdef, hGh] at h
    rw [← h, Matrix.mul_assoc]
  have heGe : (B.d.e)ᴴ * G * B.d.e = 0 := B.d.ee
  have heGe' : (B.d.e)ᴴ * G * B.d.e' = 1 := by
    have h := congrArg Matrix.conjTranspose B.d.e'e
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
    rw [← hGdef, hGh] at h
    rw [← h, Matrix.mul_assoc]
  have key : ∀ x : Fin B.V.rank → D.host.E, ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * p.pr (x r') =
      p.pr ((((B.d.e)ᴴ * G) *ᵥ x) i) := by
    intro x
    change ∑ r, ∑ r', LocMod.Witness.prH p _ * LocMod.Witness.prH p _ * LocMod.Witness.prH p _ = LocMod.Witness.prH p _
    simp only [← map_mul, ← map_sum]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have keyc : ∀ (a : k) (x : Fin B.V.rank → D.host.E), ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * (a * p.pr (x r')) =
      a * p.pr ((((B.d.e)ᴴ * G) *ᵥ x) i) := by
    intro a x
    rw [← key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r' _ => ?_
    ring
  have colM : ∀ {κ : Type} (M : Matrix (Fin B.V.rank) κ D.host.E) (j : κ), (((B.d.e)ᴴ * G) *ᵥ fun r => M r j) i = ((B.d.e)ᴴ * G * M) i j := by
    intro κ M j
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  refine ⟨Sum.inr ⟨i.val, by omega⟩, Sum.inr ⟨2 * ρ - i.val, by omega⟩, fun r => h2 i _ rfl r,
    fun r => h4 i _ (by simp only; omega) r, ?_⟩
  rintro (a | ⟨j, hj⟩) hm
  · have hM : ((B.d.e)ᴴ * G * (B.d.i₀ * B.o.iA)) = 0 := by rw [← Matrix.mul_assoc, heG0, Matrix.zero_mul]
    generalize B.d.i₀ * B.o.iA = M at h1 hM
    calc ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * F.β r' (Sum.inl a)
        = ∑ u, FA.β u a * ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * p.pr (M r' u) := by
          simp_rw [h1 _ a, Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r' _ => ?_
          refine Finset.sum_congr rfl fun u _ => ?_
          ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun u _ => ?_
          rw [key (fun r' => M r' u), colM, hM]
          simp [LocMod.Place.pr]
  · have hne : j ≠ 2 * ρ - i.val := fun h => hm (by subst h; rfl)
    rcases lt_trichotomy j ρ with hlt | heq | hgt
    · simp_rw [h2 ⟨j, hlt⟩ ⟨j, hj⟩ rfl]
      refine (keyc _ (fun r' => B.d.e r' ⟨j, hlt⟩)).trans ?_
      rw [colM, heGe]
      simp [LocMod.Place.pr]
    · simp_rw [h3 ⟨j, hj⟩ heq]
      refine (keyc _ (B.d.i₀ *ᵥ vecB B.o B.ζ)).trans ?_
      rw [Matrix.mulVec_mulVec, heG0, Matrix.zero_mulVec]
      simp [LocMod.Place.pr]
    · have hlt' : 2 * ρ - j < ρ := by omega
      simp_rw [h4 ⟨2 * ρ - j, hlt'⟩ ⟨j, hj⟩ (by simp only; omega)]
      refine (keyc _ (fun r' => B.d.e' r' ⟨2 * ρ - j, hlt'⟩)).trans ?_
      rw [colM, heGe', Matrix.one_apply_ne (fun h => hne (by rw [Fin.ext_iff] at h; simp only at h; omega))]
      simp [LocMod.Place.pr]

end GlobalTheory.BesFrameCols
