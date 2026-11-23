import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZero.SBBox

variable {D : D7}

theorem half_add {m n : ℕ} {e : AE D} {u t : Mx D m n} (hu : IsHalf e u) (ht : IsHalf e t) : IsHalf e (u + t) := by
  intro i j
  rw [Matrix.add_apply, mul_add, hu, ht]

theorem half_sub {m n : ℕ} {e : AE D} {u t : Mx D m n} (hu : IsHalf e u) (ht : IsHalf e t) : IsHalf e (u - t) := by
  intro i j
  rw [Matrix.sub_apply, mul_sub, hu, ht]

theorem half_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (N : ℕ) : IsHalf e (N • u) := by
  induction N with
  | zero => intro i j; rw [zero_smul, Matrix.zero_apply, mul_zero]
  | succ N ih => rw [succ_nsmul]; exact half_add ih hu

theorem half_mul {m n l : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (x : Mx D n l) :
    IsHalf e (u * x : Mx D m l) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [← mul_assoc, hu]

theorem half_of_res {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {t : WO S T}
    (h1 : IsHalf e (o.resS T t).1) (h2 : IsHalf e (o.resS T t).2) : IsHalf e t := by
  rw [← (o.resS T).symm_apply_apply t]
  exact half_add (half_mul h1 _) (half_mul h2 _)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {T L : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem zcol_add (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y y' : WO L T) :
    zcol β ζ (y + y') = zcol β ζ y + zcol β ζ y' := by
  unfold zcol
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  rw [Matrix.add_mulVec, Pi.add_apply, map_add]; rfl

theorem zcol_zero (β : Frame p T n) (ζ : Fin L.rank → D.host.E) : zcol β ζ 0 = 0 := by
  have := zcol_add β ζ 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem zcol_nsmul (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y : WO L T) (N : ℕ) :
    zcol β ζ (N • y) = N • zcol β ζ y := by
  induction N with
  | zero => rw [zero_smul, zero_smul, zcol_zero]
  | succ N ih => rw [succ_nsmul, succ_nsmul, zcol_add, ih]

theorem colFun_ne_zero (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (Λ : Submodule 𝒪[k] (n → k)) (y : WO L T) :
    colFun β ζ (vecInd Λ) y ≠ 0 ↔ IsHalf p.e y ∧ zcol β ζ y ∈ Λ := by
  unfold colFun vecInd
  by_cases h : IsHalf p.e y <;> by_cases h' : zcol β ζ y ∈ Λ <;> simp [h, h']

theorem colFun_add (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (Λ : Submodule 𝒪[k] (n → k)) (y u : WO L T)
    (hu : IsHalf p.e u) (hu' : zcol β ζ u ∈ Λ) :
    colFun β ζ (vecInd Λ) (y + u) = colFun β ζ (vecInd Λ) y := by
  have h1 : IsHalf p.e (y + u) ↔ IsHalf p.e y :=
    ⟨fun h => by simpa using half_sub h hu, fun h => half_add h hu⟩
  have h2 : zcol β ζ (y + u) ∈ Λ ↔ zcol β ζ y ∈ Λ := by
    rw [zcol_add]; exact Λ.add_mem_iff_left hu'
  unfold colFun vecInd
  rw [propext h1, propext h2]

theorem halfInd_ne_zero {m l : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m l)) (t : Mx D m l) :
    halfInd e Λ t ≠ 0 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  by_cases h : t ∈ Λ ∧ IsHalf e t <;> simp [h]

theorem isSBHalf_boxS_gen {S A : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n)
    (ΛA : AddSubgroup (WO A T)) (ΛS : AddSubgroup (WO S T)) (ΛT : Submodule 𝒪[k] (n → k))
    (hf : halfInd p.e ΛS = o.boxS T (halfInd p.e ΛA) (colFun β ζ (vecInd ΛT)))
    (Φ : WO A T → ℂ) (hΦ : IsSBHalf p.e ΛA Φ) :
    IsSBHalf p.e ΛS (o.boxS T Φ (colFun β ζ (vecInd ΛT))) := by
  have key : ∀ u : WO S T, (u ∈ ΛS ∧ IsHalf p.e u) ↔
      (((o.resS T u).1 ∈ ΛA ∧ IsHalf p.e (o.resS T u).1) ∧
        (IsHalf p.e (o.resS T u).2 ∧ zcol β ζ (o.resS T u).2 ∈ ΛT)) := by
    intro u
    rw [← halfInd_ne_zero, ← halfInd_ne_zero, ← colFun_ne_zero, hf, ← mul_ne_zero_iff]
    rfl
  obtain ⟨hs, N, hN, hinv, hsup⟩ := hΦ
  have hne : ∀ t, o.boxS T Φ (colFun β ζ (vecInd ΛT)) t ≠ 0 →
      Φ (o.resS T t).1 ≠ 0 ∧ IsHalf p.e (o.resS T t).2 ∧ zcol β ζ (o.resS T t).2 ∈ ΛT := by
    intro t ht
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 ht
    exact ⟨h1, (colFun_ne_zero β ζ ΛT _).1 h2⟩
  refine ⟨fun t ht => half_of_res o (hs _ (hne t ht).1) (hne t ht).2.1, N, hN, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (key u).1 ⟨hu, hu'⟩
    unfold OrthDec.boxS
    rw [map_add, map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, hinv _ h1 h2,
      colFun_add β ζ ΛT _ _ (half_nsmul h3 N) (by rw [zcol_nsmul]; exact nsmul_mem h4 N)]
  · obtain ⟨h1, h2, h3⟩ := hne t ht
    refine ((key (N • t)).2 ?_).1
    rw [map_nsmul, Prod.smul_fst, Prod.smul_snd]
    exact ⟨⟨hsup _ h1, half_nsmul (hs _ h1) N⟩, half_nsmul h2 N, by rw [zcol_nsmul]; exact nsmul_mem h3 N⟩

theorem isSBHalf_boxS : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (o.boxS T Φ (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT))) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ o ζ β _ _ _ ΛT hf Φ hΦ => isSBHalf_boxS_gen o ζ β _ _ ΛT hf Φ hΦ

end GlobalTheory.FinPl.ExtZero.SBBox

end
