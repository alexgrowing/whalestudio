import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxMono

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

section Gen

variable {E K : Type*} [Field E] [CommRing K] {r : ℕ}

theorem zLoc_mono (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) (σ : Fin (r + 1) → Fin (r + 1))
    (ν : Fin (r + 1) → E) :
    zLoc ι cj Dd (mono σ ν) = mono σ (fun a => Dd (σ a) * cj (Dd a) * ι (ν a)) := by
  ext a b
  simp only [zLoc, mono, Matrix.of_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem zhatOM_mono (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) :
    ZhatOM (mono σ ν) = mono σ (fun a => (-1) ^ (r - (σ a).val) * ν a) := by
  ext a b
  simp only [ZhatOM, mono, Matrix.of_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem linG_mono {F : Type*} [Field F] [Algebra F K] (e : K ≃ₐ[F] F × F) (q : F) {σ : Fin (r + 1) → Fin (r + 1)}
    (hσ : ∀ a, σ (σ a) = a) (ν : Fin (r + 1) → K) :
    linG e q (mono σ ν) = mono σ (fun a => e.symm ((e (ν a)).1 / q, -((e (ν (σ a))).2 / q))) := by
  ext a b
  simp only [linG, mono, Matrix.of_apply]
  by_cases h : b = σ a
  · subst h
    rw [if_pos rfl, if_pos (hσ a).symm, if_pos rfl]
  · have h' : ¬ a = σ b := fun h' => h (by rw [h', hσ])
    rw [if_neg h, if_neg h', if_neg h]
    simp

theorem fix_single {K : Type*} [CommRing K] {l ρ : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hl : IsLoUni l)
    (hρ : IsUpUni ρ) (κ : K) :
    l * Matrix.single (Fin.last r) (Fin.last r) κ * ρ = Matrix.single (Fin.last r) (Fin.last r) κ := by
  ext x y
  rw [mul_single_mul]
  have h1 : l x (Fin.last r) = if x = Fin.last r then 1 else 0 := by
    by_cases hx : x = Fin.last r
    · subst hx; rw [if_pos rfl]; exact (hl _ _).2 rfl
    · rw [if_neg hx]; exact (hl _ _).1 (lt_of_le_of_ne (Fin.le_last x) hx)
  have h2 : ρ (Fin.last r) y = if y = Fin.last r then 1 else 0 := by
    by_cases hy : y = Fin.last r
    · subst hy; rw [if_pos rfl]; exact (hρ _ _).2 rfl
    · rw [if_neg hy]; exact (hρ _ _).1 (lt_of_le_of_ne (Fin.le_last y) hy)
  rw [h1, h2, Matrix.single_apply]
  by_cases hx : x = Fin.last r <;> by_cases hy : y = Fin.last r
  · subst hx; subst hy; simp
  · simp [hy, Ne.symm hy]
  · simp [hx, Ne.symm hx]
  · simp [hx, Ne.symm hx]

theorem fix_of_fix {K : Type*} [CommRing K] {l ρ N : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hl : IsLoUni l)
    (hρ : IsUpUni ρ) (κ : K) (h : l * (N - Matrix.single (Fin.last r) (Fin.last r) κ) * ρ =
      N - Matrix.single (Fin.last r) (Fin.last r) κ) : l * N * ρ = N := by
  rw [Matrix.mul_sub, Matrix.sub_mul, fix_single hl hρ] at h
  exact sub_left_injective h

end Gen

section Rec

open Formalism.L2.SG.CntLocal

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (u u' : D.what₂.Word)

theorem zzp_mono {p : PlF D} (hA : Agree δ M p) {σ : Fin (D.R.rS + 1) → Fin (D.R.rS + 1)} (hσ : ∀ a, σ (σ a) = a)
    (ν : Fin (D.R.rS + 1) → D.host.E) (hν : ∀ a, ν a ≠ 0) :
    ∃ ν' : Fin (D.R.rS + 1) → (D.s.atP p).Ep, (∀ a, IsUnit (ν' a)) ∧ ∃ κ : (D.s.atP p).Ep,
      ZZP (M := M) δ u u' p (mono σ ν) = mono σ ν' - Matrix.single (Fin.last D.R.rS) (Fin.last D.R.rS) κ := by
  set cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep := ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep)
  have hu : ∀ a, IsUnit (frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a)) := fun a =>
    ((frFac_unit δ M hA (σ a)).mul ((frFac_unit δ M hA a).map cj)).mul ((isUnit_iff_ne_zero.2 (hν a)).map _)
  cases h : (M p).split with
  | none =>
    refine ⟨fun a => frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a), hu, 0, ?_⟩
    rw [zzp_none δ M u u' h, zLoc_mono, Matrix.single_zero, sub_zero]
  | some g =>
    refine ⟨fun a => g.e.symm ((g.e (frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a))).1 / (g.q : (D.s.atP p).Fp),
      -((g.e (frFac δ p (σ (σ a)) * cj (frFac δ p (σ a)) * (D.s.atP p).ιE (ν (σ a)))).2 / (g.q : (D.s.atP p).Fp))),
      fun a => ?_, g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
          (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp)), ?_⟩
    · have hq := q_ne M g
      have h1 := (Prod.isUnit_iff.1 ((hu a).map g.e)).1
      have h2 := (Prod.isUnit_iff.1 ((hu (σ a)).map g.e)).2
      refine IsUnit.map g.e.symm (Prod.isUnit_iff.2 ⟨?_, ?_⟩)
      · exact isUnit_iff_ne_zero.2 (div_ne_zero h1.ne_zero hq)
      · exact isUnit_iff_ne_zero.2 (neg_ne_zero.2 (div_ne_zero h2.ne_zero hq))
    · rw [zzp_some δ M u u' h, zLoc_mono, linG_mono _ _ hσ]

end Rec

end Formalism.L2.SG.Pf.ProdEApprox
