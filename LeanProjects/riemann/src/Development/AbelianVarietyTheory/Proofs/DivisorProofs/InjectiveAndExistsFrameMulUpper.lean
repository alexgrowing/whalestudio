import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellColumnsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagLocallyAdaptedAffineFrame
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ

set_option autoImplicit false
noncomputable section

open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.FlagZ.Loc

theorem isUnit_submatrix_castLE_of_upper {R : Type*} [CommRing R] {N l : ℕ} (hl : l ≤ N)
    (b : Matrix (Fin N) (Fin N) R) (hb : ∀ i j : Fin N, j < i → b i j = 0) (hu : IsUnit b) :
    IsUnit (b.submatrix (Fin.castLE hl) (Fin.castLE hl)) := by
  have h1 : b.BlockTriangular id := fun i j h => hb i j h
  have h2 : (b.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id :=
    fun i j h => hb _ _ h
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular h1,
    IsUnit.prod_univ_iff] at hu
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular h2, IsUnit.prod_univ_iff]
  exact fun i => hu _

theorem injective_app_of_frame {X : Scheme.{0}} {F G : X.Modules} (φ : F ⟶ G) {V : X.Opens}
    {m n : Type} [Fintype m] [Fintype n] {e : m → Γ(F, V)} {c : n → Γ(G, V)} (σ : m → n)
    (hσ : Function.Injective σ) (he : VB.IsFrame e) (hc : VB.IsFrame c)
    (h : ∀ k, φ.app V (e k) = c (σ k)) (W : X.Opens) (hW : W ≤ V) :
    Function.Injective (φ.app W) := by
  have hli : LinearIndependent Γ(X, W) fun k => resM G hW (c (σ k)) :=
    (Fintype.linearIndependent_iff.2 fun a ha =>
      congrFun ((injective_iff_map_eq_zero _).1 (hc W hW).1 a
        ((Fintype.linearCombination_apply _ _ _).trans ha))).comp σ hσ
  change Function.Injective (appLinear φ W)
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  obtain ⟨a, rfl⟩ := (he W hW).2 t
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, appLinear_apply, app_resM,
    h] at ht
  have ha : a = 0 := funext (Fintype.linearIndependent_iff.1 hli a ht)
  rw [ha, map_zero]

theorem colSecOn_mul {N : ℕ} {T : Scheme.{0}} (x : T ⟶ Sp ℤ) (V : T.Opens)
    (C b : Matrix (Fin N) (Fin N) Γ(T, V)) (j : Fin N) :
    colSecOn x V (C * b) j = ∑ k, b k j • colSecOn x V C k := by
  simp only [colSecOn, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem injective_and_exists_frame_mul_upper : ∀ {T : Scheme.{0}} (x : T ⟶ Sp ℤ) {N : ℕ} {F' : T.Modules}
    (φ : F' ⟶ (Scheme.Modules.pullback x).obj (GlobalTheory.FlagZ.Taut.stdE N)) (V : T.Opens) (l : Fin (N + 1))
    (e : Fin l → Γ(F', V)) (C : GL (Fin N) Γ(T, V)) (b : Matrix (Fin N) (Fin N) Γ(T, V)),
    GlobalTheory.VB.IsFrame e → (∀ k, φ.app V (e k) = GlobalTheory.FlagZ.Loc.colSecOn x V C.1 (Fin.castLE l.is_le k)) →
    (∀ i j : Fin N, j < i → b i j = 0) → IsUnit b →
    (∀ W : T.Opens, W ≤ V → Function.Injective (φ.app W)) ∧
      ∃ s : Fin l → Γ(F', V), GlobalTheory.VB.IsFrame s ∧
        ∀ j, φ.app V (s j) = GlobalTheory.FlagZ.Loc.colSecOn x V (C.1 * b) (Fin.castLE l.is_le j) := by
  intro T x N F' φ V l e C b he hφ hb hu
  have hc : VB.IsFrame (colSecOn x V C.1) :=
    Univ.isFrame_sum_smul_of_isUnit (isFrame_stdSec x V) C.1 C.isUnit
  refine ⟨injective_app_of_frame φ _ (Fin.castLE_injective l.is_le) he hc hφ,
    _, Univ.isFrame_sum_smul_of_isUnit he _ (isUnit_submatrix_castLE_of_upper l.is_le b hb hu),
    fun j => ?_⟩
  rw [colSecOn_mul, ← appLinear_apply]
  simp only [map_sum, map_smul, appLinear_apply, hφ, Matrix.submatrix_apply]
  refine Finset.sum_of_injOn (Fin.castLE l.is_le) (Fin.castLE_injective _).injOn
    (fun _ _ => Finset.mem_univ _) (fun k _ hk => ?_) (fun _ _ => rfl)
  rw [hb, zero_smul]
  by_contra hlt
  have hk' : (k : ℕ) < l := lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 hlt)) j.2
  exact hk ⟨⟨k, hk'⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩

end GlobalTheory.FlagZ.Loc
