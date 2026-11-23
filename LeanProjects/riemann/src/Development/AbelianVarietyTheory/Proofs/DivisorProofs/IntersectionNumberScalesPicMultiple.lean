import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

namespace GlobalTheory.Selfsq

theorem selfInter_of_cls_eq_nsmul : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)], IsProjSurface k T → ∀ (L M : LB T) (hL : L.IsLB) (hM : M.IsLB) (n : ℕ), GlobalTheory.CechPic.cls M hM = n • GlobalTheory.CechPic.cls L hL → GlobalTheory.interNum k (structureModule T) ![M, M] = (n : ℤ) ^ 2 * GlobalTheory.interNum k (structureModule T) ![L, L] := by
  intro k _ T _ hT L M hL hM n hn
  have := (isVB_structureModule T).isFiniteQC
  have hv : DiffVanish (2 + 1) (chiPic k (structureModule T)) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k T) _ hT.isProjOver
      (by rw [QCoh.suppDim_structureModule, hT.dim_eq]; rfl)
  have hMM : ∀ i, ((![M, M] : Fin 2 → LB T) i).IsLB := fun i => by fin_cases i <;> exact hM
  have hLL : ∀ i, ((![L, L] : Fin 2 → LB T) i).IsLB := fun i => by fin_cases i <;> exact hL
  have eM : interNum k (structureModule T) ![M, M] = hv.form (fun _ => CechPic.cls M hM) := by
    rw [interNum_eq_multiDiff k _ hMM, hv.form_apply _ 0]
    congr 1
    funext i; fin_cases i <;> rfl
  have eL : interNum k (structureModule T) ![L, L] = hv.form (fun _ => CechPic.cls L hL) := by
    rw [interNum_eq_multiDiff k _ hLL, hv.form_apply _ 0]
    congr 1
    funext i; fin_cases i <;> rfl
  have hn' : CechPic.cls M hM = (n : ℤ) • CechPic.cls L hL := by rw [hn, natCast_zsmul]
  rw [eM, eL, hn']
  have := hv.form.map_smul_univ (fun _ => (n : ℤ)) (fun _ => CechPic.cls L hL)
  rw [this, smul_eq_mul]
  simp [Fin.prod_univ_two, sq]

end GlobalTheory.Selfsq
