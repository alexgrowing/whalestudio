import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VertForm GlobalTheory.CechPic

namespace GlobalTheory.VertForm

theorem nefOver_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (l : ℕ),
    l.Prime → NefOver L l → NefOver (L.pull π hπ) l := by
  intro k _ _ X Y p q hp hq π hπ L l hl hL Z i _ _ κ _ _ _ _ hd
  haveI : Fact l.Prime := ⟨hl⟩
  letI : Algebra (ZMod l) κ := ZMod.algebra κ l
  letI : Algebra (ZMod l) Γ(Z, ⊤) := ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod l) κ)).toAlgebra
  haveI : IsScalarTower (ZMod l) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨N, j, _, hj⟩ := hp
  obtain ⟨N', j', _, hj'⟩ := hq
  have := isProper_str k N
  have := isProper_str k N'
  have : IsProper q := hj' ▸ inferInstance
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have hp' : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := .of_comp π p
  have hg : IsProper ((i ≫ π) ≫ p ≫ spMap (Int.castRingHom k)) := inferInstance
  have h := GlobalTheory.ArInt.topSelf_pull_nonneg l (p ≫ spMap (Int.castRingHom k)) hd L.isLB (i ≫ π)
    fun Z' i' _ _ _ hd' => hL Z' i' (ZMod l) hd'
  have e : cls ((L.pull π hπ).B.pull i) (pull_isLB (L.pull π hπ).isLB i) =
      cls (L.B.pull (i ≫ π)) (pull_isLB L.isLB _) := by
    refine (cls_pull (L.pull π hπ).isLB i _).trans ?_
    refine Eq.trans ?_ (cls_pull L.isLB (i ≫ π) _).symm
    exact (pull_comp i π (cls L.B L.isLB)).symm
  rw [← topSelf_congr (ZMod l) (pull_isLB (L.pull π hπ).isLB i) (pull_isLB L.isLB _)
    ((cls_eq_iff _ _).1 e)] at h
  have e2 := GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod l) κ Z (structureModule Z) (fun _ : Fin 1 => (L.pull π hπ).B.pull i)
  rw [topSelf_def] at h ⊢
  rw [e2] at h
  haveI : Module.Finite (ZMod l) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod l) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h

end GlobalTheory.VertForm
