import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullAmpleFinite

open TopologicalSpace GlobalTheory.MulFinite

theorem sec_gs {Z Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) (r : Z ⟶ Y) (z : Z) {j j' : M.ι}
    (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') :
    gs r z (M.U j) (s.f j) = (gm r z (M.U j ⊓ M.U j') (M.g j j')).val * gs r z (M.U j') (s.f j') := by
  have hm : r z ∈ M.U j ⊓ M.U j' := ⟨hj, hj'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem pow_cancel {R : Type} [CommRing R] (g t : Rˣ) (x : R) (e : ℕ) :
    (g.val * x) ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t).val = x ^ e * t.val := by
  have h : (g ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t)) = t := by
    rw [zpow_natCast, _root_.one_mul, mul_inv_cancel_left]
  have h' : g.val ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t).val = t.val := congrArg Units.val h
  rw [mul_pow, ← h']; ring

theorem exists_fn {X W Z : Scheme.{0}} (H : LB X) (hH : H.IsLB) (L : LB W) (hL : L.IsLB)
    (s : LB.Sec L) (m : W ⟶ X) (e : ℕ) (he : e ≠ 0)
    (α : LB.Iso (pw L e) (H.pull m)) (hα : α.IsGen)
    (r : Z ⟶ W) (j₀ : H.ι) (h₀ : ∀ z, m (r z) ∈ H.U j₀) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => r ⁻¹ᵁ L.U j
  have l₂ : ∀ j, V j ≤ r ⁻¹ᵁ ((H.pull m).U (fun _ => j₀) ⊓ (pw L e).U j) :=
    fun j z hz => ⟨mem_pull.2 (h₀ z), hz⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (L.U j) (s.f j) ^ e * (gw α r z j₀ j).val := by
    refine ⟨fun j => (r.appLE _ _ le_rfl).hom (s.f j) ^ e *
      (r.appLE _ _ (l₂ j)).hom (α.s (fun _ => j₀, j)).val, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_) ?_)
    · exact congrArg (· ^ e) (gs_appLE r z _ _ _ hz _)
    · exact (gs_appLE r z _ _ _ hz _).trans (gs_unit r z _ (l₂ j hz) _)
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hL (r z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_gs s r z hz.1 hz.2,
        (isGen_iff α).1 hα Z r z j₀ j₀ j j' (h₀ z) (h₀ z) hz.1 hz.2]
      have h1 : gm (r ≫ m) z (H.U j₀ ⊓ H.U j₀) (H.g j₀ j₀) = 1 := gm_self hH _ z (h₀ z)
      have t₁ : gm r z ((pw L e).U j ⊓ (pw L e).U j') ((pw L e).g j j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') ^ (e : ℤ) := map_zpow _ _ _
      rw [h1, t₁]
      exact pow_cancel _ _ _ _)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hL (r z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔ IsUnit (gs r z (L.U j) (s.f j)) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, Units.isUnit_mul_units, isUnit_pow_iff he]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨j, (isUnit_gs r z _ hj _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ nonzeroLocus s from h)
    have hk' : r z ∈ L.U k := W.basicOpen_le _ hk
    rw [sec_gs s r z hj hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isFinite_of_pull_iso_pow :
    ∀ (K : Type) [Field K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (n : ℕ) (s : Fin (n + 1) → LB.Sec H') (d : ℕ), H.IsLB → H'.IsLB → IsSeparated f → VeryAmpleBy (φ ≫ f) H' s → 1 ≤ d → LBIso (pw H' d) (H.pull φ) → IsFinite φ := by
  intro K _ X X' f φ H H' n s d hH hH' hf hva hd ⟨α, hα⟩
  have : IsProper (φ ≫ f) := isProper_of_isProjBy K X' _ ⟨H', hH', n, s, hva⟩
  have : IsProper φ := .of_comp _ f
  suffices LocallyQuasiFinite φ from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  obtain ⟨hcov, hs⟩ := hva
  have hy : ∀ z, φ (φ.fiberι y z) = y := fun z => (φ.range_fiberι y).le ⟨z, rfl⟩
  have := isAffineHom_fromSpecResidueField X y
  have : IsAffineHom (φ.fiberι y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback φ (X.fromSpecResidueField y)).flip this
  obtain ⟨j₀, hj₀⟩ := Geo.Tor.exists_chart hH y
  have key := fun i => exists_fn H hH H' hH' (s i) φ d (by omega) α hα (φ.fiberι y) j₀ (fun z => by
    rw [hy]; exact hj₀)
  choose a ha using key
  have : IsProper (φ.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd φ (X.fromSpecResidueField y)))
  refine locallyQuasiFinite_of_cover (K := X.residueField y) (φ.fiberToSpecResidueField y) a ?_ fun i => ?_
  · simp only [ha]
    rw [← Scheme.Hom.preimage_iSup]
    exact (congrArg (fun V => φ.fiberι y ⁻¹ᵁ V) hcov).trans rfl
  · rw [ha]
    exact (hs i).1.preimage _

end GlobalTheory.PullAmpleFinite
