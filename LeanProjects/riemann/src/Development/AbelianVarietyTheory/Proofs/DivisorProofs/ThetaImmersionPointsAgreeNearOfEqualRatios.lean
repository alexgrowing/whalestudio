import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaSep

open GlobalTheory.ProjSpace

variable {X H Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem sval_eq_secRatio_mul {φ : K → (H ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ H) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (ha : r z ∈ nonzeroLocus a) :
    sval b r z J = gs r z (nonzeroLocus a) (secRatio a b) * sval a r z J := by
  have hc := hJ.mem φ r
  have hm : r z ∈ nonzeroLocus a ⊓ (LB.LinComb L φ ε).U (fun k => J (r ≫ φ k)) := ⟨ha, hc⟩
  have e := congrArg (gs r z _) (secRatio_spec a b (fun k => J (r ≫ φ k)))
  rw [gs_mul r z _ hm, gs_res r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  exact e

theorem pullRatio_ι_comp {R : Type} [CommRing R] {M : ℕ} (P : H ⟶ PSpace R M) {U : H.Opens} {i : Fin (M + 1)}
    (hi : U ≤ P ⁻¹ᵁ chart R M i) (r : Z ⟶ H) (W : Z.Opens) (hW : W ≤ r ⁻¹ᵁ U)
    (h : ⊤ ≤ (W.ι ≫ r ≫ P) ⁻¹ᵁ chart R M i) (j : Fin (M + 1)) :
    pullRatio (W.ι ≫ r ≫ P) ⊤ i h j =
      (W.ι.appLE (r ⁻¹ᵁ U) ⊤ (W.ι_preimage_self.ge.trans (W.ι.preimage_mono hW))).hom
        ((r.app U).hom (pullRatio P U i hi j)) := by
  have hW' : ⊤ ≤ W.ι ⁻¹ᵁ (r ⁻¹ᵁ U) := W.ι_preimage_self.ge.trans (W.ι.preimage_mono hW)
  rw [pullRatio_of_eq (Category.assoc W.ι r P).symm h ((hW'.trans ((W.ι ≫ r).preimage_mono hi))),
    ← appLE_pullRatio (W.ι ≫ r) hW', Scheme.Hom.app_eq_appLE, appLE_appLE]

end GlobalTheory.Mum.ThetaSep

namespace GlobalTheory.Mum.ThetaSep

open GlobalTheory.ProjSpace

theorem agree_near_of_minors : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k N : ℕ)
    (τ : Fin (N + 1) → SecK D.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤),
    IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) → ∀ (T : Over (Sp R)) (y y' : T ⟶ Y.H) (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    (∀ j l : Fin (N + 1), sval (τ j) y.left z J * sval (τ l) y'.left z J =
      sval (τ l) y.left z J * sval (τ j) y'.left z J) →
    ∃ W : T.left.Opens, z ∈ W ∧ W.ι ≫ y.left = W.ι ≫ y'.left := by
  intro R _ _ D Y k N τ hτ hImm T y y' z J hJ hrel
  have hmono : Mono (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := inferInstance
  obtain ⟨j₀, hj₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y.left z)))
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y'.left z)))
  have ua : IsUnit (sval (τ j₀) y.left z J) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).1 hj₀
  have ubi : IsUnit (sval (τ i) y'.left z J) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).1 hi
  have ub : IsUnit (sval (τ j₀) y'.left z J) := by
    have h := hrel j₀ i
    have : IsUnit (sval (τ i) y.left z J * sval (τ j₀) y'.left z J) := h ▸ ua.mul ubi
    exact isUnit_of_mul_isUnit_right this
  have hj₀' : y'.left z ∈ nonzeroLocus (τ j₀) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).2 ub
  have hg : ∀ j, gs y.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) =
      gs y'.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) := by
    intro j
    have h := hrel j₀ j
    rw [sval_eq_secRatio_mul (τ j₀) (τ j) y.left z hJ hj₀,
      sval_eq_secRatio_mul (τ j₀) (τ j) y'.left z hJ hj₀'] at h
    refine ((ua.mul ub).mul_right_cancel ?_).symm
    calc _ = sval (τ j₀) y.left z J * (gs y'.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) *
          sval (τ j₀) y'.left z J) := by ring
      _ = _ := by rw [h]; ring
  have hW : ∀ j, ∃ W : T.left.Opens, z ∈ W ∧ ∃ (h₁ : W ≤ y.left ⁻¹ᵁ nonzeroLocus (τ j₀))
      (h₂ : W ≤ y'.left ⁻¹ᵁ nonzeroLocus (τ j₀)),
      resG T.left h₁ ((y.left.app _).hom (secRatio (τ j₀) (τ j))) =
        resG T.left h₂ ((y'.left.app _).hom (secRatio (τ j₀) (τ j))) := by
    intro j
    have e := hg j
    rw [gs_eq _ z _ hj₀, gs_eq _ z _ hj₀'] at e
    obtain ⟨W, hzW, iU, iV, e'⟩ := TopCat.Presheaf.germ_eq T.left.presheaf z hj₀ hj₀' _ _ e
    exact ⟨W, hzW, leOfHom iU, leOfHom iV, e'⟩
  choose Wj hzWj h₁ h₂ heq using hW
  let W : T.left.Opens := Finset.univ.inf Wj
  have hzW : z ∈ W := Finset.inf_induction (p := fun U : T.left.Opens => z ∈ U) trivial
    (fun _ h _ h' => ⟨h, h'⟩) (fun j _ => hzWj j)
  have hWle : ∀ j, W ≤ Wj j := fun j => Finset.inf_le (Finset.mem_univ j)
  refine ⟨W, hzW, (cancel_mono (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ)).1 ?_⟩
  have hpre := toProj_preimage_chart Y.H.hom τ hτ j₀
  have hA : ∀ (r : T.left ⟶ Y.H.left), W ≤ r ⁻¹ᵁ nonzeroLocus (τ j₀) →
      ⊤ ≤ (W.ι ≫ r ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) ⁻¹ᵁ chart R N j₀ := fun r hr =>
    (W.ι_preimage_self.ge.trans (W.ι.preimage_mono hr)).trans
      ((W.ι ≫ r).preimage_mono hpre.ge)
  have hy₁ : W ≤ y.left ⁻¹ᵁ nonzeroLocus (τ j₀) := (hWle j₀).trans (h₁ j₀)
  have hy₂ : W ≤ y'.left ⁻¹ᵁ nonzeroLocus (τ j₀) := (hWle j₀).trans (h₂ j₀)
  simp only [Category.assoc]
  refine hom_ext ?_ fun _ => ⟨⊤, trivial, j₀, hA _ hy₁, hA _ hy₂, fun j => ?_⟩
  · simp only [Category.assoc, toProj_str]
    rw [Over.w y, Over.w y']
  · rw [pullRatio_ι_comp _ hpre.ge _ W hy₁, pullRatio_ι_comp _ hpre.ge _ W hy₂, pullRatio_toProj]
    have hW₁ : ⊤ ≤ W.ι ⁻¹ᵁ Wj j := W.ι_preimage_self.ge.trans (W.ι.preimage_mono (hWle j))
    rw [← appLE_resG W.ι (h₁ j) hW₁, ← appLE_resG W.ι (h₂ j) hW₁, heq j]

end GlobalTheory.Mum.ThetaSep
