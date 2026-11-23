import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExists

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.RegroupFin

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem map_phiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  simp [PhiU, GlobalTheory.Tw.Phi, GeneralLinearGroup.map, apply_ite f]

theorem map_thetaGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaGL n c g) = thetaGL n c' (GeneralLinearGroup.map f g) := by
  have h1 : ∀ x : GL (Fin n) R, GeneralLinearGroup.map f (invT n R x) = invT n S (GeneralLinearGroup.map f x) := by
    intro x
    apply Units.ext
    ext i j
    have e : (GeneralLinearGroup.map f x)⁻¹ = GeneralLinearGroup.map f x⁻¹ := (map_inv _ x).symm
    simp only [invT, MonoidHom.coe_mk, OneHom.coe_mk, e]
    rfl
  have h2 : GeneralLinearGroup.map f (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map f g) := by
    apply Units.ext
    ext i j
    exact h _
  have h3 : ∀ (T : Type) [CommRing T] (d : T →+* T) (x : GL (Fin n) T),
      thetaGL n d x = PhiU n T * invT n T (GeneralLinearGroup.map d x) * (PhiU n T)⁻¹ := fun _ _ _ _ => rfl
  rw [h3, h3, map_mul, map_mul, map_inv, map_phiU, h1, h2]

theorem evw_pv (v : PlF E) (w : Above v) (y : Gf E a b) : evw w (pv a b v y) = atW w.1 y := by
  refine Prod.ext ?_ ?_ <;> · apply Units.ext; ext i j; rfl

theorem cjv_spec (hc : CjEx) (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cjv v (projv v x) := by
  have h := hc E v
  unfold cjv
  rw [dif_pos h]
  exact h.choose_spec.2 x

theorem pv_thP (hc : CjEx) (v : PlF E) (y : Gf E a b) : pv a b v (thP E a b y) = thv a b v (pv a b v y) :=
  Prod.ext (map_thetaGL (projv v) _ (cjv v) (cjv_spec hc v) a y.1) (map_thetaGL (projv v) _ (cjv v) (cjv_spec hc v) b y.2)

theorem finprod_fibres {X Y : Type} (u : X → Y) (S : Set X) (hu : Set.InjOn u S) (F : X → ℂ) :
    ∏ᶠ w ∈ S, F w = ∏ᶠ v : Y, ∏ᶠ (w : {w : X // u w = v}) (_ : w.1 ∈ S), F w.1 := by
  set G : Y → ℂ := fun v => ∏ᶠ (w : {w : X // u w = v}) (_ : w.1 ∈ S), F w.1 with hG
  have hone : ∀ v, v ∉ u '' S → G v = 1 := by
    intro v hv
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    have hw : w.1 ∉ S := fun hw => hv ⟨w.1, hw, w.2⟩
    simp [hw]
  have hval : ∀ w ∈ S, G (u w) = F w := by
    intro w hw
    have hs : {i : {x : X // u x = u w} | i.1 ∈ S} = {⟨w, rfl⟩} := by
      ext i
      change i.1 ∈ S ↔ i = ⟨w, rfl⟩
      constructor
      · intro hi
        exact Subtype.ext (hu hi hw i.2)
      · rintro rfl
        exact hw
    have : G (u w) = ∏ᶠ i ∈ {i : {x : X // u x = u w} | i.1 ∈ S}, F i.1 := rfl
    rw [this, hs, finprod_mem_singleton]
  have h1 : ∏ᶠ v, G v = ∏ᶠ v ∈ u '' S, G v := by
    rw [← finprod_mem_univ]
    refine finprod_mem_inter_mulSupport_eq' _ _ _ fun v hv => ?_
    simp only [Set.mem_univ, true_iff]
    by_contra hn
    exact hv (hone v hn)
  rw [h1, finprod_mem_image hu]
  exact (finprod_mem_congr rfl hval).symm

theorem regroup_of_cjEx (hc : CjEx) : Regroup := by
  intro E _ _ _ a b S hS φ₁ φ₂ _ _ y
  have hinj : Set.InjOn (fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))) S := by
    intro u hu u' hu' h
    obtain ⟨x, -, hx⟩ := hS u
    exact (hx u ⟨hu, rfl⟩).trans (hx u' ⟨hu', h.symm⟩).symm
  unfold finFn
  rw [finprod_fibres _ S hinj]
  refine finprod_congr fun v => ?_
  unfold fv
  refine finprod_congr fun w => finprod_congr fun _ => ?_
  rw [evw_pv, ← pv_thP hc, evw_pv]

theorem regroup : Regroup := regroup_of_cjEx GlobalTheory.CompanionTheory.CjEx.cjEx

end GlobalTheory.CompanionTheory.RegroupFin

end
