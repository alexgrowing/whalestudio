import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory in
open MonObj in

theorem isCombAtG_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X0 : Scheme.{0}} (t : SAB H X0) {R : Type} [CommRing R] (x : Sp R ⟶ X0) {m n : ℕ}
    (f : Fin m → Fin n) (hf : Function.Injective f)
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {v' : Fin n → (Sp (DualNumber R) ⟶ t.G.left)}
    (hv : ∀ j, IsTanAtG t x (v' j)) {cf : Fin m → R} {cf' : Fin n → R}
    (hvf : ∀ k, v' (f k) = v k) (hcf : ∀ k, cf' (f k) = cf k) (hz : ∀ c, (¬ ∃ k, f k = c) → cf' c = 0)
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x v cf w) : IsCombAtG t x v' cf' w := by
  classical
  have h0 : spMap (epsMul (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have e : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
      RingHom.ext fun z => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Spec.map_comp, e]
    rfl
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨Function.extend f u 1, fun c => ?_, ?_⟩
  · by_cases hc : ∃ k, f k = c
    · obtain ⟨k, rfl⟩ := hc
      rw [hf.extend_apply, hu, hvf, hcf]
    · let p : tEpsG x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
      rw [Function.extend_apply' _ _ _ hc, hz c hc, h0, Category.assoc, (hv c).2, Pi.one_apply,
        ← MonObj.comp_one p]
      rfl
  · rw [← hw]
    congr 1
    letI : CommMonoid (tEpsG x ⟶ t.G) := Hom.commMonoid
    rw [List.prod_ofFn, List.prod_ofFn]
    symm
    refine Finset.prod_of_injOn f hf.injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
    · intro c _ hc
      rw [Function.extend_apply' _ _ _ ?_, Pi.one_apply]
      rintro ⟨k, rfl⟩
      exact hc ⟨k, by simp, rfl⟩
    · intro k _
      rw [hf.extend_apply]

theorem isCombAtG_flatFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x : Sp S ⟶ X) (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ t.G.left)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (w : Sp (DualNumber S) ⟶ t.G.left), (∀ τ k, IsTanAtG t x (w' τ k)) → IsCombAtG t x (w' σ) (A σ i) w → IsCombAtG t x (fun c => w' (e'.symm c).1 (e'.symm c).2) (fun c => GlobalTheory.LogKSDiv.flatFrame A e e' (e ⟨σ, i⟩) c) w := by
  classical
  intro E _ _ _ H Dw X t S _ x n n' e e' w' A σ i w htan h
  refine isCombAtG_extend t x (fun k => e' ⟨σ, k⟩) (fun a b hab => ?_) (fun c => htan _ _) (fun k => ?_)
    (fun k => flatFrame_apply A e e' σ i k) (fun c hc => ?_) h
  · exact sigma_mk_injective (β := fun τ : E →+* ℂ => Fin (Dw.mult τ)) (e'.injective hab)
  · show (fun z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => w' z.1 z.2) (e'.symm (e' ⟨σ, k⟩)) = _
    rw [Equiv.symm_apply_apply]
  · obtain ⟨⟨τ, k⟩, rfl⟩ := e'.surjective c
    have hne : σ ≠ τ := by
      rintro rfl
      exact hc ⟨k, rfl⟩
    simp [flatFrame, Matrix.blockDiagonal'_apply_ne _ _ _ hne]

end GlobalTheory.LogKSDiv
