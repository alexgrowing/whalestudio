import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MapUniq

variable {X X' : Scheme.{0}}

theorem hom_ext_of_gs {I : Type} (D : I → X.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (φ ψ : X' ⟶ X) (hm : ∀ i z, φ z ∈ D i → ψ z ∈ D i)
    (h : ∀ i z, φ z ∈ D i → ∀ a : Γ(X, D i), gs φ z _ a = gs ψ z _ a) : φ = ψ := by
  refine Scheme.hom_ext_of_forall _ _ fun z => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ z ∈ ⨆ i, D i by rw [hc]; trivial)
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hle⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ (φ ⁻¹ᵁ D i : Set X') from hi) (φ ⁻¹ᵁ D i).isOpen
  have e₁ : V ≤ φ ⁻¹ᵁ D i := hle
  have e₂ : V ≤ ψ ⁻¹ᵁ D i := fun y hy => hm i y (e₁ hy)
  have e : φ.appLE (D i) V e₁ = ψ.appLE (D i) V e₂ := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => fn_ext fun y hy => ?_)
    have k : ∀ (χ : X' ⟶ X) (e : V ≤ χ ⁻¹ᵁ D i), gs (𝟙 X') y V ((χ.appLE (D i) V e).hom a) = gs χ y _ a :=
      fun χ e => ((gs_res (𝟙 X') y e hy _).trans (gs_pull (𝟙 X') χ y _ (e hy) a)).trans (by rw [Category.id_comp])
    rw [k, k]
    exact h i y (e₁ hy) a
  refine ⟨V, hzV, ?_⟩
  have hV' : IsAffineOpen V := hV
  rw [← cancel_epi hV'.isoSpec.inv, ← Category.assoc, ← Category.assoc, hV'.isoSpec_inv_ι,
    ← (hD i).SpecMap_appLE_fromSpec φ hV' e₁, ← (hD i).SpecMap_appLE_fromSpec ψ hV' e₂, e]

theorem gs_cst {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (φ : X' ⟶ X) (z : X') (W : X.Opens)
    (h : φ z ∈ W) (c : R) :
    gs φ z W (AbLaw.cst f W c) = gs (φ ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) :=
  (gs_res φ z le_top h _).trans (gs_pull φ f z ⊤ trivial _)

theorem hom_eq_of_pull_sections : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ ψ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)) (w' : LB.Iso H' (H.pull ψ)), H'.IsLB → φ ≫ f = ψ ≫ f → w.IsGen → w'.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (ψ) z ∈ (H).U k → z ∈ (H').U k' → gs (ψ) z _ ((s j).f k) = (Geo.Tor.gw (w') (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → φ = ψ := by
  intro R _ X f H n s hH hs X' H' s' φ ψ w w' hH' hf _ _ hφ hψ
  choose r hr hsurj using fun i => (hs.2 i).2
  have mem : ∀ (χ : X' ⟶ X) (u : LB.Iso H' (H.pull χ)),
      (∀ j z (k : H.ι) (k' : H'.ι), χ z ∈ H.U k → z ∈ H'.U k' →
        gs χ z _ ((s j).f k) = (Geo.Tor.gw u (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k')) →
      ∀ i z k', z ∈ H'.U k' → (χ z ∈ nonzeroLocus (s i) ↔ IsUnit (gs (𝟙 X') z _ ((s' i).f k'))) ∧
        (χ z ∈ nonzeroLocus (s i) → ∀ j, gs (𝟙 X') z _ ((s' j).f k') =
          gs χ z _ (r i j) * gs (𝟙 X') z _ ((s' i).f k')) := by
    intro χ u hu i z k' hk'
    obtain ⟨k, hk⟩ := exists_chart hH (χ z)
    refine ⟨?_, fun hz j => ?_⟩
    · rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) χ z hk, hu i z k k' hk hk', Units.isUnit_units_mul]
    · have e := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) χ z hz hk
      rw [hu i z k k' hk hk', hu j z k k' hk hk', mul_left_comm] at e
      exact (Units.mul_right_inj _).1 e
  have hm : ∀ i z, φ z ∈ nonzeroLocus (s i) → ψ z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    exact (mem ψ w' hψ i z k' hk').1.2 ((mem φ w hφ i z k' hk').1.1 hz)
  refine hom_ext_of_gs (fun i => nonzeroLocus (s i)) (fun i => (hs.2 i).1) hs.1 φ ψ hm fun i z hz a => ?_
  obtain ⟨k', hk'⟩ := exists_chart hH' z
  have hz' := hm i z hz
  have hrr : ∀ j, gs φ z _ (r i j) = gs ψ z _ (r i j) := fun j =>
    ((mem φ w hφ i z k' hk').1.1 hz).mul_right_cancel
      (((mem φ w hφ i z k' hk').2 hz j).symm.trans ((mem ψ w' hψ i z k' hk').2 hz' j))
  obtain ⟨p, rfl⟩ := hsurj i a
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, gs_cst f φ z _ hz, gs_cst f ψ z _ hz', hf]
  | add p q hp hq => rw [map_add, gs_add φ z _ hz, gs_add ψ z _ hz', hp, hq]
  | mul_X p j hp => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul φ z _ hz, gs_mul ψ z _ hz', hp, hrr]

end GlobalTheory.MapUniq
