import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogKSUp

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem chart_res' {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE h).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
  U.2.map_fromSpec W.2 (homOfLE h).op

theorem exists_factor {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (hr : ∀ z, (spMap φ ≫ GlobalTheory.LogKS.chart U) z ∈ W.1) :
    ∃ φ' : Γ(X, W.1) →+* S, φ = φ'.comp (X.presheaf.map (homOfLE h).op).hom := by
  have hr' : Set.range (spMap φ ≫ GlobalTheory.LogKS.chart U) ⊆ Set.range (GlobalTheory.LogKS.chart W) := by
    show _ ⊆ Set.range (IsAffineOpen.fromSpec W.2)
    rw [W.2.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact hr z
  have : IsOpenImmersion (GlobalTheory.LogKS.chart W) := W.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (GlobalTheory.LogKS.chart U) := U.2.isOpenImmersion_fromSpec
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Sp S ⟶ Sp Γ(X, W.1), ψ ≫ GlobalTheory.LogKS.chart W = spMap φ ≫ GlobalTheory.LogKS.chart U :=
    ⟨IsOpenImmersion.lift (GlobalTheory.LogKS.chart W) _ hr', IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨(Spec.preimage ψ).hom, ?_⟩
  have hfac : spMap (Spec.preimage ψ).hom ≫ GlobalTheory.LogKS.chart W = spMap φ ≫ GlobalTheory.LogKS.chart U := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    exact hψ
  rw [← chart_res' U W h, ← Category.assoc, spMap_comp''] at hfac
  have h2 := Spec.map_inj.1 ((cancel_mono (GlobalTheory.LogKS.chart U)).1 hfac)
  simpa using (congrArg CommRingCat.Hom.hom h2).symm

end GlobalTheory.LogKSUp

namespace GlobalTheory.LogKSUp

theorem isKS_of_inf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U W : X.affineOpens) (hW : W.1 = U.1 ⊓ V) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (DW : Γ(X, W.1) → Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ r, DW ((X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D r)) → IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW ((X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom.mapMatrix Θ) → IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U W hW n v D DW Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩
  have hWU : W.1 ≤ U.1 := hW.le.trans inf_le_left
  have hWW : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ W.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, Wc, j, d, ?_, hj, hfld, fun i h r => ?_, fun i i' O hO f S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [hsup, hW, inf_assoc, inf_idem]
  · have e : ∀ r : Γ(X, U.1), (t.G.hom.appLE U.1 (Wc i) h).hom r =
        (t.G.hom.appLE W.1 (Wc i) (hWW i)).hom ((X.presheaf.map (homOfLE hWU).op).hom r) := by
      intro r
      exact (congrArg (fun k => k.hom r) (t.G.hom.map_appLE (hWW i) (homOfLE hWU).op)).symm
    rw [e, e, hcomp i (hWW i), hD]
  · have hr : ∀ z, (spMap φ ≫ GlobalTheory.LogKS.chart U) z ∈ W.1 := by
      intro z
      rw [← hg₀]
      have hz : g₀ z ∈ O := hO' (show z ∈ (⊤ : (Sp S).Opens) from trivial)
      exact hWW i (inf_le_left (a := Wc i) (b := Wc i') (hO hz))
    obtain ⟨φ', hfac⟩ := exists_factor U W hWU φ hr
    have hg₀' : g₀ ≫ t.G.hom = spMap φ' ≫ GlobalTheory.LogKS.chart W := by
      rw [hg₀, hfac, ← spMap_comp'', Category.assoc, chart_res']
    have := htest i i' O hO f S φ' g₀ w hg₀' hO' fun a => by
      obtain ⟨g', v', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v', h₁, ?_, h₃⟩
      rw [h₂, ← Category.assoc, spMap_comp'', dualMap_comp'', ← hfac]
    rw [this]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hfac]
    rfl

end GlobalTheory.LogKSUp
