import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetF
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnValJetGlob

set_option backward.isDefEq.respectTransparency false in

theorem appLE_spMap_jetPt {N m : ℕ} {I : Type} {Z : Scheme.{0}} (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (hq : IsHolFam q)
    (χ : Jet ℂ (Fin 1 × Fin N) m →+* Jet ℂ I m) [IsLocalHom χ] (U : Z.Opens)
    (h : ⊤ ≤ (spMap χ ≫ jetPt q hq m) ⁻¹ᵁ U) :
    q 0 cpt ∈ U ∧ ∀ f : Γ(Z, U), (spMap χ ≫ jetPt q hq m).appLE U ⊤ h f =
      toΓ _ (χ (jetOf m fun v => valAt' (q v) U f)) := by
  have hU : q 0 cpt ∈ U := by
    have : (spMap χ ≫ jetPt q hq m) (IsLocalRing.closedPoint _) ∈ U :=
      h (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [Scheme.Hom.comp_apply, spMap, Spec_closedPoint, jetPt_closedPoint] at this
  refine ⟨hU, fun f => ?_⟩
  have hp : ⊤ ≤ jetPt q hq m ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (jetPt q hq m) (by rw [jetPt_closedPoint]; exact hU)).ge
  have k := specMap_comp_appLE (CommRingCat.ofHom χ) (jetPt q hq m) U h hp
  rw [jetPt_appLE q hq m U hU hp, Category.assoc, Iso.inv_hom_id_assoc, ← Iso.eq_comp_inv] at k
  have k' := ConcreteCategory.congr_hom k f
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, jetψ_apply] at k'
  exact k'

set_option backward.isDefEq.respectTransparency false in

theorem jetRd_pullGen : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (q : (Fin (n * g) → ℂ) → (Sp ℂ ⟶ Z)) (hq : IsHolFam q), (∀ v, Φ.GenRd φ ε t (q v) (fun k => Λ k (colsOf n g v)) 1) → Φ.JetRd m (fun k => (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt q hq m) ≫ φ k) ε (LB.pullGen L.L φ ε t (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt q hq m)) Λ := by
  intro S A _ _ L x0 g Φ n m Z K _ φ ε t Λ q hq H
  refine ⟨fun k => ?_, fun j h => ?_⟩
  · have he : ∀ v, q v ≫ φ k = (Φ.e (Λ k (colsOf n g v))).left := fun v => (H v).1 k
    have hol : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e (Λ k (colsOf n g v))).left) := by
      have h := isHolFam_comp q hq (φ k)
      rwa [show (fun v => q v ≫ φ k) = fun v => (Φ.e (Λ k (colsOf n g v))).left from funext he] at h
    refine ⟨hol, ?_⟩
    beta_reduce
    rw [Category.assoc, jetPt_comp q hq (φ k) _ hol he]
  · have : IsLocalHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) :=
      isLocalHom_jetMap (K := ℂ) (m := m) _ _
    have h' : ⊤ ≤ (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt q hq m) ⁻¹ᵁ LB.wchart L.L φ j := by
      intro x hx
      have hx' := h hx
      simp only [LB.wchart] at hx' ⊢
      exact Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hx' k
        simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using this
    obtain ⟨hU, hf⟩ := appLE_spMap_jetPt q hq _ _ h'
    have hj : jetOf m (fun v => valAt' (q v) (LB.wchart L.L φ j) (t.s j).val) =
        jetOf m (fun v => ∏ k, Φ.fr (j k) (Λ k (colsOf n g v)) ^ ε k) := by
      refine jetOf_congr m ((eventually_mem q hq hU).mono fun v hv => ?_)
      have := (H v).2 j hv
      rw [_root_.one_mul] at this
      exact this
    have hf' := hf (t.s j).val
    rw [hj] at hf'
    refine Eq.trans ?_ hf'
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    show ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom
      (((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE _).op).hom _) = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

end GlobalTheory.AnValJetGlob
