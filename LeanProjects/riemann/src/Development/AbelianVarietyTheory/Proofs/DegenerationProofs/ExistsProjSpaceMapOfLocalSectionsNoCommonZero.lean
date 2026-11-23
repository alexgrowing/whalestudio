import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

noncomputable section

namespace GlobalTheory.ZH.CoordMap

variable {X Y : Scheme.{0}}

def pullOn (B : LB X) (V : X.Opens) (g : Y ⟶ X) : LB Y where
  ι := B.ι
  U j := g ⁻¹ᵁ (V ⊓ B.U j)
  g j j' := Units.map (g.appLE (B.U j ⊓ B.U j') (g ⁻¹ᵁ (V ⊓ B.U j) ⊓ g ⁻¹ᵁ (V ⊓ B.U j'))
    (inf_le_inf (g.preimage_mono inf_le_right) (g.preimage_mono inf_le_right))).hom.toMonoidHom (B.g j j')

def pullSecOn {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j)) (h : σ ∈ secOn B V) :
    (pullOn B V g).Sec where
  f j := (g.appLE (V ⊓ B.U j) (g ⁻¹ᵁ (V ⊓ B.U j)) le_rfl).hom (σ j)
  compat j j' := by
    have hW : g ⁻¹ᵁ (V ⊓ B.U j) ⊓ g ⁻¹ᵁ (V ⊓ B.U j') ≤ g ⁻¹ᵁ (V ⊓ B.U j ⊓ B.U j') :=
      le_inf inf_le_left (inf_le_right.trans (g.preimage_mono inf_le_right))
    have e := congrArg (g.appLE _ _ hW).hom (h j j')
    rw [map_mul, ProjSpace.appLE_resG, ProjSpace.appLE_resG, ProjSpace.appLE_resG] at e
    exact (ProjSpace.resG_appLE g le_rfl inf_le_left _).trans (e.trans
      (congrArg (_ * ·) (ProjSpace.resG_appLE g le_rfl inf_le_right _).symm))

theorem resG_pullSecOn {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j)) (h : σ ∈ secOn B V)
    (j : B.ι) {T : Y.Opens} (hj : T ≤ g ⁻¹ᵁ (V ⊓ B.U j)) :
    resG Y (U := (pullOn B V g).U j) hj ((pullSecOn g σ h).f j) = (g.appLE _ T hj).hom (σ j) :=
  ProjSpace.resG_appLE g le_rfl hj _

theorem preimage_basicOpen_le {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j))
    (h : σ ∈ secOn B V) (j : B.ι) : g ⁻¹ᵁ X.basicOpen (σ j) ≤ nonzeroLocus (pullSecOn g σ h) := by
  refine le_trans ?_ (le_iSup (fun k => Y.basicOpen ((pullSecOn g σ h).f k)) j)
  refine le_trans ?_ (Scheme.basicOpen_appLE g (g ⁻¹ᵁ (V ⊓ B.U j)) _ le_rfl (σ j)).ge
  exact le_inf (g.preimage_mono (X.basicOpen_le _)) le_rfl

theorem exists_coordMap : ∀ (o : Type) [CommRing o] (X Z : Scheme.{0}) (f : X ⟶ Z) (s : Z ⟶ Sp o) (B : LB X) (V : X.Opens) (J : Type) (σ : J → ∀ j, Γ(X, V ⊓ B.U j)) (m : ℕ) (e : Fin (m + 1) ≃ J), (∀ i, σ i ∈ secOn B V) → (∀ x ∈ V, ∃ i j, x ∈ X.basicOpen (σ i j)) → ∃ π : V.toScheme ⟶ PSpace o m, π ≫ PSpace.str o m = (V.ι ≫ f) ≫ s ∧ (∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens) (hi : T ≤ π ⁻¹ᵁ ProjSpace.chart o m i) (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) = ProjSpace.pullRatio π T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ V.toScheme) (j : B.ι), ⊤ ≤ (x ≫ V.ι) ⁻¹ᵁ B.U j → Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (x ≫ π) (fun k => valF (x ≫ V.ι) (V ⊓ B.U j) (σ (e k) j)) := by
  intro o _ X Z f s B V J σ m e hσ hne
  let t : Fin (m + 1) → (pullOn B V V.ι).Sec := fun k => pullSecOn V.ι (σ (e k)) (hσ _)
  have ht : ⨆ i, nonzeroLocus (t i) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, j, hij⟩ := hne (V.ι y) y.2
    obtain ⟨k, rfl⟩ := e.surjective i
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, preimage_basicOpen_le V.ι _ (hσ _) j hij⟩
  have key : ∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens)
      (hi : T ≤ ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht ⁻¹ᵁ ProjSpace.chart o m i)
      (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧
        ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) =
          ProjSpace.pullRatio _ T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j) := by
    intro i j T hi hj
    refine ⟨?_, fun k => ?_⟩
    · rw [← resG_pullSecOn V.ι _ (hσ _) j hj]
      exact ProjSpace.isUnit_resG_sec (t i) j (hi.trans (ProjSpace.toProj_preimage_chart _ t ht i).le) hj
    · rw [← resG_pullSecOn V.ι _ (hσ _) j hj, ← resG_pullSecOn V.ι _ (hσ _) j hj]
      exact ProjSpace.sec_eq_pullRatio_toProj_mul _ t ht i k j hi hj
  refine ⟨ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht, ProjSpace.toProj_str _ t ht, key, ?_⟩
  generalize ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht = π at key
  intro K _ x j hx
  obtain ⟨i, hi⟩ := Points.exists_le_preimage_of_iSup_eq_top (x ≫ π) (ProjSpace.iSup_chart o m)
  have hT : ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ ProjSpace.chart o m i ⊓ V.ι ⁻¹ᵁ (V ⊓ B.U j)) :=
    fun z hz => ⟨hi hz, (x z).2, hx hz⟩
  obtain ⟨hu, hk⟩ := key i j _ inf_le_left inf_le_right
  have hu' := hu.map (Points.valMap x _ hT).hom
  rw [← Points.valR_eq] at hu'
  refine ⟨i, hu'.unit, hi, fun k => ?_⟩
  have := congrArg (valR x _) (hk k)
  rw [Points.valR_mul x _ hT, Points.valR_appLE x _ _ hT, ProjSpace.pullRatio, Points.valR_appLE x _ _ hT] at this
  exact this.trans (mul_comm _ _)

end GlobalTheory.ZH.CoordMap
