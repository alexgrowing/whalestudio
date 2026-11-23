import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IndepOnEmpty
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

variable {X Y T : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}

theorem comb_res (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) {V W : T.Opens} (hle : V ≤ W)
    (c : Fin N → Γ(T, W)) (y : Y) (i : L.ι) (h : p₁ y ∈ V) :
    comb b p₁ p₂ V (fun k => (T.presheaf.map (homOfLE hle).op).hom (c k)) y i = comb b p₁ p₂ W c y i := by
  unfold comb
  exact Finset.sum_congr rfl fun k _ => by rw [gs_res p₁ y hle h]

theorem comb_sub (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) {W : T.Opens}
    (c c' : Fin N → Γ(T, W)) (y : Y) (i : L.ι) (h : p₁ y ∈ W) :
    comb b p₁ p₂ W (c - c') y i = comb b p₁ p₂ W c y i - comb b p₁ p₂ W c' y i := by
  unfold comb
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gs_eq_gsHom p₁ y W h, Pi.sub_apply, map_sub, sub_mul]

theorem exists_affine_le (W : T.Opens) (x : T) (hx : x ∈ W) :
    ∃ V : T.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ W := by
  obtain ⟨V, hV, hxV, hle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens) hx
  exact ⟨V, hV, hxV, hle⟩

theorem indepOn_of_affine (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X)
    (H : ∀ W : T.Opens, IsAffineOpen W → IndepOn b p₁ p₂ W) (W : T.Opens) : IndepOn b p₁ p₂ W := by
  intro c hc
  funext k
  refine fn_ext fun x hx => ?_
  obtain ⟨V, hV, hxV, hle⟩ := exists_affine_le W x hx
  have h0 := H V hV (fun k => (T.presheaf.map (homOfLE hle).op).hom (c k)) fun y i h₁ h₂ =>
    (comb_res b p₁ p₂ hle c y i h₁).trans (hc y i (hle h₁) h₂)
  have hk : (T.presheaf.map (homOfLE hle).op).hom (c k) = 0 := congrFun h0 k
  have hxV' : (𝟙 T : T ⟶ T) x ∈ V := hxV
  rw [← gs_res (𝟙 T) x hle hxV', ← gs_res (𝟙 T) x hle hxV', hk, Pi.zero_apply, map_zero]

theorem basis_of_affine (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t))
    (p₁ : Y ⟶ T) (p₂ : Y ⟶ X)
    (H : ∀ W : T.Opens, IsAffineOpen W → IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W) (W : T.Opens) :
    IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W := by
  have hI := indepOn_of_affine b p₁ p₂ fun W hW => (H W hW).1
  refine ⟨hI W, fun σ hσ => ?_⟩
  let Ix := {V : T.Opens // IsAffineOpen V ∧ V ≤ W}
  have hloc : ∀ V : Ix, ∃ c : Fin N → Γ(T, V.1), ∀ (y : Y) (i : L.ι), p₁ y ∈ V.1 → p₂ y ∈ L.U i →
      gs (𝟙 Y) y _ (σ i) = comb b p₁ p₂ V.1 c y i := by
    intro V
    have hle : ∀ i, p₁ ⁻¹ᵁ V.1 ⊓ p₂ ⁻¹ᵁ L.U i ≤ p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i := fun i y hy => ⟨V.2.2 hy.1, hy.2⟩
    have hr : ∀ (y : Y) i, p₁ y ∈ V.1 → p₂ y ∈ L.U i →
        gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (hle i)).op).hom (σ i)) = gs (𝟙 Y) y _ (σ i) :=
      fun y i h₁ h₂ => gs_res (𝟙 Y) y (hle i) ⟨h₁, h₂⟩ _
    obtain ⟨c, hc⟩ := (H V.1 V.2.1).2 (fun i => (Y.presheaf.map (homOfLE (hle i)).op).hom (σ i))
      (fun y i i' h₁ h₂ h₃ => (hr y i h₁ h₂).trans ((hσ y i i' (V.2.2 h₁) h₂ h₃).trans
        (congrArg _ (hr y i' h₁ h₃).symm)))
    exact ⟨c, fun y i h₁ h₂ => (hr y i h₁ h₂).symm.trans (hc y i h₁ h₂)⟩
  choose c hc using hloc
  have hcomp : ∀ V V' : Ix, (fun k => (T.presheaf.map (homOfLE (inf_le_left : V.1 ⊓ V'.1 ≤ V.1)).op).hom (c V k)) =
      (fun k => (T.presheaf.map (homOfLE (inf_le_right : V.1 ⊓ V'.1 ≤ V'.1)).op).hom (c V' k)) := by
    intro V V'
    refine sub_eq_zero.1 (hI (V.1 ⊓ V'.1) _ fun y i h₁ h₂ => ?_)
    rw [comb_sub b p₁ p₂ _ _ y i h₁, comb_res b p₁ p₂ _ _ y i h₁, comb_res b p₁ p₂ _ _ y i h₁,
      ← hc V y i h₁.1 h₂, ← hc V' y i h₁.2 h₂, sub_self]
  have glue : ∀ k, ∃ a : Γ(T, W), ∀ V : Ix, (T.presheaf.map (homOfLE V.2.2).op).hom a = c V k := by
    intro k
    obtain ⟨a, ha, -⟩ := T.sheaf.existsUnique_gluing' (fun V : Ix => V.1) W (fun V => homOfLE V.2.2)
      (fun x hx => by
        obtain ⟨V, hV, hxV, hle⟩ := exists_affine_le W x hx
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hle⟩, hxV⟩) (fun V => c V k)
      (fun V V' => congrFun (hcomp V V') k)
    exact ⟨a, ha⟩
  choose a ha using glue
  refine ⟨a, fun y i h₁ h₂ => ?_⟩
  obtain ⟨V, hV, hyV, hle⟩ := exists_affine_le W (p₁ y) h₁
  rw [hc ⟨V, hV, hle⟩ y i hyV h₂, ← comb_res b p₁ p₂ hle a y i hyV]
  exact congrArg (fun c => comb b p₁ p₂ V c y i) (funext fun k => (ha k ⟨V, hV, hle⟩).symm)

end GlobalTheory.RelBasis
