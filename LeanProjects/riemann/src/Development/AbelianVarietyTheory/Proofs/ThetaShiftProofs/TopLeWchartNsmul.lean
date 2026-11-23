import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbelianLetters

section Val

variable {A : Type} [CommRing A] {X Y : Scheme.{0}}

variable {L : LB X} {K : Type} [Fintype K] {ε : K → ℤ}

theorem valR_of_corr (hL : L.IsLB) {φ φ' : K → (Y ⟶ X)} (e : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (h : LB.Gen.Corr L φ ε φ' ε t t')
    (x : Sp A ⟶ Y) (j : K → L.ι) :
    valR x (LB.wchart L φ j) (t.s j).val = valR x (LB.wchart L φ' j) (t'.s j).val := by
  subst e
  rw [TorusCoord.gen_eq_of_corr hL ht ht' h]

theorem top_le_wchart_iff {Z : Scheme.{0}} (φ : K → (Y ⟶ X)) (h : Z ⟶ Y) (j : K → L.ι) :
    ⊤ ≤ LB.wchart L (fun k => h ≫ φ k) j ↔ ⊤ ≤ h ⁻¹ᵁ LB.wchart L φ j :=
  ⟨fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k,
    fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k⟩

theorem valR_pullGen (φ : K → (Y ⟶ X)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Sp A ⟶ Y) (j : K → L.ι) :
    valR (𝟙 (Sp A)) (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j).val =
      valR h (LB.wchart L φ j) (t.s j).val := by
  by_cases H : ⊤ ≤ h ⁻¹ᵁ LB.wchart L φ j
  · have H' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := (top_le_wchart_iff φ h j).2 H
    refine (HolHom.valR_res (𝟙 (Sp A)) _ _ H').trans ?_
    exact (HolHom.valR_comp (𝟙 (Sp A)) h _ _).symm.trans (by rw [Category.id_comp]; rfl)
  · have H' : ¬ ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := fun H' => H ((top_le_wchart_iff φ h j).1 H')
    exact (dif_neg H').trans (Eq.symm (show valR h (LB.wchart L φ j) (t.s j).val = 0 from dif_neg H))

end Val

section Pull

variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R}

theorem gtφT_pull {T T' : Over (Sp R)} {b : T ⟶ D.P.A} {b' : T' ⟶ D.P.A} {h : T'.left ⟶ T.left}
    (e : b'.left = h ≫ b.left) (χ : D.X) :
    Out.DegPre.gtφT D T' b' χ = fun k => h ≫ Out.DegPre.gtφT D T b χ k := by
  funext k
  rw [TorusCoord.gtφT_eq, ← Category.id_comp (D.Oφ b' χ k)]
  exact ((TorusCoord.comp_eq_of_left b b' h (𝟙 _) (by rw [Category.id_comp, e])).1 χ k).symm

theorem top_le_wchart_pull {T T' : Over (Sp R)} {b : T ⟶ D.P.A} {b' : T' ⟶ D.P.A} {h : T'.left ⟶ T.left}
    (e : b'.left = h ≫ b.left) (χ : D.X) (j : Fin 4 → D.P.L.ι) :
    ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D T' b' χ) j ↔ ⊤ ≤ h ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D T b χ) j := by
  rw [gtφT_pull e, top_le_wchart_iff]

theorem valR_of_isPull {A : Type} [CommRing A] {p : Sp A ⟶ Sp R} {T : Over (Sp R)} {g : Out.GtPt D T}
    {g' : Out.GtPt D (Over.mk p)} {h : Sp A ⟶ T.left} (H : Out.GtPt.IsPull (T' := Over.mk p) h g g') (χ : D.X)
    (j : Fin 4 → D.P.L.ι) :
    valR (𝟙 (Sp A)) (LB.wchart D.P.L (Out.DegPre.gtφT D (Over.mk p) g'.b χ) j) ((g'.s χ).s j).val =
      valR h (LB.wchart D.P.L (Out.DegPre.gtφT D T g.b χ) j) ((g.s χ).s j).val :=
  (valR_of_corr D.P.isLB (gtφT_pull H.1 χ) (g'.isGen χ) (DVR.pullGen_isGen _ _ _ _ (g.isGen χ) _) (H.2 χ) _ j).trans
    (valR_pullGen _ _ h j)

end Pull

section Ex

variable [Algebra (FractionRing ℂ) ℂ] {D : Out.DegPre ℂ} {g : ℕ} {ex : (Fin g → ℂ) → Out.GtPtF D ℂ}

theorem b_add (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) (z z' : Fin g → ℂ) :
    (ex (z + z')).b = (ex z).b * (ex z').b := (h z z').1

theorem b_zero (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) : (ex 0).b = 1 := by
  have := b_add h 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem b_nsmul (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) (n : ℕ) (z : Fin g → ℂ) :
    (ex ((n : ℂ) • z)).b = (ex z).b ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero, b_zero h]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, b_add h, ih, pow_succ]

theorem top_le_wchart_nsmul (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) {n : ℕ} {b₀ : D.P.A ⟶ D.P.A}
    (hb : b₀ = 𝟙 D.P.A ^ n) (z : Fin g → ℂ) (χ : D.X) (j : Fin 4 → D.P.L.ι) :
    ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b χ) j ↔
      ⊤ ≤ (show Sp ℂ ⟶ _ from (ex z).b.left) ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A b₀ χ) j :=
  top_le_wchart_pull (T' := Out.TF (R := ℂ) ℂ) (h := (ex z).b.left) (by
    rw [b_nsmul h, hb, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]) χ j

theorem tf_hom [IsScalarTower ℂ (FractionRing ℂ) ℂ] : (Out.TF (R := ℂ) ℂ).hom = 𝟙 (Sp ℂ) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact Spec.map_id _

def IsRatio (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (n : ℕ) (s₀ : Out.GtPt D D.P.A) (u : D.X → (Fin g → ℂ) → ℂ) : Prop :=
  ∀ x z j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j →
    chiVal (ex ((n : ℂ) • z)) x j = u x z * valAt' (show Sp ℂ ⟶ _ from (ex z).b.left)
      (LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A s₀.b x) j) ((s₀.s x).s j).val

end Ex

end GlobalTheory.AbelianLetters
