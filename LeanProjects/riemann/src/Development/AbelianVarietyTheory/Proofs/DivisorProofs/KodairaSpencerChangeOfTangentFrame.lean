import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndSectionValueTranslateProdFirstOrderLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateTangentCombinationEqProdStatement
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

attribute [local instance] Over.cartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.KSFrameChange

theorem sum_four_comm {R : Type} [AddCommMonoid R] {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → R) :
    ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ y, ∑ x, ∑ b, ∑ a, F a b x y :=
  calc ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ a, ∑ b, ∑ y, ∑ x, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ y, ∑ b, ∑ x, F a b x y := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ a, ∑ b, ∑ x, F a b x y := Finset.sum_comm
    _ = ∑ y, ∑ a, ∑ x, ∑ b, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ a, ∑ b, F a b x y := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ b, ∑ a, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_four_comm' {R : Type} [AddCommMonoid R] {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → R) :
    ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ x, ∑ y, ∑ b, ∑ a, F a b x y :=
  (sum_four_comm F).trans Finset.sum_comm

theorem isKS_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (V : X.Opens) (U : X.affineOpens) (n n' : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (v' : Fin n' → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (B : Matrix (Fin n) (Fin n') Γ(X, U.1))
    (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)),
    (∀ a, IsTanAtG t (GlobalTheory.LogKS.chart U) (v a)) → (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) →
    (∀ a, IsCombAtG t (GlobalTheory.LogKS.chart U) v' (B a) (v a)) → GlobalTheory.LogKS.IsKS t V U v D Θ →
    GlobalTheory.LogKS.IsKS t V U v' D (_root_.Matrix.transpose B * Θ * B) := by
  intro E _ _ _ H X t V U n n' v v' B D Θ hv hv' hB hKS
  obtain ⟨J, W, j, d, hcov, hWL, hF, hD, hc⟩ := hKS
  refine ⟨J, W, j, d, hcov, hWL, hF, hD, ?_⟩
  intro i i' O hO f S _ φ g₀ w' hg hgO htr'
  choose w hw using fun a => (GlobalTheory.LogKS.existsUnique_isTranslate t φ hg (hv a)).exists
  rw [hc i i' O hO f S φ g₀ w hg hgO hw]
  let g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  choose gc yc hgc hyc hwc using htr'
  have hgc' : ∀ c, gc c = g' := fun c => Over.OverMorphism.ext (hgc c)
  have key : ∀ a (O' : t.G.left.Opens) (f' : Γ(t.G.left, O')), ⊤ ≤ g₀ ⁻¹ᵁ O' →
      (valR (w a) O' f').snd = ∑ c, φ (B a c) * (valR (w' c) O' f').snd := by
    intro a O' f' hO'
    obtain ⟨h0, hw'⟩ := GlobalTheory.T.translate_tangent_combination_eq_prod t U v' (B a) (v a) φ g₀ hg g' yc hv' (hB a) rfl hyc
    rw [hw' (w a) (hw a), GlobalTheory.T.snd_sectionValue_translate_prod_first_order_linear (g₀ ≫ t.G.hom) t.G g₀ g' rfl yc (fun c => φ (B a c)) h0 O' f' hO']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hwc c, hgc' c]
  simp_rw [key _ O f hgO]
  have hO2 : ⊤ ≤ g₀ ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i')) :=
    hgO.trans (fun x hx => (hO.trans (inf_le_inf (hWL i) (hWL i'))) hx)
  simp_rw [key _ _ _ hO2]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [sum_four_comm']
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KSFrameChange
