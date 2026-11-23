import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstFnCompSpMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CechPrimitive
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSymmOfSquare
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerOfIsPushout
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLieCombZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSquareOfIsGrpPullback
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Sym

private lemma pbT_rsT_eq_pbT_of_le_preimage {Y Z : Scheme.{0}} (n : Z ⟶ Y) {O₀ T : Y.Opens} (s : Γ(Y, O₀)) (hT : T ≤ O₀)
    {O : Z.Opens} (hO : O ≤ n ⁻¹ᵁ T) : pbT n (rsT s T) O = pbT n s O := by
  rw [← pbT_id s T, pbT_pbT n (𝟙 Y) (le_trans hT (le_of_eq rfl)) hO, Category.comp_id]

private lemma pbT_add_pbT_eq_pbT_add {Y Z : Scheme.{0}} (n : Z ⟶ Y) {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Z.Opens) :
    pbT n s O + pbT n t O = pbT n (s + t) O := by
  unfold pbT
  split_ifs <;> simp

theorem pbT_coc {Y Z : Scheme.{0}} {I : Type} {U : I → Y.Opens} {c : C1 U} (hc : IsCoc U c) (n : Z ⟶ Y) (i j k : I)
    {O : Z.Opens} (hi : O ≤ n ⁻¹ᵁ U i) (hj : O ≤ n ⁻¹ᵁ U j) (hk : O ≤ n ⁻¹ᵁ U k) :
    pbT n (c i j) O + pbT n (c j k) O = pbT n (c i k) O := by
  have hT : O ≤ n ⁻¹ᵁ (U i ⊓ U j ⊓ U k) := by
    intro x hx
    exact ⟨⟨hi hx, hj hx⟩, hk hx⟩
  rw [← pbT_rsT_eq_pbT_of_le_preimage n (c i j) (inf_le_left) hT, ← pbT_rsT_eq_pbT_of_le_preimage n (c j k) (le_trans (le_of_eq (by ac_rfl)) inf_le_right) hT,
    ← pbT_rsT_eq_pbT_of_le_preimage n (c i k) (le_inf (le_trans inf_le_left inf_le_left) inf_le_right) hT, pbT_add_pbT_eq_pbT_add, hc i j k]

theorem exists_square_data {K R : Type} [Field K] [CommRing R] {g : ℕ} {X X₂ Y Z : Scheme.{0}} {m : Y ⟶ X}
    {D : R → K} {q₂ : Z ⟶ Sp K} {s₂ : X₂ ⟶ Sp R} {m₂ : Z ⟶ X₂} {π₀ π₁ π₂ : X₂ ⟶ X} {p₀ p₁ p₂ : Z ⟶ Y}
    (sq₀ : m₂ ≫ π₀ = p₀ ≫ m) (sq₁ : m₂ ≫ π₁ = p₁ ≫ m) (sq₂ : m₂ ≫ π₂ = p₂ ≫ m) {L : LB X} (hL : L.IsLB)
    {d₂ : L.ι → L.ι → ∀ O : X₂.Opens, Γ(X₂, O) → Γ(Z, m₂ ⁻¹ᵁ O)}
    (hd₂ : ∀ i j, LocDerK q₂ s₂ m₂ D (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j))
    {θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)} {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    (hφ : IsDlog m L dd φ) (hc : ∀ a, IsCoc _ (φ a))
    {w w' : Fin g → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hw : ∀ a, IsVF q₂ (w a)) (hw' : ∀ a, IsVF q₂ (w' a))
    (w₀ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₀ ⁻¹ᵁ V → w a O (pbT p₀ h O) = pbT p₀ (dd a V h) O)
    (w₁ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₁ ⁻¹ᵁ V → w a O (pbT p₁ h O) = pbT p₁ (dd a V h) O)
    (w₂ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₂ ⁻¹ᵁ V → w a O (pbT p₂ h O) = 0)
    (w₀' : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₀ ⁻¹ᵁ V → w' a O (pbT p₀ h O) = pbT p₀ (dd a V h) O)
    (w₂' : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₂ ⁻¹ᵁ V → w' a O (pbT p₂ h O) = pbT p₂ (dd a V h) O)
    (w₁' : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₁ ⁻¹ᵁ V → w' a O (pbT p₁ h O) = 0)
    (df : ∀ i i' j O, O ≤ π₁ ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ π₂ ⁻¹ᵁ L.U j → ∀ f : Γ(X₂, O),
      d₂ i' j O f - d₂ i j O f = ∑ a, pbT p₁ (θ a i i') _ * w a _ (pbT m₂ f _))
    (df' : ∀ i j j' O, O ≤ π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ (L.U j ⊓ L.U j') → ∀ f : Γ(X₂, O),
      d₂ i j' O f - d₂ i j O f = ∑ a, pbT p₂ (θ a j j') _ * w' a _ (pbT m₂ f _))
    (V : L.ι × L.ι × L.ι → Z.Opens)
    (hV : ∀ α, V α ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ L.U α.1 ⊓ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U α.2.1 ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U α.2.2)
    (prim : ∀ a, IsCob V (fun α β => pbT p₀ (φ a α.1 β.1) _ - pbT p₁ (φ a α.2.1 β.2.1) _ -
      pbT p₂ (φ a α.2.2 β.2.2) _)) :
    ∃ (k : ∀ i j, C1 (fun α => p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α))
      (e : Fin g → ∀ j α, Γ(Z, p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α)) (e' : Fin g → ∀ i α, Γ(Z, p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V α)),
      (∀ i j, IsCoc _ (k i j)) ∧
      (∀ a j j' α O, O ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U j') ⊓ V α →
        rsT (e a j' α) O - rsT (e a j α) O = pbT p₂ (φ a j j') O) ∧
      (∀ a i i' α O, O ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i') ⊓ V α →
        rsT (e' a i' α) O - rsT (e' a i α) O = pbT p₁ (φ a i i') O) ∧
      (∀ i i' j α β O, O ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i') ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α ⊓ V β →
        rsT (k i' j α β) O - rsT (k i j α β) O = ∑ a, pbT p₁ (θ a i i') O * (rsT (e a j α) O - rsT (e a j β) O)) ∧
      (∀ i j j' α β O, O ≤ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U j') ⊓ V α ⊓ V β →
        rsT (k i j' α β) O - rsT (k i j α β) O = ∑ a, pbT p₂ (θ a j j') O * (rsT (e' a i α) O - rsT (e' a i β) O)) := by
  classical
  choose b hb using prim
  have hQ : ∀ i j, p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ≤
      (𝟙 Z) ⁻¹ᵁ m₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) := by
    intro i j x hx
    have h1 : x ∈ (m₂ ≫ π₁) ⁻¹ᵁ L.U i := by rw [sq₁]; exact hx.1
    have h2 : x ∈ (m₂ ≫ π₂) ⁻¹ᵁ L.U j := by rw [sq₂]; exact hx.2
    exact And.intro h1 h2
  have hDer : ∀ (n : Z ⟶ Y) (π : X₂ ⟶ X), m₂ ≫ π = n ≫ m → ∀ i j,
      Der (n ≫ m) (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j)
        (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) :=
    fun n π h i j => der_tr (hd₂ i j) (𝟙 Z) π (by rw [Category.id_comp, h]) (hQ i j)
  have hC : ∀ (n : Z ⟶ Y) (π : X₂ ⟶ X) (sel : L.ι × L.ι × L.ι → L.ι), m₂ ≫ π = n ≫ m →
      (∀ α, V α ≤ (n ≫ m) ⁻¹ᵁ L.U (sel α)) → ∀ (i j : L.ι) (α β α₃ : L.ι × L.ι × L.ι),
      rsT (dl (n ≫ m) L (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) (sel α) (sel β)
          ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β)))
        ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) ⊓
          (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α₃)) +
      rsT (dl (n ≫ m) L (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) (sel β) (sel α₃)
          ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α₃)))
        ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) ⊓
          (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α₃)) =
      rsT (dl (n ≫ m) L (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) (sel α) (sel α₃)
          ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α₃)))
        ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) ⊓
          (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α₃)) := by
    intro n π sel h hs i j α β α₃
    have D := hDer n π h i j
    rw [D.rsT_dl L _ _ inf_le_left (inf_le_left.trans inf_le_left)
        (inf_le_left.trans (inf_le_right.trans (hs α))) (inf_le_right.trans (inf_le_right.trans (hs β))),
      D.rsT_dl L _ _ (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (inf_le_left.trans inf_le_left)
        (inf_le_left.trans (inf_le_right.trans (hs β))) (inf_le_right.trans (inf_le_right.trans (hs α₃))),
      D.rsT_dl L _ _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (inf_le_left.trans inf_le_left)
        (inf_le_left.trans (inf_le_right.trans (hs α))) (inf_le_right.trans (inf_le_right.trans (hs α₃)))]
    exact D.dl_coc hL _ _ _ (inf_le_right.trans inf_le_left)
      (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans (hs α))))
      (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans (hs β))))
      (inf_le_right.trans (inf_le_right.trans (hs α₃)))
  have hs0 : ∀ α, V α ≤ (p₀ ≫ m) ⁻¹ᵁ L.U α.1 := fun α => (hV α).trans (inf_le_left.trans inf_le_left)
  have hs1 : ∀ α, V α ≤ (p₁ ≫ m) ⁻¹ᵁ L.U α.2.1 := fun α => (hV α).trans (inf_le_left.trans inf_le_right)
  have hs2 : ∀ α, V α ≤ (p₂ ≫ m) ⁻¹ᵁ L.U α.2.2 := fun α => (hV α).trans inf_le_right
  have hR : ∀ (n : Z ⟶ Y) (π : X₂ ⟶ X) (sel : L.ι × L.ι × L.ι → L.ι), m₂ ≫ π = n ≫ m →
      (∀ α, V α ≤ (n ≫ m) ⁻¹ᵁ L.U (sel α)) → ∀ (i j : L.ι) (α β : L.ι × L.ι × L.ι) (O : Z.Opens),
      O ≤ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) →
      rsT (dl (n ≫ m) L (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) (sel α) (sel β)
          ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β))) O =
        dl (n ≫ m) L (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) (sel α) (sel β) O :=
    fun n π sel h hs i j α β O hO => (hDer n π h i j).rsT_dl L _ _ hO (inf_le_left.trans inf_le_left)
      (inf_le_left.trans (inf_le_right.trans (hs α))) (inf_le_right.trans (inf_le_right.trans (hs β)))
  have hB : ∀ (α β : L.ι × L.ι × L.ι) (O : Z.Opens), O ≤ V α ⊓ V β → ∀ a,
      pbT p₀ (φ a α.1 β.1) O - pbT p₁ (φ a α.2.1 β.2.1) O - pbT p₂ (φ a α.2.2 β.2.2) O =
        rsT (b a β) O - rsT (b a α) O := by
    intro α β O hOV a
    have h0V : V α ⊓ V β ≤ p₀ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.1 ⊓ m ⁻¹ᵁ L.U β.1) :=
      fun x hx => And.intro (hs0 α hx.1) (hs0 β hx.2)
    have h1V : V α ⊓ V β ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.1 ⊓ m ⁻¹ᵁ L.U β.2.1) :=
      fun x hx => And.intro (hs1 α hx.1) (hs1 β hx.2)
    have h2V : V α ⊓ V β ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.2 ⊓ m ⁻¹ᵁ L.U β.2.2) :=
      fun x hx => And.intro (hs2 α hx.1) (hs2 β hx.2)
    have := congrArg (fun s => rsT s O) (hb a α β)
    simp only [GlobalTheory.KS.Square.rsT_sub] at this
    rwa [GlobalTheory.KS.Square.rsT_pbT p₀ hOV h0V, GlobalTheory.KS.Square.rsT_pbT p₁ hOV h1V, GlobalTheory.KS.Square.rsT_pbT p₂ hOV h2V,
      GlobalTheory.KS.Square.rsT_rsT hOV inf_le_right, GlobalTheory.KS.Square.rsT_rsT hOV inf_le_left] at this
  refine ⟨fun i j α β =>
      dl (p₀ ≫ m) L (tr (𝟙 Z) m₂ π₀ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) α.1 β.1 _ -
        dl (p₁ ≫ m) L (tr (𝟙 Z) m₂ π₁ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) α.2.1 β.2.1 _ -
        dl (p₂ ≫ m) L (tr (𝟙 Z) m₂ π₂ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) α.2.2 β.2.2 _,
    fun a j α => pbT p₂ (φ a α.2.2 j) _ - rsT (b a α) _,
    fun a i α => pbT p₁ (φ a α.2.1 i) _ - rsT (b a α) _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j α β α₃
    simp only [GlobalTheory.KS.Square.rsT_sub]
    linear_combination hC p₀ π₀ (fun α => α.1) sq₀ hs0 i j α β α₃ -
      hC p₁ π₁ (fun α => α.2.1) sq₁ hs1 i j α β α₃ - hC p₂ π₂ (fun α => α.2.2) sq₂ hs2 i j α β α₃
  · intro a j j' α O hO
    simp only [GlobalTheory.KS.Square.rsT_sub]
    have hA : O ≤ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j' ⊓ V α := fun x hx => And.intro (hO hx).1.2 (hO hx).2
    have hA' : O ≤ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α := fun x hx => And.intro (hO hx).1.1 (hO hx).2
    have hB' : p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j' ⊓ V α ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.2 ⊓ m ⁻¹ᵁ L.U j') :=
      fun x hx => And.intro (hs2 α hx.2) hx.1
    have hB'' : p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.2 ⊓ m ⁻¹ᵁ L.U j) :=
      fun x hx => And.intro (hs2 α hx.2) hx.1
    rw [GlobalTheory.KS.Square.rsT_pbT p₂ hA hB', GlobalTheory.KS.Square.rsT_pbT p₂ hA' hB'',
      GlobalTheory.KS.Square.rsT_rsT hA inf_le_right, GlobalTheory.KS.Square.rsT_rsT hA' inf_le_right]
    have c1 := pbT_coc (hc a) p₂ α.2.2 j j' (O := O) (fun x hx => hs2 α (hO hx).2) (fun x hx => (hO hx).1.1)
      (fun x hx => (hO hx).1.2)
    linear_combination -c1
  · intro a i i' α O hO
    simp only [GlobalTheory.KS.Square.rsT_sub]
    have hA : O ≤ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i' ⊓ V α := fun x hx => And.intro (hO hx).1.2 (hO hx).2
    have hA' : O ≤ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V α := fun x hx => And.intro (hO hx).1.1 (hO hx).2
    have hB' : p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i' ⊓ V α ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.1 ⊓ m ⁻¹ᵁ L.U i') :=
      fun x hx => And.intro (hs1 α hx.2) hx.1
    have hB'' : p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V α ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.1 ⊓ m ⁻¹ᵁ L.U i) :=
      fun x hx => And.intro (hs1 α hx.2) hx.1
    rw [GlobalTheory.KS.Square.rsT_pbT p₁ hA hB', GlobalTheory.KS.Square.rsT_pbT p₁ hA' hB'',
      GlobalTheory.KS.Square.rsT_rsT hA inf_le_right, GlobalTheory.KS.Square.rsT_rsT hA' inf_le_right]
    have c1 := pbT_coc (hc a) p₁ α.2.1 i i' (O := O) (fun x hx => hs1 α (hO hx).2) (fun x hx => (hO hx).1.1)
      (fun x hx => (hO hx).1.2)
    linear_combination -c1
  · intro i i' j α β O hO
    simp only [GlobalTheory.KS.Square.rsT_sub]
    have hOi : O ≤ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) :=
      fun x hx => And.intro (And.intro (And.intro (hO hx).1.1.1.1 (hO hx).1.1.2) (hO hx).1.2)
        (And.intro (And.intro (hO hx).1.1.1.1 (hO hx).1.1.2) (hO hx).2)
    have hOi' : O ≤ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i' ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i' ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) :=
      fun x hx => And.intro (And.intro (And.intro (hO hx).1.1.1.2 (hO hx).1.1.2) (hO hx).1.2)
        (And.intro (And.intro (hO hx).1.1.1.2 (hO hx).1.1.2) (hO hx).2)
    rw [hR p₀ π₀ (fun α => α.1) sq₀ hs0 i j α β O hOi, hR p₁ π₁ (fun α => α.2.1) sq₁ hs1 i j α β O hOi,
      hR p₂ π₂ (fun α => α.2.2) sq₂ hs2 i j α β O hOi, hR p₀ π₀ (fun α => α.1) sq₀ hs0 i' j α β O hOi',
      hR p₁ π₁ (fun α => α.2.1) sq₁ hs1 i' j α β O hOi', hR p₂ π₂ (fun α => α.2.2) sq₂ hs2 i' j α β O hOi']
    have hOV : O ≤ V α ⊓ V β := fun x hx => And.intro (hO hx).1.2 (hO hx).2
    have hAα : O ≤ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α := fun x hx => And.intro (hO hx).1.1.2 (hO hx).1.2
    have hAβ : O ≤ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β := fun x hx => And.intro (hO hx).1.1.2 (hO hx).2
    have hCα : p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.2 ⊓ m ⁻¹ᵁ L.U j) :=
      fun x hx => And.intro (hs2 α hx.2) hx.1
    have hCβ : p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U β.2.2 ⊓ m ⁻¹ᵁ L.U j) :=
      fun x hx => And.intro (hs2 β hx.2) hx.1
    simp only [GlobalTheory.KS.Square.rsT_pbT p₂ hAα hCα, GlobalTheory.KS.Square.rsT_pbT p₂ hAβ hCβ,
      GlobalTheory.KS.Square.rsT_rsT hAα inf_le_right, GlobalTheory.KS.Square.rsT_rsT hAβ inf_le_right]
    have hQ₀ : π₁ ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ π₂ ⁻¹ᵁ L.U j ≤ π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j :=
      fun x hx => And.intro hx.1.1 hx.2
    have hQ₀' : π₁ ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ π₂ ⁻¹ᵁ L.U j ≤ π₁ ⁻¹ᵁ L.U i' ⊓ π₂ ⁻¹ᵁ L.U j :=
      fun x hx => And.intro hx.1.2 hx.2
    have hT : m₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ π₂ ⁻¹ᵁ L.U j) ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i') := by
      intro x hx
      have h1 : x ∈ (m₂ ≫ π₁) ⁻¹ᵁ (L.U i ⊓ L.U i') := hx.1
      rw [sq₁] at h1
      exact h1
    have hOQ : O ≤ m₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ π₂ ⁻¹ᵁ L.U j) := by
      intro x hx
      have h1 : x ∈ (p₁ ≫ m) ⁻¹ᵁ (L.U i ⊓ L.U i') := (hO hx).1.1.1
      have h2 : x ∈ (p₂ ≫ m) ⁻¹ᵁ L.U j := (hO hx).1.1.2
      rw [← sq₁] at h1
      rw [← sq₂] at h2
      exact And.intro h1 h2
    have E0 := dl_diff (hd₂ i j) (hd₂ i' j) sq₀ hQ₀ hQ₀' (fun a => θ a i i') hT hw (df i i' j) 1
      (fun a V h O hO => by rw [w₀ a V h O hO, Nat.cast_one, _root_.one_mul]) hφ α.1 β.1 hOQ
      (fun x hx => hs0 α (hO hx).1.2) (fun x hx => hs0 β (hO hx).2)
    have E1 := dl_diff (hd₂ i j) (hd₂ i' j) sq₁ hQ₀ hQ₀' (fun a => θ a i i') hT hw (df i i' j) 1
      (fun a V h O hO => by rw [w₁ a V h O hO, Nat.cast_one, _root_.one_mul]) hφ α.2.1 β.2.1 hOQ
      (fun x hx => hs1 α (hO hx).1.2) (fun x hx => hs1 β (hO hx).2)
    have E2 := dl_diff (hd₂ i j) (hd₂ i' j) sq₂ hQ₀ hQ₀' (fun a => θ a i i') hT hw (df i i' j) 0
      (fun a V h O hO => by rw [w₂ a V h O hO, Nat.cast_zero, MulZeroClass.zero_mul]) hφ α.2.2 β.2.2 hOQ
      (fun x hx => hs2 α (hO hx).1.2) (fun x hx => hs2 β (hO hx).2)
    have key : ∀ a, pbT p₁ (θ a i i') O * (pbT p₂ (φ a α.2.2 j) O - rsT (b a α) O - (pbT p₂ (φ a β.2.2 j) O - rsT (b a β) O)) =
        pbT p₁ (θ a i i') O * (((1 : ℕ) : Γ(Z, O)) * pbT p₀ (φ a α.1 β.1) O) -
        pbT p₁ (θ a i i') O * (((1 : ℕ) : Γ(Z, O)) * pbT p₁ (φ a α.2.1 β.2.1) O) -
        pbT p₁ (θ a i i') O * (((0 : ℕ) : Γ(Z, O)) * pbT p₂ (φ a α.2.2 β.2.2) O) := by
      intro a
      have c1 := pbT_coc (hc a) p₂ α.2.2 β.2.2 j (O := O) (fun x hx => hs2 α (hO hx).1.2)
        (fun x hx => hs2 β (hO hx).2) (fun x hx => (hO hx).1.1.2)
      have c2 := hB α β O hOV a
      push_cast
      linear_combination (-(pbT p₁ (θ a i i') O)) * (c1 + c2)
    rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linear_combination E0 - E1 - E2
  · intro i j j' α β O hO
    simp only [GlobalTheory.KS.Square.rsT_sub]
    have hOi : O ≤ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) :=
      fun x hx => And.intro (And.intro (And.intro (hO hx).1.1.1 (hO hx).1.1.2.1) (hO hx).1.2)
        (And.intro (And.intro (hO hx).1.1.1 (hO hx).1.1.2.1) (hO hx).2)
    have hOi' : O ≤ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j' ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j' ⊓ V β) :=
      fun x hx => And.intro (And.intro (And.intro (hO hx).1.1.1 (hO hx).1.1.2.2) (hO hx).1.2)
        (And.intro (And.intro (hO hx).1.1.1 (hO hx).1.1.2.2) (hO hx).2)
    rw [hR p₀ π₀ (fun α => α.1) sq₀ hs0 i j α β O hOi, hR p₁ π₁ (fun α => α.2.1) sq₁ hs1 i j α β O hOi,
      hR p₂ π₂ (fun α => α.2.2) sq₂ hs2 i j α β O hOi, hR p₀ π₀ (fun α => α.1) sq₀ hs0 i j' α β O hOi',
      hR p₁ π₁ (fun α => α.2.1) sq₁ hs1 i j' α β O hOi', hR p₂ π₂ (fun α => α.2.2) sq₂ hs2 i j' α β O hOi']
    have hOV : O ≤ V α ⊓ V β := fun x hx => And.intro (hO hx).1.2 (hO hx).2
    have hAα : O ≤ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V α := fun x hx => And.intro (hO hx).1.1.1 (hO hx).1.2
    have hAβ : O ≤ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V β := fun x hx => And.intro (hO hx).1.1.1 (hO hx).2
    have hCα : p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V α ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.1 ⊓ m ⁻¹ᵁ L.U i) :=
      fun x hx => And.intro (hs1 α hx.2) hx.1
    have hCβ : p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V β ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U β.2.1 ⊓ m ⁻¹ᵁ L.U i) :=
      fun x hx => And.intro (hs1 β hx.2) hx.1
    simp only [GlobalTheory.KS.Square.rsT_pbT p₁ hAα hCα, GlobalTheory.KS.Square.rsT_pbT p₁ hAβ hCβ,
      GlobalTheory.KS.Square.rsT_rsT hAα inf_le_right, GlobalTheory.KS.Square.rsT_rsT hAβ inf_le_right]
    have hQ₀ : π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j :=
      fun x hx => And.intro hx.1 hx.2.1
    have hQ₀' : π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j' :=
      fun x hx => And.intro hx.1 hx.2.2
    have hT : m₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ (L.U j ⊓ L.U j')) ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U j') := by
      intro x hx
      have h1 : x ∈ (m₂ ≫ π₂) ⁻¹ᵁ (L.U j ⊓ L.U j') := hx.2
      rw [sq₂] at h1
      exact h1
    have hOQ : O ≤ m₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ (L.U j ⊓ L.U j')) := by
      intro x hx
      have h1 : x ∈ (p₁ ≫ m) ⁻¹ᵁ L.U i := (hO hx).1.1.1
      have h2 : x ∈ (p₂ ≫ m) ⁻¹ᵁ (L.U j ⊓ L.U j') := (hO hx).1.1.2
      rw [← sq₁] at h1
      rw [← sq₂] at h2
      exact And.intro h1 h2
    have E0 := dl_diff (hd₂ i j) (hd₂ i j') sq₀ hQ₀ hQ₀' (fun a => θ a j j') hT hw' (df' i j j') 1
      (fun a V h O hO => by rw [w₀' a V h O hO, Nat.cast_one, _root_.one_mul]) hφ α.1 β.1 hOQ
      (fun x hx => hs0 α (hO hx).1.2) (fun x hx => hs0 β (hO hx).2)
    have E1 := dl_diff (hd₂ i j) (hd₂ i j') sq₁ hQ₀ hQ₀' (fun a => θ a j j') hT hw' (df' i j j') 0
      (fun a V h O hO => by rw [w₁' a V h O hO, Nat.cast_zero, MulZeroClass.zero_mul]) hφ α.2.1 β.2.1 hOQ
      (fun x hx => hs1 α (hO hx).1.2) (fun x hx => hs1 β (hO hx).2)
    have E2 := dl_diff (hd₂ i j) (hd₂ i j') sq₂ hQ₀ hQ₀' (fun a => θ a j j') hT hw' (df' i j j') 1
      (fun a V h O hO => by rw [w₂' a V h O hO, Nat.cast_one, _root_.one_mul]) hφ α.2.2 β.2.2 hOQ
      (fun x hx => hs2 α (hO hx).1.2) (fun x hx => hs2 β (hO hx).2)
    have key : ∀ a, pbT p₂ (θ a j j') O * (pbT p₁ (φ a α.2.1 i) O - rsT (b a α) O - (pbT p₁ (φ a β.2.1 i) O - rsT (b a β) O)) =
        pbT p₂ (θ a j j') O * (((1 : ℕ) : Γ(Z, O)) * pbT p₀ (φ a α.1 β.1) O) -
        pbT p₂ (θ a j j') O * (((0 : ℕ) : Γ(Z, O)) * pbT p₁ (φ a α.2.1 β.2.1) O) -
        pbT p₂ (θ a j j') O * (((1 : ℕ) : Γ(Z, O)) * pbT p₂ (φ a α.2.2 β.2.2) O) := by
      intro a
      have c1 := pbT_coc (hc a) p₁ α.2.1 β.2.1 i (O := O) (fun x hx => hs1 α (hO hx).1.2)
        (fun x hx => hs1 β (hO hx).2) (fun x hx => (hO hx).1.1.1)
      have c2 := hB α β O hOV a
      push_cast
      linear_combination (-(pbT p₂ (θ a j j') O)) * (c1 + c2)
    rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linear_combination E0 - E1 - E2

theorem exists_symm_of_ksCoc : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ) := by
  intro hLaws hLaws2 hGen K _ P₀ g v dd hv hdd R _ x₀ P m L _ D d θ φ hpb hL hU hiso hks hφ
  classical
  obtain ⟨⟨m₂, hsqr, hm₀, hbase⟩, hsep, hpull, haff, hinter⟩ := square_fibre_affine_opens K P₀ R x₀ P m hpb
  have hmb : m ≫ P.A.hom = P₀.A.hom ≫ spMap x₀ := hpb.1.w
  have hdl := (DlogPol.dlog_independent K P₀ g v dd hv hdd P.A.left m L hL hiso).2 φ hφ
  have hcov : ⨆ i, m ⁻¹ᵁ L.U i = ⊤ := by
    refine eq_top_iff.2 (fun x _ => ?_)
    have hx : m.base x ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  choose w hw using fun a => SquareField.main K P₀.A (v a) (dd a) (hv.1 a) (hdd a)
    (fst P₀.A P₀.A) (snd P₀.A P₀.A) (Or.inl ⟨rfl, rfl⟩)
  choose w' hw' using fun a => SquareField.main K P₀.A (v a) (dd a) (hv.1 a) (hdd a)
    (snd P₀.A P₀.A) (fst P₀.A P₀.A) (Or.inr ⟨rfl, rfl⟩)
  have hvf : ∀ a, IsVF (P₀.A ⊗ P₀.A).hom (w a) :=
    fun a => ⟨(hw a).1, (hw a).2.1, (hw a).2.2.1, (hw a).2.2.2.1⟩
  have hvf' : ∀ a, IsVF (P₀.A ⊗ P₀.A).hom (w' a) :=
    fun a => ⟨(hw' a).1, (hw' a).2.1, (hw' a).2.2.1, (hw' a).2.2.2.1⟩
  have hPL := fun (W W' : P.A.left.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') =>
    ProdLift.main K R x₀ P.A P₀.A m m₂ D W W' hmb hsqr hW hW' _ rfl
  choose d₂ hd₂ using fun i j => (hPL (L.U i) (L.U j) (hU i) (hU j)).1 (d i) (d j) (hks.der i) (hks.der j)
  have df : ∀ i i' j O, O ≤ (fst P.A P.A).left ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ (snd P.A P.A).left ⁻¹ᵁ L.U j →
      ∀ f : Γ((P.A ⊗ P.A).left, O), d₂ i' j O f - d₂ i j O f =
        ∑ a, pbT (fst P₀.A P₀.A).left (θ a i i') _ * w a _ (pbT m₂ f _) :=
    fun i i' j O hO f => diff_prod x₀ (hks.der i) (hks.der i') (hks.der j) (hU i) (hU i') (hU j) hbase
      (hd₂ i j).1 (hd₂ i' j).1 hsqr.1 hsqr.2 inf_le_left inf_le_left inf_le_right inf_le_right
      (Q₀ := (fst P.A P.A).left ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ (snd P.A P.A).left ⁻¹ᵁ L.U j)
      (fun x hx => And.intro hx.1.1 hx.2) (fun x hx => And.intro hx.1.2 hx.2)
      (hd₂ i j).2.1 (hd₂ i j).2.2 (hd₂ i' j).2.1 (hd₂ i' j).2.2
      (hPL (L.U i ⊓ L.U i') (L.U j) (hinter _ _ (hU i) (hU i')) (hU j)).2
      (fun a => θ a i i') (fun f => hks.diff i i' _ le_rfl f) hvf
      (fun a => (hw a).2.2.2.2.2.1) (fun a => (hw a).2.2.2.2.2.2) O hO f
  have df' : ∀ i j j' O, O ≤ (fst P.A P.A).left ⁻¹ᵁ L.U i ⊓ (snd P.A P.A).left ⁻¹ᵁ (L.U j ⊓ L.U j') →
      ∀ f : Γ((P.A ⊗ P.A).left, O), d₂ i j' O f - d₂ i j O f =
        ∑ a, pbT (snd P₀.A P₀.A).left (θ a j j') _ * w' a _ (pbT m₂ f _) :=
    fun i j j' O hO f => diff_prod x₀ (hks.der j) (hks.der j') (hks.der i) (hU j) (hU j') (hU i) hbase
      (hd₂ i j).1 (hd₂ i j').1 hsqr.2 hsqr.1 inf_le_right inf_le_right inf_le_left inf_le_left
      (Q₀ := (fst P.A P.A).left ⁻¹ᵁ L.U i ⊓ (snd P.A P.A).left ⁻¹ᵁ (L.U j ⊓ L.U j'))
      (fun x hx => And.intro hx.1 hx.2.1) (fun x hx => And.intro hx.1 hx.2.2)
      (hd₂ i j).2.2 (hd₂ i j).2.1 (hd₂ i j').2.2 (hd₂ i j').2.1
      (fun a b ha hb h1 h2 => (hPL (L.U i) (L.U j ⊓ L.U j') (hU i) (hinter _ _ (hU j) (hU j'))).2 a b ha hb h2 h1)
      (fun a => θ a j j') (fun f => hks.diff j j' _ le_rfl f) hvf'
      (fun a => (hw' a).2.2.2.2.2.1) (fun a => (hw' a).2.2.2.2.2.2) O hO f
  have prim := fun a => Primitive.cech_primitive hLaws hLaws2 hGen K P₀ L.ι (fun i => m ⁻¹ᵁ L.U i) (φ a) hcov (hdl.1 a)
  obtain ⟨k, e, e', hk, he, he', hki, hkj⟩ := exists_square_data hm₀ hsqr.1 hsqr.2 hL (fun i j => (hd₂ i j).1)
    hφ hdl.1 hvf hvf' (fun a => (hw a).2.2.2.2.1) (fun a => (hw a).2.2.2.2.2.1) (fun a => (hw a).2.2.2.2.2.2)
    (fun a => (hw' a).2.2.2.2.1) (fun a => (hw' a).2.2.2.2.2.1) (fun a => (hw' a).2.2.2.2.2.2) df df' _
    (fun α => le_rfl) prim
  exact exists_isSymm_of_square K P₀.A.left (P₀.A ⊗ P₀.A).left P₀.A.hom (fst P₀.A P₀.A).left (snd P₀.A P₀.A).left
    L.ι (fun i => m ⁻¹ᵁ L.U i) g θ φ hsep hpull (fun i => haff _ (hU i)) hdl.2 _ _ k e e'
    (Primitive.iSup_triple hcov _ _ _) hk he he' hki hkj

end GlobalTheory.KS.Sym
end
