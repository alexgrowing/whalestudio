import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsCobOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KunnethSymmProductAffineCoversStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Square

variable {Z : Scheme.{0}}

theorem rsT_eq {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) : rsT s O = resG Z h s := by
  unfold rsT
  rw [dif_pos h]

theorem rsT_self {O : Z.Opens} (s : Γ(Z, O)) : rsT s O = s := by
  unfold rsT resG
  simp

theorem rsT_add {O₀ : Z.Opens} (O : Z.Opens) (s t : Γ(Z, O₀)) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT
  split_ifs with h
  · exact map_add _ s t
  · exact (add_zero 0).symm

theorem rsT_sub {O₀ : Z.Opens} (O : Z.Opens) (s t : Γ(Z, O₀)) : rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT
  split_ifs with h
  · exact map_sub _ s t
  · exact (sub_zero 0).symm

theorem rsT_neg {O₀ : Z.Opens} (O : Z.Opens) (s : Γ(Z, O₀)) : rsT (-s) O = -rsT s O := by
  unfold rsT
  split_ifs with h
  · exact map_neg _ s
  · exact neg_zero.symm

theorem rsT_mul {O₀ : Z.Opens} (O : Z.Opens) (s t : Γ(Z, O₀)) : rsT (s * t) O = rsT s O * rsT t O := by
  unfold rsT
  split_ifs with h
  · exact map_mul _ s t
  · exact (mul_zero 0).symm

theorem rsT_sum {O₀ : Z.Opens} (O : Z.Opens) {g : ℕ} (s : Fin g → Γ(Z, O₀)) :
    rsT (∑ a, s a) O = ∑ a, rsT (s a) O := by
  unfold rsT
  split_ifs with h
  · exact map_sum _ s Finset.univ
  · exact Finset.sum_const_zero.symm

theorem rsT_rsT {O₀ O O' : Z.Opens} (h' : O' ≤ O) (h : O ≤ O₀) (s : Γ(Z, O₀)) :
    rsT (rsT s O) O' = rsT s O' := by
  rw [rsT_eq h', rsT_eq h, rsT_eq (h'.trans h)]
  unfold resG
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rsT_pbT {Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O O' : Z.Opens} (h' : O' ≤ O)
    (h : O ≤ f ⁻¹ᵁ O₀) (s : Γ(Y, O₀)) : rsT (pbT f s O) O' = pbT f s O' := by
  unfold pbT
  rw [dif_pos h, dif_pos (h'.trans h), rsT_eq h']
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

variable {J : Type} {V : J → Z.Opens}

theorem iSup_inf_eq (hV : ⨆ α, V α = ⊤) (W : Z.Opens) : ⨆ α, W ⊓ V α = W := by
  rw [← inf_iSup_eq, hV, inf_top_eq]

theorem ext_cover (hV : ⨆ α, V α = ⊤) {W : Z.Opens} (s t : Γ(Z, W))
    (h : ∀ α, rsT s (W ⊓ V α) = rsT t (W ⊓ V α)) : s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq' (F := Z.sheaf) (U := fun α => W ⊓ V α) (V := W)
    (iUV := fun α => homOfLE inf_le_left) (iSup_inf_eq hV W).ge s t fun α => ?_
  have hα := h α
  rw [rsT_eq inf_le_left, rsT_eq inf_le_left] at hα
  exact hα

theorem exists_glue (hV : ⨆ α, V α = ⊤) (W : Z.Opens) (F : J → ∀ O : Z.Opens, Γ(Z, O))
    (h₁ : ∀ α O, O ≤ W ⊓ V α → rsT (F α (W ⊓ V α)) O = F α O)
    (h₂ : ∀ α β O, O ≤ W ⊓ V α ⊓ V β → F α O = F β O) :
    ∃ s : Γ(Z, W), ∀ α O, O ≤ W ⊓ V α → rsT s O = F α O := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := Z.sheaf) (U := fun α => W ⊓ V α) (V := W)
    (iUV := fun α => homOfLE inf_le_left) (iSup_inf_eq hV W).ge (fun α => F α (W ⊓ V α)) (by
      intro α β
      have e1 := h₁ α ((W ⊓ V α) ⊓ (W ⊓ V β)) inf_le_left
      have e2 := h₁ β ((W ⊓ V α) ⊓ (W ⊓ V β)) inf_le_right
      have e3 := h₂ α β ((W ⊓ V α) ⊓ (W ⊓ V β)) (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      rw [rsT_eq inf_le_left] at e1
      rw [rsT_eq inf_le_right] at e2
      exact e1.trans (e3.trans e2.symm))
  refine ⟨s, fun α O hO => ?_⟩
  have hsα : resG Z (inf_le_left : W ⊓ V α ≤ W) s = F α (W ⊓ V α) := hs α
  rw [← rsT_rsT hO inf_le_left s, rsT_eq (inf_le_left : W ⊓ V α ≤ W) s, hsα]
  exact h₁ α O hO

theorem isAffineOpen_prod {S X Y : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S}
    (H : IsPullback p q iX iY) [IsAffine S] {U : X.Opens} {W : Y.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) := by
  have : IsAffine U := hU
  have : IsAffine W := hW
  have : IsAffine (⊤ : S.Opens) := isAffineOpen_top S
  exact IsAffine.of_isPullback
    (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top rfl)

theorem exists_split (hV : ⨆ α, V α = ⊤) {W : Z.Opens} (hW : IsAffineOpen W)
    (k : C1 fun α => W ⊓ V α) (hk : IsCoc _ k) :
    ∃ c : ∀ α, Γ(Z, W ⊓ V α), ∀ α β O, O ≤ W ⊓ V α ⊓ V β →
      rsT (k α β) O = rsT (c β) O - rsT (c α) O := by
  have hW' : IsAffineOpen (⨆ α, W ⊓ V α) := by
    rw [iSup_inf_eq hV W]
    exact hW
  obtain ⟨b, hb⟩ := isCob_of_isAffineOpen Z J (fun α => W ⊓ V α) k hW' hk
  refine ⟨b, fun α β O hO => ?_⟩
  have hO' : O ≤ (W ⊓ V α) ⊓ (W ⊓ V β) :=
    le_inf (hO.trans inf_le_left) (le_inf (hO.trans (inf_le_left.trans inf_le_left)) (hO.trans inf_le_right))
  rw [hb α β, rsT_sub, rsT_rsT hO' inf_le_right, rsT_rsT hO' inf_le_left]

theorem exists_compare (hV : ⨆ α, V α = ⊤) {Y : Scheme.{0}} (p : Z ⟶ Y) {T : Y.Opens}
    {W A B E : Z.Opens} (hA : W ≤ A) (hB : W ≤ B) (hE : W ≤ E) (hT : W ≤ p ⁻¹ᵁ T) {g : ℕ}
    (θ : Fin g → Γ(Y, T)) (e : Fin g → ∀ α, Γ(Z, E ⊓ V α))
    (k : C1 fun α => A ⊓ V α) (k' : C1 fun α => B ⊓ V α)
    (c : ∀ α, Γ(Z, A ⊓ V α)) (c' : ∀ α, Γ(Z, B ⊓ V α))
    (hc : ∀ α β O, O ≤ A ⊓ V α ⊓ V β → rsT (k α β) O = rsT (c β) O - rsT (c α) O)
    (hc' : ∀ α β O, O ≤ B ⊓ V α ⊓ V β → rsT (k' α β) O = rsT (c' β) O - rsT (c' α) O)
    (h : ∀ α β O, O ≤ W ⊓ V α ⊓ V β → rsT (k' α β) O - rsT (k α β) O =
      ∑ a, pbT p (θ a) O * (rsT (e a α) O - rsT (e a β) O)) :
    ∃ s : Γ(Z, W), ∀ α O, O ≤ W ⊓ V α →
      rsT s O = rsT (c' α) O - rsT (c α) O + ∑ a, pbT p (θ a) O * rsT (e a α) O := by
  refine exists_glue hV W
    (fun α O => rsT (c' α) O - rsT (c α) O + ∑ a, pbT p (θ a) O * rsT (e a α) O)
    (fun α O hO => ?_) (fun α β O hO => ?_)
  · have hAα : W ⊓ V α ≤ A ⊓ V α := inf_le_inf_right _ hA
    have hBα : W ⊓ V α ≤ B ⊓ V α := inf_le_inf_right _ hB
    have hEα : W ⊓ V α ≤ E ⊓ V α := inf_le_inf_right _ hE
    have hTα : W ⊓ V α ≤ p ⁻¹ᵁ T := inf_le_left.trans hT
    simp only [rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_rsT hO hAα, rsT_rsT hO hBα, rsT_rsT hO hEα,
      rsT_pbT p hO hTα]
  · have h1 := hc α β O (hO.trans (inf_le_inf_right _ (inf_le_inf_right _ hA)))
    have h2 := hc' α β O (hO.trans (inf_le_inf_right _ (inf_le_inf_right _ hB)))
    have h3 := h α β O hO
    simp only [mul_sub, Finset.sum_sub_distrib] at h3
    linear_combination h2 - h1 - h3

end GlobalTheory.KS.Square

namespace GlobalTheory.KS
open Square

theorem exists_isSymm_of_square : ∀ (K : Type) [Field K] (Y Z : Scheme.{0}) (q : Y ⟶ Sp K) (p₁ p₂ : Z ⟶ Y) (I : Type) [Finite I] (U : I → Y.Opens) (g : ℕ) (θ φ : Fin g → C1 U), IsSeparated q → IsPullback p₁ p₂ q q → (∀ i, IsAffineOpen (U i)) → (∀ c, IsCob U (lc q c φ) → c = 0) → ∀ (J : Type) (V : J → Z.Opens) (k : ∀ i j, C1 (fun α => p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j ⊓ V α)) (e : Fin g → ∀ j α, Γ(Z, p₂ ⁻¹ᵁ U j ⊓ V α)) (e' : Fin g → ∀ i α, Γ(Z, p₁ ⁻¹ᵁ U i ⊓ V α)), ⨆ α, V α = ⊤ → (∀ i j, IsCoc _ (k i j)) → (∀ a j j' α O, O ≤ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α → rsT (e a j' α) O - rsT (e a j α) O = pbT p₂ (φ a j j') O) → (∀ a i i' α O, O ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ V α → rsT (e' a i' α) O - rsT (e' a i α) O = pbT p₁ (φ a i i') O) → (∀ i i' j α β O, O ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j ⊓ V α ⊓ V β → rsT (k i' j α β) O - rsT (k i j α β) O = ∑ a, pbT p₁ (θ a i i') O * (rsT (e a j α) O - rsT (e a j β) O)) → (∀ i j j' α β O, O ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α ⊓ V β → rsT (k i j' α β) O - rsT (k i j α β) O = ∑ a, pbT p₂ (θ a j j') O * (rsT (e' a i α) O - rsT (e' a i β) O)) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob U (θ b - lc q (Θ b) φ) := by
  intro K _ Y Z q p₁ p₂ I _ U g θ φ hq H hU hφ J V k e e' hV hk he he' hk₁ hk₂
  have hA : ∀ i j, IsAffineOpen (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j) := fun i j =>
    isAffineOpen_prod H (hU i) (hU j)
  choose c hc using fun i j => exists_split hV (hA i j) (k i j) (hk i j)
  choose u hu using fun i i' j => exists_compare hV p₁ (T := U i ⊓ U i')
    (W := p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j) (A := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j)
    (B := p₁ ⁻¹ᵁ U i' ⊓ p₂ ⁻¹ᵁ U j) (E := p₂ ⁻¹ᵁ U j)
    (inf_le_inf_right _ (p₁.preimage_mono inf_le_left)) (inf_le_inf_right _ (p₁.preimage_mono inf_le_right))
    inf_le_right inf_le_left (fun a => θ a i i') (fun a => e a j) (k i j) (k i' j) (c i j) (c i' j)
    (hc i j) (hc i' j) (hk₁ i i' j)
  choose v hv using fun i j j' => exists_compare hV p₂ (T := U j ⊓ U j')
    (W := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) (A := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j)
    (B := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j') (E := p₁ ⁻¹ᵁ U i)
    (inf_le_inf_left _ (p₂.preimage_mono inf_le_left)) (inf_le_inf_left _ (p₂.preimage_mono inf_le_right))
    inf_le_left inf_le_right (fun a => θ a j j') (fun a => e' a i) (k i j) (k i j') (c i j) (c i j')
    (hc i j) (hc i j') (hk₂ i j j')
  refine GlobalTheory.T.kunneth_symm_product_affine_covers K Y Z q p₁ p₂ I U g θ φ hq H hU hφ u (fun i j j' => -v i j j') ?_
  intro i i' j j'
  apply ext_cover hV
  intro α
  have hQ1 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j' :=
    inf_le_inf_left _ (p₂.preimage_mono inf_le_right)
  have hQ2 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j :=
    inf_le_inf_left _ (p₂.preimage_mono inf_le_left)
  have hQ3 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ U i' ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') :=
    inf_le_inf_right _ (p₁.preimage_mono inf_le_right)
  have hQ4 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') :=
    inf_le_inf_right _ (p₁.preimage_mono inf_le_left)
  have hu₁ := hu i i' j' α _ (inf_le_inf_right (V α) hQ1)
  have hu₂ := hu i i' j α _ (inf_le_inf_right (V α) hQ2)
  have hv₁ := hv i' j j' α _ (inf_le_inf_right (V α) hQ3)
  have hv₂ := hv i j j' α _ (inf_le_inf_right (V α) hQ4)
  have hφ₂ := fun a => he a j j' α (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α) (inf_le_inf_right (V α) inf_le_right)
  have hφ₁ := fun a => he' a i i' α (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α) (inf_le_inf_right (V α) inf_le_left)
  have hO : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α ≤
      p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') := inf_le_left
  simp only [rsT_add, rsT_sub, rsT_neg, rsT_sum, rsT_mul, rsT_rsT hO hQ1, rsT_rsT hO hQ2,
    rsT_rsT hO hQ3, rsT_rsT hO hQ4, rsT_pbT p₁ hO inf_le_left, rsT_pbT p₂ hO inf_le_right]
  rw [hu₁, hu₂, hv₁, hv₂]
  simp only [← hφ₁, ← hφ₂, mul_sub, sub_mul, Finset.sum_sub_distrib]
  simp only [mul_comm (rsT (e' _ _ α) _)]
  ring

end GlobalTheory.KS
