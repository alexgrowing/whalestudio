import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KappaCoc

theorem resG_resG' (Z : Scheme.{0}) {U V O : Z.Opens} (h : V ≤ U) (h' : O ≤ V) (f : Γ(Z, U)) :
    resG Z h' (resG Z h f) = resG Z (h'.trans h) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem dlog_cocycle {Z : Scheme.{0}} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hd : IsField W₀ d)
    (L : LB Z) (hL : L.IsLB) {a b c : L.ι} {W₁ W₂ W₃ : Z.Opens} (h₁ : W₁ ≤ L.U a) (h₂ : W₂ ≤ L.U b)
    (h₃ : W₃ ≤ L.U c) (hW₁ : W₁ ≤ W₀) (hW₂ : W₂ ≤ W₀) :
    resG Z (inf_le_left : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₂) (d (W₁ ⊓ W₂) (resG Z (inf_le_inf h₁ h₂) (L.g a b).val) *
        resG Z (inf_le_inf h₁ h₂) (L.g a b)⁻¹.val) +
      resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂ ⊓ W₃)
        (d (W₂ ⊓ W₃) (resG Z (inf_le_inf h₂ h₃) (L.g b c).val) * resG Z (inf_le_inf h₂ h₃) (L.g b c)⁻¹.val) =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₃)
        (d (W₁ ⊓ W₃) (resG Z (inf_le_inf h₁ h₃) (L.g a c).val) * resG Z (inf_le_inf h₁ h₃) (L.g a c)⁻¹.val) := by
  have l₁ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₂ := inf_le_left
  have l₂ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂ ⊓ W₃ := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₃ := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hV : W₁ ⊓ W₂ ⊓ W₃ ≤ W₀ := inf_le_left.trans (inf_le_left.trans hW₁)
  have lU : W₁ ⊓ W₂ ⊓ W₃ ≤ L.U a ⊓ L.U b ⊓ L.U c := inf_le_inf (inf_le_inf h₁ h₂) h₃
  have comm : ∀ {O : Z.Opens} (h : W₁ ⊓ W₂ ⊓ W₃ ≤ O), O ≤ W₀ → ∀ x : Γ(Z, O),
      resG Z h (d O x) = d _ (resG Z h x) := fun h hO x => (hd.2.2 _ _ h hO x).symm
  rw [map_mul, map_mul, map_mul, comm l₁ (inf_le_left.trans hW₁), comm l₂ (inf_le_left.trans hW₂),
    comm l₃ (inf_le_left.trans hW₁), resG_resG', resG_resG', resG_resG', resG_resG', resG_resG', resG_resG']
  have uv : ∀ {p q : L.ι} (h : W₁ ⊓ W₂ ⊓ W₃ ≤ L.U p ⊓ L.U q),
      resG Z h (L.g p q).val * resG Z h (L.g p q)⁻¹.val = 1 := fun h => by
    rw [← map_mul, Units.mul_inv, map_one]
  have co := congrArg (fun u : Γ(Z, L.U a ⊓ L.U b ⊓ L.U c)ˣ => resG Z lU u.val) (hL.cocycle a b c)
  simp only [Units.val_mul, map_mul] at co
  change resG Z lU (resG Z _ (L.g a b).val) * resG Z lU (resG Z _ (L.g b c).val) =
    resG Z lU (resG Z _ (L.g a c).val) at co
  rw [resG_resG', resG_resG', resG_resG'] at co
  have e := hd.2.1 _ hV (resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b).val)
    (resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c).val)
  rw [co] at e
  have ua := uv (l₁.trans (inf_le_inf h₁ h₂))
  have ub := uv (l₂.trans (inf_le_inf h₂ h₃))
  have uc := uv (l₃.trans (inf_le_inf h₁ h₃))
  set A := resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b).val
  set B := resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c).val
  set C := resG Z (l₃.trans (inf_le_inf h₁ h₃)) (L.g a c).val
  set A' := resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b)⁻¹.val
  set B' := resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c)⁻¹.val
  set C' := resG Z (l₃.trans (inf_le_inf h₁ h₃)) (L.g a c)⁻¹.val
  set dA := d _ A
  set dB := d _ B
  set dC := d _ C
  linear_combination (-C') * e - (dA * A' * C' + dB * B' * C') * co + dA * B * C' * ua + dB * A * C' * ub -
    (dA * A' + dB * B') * uc

end GlobalTheory.KappaCoc

theorem GlobalTheory.KappaCoc.kappa_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)), ∀ (b : Fin n) (i i' i'' : J), resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (δ b (W i' ⊓ W i'') (resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i'')).val) * resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i''))⁻¹.val) = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (δ b (W i ⊓ W i'') (resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i'')).val) * resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i''))⁻¹.val) := by
  intro E _ _ _ H X t U n δ hδ J W j _ _ hWU hj b i i' i''
  exact GlobalTheory.KappaCoc.dlog_cocycle (hδ b) t.PP.L t.PP.isLB (hj i) (hj i') (hj i'') (hWU i) (hWU i')
