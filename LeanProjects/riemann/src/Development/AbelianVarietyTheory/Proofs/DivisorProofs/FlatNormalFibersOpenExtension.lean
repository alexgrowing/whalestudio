import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorEqZeroOfRestrictAffineInf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem rule_eq_on_extend_chart : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (N : ℕ) (M : Scheme.{0}) (sM : M ⟶ Sp (Localization.Away (N : ℤ)))
    (U : Obj F 𝔠 M) (V : M.Opens), Flat sM →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback sM t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback sM t)),
      pullback.fst sM t y ∉ V → 2 ≤ ringKrullDim ((pullback sM t).presheaf.stalk y)) →
    ∀ (W : M.Opens) (hW : IsAffineOpen W),
    (∀ (W' : M.Opens) (hW' : IsAffineOpen W'), W' ≤ W ⊓ V → ∀ (Y' : Obj F 𝔠 (Sp Γ(M, W')))
      (φ' : Y'.A.left ⟶ U.A.left), Y'.IsPullBy U hW'.fromSpec φ' → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : Γ(M, W') →+* B) (Y'' : Obj F 𝔠 (Sp B)) (φ'' : Y''.A.left ⟶ Y'.A.left),
    Y''.IsPullBy Y' (spMap σ) φ'' → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y''.DetGen), s.val B Y'' h δ = t.val B Y'' h δ)) →
    ∀ (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left), Y.IsPullBy U hW.fromSpec φ →
    ∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : Γ(M, W) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W)).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] Γ(M, W))) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ := by
  intro F _ _ 𝔠 R₀ _ k s t N M sM U V hflat hnorm hcodim W hW hagree Y φ hY YC ψ hYC h δ
  set d := s.val _ YC h δ - t.val _ YC h δ with hd
  suffices hd0 : TensorProduct.comm ℤ R₀ Γ(M, W) d = 0 by
    have : d = 0 := by simpa using congrArg (TensorProduct.comm ℤ R₀ Γ(M, W)).symm hd0
    exact sub_eq_zero.mp this
  refine rTensor_eq_zero_of_restrict_affine_inf N M sM V hflat hnorm hcodim W hW R₀ _ ?_
  intro W' hW' hle
  let ρ : Γ(M, W) →+* Γ(M, W') := (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom
  let τ' : R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W') :=
    Algebra.TensorProduct.map (AlgHom.id R₀ R₀) ρ.toIntAlgHom
  have hswap : ∀ x : R₀ ⊗[ℤ] Γ(M, W), LinearMap.rTensor R₀ ρ.toAddMonoidHom.toIntLinearMap
      (TensorProduct.comm ℤ R₀ Γ(M, W) x) = TensorProduct.comm ℤ R₀ Γ(M, W') (τ' x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [τ']
    | add x y hx hy => simp only [map_add, hx, hy]
  change LinearMap.rTensor R₀ ρ.toAddMonoidHom.toIntLinearMap _ = 0
  rw [hswap]
  suffices hτ : τ' d = 0 by rw [hτ, map_zero]

  let incR : Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W) :=
    (Algebra.TensorProduct.includeRight : Γ(M, W) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W)).toRingHom
  let incR' : Γ(M, W') →+* R₀ ⊗[ℤ] Γ(M, W') :=
    (Algebra.TensorProduct.includeRight : Γ(M, W') →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W')).toRingHom
  obtain ⟨Y', φ', hY'⟩ := Obj.exists_isPullBy U hW'.fromSpec
  obtain ⟨YC', ψ', hYC'⟩ := Obj.exists_isPullBy YC (spMap (τ' : R₀ ⊗[ℤ] Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W')))
  have hcomm : (τ' : R₀ ⊗[ℤ] Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W')).comp incR = incR'.comp ρ := by
    ext x; simp [τ', incR, incR']
  have hbase : spMap (τ' : R₀ ⊗[ℤ] Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W')) ≫ spMap incR ≫ hW.fromSpec =
      spMap incR' ≫ hW'.fromSpec := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomm, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc]
    congr 1
    exact hW.map_fromSpec hW' (homOfLE (hle.trans inf_le_left)).op
  have hall := hYC'.comp (hYC.comp hY)
  rw [hbase] at hall
  obtain ⟨ψ'', hψ'', -⟩ := hall.cancel hY'
  obtain ⟨δ', hδ', -⟩ := hYC'.existsUnique_detGen _ δ
  have h' : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] Γ(M, W')) := map_natCast τ' 6 ▸ h.map τ'
  have heq := hagree W' hW' hle Y' φ' hY' (R₀ ⊗[ℤ] Γ(M, W')) incR' YC' ψ'' hψ'' h' δ'
  have hs := s.baseChange _ _ τ' YC h YC' h' ψ' δ δ' hYC' hδ'
  have ht := t.baseChange _ _ τ' YC h YC' h' ψ' δ δ' hYC' hδ'
  rw [hd, map_sub, ← hs, ← ht, heq, sub_self]

end GlobalTheory.RealMult
