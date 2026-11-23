import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionLinCombFiberProductSeparatedStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_sum_tmul_linearIndependent {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (t : TensorProduct F M N) :
    ∃ (m : ℕ) (e : Fin m → M) (c : Fin m → N), LinearIndependent F e ∧ t = ∑ k, TensorProduct.tmul F (e k) (c k) := by
  classical
  let B := Module.Basis.ofVectorSpace F M
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left B t
  let σ := c.support.equivFin.symm
  refine ⟨_, fun k => B (σ k), fun k => c (σ k), ?_, ?_⟩
  · exact B.linearIndependent.comp (fun k => (σ k).val) (Subtype.val_injective.comp σ.injective)
  · rw [← hc, Finsupp.sum, ← Finset.sum_coe_sort]
    exact (Equiv.sum_comp σ (fun i => TensorProduct.tmul F (B i) (c i))).symm

section
variable {F : Type} [CommRing F] {Z Y T : Scheme.{0}} {L : LB Z} (p : Y ⟶ Spec (CommRingCat.of F))
  {K : Type} [Fintype K] (φ : K → (Y ⟶ Z)) (ε : K → ℤ)

noncomputable def svalAddHom (r : T ⟶ Y) (z : T) {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) :
    SecMod p (LB.LinComb L φ ε) →+ T.presheaf.stalk z :=
  AddMonoidHom.mk' (fun s => sval s.sec r z J) (fun _ _ => gs_add r z _ (hJ.mem φ r) _ _)

theorem svalAddHom_smul (r : T ⟶ Y) (z : T) {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) (c : F)
    (s : SecMod p (LB.LinComb L φ ε)) :
    svalAddHom p φ ε r z hJ (c • s) =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * svalAddHom p φ ε r z hJ s :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _)
    ((gs_res r z le_top (hJ.mem φ r) _).trans (gs_pull r p z ⊤ trivial _)))

noncomputable def secCompAddHom (N : LB Y) (j : N.ι) : SecMod p N →+ Γ(Y, N.U j) :=
  AddMonoidHom.mk' (fun s => s.sec.f j) (fun _ _ => rfl)

end

theorem tensor_sections_eq_zero_iff : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec (CommRingCat.of F)) (p₂ : Y₂ ⟶ Spec (CommRingCat.of F)) [QuasiCompact p₁] [IsSeparated p₁] [QuasiCompact p₂] [IsSeparated p₂] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁ ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂ ⟶ Z)) (ε₂ : K₂ → ℤ) (n : ℕ) (a : Fin n → SecMod p₁ (LB.LinComb L φ₁ ε₁)) (b : Fin n → SecMod p₂ (LB.LinComb L φ₂ ε₂)), (∑ i, TensorProduct.tmul F (a i) (b i) = 0) ↔ ∀ (T : Scheme.{0}) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂), r₁ ≫ p₁ = r₂ ≫ p₂ → ∀ (z : T) (J), Good L z J → ∑ i, sval (a i).sec r₁ z J * sval (b i).sec r₂ z J = 0 := by
  intro F _ Z L hL Y₁ Y₂ p₁ p₂ _ _ _ _ K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂ n a b
  have key : ∀ (T : Scheme.{0}) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂), r₁ ≫ p₁ = r₂ ≫ p₂ → ∀ (z : T) (J), Good L z J →
      ∃ Φ : TensorProduct F (SecMod p₁ (LB.LinComb L φ₁ ε₁)) (SecMod p₂ (LB.LinComb L φ₂ ε₂)) →+ T.presheaf.stalk z,
        ∀ s t, Φ (TensorProduct.tmul F s t) = sval s.sec r₁ z J * sval t.sec r₂ z J := by
    intro T r₁ r₂ h z J hJ
    refine ⟨TensorProduct.liftAddHom
      ((AddMonoidHom.mul.compl₂ (svalAddHom p₂ φ₂ ε₂ r₂ z hJ)).comp (svalAddHom p₁ φ₁ ε₁ r₁ z hJ)) ?_, fun s t => rfl⟩
    intro c s t
    change svalAddHom p₁ φ₁ ε₁ r₁ z hJ (c • s) * svalAddHom p₂ φ₂ ε₂ r₂ z hJ t =
      svalAddHom p₁ φ₁ ε₁ r₁ z hJ s * svalAddHom p₂ φ₂ ε₂ r₂ z hJ (c • t)
    rw [svalAddHom_smul, svalAddHom_smul, h]
    ring
  constructor
  · intro h0 T r₁ r₂ h z J hJ
    obtain ⟨Φ, hΦ⟩ := key T r₁ r₂ h z J hJ
    have := congrArg Φ h0
    rwa [map_sum, map_zero, Finset.sum_congr rfl (fun i _ => hΦ (a i) (b i))] at this
  · intro H
    obtain ⟨m, e, c, he, ht⟩ := exists_sum_tmul_linearIndependent (∑ i, TensorProduct.tmul F (a i) (b i))
    have : QuasiCompact (Over.mk p₁).hom := ‹QuasiCompact p₁›
    have : IsSeparated (Over.mk p₁).hom := ‹IsSeparated p₁›
    have : QuasiCompact (Over.mk p₂).hom := ‹QuasiCompact p₂›
    have : IsSeparated (Over.mk p₂).hom := ‹IsSeparated p₂›
    have hc := (GlobalTheory.T.section_lin_comb_fiber_product_separated F Z L hL (Over.mk p₁) (Over.mk p₂) K₁ K₂ φ₁ ε₁ φ₂ ε₂).2 m
      (fun k => (e k).sec) (fun k => (c k).sec) (fun d hd => by
        have h1 : ∑ k, d k • e k = 0 := DVR.SecOps.sec_ext fun j =>
          (map_sum (secCompAddHom p₁ _ j) _ _).trans (hd j)
        exact funext (Fintype.linearIndependent_iff.1 he d h1)) (fun z J hJ => by
        have w : (fst (Over.mk p₁) (Over.mk p₂)).left ≫ p₁ = (snd (Over.mk p₁) (Over.mk p₂)).left ≫ p₂ :=
          (Over.w (fst (Over.mk p₁) (Over.mk p₂))).trans (Over.w (snd (Over.mk p₁) (Over.mk p₂))).symm
        obtain ⟨Φ, hΦ⟩ := key _ _ _ w z J hJ
        have h2 := congrArg Φ ht
        rw [map_sum, map_sum, Finset.sum_congr rfl (fun i _ => hΦ (a i) (b i)),
          Finset.sum_congr rfl (fun i _ => hΦ (e i) (c i))] at h2
        exact h2.symm.trans (H _ _ _ w z J hJ))
    rw [ht]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : c k = 0 := DVR.SecOps.sec_ext fun j => hc k j
    rw [this, TensorProduct.tmul_zero]

end GlobalTheory
