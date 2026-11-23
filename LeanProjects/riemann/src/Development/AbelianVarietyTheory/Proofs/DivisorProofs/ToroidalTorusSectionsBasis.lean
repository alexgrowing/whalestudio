import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfPowEqOne

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.HalfGeo
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilEquivar

theorem prod_zpow_eq {U J : Type} [CommGroup U] [Fintype J] (ζ : U) (f : J → ℤ) :
    ∏ i, ζ ^ f i = ζ ^ ∑ i, f i := by
  have s := map_prod (zpowersHom U ζ) (fun i => Multiplicative.ofAdd (f i)) Finset.univ
  rw [← ofAdd_sum] at s
  exact s.symm

theorem chars_transform {G T U : Type} [CommGroup G] [CommGroup T] [CommGroup U] (e : T →* G)
    (hinj : Function.Injective e) (A : G →* G) {N : ℕ} (σ : Fin N → T) (ζ : U) (B M M' : Matrix (Fin N) (Fin N) ℤ)
    (hM : M.transpose * B = B * M') (hA : ∀ m, A (e (σ m)) = ∏ m', e (σ m') ^ M m' m) (χ : Fin N → (T →* U))
    (hχ : ∀ m i, χ m (σ i) = ζ ^ B i m) (k k' : T) (n : Fin N → ℕ) (hk : e k = ∏ i, e (σ i) ^ n i)
    (hk' : e k' = A (e k)) (m : Fin N) : χ m k' = ∏ m', χ m' k ^ M' m' m := by
  have h1 : k = ∏ i, σ i ^ n i := hinj (by simp only [hk, map_prod, map_pow])
  have h2 : k' = ∏ i, (∏ j, σ j ^ M j i) ^ n i :=
    hinj (by simp only [hk', hk, map_prod, map_pow, map_zpow, hA])
  rw [h2, h1]
  simp only [map_prod, map_pow, map_zpow, hχ, ← zpow_natCast, ← zpow_mul, prod_zpow_eq]
  congr 1
  have h3 : ∀ i, ∑ j, B j m * M j i = ∑ j, B i j * M' j m := fun i => by
    have := congrFun (congrFun hM i) m
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [h3, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem equivar_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)
    (K : Type) [Field K] (ξ₀ : Sp K ⟶ Xo.XF c) (ξ : Sp K ⟶ Z.X), ξ₀ ≫ Z.j = ξ → ∀ q : ℕ, q ≠ 0 →
    ∀ (N : ℕ) (b : Module.Basis (Fin N) ℤ Dw.La) (s : Fin N → (Over.mk ξ₀ ⟶ Z.oF.t.G)) (ζ : Kˣ),
    IsGram Z.oF.t q s ζ (GlobalTheory.EqHalf.gram Dw b) → (∀ a : Over.mk ξ₀ ⟶ Z.oF.t.G, a ^ q = 1 → ∃ n : Fin N → ℕ, a = ∏ m, s m ^ n m) →
    (∀ (α : 𝓞 E) (m : Fin N), s m ≫ Z.oF.t.act.act α = ∏ m', s m' ^ GlobalTheory.EqHalf.latMat Dw b α m' m) →
    ∀ χ : Fin N → (TorsK Z.t ξ q →* Kˣ), (∀ m, IsWeilHom Z.oF.t Z.m.φ (s m) (χ m)) →
    ∀ (α : 𝓞 E) (k k' : TorsK Z.t ξ q), k'.1 = k.1 ≫ Z.t.act.act α →
      ∀ m, χ m k' = ∏ m', χ m' k ^ GlobalTheory.EqHalf.chiAct Dw b α m m' := by
  intro E _ _ _ H Dw l Xo c O _ β Z K _ ξ₀ ξ hξ q hq N b s ζ hG hgen hact χ hχ α k k' hk m
  subst hξ
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.WeilTorsChar.exists_mulEquiv_points _ Z.t.G Z.oF.t.G Z.m.φ Z.m.cart (Over.mk ξ₀)
  let P := GlobalTheory.Obj.toPolAV Z.oF
  let e : TorsK Z.t (ξ₀ ≫ Z.j) q →* (Over.mk ξ₀ ⟶ Z.oF.t.G) :=
    Φ.symm.toMonoidHom.comp (TorsK Z.t (ξ₀ ≫ Z.j) q).subtype
  have he : ∀ t, e t = Φ.symm t.1 := fun _ => rfl
  let σ : Fin N → TorsK Z.t (ξ₀ ≫ Z.j) q := fun i =>
    ⟨Φ (s i), (map_pow Φ _ _).symm.trans ((congrArg Φ (hG.1 i)).trans (map_one _))⟩
  have hσ : ∀ i, e (σ i) = s i := fun i => Φ.symm_apply_apply _
  haveI := Z.oF.t.act.hom α
  let A : (Over.mk ξ₀ ⟶ Z.oF.t.G) →* (Over.mk ξ₀ ⟶ Z.oF.t.G) := IsMonHom.monoidHom (Z.oF.t.act.act α) _
  have hA : ∀ x, A x = x ≫ Z.oF.t.act.act α := fun _ => rfl
  have hek : e k ^ q = 1 := by
    have ht : k.1 ^ q = 1 := k.2
    rw [he]
    exact (map_pow Φ.symm _ _).symm.trans ((congrArg Φ.symm ht).trans (map_one _))
  obtain ⟨n, hn⟩ := hgen (e k) hek
  refine chars_transform e (Φ.symm.injective.comp Subtype.val_injective) A σ ζ (GlobalTheory.EqHalf.gram Dw b)
    (GlobalTheory.EqHalf.latMat Dw b α) (GlobalTheory.EqHalf.latMat Dw b (H.bar α)) (GlobalTheory.EqHalf.latMat_transpose_mul_gram Dw b α)
    (fun i => ?_) χ (fun j i => ?_) k k' n ?_ ?_ m
  · simp only [hσ, hA]
    exact hact α i
  · exact GlobalTheory.Ex.Specialise.unitOn_bijective.1
      ((GlobalTheory.LevelCompare.weil_existsUnique P q (s i) (s j) (hG.1 i) (hG.1 j)).unique
        (hχ j (σ i) (s i) (hΦ (s i)).symm) (hG.2 i j))
  · simp only [hσ]
    exact hn
  · rw [hA, he k']
    refine (Φ.symm_apply_eq).2 (Over.OverMorphism.ext ?_)
    have h1 : (e k).left ≫ Z.m.φ = k.1.left := by
      rw [← hΦ (e k), he]
      exact congrArg (fun u => u.left) (Φ.apply_symm_apply k.1)
    refine Eq.trans ?_ (hΦ _).symm
    rw [hk, Over.comp_left, Over.comp_left, Category.assoc, ← h1, Category.assoc]
    exact congrArg _ (Z.m.act α).symm

end GlobalTheory.WeilEquivar
