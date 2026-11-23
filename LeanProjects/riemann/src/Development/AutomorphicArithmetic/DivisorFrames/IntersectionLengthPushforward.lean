import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.PdegEqOfIsDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AutomorphicArithmetic.DivisorFrames.IntersectionNumberGenericRank
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem chi_tower' {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    (F : X.Modules) : chi k F = (Module.finrank k K : ℤ) * chi K F := by
  have hT (n : ℕ) : IsScalarTower k K (coh F n) := by
    refine ⟨fun a b x => ?_⟩
    change cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) (a • b)) x =
      cohOn.action F ⊤ n (algebraMap k Γ(X, ⊤) a) (cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) b) x)
    rw [Algebra.smul_def, map_mul, map_mul, hk]
    rfl
  have e (n : ℕ) : ((-1 : ℤ) ^ n * hdim k F n) = (Module.finrank k K : ℤ) * ((-1 : ℤ) ^ n * hdim K F n) := by
    rw [hdim_def, hdim_def, ← Module.finrank_mul_finrank k K (coh F n)]
    push_cast
    ring
  rw [chi_def, chi_def]
  simp_rw [e]
  exact (mul_finsum _ _).symm

private theorem interNum_tower' {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    {ι : Type} [Fintype ι] (F : X.Modules) (L : ι → LB X) :
    interNum k F L = (Module.finrank k K : ℤ) * interNum K F L := by
  rw [interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [chi_tower' k K hk]
  ring

private theorem range_eq_closure' {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] :
    Set.range i = closure {i (genericPoint Z)} := by
  rw [← Set.image_singleton, i.isClosedEmbedding.closure_image_eq, (genericPoint_spec Z).def, Set.image_univ]

theorem UpperTheory.intersection_length_pushforward :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p] [Finite (ResidueField O)] (B : Vert.Model O) (L : Fin B.relDim → LB B.X), (∀ k, (L k).IsLB) → ∀ (Z : Scheme.{0}) (i : Z ⟶ B.X) [IsClosedImmersion i] [IsIntegral Z], (∀ z : Z, i z ∉ B.gen) → ∀ (G : Z.Modules), GlobalTheory.QCoh.IsFiniteQC G → interLen O ((Scheme.Modules.pushforward i).obj G) L * (resDeg O p : ℤ) = (GlobalTheory.VB.genRank G : ℤ) * pdeg p L (i (genericPoint Z)) := by
  intro O _ _ _ p _ _ _ B L hL Z i _ _ hZ G hG
  let φ : O →+* Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of O)).inv ≫ (i ≫ B.str).appTop).hom
  have eφ : ∀ a, φ a = i.appTop (B.const a) := fun a => by
    rw [Vert.Model.const, Vert.Model.const_eq]
    simp only [φ, Scheme.Hom.comp_appTop]
    rfl
  have hφ : ∀ a ∈ maximalIdeal O, φ a = 0 := fun a ha => by
    rw [← basicOpen_eq_bot_iff]
    by_contra hne
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    have h0 : B.str (i x) = closedPoint O := not_not.1 (mt Vert.Model.mem_gen.2 (hZ x))
    rw [eφ, ← Scheme.preimage_basicOpen_top] at hx
    exact Vert.Model.mem_basicOpen_const.1 hx (h0 ▸ ha)
  let ψ : ResidueField O →+* Γ(Z, ⊤) := Ideal.Quotient.lift _ φ hφ
  letI : Algebra (ZMod p) (ResidueField O) := ZMod.algebra _ p
  letI : Algebra (ResidueField O) Γ(Z, ⊤) := ψ.toAlgebra
  letI : Algebra (ZMod p) Γ(Z, ⊤) := (ψ.comp (algebraMap (ZMod p) (ResidueField O))).toAlgebra
  have h₁ : strHom (ResidueField O) Z ≫ spMap (residue O) = i ≫ B.str := by
    have e : CommRingCat.ofHom (residue O) ≫ CommRingCat.ofHom ψ =
        (Scheme.ΓSpecIso (.of O)).inv ≫ (i ≫ B.str).appTop := rfl
    refine (Category.assoc _ _ _).trans ((congrArg (Z.toSpecΓ ≫ ·)
      ((Spec.map_comp _ _).symm.trans (congrArg Spec.map e))).trans ?_)
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hp : IsProjOver (strHom (ResidueField O) Z) :=
    RegCoverExists.isProjOver_of_comp_spMap (residue O)
      (h₁ ▸ ProjSpace.isProjOver_comp_of_isClosedImmersion i B.isProjOver)
  have hL' : ∀ j, ((L j).pull i).IsLB := fun j => LB.isLB_pull (hL j) i
  have e₁ : interLen O ((Scheme.Modules.pushforward i).obj G) L =
      interNum (ResidueField O) G fun j => (L j).pull i := by
    rw [interLen_eq_multiDiff O _ hL,
      chiLenPic_pushforward O (ResidueField O) residue_surjective i (fun r => (eφ r).symm), multiDiff_comap,
      interNum_eq_multiDiff _ _ hL', Function.comp_apply, map_zero]
    rfl
  have hdim : ∀ {Z' : Scheme.{0}} (i' : Z' ⟶ B.X) [IsClosedImmersion i'] [IsIntegral Z'],
      topologicalKrullDim (closure {i' (genericPoint Z')} : Set B.X) = topologicalKrullDim Z' := fun i' _ _ =>
    topologicalKrullDim_eq_of_isEmbedding i'.isClosedEmbedding.isEmbedding (range_eq_closure' i')
  have hd : topologicalKrullDim Z ≤ (B.relDim : WithBot ℕ∞) := by
    rw [← topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding rfl]
    refine (QCoh.topologicalKrullDim_mono ?_).trans B.dim_special_le
    rintro _ ⟨z, rfl⟩
    exact hZ z
  rw [e₁, UpperTheory.intersection_number_generic_rank (ResidueField O) Z hp _ hd _ hL' G hG, mul_assoc]
  congr 1
  rcases hd.eq_or_lt with h | h
  · rw [UpperTheory.pdeg_eq_of_isDeg p B.X _ L hL _ _ ⟨Z, i, inferInstance, inferInstance, inferInstance, rfl, h, rfl⟩,
      interNum_tower' (ZMod p) (ResidueField O) (fun _ => rfl), mul_comm]
    rfl
  · have h' : ¬ ∃ a, IsDeg p L (i (genericPoint Z)) a := fun ⟨_, Z', i', _, _, _, hz, hd', _⟩ => by
      rw [← hdim i', hz, hdim i] at hd'
      exact h.ne hd'
    rw [pdeg, dif_neg h', interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom (ResidueField O) Z)
      (structureModule Z) hp (by rwa [QCoh.suppDim_structureModule, Fintype.card_fin]) hL', zero_mul]
