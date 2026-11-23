import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
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

namespace GlobalTheory.LogKSDiv.GenUniq

open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)

attribute [local instance] Over.cartesianMonoidalCategory

theorem dualMap_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (Formalism.L2.Pj.dualMap f) := by
  intro a b h
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp only [Formalism.L2.Pj.dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add] at h1 h2
  exact TrivSqZeroExt.ext (hf h1) (hf h2)

theorem exists_common_denom {A K : Type} [CommRing A] [Field K] (ρ : A →+* K)
    (hfr : ∀ x : K, ∃ a b : A, ρ b ≠ 0 ∧ x * ρ b = ρ a) {κ : Type} [Fintype κ] (c : κ → K) :
    ∃ (b : A) (a : κ → A), ρ b ≠ 0 ∧ ∀ i, ρ b * c i = ρ (a i) := by
  classical
  choose a b hb hab using hfr
  refine ⟨∏ i, b (c i), fun i => a (c i) * ∏ j ∈ Finset.univ.erase i, b (c j), ?_, fun i => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hb _
  · rw [← Finset.mul_prod_erase Finset.univ (fun j => b (c j)) (Finset.mem_univ i), map_mul, map_mul, ← hab]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def bcEps {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) :
    tEpsG (spMap ρ ≫ x) ⟶ tEpsG x :=
  Over.homMk (spMap (Formalism.L2.Pj.dualMap ρ)) (by
    show spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (algebraMap A (DualNumber A)) ≫ x =
      spMap (algebraMap K (DualNumber K)) ≫ spMap ρ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg])

theorem bcEps_smT {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) (a : A)
    (v : tEpsG x ⟶ t.G) :
    bcEps ρ x ≫ smT x a v = smT (spMap ρ ≫ x) (ρ a) (bcEps ρ x ≫ v) := by
  apply Over.OverMorphism.ext
  show spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (epsMul a) ≫ v.left =
    spMap (epsMul (ρ a)) ≫ spMap (Formalism.L2.Pj.dualMap ρ) ≫ v.left
  rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_epsMul]

theorem bcEps_combT {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) {n : ℕ}
    (v : Fin n → (tEpsG x ⟶ t.G)) (a : Fin n → A) :
    bcEps ρ x ≫ combT x v a = combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ v i) (fun i => ρ (a i)) := by
  let f : (tEpsG x ⟶ t.G) →* (tEpsG (spMap ρ ≫ x) ⟶ t.G) :=
    { toFun := fun u => bcEps ρ x ≫ u
      map_one' := MonObj.comp_one _
      map_mul' := fun u w => MonObj.comp_mul _ _ _ }
  have h := map_prod f (fun j => smT x (a j) (v j)) Finset.univ
  refine h.trans ?_
  exact Finset.prod_congr rfl fun i _ => bcEps_smT t ρ x (a i) (v i)

theorem coeff_unique {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hinj : Function.Injective ρ)
    (hfr : ∀ x : K, ∃ a b : A, ρ b ≠ 0 ∧ x * ρ b = ρ a) (x : Sp A ⟶ X) {n : ℕ}
    (v : Fin n → (Sp (DualNumber A) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf : Fin n → A, IsCombAtG t x v cf w)
    (cf cf' : Fin n → K) (w : Sp (DualNumber K) ⟶ t.G.left)
    (h : IsCombAtG t (spMap ρ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap ρ) ≫ v i) cf w)
    (h' : IsCombAtG t (spMap ρ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap ρ) ≫ v i) cf' w) : cf = cf' := by
  let V : Fin n → (tEpsG x ⟶ t.G) := fun i => ovT (hv i)
  have e := (isCombAtG_iff t (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf w).1 h
  have e' := (isCombAtG_iff t (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf' w).1 h'
  have hc : combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf =
      combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf' := Over.OverMorphism.ext (e.trans e'.symm)
  obtain ⟨b, a, hb0, ha⟩ := exists_common_denom ρ hfr (Sum.elim cf cf')
  have hs := congrArg (smT (spMap ρ ≫ x) (ρ b)) hc
  rw [smT_combT, smT_combT] at hs
  have a1 : (fun j => ρ b * cf j) = fun j => ρ (a (Sum.inl j)) := funext fun j => ha (Sum.inl j)
  have a2 : (fun j => ρ b * cf' j) = fun j => ρ (a (Sum.inr j)) := funext fun j => ha (Sum.inr j)
  rw [a1, a2, ← bcEps_combT, ← bcEps_combT] at hs
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hdom : IsSchemeTheoreticallyDominant (spMap (Formalism.L2.Pj.dualMap ρ)) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom _) (dualMap_injective ρ hinj)
  have hA : (combT x V fun j => a (Sum.inl j)).left = (combT x V fun j => a (Sum.inr j)).left :=
    GlobalTheory.ExtUnique.hom_ext_of_dominant t.G.hom
      ((Over.w (combT x V fun j => a (Sum.inl j))).trans (Over.w (combT x V fun j => a (Sum.inr j))).symm)
      (spMap (Formalism.L2.Pj.dualMap ρ)) (congrArg (fun φ => φ.left) hs)
  have ht : IsTanAtG t x (combT x V fun j => a (Sum.inl j)).left :=
    isTanAtG_of _ (combT_tan x V (fun j => smT_zero_ovT (hv j)) _)
  have haa : (fun j => a (Sum.inl j)) = fun j => a (Sum.inr j) :=
    (hb _ ht).unique ((isCombAtG_iff t x V _ _).2 rfl) ((isCombAtG_iff t x V _ _).2 hA.symm)
  funext j
  apply mul_left_cancel₀ hb0
  rw [congrFun a1 j, congrFun a2 j, congrFun haa j]

end GlobalTheory.LogKSDiv.GenUniq

namespace GlobalTheory.LogKSDiv

theorem generic_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (W : X.affineOpens) (K : Type) [Field K] (ρW : Γ(X, W.1) →+* K), Function.Injective ρW → (∀ x : K, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, W.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart W) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) v cf w) → ∀ (cf cf' : Fin n → K) (w : Sp (DualNumber K) ⟶ t.G.left), IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap ρW) ≫ v i) cf w → IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap ρW) ≫ v i) cf' w → cf = cf' :=
  fun _ _ _ _ _ _ t W _ _ ρW hinj hfr _ v hv hb cf cf' w h h' =>
    GenUniq.coeff_unique t ρW hinj hfr (GlobalTheory.LogKS.chart W) v hv hb cf cf' w h h'

end GlobalTheory.LogKSDiv
