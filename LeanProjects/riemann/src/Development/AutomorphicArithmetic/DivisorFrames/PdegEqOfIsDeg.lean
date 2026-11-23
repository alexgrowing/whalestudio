import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem interNum_eq_of_range_eq (p : ℕ) [Fact p.Prime] {X Z Z' : Scheme.{0}} {d : ℕ} (N : Fin d → LB X)
    (hN : ∀ j, (N j).IsLB) [Algebra (ZMod p) Γ(Z, ⊤)] [Algebra (ZMod p) Γ(Z', ⊤)] (i : Z ⟶ X) (i' : Z' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsReduced Z] [IsReduced Z'] (h : Set.range i = Set.range i') :
    interNum (ZMod p) (structureModule Z') (fun j => (N j).pull i') =
      interNum (ZMod p) (structureModule Z) (fun j => (N j).pull i) := by
  have e : i'.ker = i.ker := by
    rw [← InterModel.radical_ker i, ← InterModel.radical_ker i', ← Scheme.IdealSheafData.vanishingIdeal_support,
      ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker, h]
  let j : Z ⟶ Z' := IsClosedImmersion.lift i' i e.le
  have hj : j ≫ i' = i := IsClosedImmersion.lift_fac _ _ _
  have : IsClosedImmersion (j ≫ i') := hj ▸ inferInstance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j i'
  have hr : Set.range j = (⊤ : TopologicalSpace.Closeds Z') := Set.eq_univ_of_forall fun y => by
    obtain ⟨x, hx⟩ := h.ge ⟨y, rfl⟩
    exact ⟨x, i'.isClosedEmbedding.injective (by rw [← hx, ← hj]; rfl)⟩
  have hL' : ∀ a, ((N a).pull i').IsLB := fun a => LB.isLB_pull (hN a) i'
  rw [← interNumOn_id, ← InterModel.interNumRed_eq_interNumOn (ZMod p) (𝟙 _) ⊤ (by simp),
    InterModel.interNumRed_eq_interNumOn (ZMod p) j ⊤ hr, interNumOn_eq_interNum_pull (fun r =>
    RingHom.congr_fun (RingHom.ext_zmod (j.appTop.hom.comp (algebraMap _ _)) (algebraMap _ _)) r) hL']
  refine interNum_congr_cls _ _ (fun a => LB.isLB_pull (hL' a) j) (fun a => LB.isLB_pull (hN a) i) fun a => ?_
  exact ((CechPic.pull_comp j i' (cls (N a) (hN a))).symm.trans (by rw [hj])).trans (CechPic.cls_pull (hN a) i _).symm

private theorem range_eq_closure {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] :
    Set.range i = closure {i (genericPoint Z)} := by
  rw [← Set.image_singleton, i.isClosedEmbedding.closure_image_eq, (genericPoint_spec Z).def, Set.image_univ]

theorem UpperTheory.pdeg_eq_of_isDeg :
    ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (d : ℕ) (N : Fin d → LB X), (∀ j, (N j).IsLB) → ∀ (z : X) (a : ℤ), IsDeg p N z a → pdeg p N z = a := by
  intro p _ X d N hN z a ha
  have hex : ∃ a, IsDeg p N z a := ⟨a, ha⟩
  rw [pdeg, dif_pos hex]
  obtain ⟨Z', i', _, _, _, hz', -, e'⟩ := hex.choose_spec
  obtain ⟨Z, i, _, _, _, hz, -, e⟩ := ha
  rw [e', e]
  exact interNum_eq_of_range_eq p N hN i i' (by rw [range_eq_closure, range_eq_closure, hz, hz'])
