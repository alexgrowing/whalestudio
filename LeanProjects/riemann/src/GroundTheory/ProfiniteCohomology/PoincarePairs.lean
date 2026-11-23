import Mathlib
import GroundTheory.ProfiniteCohomology.PoincarePairs.Devissage
import GroundTheory.ProfiniteCohomology.PoincarePairs.MackeyCup
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section Natural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

theorem LeibnizPairing.homologyMap_homology {M N P P' : CochainComplex (ModuleCat.{u} k) ℕ}
    (μ₁ : LeibnizPairing M N P) (μ₂ : LeibnizPairing M N P') (ψ : P ⟶ P')
    (hψ : ∀ {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : N.X s),
      (ψ.f n).hom (μ₁.μ h x y) = μ₂.μ h x y)
    {r s n : ℕ} (h : r + s = n) (x : M.homology r) (y : N.homology s) :
    (HomologicalComplex.homologyMap ψ n).hom (μ₁.homology h x y) = μ₂.homology h x y := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective M r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective N s y
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply,
    LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles]
  exact hψ h _ _

variable {A B C C' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  [IsDiscreteRep C']

theorem compactCohomologyResMap_compactCupRes (μ : A ⊗ B ⟶ C) (ψ : C ⟶ C') {r s n : ℕ}
    (h : r + s = n) (y : compactCohomologyRes φ A r) (x : cohomology B s) :
    (compactCohomologyResMap φ ψ n).hom (compactCupRes φ μ h y x) =
      compactCupRes φ (μ ≫ ψ) h y x := by
  rw [compactCupRes_eq_homology, compactCupRes_eq_homology]
  refine LeibnizPairing.homologyMap_homology _ _ _ (fun {r s n} h p z => ?_) h y x
  revert p
  intro (p : (cochainsComplex A).X r ×
    shiftNegOneX (piComplex fun v => cochainsComplex (Rep.res (φ v).toMonoidHom A)) r)
  refine Prod.ext rfl ?_
  cases r with
  | zero =>
    exact map_zero (shiftNegOneMapF (piMap fun v => cochainsMap
      ((Rep.resFunctor (φ v).toMonoidHom).map ψ)) n).hom
  | succ r =>
    cases n with
    | zero => rfl
    | succ n => rfl

theorem bijective_compactCohomologyResMap_of_comp_eq_id (f : A ⟶ B) (g : B ⟶ A)
    (hfg : f ≫ g = 𝟙 A) (hgf : g ≫ f = 𝟙 B) (m : ℕ) :
    Function.Bijective (compactCohomologyResMap φ f m) := by
  refine Function.bijective_iff_has_inverse.2 ⟨compactCohomologyResMap φ g m, fun x => ?_,
    fun y => ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← compactCohomologyResMap_comp, hfg,
      compactCohomologyResMap_id]
    rfl
  · rw [← ConcreteCategory.comp_apply, ← compactCohomologyResMap_comp, hgf,
      compactCohomologyResMap_id]
    rfl

end Natural

section Bridge

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

theorem compactCores_mackeyCompactCohomologyIso {k : Type u} [CommRing k] (V : OpenSubgroup G)
    (A : Rep.{u} k G) [IsDiscreteRep A] (m : ℕ)
    (w : compactCohomologyRes φ (Rep.coind (V : Subgroup G).subtype (Rep.res (V : Subgroup G).subtype A)) m) :
    (compactCores φ V A m).hom
        ((mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype A) m).hom.hom w) =
      (compactCohomologyResMap φ (coindTrace (V : Subgroup G) A) m).hom w := by
  change (compactCohomologyResMap φ (coindTrace (V : Subgroup G) A) m).hom
    ((mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype A) m).inv.hom
      ((mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype A) m).hom.hom w)) = _
  rw [hom_apply_hom_apply_of_comp_eq
    (mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype A) m).hom_inv_id w]
  rfl

variable {n : ℕ} [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D]

omit [NeZero n] [IsDiscreteRep D] in

theorem tensorHom_coindDualHom_dualEvalPairing (U : OpenSubgroup G) :
    (coindDualHom (U : Subgroup G) (ULift.{u} (ZMod n)) D ⊗ₘ
        𝟙 (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n))) ≫
      dualEvalPairing D (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)) =
    coindPairing (U : Subgroup G)
        (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{u} (U : Subgroup G) n)) ≫
      coindTrace (U : Subgroup G) D := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul μ f => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

omit [NeZero n] in

theorem tensorHom_zmodDualIso_zmodMulPairingRight {K : Type u} [Group K]
    (E : Rep.{u} (ULift.{u} ℤ) K) (hE : ∀ d : E, n • d = 0) :
    ((zmodDualIso n E hE).hom ⊗ₘ 𝟙 (zmodRep.{u} K n)) ≫ zmodMulPairingRight n E hE =
      dualEvalPairing E (zmodRep.{u} K n) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul ν a =>
    obtain ⟨a⟩ := a
    change zmodMulAddHom n hE a (ν (ULift.up 1)) = ν (ULift.up a)
    rw [zmodMulAddHom_apply]
    exact (dualRep_zmodRep_apply n E ν a).symm
  | add z z' hz hz' => simp only [map_add, hz, hz']

variable {D}

def coindDualCompactMap (hD : ∀ d : D, n • d = 0) (U : OpenSubgroup G) (s : ℕ) :
    compactCohomologyRes φ
        (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n))) s →+
      compactCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) s :=
  ((compactCohomologyResMap (mackeyFamily U φ)
      (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom s).hom.comp
    (((mackeyCompactCohomologyIso U φ
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{u} (U : Subgroup G) n)) s).hom.hom).comp
      (compactCohomologyResMap φ (coindDualInv (U : Subgroup G) (ULift.{u} (ZMod n)) D) s).hom)).toAddMonoidHom

theorem bijective_coindDualCompactMap (hD : ∀ d : D, n • d = 0) (U : OpenSubgroup G) (s : ℕ) :
    Function.Bijective (coindDualCompactMap φ hD U s) := by
  have h1 := bijective_compactCohomologyResMap_of_comp_eq_id (mackeyFamily U φ)
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).inv (Iso.hom_inv_id _)
    (Iso.inv_hom_id _) s
  have h2 : Function.Bijective (mackeyCompactCohomologyIso U φ
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{u} (U : Subgroup G) n)) s).hom.hom :=
    Function.bijective_iff_has_inverse.2 ⟨(mackeyCompactCohomologyIso U φ _ s).inv.hom,
      fun w => hom_apply_hom_apply_of_comp_eq (mackeyCompactCohomologyIso U φ _ s).hom_inv_id w,
      fun w => hom_apply_hom_apply_of_comp_eq (mackeyCompactCohomologyIso U φ _ s).inv_hom_id w⟩
  have h3 := bijective_compactCohomologyResMap_of_comp_eq_id φ
    (coindDualInv (U : Subgroup G) (ULift.{u} (ZMod n)) D)
    (coindDualHom (U : Subgroup G) (ULift.{u} (ZMod n)) D)
    (coindDualInv_comp_coindDualHom _ _ _) (coindDualHom_comp_coindDualInv _ _ _) s
  exact h1.comp (h2.comp h3)

theorem compactDualityMap_coind (hD : ∀ d : D, n • d = 0) (U : OpenSubgroup G)
    (t : compactCohomologyRes φ D 3 →+ ZMod n) {r s : ℕ} (h : r + s = 3)
    (x : cohomology (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)) r)
    (y : compactCohomologyRes φ
      (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n))) s) :
    compactDualityMap φ D h t
        (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)) x y =
      zmodCompactDualityMap φ D hD U h t ((shapiroMap U (zmodRep.{u} (U : Subgroup G) n) r).hom x)
        (coindDualCompactMap φ hD U s y) := by
  have hy : (compactCohomologyResMap φ (coindDualHom (U : Subgroup G) (ULift.{u} (ZMod n)) D) s).hom
      ((compactCohomologyResMap φ (coindDualInv (U : Subgroup G) (ULift.{u} (ZMod n)) D) s).hom y) =
        y := by
    rw [← ConcreteCategory.comp_apply, ← compactCohomologyResMap_comp,
      coindDualInv_comp_coindDualHom, compactCohomologyResMap_id]
    rfl
  rw [compactDualityMap_apply, zmodCompactDualityMap_apply]
  conv_lhs => rw [← hy]
  rw [compactCupRes_compactCohomologyResMap φ _
    ((coindDualHom (U : Subgroup G) (ULift.{u} (ZMod n)) D ⊗ₘ
      𝟙 (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n))) ≫
      dualEvalPairing D (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)))
    _ (𝟙 _) (by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]), cohomologyMap_id,
    tensorHom_coindDualHom_dualEvalPairing, ← compactCohomologyResMap_compactCupRes,
    ← compactCores_mackeyCompactCohomologyIso, mackeyCompactCohomologyIso_compactCupRes]
  congr 2
  rw [ModuleCat.hom_id, LinearMap.id_apply]
  have e := compactCupRes_compactCohomologyResMap (mackeyFamily U φ)
    (zmodMulPairingRight n (Rep.res (U : Subgroup G).subtype D) hD)
    (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{u} (U : Subgroup G) n))
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom (𝟙 _)
    (by rw [tensorHom_zmodDualIso_zmodMulPairingRight, MonoidalCategory.id_tensorHom_id,
      Category.id_comp]) ((Nat.add_comm s r).trans h)
    ((mackeyCompactCohomologyIso U φ
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{u} (U : Subgroup G) n)) s).hom.hom
      ((compactCohomologyResMap φ (coindDualInv (U : Subgroup G) (ULift.{u} (ZMod n)) D) s).hom y))
    ((shapiroMap U (zmodRep.{u} (U : Subgroup G) n) r).hom x)
  rw [cohomologyMap_id, ModuleCat.hom_id, LinearMap.id_apply] at e
  exact e.symm

end Bridge

section Main

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {t : compactCohomologyRes φ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace CompactDualityHypotheses

variable (H : CompactDualityHypotheses φ n D t U₀)

include H in

theorem bijective_compactDualityMap_coind (U : OpenSubgroup G) (hU : U ≤ U₀) {r s : ℕ}
    (h : r + s = 3) :
    Function.Bijective (compactDualityMap φ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n))) := by
  have hD := nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv
  have hsh : Function.Bijective (shapiroMap U (zmodRep.{u} (U : Subgroup G) n) r) :=
    Function.bijective_iff_has_inverse.2 ⟨inv (shapiroMap U _ r), inv_shapiroMap_apply U r,
      shapiroMap_inv_apply U r⟩
  exact bijective_of_bijective_comp (H.bijective_base U hU h) hsh
    (bijective_coindDualCompactMap φ hD U s) (compactDualityMap_coind φ hD U t h)

include H in

theorem compactGroupDualityHypotheses : CompactGroupDualityHypotheses φ n D t U₀ where
  nonempty_addEquiv := H.nonempty_addEquiv
  subsingleton_four := H.subsingleton_four
  bijective_coind U hU _ _ h := H.bijective_compactDualityMap_coind U hU h

include H in

theorem bijective_compactDualityMap (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactDualityMap φ D h t M) :=
  H.compactGroupDualityHypotheses.bijective_compactDualityMap M hM h

end CompactDualityHypotheses

end Main

end GroundTheory.ProfCoh
