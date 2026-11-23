import Development.EtaleCohomology.EtaleSheaves.LeafCompPf
import Development.EtaleCohomology.EtaleSheaves.LSchClsPfYon
import Development.EtaleCohomology.WeilConjectures.GlueOfSig
import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalDifferentialFormulaHolds

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafCoprodPf

section General
variable {C : Type*} [Category C] [Preadditive C]

theorem sum_comp_split {K L : CochainComplex C ℤ} {n : ℤ} {ι : Type} {Kj : ι → CochainComplex C ℤ}
    (i : ∀ j, Kj j ⟶ K) (p : ∀ j, K ⟶ Kj j) (α : Cochain K L n) (s : Finset ι) :
    ∑ j ∈ s, (Cochain.ofHom (p j)).comp ((Cochain.ofHom (i j)).comp α (zero_add n)) (zero_add n) =
      (Cochain.ofHom (∑ j ∈ s, p j ≫ i j)).comp α (zero_add n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Cochain.ofHom_add, Cochain.add_comp,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

theorem cls_inj {K L : CochainComplex C ℤ} {ι : Type} [Fintype ι] {Kj : ι → CochainComplex C ℤ}
    (i : ∀ j, Kj j ⟶ K) (p : ∀ j, K ⟶ Kj j) (hsum : ∑ j, p j ≫ i j = 𝟙 K) (n : ℤ)
    (x : CohomologyClass K L n) (hx : ∀ j, cpre (Cocycle.ofHom (i j)) L n n (zero_add n) x = 0) : x = 0 := by
  classical
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have h : ∀ j, ∃ β : Cochain (Kj j) L (n - 1),
      δ (n - 1) n β = (Cochain.ofHom (i j)).comp α.1 (zero_add n) := by
    intro j
    have := hx j
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff] at this
    obtain ⟨m, hm, β, hβ⟩ := this
    obtain rfl : m = n - 1 := by omega
    exact ⟨β, by rw [hβ]; rfl⟩
  choose β hβ using h
  have hδ : ∀ s : Finset ι, δ (n - 1) n (∑ j ∈ s, (Cochain.ofHom (p j)).comp (β j) (zero_add _)) =
      ∑ j ∈ s, (Cochain.ofHom (p j)).comp ((Cochain.ofHom (i j)).comp α.1 (zero_add n)) (zero_add n) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, δ_add, ih, δ_ofHom_comp, hβ]
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨n - 1, by omega, ∑ j, (Cochain.ofHom (p j)).comp (β j) (zero_add _), ?_⟩
  rw [hδ, sum_comp_split, hsum, Cochain.id_comp]

end General

section Sheaves
variable (R : Type) [CommRing R]

abbrev W : Spc ⥤ SimplicialObject (Shv R) := (SimplicialObject.whiskering _ _).obj (free R)

abbrev G : SimplicialObject (Shv R) ⥤ Cx R :=
  AlgebraicTopology.alternatingFaceMapComplex (Shv R) ⋙ ComplexShape.embeddingDownNat.extendFunctor (Shv R)

variable {m : ℕ} (Z : Fin m → Scheme.{0})

def gen (j : Fin m) : Sec ((free R).obj (yoneda.obj (Z j))) (∐ Z) :=
  ((LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (Z j))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).2
    (Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))))).choose

theorem gen_res (j t : Fin m) : Sec.res (Sigma.ι Z t) (gen R Z j) =
    Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))) t :=
  congrFun ((LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (Z j))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).2
    (Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))))).choose_spec t

def pr (j : Fin m) : (free R).obj (yoneda.obj (∐ Z)) ⟶ (free R).obj (yoneda.obj (Z j)) :=
  LateralTheory.E.L_sch_clsPfYon.yon R _ _ (gen R Z j)

theorem sec_comp {F F' F'' : Shv R} (φ : F ⟶ F') (ψ : F' ⟶ F'') {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sum_pr : ∑ j, pr R Z j ≫ (free R).map (yoneda.map (Sigma.ι Z j)) = 𝟙 _ := by
  classical
  apply LateralTheory.E.L_sch_clsPfYon.yon_ext
  apply (LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (∐ Z))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).1
  funext t
  change Sec.res (Sigma.ι Z t) _ = Sec.res (Sigma.ι Z t) _
  rw [LateralTheory.E.LeafKumSpecPf.sec_res_map, LateralTheory.E.LeafKumSpecPf.sec_res_map]
  erw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
  have hy : (ConcreteCategory.hom ((yoneda.obj (∐ Z)).map (Sigma.ι Z t).op)) (𝟙 (∐ Z)) = Sigma.ι Z t := by
    rfl
  rw [hy, LateralTheory.EtaleFoundations.EvDeltaPf.sec_sum, Finset.sum_eq_single t]
  · rw [sec_comp, pr, LateralTheory.E.L_sch_clsPfYon.yon_res, gen_res, Pi.single_eq_same,
      LateralTheory.EtaleFoundations.EvDeltaPf.freeGen_map]
    rfl
  · intro b _ hb
    rw [sec_comp, pr, LateralTheory.E.L_sch_clsPfYon.yon_res, gen_res, Pi.single_eq_of_ne (Ne.symm hb)]
    exact map_zero _
  · simp

def prS (j : Fin m) : (W R).obj (sch.obj (∐ Z)) ⟶ (W R).obj (sch.obj (Z j)) where
  app _ := pr R Z j
  naturality a b θ := by
    change (free R).map (𝟙 _) ≫ pr R Z j = pr R Z j ≫ (free R).map (𝟙 _)
    simp

theorem sum_prS : ∑ j, prS R Z j ≫ (W R).map (sch.map (Sigma.ι Z j)) = 𝟙 _ := by
  refine NatTrans.ext (funext fun a => ?_)
  rw [NatTrans.app_sum]
  exact sum_pr R Z

end Sheaves

theorem LeafCoprod_of : LateralTheory.E.E4.LeafCoprod := by
  intro _ q n i m Z hZ
  have : ∀ j, Finite (Ht q (sch.obj (Z j)) n i) := hZ
  refine Finite.of_injective (AddMonoidHom.pi fun j => pull (ZMod q) (sch.map (Sigma.ι Z j)) (tw q i) n) ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hsum : ∑ j, (G (ZMod q)).map (prS (ZMod q) Z j) ≫ (chains (ZMod q)).map (sch.map (Sigma.ι Z j)) = 𝟙 _ := by
    have h1 : (G (ZMod q)).map (∑ j, prS (ZMod q) Z j ≫ (W (ZMod q)).map (sch.map (Sigma.ι Z j))) = 𝟙 _ := by
      rw [sum_prS, CategoryTheory.Functor.map_id]
    rw [Functor.map_sum] at h1
    simp only [Functor.map_comp] at h1
    exact h1
  exact cls_inj (fun j => (chains (ZMod q)).map (sch.map (Sigma.ι Z j))) (fun j => (G (ZMod q)).map (prS (ZMod q) Z j))
    hsum n x (fun j => congrFun hx j)

end LateralTheory.E.LeafCoprodPf
