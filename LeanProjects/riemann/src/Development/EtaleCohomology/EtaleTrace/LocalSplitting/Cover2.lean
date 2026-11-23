import Development.EtaleCohomology.EtaleTrace.LTwoEpiPf
import Development.EtaleCohomology.EtaleTrace.LDblPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LSplitPf.Sch

theorem cov {X : Scheme.{0}} (O1 O2 : X.Opens) (hcov : O1 ⊔ O2 = ⊤) :
    Sieve.ofArrows (fun b : Bool => cond b (O1 : Scheme.{0}) O2) (fun b => match b with | true => O1.ι | false => O2.ι) ∈
      Scheme.etaleTopology.{0} X := by
  apply Scheme.zariskiTopology_le_etaleTopology
  have hU : TopologicalSpace.IsOpenCover (fun b : Bool => cond b O1 O2) := by
    show ⨆ b, cond b O1 O2 = ⊤
    rw [iSup_bool_eq]; simpa using hcov
  apply GrothendieckTopology.superset_covering _ ?_ (X.openCoverOfIsOpenCover _ hU).mem_grothendieckTopology
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro - - ⟨k⟩
  rcases k with (_ | _)
  · exact ⟨_, 𝟙 _, O2.ι, ⟨false⟩, Category.id_comp _⟩
  · exact ⟨_, 𝟙 _, O1.ι, ⟨true⟩, Category.id_comp _⟩

theorem psi (R : Type) [CommRing R] {X : Scheme.{0}} (O1 O2 : X.Opens) (hcov : O1 ⊔ O2 = ⊤) (G : Shv R)
    (ψ : (freeP R).obj (yoneda.obj X) ⟶ G.val)
    (hi : (freeP R).map (yoneda.map O1.ι) ≫ ψ = 0) (hj : (freeP R).map (yoneda.map O2.ι) ≫ ψ = 0) : ψ = 0 := by
  let s := (ψ.app (op X)).hom (ModuleCat.freeMk (ULift.up (𝟙 X)))
  have nat : ∀ (T : Scheme.{0}) (t : T ⟶ X),
      (ψ.app (op T)).hom (ModuleCat.freeMk (ULift.up t)) = (G.val.map t.op).hom s := by
    intro T t
    have h := congrArg (fun φ => φ.hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) (ψ.naturality t.op)
    change (ψ.app (op T)).hom (((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.map ((yoneda.obj X).map t.op))).hom
      (ModuleCat.freeMk (ULift.up (𝟙 X)))) = _ at h
    erw [LateralTheory.EtaleTrace.ltwo_fm] at h
    simp at h
    exact h
  have hz : ∀ {Y : Scheme.{0}} (f : Y ⟶ X), (freeP R).map (yoneda.map f) ≫ ψ = 0 → (G.val.map f.op).hom s = 0 := by
    intro Y f hf
    rw [← nat]
    have h := congrArg (fun φ => (φ.app (op Y)).hom (ModuleCat.freeMk (ULift.up (𝟙 Y)))) hf
    change (ψ.app (op Y)).hom (((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.map ((yoneda.map f).app (op Y)))).hom
      (ModuleCat.freeMk (ULift.up (𝟙 Y)))) = 0 at h
    erw [LateralTheory.EtaleTrace.ltwo_fm] at h
    simpa using h
  have hs : s = 0 := by
    have key : ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ s) = 0 := by
      refine Presheaf.IsSheaf.hom_ext_ofArrows G.cond _ (cov O1 O2 hcov) (fun b => ?_)
      refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
      cases b
      · simpa using hz O2.ι hj
      · simpa using hz O1.ι hi
    simpa using congrArg (fun φ => φ.hom 1) key
  refine NatTrans.ext (funext fun T => ModuleCat.free_hom_ext (fun x => ?_))
  obtain ⟨t⟩ := x
  erw [nat T.unop t, hs]
  simp
  rfl

theorem epi (R : Type) [CommRing R] {X : Scheme.{0}} (O1 O2 : X.Opens) (hcov : O1 ⊔ O2 = ⊤) (n) :
    Epi (biprod.desc ((free R).map ((sch.map O1.ι).app n)) ((free R).map ((sch.map O2.ι).app n))) := by
  change Epi (biprod.desc ((free R).map (yoneda.map O1.ι)) ((free R).map (yoneda.map O2.ι)))
  apply Preadditive.epi_of_cancel_zero
  intro G φ hφ
  have h1 : (free R).map (yoneda.map O1.ι) ≫ φ = 0 := by simpa using biprod.inl ≫= hφ
  have h2 : (free R).map (yoneda.map O2.ι) ≫ φ = 0 := by simpa using biprod.inr ≫= hφ
  let J := Scheme.etaleTopology.{0}
  let φ' : sheafify J ((freeP R).obj (yoneda.obj X)) ⟶ G.obj := φ.hom
  have hv : ∀ {Y : Scheme.{0}} (f : Y ⟶ X), (free R).map (yoneda.map f) ≫ φ = 0 →
      (freeP R).map (yoneda.map f) ≫ (toSheafify J _ ≫ φ') = 0 := by
    intro Y f hf
    have this : sheafifyMap J ((freeP R).map (yoneda.map f)) ≫ φ' = 0 := by
      have := congrArg (fun ψ => ψ.hom) hf
      exact this
    rw [← Category.assoc, toSheafify_naturality, Category.assoc, this, comp_zero]
  have hψ := psi R O1 O2 hcov G _ (hv O1.ι h1) (hv O2.ι h2)
  apply Sheaf.hom_ext
  exact sheafify_hom_ext (J := J) φ' 0 G.property (by rw [hψ]; simp)

theorem cover2 (R : Type) [CommRing R] {X : Scheme.{0}} (O1 O2 : X.Opens) (hcov : O1 ⊔ O2 = ⊤) :
    Cover2 R (sch.map O1.ι) (sch.map O2.ι) :=
  ⟨inferInstance, inferInstance, epi R O1 O2 hcov⟩

end LateralTheory.EtaleTrace.LSplitPf.Sch
