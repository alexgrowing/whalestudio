import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyMVPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.FreeCovPf

variable {X : Scheme.{0}} (U V : X.Opens)

def pieces : Bool → Scheme.{0}
  | true => U.toScheme
  | false => V.toScheme

def incl : (b : Bool) → pieces U V b ⟶ (U ⊔ V : X.Opens).toScheme
  | true => X.homOfLE le_sup_left
  | false => X.homOfLE le_sup_right

theorem cover_mem :
    Sieve.ofArrows (pieces U V) (incl U V) ∈ Scheme.etaleTopology.{0} (U ⊔ V : X.Opens).toScheme := by
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => ?_, fun b => ?_⟩
  · have hx : x.1 ∈ U ⊔ V := x.2
    rcases (TopologicalSpace.Opens.mem_sup.1 hx) with h | h
    · exact ⟨true, ⟨⟨x.1, h⟩, Subtype.ext (Scheme.homOfLE_apply (le_sup_left : U ≤ U ⊔ V) _)⟩⟩
    · exact ⟨false, ⟨⟨x.1, h⟩, Subtype.ext (Scheme.homOfLE_apply (le_sup_right : V ≤ U ⊔ V) _)⟩⟩
  · cases b
    · exact (inferInstance : Etale (X.homOfLE (le_sup_right : V ≤ U ⊔ V)))
    · exact (inferInstance : Etale (X.homOfLE (le_sup_left : U ≤ U ⊔ V)))

theorem sec_zero (R : Type) [CommRing R] (Zs : Shv R) (z : Zs.val.obj (op (U ⊔ V : X.Opens).toScheme))
    (h : ∀ b, Zs.val.map (incl U V b).op z = 0) : z = 0 := by
  have e := Presheaf.IsSheaf.hom_ext_ofArrows Zs.cond (incl U V) (cover_mem U V)
    (E := ModuleCat.of (ULift.{1} R) (ULift.{1} R))
    (x := ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ z)) (y := 0) (fun b => by
      ext1
      apply LinearMap.ext_ring
      simp [h b])
  have := congrArg (fun φ => φ.hom (1 : ULift.{1} R)) e
  simpa using this

theorem main (R : Type) [CommRing R] :
    Epi (biprod.desc ((free R).map (yoneda.map (X.homOfLE (le_sup_left : U ≤ U ⊔ V))))
      ((free R).map (yoneda.map (X.homOfLE (le_sup_right : V ≤ U ⊔ V))))) := by
  apply Preadditive.epi_of_cancel_zero
  intro Zs g hg
  have ha := congrArg (fun k => biprod.inl ≫ k) hg
  have hb := congrArg (fun k => biprod.inr ≫ k) hg
  simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, comp_zero] at ha hb
  let adj := sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  let W := (U ⊔ V : X.Opens).toScheme
  let g' := adj.homEquiv _ _ g
  let z := g'.app (op W) (ModuleCat.freeMk (ULift.up (𝟙 W)))
  have hval : ∀ (T : Scheme.{0}) (t : T ⟶ W),
      g'.app (op T) (ModuleCat.freeMk (ULift.up t : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op T)))) = Zs.val.map t.op z := by
    intro T t
    have := congrArg (fun φ => φ.hom (ModuleCat.freeMk (ULift.up (𝟙 W) : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op W))))) (g'.naturality t.op)
    have key : ((freeP R).obj (yoneda.obj W)).map t.op (ModuleCat.freeMk (ULift.up (𝟙 W) : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op W)))) = ModuleCat.freeMk (ULift.up t : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op T))) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
    exact (congrArg (fun v => (g'.app (op T)) v) key).symm.trans this
  have h0 : ∀ (P : PSh), adj.homEquiv _ _ (0 : (presheafToSheaf _ _).obj ((freeP R).obj P) ⟶ Zs) = 0 := by
    intro P
    rw [Adjunction.homEquiv_unit]
    simp
  have hres : ∀ {Y : Scheme.{0}} (i : Y ⟶ W), (free R).map (yoneda.map i) ≫ g = 0 → Zs.val.map i.op z = 0 := by
    intro Y i hi
    have h1 : adj.homEquiv _ _ ((presheafToSheaf _ _).map ((freeP R).map (yoneda.map i)) ≫ g) =
        (freeP R).map (yoneda.map i) ≫ g' :=
      adj.homEquiv_naturality_left _ _
    have hi' : (presheafToSheaf _ _).map ((freeP R).map (yoneda.map i)) ≫ g = 0 := hi
    rw [hi', h0] at h1
    have h2 := congrArg (fun φ => (φ.app (op Y)).hom (ModuleCat.freeMk (ULift.up (𝟙 Y) : uliftFunctor.{1, 0}.obj ((yoneda.obj Y).obj (op Y))))) h1
    have key : ((freeP R).map (yoneda.map i)).app (op Y) (ModuleCat.freeMk (ULift.up (𝟙 Y) : uliftFunctor.{1, 0}.obj ((yoneda.obj Y).obj (op Y)))) = ModuleCat.freeMk (ULift.up i : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op Y))) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
    rw [← hval]
    exact ((congrArg (fun v => (g'.app (op Y)) v) key).symm.trans h2.symm)
  have hz : z = 0 := sec_zero U V R Zs z (fun b => by
    cases b
    · exact hres _ hb
    · exact hres _ ha)
  have hg' : g' = 0 := by
    apply NatTrans.ext
    funext T
    induction T using Opposite.rec with | op T => ?_
    apply ModuleCat.free_hom_ext
    rintro ⟨t⟩
    erw [hval T t]
    rw [hz, map_zero]
    rfl
  exact (adj.homEquiv _ _).injective (hg'.trans (h0 _).symm)

theorem LeafFreeCov_of : LateralTheory.CohomologicalPurity.Thom.LeafFreeCov := fun R _ _ U V => main U V R

end LateralTheory.CohomologicalPurity.FreeCovPf
