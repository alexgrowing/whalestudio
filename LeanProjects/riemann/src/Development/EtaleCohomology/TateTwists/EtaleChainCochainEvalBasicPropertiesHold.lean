import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationLinear

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvB
variable {R : Type} [CommRing R]

theorem ev_add {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  simp [ev]

noncomputable def evHom {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun α => ev α p s h U x) (fun α β => ev_add α β p s h U x)

theorem ev_compHom {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  simp [ev, Cochain.comp_v _ _ (add_zero n) _ s s h (add_zero s)]

theorem isZero_pos {E : Spc} (a : ℤ) (ha : 0 < a) : IsZero (((chains R).obj E).X a) := by
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  change -(j : ℤ) = a at hj
  omega

theorem free_ext {P : PSh} {F : Shv R} (φ ψ : (free R).obj P ⟶ F)
    (hφ : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ F.cond
  ext U : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have := hφ U.unop x
  simp only [freeGen] at this
  exact this

theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := congrArg (fun f => ModuleCat.Hom.hom f y) (φ.hom.naturality g.op)
  simpa using this.symm

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) x :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have key := fun y => congrArg (fun f => ModuleCat.Hom.hom f y)
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  unfold freeGen
  refine ((key _).symm).trans ?_
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.whiskeringRight_obj_map, Functor.comp_map, Functor.whiskerRight_app, uliftFunctor_map] <;> try (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  all_goals simp [freeP, ModuleCat.freeMk, ModuleCat.free, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem freeGen_map {P Q : PSh} (f : P ⟶ Q) U x :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have key := fun y => congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) y)
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at key
  unfold freeGen
  refine ((key _).symm).trans ?_
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.whiskeringRight_obj_map, Functor.comp_map, Functor.whiskerRight_app, uliftFunctor_map] <;> try (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  all_goals simp [freeP, ModuleCat.freeMk, ModuleCat.free, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem chainsXIso_nat {E' E : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p:ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  simp [chainsXIso, chains, chainsN, HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f p = -(p:ℤ) from rfl)]
  erw [Iso.inv_hom_id_assoc]
  try rfl

theorem ev_res {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  have := sec_nat ((chainsXIso R E p).inv ≫ α.v _ _ h) g (freeGen R _ U x)
  rw [freeGen_res] at this
  exact this

theorem ev_ext {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (hαβ : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  apply Cochain.ext
  intro a b hab
  by_cases ha : 0 < a
  · exact (isZero_pos a ha).eq_of_src _ _
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = -(k : ℤ) := ⟨(-a).toNat, by omega⟩
  rw [← cancel_epi (chainsXIso R E k).inv]
  exact free_ext _ _ (fun U x => hαβ k b hab U x)

theorem ev_pull {E E' : Spc} {I : Cx R} {n : ℤ} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  have e1 : ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)).v (-(p:ℤ)) s h =
      ((chains R).map f).f (-(p:ℤ)) ≫ α.v (-(p:ℤ)) s h := by
    rw [Cochain.comp_v _ _ (zero_add n) (-(p:ℤ)) (-(p:ℤ)) s (add_zero _) h, Cochain.ofHom_v]
  unfold ev
  rw [e1, ← Category.assoc, chainsXIso_nat, Category.assoc]
  have := freeGen_map (R := R) (f.app (op (SimplexCategory.mk p))) U x
  simp only [Sec.map] at this
  simp [this, Sx.map]

end LateralTheory.EtaleFoundations.EvB

theorem LateralTheory.EtaleFoundations.etale_chain_cochain_eval_basic_properties_hold : LateralTheory.EtaleFoundations.EtaleCochainEvaluationLinear := by
  intro R _ E I n
  refine ⟨fun α β p s h U x => ?_, fun α p s h V U g x => LateralTheory.EtaleFoundations.EvB.ev_res α p s h V U g x,
    fun α β hαβ => LateralTheory.EtaleFoundations.EvB.ev_ext α β hαβ, fun f α p s h U x => LateralTheory.EtaleFoundations.EvB.ev_pull f α p s h U x,
    fun m α p s h U x => LateralTheory.EtaleFoundations.EvB.ev_compHom m α p s h U x⟩
  have H := LateralTheory.EtaleFoundations.EvB.evHom (I := I) (n := n) (E := E) p s h U x
  exact ⟨map_add (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) α β, map_sub (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) α β,
    map_zero (LateralTheory.EtaleFoundations.EvB.evHom (I := I) (n := n) p s h U x), fun c => map_zsmul (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) c α⟩
