import Development.EtaleCohomology.EtaleSheaves.ClsBiprodEqZero
import Development.EtaleCohomology.EtaleSheaves.LeafCover2Of
import Development.EtaleCohomology.EtaleSheaves.LeafKunEmptyPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.DescEqvPf

variable {R : Type} [CommRing R]

theorem mono_sch {X Y : Scheme.{0}} (j : X ⟶ Y) [Mono j] : Mono (sch.map j) := by
  rw [NatTrans.mono_iff_mono_app]; intro n
  rw [NatTrans.mono_iff_mono_app]; intro T
  rw [mono_iff_injective]; intro a b h
  exact (cancel_mono j).1 h

theorem sub_of_iso {E E' : Spc} (i : E ≅ E') (F : Shv R) (n : ℤ) [Subsingleton (H R E' F n)] :
    Subsingleton (H R E F n) := by
  constructor; intro x y
  have hx : x = pull R i.hom F n (pull R i.inv F n x) := by rw [← pull_comp, i.hom_inv_id, pull_id]
  have hy : y = pull R i.hom F n (pull R i.inv F n y) := by rw [← pull_comp, i.hom_inv_id, pull_id]
  rw [hx, hy, Subsingleton.elim (pull R i.inv F n x) (pull R i.inv F n y)]

theorem sub_of_zero (E : Spc) (h : ∀ p, IsZero (((chains R).obj E).X p)) (F : Shv R) (n : ℤ) :
    Subsingleton (H R E F n) := by
  constructor; intro x y
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective y
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro p q hpq
  exact (h p).eq_of_src _ _

theorem bij_of_sub {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) [Subsingleton (H R E F n)]
    [Subsingleton (H R E' F n)] : Function.Bijective (pull R f F n) :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

instance freeModPresE : PreservesColimitsOfShape (Discrete PEmpty.{1}) (ModuleCat.free.{1} (ULift.{1} R)) := by
  have := (ModuleCat.adj.{1} (ULift.{1} R)).leftAdjoint_preservesColimits
  infer_instance

instance freePresE : PreservesColimitsOfShape (Discrete PEmpty.{1}) (free R) := by unfold free freeP; infer_instance

theorem chains_zero_of_initial (E : Spc) (hE : IsInitial E) (p : ℤ) : IsZero (((chains R).obj E).X p) := by
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = p
  · obtain ⟨j, hj⟩ := h
    have h1 : IsInitial (E.obj (op (SimplexCategory.mk j))) :=
      IsInitial.isInitialObj ((evaluation _ _).obj (op (SimplexCategory.mk j))) _ hE
    have h2 : IsInitial ((free R).obj (E.obj (op (SimplexCategory.mk j)))) := IsInitial.isInitialObj (free R) _ h1
    have hz : IsZero (((chainsN R).obj E).X j) := h2.isZero
    exact hz.of_iso (HomologicalComplex.extendXIso ((chainsN R).obj E) ComplexShape.embeddingDownNat hj)
  · push Not at h
    exact HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p h

end LateralTheory.E.DescEqvPf

namespace LateralTheory.E.DescEqvPf

variable {A R0 R1 : Type} [CommRing A] [CommRing R0] [CommRing R1] (e : A ≃+* R0 × R1)

def psi : Spec (.of R0) ⨿ Spec (.of R1) ⟶ Spec (.of A) :=
  coprodSpec R0 R1 ≫ Spec.map (CommRingCat.ofHom e.toRingHom)

instance : IsIso (psi e) := by
  unfold psi
  have : IsIso (CommRingCat.ofHom e.toRingHom) := (e.toCommRingCatIso).isIso_hom
  infer_instance

theorem inl_psi : coprod.inl ≫ psi e = Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) := by
  rw [psi, coprodSpec_inl_assoc, ← Spec.map_comp]; rfl

theorem inr_psi : coprod.inr ≫ psi e = Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) := by
  rw [psi, coprodSpec_inr_assoc, ← Spec.map_comp]; rfl

instance oi0 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))) := by
  rw [← inl_psi]; infer_instance

instance oi1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom))) := by
  rw [← inr_psi]; infer_instance

theorem empty_pb : IsEmpty ↥(Limits.pullback (C := Scheme.{0}) (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)))
    (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) := by
  refine ⟨fun z => ?_⟩
  have h := pullback.condition (f := Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)))
    (g := Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))
  have k0 : Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) ≫ inv (psi e) = coprod.inl := by
    rw [← inl_psi]; simp
  have k1 : Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) ≫ inv (psi e) = coprod.inr := by
    rw [← inr_psi]; simp
  have h2 := congrArg (fun f => (f ≫ inv (psi e)).base z) h
  simp only [Category.assoc] at h2
  rw [k0, k1, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h2
  exact Set.disjoint_left.mp (isCompl_range_inl_inr (Spec (.of R0)) (Spec (.of R1))).disjoint ⟨_, rfl⟩ ⟨_, h2.symm⟩

end LateralTheory.E.DescEqvPf

namespace LateralTheory.E.DescEqvPf

variable {R : Type} [CommRing R]

instance schPresPb : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance

theorem eqv_id (E : Spc) (F : Shv R) : Eqv R (𝟙 E) F := fun n =>
  ⟨fun a b h => by rwa [pull_id, pull_id] at h, fun y => ⟨y, pull_id R E F n y⟩⟩

theorem loc_coprod (U V : Spc) : LateralTheory.E.D2.LocCover (coprod.inl : U ⟶ U ⨿ V) coprod.inr := by
  intro n X x
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, ?_⟩
  intro Y k _
  let G : Spc ⥤ Type := (evaluation _ _).obj (op (SimplexCategory.mk n)) ⋙ (evaluation _ _).obj (op X)
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit (isColimitOfPreserves G (coprodIsCoprod U V)) x
  rcases j with ⟨(_ | _)⟩
  · left
    refine ⟨(U.obj _).map k.op y, ?_⟩
    rw [← hy]
    exact NatTrans.naturality_apply ((coprod.inl : U ⟶ U ⨿ V).app (op (SimplexCategory.mk n))) k.op y
  · right
    refine ⟨(V.obj _).map k.op y, ?_⟩
    rw [← hy]
    exact NatTrans.naturality_apply ((coprod.inr : V ⟶ U ⨿ V).app (op (SimplexCategory.mk n))) k.op y

theorem cover_coprod (U V : Spc) : Cover2 R (coprod.inl : U ⟶ U ⨿ V) coprod.inr :=
  LateralTheory.E.LeafCover2Pf.LeafCover2_of R _ _ inferInstance inferInstance (loc_coprod U V)

theorem sub_pb_coprod (U V : Spc) (F : Shv R) (n : ℤ) :
    Subsingleton (H R (pullback (coprod.inl : U ⟶ U ⨿ V) coprod.inr) F n) := by
  have hP := FinitaryExtensive.isPullback_initial_to_binaryCofan (coprodIsCoprod U V)
  have hI : IsInitial (pullback (coprod.inl : U ⟶ U ⨿ V) coprod.inr) :=
    IsInitial.ofIso initialIsInitial hP.isoPullback
  exact sub_of_zero _ (chains_zero_of_initial _ hI) F n

variable {A R0 R1 : Type} [CommRing A] [CommRing R0] [CommRing R1] (e : A ≃+* R0 × R1)

theorem loc_sch : LateralTheory.E.D2.LocCover (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))))
    (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) := by
  intro n X x
  let x' : X ⟶ Spec (.of A) := x
  let C : Scheme.OpenCover.{0} X := (coprodOpenCover.{0} (Spec (.of R0)) (Spec (.of R1))).pullback₁ (x' ≫ inv (psi e))
  refine ⟨Sieve.ofArrows C.X C.f, Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology C), ?_⟩
  intro Y k hk
  rw [Sieve.mem_ofArrows_iff] at hk
  obtain ⟨i, h, rfl⟩ := hk
  rcases i with (_ | _)
  · left
    refine ⟨h ≫ pullback.snd _ _, ?_⟩
    have c := pullback.condition (f := x' ≫ inv (psi e)) (g := (coprod.inl : Spec (.of R0) ⟶ _))
    have c' : pullback.fst (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _) ≫ x' =
        pullback.snd (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _) ≫
          Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) := by
      rw [← inl_psi, ← Category.assoc, ← c]; simp
    change (h ≫ pullback.snd (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _)) ≫
        Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) =
      (h ≫ pullback.fst (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _)) ≫ x'
    exact (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) c'.symm).trans (Category.assoc _ _ _).symm)
  · right
    refine ⟨h ≫ pullback.snd _ _, ?_⟩
    have c := pullback.condition (f := x' ≫ inv (psi e)) (g := (coprod.inr : Spec (.of R1) ⟶ _))
    have c' : pullback.fst (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _) ≫ x' =
        pullback.snd (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _) ≫
          Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) := by
      rw [← inr_psi, ← Category.assoc, ← c]; simp
    change (h ≫ pullback.snd (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _)) ≫
        Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) =
      (h ≫ pullback.fst (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _)) ≫ x'
    exact (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) c'.symm).trans (Category.assoc _ _ _).symm)

theorem cover_sch : Cover2 R (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))))
    (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) :=
  LateralTheory.E.LeafCover2Pf.LeafCover2_of R _ _ (mono_sch _) (mono_sch _) (loc_sch e)

theorem sub_pb_sch (F : Shv R) (n : ℤ) :
    Subsingleton (H R (pullback (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))))
      (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom))))) F n) := by
  have := empty_pb e
  have := LateralTheory.E.LeafKunEmptyPf.H_sub (R := R) (Limits.pullback (C := Scheme.{0})
    (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)))
    (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) F n
  exact sub_of_iso (PreservesPullback.iso sch _ _).symm F n

end LateralTheory.E.DescEqvPf

theorem LateralTheory.E.BinPf.DescEqv_of : LateralTheory.E.BinPf.DescEqv := by
  intro H q A R0 R1 _ _ _ e i
  open LateralTheory.E.DescEqvPf in
  exact H.a4 (ZMod q) (coprod.inl : sp R0 ⟶ sp R0 ⨿ sp R1) coprod.inr
    (spMap ((RingHom.fst R0 R1).comp e.toRingHom)) (spMap ((RingHom.snd R0 R1).comp e.toRingHom)) _ (𝟙 _) (𝟙 _) (by rw [Category.id_comp]; exact coprod.inl_desc _ _)
    (by rw [Category.id_comp]; exact coprod.inr_desc _ _) (tw q i)
    (cover_coprod _ _) (cover_sch e) (eqv_id _ _) (eqv_id _ _)
    (fun n => by
      have := sub_pb_coprod (R := ZMod q) (sp R0) (sp R1) (tw q i) n
      have := sub_pb_sch (R := ZMod q) e (tw q i) n
      exact bij_of_sub _ _ n)
