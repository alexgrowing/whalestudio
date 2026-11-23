import Development.EtaleCohomology.TateTwists.acycPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.columnPf

theorem loc_top (U : Scheme.{0}) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) :
    Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h1 : Loc U P) (h2 : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hP⟩ := h1
  obtain ⟨T, hT, hQ⟩ := h2
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (hPQ : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hQ using hPQ
  refine ⟨Sieve.bind S.arrows fun V g hg => T V g (hP V g hg), Scheme.etaleTopology.bind_covering hS
    (fun V g hg => hT V g (hP V g hg)), ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact hQ V g (hP V g hg) W k hk

theorem loc_pull {U V : Scheme.{0}} {P : ∀ W : Scheme.{0}, (W ⟶ U) → Prop} (h : Loc U P) (g : V ⟶ U) :
    Loc V fun W k => P W (k ≫ g) := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => hP W _ hk⟩

theorem loc_finset {ι : Type*} (s : Finset ι) {U : Scheme.{0}} {P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ i ∈ s, Loc U (P i)) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_top U (by simp)
  | insert a s ha ih =>
    have := loc_and (h a (by simp)) (ih fun i hi => h i (by simp [hi]))
    exact loc_mono this fun V g ⟨h1, h2⟩ i hi => by
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h1
      · exact h2 i hi

theorem loc_empty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun _ _ h => h.elim⟩

def lift : Prop :=
  ∀ (R : Type) [CommRing R] (M : Shv R) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ M.obj),
    (∀ (U : Scheme.{0}) (y : Sec M U), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = Sec.res g y) →
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) →
    ∀ (F G : Shv R) (δ : F ⟶ G) (U : Scheme.{0}) (x : Sec F U ⊗[ULift.{1} R] Sec M U),
      TensorProduct.map (δ.hom.app (op U)).hom LinearMap.id x = 0 →
      Loc U fun V g => ∃ x' : Sec F V ⊗[ULift.{1} R] P.obj (op V),
        TensorProduct.map (δ.hom.app (op V)).hom LinearMap.id x' = 0 ∧
        TensorProduct.map LinearMap.id (φ.app (op V)).hom x' = TensorProduct.map (F.obj.map g.op).hom (M.obj.map g.op).hom x

def kill : Prop :=
  ∀ (R : Type) [CommRing R] (C : Cx R) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)),
    LateralTheory.EtaleFoundations.acyc.LocAcyc C → ∀ (V : Scheme.{0}) (s : ℤ) (x' : Sec (C.X s) V ⊗[ULift.{1} R] P.obj (op V)),
      Module.Flat (ULift.{1} R) (P.obj (op V)) →
      TensorProduct.map ((C.d s (s + 1)).hom.app (op V)).hom LinearMap.id x' = 0 →
      Loc V fun W k => ∃ y : Sec (C.X (s - 1)) W ⊗[ULift.{1} R] P.obj (op W),
        TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id y =
          TensorProduct.map ((C.X s).obj.map k.op).hom (P.map k.op).hom x'

end LateralTheory.EtaleFoundations.columnPf

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.acyc.column_of_cut (hL : lift) (hK : kill) : LateralTheory.EtaleFoundations.acyc.column := by
  intro R _ C J hJ hC U s t x hx
  obtain ⟨P, φ, hsurj, hker, hflat⟩ := hJ t
  refine loc_bind (hL R (J.X t) P φ hsurj hker (C.X s) (C.X (s + 1)) (C.d s (s + 1)) U x hx) ?_
  rintro V g ⟨x', hx'0, hx'⟩
  by_cases hV : Nonempty V
  · refine loc_mono (hK R C P hC V s x' (hflat V hV) hx'0) ?_
    rintro W k ⟨y, hy⟩
    refine ⟨TensorProduct.map LinearMap.id (φ.app (op W)).hom y, ?_⟩
    have e1 : TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id
        (TensorProduct.map LinearMap.id (φ.app (op W)).hom y) =
        TensorProduct.map LinearMap.id (φ.app (op W)).hom
          (TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id y) := by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
      rfl
    rw [e1, hy, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    have e2 : (TensorProduct.map ((C.X s).obj.map (k ≫ g).op).hom ((J.X t).obj.map (k ≫ g).op).hom) x =
        TensorProduct.map ((C.X s).obj.map k.op).hom ((J.X t).obj.map k.op).hom
          (TensorProduct.map ((C.X s).obj.map g.op).hom ((J.X t).obj.map g.op).hom x) := by
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, op_comp, Functor.map_comp, Functor.map_comp]
      rfl
    rw [e2, ← hx', ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    congr 2
    have := φ.naturality k.op
    exact congrArg ModuleCat.Hom.hom this
  · have : IsEmpty V := not_nonempty_iff.1 hV
    exact loc_empty V _

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.kill_of : kill := by
  classical
  intro R _ C P hC V s x' hflat hx'
  set d := ((C.d s (s + 1)).hom.app (op V)).hom
  have hex := Module.Flat.rTensor_exact (M := P.obj (op V)) (LinearMap.exact_subtype_ker_map d)
  obtain ⟨w, hw⟩ := (hex x').1 hx'
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset w
  have hloc : ∀ i ∈ S, Loc V fun W k => ∃ y : Sec (C.X (s - 1)) W,
      Sec.map (C.d (s - 1) s) y = Sec.res k (i.1 : Sec (C.X s) V) := fun i _ =>
    hC V s (i.1 : Sec (C.X s) V) i.1.2
  refine loc_mono (loc_finset S hloc) ?_
  intro W k hk
  choose y hy using hk
  refine ⟨∑ i ∈ S.attach, y i.1 i.2 ⊗ₜ (P.map k.op).hom i.1.2, ?_⟩
  rw [map_sum, ← hw, hS, map_sum, map_sum]
  rw [← Finset.sum_attach S]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.id_apply]
  congr 1
  exact hy i.1 i.2
