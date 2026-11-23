import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Limits Simplicial

namespace GlobalTheory.CompanionTheory.Hodge.Nerve

variable {R : Type} [CommRing R]

section Cochains

variable {C : Type} [Category.{0} C]

abbrev NC (G : C ⥤ ModuleCat.{0} R) (n : ℕ) : Type :=
  ∀ c : Fin (n + 1) ⥤ C, G.obj (c.obj (Fin.last n))

def pullNC (G : C ⥤ ModuleCat.{0} R) {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) : NC G m →ₗ[R] NC G n :=
  LinearMap.pi fun c ↦ (G.map (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))).hom ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (m + 1) ⥤ C ↦ (G.obj (c.obj (Fin.last m)) : Type))
      (θ.monotone.functor ⋙ c)

theorem pullNC_apply (G : C ⥤ ModuleCat.{0} R) {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (f : NC G m)
    (c : Fin (n + 1) ⥤ C) :
    pullNC G θ f c = (G.map (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))).hom (f (θ.monotone.functor ⋙ c)) :=
  rfl

theorem map_map_chain (G : C ⥤ ModuleCat.{0} R) {n : ℕ} (c : Fin (n + 1) ⥤ C) {x y z : Fin (n + 1)} (a : x ≤ y)
    (b : y ≤ z) (v : G.obj (c.obj x)) :
    (G.map (c.map (homOfLE b))).hom ((G.map (c.map (homOfLE a))).hom v) =
      (G.map (c.map (homOfLE (a.trans b)))).hom v := by
  rw [← ModuleCat.comp_apply, ← G.map_comp, ← c.map_comp]
  rfl

def cosimp (G : C ⥤ ModuleCat.{0} R) : CosimplicialObject (ModuleCat.{0} R) where
  obj n := ModuleCat.of R (NC G n.len)
  map θ := ModuleCat.ofHom (pullNC G θ.toOrderHom)
  map_id n := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    have e : c.map (homOfLE (Fin.le_last (Fin.last n.len))) = 𝟙 _ := c.map_id _
    change (G.map (c.map (homOfLE (Fin.le_last (Fin.last n.len))))).hom (f c) = f c
    rw [e, G.map_id]
    rfl
  map_comp {a b d} θ ψ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    change (G.map (c.map _)).hom (f ((θ ≫ ψ).toOrderHom.monotone.functor ⋙ c)) =
      (G.map (c.map _)).hom ((G.map (c.map (homOfLE (ψ.toOrderHom.monotone (Fin.le_last (θ.toOrderHom (Fin.last a.len))))))).hom
        (f (θ.toOrderHom.monotone.functor ⋙ ψ.toOrderHom.monotone.functor ⋙ c)))
    exact (map_map_chain G c _ _ _).symm

def cosimpMap {G G' : C ⥤ ModuleCat.{0} R} (φ : G ⟶ G') : cosimp G ⟶ cosimp G' where
  app n := ModuleCat.ofHom (LinearMap.pi fun c ↦ (φ.app _).hom ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (n.len + 1) ⥤ C ↦ (G.obj (c.obj (Fin.last n.len)) : Type)) c)
  naturality a b θ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    exact congr(($(φ.naturality (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last a.len)))))).hom _))

def cosimpFunctor : (C ⥤ ModuleCat.{0} R) ⥤ CosimplicialObject (ModuleCat.{0} R) where
  obj := cosimp
  map := cosimpMap
  map_id _ := rfl
  map_comp _ _ := rfl

def nerveCx : (C ⥤ ModuleCat.{0} R) ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  cosimpFunctor ⋙ AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{0} R)

instance : (nerveCx (R := R) (C := C)).PreservesZeroMorphisms where
  map_zero G G' := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    change (0 : G.obj _ ⟶ G'.obj _).hom (f c) = 0
    rfl

def dNC (G : C ⥤ ModuleCat.{0} R) (n : ℕ) : NC G n →ₗ[R] NC G (n + 1) :=
  ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • pullNC G (Fin.succAboveOrderEmb i).toOrderHom

theorem nerveCx_X (G : C ⥤ ModuleCat.{0} R) (n : ℕ) : (nerveCx.obj G).X n = ModuleCat.of R (NC G n) := rfl

theorem nerveCx_d (G : C ⥤ ModuleCat.{0} R) (n : ℕ) :
    (nerveCx.obj G).d n (n + 1) = ModuleCat.ofHom (dNC G n) := by
  have h0 : (nerveCx.obj G).d n (n + 1) = AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp G) n :=
    CochainComplex.of_d (fun n ↦ (cosimp G).obj ⦋n⦌) (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp G)) n
  refine h0.trans ?_
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (ModuleCat.ofHom (pullNC G (Fin.succAboveOrderEmb i).toOrderHom) :
    ModuleCat.of R (NC G n) ⟶ ModuleCat.of R (NC G (n + 1)))) = _
  refine ModuleCat.hom_ext ?_
  rw [ModuleCat.hom_ofHom, ModuleCat.hom_sum]
  unfold dNC
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : ((-1 : R) ^ (i : ℕ)) = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : R) := by push_cast; rfl
  rw [h, Int.cast_smul_eq_zsmul, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom]

theorem nerveCx_map_f {G G' : C ⥤ ModuleCat.{0} R} (φ : G ⟶ G') (n : ℕ) (f : NC G n) (c : Fin (n + 1) ⥤ C) :
    (show NC G' n from ((nerveCx.map φ).f n).hom f) c = (φ.app _).hom (f c) := rfl

@[simps] def toMod (F : C ⥤ CommAlgCat.{0} R) : C ⥤ ModuleCat.{0} R where
  obj T := ModuleCat.of R (F.obj T)
  map φ := ModuleCat.ofHom (GlobalTheory.CatCoh.mp F φ).toLinearMap
  map_id T := ModuleCat.hom_ext (LinearMap.ext fun b ↦ GlobalTheory.CatCoh.mp_id F T b)
  map_comp φ ψ := ModuleCat.hom_ext (LinearMap.ext fun b ↦ GlobalTheory.CatCoh.mp_comp F φ ψ b)

theorem dNC_toMod (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) : dNC (toMod F) n = MainStatements.Hodge.dn F n := rfl

end Cochains

section Cube

variable {P : Type} [SemilatticeInf P] {κ : Type} (e : κ → P)

def cubeRes (G : Pᵒᵖ ⥤ ModuleCat.{0} R) {s t : Finset κ} (h : s ⊆ t) :
    (∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))) →ₗ[R]
      ∀ ht : PLift t.Nonempty, G.obj (op (t.inf' ht.down e)) :=
  LinearMap.pi fun _ ↦ if hs : s.Nonempty then
    (G.map (homOfLE (Finset.inf'_mono e h hs)).op).hom ∘ₗ
      LinearMap.proj (R := R) (φ := fun hs : PLift s.Nonempty ↦ (G.obj (op (s.inf' hs.down e)) : Type)) ⟨hs⟩
  else 0

theorem cubeRes_apply (G : Pᵒᵖ ⥤ ModuleCat.{0} R) {s t : Finset κ} (h : s ⊆ t)
    (x : ∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))) (hs : s.Nonempty) (ht : PLift t.Nonempty) :
    cubeRes e G h x ht = (G.map (homOfLE (Finset.inf'_mono e h hs)).op).hom (x ⟨hs⟩) := by
  simp [cubeRes, hs]

theorem cubeRes_empty (G : Pᵒᵖ ⥤ ModuleCat.{0} R) {s t : Finset κ} (h : s ⊆ t)
    (x : ∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))) (hs : ¬ s.Nonempty) (ht : PLift t.Nonempty) :
    cubeRes e G h x ht = 0 := by
  simp [cubeRes, hs]

def cubeOf (G : Pᵒᵖ ⥤ ModuleCat.{0} R) : Cube.{0} κ R :=
  Cube.mk (fun s ↦ ModuleCat.of R (∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))))
    (fun h ↦ cubeRes e G h)
    (fun s x ↦ funext fun hs ↦ by
      rw [cubeRes_apply e G _ x hs.down hs]
      exact congr(($(G.map_id (op (s.inf' hs.down e)))).hom (x hs)))
    (fun {s t w} h h' x ↦ funext fun hw ↦ by
      by_cases hs : s.Nonempty
      · rw [cubeRes_apply e G h' _ (hs.mono h) hw, cubeRes_apply e G h x hs ⟨hs.mono h⟩,
          cubeRes_apply e G (h.trans h') x hs hw, ← ModuleCat.comp_apply, ← G.map_comp]
        rfl
      · rw [cubeRes_empty e G (h.trans h') x hs hw]
        by_cases ht : t.Nonempty
        · rw [cubeRes_apply e G h' _ ht hw, cubeRes_empty e G h x hs ⟨ht⟩, map_zero]
        · rw [cubeRes_empty e G h' _ ht hw])

def cubeOfMap {G G' : Pᵒᵖ ⥤ ModuleCat.{0} R} (φ : G ⟶ G') : cubeOf e G ⟶ cubeOf e G' :=
  Cube.homMk (fun s ↦ LinearMap.pi fun hs ↦ (φ.app _).hom ∘ₗ
      LinearMap.proj (R := R) (φ := fun hs : PLift s.Nonempty ↦ (G.obj (op (s.inf' hs.down e)) : Type)) hs)
    (fun {s t} h x ↦ funext fun ht ↦ by
      by_cases hs : s.Nonempty
      · refine ((congrArg (φ.app _).hom (cubeRes_apply e G h x hs ht)).trans ?_).trans
          (cubeRes_apply e G' h _ hs ht).symm
        exact congr(($(φ.naturality (homOfLE (Finset.inf'_mono e h hs)).op)).hom (x ⟨hs⟩))
      · exact ((congrArg (φ.app _).hom (cubeRes_empty e G h x hs ht)).trans (map_zero _)).trans
          (cubeRes_empty e G' h _ hs ht).symm)

def cubeOfFunctor : (Pᵒᵖ ⥤ ModuleCat.{0} R) ⥤ Cube.{0} κ R where
  obj := cubeOf e
  map := cubeOfMap e
  map_id G := by
    ext s
    rfl
  map_comp φ ψ := by
    ext s
    rfl

def cechOf [LinearOrder κ] : (Pᵒᵖ ⥤ ModuleCat.{0} R) ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  cubeOfFunctor e ⋙ cechFunctor κ R

instance : (cubeOfFunctor (R := R) e).PreservesZeroMorphisms := ⟨fun G G' ↦ by ext s; rfl⟩

instance [LinearOrder κ] : (cechOf (R := R) e).PreservesZeroMorphisms := by
  unfold cechOf
  infer_instance

end Cube

section Coinduced

variable {P : Type} [SemilatticeInf P]

def coind (M : P → ModuleCat.{0} R) : Pᵒᵖ ⥤ ModuleCat.{0} R where
  obj a := ModuleCat.of R (∀ b : {b : P // b ≤ a.unop}, M b.1)
  map {a a'} φ := ModuleCat.ofHom
    { toFun := fun f b ↦ f ⟨b.1, b.2.trans (leOfHom φ.unop)⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

def toCoind (G : Pᵒᵖ ⥤ ModuleCat.{0} R) : G ⟶ coind fun b ↦ G.obj (op b) where
  app a := ModuleCat.ofHom
    { toFun := fun x b ↦ (G.map (homOfLE b.2).op).hom x
      map_add' := fun x y ↦ funext fun b ↦ map_add _ x y
      map_smul' := fun r x ↦ funext fun b ↦ map_smul _ r x }
  naturality a a' φ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext fun b ↦ ?_)
    change (G.map (homOfLE b.2).op).hom ((G.map φ).hom x) = (G.map (homOfLE (b.2.trans (leOfHom φ.unop))).op).hom x
    rw [← ModuleCat.comp_apply, ← G.map_comp]
    rfl

end Coinduced

end GlobalTheory.CompanionTheory.Hodge.Nerve
