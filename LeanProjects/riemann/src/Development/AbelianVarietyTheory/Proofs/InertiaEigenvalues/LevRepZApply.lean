import Mathlib

noncomputable section

namespace GlobalTheory.ShapeNeg

variable {O : Type} [CommRing O] (M : Type) [AddCommGroup M] [Module O M]

def Lev (c : O) : Type := ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M))

variable {M}

instance (c : O) : AddCommGroup (Lev M c) := inferInstanceAs (AddCommGroup ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)))
instance (c : O) : Module O (Lev M c) := inferInstanceAs (Module O ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)))
instance (c : O) : TopologicalSpace (Lev M c) := ⊥
instance (c : O) : DiscreteTopology (Lev M c) := ⟨rfl⟩
instance (c : O) : IsTopologicalAddGroup (Lev M c) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def Lev.val {c : O} (x : Lev M c) : M :=
  Subtype.val (p := fun m => m ∈ LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) x

theorem Lev.smul_val {c : O} (x : Lev M c) : c • x.val = 0 := by
  have hx := LinearMap.mem_ker.1
    (Subtype.property (p := fun m => m ∈ LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) x)
  exact hx

@[ext] theorem Lev.ext {c : O} {x y : Lev M c} (h : x.val = y.val) : x = y := by
  exact Subtype.ext (p := fun m => m ∈ LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) h

theorem Lev.val_add {c : O} (x y : Lev M c) : (x + y).val = x.val + y.val := rfl
theorem Lev.val_smul {c : O} (a : O) (x : Lev M c) : (a • x).val = a • x.val := rfl
theorem Lev.val_zero {c : O} : (0 : Lev M c).val = 0 := rfl

def Lev.mk {c : O} (m : M) (h : c • m = 0) : Lev M c :=
  (⟨m, by simpa using h⟩ : ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)))

theorem Lev.val_mk {c : O} (m : M) (h : c • m = 0) : (Lev.mk m h).val = m := rfl

variable {G : Type} [Group G]

def levRep (ρ : Representation O G M) (c : O) : Representation O G (Lev M c) where
  toFun g :=
    { toFun := fun x => Lev.mk (ρ g x.val) (by rw [← map_smul, Lev.smul_val, map_zero])
      map_add' := fun x y => Lev.ext (by rw [Lev.val_mk, Lev.val_add, Lev.val_add, map_add]; rfl)
      map_smul' := fun a x => Lev.ext (by rw [Lev.val_mk, Lev.val_smul, Lev.val_smul, map_smul]; rfl) }
  map_one' := by ext x; show ρ 1 x.val = x.val; rw [map_one]; rfl
  map_mul' g h := by ext x; show ρ (g * h) x.val = ρ g (ρ h x.val); rw [map_mul]; rfl

theorem levRep_val (ρ : Representation O G M) (c : O) (g : G) (x : Lev M c) :
    (levRep ρ c g x).val = ρ g x.val := rfl

abbrev levZ (p r : ℕ) [NeZero (p ^ r)] {c : O} (h : ((p : O) ^ r) ∈ Ideal.span {c}) :
    Module (ZMod (p ^ r)) (Lev M c) :=
  AddCommGroup.zmodModule (fun x => by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
    apply Lev.ext
    show ((p ^ r : ℕ) • x.val) = 0
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, ← ha, mul_smul, Lev.smul_val, smul_zero])

def levRepZ (p r : ℕ) [NeZero (p ^ r)] {c : O} (h : ((p : O) ^ r) ∈ Ideal.span {c})
    (ρ : Representation O G M) :
    @Representation (ZMod (p ^ r)) G (Lev M c) _ _ _ (levZ p r h) :=
  letI := levZ (M := M) p r h
  { toFun := fun g => (levRep ρ c g).toAddMonoidHom.toZModLinearMap (p ^ r)
    map_one' := LinearMap.ext fun x =>
      congrArg (fun f : Module.End O (Lev M c) => f x) (map_one (levRep ρ c))
    map_mul' := fun g g' => LinearMap.ext fun x =>
      congrArg (fun f : Module.End O (Lev M c) => f x) (map_mul (levRep ρ c) g g') }

theorem levRepZ_apply (p r : ℕ) [NeZero (p ^ r)] {c : O} (h : ((p : O) ^ r) ∈ Ideal.span {c})
    (ρ : Representation O G M) (g : G) (x : Lev M c) :
    levRepZ p r h ρ g x = levRep ρ c g x := rfl

end GlobalTheory.ShapeNeg
