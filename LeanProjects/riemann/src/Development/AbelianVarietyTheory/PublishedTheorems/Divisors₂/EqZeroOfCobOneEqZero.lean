import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

noncomputable section

open TensorProduct Coalgebra CategoryTheory

namespace GlobalTheory

namespace PDiv

section Level

variable {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]

variable (O A) in

def cobOne : A →ₗ[O] A ⊗[O] A :=
  comul - (TensorProduct.mk O A A).flip 1 - TensorProduct.mk O A A 1

theorem cobOne_apply (b : A) : cobOne O A b = comul b - b ⊗ₜ 1 - 1 ⊗ₜ b := rfl

variable (O A) in

def cobTwo : A ⊗[O] A →ₗ[O] A ⊗[O] (A ⊗[O] A) :=
  TensorProduct.mk O A (A ⊗[O] A) 1 - (TensorProduct.assoc O A A A).toLinearMap ∘ₗ comul.rTensor A
    + comul.lTensor A - ((TensorProduct.mk O A A).flip 1).lTensor A

theorem cobTwo_apply (c : A ⊗[O] A) : cobTwo O A c =
    1 ⊗ₜ c - TensorProduct.assoc O A A A (comul.rTensor A c) + comul.lTensor A c
      - ((TensorProduct.mk O A A).flip 1).lTensor A c := rfl

variable (O A) in

def symCocycles : Submodule O (A ⊗[O] A) :=
  LinearMap.ker (cobTwo O A) ⊓ LinearMap.ker ((TensorProduct.comm O A A).toLinearMap - LinearMap.id)

theorem mem_symCocycles {c : A ⊗[O] A} :
    c ∈ symCocycles O A ↔ cobTwo O A c = 0 ∧ TensorProduct.comm O A A c = c := by
  simp [symCocycles, sub_eq_zero]

theorem cobTwo_cobOne (b : A) : cobTwo O A (cobOne O A b) = 0 := by
  have h1 : ∀ t : A ⊗[O] A, TensorProduct.assoc O A A A (t ⊗ₜ 1) =
      ((TensorProduct.mk O A A).flip 1).lTensor A t := fun t => by
    induction t with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  have h2 : comul (R := O) (1 : A) = 1 ⊗ₜ 1 := by simp [Algebra.TensorProduct.one_def]
  simp only [cobTwo_apply, cobOne_apply, map_sub, tmul_sub, coassoc_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, h1, h2, LinearMap.flip_apply, mk_apply]
  rw [assoc_tmul 1 1 b]
  abel

theorem cobOne_mem [IsCocomm O A] (b : A) : cobOne O A b ∈ symCocycles O A :=
  mem_symCocycles.2 ⟨cobTwo_cobOne b, by
    simp only [cobOne_apply, map_sub, comm_comul, comm_tmul]; abel⟩

abbrev pullbackTwo (f : A →ₐc[O] B) : A ⊗[O] A →ₗ[O] B ⊗[O] B :=
  TensorProduct.map (f : A →ₗ[O] B) (f : A →ₗ[O] B)

theorem pullTwo_comul (f : A →ₐc[O] B) (a : A) : pullbackTwo f (comul a) = comul (f a) :=
  LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) a

theorem pullTwo_cobOne (f : A →ₐc[O] B) (b : A) :
    pullbackTwo f (cobOne O A b) = cobOne O B (f b) := by
  simp [cobOne_apply, pullTwo_comul]

theorem cobTwo_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    cobTwo O B (pullbackTwo f c) = TensorProduct.map (f : A →ₗ[O] B) (pullbackTwo f) (cobTwo O A c) := by
  induction c with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    have h := TensorProduct.map_map_assoc (f : A →ₗ[O] B) (f : A →ₗ[O] B) (f : A →ₗ[O] B)
      (comul a ⊗ₜ b)
    simp [cobTwo_apply, pullTwo_comul, h]

theorem pullTwo_mem (f : A →ₐc[O] B) {c : A ⊗[O] A} (hc : c ∈ symCocycles O A) :
    pullbackTwo f c ∈ symCocycles O B := by
  rw [mem_symCocycles] at hc ⊢
  exact ⟨by rw [cobTwo_pullTwo, hc.1, map_zero], by rw [← TensorProduct.map_comm, hc.2]⟩

theorem pullTwo_comp {D : Type} [CommRing D] [Bialgebra O D] (g : B →ₐc[O] D) (f : A →ₐc[O] B)
    (c : A ⊗[O] A) : pullbackTwo (g.comp f) c = pullbackTwo g (pullbackTwo f c) := by
  induction c with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp

theorem pullTwo_id (c : A ⊗[O] A) : pullbackTwo (BialgHom.id O A) c = c := by
  induction c with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp

theorem mulBy_of_cobOne_eq_zero [IsCocomm O A] {b : A} (hb : cobOne O A b = 0) (k : ℕ) :
    mulBy O A k b = k • b ∧ counit (R := O) b = 0 := by
  have hp : IsPrimitiveElem O b := by
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb; exact hb
  refine ⟨?_, hp.counit_eq_zero⟩
  have key : ∀ k : ℕ, (WithConv.toConv (AlgHom.id O A) ^ k) b = k • b := fun k => by
    induction k with
    | zero => simp [hp.counit_eq_zero]
    | succ k ih =>
      rw [pow_succ, AlgHom.convMul_apply, show comul b = _ from hp, succ_nsmul, ← ih]
      simp
  exact (DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id O A) k) b).trans (key k)

end Level

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} {O : Type} [CommRing O] (G H K : PDivGroup p O)

def funs : Submodule O (∀ n, G.A n) where
  carrier := {b | ∀ n, G.res n (b (n + 1)) = b n}
  zero_mem' _ := map_zero _
  add_mem' {v w} hv hw n := by rw [Pi.add_apply, map_add, hv n, hw n, Pi.add_apply]
  smul_mem' c w hw n := by rw [Pi.smul_apply, map_smul, hw n, Pi.smul_apply]

def cocycles : Submodule O (∀ n, G.A n ⊗[O] G.A n) where
  carrier := {c | ∀ n, c n ∈ symCocycles O (G.A n) ∧ pullbackTwo (G.res n) (c (n + 1)) = c n}
  zero_mem' _ := ⟨zero_mem _, map_zero _⟩
  add_mem' {v w} hv hw n := ⟨add_mem (hv n).1 (hw n).1, by
    rw [Pi.add_apply, map_add, (hv n).2, (hw n).2, Pi.add_apply]⟩
  smul_mem' c w hw n := ⟨Submodule.smul_mem _ c (hw n).1, by
    rw [Pi.smul_apply, map_smul, (hw n).2, Pi.smul_apply]⟩

def cob : G.funs →ₗ[O] G.cocycles where
  toFun b := ⟨fun n => cobOne O _ (b.1 n), fun n =>
    ⟨cobOne_mem _, (pullTwo_cobOne _ _).trans (congrArg _ (b.2 n))⟩⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add (cobOne O _) _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul (cobOne O _) _ _)

def dFun : G.funs →ₗ[O] G.omega where
  toFun b := ⟨fun n => dUnit O (b.1 n), fun n => (cotMap_d _ _).trans (congrArg _ (b.2 n))⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add (AugCot.d _) _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul (AugCot.d _) _ _)

abbrev VecExt : Type := G.cocycles ⧸ LinearMap.range G.cob

abbrev RigExt : Type := (G.cocycles × G.omega) ⧸ LinearMap.range (G.cob.prod G.dFun)

def rigMk : G.cocycles × G.omega →ₗ[O] G.RigExt := Submodule.mkQ _

def rigOfOmega : G.omega →ₗ[O] G.RigExt := G.rigMk ∘ₗ LinearMap.inr O _ _

def rigToExt : G.RigExt →ₗ[O] G.VecExt :=
  Submodule.mapQ _ _ (LinearMap.fst O _ _) (by rintro _ ⟨b, rfl⟩; exact ⟨b, rfl⟩)

theorem rigToExt_surjective : Function.Surjective G.rigToExt := fun x => by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  exact ⟨G.rigMk (c, 0), rfl⟩

theorem exact_rigOfOmega_rigToExt : Function.Exact G.rigOfOmega G.rigToExt := fun x => by
  obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  constructor
  · intro h
    obtain ⟨b, rfl⟩ : c ∈ LinearMap.range G.cob := (Submodule.Quotient.mk_eq_zero _).1 h
    refine ⟨w - G.dFun b, Eq.symm ((Submodule.Quotient.eq _).2 (LinearMap.mem_range.2 ⟨b, ?_⟩))⟩
    simp
  · rintro ⟨w', h⟩
    rw [← h]
    exact (Submodule.Quotient.mk_eq_zero _).2 (zero_mem _)

theorem eq_zero_of_cobOne_eq_zero [IsDomain O] (hp : (p : O) ≠ 0) (n : ℕ) {b : G.A n}
    (hb : cobOne O _ b = 0) : b = 0 := by
  obtain ⟨h1, h2⟩ := mulBy_of_cobOne_eq_zero hb (p ^ n)
  rw [G.mulBy_pow_self, h2, map_zero, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ hp)

theorem rigOfOmega_injective [IsDomain O] (hp : (p : O) ≠ 0) :
    Function.Injective G.rigOfOmega := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hw
  have h0 : b = 0 := Subtype.ext (funext fun n => G.eq_zero_of_cobOne_eq_zero hp n
    (congrArg (fun x : G.cocycles × G.omega => x.1.1 n) hb))
  rw [h0, map_zero] at hb
  exact (congrArg Prod.snd hb).symm

variable {G H K}

def funsMap (f : G ⟶ H) : H.funs →ₗ[O] G.funs where
  toFun b := ⟨fun n => f.app n (b.1 n), fun n => (res_app f n _).trans (congrArg _ (b.2 n))⟩
  map_add' _ _ := Subtype.ext (funext fun n => map_add (f.app n) _ _)
  map_smul' _ _ := Subtype.ext (funext fun n => map_smul (f.app n) _ _)

def cocyclesMap (f : G ⟶ H) : H.cocycles →ₗ[O] G.cocycles where
  toFun c := ⟨fun n => pullbackTwo (f.app n) (c.1 n), fun n => ⟨pullTwo_mem _ (c.2 n).1, by
    rw [← pullTwo_comp, f.comm, pullTwo_comp, (c.2 n).2]⟩⟩
  map_add' _ _ := Subtype.ext (funext fun n => map_add (pullbackTwo (f.app n)) _ _)
  map_smul' _ _ := Subtype.ext (funext fun n => map_smul (pullbackTwo (f.app n)) _ _)

theorem cocyclesMap_cob (f : G ⟶ H) (b : H.funs) :
    cocyclesMap f (H.cob b) = G.cob (funsMap f b) :=
  Subtype.ext (funext fun _ => pullTwo_cobOne _ _)

def vecExtMap (f : G ⟶ H) : H.VecExt →ₗ[O] G.VecExt :=
  Submodule.mapQ _ _ (cocyclesMap f) (by
    rintro _ ⟨b, rfl⟩; exact ⟨funsMap f b, (cocyclesMap_cob f b).symm⟩)

variable [Fact p.Prime]

theorem omegaMap_dFun (f : G ⟶ H) (b : H.funs) :
    omegaMap G H f (H.dFun b) = G.dFun (funsMap f b) :=
  Subtype.ext (funext fun _ => cotMap_d _ _)

def rigExtMap (f : G ⟶ H) : H.RigExt →ₗ[O] G.RigExt :=
  Submodule.mapQ _ _ ((cocyclesMap f).prodMap (omegaMap G H f)) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨funsMap f b, Prod.ext (cocyclesMap_cob f b).symm (omegaMap_dFun f b).symm⟩)

@[simp] theorem rigExtMap_mk (f : G ⟶ H) (c : H.cocycles) (w : H.omega) :
    rigExtMap f (H.rigMk (c, w)) = G.rigMk (cocyclesMap f c, omegaMap G H f w) := rfl

@[simp] theorem rigExtMap_id : rigExtMap (𝟙 G) = LinearMap.id :=
  LinearMap.ext fun x => by
    obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    exact congrArg G.rigMk (Prod.ext (Subtype.ext (funext fun _ => pullTwo_id _))
      (LinearMap.congr_fun omegaMap_id w))

theorem rigExtMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    rigExtMap (f ≫ g) = rigExtMap f ∘ₗ rigExtMap g :=
  LinearMap.ext fun x => by
    obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    exact congrArg G.rigMk (Prod.ext (Subtype.ext (funext fun _ => pullTwo_comp _ _ _))
      (LinearMap.congr_fun (omegaMap_comp f g) w))

theorem rigExtMap_rigOfOmega (f : G ⟶ H) (w : H.omega) :
    rigExtMap f (H.rigOfOmega w) = G.rigOfOmega (omegaMap G H f w) :=
  congrArg G.rigMk (Prod.ext (map_zero (cocyclesMap f)) rfl)

theorem rigToExt_rigExtMap (f : G ⟶ H) (x : H.RigExt) :
    G.rigToExt (rigExtMap f x) = vecExtMap f (H.rigToExt x) := by
  obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

variable (G) in

abbrev LieUniv : Type := Module.Dual O G.RigExt

def lieUnivMap (f : G ⟶ H) : G.LieUniv →ₗ[O] H.LieUniv := (rigExtMap f).dualMap

variable (G) in

def lieUnivToLie : G.LieUniv →ₗ[O] G.Lie := G.rigOfOmega.dualMap

section Carry

variable (p O)

def digitFun (n : ℕ) : (const p O).A n := (constFun p O n).symm fun k => (k.val : O)

variable {p O}

end Carry

end PDivGroup

end GlobalTheory
