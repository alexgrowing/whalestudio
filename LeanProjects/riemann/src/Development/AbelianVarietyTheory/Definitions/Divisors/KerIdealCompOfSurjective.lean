import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv

namespace GlobalTheory.PDiv

section Conv

variable {R A B C D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]

section Points

variable [Bialgebra R A] [Bialgebra R C] [Algebra R B] [Algebra R D]

def pointsMap (B : Type*) [CommRing B] [Algebra R B] (f : C →ₐc[R] A) :
    WithConv (A →ₐ[R] B) →* WithConv (C →ₐ[R] B) where
  toFun x := toConv (x.ofConv.comp (f : C →ₐ[R] A))
  map_one' := by ext c; simp
  map_mul' x y := congrArg toConv (AlgHom.convMul_comp_bialgHom_distrib x y f)

@[simp] theorem ptsMap_ofConv (f : C →ₐc[R] A) (x : WithConv (A →ₐ[R] B)) :
    (pointsMap B f x).ofConv = x.ofConv.comp (f : C →ₐ[R] A) := rfl

def ptsPush (A : Type*) [CommRing A] [Bialgebra R A] (g : B →ₐ[R] D) :
    WithConv (A →ₐ[R] B) →* WithConv (A →ₐ[R] D) where
  toFun x := toConv (g.comp x.ofConv)
  map_one' := by ext c; simp
  map_mul' x y := congrArg toConv (AlgHom.comp_convMul_distrib g x y)

@[simp] theorem ptsPush_ofConv (g : B →ₐ[R] D) (x : WithConv (A →ₐ[R] B)) :
    (ptsPush A g x).ofConv = g.comp x.ofConv := rfl

theorem convMul_apply_groupLike (x y : WithConv (A →ₐ[R] B)) {u : A} (hu : IsGroupLikeElem R u) :
    (x * y) u = x u * y u := by
  rw [AlgHom.convMul_apply, hu.comul_eq_tmul_self]; simp

theorem convPow_apply_groupLike (x : WithConv (A →ₐ[R] B)) {u : A} (hu : IsGroupLikeElem R u)
    (n : ℕ) : (x ^ n) u = x u ^ n := by
  induction n with
  | zero => simp [hu.counit_eq_one]
  | succ n ih => rw [pow_succ, convMul_apply_groupLike _ _ hu, ih, pow_succ]

end Points

variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]

def toPts [IsCocomm R C] : WithConv (C →ₐc[R] A) →* WithConv (C →ₐ[R] A) where
  toFun f := toConv (f.ofConv : C →ₐ[R] A)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem toPts_ofConv [IsCocomm R C] (f : WithConv (C →ₐc[R] A)) :
    (toPts f).ofConv = (f.ofConv : C →ₐ[R] A) := rfl

theorem toPts_injective [IsCocomm R C] :
    Function.Injective (toPts : WithConv (C →ₐc[R] A) → _) := fun _ _ h =>
  ofConv_injective (BialgHom.coe_toAlgHom_injective (congrArg ofConv h))

def precomp [IsCocomm R C] [IsCocomm R D] (A : Type*) [CommRing A] [Bialgebra R A]
    (h : D →ₐc[R] C) : WithConv (C →ₐc[R] A) →* WithConv (D →ₐc[R] A) where
  toFun f := toConv (f.ofConv.comp h)
  map_one' := toPts_injective (map_one (pointsMap A h))
  map_mul' f g := toPts_injective (map_mul (pointsMap A h) (toPts f) (toPts g))

@[simp] theorem precomp_ofConv [IsCocomm R C] [IsCocomm R D] (h : D →ₐc[R] C)
    (f : WithConv (C →ₐc[R] A)) : (precomp A h f).ofConv = f.ofConv.comp h := rfl

def postcomp (C : Type*) [CommRing C] [Bialgebra R C] [IsCocomm R C] (h : A →ₐc[R] B) :
    WithConv (C →ₐc[R] A) →* WithConv (C →ₐc[R] B) where
  toFun f := toConv (h.comp f.ofConv)
  map_one' := toPts_injective (map_one (ptsPush C (h : A →ₐ[R] B)))
  map_mul' f g := toPts_injective (map_mul (ptsPush C (h : A →ₐ[R] B)) (toPts f) (toPts g))

@[simp] theorem postcomp_ofConv [IsCocomm R C] (h : A →ₐc[R] B)
    (f : WithConv (C →ₐc[R] A)) : (postcomp C h f).ofConv = h.comp f.ofConv := rfl

variable (R A) in

def mulBy [IsCocomm R A] (n : ℕ) : A →ₐc[R] A := (toConv (BialgHom.id R A) ^ n).ofConv

theorem comp_mulBy_pts [IsCocomm R A] {E : Type*} [CommRing E] [Algebra R E] (x : A →ₐ[R] E)
    (n : ℕ) : x.comp (mulBy R A n : A →ₐ[R] A) = (toConv x ^ n).ofConv := by
  have h := map_pow ((ptsPush A x).comp toPts) (toConv (BialgHom.id R A)) n
  exact congrArg ofConv h

theorem comp_mulBy [IsCocomm R C] (f : C →ₐc[R] A) (n : ℕ) :
    f.comp (mulBy R C n) = (toConv f ^ n).ofConv :=
  congrArg ofConv (map_pow (postcomp C f) (toConv (BialgHom.id R C)) n)

theorem mulBy_comp [IsCocomm R C] [IsCocomm R A] (f : C →ₐc[R] A) (n : ℕ) :
    (mulBy R A n).comp f = (toConv f ^ n).ofConv :=
  congrArg ofConv (map_pow (precomp A f) (toConv (BialgHom.id R A)) n)

theorem map_mulBy [IsCocomm R C] [IsCocomm R A] (f : C →ₐc[R] A) (n : ℕ) (c : C) :
    f (mulBy R C n c) = mulBy R A n (f c) :=
  DFunLike.congr_fun ((comp_mulBy f n).trans (mulBy_comp f n).symm) c

theorem mulBy_mulBy [IsCocomm R A] (m n : ℕ) (a : A) :
    mulBy R A m (mulBy R A n a) = mulBy R A (m * n) a := by
  have h := comp_mulBy (mulBy R A m) n
  rw [mulBy, toConv_ofConv, ← pow_mul] at h
  exact DFunLike.congr_fun h a

theorem mulBy_groupLike [IsCocomm R A] (n : ℕ) {u : A} (hu : IsGroupLikeElem R u) :
    mulBy R A n u = u ^ n := by
  have h := DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id R A) n) u
  exact h.trans (convPow_apply_groupLike (toConv (AlgHom.id R A)) hu n)

variable (R A) in

abbrev augIdeal : Ideal A := RingHom.ker (counitAlgHom R A)

abbrev kerIdeal (f : C →ₐc[R] A) : Ideal A := Ideal.map (f : C →ₐ[R] A) (augIdeal R C)

variable (R A) in

abbrev torsionIdeal [IsCocomm R A] (n : ℕ) : Ideal A := kerIdeal (mulBy R A n)

theorem kerIdeal_le_ker_iff (f : C →ₐc[R] A) {E : Type*} [CommRing E] [Algebra R E]
    (x : A →ₐ[R] E) :
    kerIdeal f ≤ RingHom.ker x ↔ ∀ c, x (f c) = algebraMap R E (counit c) := by
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · intro h c
    have := h (x := c - algebraMap R C (counit c)) (by simp [RingHom.mem_ker])
    rw [Ideal.mem_comap, RingHom.mem_ker, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes,
      sub_eq_zero] at this
    exact this
  · intro h c hc
    have hc' : counit (R := R) c = 0 := hc
    simp [RingHom.mem_ker, h, hc']

theorem torsionIdeal_le_ker_iff [IsCocomm R A] (n : ℕ) {E : Type*} [CommRing E] [Algebra R E]
    (x : A →ₐ[R] E) : torsionIdeal R A n ≤ RingHom.ker x ↔ toConv x ^ n = 1 := by
  rw [kerIdeal_le_ker_iff]
  have h := comp_mulBy_pts x n
  constructor
  · intro h'
    refine ofConv_injective (h.symm.trans (AlgHom.ext h'))
  · intro h' c
    rw [h'] at h
    exact DFunLike.congr_fun h c

theorem kerIdeal_of_surjective {f : C →ₐc[R] A} (hf : Function.Surjective f) :
    kerIdeal f = augIdeal R A := by
  refine le_antisymm ((kerIdeal_le_ker_iff f _).2 fun c => by simp) fun a ha => ?_
  obtain ⟨c, rfl⟩ := hf a
  refine Ideal.mem_map_of_mem _ ?_
  simpa [RingHom.mem_ker] using ha

theorem kerIdeal_comp (g : A →ₐc[R] B) (f : C →ₐc[R] A) :
    kerIdeal (g.comp f) = Ideal.map (g : A →ₐ[R] B) (kerIdeal f) :=
  (Ideal.map_mapₐ (f : C →ₐ[R] A) (g : A →ₐ[R] B)).symm

theorem kerIdeal_comp_of_surjective (g : A →ₐc[R] B) {f : C →ₐc[R] A}
    (hf : Function.Surjective f) : kerIdeal (g.comp f) = kerIdeal g := by
  rw [kerIdeal_comp, kerIdeal_of_surjective hf]

theorem map_torsionIdeal [IsCocomm R C] [IsCocomm R A] {f : C →ₐc[R] A}
    (hf : Function.Surjective f) (n : ℕ) :
    Ideal.map (f : C →ₐ[R] A) (torsionIdeal R C n) = torsionIdeal R A n := by
  rw [← kerIdeal_comp, comp_mulBy, ← mulBy_comp, kerIdeal_comp_of_surjective _ hf]

theorem torsionIdeal_le_of_dvd [IsCocomm R A] {m n : ℕ} (h : m ∣ n) :
    torsionIdeal R A n ≤ torsionIdeal R A m := by
  obtain ⟨k, rfl⟩ := h
  have h1 := (torsionIdeal_le_ker_iff m (Ideal.Quotient.mkₐ R (torsionIdeal R A m))).1
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h2 := (torsionIdeal_le_ker_iff (m * k) (Ideal.Quotient.mkₐ R (torsionIdeal R A m))).2
    (by rw [pow_mul, h1, one_pow])
  exact fun a ha => Ideal.Quotient.eq_zero_iff_mem.1 (h2 ha)

def liftSurj (i : A →ₐc[R] B) (hi : Function.Surjective i) (f : A →ₐc[R] C)
    (h : RingHom.ker i ≤ RingHom.ker f) : B →ₐc[R] C :=
  .ofAlgHom (AlgHom.liftOfSurjective (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h)
    (AlgHom.ext fun b => by
      obtain ⟨a, rfl⟩ := hi b
      have := AlgHom.liftOfSurjective_apply (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h a
      simp at this
      simp [this])
    (AlgHom.ext fun b => by
      obtain ⟨a, rfl⟩ := hi b
      have h1 := AlgHom.liftOfSurjective_comp (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h
      have h2 := AlgHom.liftOfSurjective_apply (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h a
      have h3 := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom i) a
      have h4 := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom f) a
      generalize AlgHom.liftOfSurjective (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h = g at h1 h2 ⊢
      change Algebra.TensorProduct.map g g ((comulAlgHom R B).comp (i : A →ₐ[R] B) a) =
        comulAlgHom R C (g ((i : A →ₐ[R] B) a))
      rw [h2]
      refine (congrArg (Algebra.TensorProduct.map g g) h3).symm.trans (Eq.trans ?_ h4)
      change Algebra.TensorProduct.map g g (Algebra.TensorProduct.map (i : A →ₐ[R] B)
        (i : A →ₐ[R] B) (comulAlgHom R A a)) = _
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, h1]
      rfl)

@[simp] theorem liftSurj_apply (i : A →ₐc[R] B) (hi : Function.Surjective i) (f : A →ₐc[R] C)
    (h : RingHom.ker i ≤ RingHom.ker f) (a : A) : liftSurj i hi f h (i a) = f a :=
  AlgHom.liftOfSurjective_apply (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h a

variable (R A) in

abbrev Cot : Type _ := AugCot (counitAlgHom R A)

variable (R) in

abbrev dUnit (a : A) : Cot R A := AugCot.d (counitAlgHom R A) a

def cotMap (f : C →ₐc[R] A) : Cot R C →ₗ[R] Cot R A :=
  AugCot.map (f : C →ₐ[R] A) (BialgHomClass.counitAlgHom_comp f)

@[simp] theorem cotMap_d (f : C →ₐc[R] A) (c : C) : cotMap f (dUnit R c) = dUnit R (f c) :=
  AugCot.map_d _ _ c

theorem cotMap_comp (g : A →ₐc[R] B) (f : C →ₐc[R] A) :
    cotMap (g.comp f) = cotMap g ∘ₗ cotMap f :=
  AugCot.hom_ext fun c => by simp

@[simp] theorem cotMap_id : cotMap (BialgHom.id R A) = LinearMap.id :=
  AugCot.hom_ext fun c => by simp

theorem cotMap_one [IsCocomm R C] : cotMap (1 : WithConv (C →ₐc[R] A)).ofConv = 0 :=
  AugCot.hom_ext fun c => by
    rw [cotMap_d]
    exact AugCot.d_algebraMap _ _

theorem cotMap_mul [IsCocomm R C] (f g : WithConv (C →ₐc[R] A)) :
    cotMap (f * g).ofConv = cotMap f.ofConv + cotMap g.ofConv :=
  AugCot.hom_ext fun c => by
    have r := Coalgebra.Repr.arbitrary R c
    have h : (f * g).ofConv c = ∑ i ∈ r.index, f.ofConv (r.left i) * g.ofConv (r.right i) :=
      r.convMul_apply (toConv f.ofConv.toLinearMap) (toConv g.ofConv.toLinearMap)
    have h1 := congrArg (fun x => dUnit R (g.ofConv x)) (Coalgebra.sum_counit_smul r)
    have h2 : ∑ i ∈ r.index, counit (R := R) (r.right i) • r.left i = c := by
      have := congrArg (TensorProduct.rid R C) (Coalgebra.sum_tmul_counit_eq r)
      simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using this
    have h3 := congrArg (fun x => dUnit R (f.ofConv x)) h2
    simp only [map_sum, map_smul] at h1 h3
    rw [LinearMap.add_apply, cotMap_d, cotMap_d, cotMap_d, h, ← h1, ← h3, add_comm,
      ← Finset.sum_add_distrib, dUnit, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AugCot.d_mul]
    simp

theorem cotMap_pow [IsCocomm R C] (f : WithConv (C →ₐc[R] A)) (n : ℕ) :
    cotMap (f ^ n).ofConv = n • cotMap f.ofConv := by
  induction n with
  | zero => rw [pow_zero, cotMap_one, zero_smul]
  | succ n ih => rw [pow_succ, cotMap_mul, ih, succ_nsmul]

theorem dUnit_mul_groupLike {u v : A} (hu : IsGroupLikeElem R u) (hv : IsGroupLikeElem R v) :
    dUnit R (u * v) = dUnit R u + dUnit R v := by
  rw [dUnit, AugCot.d_mul]
  simp [hu.counit_eq_one, hv.counit_eq_one, add_comm]

section Dual

variable [Module.Finite R A] [Module.Projective R A] [Module.Finite R C] [Module.Projective R C]
  [IsCocomm R A] [IsCocomm R C]

variable (R A C) in

def dualMonoidHom :
    WithConv (C →ₐc[R] A) →* WithConv (CartierDual R A →ₐc[R] CartierDual R C) where
  toFun f := toConv (CartierDual.map f.ofConv)
  map_one' := ofConv_injective <| BialgHom.ext fun φ => CartierDual.ext_apply fun c => by
    change φ.ofConv (algebraMap R A (counit c)) = (algebraMap R (CartierDual R C) (φ.ofConv 1)) c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul]
    change _ = φ.ofConv 1 * counit c
    rw [smul_eq_mul, mul_comm]
  map_mul' f g := ofConv_injective <| BialgHom.ext fun φ => CartierDual.ext_apply fun c => by
    have r := Coalgebra.Repr.arbitrary R c
    have h : (f * g).ofConv c = ∑ i ∈ r.index, f.ofConv (r.left i) * g.ofConv (r.right i) :=
      r.convMul_apply (toConv f.ofConv.toLinearMap) (toConv g.ofConv.toLinearMap)
    change φ.ofConv ((f * g).ofConv c) = (LinearMap.mul' R _ (TensorProduct.map
      (CartierDual.transpose f.ofConv.toLinearMap) (CartierDual.transpose g.ofConv.toLinearMap)
      (comul φ))) c
    rw [CartierDual.mul'_apply, CartierDual.pair_map_transpose, h, ← r.eq]
    simp only [map_sum, TensorProduct.map_tmul, CartierDual.pair_comul_tmul]
    rfl

omit [IsCocomm R A] in

@[simp] theorem dualMonoidHom_ofConv (f : WithConv (C →ₐc[R] A)) :
    (dualMonoidHom R A C f).ofConv = CartierDual.map f.ofConv := rfl

theorem dual_mulBy (n : ℕ) : CartierDual.map (mulBy R A n) = mulBy R (CartierDual R A) n :=
  congrArg ofConv (map_pow (dualMonoidHom R A A) (toConv (BialgHom.id R A)) n)

end Dual

end Conv

section Mu

variable (R : Type*) [CommRing R] (m : ℕ)

def muT : AddMonoidAlgebra R (ZMod m) := AddMonoidAlgebra.single 1 1

theorem isGroupLikeElem_muT : IsGroupLikeElem R (muT R m) :=
  AddMonoidAlgebra.isGroupLikeElem_single_one _

theorem muT_pow (k : ℕ) : muT R m ^ k = AddMonoidAlgebra.single (k : ZMod m) 1 := by
  simp [muT, AddMonoidAlgebra.single_pow]

theorem muT_pow_self : muT R m ^ m = 1 := by
  rw [muT_pow, ZMod.natCast_self]; rfl

variable {R m} [NeZero m] {B : Type*} [CommRing B] [Algebra R B]

theorem mu_algHom_ext {x y : AddMonoidAlgebra R (ZMod m) →ₐ[R] B}
    (h : x (muT R m) = y (muT R m)) : x = y :=
  AddMonoidAlgebra.algHom_ext (fun k => by
    rw [← ZMod.natCast_zmod_val k, ← muT_pow R m, map_pow, map_pow, h]) (Subsingleton.elim _ _)

variable (R) in

def muPoint (u : B) (hu : u ^ m = 1) : AddMonoidAlgebra R (ZMod m) →ₐ[R] B :=
  AddMonoidAlgebra.lift R B (ZMod m)
    { toFun := fun k => u ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun k l => by
        rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hu, pow_add] }

theorem muPoint_single (u : B) (hu : u ^ m = 1) (k : ZMod m) :
    muPoint R u hu (AddMonoidAlgebra.single k 1) = u ^ k.val := by
  simp [muPoint]

@[simp] theorem muPoint_muT (u : B) (hu : u ^ m = 1) : muPoint R u hu (muT R m) = u := by
  have h : (1 : ZMod m).val = 1 % m := by rw [← ZMod.val_natCast, Nat.cast_one]
  rw [muT, muPoint_single, h, ← pow_eq_pow_mod _ hu, pow_one]

def muChar {A : Type*} [CommRing A] [Bialgebra R A] (u : A) (hg : IsGroupLikeElem R u)
    (hu : u ^ m = 1) : AddMonoidAlgebra R (ZMod m) →ₐc[R] A :=
  .ofAlgHom (muPoint R u hu)
    (mu_algHom_ext (by simp [hg.counit_eq_one, (isGroupLikeElem_muT R m).counit_eq_one]))
    (mu_algHom_ext (by
      simp [hg.comul_eq_tmul_self, (isGroupLikeElem_muT R m).comul_eq_tmul_self]))

@[simp] theorem muChar_muT {A : Type*} [CommRing A] [Bialgebra R A] (u : A)
    (hg : IsGroupLikeElem R u) (hu : u ^ m = 1) : muChar u hg hu (muT R m) = u :=
  muPoint_muT u hu

theorem mu_bialgHom_ext {A : Type*} [CommRing A] [Bialgebra R A]
    {x y : AddMonoidAlgebra R (ZMod m) →ₐc[R] A} (h : x (muT R m) = y (muT R m)) : x = y :=
  BialgHom.coe_toAlgHom_injective (mu_algHom_ext h)

end Mu

section PPow

variable {p : ℕ} [Fact p.Prime] {M : Type*} [Monoid M]

def digit (n : ℕ) (a : ℤ_[p]) : ℕ := (PadicInt.toZModPow n a).val

theorem cast_digit (n : ℕ) (a : ℤ_[p]) :
    (digit n a : ZMod (p ^ n)) = PadicInt.toZModPow n a := ZMod.natCast_zmod_val _

theorem pow_dvd_sub_digit (n : ℕ) (a : ℤ_[p]) : (p : ℤ_[p]) ^ n ∣ a - digit n a := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_natCast, cast_digit, sub_self]

theorem pow_digit_eq {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) {a : ℤ_[p]} {k : ℕ}
    (h : (k : ZMod (p ^ n)) = PadicInt.toZModPow n a) : x ^ digit n a = x ^ k := by
  rw [digit, ← h, ZMod.val_natCast, ← pow_eq_pow_mod _ hx]

theorem pow_digit_natCast {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) (k : ℕ) :
    x ^ digit n (k : ℤ_[p]) = x ^ k := pow_digit_eq hx (map_natCast _ k).symm

theorem pow_digit_one {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) : x ^ digit n (1 : ℤ_[p]) = x :=
  (pow_digit_eq hx (k := 1) (by simp)).trans (pow_one x)

@[simp] theorem digit_zero (n : ℕ) : digit n (0 : ℤ_[p]) = 0 := by simp [digit]

theorem pow_digit_add {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) (a b : ℤ_[p]) :
    x ^ digit n (a + b) = x ^ digit n a * x ^ digit n b := by
  rw [← pow_add]
  exact pow_digit_eq hx (by rw [Nat.cast_add, cast_digit, cast_digit, map_add])

theorem pow_digit_mul {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) (a b : ℤ_[p]) :
    x ^ digit n (a * b) = (x ^ digit n b) ^ digit n a := by
  rw [← pow_mul]
  exact pow_digit_eq hx (by rw [Nat.cast_mul, cast_digit, cast_digit, map_mul, mul_comm])

theorem pow_digit_succ {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) (a : ℤ_[p]) :
    x ^ digit (n + 1) a = x ^ digit n a := by
  refine (pow_digit_eq hx ?_).symm
  rw [digit, ZMod.natCast_val]
  exact PadicInt.cast_toZModPow n (n + 1) n.le_succ a

end PPow

end GlobalTheory.PDiv
