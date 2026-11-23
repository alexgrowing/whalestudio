import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice

noncomputable section

namespace GlobalTheory.Cusp

open scoped TensorProduct
open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

section Perp

variable {V : HSpace E}

theorem mem_perp {W : Submodule E V.V} {y : V.V} : y ∈ perp V W ↔ ∀ x ∈ W, V.hD y x = 0 := by
  simp [perp, Submodule.mem_iInf, HSpace.hD]

theorem perp_anti {A B : Submodule E V.V} (h : A ≤ B) : perp V B ≤ perp V A :=
  fun _ hy => mem_perp.2 fun x hx => mem_perp.1 hy x (h hx)

@[simp] theorem perp_bot : perp V ⊥ = ⊤ :=
  eq_top_iff.2 fun y _ => mem_perp.2 fun x hx => by simp [(Submodule.mem_bot E).1 hx, HSpace.hD]

@[simp] theorem perp_top : perp V ⊤ = ⊥ :=
  eq_bot_iff.2 fun y hy => V.nondeg.2 y fun x => mem_perp.1 hy x trivial

theorem le_perp_of_le {A B : Submodule E V.V} (h : A ≤ B) (hB : B ≤ perp V B) : A ≤ perp V A :=
  h.trans (hB.trans (perp_anti h))

end Perp

section Ext

variable (V : HSpace E) (R : Type) [CommRing R] [Algebra F R]

omit [NumberField F]

theorem coordR_mem {W : Submodule E V.V} {x : V.V} (hx : x ∈ W) : coordR (F := F) V R x ∈ extSub (F := F) V R W :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem extSub_mono {A B : Submodule E V.V} (h : A ≤ B) : extSub (F := F) V R A ≤ extSub (F := F) V R B :=
  Submodule.span_mono (Set.image_mono h)

theorem mulVec_mem_extSub {W : Submodule E V.V} {r : ℕ} (M : Matrix (Fin V.rank) (Fin r) E)
    (h : ∀ k, vecOf V (Mᵀ k) ∈ W) (a : Fin r → R ⊗[F] E) :
    M.map (inclR (F := F) R) *ᵥ a ∈ extSub (F := F) V R W :=
  extSub_mono V R (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h k) : colSpan V M ≤ W)
    ((mem_extSub_colSpan V R M _).2 ⟨a, rfl⟩)

theorem map_mulVec_coordR {r : ℕ} (M : Matrix (Fin r) (Fin V.rank) E) (x : V.V) :
    M.map (inclR (F := F) R) *ᵥ coordR (F := F) V R x = fun i => inclR R ((M *ᵥ fun j => V.frame.repr x j) i) :=
  funext fun i => (RingHom.map_mulVec (inclR (F := F) R) M (fun j => V.frame.repr x j) i).symm

theorem mem_extSub_iff_of_ker {W : Submodule E V.V} {r : ℕ} (T : Matrix (Fin r) (Fin V.rank) E)
    (P : Matrix (Fin V.rank) (Fin r) E) (hP : T * P * T = T)
    (hW : ∀ x, x ∈ W ↔ (T *ᵥ fun j => V.frame.repr x j) = 0) (y : Fin V.rank → R ⊗[F] E) :
    y ∈ extSub (F := F) V R W ↔ T.map (inclR (F := F) R) *ᵥ y = 0 := by
  constructor
  · intro hy
    refine (Submodule.span_le (p := LinearMap.ker (T.map (inclR (F := F) R)).mulVecLin)).2 ?_ hy
    rintro _ ⟨x, hx, rfl⟩
    change T.map (inclR (F := F) R) *ᵥ coordR V R x = 0
    rw [map_mulVec_coordR, (hW x).1 hx]
    funext i; simp
  · intro hy
    have h := mulVec_mem_extSub (F := F) V R (W := W) (1 - P * T) (fun k => (hW _).2 (by
      have : T * (1 - P * T) = 0 := by rw [Matrix.mul_sub, ← Matrix.mul_assoc, hP, Matrix.mul_one, sub_self]
      funext i
      simp only [repr_vecOf]
      exact congrFun (congrFun this i) k)) y
    rwa [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.sub_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero, sub_zero] at h

theorem exists_cut (W : Submodule E V.V) : ∃ T : Matrix (Fin V.rank) (Fin V.rank) E, T * 1 * T = T ∧
    ∀ x, x ∈ W ↔ (T *ᵥ fun j => V.frame.repr x j) = 0 := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  let π : V.V →ₗ[E] V.V := U.projection W hU.symm
  refine ⟨LinearMap.toMatrix V.frame V.frame π, ?_, fun x => ?_⟩
  · rw [Matrix.mul_one, ← LinearMap.toMatrix_mul, (Submodule.isIdempotentElem_projection hU.symm).eq]
  · have := LinearMap.toMatrix_mulVec_repr V.frame V.frame π x
    rw [show (fun j => V.frame.repr x j) = ⇑(V.frame.repr x) from rfl, this, Finsupp.coe_eq_zero,
      LinearEquiv.map_eq_zero_iff, Submodule.projection_apply_eq_zero_iff]

@[simp] theorem extSub_bot : extSub (F := F) V R ⊥ = ⊥ :=
  Submodule.span_eq_bot.2 (by rintro _ ⟨x, hx, rfl⟩; funext i; simp [coordR, (Submodule.mem_bot E).1 hx])

@[simp] theorem extSub_top : extSub (F := F) V R ⊤ = ⊤ :=
  eq_top_iff.2 fun y _ => (mem_extSub_iff_of_ker V R (r := 0) 0 0 (by simp) (fun _ => by simp [eq_iff_true_of_subsingleton]) y).2
    (Subsingleton.elim _ _)

theorem coordR_mem_iff [Nontrivial R] {W : Submodule E V.V} {x : V.V} :
    coordR (F := F) V R x ∈ extSub (F := F) V R W ↔ x ∈ W := by
  obtain ⟨T, h1, h2⟩ := exists_cut V W
  have hi : Function.Injective (inclR (F := F) (E := E) R) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F R).injective
  rw [mem_extSub_iff_of_ker V R T 1 h1 h2, map_mulVec_coordR, h2]
  exact ⟨fun h => funext fun i => hi ((congrFun h i).trans (map_zero _).symm), fun h => by rw [h]; funext i; simp⟩

variable {R} {R' : Type} [CommRing R'] [Algebra F R']

def mapVec (φ : R →ₐ[F] R') (y : Fin V.rank → R ⊗[F] E) : Fin V.rank → R' ⊗[F] E :=
  fun i => Algebra.TensorProduct.map φ (AlgHom.id F E) (y i)

@[simp] theorem mapVec_coordR (φ : R →ₐ[F] R') (x : V.V) : mapVec V φ (coordR V R x) = coordR V R' x := by
  funext i; simp [mapVec, coordR, inclR]

theorem mapVec_sub (φ : R →ₐ[F] R') (y z : Fin V.rank → R ⊗[F] E) :
    mapVec V φ (y - z) = mapVec V φ y - mapVec V φ z := funext fun _ => map_sub _ _ _

theorem map_mulVec_mapVec (φ : R →ₐ[F] R') (T : Matrix (Fin V.rank) (Fin V.rank) E) (y : Fin V.rank → R ⊗[F] E) :
    T.map (inclR (F := F) R') *ᵥ mapVec V φ y = mapVec V φ (T.map (inclR (F := F) R) *ᵥ y) := by
  funext i
  refine Eq.trans ?_ (RingHom.map_mulVec (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom _ y i).symm
  congr 1
  ext a b
  simp [inclR]

theorem mapVec_mem (φ : R →ₐ[F] R') {W : Submodule E V.V} {y : Fin V.rank → R ⊗[F] E}
    (hy : y ∈ extSub (F := F) V R W) : mapVec V φ y ∈ extSub (F := F) V R' W := by
  obtain ⟨T, h1, h2⟩ := exists_cut V W
  rw [mem_extSub_iff_of_ker V _ T 1 h1 h2] at hy ⊢
  rw [map_mulVec_mapVec, hy]
  funext i; simp [mapVec]

omit [NumberField E] [StarRing E] in

theorem repr_map {ι : Type} (b : Module.Basis ι F E) (φ : R →ₐ[F] R') (u : R ⊗[F] E) (j : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) u) j =
      φ ((Algebra.TensorProduct.basis R b).repr u j) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a e => simp

end Ext

section Form

variable (hc : CMData F E) (V : HSpace E) {R : Type} [CommRing R] [Algebra F R]

theorem hR_eq (x y : Fin V.rank → R ⊗[F] E) : hR R hc.sig V.gram x y =
    (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (x i)) ⬝ᵥ (V.gram.map (inclR (F := F) R) *ᵥ y) := by
  simp only [hR, hform, JR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hR_mulVec {r : ℕ} (M : Matrix (Fin V.rank) (Fin r) (R ⊗[F] E)) (a : Fin r → R ⊗[F] E)
    (y : Fin V.rank → R ⊗[F] E) : hR R hc.sig V.gram (M *ᵥ a) y = (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (a i)) ⬝ᵥ
      ((cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig) M * V.gram.map (inclR (F := F) R)) *ᵥ y) := by
  rw [hR_eq, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (cT _ M)]
  congr 1
  funext i
  exact (RingHom.map_mulVec _ M a i).trans (congrFun (Matrix.vecMul_transpose _ _).symm i)

theorem hR_act (g : HA R hc.sig V.gram) (x y : Fin V.rank → R ⊗[F] E) :
    hR R hc.sig V.gram (act hc V g x) (act hc V g y) = hR R hc.sig V.gram x y := by
  have hg : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig) (HA.mat R hc.sig V.gram g).1 * V.gram.map (inclR (F := F) R) *
    (HA.mat R hc.sig V.gram g).1 = V.gram.map (inclR (F := F) R) := g.2
  rw [act, hR_mulVec, act, Matrix.mulVec_mulVec, hg, hR_eq]

theorem hR_act_sub (g : HA R hc.sig V.gram) (x y : Fin V.rank → R ⊗[F] E) :
    hR R hc.sig V.gram x (act hc V g y - y) = hR R hc.sig V.gram (act hc V g⁻¹ x - x) y := by
  have h := hR_act hc V g (act hc V g⁻¹ x) y
  rw [← act_mul, mul_inv_cancel, act_one] at h
  simp only [hR_eq, Matrix.mulVec_sub, dotProduct_sub, Pi.sub_apply, map_sub] at h ⊢
  rw [h, ← sub_dotProduct]
  rfl

theorem mem_extSub_perp {W : Submodule E V.V} {y : Fin V.rank → R ⊗[F] E} :
    y ∈ extSub (F := F) V R (perp V W) ↔ ∀ x ∈ extSub (F := F) V R W, hR R hc.sig V.gram x y = 0 := by
  obtain ⟨r, C, hC, rfl⟩ := exists_colSpan V W
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective C.mulVecLin
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 hC))
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r) (Fin V.rank) E, L * C = 1 :=
    ⟨LinearMap.toMatrix' l, by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]; exact hl⟩
  have hT : cT (hc.sig : E →+* E) C * V.gram * (V.gram⁻¹ * cT (hc.sig : E →+* E) L) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (gram_det_isUnit V), ← cT_mul, hL, cT_one]
  rw [mem_extSub_iff_of_ker V R _ _ (by rw [hT, Matrix.one_mul]) (mem_perp_colSpan hc V C), Matrix.map_mul,
    ← GlobalTheory.AutFunCounterexample.cT_map_gen]
  simp only [mem_extSub_colSpan]
  constructor
  · rintro h _ ⟨a, rfl⟩
    rw [hR_mulVec, h, dotProduct_zero]
  · intro h
    funext k
    have := h _ ⟨Pi.single k 1, rfl⟩
    rw [hR_mulVec] at this
    simpa [dotProduct, Pi.single_apply, apply_ite] using this

end Form

section Step

variable (hc : CMData F E) (V : HSpace E) (R : Type) [CommRing R] [Algebra F R]

def trivOn (A B : Submodule E V.V) : Subgroup (HA R hc.sig V.gram) where
  carrier := {g | g ∈ parab hc V R A ∧ ∀ y ∈ extSub (F := F) V R B, act hc V g y - y ∈ extSub (F := F) V R A}
  one_mem' := ⟨one_mem _, fun y _ => by rw [act_one, sub_self]; exact zero_mem _⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun y hy => by
    have e : act hc V (a * b) y - y = act hc V a (act hc V b y - y) + (act hc V a y - y) := by
      rw [act_sub, act_mul]; abel
    rw [e]; exact add_mem ((ha.1 _).1 (hb.2 y hy)) (ha.2 y hy)⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun y hy => by
    have e : act hc V a⁻¹ y - y = -act hc V a⁻¹ (act hc V a y - y) := by rw [act_sub, act_inv]; abel
    rw [e]; exact neg_mem ((inv_mem ha.1 _).1 (ha.2 y hy))⟩

variable {hc V R} {A B W : Submodule E V.V} {g : HA R hc.sig V.gram}

theorem mem_parab_iff_maps : g ∈ parab hc V R W ↔ ∀ y ∈ extSub (F := F) V R W, act hc V g y ∈ extSub (F := F) V R W := by
  refine ⟨fun h y => (h y).1, fun h y => ⟨h y, fun hy => ?_⟩⟩
  let f := (HA.mat R hc.sig V.gram g).1.mulVecLin
  have hs : Function.Surjective ((extSub (F := F) V R W).mapQ (extSub (F := F) V R W) f h) := fun q => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨Submodule.Quotient.mk (act hc V g⁻¹ z), congrArg Submodule.Quotient.mk ?_⟩
    change act hc V g _ = z
    rw [← act_mul, mul_inv_cancel, act_one]
  refine (Submodule.Quotient.mk_eq_zero _).1 (OrzechProperty.injective_of_surjective_endomorphism _ hs ?_)
  rw [map_zero]
  exact (Submodule.Quotient.mk_eq_zero _).2 hy

theorem mem_parab : g ∈ parab hc V R W ↔ ∀ x ∈ W, act hc V g (coordR V R x) ∈ extSub (F := F) V R W :=
  mem_parab_iff_maps.trans ⟨fun h _ hx => h _ (coordR_mem V R hx), fun h _ hy =>
    (Submodule.span_le (p := (extSub (F := F) V R W).comap (HA.mat R hc.sig V.gram g).1.mulVecLin)).2
      (by rintro _ ⟨x, hx, rfl⟩; exact h x hx) hy⟩

@[simp] theorem parab_bot : parab hc V R ⊥ = ⊤ :=
  eq_top_iff.2 fun g _ => mem_parab_iff_maps.2 fun y hy => by
    rw [extSub_bot, Submodule.mem_bot] at hy ⊢
    rw [hy, act, Matrix.mulVec_zero]

theorem parab_le_perp : parab hc V R W ≤ parab hc V R (perp V W) := fun g hg =>
  mem_parab_iff_maps.2 fun y hy => (mem_extSub_perp hc V).2 fun x hx => by
    rw [← hR_act hc V g⁻¹, act_inv]
    exact (mem_extSub_perp hc V).1 hy _ ((inv_mem hg x).1 hx)

theorem mem_trivOn_iff_maps (h : A ≤ B) :
    g ∈ trivOn hc V R A B ↔ ∀ y ∈ extSub (F := F) V R B, act hc V g y - y ∈ extSub (F := F) V R A :=
  ⟨fun h => h.2, fun h' => ⟨mem_parab_iff_maps.2 fun y hy => by
    simpa using add_mem (h' y (extSub_mono V R h hy)) hy, h'⟩⟩

theorem mem_trivOn (h : A ≤ B) : g ∈ trivOn hc V R A B ↔
    ∀ x ∈ B, act hc V g (coordR V R x) - coordR V R x ∈ extSub (F := F) V R A :=
  (mem_trivOn_iff_maps h).trans ⟨fun h _ hx => h _ (coordR_mem V R hx), fun h _ hy =>
    ((Submodule.span_le (p := (extSub (F := F) V R A).comap
      ((HA.mat R hc.sig V.gram g).1.mulVecLin - LinearMap.id))).2 (by rintro _ ⟨x, hx, rfl⟩; exact h x hx) hy :)⟩

theorem trivOn_le_parab (h1 : A ≤ W) (h2 : W ≤ B) : trivOn hc V R A B ≤ parab hc V R W := fun g hg =>
  mem_parab_iff_maps.2 fun y hy => by simpa using add_mem (extSub_mono V R h1 (hg.2 y (extSub_mono V R h2 hy))) hy

theorem trivOn_mono {A' B' : Submodule E V.V} (h1 : A ≤ A') (h2 : A' ≤ B') (h3 : B' ≤ B) :
    trivOn hc V R A B ≤ trivOn hc V R A' B' := fun _ hg =>
  (mem_trivOn_iff_maps h2).2 fun y hy => extSub_mono V R h1 (hg.2 y (extSub_mono V R h3 hy))

theorem trivOn_le_trivOn_perp (h : A ≤ B) : trivOn hc V R A B ≤ trivOn hc V R (perp V B) (perp V A) := fun g hg =>
  (mem_trivOn_iff_maps (perp_anti h)).2 fun y hy => (mem_extSub_perp hc V).2 fun x hx => by
    rw [hR_act_sub]
    exact (mem_extSub_perp hc V).1 hy _ ((inv_mem hg).2 x hx)

theorem conj_mem_trivOn {p : HA R hc.sig V.gram} (hA : p ∈ parab hc V R A) (hB : p ∈ parab hc V R B)
    (hg : g ∈ trivOn hc V R A B) : p * g * p⁻¹ ∈ trivOn hc V R A B :=
  ⟨mul_mem (mul_mem hA hg.1) (inv_mem hA), fun y hy => by
    have := (hA _).1 (hg.2 _ ((inv_mem hB y).1 hy))
    rwa [act_sub, ← act_mul, ← act_mul, ← act_mul, mul_inv_cancel, act_one] at this⟩

@[simp] theorem trivOn_bot_top : trivOn hc V R ⊥ ⊤ = ⊥ :=
  eq_bot_iff.2 fun g hg => HA_ext _ _ fun r s => by
    have := hg.2 (Pi.single s 1) (by simp)
    rw [extSub_bot, Submodule.mem_bot, sub_eq_zero] at this
    have e := congrFun (this.trans (act_one hc V _).symm) r
    simpa only [act, Matrix.mulVec_single_one, Matrix.col_apply] using e

variable {R' : Type} [CommRing R'] [Algebra F R']

theorem act_mapH (φ : R →ₐ[F] R') (g : HA R hc.sig V.gram) (y : Fin V.rank → R ⊗[F] E) :
    act hc V (mapH hc.sig V.gram φ g) (mapVec V φ y) = mapVec V φ (act hc V g y) :=
  funext fun i => (RingHom.map_mulVec (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom _ y i).symm

theorem mapH_mem_parab (φ : R →ₐ[F] R') (hg : g ∈ parab hc V R W) : mapH hc.sig V.gram φ g ∈ parab hc V R' W :=
  mem_parab.2 fun x hx => by rw [← mapVec_coordR V φ, act_mapH]; exact mapVec_mem V φ (mem_parab.1 hg x hx)

theorem mapH_mem_trivOn (h : A ≤ B) (φ : R →ₐ[F] R') (hg : g ∈ trivOn hc V R A B) :
    mapH hc.sig V.gram φ g ∈ trivOn hc V R' A B :=
  (mem_trivOn h).2 fun x hx => by
    rw [← mapVec_coordR V φ, act_mapH, ← mapVec_sub]; exact mapVec_mem V φ ((mem_trivOn h).1 hg x hx)

end Step

section Closed

variable {hc : CMData F E} {V : HSpace E} {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
  [IsTopologicalRing R] [T2Space R]

theorem isClosed_act_sub_mem (W : Submodule E V.V) (y z : Fin V.rank → R ⊗[F] E) :
    IsClosed {g : HA R hc.sig V.gram | act hc V g y - z ∈ extSub (F := F) V R W} := by
  obtain ⟨T, h1, h2⟩ := exists_cut V W
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  have : T2Space (R ⊗[F] E) :=
    .of_injective_continuous (f := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun)
      (LinearEquiv.injective _) (IsModuleTopology.continuous_of_linearMap
        (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun.toLinearMap)
  have hm : Continuous fun g : HA R hc.sig V.gram => (HA.mat _ hc.sig V.gram g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  simp only [mem_extSub_iff_of_ker V _ T 1 h1 h2]
  exact isClosed_eq (continuous_const.matrix_mulVec ((hm.matrix_mulVec continuous_const).sub continuous_const))
    continuous_const

theorem isClosed_parab (W : Submodule E V.V) : IsClosed (parab hc V R W : Set (HA R hc.sig V.gram)) := by
  convert isClosed_biInter fun x (_ : x ∈ W) => isClosed_act_sub_mem (hc := hc) W (coordR V R x) 0 using 1
  ext g
  simpa using mem_parab

theorem isClosed_trivOn {A B : Submodule E V.V} (h : A ≤ B) :
    IsClosed (trivOn hc V R A B : Set (HA R hc.sig V.gram)) := by
  convert isClosed_biInter fun x (_ : x ∈ B) => isClosed_act_sub_mem (hc := hc) A (coordR V R x) (coordR V R x) using 1
  ext g
  simpa using mem_trivOn h

end Closed

section Adelic

open GlobalTheory.AdelicU

variable {hc : CMData F E} {V : HSpace E} {A B W : Submodule E V.V} {g : GAd hc.sig V.gram}

theorem mem_extSub_of_adelic {y : Fin V.rank → AF F ⊗[F] E}
    (h : ∀ w, mapVec V (evInf F w) y ∈ extSub (F := F) V w.Completion W)
    (h' : ∀ v, mapVec V (evFin F v) y ∈ extSub (F := F) V (Fv F v) W) : y ∈ extSub (F := F) V (AF F) W := by
  obtain ⟨T, h1, h2⟩ := exists_cut V W
  simp only [mem_extSub_iff_of_ker V _ T 1 h1 h2, map_mulVec_mapVec] at h h' ⊢
  funext k
  let b := Module.finBasis F E
  refine (Algebra.TensorProduct.basis (AF F) b).repr.map_eq_zero_iff.1 (Finsupp.ext fun j =>
    Prod.ext (funext fun w => ?_) (Subtype.ext (funext fun v => ?_)))
  · exact (repr_map b (evInf F w) _ j).symm.trans
      (by rw [show Algebra.TensorProduct.map _ _ _ = 0 from congrFun (h w) k]; simp; rfl)
  · exact (repr_map b (evFin F v) _ j).symm.trans
      (by rw [show Algebra.TensorProduct.map _ _ _ = 0 from congrFun (h' v) k]; simp; rfl)

theorem mem_parab_of_adelic (h : ∀ w, projArch hc.sig V.gram w g ∈ parab hc V w.Completion W)
    (h' : ∀ v, proj hc.sig V.gram v g ∈ parab hc V (Fv F v) W) : g ∈ parab hc V (AF F) W :=
  mem_parab.2 fun x hx => mem_extSub_of_adelic
    (fun w => by rw [← act_mapH, mapVec_coordR]; exact mem_parab.1 (h w) x hx)
    fun v => by rw [← act_mapH, mapVec_coordR]; exact mem_parab.1 (h' v) x hx

theorem mem_trivOn_of_adelic (e : A ≤ B) (h : ∀ w, projArch hc.sig V.gram w g ∈ trivOn hc V w.Completion A B)
    (h' : ∀ v, proj hc.sig V.gram v g ∈ trivOn hc V (Fv F v) A B) : g ∈ trivOn hc V (AF F) A B :=
  (mem_trivOn e).2 fun x hx => mem_extSub_of_adelic
    (fun w => by rw [mapVec_sub, ← act_mapH, mapVec_coordR]; exact (mem_trivOn e).1 (h w) x hx)
    fun v => by rw [mapVec_sub, ← act_mapH, mapVec_coordR]; exact (mem_trivOn e).1 (h' v) x hx

end Adelic

section Rat

variable (hc : CMData F E) (V : HSpace E)

def ratAct (γ : GRat hc V) : V.V →ₗ[E] V.V := Matrix.toLin V.frame V.frame γ.1.1

variable {hc V} (R : Type) [CommRing R] [Algebra F R] {A B W : Submodule E V.V} {γ : GRat hc V}

theorem act_diagH (γ : GRat hc V) (x : V.V) :
    act hc V (diagH hc.sig V.gram R γ) (coordR V R x) = coordR V R (ratAct hc V γ x) :=
  (map_mulVec_coordR V R γ.1.1 x).trans (funext fun i => congrArg (inclR R) (by
    rw [ratAct, Matrix.repr_toLin]))

variable [Nontrivial R]

theorem diagH_mem_parab : diagH hc.sig V.gram R γ ∈ parab hc V R W ↔ ∀ x ∈ W, ratAct hc V γ x ∈ W := by
  simp only [mem_parab, act_diagH, coordR_mem_iff]

theorem diagH_mem_trivOn (h : A ≤ B) :
    diagH hc.sig V.gram R γ ∈ trivOn hc V R A B ↔ ∀ x ∈ B, ratAct hc V γ x - x ∈ A := by
  have e : ∀ y z : V.V, coordR (F := F) V R y - coordR V R z = coordR V R (y - z) := fun y z => by
    funext i; simp [coordR]
  simp only [mem_trivOn h, act_diagH, e, coordR_mem_iff]

end Rat

structure IsoFlag (V : HSpace E) where

  k : ℕ

  X : Fin (k + 1) → Submodule E V.V
  zero : X 0 = ⊥
  strictMono : StrictMono X
  iso : X (Fin.last k) ≤ perp V (X (Fin.last k))

namespace IsoFlag

variable {V : HSpace E} (𝔉 : IsoFlag V)

def Proper : Prop := 0 < 𝔉.k

abbrev top : Submodule E V.V := 𝔉.X (Fin.last 𝔉.k)

theorem le_top (i : Fin (𝔉.k + 1)) : 𝔉.X i ≤ 𝔉.top := 𝔉.strictMono.monotone (Fin.le_last i)

theorem le_succ (i : Fin 𝔉.k) : 𝔉.X i.castSucc ≤ 𝔉.X i.succ := 𝔉.strictMono.monotone i.castSucc_le_succ

theorem le_perp (i j : Fin (𝔉.k + 1)) : 𝔉.X i ≤ perp V (𝔉.X j) :=
  (𝔉.le_top i).trans (𝔉.iso.trans (perp_anti (𝔉.le_top j)))

theorem isIsotropic {i : Fin (𝔉.k + 1)} (hi : i ≠ 0) : IsIsotropic V (𝔉.X i) :=
  ⟨𝔉.zero ▸ (𝔉.strictMono (Fin.pos_iff_ne_zero.2 hi)).ne', 𝔉.le_perp i i⟩

theorem Proper.isIsotropic_top {𝔉 : IsoFlag V} (h : 𝔉.Proper) : IsIsotropic V 𝔉.top :=
  𝔉.isIsotropic (Fin.ne_of_val_ne h.ne')

variable (V) in

def nil : IsoFlag V := ⟨0, fun _ => ⊥, rfl, Fin.strictMono_iff_lt_succ.2 fun i => i.elim0, bot_le⟩

def single {W : Submodule E V.V} (hW : IsIsotropic V W) : IsoFlag V :=
  ⟨1, ![⊥, W], rfl, Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i; exact bot_lt_iff_ne_bot.2 hW.1, hW.2⟩

theorem proper_single {W : Submodule E V.V} (hW : IsIsotropic V W) : (single hW).Proper := one_pos

def ofVectors {r : ℕ} (e : Fin r → V.V) (he : LinearIndependent E e) (h0 : ∀ a b, V.hD (e a) (e b) = 0) : IsoFlag V where
  k := r
  X i := Submodule.span E (e '' {j | j.val < i.val})
  zero := by simp
  strictMono := fun i j hij => by
    refine lt_of_le_of_ne (Submodule.span_mono (Set.image_mono fun a (h : a.val < i.val) => h.trans hij)) fun h => ?_
    have hi : i.val < r := lt_of_lt_of_le hij (Nat.lt_succ_iff.1 j.2)
    refine he.notMem_span_image (s := {j | j.val < i.val}) (x := ⟨i, hi⟩) (lt_irrefl i.val) ?_
    exact h.ge (Submodule.subset_span ⟨_, hij, rfl⟩)
  iso := Submodule.span_le.2 (by
    rintro _ ⟨a, -, rfl⟩
    refine mem_perp.2 fun x hx => ?_
    refine (Submodule.span_le (p := LinearMap.ker (V.hT.flip (e a)))).2 ?_ hx
    rintro _ ⟨b, -, rfl⟩
    exact h0 a b)

section Points

variable (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

def par : Subgroup (HA R hc.sig V.gram) := ⨅ i, parab hc V R (𝔉.X i)

def unip : Subgroup (HA R hc.sig V.gram) :=
  (⨅ i : Fin 𝔉.k, trivOn hc V R (𝔉.X i.castSucc) (𝔉.X i.succ)) ⊓ trivOn hc V R 𝔉.top (perp V 𝔉.top) ⊓
    ⨅ i : Fin 𝔉.k, trivOn hc V R (perp V (𝔉.X i.succ)) (perp V (𝔉.X i.castSucc))

def parRat : Subgroup (GRat hc V) := (𝔉.par hc F).comap (diagH hc.sig V.gram F)

def unipRat : Subgroup (GRat hc V) := (𝔉.unip hc F).comap (diagH hc.sig V.gram F)

variable {𝔉 hc R} {g : HA R hc.sig V.gram}

theorem mem_par : g ∈ 𝔉.par hc R ↔ ∀ i, g ∈ parab hc V R (𝔉.X i) := Subgroup.mem_iInf

theorem mem_unip : g ∈ 𝔉.unip hc R ↔ (∀ i : Fin 𝔉.k, g ∈ trivOn hc V R (𝔉.X i.castSucc) (𝔉.X i.succ)) ∧
    g ∈ trivOn hc V R 𝔉.top (perp V 𝔉.top) := by
  simp only [unip, Subgroup.mem_inf, Subgroup.mem_iInf]
  exact and_iff_left_of_imp fun h i => trivOn_le_trivOn_perp (𝔉.le_succ i) (h.1 i)

theorem mem_unip_iff : g ∈ 𝔉.unip hc R ↔
    (∀ i : Fin 𝔉.k, ∀ x ∈ 𝔉.X i.succ, act hc V g (coordR V R x) - coordR V R x ∈ extSub (F := F) V R (𝔉.X i.castSucc)) ∧
      ∀ x ∈ perp V 𝔉.top, act hc V g (coordR V R x) - coordR V R x ∈ extSub (F := F) V R 𝔉.top :=
  mem_unip.trans (and_congr (forall_congr' fun i => mem_trivOn (𝔉.le_succ i)) (mem_trivOn 𝔉.iso))

variable (𝔉 hc R)

theorem unip_le_par : 𝔉.unip hc R ≤ 𝔉.par hc R := fun _ hg => mem_par.2 fun i =>
  Fin.lastCases (mem_unip.1 hg).2.1 (fun j => ((mem_unip.1 hg).1 j).1) i

variable {𝔉 hc R} in

theorem conj_mem_unip {p : HA R hc.sig V.gram} (hp : p ∈ 𝔉.par hc R) (hg : g ∈ 𝔉.unip hc R) :
    p * g * p⁻¹ ∈ 𝔉.unip hc R :=
  mem_unip.2 ⟨fun i => conj_mem_trivOn (mem_par.1 hp _) (mem_par.1 hp _) ((mem_unip.1 hg).1 i),
    conj_mem_trivOn (mem_par.1 hp _) (parab_le_perp (mem_par.1 hp _)) (mem_unip.1 hg).2⟩

instance normal_unip : ((𝔉.unip hc R).subgroupOf (𝔉.par hc R)).Normal :=
  ⟨fun _ hn p => conj_mem_unip p.2 hn⟩

@[simp] theorem par_nil : (nil V).par hc R = ⊤ := by simp [par, nil]

@[simp] theorem unip_nil : (nil V).unip hc R = ⊥ :=
  eq_bot_iff.2 fun g hg => by simpa [nil, top] using (mem_unip.1 hg).2

variable {W : Submodule E V.V} (hW : IsIsotropic V W)

theorem par_single : (single hW).par hc R = parab hc V R W :=
  Subgroup.ext fun g => mem_par.trans (Fin.forall_fin_two.trans (and_iff_right (parab_bot (hc := hc) (V := V) (R := R) ▸ trivial)))

theorem unip_single : (single hW).unip hc R = unipRad hc V R W :=
  Subgroup.ext fun g => mem_unip.trans (and_congr (Fin.forall_fin_one.trans ((mem_trivOn_iff_maps bot_le).trans
    (forall₂_congr fun y _ => by rw [extSub_bot, Submodule.mem_bot, sub_eq_zero]))) (mem_trivOn_iff_maps hW.2))

theorem par_le_parab (i : Fin (𝔉.k + 1)) : 𝔉.par hc R ≤ parab hc V R (𝔉.X i) := iInf_le _ i

theorem par_le_parab_perp (i : Fin (𝔉.k + 1)) : 𝔉.par hc R ≤ parab hc V R (perp V (𝔉.X i)) :=
  (𝔉.par_le_parab hc R i).trans parab_le_perp

theorem unip_single_le {i : Fin (𝔉.k + 1)} (hi : i ≠ 0) : (single (𝔉.isIsotropic hi)).unip hc R ≤ 𝔉.unip hc R := by
  intro g hg
  obtain ⟨h1, h2⟩ := mem_unip.1 hg
  refine mem_unip.2 ⟨fun j => ?_, trivOn_mono (𝔉.le_top i) 𝔉.iso (perp_anti (𝔉.le_top i)) h2⟩
  rcases le_or_gt i j.castSucc with h | h
  · exact trivOn_mono (𝔉.strictMono.monotone h) (𝔉.le_succ j) (𝔉.le_perp _ i) h2
  · exact trivOn_mono bot_le (𝔉.le_succ j) (𝔉.strictMono.monotone (Fin.castSucc_lt_iff_succ_le.1 h)) (h1 (0 : Fin 1))

variable {𝔉 hc R} {R' : Type} [CommRing R'] [Algebra F R']

theorem mapH_mem_par (φ : R →ₐ[F] R') (hg : g ∈ 𝔉.par hc R) : mapH hc.sig V.gram φ g ∈ 𝔉.par hc R' :=
  mem_par.2 fun i => mapH_mem_parab φ (mem_par.1 hg i)

theorem mapH_mem_unip (φ : R →ₐ[F] R') (hg : g ∈ 𝔉.unip hc R) : mapH hc.sig V.gram φ g ∈ 𝔉.unip hc R' :=
  mem_unip.2 ⟨fun i => mapH_mem_trivOn (𝔉.le_succ i) φ ((mem_unip.1 hg).1 i), mapH_mem_trivOn 𝔉.iso φ (mem_unip.1 hg).2⟩

theorem mem_parRat {γ : GRat hc V} : γ ∈ 𝔉.parRat hc ↔ ∀ i, ∀ x ∈ 𝔉.X i, ratAct hc V γ x ∈ 𝔉.X i :=
  mem_par.trans (forall_congr' fun _ => diagH_mem_parab F)

theorem mem_unipRat {γ : GRat hc V} : γ ∈ 𝔉.unipRat hc ↔
    (∀ i : Fin 𝔉.k, ∀ x ∈ 𝔉.X i.succ, ratAct hc V γ x - x ∈ 𝔉.X i.castSucc) ∧
      ∀ x ∈ perp V 𝔉.top, ratAct hc V γ x - x ∈ 𝔉.top :=
  mem_unip.trans (and_congr (forall_congr' fun i => diagH_mem_trivOn F (𝔉.le_succ i)) (diagH_mem_trivOn F 𝔉.iso))

theorem diagH_mem_par [Nontrivial R] {γ : GRat hc V} : diagH hc.sig V.gram R γ ∈ 𝔉.par hc R ↔ γ ∈ 𝔉.parRat hc :=
  (mem_par.trans (forall_congr' fun _ => diagH_mem_parab R)).trans mem_parRat.symm

theorem diagH_mem_unip [Nontrivial R] {γ : GRat hc V} : diagH hc.sig V.gram R γ ∈ 𝔉.unip hc R ↔ γ ∈ 𝔉.unipRat hc :=
  (mem_unip.trans (and_congr (forall_congr' fun i => diagH_mem_trivOn R (𝔉.le_succ i))
    (diagH_mem_trivOn R 𝔉.iso))).trans mem_unipRat.symm

variable (𝔉 hc R) [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

theorem isClosed_par : IsClosed (𝔉.par hc R : Set (HA R hc.sig V.gram)) := by
  rw [par, Subgroup.coe_iInf]; exact isClosed_iInter fun _ => isClosed_parab _

theorem isClosed_unip : IsClosed (𝔉.unip hc R : Set (HA R hc.sig V.gram)) := by
  convert (isClosed_iInter fun i => isClosed_trivOn (hc := hc) (R := R) (𝔉.le_succ i)).inter (isClosed_trivOn 𝔉.iso) using 1
  ext g
  simpa using mem_unip

end Points

section Places

open GlobalTheory.AdelicU

variable (hc : CMData F E)

instance : LocallyCompactSpace (𝔉.par hc (AF F)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  (𝔉.isClosed_par hc _).locallyCompactSpace

instance : LocallyCompactSpace (𝔉.unip hc (AF F)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  (𝔉.isClosed_unip hc _).locallyCompactSpace

instance (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (𝔉.par hc (Fv F v)) :=
  (𝔉.isClosed_par hc _).locallyCompactSpace

instance (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (𝔉.unip hc (Fv F v)) :=
  (𝔉.isClosed_unip hc _).locallyCompactSpace

variable {𝔉 hc} {g : GAd hc.sig V.gram}

theorem mem_par_adelic : g ∈ 𝔉.par hc (AF F) ↔ (∀ w, projArch hc.sig V.gram w g ∈ 𝔉.par hc w.Completion) ∧
    ∀ v, proj hc.sig V.gram v g ∈ 𝔉.par hc (Fv F v) :=
  ⟨fun h => ⟨fun _ => mapH_mem_par _ h, fun _ => mapH_mem_par _ h⟩, fun h => mem_par.2 fun i =>
    mem_parab_of_adelic (fun w => mem_par.1 (h.1 w) i) fun v => mem_par.1 (h.2 v) i⟩

theorem mem_unip_adelic : g ∈ 𝔉.unip hc (AF F) ↔ (∀ w, projArch hc.sig V.gram w g ∈ 𝔉.unip hc w.Completion) ∧
    ∀ v, proj hc.sig V.gram v g ∈ 𝔉.unip hc (Fv F v) :=
  ⟨fun h => ⟨fun _ => mapH_mem_unip _ h, fun _ => mapH_mem_unip _ h⟩, fun h => mem_unip.2 ⟨fun i =>
    mem_trivOn_of_adelic (𝔉.le_succ i) (fun w => (mem_unip.1 (h.1 w)).1 i) fun v => (mem_unip.1 (h.2 v)).1 i,
    mem_trivOn_of_adelic 𝔉.iso (fun w => (mem_unip.1 (h.1 w)).2) fun v => (mem_unip.1 (h.2 v)).2⟩⟩

theorem emb_mem_unip {v : HeightOneSpectrum (𝓞 F)} {x : GLoc hc.sig V.gram v} :
    emb hc.sig V.gram v x ∈ 𝔉.unip hc (AF F) ↔ x ∈ 𝔉.unip hc (Fv F v) :=
  mem_unip_adelic.trans ⟨fun h => by simpa using h.2 v, fun h => ⟨fun w => by simp [one_mem], fun u => by
    by_cases e : u = v
    · subst e; simpa using h
    · rw [proj_emb_ne _ _ e]; exact one_mem _⟩⟩

theorem emb_mem_par {v : HeightOneSpectrum (𝓞 F)} {x : GLoc hc.sig V.gram v} :
    emb hc.sig V.gram v x ∈ 𝔉.par hc (AF F) ↔ x ∈ 𝔉.par hc (Fv F v) :=
  mem_par_adelic.trans ⟨fun h => by simpa using h.2 v, fun h => ⟨fun w => by simp [one_mem], fun u => by
    by_cases e : u = v
    · subst e; simpa using h
    · rw [proj_emb_ne _ _ e]; exact one_mem _⟩⟩

end Places

end IsoFlag

section Witt

variable (V : HSpace E)

def wittIndex : ℕ := sSup {d | ∃ W : Submodule E V.V, W ≤ perp V W ∧ Module.finrank E W = d}

theorem isGreatest_wittIndex :
    IsGreatest {d | ∃ W : Submodule E V.V, W ≤ perp V W ∧ Module.finrank E W = d} (wittIndex V) :=
  have h : BddAbove {d | ∃ W : Submodule E V.V, W ≤ perp V W ∧ Module.finrank E W = d} :=
    ⟨Module.finrank E V.V, by rintro _ ⟨W, -, rfl⟩; exact W.finrank_le⟩
  ⟨Nat.sSup_mem ⟨_, ⊥, bot_le, rfl⟩ h, fun _ hd => le_csSup h hd⟩

variable {V}

theorem finrank_le_wittIndex {W : Submodule E V.V} (h : W ≤ perp V W) : Module.finrank E W ≤ wittIndex V :=
  (isGreatest_wittIndex V).2 ⟨W, h, rfl⟩

theorem le_wittIndex_iff {i : ℕ} :
    i ≤ wittIndex V ↔ ∃ W : Submodule E V.V, W ≤ perp V W ∧ Module.finrank E W = i := by
  refine ⟨fun h => ?_, fun h => (isGreatest_wittIndex V).2 h⟩
  obtain ⟨W, hW, e⟩ := (isGreatest_wittIndex V).1
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := E) (M := W) (h.trans e.ge)
  refine ⟨_, le_perp_of_le (Submodule.span_le.2 ?_) hW, (finrank_span_eq_card (hf.map' W.subtype W.ker_subtype)).trans
    (Fintype.card_fin i)⟩
  rintro _ ⟨a, rfl⟩
  exact (f a).2

theorem wittIndex_pos_iff : 0 < wittIndex V ↔ ∃ W, IsIsotropic V W := by
  constructor
  · intro h
    obtain ⟨W, hW, e⟩ := (isGreatest_wittIndex V).1
    exact ⟨W, fun h0 => by rw [h0, finrank_bot] at e; omega, hW⟩
  · rintro ⟨W, h0, hW⟩
    exact (Nat.pos_of_ne_zero fun e => h0 (Submodule.finrank_eq_zero.1 e)).trans_le (finrank_le_wittIndex hW)

theorem wittIndex_eq_zero_iff : wittIndex V = 0 ↔ ∀ x, V.hD x x = 0 → x = 0 := by
  rw [← not_iff_not, ← Ne, ← Nat.pos_iff_ne_zero, wittIndex_pos_iff]
  push Not
  constructor
  · rintro ⟨W, h0, hW⟩
    obtain ⟨x, hx, h⟩ := (Submodule.ne_bot_iff W).1 h0
    exact ⟨x, mem_perp.1 (hW hx) x hx, h⟩
  · rintro ⟨x, h, hx⟩
    refine ⟨E ∙ x, by simpa using hx, (Submodule.span_singleton_le_iff_mem _ _).2 (mem_perp.2 fun y hy => ?_)⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    simp [HSpace.hD, show V.hT x x = 0 from h]

theorem IsoFlag.k_le_wittIndex (𝔉 : IsoFlag V) : 𝔉.k ≤ wittIndex V := by
  have h : StrictMono fun i => Module.finrank E (𝔉.X i) := fun i j h => Submodule.finrank_lt_finrank_of_lt (𝔉.strictMono h)
  have : ∀ i : Fin (𝔉.k + 1), i.val ≤ Module.finrank E (𝔉.X i) := fun i =>
    Fin.induction (Nat.zero_le _) (fun i ih => Nat.succ_le_of_lt (ih.trans_lt (h i.castSucc_lt_succ))) i
  exact (this (Fin.last _)).trans (finrank_le_wittIndex 𝔉.iso)

theorem exists_proper_iff : (∃ 𝔉 : IsoFlag V, 𝔉.Proper) ↔ 0 < wittIndex V :=
  ⟨fun ⟨𝔉, h⟩ => lt_of_lt_of_le h 𝔉.k_le_wittIndex,
    fun h => (wittIndex_pos_iff.1 h).elim fun _ hW => ⟨_, IsoFlag.proper_single hW⟩⟩

end Witt

end GlobalTheory.Cusp

end
