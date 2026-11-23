import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatEtaleSheafPreservesLocalExactnessStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

abbrev Sec.lin {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Sec F U →ₗ[ULift.{1} R] Sec G U := (φ.hom.app (op U)).hom

abbrev Tens.of (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w}) :
    (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) →ₗ[ULift.{1} R] Tens I J U w :=
  DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w} (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p

def Tens.d (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    Tens.of I J U (w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map (Sec.lin (I.d p.1.1 (p.1.1 + 1)) U) LinearMap.id +
    ((p.1.1.negOnePow : ℤˣ) : ℤ) •
      (Tens.of I J U (w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
        TensorProduct.map LinearMap.id (Sec.lin (J.d p.1.2 (p.1.2 + 1)) U))

theorem Tens.d_of_tmul (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.d I J U w (Tens.of I J U w p (a ⊗ₜ b)) =
      Tens.of I J U (w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩
          (Sec.map (I.d p.1.1 (p.1.1 + 1)) a ⊗ₜ b) +
        ((p.1.1.negOnePow : ℤˣ) : ℤ) • Tens.of I J U (w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩
          (a ⊗ₜ Sec.map (J.d p.1.2 (p.1.2 + 1)) b) := by
  simp [Tens.d, Tens.of, DirectSum.toModule_lof]

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]
open scoped DirectSum TensorProduct

theorem Pair.lift_of_tmul {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (Tens.of I J U w p (a ⊗ₜ b)) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  simp [Pair.lift, Tens.of, DirectSum.toModule_lof]

theorem Pair.lift_tensD {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    μ.lift U (w + 1) (Tens.d I J U w x) = Sec.map (K.d w (w + 1)) (μ.lift U w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have e := Tens.d_of_tmul I J U w p a b
      simp only [Tens.of, DirectSum.lof_eq_of] at e
      rw [e, map_add, map_zsmul]
      have e1 := μ.lift_of_tmul U (w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩
        (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) b
      have e2 := μ.lift_of_tmul U (w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩
        a (Sec.map (J.d p.1.2 (p.1.2 + 1)) b)
      have e3 := μ.lift_of_tmul U w p a b
      simp only [Tens.of, DirectSum.lof_eq_of] at e1 e2 e3
      rw [e1, e2, e3, μ.leibniz U p.1.1 p.1.2 w p.2 a b, Units.smul_def]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem Pair.lift_tensRes {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have e3 := μ.lift_of_tmul U w p a b
      have e4 := μ.lift_of_tmul V w p (Sec.res g a) (Sec.res g b)
      simp only [Tens.of, DirectSum.lof_eq_of] at e3 e4
      rw [e3, μ.nat g, ← e4, ← DirectSum.lof_eq_of (ULift.{1} R), ← DirectSum.lof_eq_of (ULift.{1} R), Tens.res, DirectSum.lmap_lof]
      rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem Tens.res_of_tmul (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (Tens.of I J U w p (a ⊗ₜ b)) = Tens.of I J V w p (Sec.res g a ⊗ₜ Sec.res g b) := by
  rw [Tens.res, Tens.of, DirectSum.lmap_lof]
  rfl

theorem Sec.res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

theorem Tens.res_d (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Tens.res g (w + 1) (Tens.d I J U w x) = Tens.d I J V w (Tens.res g w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have e := Tens.res_of_tmul I J g w p a b
      have e1 := Tens.d_of_tmul I J U w p a b
      have e2 := Tens.d_of_tmul I J V w p (Sec.res g a) (Sec.res g b)
      simp only [Tens.of, DirectSum.lof_eq_of] at e e1 e2
      rw [e, e1, e2, map_add, map_zsmul, ← DirectSum.lof_eq_of (ULift.{1} R), ← DirectSum.lof_eq_of (ULift.{1} R),
        Tens.res, DirectSum.lmap_lof, DirectSum.lmap_lof]
      simp only [TensorProduct.map_tmul, DirectSum.lof_eq_of]
      have h1 := Sec.res_map (I.d p.1.1 (p.1.1 + 1)) g a
      have h2 := Sec.res_map (J.d p.1.2 (p.1.2 + 1)) g b
      simp only [Sec.res] at h1 h2
      rw [h1, h2]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]
open scoped DirectSum TensorProduct

theorem Sec.map_d_d (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (a : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) a) = 0 := by
  have h : Sec.map (I.d j k) (Sec.map (I.d i j) a) = Sec.map (I.d i j ≫ I.d j k) a := rfl
  rw [h, I.d_comp_d]
  rfl

theorem Tens.d_d (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Tens.d I J U (w + 1) (Tens.d I J U w x) = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have e := Tens.d_of_tmul I J U w p a b
      have e1 := Tens.d_of_tmul I J U (w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩
        (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) b
      have e2 := Tens.d_of_tmul I J U (w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩
        a (Sec.map (J.d p.1.2 (p.1.2 + 1)) b)
      simp only [Tens.of, DirectSum.lof_eq_of] at e e1 e2
      rw [e, map_add, map_zsmul, e1, e2]
      simp only [Sec.map_d_d, TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, smul_zero, add_zero,
        smul_add, Int.negOnePow_succ, Units.val_neg, neg_smul, smul_smul]
      simp
    | add y z hy hz => simp only [map_add, hy, hz, add_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]
open scoped DirectSum TensorProduct

theorem Tens.d_of (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (y : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Tens.d I J U w (DirectSum.of _ p y) =
      DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
          ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩
          (TensorProduct.map (Sec.lin (I.d p.1.1 (p.1.1 + 1)) U) LinearMap.id y) +
        ((p.1.1.negOnePow : ℤˣ) : ℤ) • DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
          ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩
          (TensorProduct.map LinearMap.id (Sec.lin (J.d p.1.2 (p.1.2 + 1)) U) y) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [Tens.d, DirectSum.toModule_lof]
  simp [Tens.of, DirectSum.lof_eq_of]

def Tens.upper {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (n : ℤ) (x : Tens I J U w) : Tens I J U w :=
  DFinsupp.filter (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => n ≤ p.1.2) x

theorem Tens.upper_apply {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (n : ℤ) (x : Tens I J U w) (p) :
    Tens.upper n x p = if n ≤ p.1.2 then x p else 0 := DFinsupp.filter_apply _ _ _

theorem Tens.upper_of {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (n : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (y : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Tens.upper n (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p y) =
      if n ≤ p.1.2 then DirectSum.of _ p y else 0 := by
  unfold Tens.upper
  rw [DirectSum.of, DFinsupp.singleAddHom_apply, DFinsupp.filter_single]

theorem Tens.upper_add {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (n : ℤ) (x y : Tens I J U w) :
    Tens.upper n (x + y) = Tens.upper n x + Tens.upper n y := DFinsupp.filter_add _ _ _

theorem Tens.d_upper_low (I J : Cx R) (U : Scheme.{0}) (w n : ℤ) (x : Tens I J U w)
    (q : {q : ℤ × ℤ // q.1 + q.2 = w + 1}) (hq : q.1.2 < n) : Tens.d I J U w (Tens.upper n x) q = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp [Tens.upper]
  | of p y =>
    rw [Tens.upper_of]
    split_ifs with hp
    · rw [Tens.d_of, DFinsupp.add_apply, DFinsupp.smul_apply, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne, smul_zero, add_zero]
      · intro h; subst h; simp at hq; omega
      · intro h; subst h; simp at hq; omega
    · simp
  | add x y hx hy => rw [Tens.upper_add, map_add, DFinsupp.add_apply, hx, hy, add_zero]

theorem Tens.d_upper_edge (I J : Cx R) (U : Scheme.{0}) (w n s : ℤ) (h : s + n = w) (x : Tens I J U w) :
    Tens.d I J U w (Tens.upper n x) ⟨(s + 1, n), by simp only; omega⟩ =
      TensorProduct.map (Sec.lin (I.d s (s + 1)) U) LinearMap.id (x ⟨(s, n), h⟩) := by
  induction x using DirectSum.induction_on with
  | zero => simp [Tens.upper]
  | of p y =>
    obtain ⟨⟨a, b⟩, hp⟩ := p
    rw [Tens.upper_of]
    by_cases hab : a = s ∧ b = n
    · obtain ⟨rfl, rfl⟩ := hab
      rw [if_pos le_rfl, Tens.d_of, DFinsupp.add_apply, DFinsupp.smul_apply, DirectSum.of_eq_same, DirectSum.of_eq_of_ne,
        smul_zero, add_zero, DirectSum.of_eq_same]
      intro e; simp at e
    · rw [DirectSum.of_eq_of_ne]
      · split_ifs with hb
        · rw [Tens.d_of, DFinsupp.add_apply, DFinsupp.smul_apply, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne,
            smul_zero, add_zero, map_zero]
          · intro e; simp at e; simp at hb; omega
          · intro e; simp at e; simp at hb hp; omega
        · simp
      · intro e; simp at e; omega
  | add x y hx hy => rw [Tens.upper_add, map_add, DFinsupp.add_apply, hx, hy, DFinsupp.add_apply, map_add]

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]
open scoped DirectSum TensorProduct

theorem Sec.eq_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h : Sec.map (𝟙 F) x = Sec.map (0 : F ⟶ F) x := by rw [hF.eq_of_src (𝟙 F) 0]
  exact h

theorem tensor_eq_zero_left {S M N : Type*} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (h : ∀ m : M, m = 0) (y : M ⊗[S] N) : y = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rw [h m, TensorProduct.zero_tmul]
  | add y z hy hz => rw [hy, hz, add_zero]

theorem tensor_eq_zero_right {S M N : Type*} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (h : ∀ n : N, n = 0) (y : M ⊗[S] N) : y = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rw [h n, TensorProduct.tmul_zero]
  | add y z hy hz => rw [hy, hz, add_zero]

theorem Tens.res_apply {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) (p) :
    Tens.res g w x p = TensorProduct.map ((I.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom (x p) := rfl

theorem Tens.res_comp {I J : Cx R} {W V U : Scheme.{0}} (m : W ⟶ V) (k : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Tens.res (m ≫ k) w x = Tens.res m w (Tens.res k w x) := by
  refine DFinsupp.ext fun p => ?_
  rw [Tens.res_apply, Tens.res_apply, Tens.res_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  simp [op_comp, Functor.map_comp]

theorem rTensor_res_comm {B C M : Shv R} (g : B ⟶ C) {V U : Scheme.{0}} (k : V ⟶ U)
    (x : Sec B U ⊗[ULift.{1} R] Sec M U) :
    LinearMap.rTensor _ (g.hom.app (op V)).hom (TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x) =
      TensorProduct.map (C.obj.map k.op).hom (M.obj.map k.op).hom (LinearMap.rTensor _ (g.hom.app (op U)).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have h := Sec.res_map g k a
    simp only [Sec.res, Sec.map] at h
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, h]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem Tens.cycle_loc_boundary {C J : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b]
    (hJ : ∀ t, FlatS (J.X t)) (hC : C.Acyclic) (w : ℤ) (U : Scheme.{0}) (x : Tens C J U (w + 1))
    (hx : Tens.d C J U (w + 1) x = 0) :
    Loc U fun V g => ∃ y : Tens C J V w, Tens.d C J V w y = Tens.res g (w + 1) x := by
  obtain ⟨L_all, L_mono, -, -, L_trans, -, -⟩ := loc_calculus
  let P : ℤ → Prop := fun n => ∀ (U : Scheme.{0}) (x : Tens C J U (w + 1)), Tens.upper n x = x →
    Tens.d C J U (w + 1) x = 0 → Loc U fun V g => ∃ y : Tens C J V w, Tens.d C J V w y = Tens.res g (w + 1) x
  have base : P (w + 2 - a) := by
    intro U x hu _
    have hx0 : x = 0 := by
      refine DFinsupp.ext fun p => ?_
      rw [← hu, Tens.upper_apply]
      split_ifs with hp
      · have hs : p.1.1 < a := by have := p.2; omega
        exact tensor_eq_zero_left (fun m => Sec.eq_zero_of_isZero (C.isZero_of_isStrictlyGE a p.1.1 hs) m) _
      · rfl
    refine L_all _ _ fun V g => ⟨0, ?_⟩
    rw [hx0, map_zero, map_zero]
  have step : ∀ n, P (n + 1) → P n := by
    intro n ih U x hu hdx
    have hedge : LinearMap.rTensor _ ((C.d (w - n + 1) (w - n + 1 + 1)).hom.app (op U)).hom
        (x ⟨(w - n + 1, n), by simp only; omega⟩) = 0 := by
      have := Tens.d_upper_edge C J U (w + 1) n (w - n + 1) (by omega) x
      rw [hu, hdx] at this
      exact this.symm
    have hexact : ∀ (U : Scheme.{0}) (b : Sec (C.X (w - n + 1)) U), Sec.map (C.d (w - n + 1) (w - n + 1 + 1)) b = 0 →
        Loc U fun V k => ∃ a : Sec (C.X (w - n)) V, Sec.map (C.d (w - n) (w - n + 1)) a = Sec.res k b :=
      (GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally R (C.sc' (w - n) (w - n + 1) (w - n + 1 + 1))).mp
        ((C.exactAt_iff' (w - n) (w - n + 1) (w - n + 1 + 1) (by simp) (by simp)).mp (hC (w - n + 1)))
    have hloc : Loc U fun V k => LinearMap.rTensor _ ((C.d (w - n + 1) (w - n + 1 + 1)).hom.app (op V)).hom
        (TensorProduct.map ((C.X (w - n + 1)).obj.map k.op).hom ((J.X n).obj.map k.op).hom
          (x ⟨(w - n + 1, n), by simp only; omega⟩)) = 0 :=
      L_all _ _ fun V k => by rw [rTensor_res_comm, hedge, map_zero]
    have hrow := GlobalTheory.T.tensor_flat_etaleSheaf_preserves_local_exactness R (J.X n) (hJ n) (C.d (w - n) (w - n + 1)) (C.d (w - n + 1) (w - n + 1 + 1))
      (C.d_comp_d _ _ _) hexact U _ hloc
    apply L_trans
    refine L_mono _ _ _ hrow ?_
    rintro V k ⟨y0, hy0⟩
    let y : Tens C J V w := DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} =>
      Sec (C.X q.1.1) V ⊗[ULift.{1} R] Sec (J.X q.1.2) V) ⟨(w - n, n), by simp only; omega⟩ y0
    have hyu : Tens.upper n y = y := by
      simp only [y]
      rw [Tens.upper_of, if_pos le_rfl]
    let x' : Tens C J V (w + 1) := Tens.res k (w + 1) x - Tens.d C J V w y
    have hx'd : Tens.d C J V (w + 1) x' = 0 := by
      simp only [x', map_sub, ← Tens.res_d, hdx, map_zero, Tens.d_d, sub_zero]
    have hx'u : Tens.upper (n + 1) x' = x' := by
      refine DFinsupp.ext fun q => ?_
      rw [Tens.upper_apply]
      split_ifs with hq
      · rfl
      symm
      show (Tens.res k (w + 1) x - Tens.d C J V w y) q = 0
      rw [DFinsupp.sub_apply]
      rcases lt_or_eq_of_le (Int.lt_add_one_iff.mp (not_le.mp hq)) with hlt | heq
      · rw [Tens.res_apply, ← hu, Tens.upper_apply, if_neg (by omega), map_zero, ← hyu,
          Tens.d_upper_low C J V w n _ q hlt, sub_zero]
      · obtain ⟨⟨s', t'⟩, hq'⟩ := q
        simp only at heq hq'
        subst heq
        obtain rfl : s' = w - t' + 1 := by omega
        rw [Tens.res_apply, ← hyu, Tens.d_upper_edge C J V w t' (w - t') (by omega) y]
        simp only [y]
        rw [DirectSum.of_eq_same, sub_eq_zero]
        exact hy0.symm
    refine L_mono _ _ _ (ih V x' hx'u hx'd) ?_
    rintro W m ⟨z, hz⟩
    refine ⟨z + Tens.res m w y, ?_⟩
    rw [map_add, hz, Tens.res_comp, ← Tens.res_d]
    simp only [x', map_sub, sub_add_cancel]
  have hall : ∀ k : ℕ, P (w + 2 - a - k) := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      have e : w + 2 - a - ((k + 1 : ℕ) : ℤ) + 1 = w + 2 - a - (k : ℤ) := by push_cast; ring
      exact step _ (e ▸ ih)
  refine hall (w + 2 - a - b).toNat U x ?_ hx
  refine DFinsupp.ext fun p => ?_
  rw [Tens.upper_apply]
  split_ifs with hp
  · rfl
  · have ht : p.1.2 < b := by omega
    exact (tensor_eq_zero_right (fun m => Sec.eq_zero_of_isZero (J.isZero_of_isStrictlyGE b p.1.2 ht) m) _).symm

theorem acyclic_of_isTensor : ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b]
    (τ : Pair C J T), τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic := by
  intro R _ C J T a b _ _ τ hT hJ hC j
  obtain ⟨L_all, L_mono, -, -, L_trans, -, -⟩ := loc_calculus
  obtain ⟨w, rfl⟩ : ∃ w, j = w + 1 := ⟨j - 1, by ring⟩
  rw [T.exactAt_iff' w (w + 1) (w + 1 + 1) (by simp) (by simp), GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  rintro U (z : Sec (T.X (w + 1)) U) (hz' : Sec.map (T.d (w + 1) (w + 1 + 1)) z = 0)
  apply L_trans
  refine L_mono _ _ _ (hT.1 U (w + 1) z) ?_
  rintro V g ⟨x, hx⟩
  have h1 : τ.lift V (w + 1 + 1) (Tens.d C J V (w + 1) x) = 0 := by
    rw [Pair.lift_tensD, hx, ← Sec.res_map, hz']
    exact map_zero _
  apply L_trans
  refine L_mono _ _ _ (hT.2 V (w + 1 + 1) _ h1) ?_
  intro W k hk
  rw [Tens.res_d] at hk
  refine L_mono _ _ _ (Tens.cycle_loc_boundary a b hJ hC w W _ hk) ?_
  rintro W' m ⟨y, hy⟩
  refine ⟨τ.lift W' w y, ?_⟩
  change Sec.map (T.d w (w + 1)) (τ.lift W' w y) = _
  rw [← Pair.lift_tensD, hy, Pair.lift_tensRes, Pair.lift_tensRes, hx]
  simp [Sec.res, op_comp, Functor.map_comp]
  rfl

end GlobalTheory.EtC
