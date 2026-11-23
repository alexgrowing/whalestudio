import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RegUnitary
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.Vanish2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Transfer

theorem tr_span {E R M₁ M₂ : Type*} [Field E] [CommRing R] [AddCommGroup M₁] [Module E M₁] [AddCommGroup M₂]
    [Module R M₂] (j : E →+* R) (ι : M₁ →+ M₂) (hs : ∀ (c : E) x, ι (c • x) = j c • ι x) {S : Set M₁}
    {x : M₁} (hx : x ∈ Submodule.span E S) : ι x ∈ Submodule.span R (ι '' S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [hs]; exact Submodule.smul_mem _ _ ha

variable {E R : Type*} [Field E] [CommRing R] {n r : ℕ}

theorem tr_sub (ι : (Fin n → E) →+ (Fin n → R)) (M : Matrix (Fin n) (Fin n) E) (G : Matrix (Fin n) (Fin n) R)
    (hG : ∀ x, G *ᵥ ι x = ι (M *ᵥ x)) (x : Fin n → E) : (G - 1) *ᵥ ι x = ι ((M - 1) *ᵥ x) := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, hG, map_sub]

theorem tr_flag (j : E →+* R) (ι : (Fin n → E) →+ (Fin n → R)) (hs : ∀ (c : E) x, ι (c • x) = j c • ι x)
    (M : Matrix (Fin n) (Fin n) E) (G : Matrix (Fin n) (Fin n) R) (hG : ∀ x, G *ᵥ ι x = ι (M *ᵥ x))
    (e : Fin r → Fin n → E) (S : Set (Fin r)) (x : Fin n → E)
    (hx : (M - 1) *ᵥ x ∈ Submodule.span E (e '' S)) :
    (G - 1) *ᵥ ι x ∈ Submodule.span R ((fun b => ι (e b)) '' S) := by
  rw [tr_sub ι M G hG]
  have := tr_span j ι hs hx
  rwa [Set.image_image] at this

theorem tr_orth (j : E →+* R) (ι : (Fin n → E) →+ (Fin n → R)) (hs : ∀ (c : E) x, ι (c • x) = j c • ι x)
    (hspan : ∀ y : Fin n → R, ∃ c : Fin n → R, ∃ w : Fin n → Fin n → E, y = ∑ i, c i • ι (w i))
    (hE : (Fin n → E) → (Fin n → E) →ₗ[E] E) (B : (Fin n → R) → (Fin n → R) →ₗ[R] R)
    (hB : ∀ x y, B (ι x) (ι y) = j (hE x y))
    (e f : Fin r → Fin n → E) (hef : ∀ a b, hE (e b) (f a) = if a = b then 1 else 0)
    (M : Matrix (Fin n) (Fin n) E) (G : Matrix (Fin n) (Fin n) R) (hG : ∀ x, G *ᵥ ι x = ι (M *ᵥ x))
    (hM : ∀ w, (∀ a, hE (e a) w = 0) → (M - 1) *ᵥ w ∈ Submodule.span E (Set.range e))
    (y : Fin n → R) (hy : ∀ a, B (ι (e a)) y = 0) :
    (G - 1) *ᵥ y ∈ Submodule.span R (Set.range fun a => ι (e a)) := by
  obtain ⟨c, w, rfl⟩ := hspan y
  set w' : Fin n → Fin n → E := fun i => w i - ∑ a, hE (e a) (w i) • f a with hw'def
  have hw' : ∀ i b, hE (e b) (w' i) = 0 := by
    intro i b
    simp only [hw'def, map_sub, map_sum, map_smul, hef, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  have hdec : ∀ i, ι (w i) = ι (w' i) + ∑ a, j (hE (e a) (w i)) • ι (f a) := by
    intro i
    simp only [hw'def, map_sub, map_sum, hs]
    abel
  have hB0 : ∀ a, ∑ i, c i * j (hE (e a) (w i)) = 0 := by
    intro a
    have := hy a
    rw [map_sum] at this
    simpa [map_smul, hB] using this
  have hsum : ∑ i, c i • ι (w i) = ∑ i, c i • ι (w' i) + ∑ a, (∑ i, c i * j (hE (e a) (w i))) • ι (f a) := by
    simp only [hdec, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul, Finset.sum_smul]
    congr 1
    exact Finset.sum_comm
  rw [hsum]
  simp only [hB0, zero_smul, Finset.sum_const_zero, add_zero]
  rw [Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Matrix.mulVec_smul, tr_sub ι M G hG]
  refine Submodule.smul_mem _ _ ?_
  have := tr_span j ι hs (hM _ (hw' i))
  rwa [← Set.range_comp] at this

end Transfer

section Maps

def hfL {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (J : Matrix (Fin m) (Fin m) A) (x : Fin m → A) :
    (Fin m → A) →ₗ[A] A where
  toFun y := Formalism.UG.hform σ J x y
  map_add' y y' := by simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring

theorem hfL_apply {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (J : Matrix (Fin m) (Fin m) A) (x y : Fin m → A) :
    hfL σ J x y = Formalism.UG.hform σ J x y := rfl

def hJL {m : ℕ} (ε : Fin m → Bool) (x : Fin m → ℂ) : (Fin m → ℂ) →ₗ[ℂ] ℂ where
  toFun y := hJ ε x y
  map_add' y y' := by simp [hJ, Matrix.mulVec_add]
  map_smul' c y := by simp [hJ, Matrix.mulVec_smul]

theorem hJL_apply {m : ℕ} (ε : Fin m → Bool) (x y : Fin m → ℂ) : hJL ε x y = hJ ε x y := rfl

variable (I : AutInst)

def rvHom (v : InfinitePlace I.F) : (Fin I.n → I.E) →+ (Fin I.n → ℂ) where
  toFun := rv I v
  map_zero' := by
    unfold rv
    have : (fun i => I.φ v ((0 : Fin I.n → I.E) i)) = 0 := by funext i; simp
    rw [this, Matrix.mulVec_zero]
  map_add' x y := by
    unfold rv
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp

theorem rvHom_apply (v : InfinitePlace I.F) (x : Fin I.n → I.E) : rvHom I v x = rv I v x := rfl

theorem rv_smul' (v : InfinitePlace I.F) (c : I.E) (x : Fin I.n → I.E) :
    rvHom I v (c • x) = I.φ v c • rvHom I v x := by
  rw [rvHom_apply, rvHom_apply]
  unfold rv
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem rv_span' (v : InfinitePlace I.F) (y : Fin I.n → ℂ) :
    ∃ c : Fin I.n → ℂ, ∃ w : Fin I.n → Fin I.n → I.E, y = ∑ i, c i • rvHom I v (w i) := by
  have hPu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  refine ⟨I.P v *ᵥ y, fun i k => if i = k then 1 else 0, ?_⟩
  have h1 : ∀ i, rvHom I v (fun k => if i = k then (1 : I.E) else 0) =
      (I.P v)⁻¹ *ᵥ (fun k => if i = k then (1 : ℂ) else 0) := by
    intro i
    rw [rvHom_apply]
    unfold rv
    congr 1
    funext k
    by_cases h : i = k <;> simp [h]
  simp only [h1, ← Matrix.mulVec_smul]
  rw [← Matrix.mulVec_sum, ← pi_eq_sum_univ, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hPu,
    Matrix.one_mulVec]

def inclHom : (Fin I.n → I.E) →+ VA I where
  toFun := incl I
  map_zero' := by funext i; simp [incl]
  map_add' x y := by funext i; simp [incl]

theorem inclHom_apply (x : Fin I.n → I.E) : inclHom I x = incl I x := rfl

theorem incl_smul' (c : I.E) (x : Fin I.n → I.E) :
    inclHom I (c • x) = Formalism.UG.inclE (F := I.F) (Af I.F) c • inclHom I x := by
  funext i
  simp [inclHom, incl]

theorem incl_span' (y : VA I) :
    ∃ c : Fin I.n → I.E ⊗[I.F] Af I.F, ∃ w : Fin I.n → Fin I.n → I.E, y = ∑ i, c i • inclHom I (w i) := by
  refine ⟨y, fun i k => if i = k then 1 else 0, ?_⟩
  have h1 : ∀ i, inclHom I (fun k => if i = k then (1 : I.E) else 0) =
      fun k => if i = k then (1 : I.E ⊗[I.F] Af I.F) else 0 := by
    intro i
    funext k
    rw [inclHom_apply]
    show Formalism.UG.inclE (F := I.F) (Af I.F) _ = _
    by_cases h : i = k <;> simp [h]
  simp only [h1]
  exact pi_eq_sum_univ y

end Maps

section Coords

variable {D : D7} (X : HidaSetting D)

theorem crd_sub' (a b : (VS D).V) : X.crd (a - b) = X.crd a - X.crd b := by
  have h := crd_add X (a - b) b
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

def crdHom : (VS D).V →+ (Fin X.B.I.n → X.B.I.E) where
  toFun := X.crd
  map_zero' := crd_zero X
  map_add' := crd_add X

theorem crd_span' {S : Set (VS D).V} {v : (VS D).V} (hv : v ∈ Submodule.span D.host.E S) :
    X.crd v ∈ Submodule.span X.B.I.E (X.crd '' S) :=
  tr_span X.ιE.symm.toRingHom (crdHom X) (fun c x => crd_smul X c x) hv

theorem hef_crd (a b : Fin D.R.rS) :
    hfL (starRingEnd X.B.I.E) X.B.I.J (X.eR b) (X.fR a) = if a = b then 1 else 0 := by
  have h := Formalism.L2.SG.PoincareInHH.Cut.hform_crd X (X.eX b) (X.fY a)
  rw [X.ef] at h
  rw [hfL_apply]
  apply X.ιE.injective
  rw [HidaSetting.eR, HidaSetting.fR, h]
  by_cases hab : a = b
  · subst hab; simp
  · have : b ≠ a := fun h' => hab h'.symm
    simp [hab, this]

variable {u : D.what₂.Word}

theorem orth_of_e {v : (VS D).V} (h : ∀ a, (VS D).hT (X.eX a) v = 0) :
    v ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := by
  rw [mem_orth_iff]
  intro w hw
  have hw' : w ∈ Submodule.span D.host.E (Set.range X.eX) := by
    have : w ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := hw
    rwa [X.Fu_e] at this
  clear hw
  induction hw' using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact h a
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]

variable {Λ : Submodule (𝓞 D.host.E) (VS D).V} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
  (hn : n ∈ NLam Λ (lf D (X.Fu u))) {M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E}
  (h3 : ∀ y, X.crd (n y) = M *ᵥ X.crd y)

include h3 in
theorem mcrd (v : (VS D).V) : (M - 1) *ᵥ X.crd v = X.crd (n v - v) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← h3, crd_sub']

include hn h3 in

theorem nlam_e (a : Fin D.R.rS) : (M - 1) *ᵥ X.eR a ∈ Submodule.span X.B.I.E (X.eR '' {b | b.1 < a.1}) := by
  have hx : X.eX a ∈ Xflag (lf D (X.Fu u)) (a.1 + 1) := by
    show X.eX a ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < a.1 + 1})
    rw [X.Fu_e]
    exact Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩
  have h1 : n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1}) := by
    have := hn.2.1 a.1 _ hx
    have e : Xflag (lf D (X.Fu u)) a.1 = Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < a.1}) := rfl
    rwa [e, X.Fu_e] at this
  have := crd_span' X h1
  rw [Set.image_image] at this
  show (M - 1) *ᵥ X.crd (X.eX a) ∈ _
  rw [mcrd X h3]
  exact this

include hn h3 in

theorem nilradical_lattice_z_mem_span : (M - 1) *ᵥ X.zR u ∈ Submodule.span X.B.I.E (Set.range X.eR) := by
  have ho := orth_of_e X (u := u) (v := X.zu u) fun a => (X.zu_orth u a).1
  have h1 := hn.2.2 _ ho
  have e : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range (X.Fu u).e) := rfl
  rw [e, X.Fu_e] at h1
  have := crd_span' X h1
  rw [← Set.range_comp] at this
  show (M - 1) *ᵥ X.crd (X.zu u) ∈ _
  rw [mcrd X h3]
  exact this

include hn h3 in

theorem nlam_orth (w : Fin X.B.I.n → X.B.I.E)
    (hw : ∀ a, hfL (starRingEnd X.B.I.E) X.B.I.J (X.eR a) w = 0) :
    (M - 1) *ᵥ w ∈ Submodule.span X.B.I.E (Set.range X.eR) := by
  have ho : toV X w ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := by
    refine orth_of_e X fun a => ?_
    have h := iota_hE X (X.eR a) w
    rw [HidaSetting.eR, toV_crd] at h
    rw [← h]
    have : hE X (X.crd (X.eX a)) w = 0 := by
      have := hw a
      rw [hfL_apply] at this
      exact this
    rw [this, map_zero]
  have h1 := hn.2.2 _ ho
  have e : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range (X.Fu u).e) := rfl
  rw [e, X.Fu_e] at h1
  have := crd_span' X h1
  rw [← Set.range_comp] at this
  have hw' : w = X.crd (toV X w) := (crd_toV X w).symm
  rw [hw', mcrd X h3]
  exact this

end Coords

end Formalism.L2.SG.Pf.Vanish2

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Vanish2

theorem nLamNinf_holds : Formalism.L2.SG.TermOp.Vanish.NLamNinf := by
  intro D X u Λ x n hx hn v
  obtain ⟨M, -, h1, -, h3⟩ := hx
  have hG : ∀ y, uMat (x.1 v) *ᵥ rvHom X.B.I v y = rvHom X.B.I v ((M : Matrix _ _ _) *ᵥ y) := by
    intro y
    rw [rvHom_apply, rvHom_apply, h1 v]
    exact rv_mulVec X v _ y
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · exact tr_flag (X.B.I.φ v) (rvHom X.B.I v) (rv_smul' X.B.I v) _ _ hG X.eR _ _ (nlam_e X hn h3 a)
  · have := tr_flag (X.B.I.φ v) (rvHom X.B.I v) (rv_smul' X.B.I v) _ _ hG X.eR Set.univ _
      (by rw [Set.image_univ]; exact nilradical_lattice_z_mem_span X hn h3)
    unfold spanLt
    rw [← range_eq_image_lt]
    rwa [Set.image_univ] at this
  · have := tr_orth (X.B.I.φ v) (rvHom X.B.I v) (rv_smul' X.B.I v) (rv_span' X.B.I v)
      (fun x => hfL (starRingEnd X.B.I.E) X.B.I.J x) (fun x => hJL (X.B.I.ε v) x)
      (fun x y => by rw [hJL_apply, hfL_apply, rvHom_apply, rvHom_apply]; exact hJ_rv X v x y)
      X.eR X.fR (hef_crd X) _ _ hG (nlam_orth X hn h3) y hy
    unfold spanLt
    rw [← range_eq_image_lt]
    exact this

theorem nLamNfin_holds : Formalism.L2.SG.TermOp.Vanish.NLamNfin := by
  intro D X u Λ x n hx hn
  obtain ⟨M, -, -, h2, h3⟩ := hx
  have hG : ∀ y, X.B.I.fmat x.2 *ᵥ inclHom X.B.I y = inclHom X.B.I ((M : Matrix _ _ _) *ᵥ y) := by
    intro y
    rw [inclHom_apply, inclHom_apply, h2]
    exact incl_mulVec X _ y
  refine ⟨fun a => ?_, ?_, fun y hy => ?_⟩
  · exact tr_flag _ (inclHom X.B.I) (incl_smul' X.B.I) _ _ hG X.eR _ _ (nlam_e X hn h3 a)
  · have := tr_flag _ (inclHom X.B.I) (incl_smul' X.B.I) _ _ hG X.eR Set.univ _
      (by rw [Set.image_univ]; exact nilradical_lattice_z_mem_span X hn h3)
    rwa [Set.image_univ] at this
  · exact tr_orth _ (inclHom X.B.I) (incl_smul' X.B.I) (incl_span' X.B.I)
      (fun x => hfL (starRingEnd X.B.I.E) X.B.I.J x) (fun x => Formalism.L2.SG.PoincareInHH.Cut.hAlin X x)
      (fun x y => by
        rw [hfL_apply, inclHom_apply, inclHom_apply]
        exact Formalism.L2.SG.PoincareInHH.Cut.hA_incl X x y)
      X.eR X.fR (hef_crd X) _ _ hG (nlam_orth X hn h3) y hy

theorem ginfUnimod_holds : Formalism.L2.SG.TermOp.Vanish.GinfUnimod := fun I => muInf_right I

theorem roDiscreteC_holds : Formalism.L2.SG.TermOp.Vanish.RODiscreteC := by
  intro D X Y u u' t
  have h := ROsub_discrete X (X.Fu u) (X.Fu u') t.lam t.lam' ((Y.rowsOK u).1 _ t.mem).1.1 t.lin
  have e : Formalism.L2.SG.TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin =
      ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin := by
    ext; rfl
  rw [e]
  exact h

namespace Vanish2

section Psi

variable {n r : ℕ}

theorem hJ_spL (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (a : Fin r) {y : Fin n → ℂ}
    (hy : y ∈ spanLt e a.1) : hJ ε (f a) y = 0 := by
  have : spanLt e a.1 ≤ LinearMap.ker (hJL ε (f a)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    show hJL ε (f a) (e b) = 0
    rw [hJL_apply, hfe, if_neg]
    intro h
    rw [h] at hb
    exact lt_irrefl a.1 hb
  exact this hy

theorem fl_step {e : Fin r → Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : ∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) (k : ℕ) {y : Fin n → ℂ} (hy : y ∈ spanLt e (k + 1)) :
    (g - 1) *ᵥ y ∈ spanLt e k := by
  have : spanLt e (k + 1) ≤ (spanLt e k).comap (Matrix.mulVecLin (g - 1)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    exact spL_mono e (Nat.lt_succ_iff.1 hb) (hg b)
  exact this hy

theorem rootCoord_mul (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hh : InS e z h) (a : Fin r) :
    rootCoord ε e f z (g * h) a = rootCoord ε e f z g a + rootCoord ε e f z h a := by
  unfold rootCoord
  have hx0 : hJ ε (f a) (nxt e z a) = 0 := by
    unfold nxt
    split_ifs with hlt
    · rw [hfe, if_neg]
      intro h'
      have := congrArg Fin.val h'
      simp at this
    · exact hfz a
  have hd : (h - 1) *ᵥ nxt e z a ∈ spanLt e (a.1 + 1) := by
    unfold nxt
    split_ifs with hlt
    · exact hh.1 ⟨a.1 + 1, hlt⟩
    · exact spL_mono e (by omega) hh.2
  have L : ∀ p q : Fin n → ℂ, hJ ε (f a) (p + q) = hJ ε (f a) p + hJ ε (f a) q := fun p q => by
    rw [← hJL_apply, map_add]; rfl
  have hgd := fl_step hg.1 a.1 hd
  have e2 : h *ᵥ nxt e z a = nxt e z a + (h - 1) *ᵥ nxt e z a := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have e1 : (g * h) *ᵥ nxt e z a = g *ᵥ nxt e z a + (h - 1) *ᵥ nxt e z a +
      (g - 1) *ᵥ ((h - 1) *ᵥ nxt e z a) := by
    rw [← Matrix.mulVec_mulVec, e2, Matrix.mulVec_add, Matrix.sub_mulVec g 1, Matrix.one_mulVec]; abel
  rw [e1, e2, L, L, L, hx0, hJ_spL ε e f hfe a hgd]
  ring

theorem psiR_mul (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hh : InS e z h) :
    psiR ε gg e f z (g * h) = psiR ε gg e f z g * psiR ε gg e f z h := by
  unfold psiR
  rw [← Complex.exp_add]
  congr 1
  have hs : ∀ a, rootCoord ε e f z (g * h) a + star (rootCoord ε e f z (g * h) a) =
      (rootCoord ε e f z g a + star (rootCoord ε e f z g a)) +
        (rootCoord ε e f z h a + star (rootCoord ε e f z h a)) := by
    intro a
    rw [rootCoord_mul ε e f z hfe hfz hg hh a, star_add]
    ring
  simp only [hs, Finset.sum_add_distrib]
  ring

end Psi

section Dual

variable {D : D7} (X : HidaSetting D)

theorem hE_f_e (a b : Fin D.R.rS) : hE X (X.fR a) (X.eR b) = if b = a then 1 else 0 := by
  apply X.ιE.injective
  show X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd (X.fY a)) (X.crd (X.eX b))) = _
  rw [Formalism.L2.SG.PoincareInHH.Cut.hform_crd, hT_f_e X a b]
  split_ifs <;> simp

theorem hermitian_f_z_zero (u : D.what₂.Word) (a : Fin D.R.rS) : hE X (X.fR a) (X.zR u) = 0 := by
  apply X.ιE.injective
  show X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd (X.fY a)) (X.crd (X.zu u))) = _
  rw [Formalism.L2.SG.PoincareInHH.Cut.hform_crd, (X.zu_orth u a).2, map_zero]

end Dual

section Closed

variable {n r : ℕ}

theorem isClosed_InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} := by
  have hW : ∀ (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ),
      IsClosed {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ y ∈ W} := fun W y =>
    (Submodule.closed_of_finiteDimensional W).preimage
      ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)
  have : {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} =
      ((⋂ a, {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ e a ∈ spanLt e a.1}) ∩
        {g | (g - 1) *ᵥ z ∈ spanLt e r}) ∩
        ⋂ y, ⋂ (_ : ∀ a, hJ ε (e a) y = 0), {g | (g - 1) *ᵥ y ∈ spanLt e r} := by
    ext g
    simp only [InN, InS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [this]
  exact ((isClosed_iInter fun a => hW _ _).inter (hW _ _)).inter
    (isClosed_iInter fun y => isClosed_iInter fun _ => hW _ _)

theorem ninf_closed (I : AutInst) (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : IsClosed (Ninf I e z) := by
  have : Ninf I e z = ⋂ v, (fun s : I.Ginf => uMat (s v)) ⁻¹'
      {g | InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) g} := by
    ext s
    simp only [Ninf, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isClosed_iInter fun v => (isClosed_InN _ _ _).preimage
    (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v)))

end Closed

end Vanish2

theorem psiInfChar_holds : Formalism.L2.SG.TermOp.Vanish.PsiInfChar := by
  intro D X u
  have hfe : ∀ v a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if b = a then 1 else 0 := by
    intro v a b
    rw [hJ_rv, hE_f_e]
    split_ifs <;> simp
  have hfz : ∀ v a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 := by
    intro v a
    rw [hJ_rv, hermitian_f_z_zero, map_zero]
  refine ⟨(NinfSub X.eR (X.zR u)).one_mem, fun s hs t ht =>
    ⟨(NinfSub X.eR (X.zR u)).mul_mem hs ht, ?_⟩, fun s hs => (NinfSub X.eR (X.zR u)).inv_mem hs⟩
  unfold HidaSetting.psiInfU psiInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have : uMat ((s * t) v) = uMat (s v) * uMat (t v) := by simp [uMat]
  rw [this]
  exact psiR_mul _ _ _ _ _ (hfe v) (hfz v) (hs v).1 (ht v).1

theorem rClosedC_holds : Formalism.L2.SG.TermOp.Vanish.RClosedC := by
  intro D X Y u u' t
  have h1 := ninf_closed X.B.I X.eR (X.zR u)
  have h2 := ninf_closed X.B.I X.eR (X.zR u')
  have hc : Continuous fun y : X.B.I.Ginf => t.pt.1⁻¹ * y * t.pt.1 :=
    (continuous_const.mul continuous_id).mul continuous_const
  exact h1.inter (h2.preimage hc)

namespace Vanish2

section RatPtSec

variable {D : D7} (X : HidaSetting D)

def matOf (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  (LinearMap.toMatrix X.bas X.bas (n : (VS D).V →ₗ[D.host.E] (VS D).V)).map X.ιE.symm

theorem crd_matOf (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    X.crd (n y) = matOf X n *ᵥ X.crd y := by
  have h := LinearMap.toMatrix_mulVec_repr X.bas X.bas (n : (VS D).V →ₗ[D.host.E] (VS D).V) y
  funext i
  show X.ιE.symm (X.bas.repr (n y) i) = _
  rw [LinearEquiv.coe_coe] at h
  rw [← h]
  simp only [matOf, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rfl

theorem matOf_comp (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (l : Fin X.B.I.n → X.B.I.E)
    (h : ∀ y, n (m y) = y) : (matOf X n * matOf X m) *ᵥ l = l := by
  obtain ⟨y, rfl⟩ := crd_surj X l
  rw [← Matrix.mulVec_mulVec, ← crd_matOf, ← crd_matOf, h]

theorem matOf_mul_inv (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : matOf X n * matOf X n⁻¹ = 1 :=
  mat_eq_one_of_fix X.B.I Submodule.span_univ fun l _ => matOf_comp X n n⁻¹ l fun y => by
    show (n * n⁻¹) y = y
    rw [mul_inv_cancel]; rfl

theorem matOf_inv_mul (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : matOf X n⁻¹ * matOf X n = 1 :=
  mat_eq_one_of_fix X.B.I Submodule.span_univ fun l _ => matOf_comp X n⁻¹ n l fun y => by
    show (n⁻¹ * n) y = y
    rw [inv_mul_cancel]; rfl

end RatPtSec

theorem unitary_of_hform {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (J M : Matrix (Fin m) (Fin m) A)
    (h : ∀ x y, Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y) :
    Formalism.UG.cT σ M * J * M = J := by
  ext i j
  have hR : Formalism.UG.hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
    unfold Formalism.UG.hform
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hL : Formalism.UG.hform σ J (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) = (Formalism.UG.cT σ M * J * M) i j := by
    simp only [Matrix.mulVec_single_one, Formalism.UG.hform, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.col_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [← hL, h, hR]

def rtReal' (I : AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (v : InfinitePlace I.F) : Formalism.REAL.UJ (I.ε v) :=
  ⟨⟨(I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
    (I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
    by
      have e1 : (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *
          ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
        rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      calc (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v *
            ((I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
          = (I.P v)⁻¹ * ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * (I.P v * (I.P v)⁻¹) *
            ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one, e1, Matrix.mul_one,
              Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul],
    by
      have e1 : ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *
          (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
        rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      calc (I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v *
            ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
          = (I.P v)⁻¹ * (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *
            (I.P v * (I.P v)⁻¹) * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one, e1, Matrix.mul_one,
              Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul]⟩,
  by
    have hγ' : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
    have hc : (Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E)).map (I.φ v) =
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        starRingEnd_apply]
      exact I.cm.cmUnram.2.1 (I.φ v) _
    have hu : ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
      rw [← hc, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
    have hPP : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.conjTranspose_one]
    show ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)ᴴ *
        Formalism.REAL.Jm (I.ε v) * ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) =
        Formalism.REAL.Jm (I.ε v)
    rw [← I.P_spec v]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((I.P v)⁻¹)ᴴ (I.P v)ᴴ, hPP, Matrix.one_mul,
      ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.one_mul]
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [hu]⟩

end Vanish2

theorem ratPt_holds : Formalism.L2.SG.TermOp.Vanish.RatPt := by
  intro D X n hn
  let γ : GL (Fin X.B.I.n) X.B.I.E := ⟨matOf X n, matOf X n⁻¹, matOf_mul_inv X n, matOf_inv_mul X n⟩
  have hγ : γ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
    show Formalism.UG.cT (starRingEnd X.B.I.E) (matOf X n) * X.B.I.J * matOf X n = X.B.I.J
    refine unitary_of_hform _ _ _ fun x y => ?_
    obtain ⟨v, rfl⟩ := crd_surj X x
    obtain ⟨w, rfl⟩ := crd_surj X y
    rw [← crd_matOf, ← crd_matOf]
    apply X.ιE.injective
    rw [Formalism.L2.SG.PoincareInHH.Cut.hform_crd, Formalism.L2.SG.PoincareInHH.Cut.hform_crd, hn]
  have hf : Formalism.UG.bc (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) γ ∈
      Formalism.UG.UPts X.B.I.cm.sig X.B.I.J (Af X.B.I.F) :=
    Formalism.UG.Final.RatPtsLe X.B.I.F X.B.I.E (Fin X.B.I.n) X.B.I.cm.sig X.B.I.J (Af X.B.I.F)
      (Subgroup.mem_map_of_mem _ hγ)
  exact ⟨(fun v => rtReal' X.B.I γ hγ v, ⟨_, hf⟩), γ, hγ, fun v => rfl, rfl, crd_matOf X n⟩

section Final

open Formalism.L2.SG.TermOp.Vanish

theorem psiProd_all : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), Formalism.L2.SG.PoincareInHH.Cut.PsiProd X u :=
  fun _ X u => psiProd_holds X u

theorem chiTrivialC_holds (hK : NilradicalConjLevel) (hCol : ColPass) : ChiTrivialC :=
  chiTrivialC_of nLamNinf_holds nLamNfin_holds hK hCol psiProd_all

theorem ooFundIndepC_of_chi (hC : ChiTrivialC) : Formalism.L2.SG.Full.OOFundIndepC :=
  ooFundIndepC_of nLamNinf_holds hC

theorem ooFundIndepC_holds (hK : NilradicalConjLevel) (hCol : ColPass) : Formalism.L2.SG.Full.OOFundIndepC :=
  ooFundIndepC_of_chi (chiTrivialC_holds hK hCol)

theorem ampWellDefC_of_chi (hK : NilradicalConjLevel) (hC : ChiTrivialC) : Formalism.L2.SG.Full.AmpWellDefC :=
  ampWellDefC_of ratPt_holds nLamNinf_holds nLamNfin_holds hC hK psiProd_all

theorem ampWellDefC_holds (hK : NilradicalConjLevel) (hCol : ColPass) : Formalism.L2.SG.Full.AmpWellDefC :=
  ampWellDefC_of_chi hK (chiTrivialC_holds hK hCol)

theorem lemmaVC_of_chi (hA : AvgCore) (hC : ChiTrivialC) (h3 : RCocompactC) (h4 : NonRelCharC) :
    Formalism.L2.SG.Full.LemmaVC :=
  lemmaVC_of hA ginfUnimod_holds nLamNinf_holds hC psiInfChar_holds rClosedC_holds roDiscreteC_holds h3 h4

theorem lemmaVC_holds (hA : AvgCore) (hK : NilradicalConjLevel) (hCol : ColPass) (h3 : RCocompactC) (h4 : NonRelCharC) :
    Formalism.L2.SG.Full.LemmaVC :=
  lemmaVC_of_chi hA (chiTrivialC_holds hK hCol) h3 h4

end Final

end Formalism.L2.SG.Pf
