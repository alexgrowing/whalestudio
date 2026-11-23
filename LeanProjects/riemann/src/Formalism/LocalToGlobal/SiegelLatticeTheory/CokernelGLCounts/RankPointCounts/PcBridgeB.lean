import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcBridgeA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfIso

noncomputable section

namespace Formalism.L2.SG.Pf.PCount.BI

open Matrix

section Schur

variable {E : Type} [CommRing E] {m : ℕ} (Zm : Matrix (Fin (m + 1)) (Fin (m + 1)) E)

def hd : Matrix (Fin m) (Fin m) E := Zm.submatrix Fin.castSucc Fin.castSucc

def lc (a : Fin m) : E := Zm a.castSucc (Fin.last m)

def lr (b : Fin m) : E := Zm (Fin.last m) b.castSucc

theorem mulVec_castSucc (w : Fin (m + 1) → E) (a : Fin m) :
    (Zm *ᵥ w) a.castSucc = (hd Zm *ᵥ fun b => w b.castSucc) a + lc Zm a * w (Fin.last m) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, hd, lc, submatrix_apply]

theorem mulVec_last (w : Fin (m + 1) → E) :
    (Zm *ᵥ w) (Fin.last m) = lr Zm ⬝ᵥ (fun b => w b.castSucc) + Zm (Fin.last m) (Fin.last m) * w (Fin.last m) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, lr]

theorem schur_identity (hZ : IsUnit Zm.det) (hY : IsUnit (hd Zm).det) (v : Fin (m + 1) → E) :
    lr Zm ⬝ᵥ ((hd Zm)⁻¹ *ᵥ fun a => v a.castSucc) +
      (Zm (Fin.last m) (Fin.last m) - lr Zm ⬝ᵥ ((hd Zm)⁻¹ *ᵥ lc Zm)) * (Zm⁻¹ *ᵥ v) (Fin.last m) = v (Fin.last m) := by
  set w := Zm⁻¹ *ᵥ v with hw
  have hZw : Zm *ᵥ w = v := by rw [hw, mulVec_mulVec, mul_nonsing_inv _ hZ, one_mulVec]

  have hh : (fun a => v a.castSucc) = hd Zm *ᵥ (fun b => w b.castSucc) + w (Fin.last m) • lc Zm := by
    funext a
    rw [← hZw, mulVec_castSucc]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hl : v (Fin.last m) = lr Zm ⬝ᵥ (fun b => w b.castSucc) + Zm (Fin.last m) (Fin.last m) * w (Fin.last m) := by
    rw [← hZw, mulVec_last]
  rw [hh, mulVec_add, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hY, one_mulVec, dotProduct_add,
    dotProduct_smul, hl]
  simp only [smul_eq_mul]
  ring

theorem inv_last_last (hZ : IsUnit Zm.det) :
    Zm⁻¹ (Fin.last m) (Fin.last m) = Ring.inverse Zm.det * (hd Zm).det := by
  rw [inv_def, Matrix.smul_apply, adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, smul_eq_mul]
  have e : ((-1 : E) ^ ((Fin.last m : ℕ) + (Fin.last m : ℕ))) = 1 := by
    rw [← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [e, one_mul]
  rfl

end Schur

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E)
  {m : ℕ}

abbrev toE {k : ℕ} (x : Fin k → M.R) : Fin k → E := fun j => (x j : E)

abbrev alQ (Y : M.Mat m) (row : Fin m → M.R) : M.Cok Y →ₗ[M.R] Qt M.R := M.linQ Y row

abbrev lamQ (Z : M.Mat (m + 1)) : M.Cok Z →ₗ[M.R] Qt M.R := M.lam Z

theorem linQ_mk (Y : M.Mat m) (row : Fin m → M.R) (x : Fin m → M.R) :
    alQ M Y row (Submodule.Quotient.mk x) =
      (Rs M.R).mkQ (toE M row ⬝ᵥ ((Y.Z.map M.R.subtype)⁻¹ *ᵥ toE M x)) := by rfl

theorem lam_mk (Z : M.Mat (m + 1)) (v : Fin (m + 1) → M.R) :
    lamQ M Z (Submodule.Quotient.mk v) = (Rs M.R).mkQ (((Z.Z.map M.R.subtype)⁻¹ *ᵥ toE M v) (Fin.last m)) := by rfl

variable (Y : M.Mat m) (Z : M.Mat (m + 1)) (be al : Fin m → M.R)
  (hY : ∀ a b : Fin m, (Y.Z a b : E) = Z.Z.map M.R.subtype a.castSucc b.castSucc)
  (hbe : ∀ a : Fin m, (be a : E) = Z.Z.map M.R.subtype a.castSucc (Fin.last m))
  (hal : ∀ a : Fin m, (al a : E) = Z.Z.map M.R.subtype (Fin.last m) a.castSucc)
  (u : E) (hu : IsUnit u)
  (hsch : Z.Z.map M.R.subtype (Fin.last m) (Fin.last m) -
    lr (Z.Z.map M.R.subtype) ⬝ᵥ ((hd (Z.Z.map M.R.subtype))⁻¹ *ᵥ lc (Z.Z.map M.R.subtype)) = u)

include hY in
theorem hd_eq : hd (Z.Z.map M.R.subtype) = Y.Z.map M.R.subtype := by
  ext a b
  exact (hY a b).symm

include hbe in
theorem lc_eq : lc (Z.Z.map M.R.subtype) = toE M be := by
  funext a
  exact (hbe a).symm

include hal in
theorem lr_eq : lr (Z.Z.map M.R.subtype) = toE M al := by
  funext a
  exact (hal a).symm

include hY hbe hal hsch in
theorem hb_corner : alQ M Y al (Submodule.Quotient.mk be) + (Rs M.R).mkQ u = 0 := by
  rw [linQ_mk, ← map_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨Z.Z (Fin.last m) (Fin.last m), ?_⟩
  rw [← hsch, hd_eq M Y Z hY, lc_eq M Z be hbe, lr_eq M Z al hal]
  simp only [Algebra.linearMap_apply]
  rw [add_sub_cancel]
  rfl

include hY hbe hal hsch in

theorem schur_M (v : Fin (m + 1) → E) :
    toE M al ⬝ᵥ ((Y.Z.map M.R.subtype)⁻¹ *ᵥ fun a => v a.castSucc) + u * ((Z.Z.map M.R.subtype)⁻¹ *ᵥ v) (Fin.last m) =
      v (Fin.last m) := by
  have hYu : IsUnit (hd (Z.Z.map M.R.subtype)).det := by
    rw [hd_eq M Y Z hY]
    exact Y.unit
  have h := schur_identity (Z.Z.map M.R.subtype) Z.unit hYu v
  rw [hsch, hd_eq M Y Z hY, lr_eq M Z al hal] at h
  exact h

end Model

section Theta

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E)
  {m : ℕ} (Y : M.Mat m) (Z : M.Mat (m + 1)) (be al : Fin m → M.R)
  (hY : ∀ a b : Fin m, (Y.Z a b : E) = Z.Z.map M.R.subtype a.castSucc b.castSucc)
  (hbe : ∀ a : Fin m, (be a : E) = Z.Z.map M.R.subtype a.castSucc (Fin.last m))
  (hal : ∀ a : Fin m, (al a : E) = Z.Z.map M.R.subtype (Fin.last m) a.castSucc)
  (u : E) (hu : IsUnit u)
  (hsch : Z.Z.map M.R.subtype (Fin.last m) (Fin.last m) -
    lr (Z.Z.map M.R.subtype) ⬝ᵥ ((hd (Z.Z.map M.R.subtype))⁻¹ *ᵥ lc (Z.Z.map M.R.subtype)) = u)

def thetaRaw : (Fin (m + 1) → M.R) →ₗ[M.R] M.Cok Y × E :=
  LinearMap.prod ((Submodule.mkQ (LinearMap.range Y.Z.mulVecLin)).comp (LinearMap.funLeft M.R M.R Fin.castSucc))
    ((LinearMap.mulLeft M.R u).comp ((LinearMap.proj (R := M.R) (φ := fun _ : Fin (m + 1) => E) (Fin.last m)).comp
      ((((Z.Z.map M.R.subtype)⁻¹).mulVecLin.restrictScalars M.R).comp
        (LinearMap.compLeft (Algebra.linearMap M.R E) (Fin (m + 1))))))

theorem thetaRaw_apply (v : Fin (m + 1) → M.R) :
    thetaRaw M Y Z u v = (Submodule.Quotient.mk (fun a => v a.castSucc),
      u * ((Z.Z.map M.R.subtype)⁻¹ *ᵥ toE M v) (Fin.last m)) := rfl

include hY hbe hal hsch in
theorem thetaRaw_mem (v : Fin (m + 1) → M.R) : thetaRaw M Y Z u v ∈ NF (alQ M Y al) := by
  show _ ∈ LinearMap.ker _
  rw [LinearMap.mem_ker, thetaRaw_apply]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  rw [linQ_mk, ← map_add, schur_M M Y Z be al hY hbe hal u hsch (toE M v), Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact ⟨v (Fin.last m), rfl⟩

def thetaN : (Fin (m + 1) → M.R) →ₗ[M.R] NF (alQ M Y al) :=
  LinearMap.codRestrict _ (thetaRaw M Y Z u) (thetaRaw_mem M Y Z be al hY hbe hal u hsch)

def Theta : (Fin (m + 1) → M.R) →ₗ[M.R] CG (alQ M Y al) (Submodule.Quotient.mk be) u
    (hb_corner M Y Z be al hY hbe hal u hsch) :=
  (Submodule.mkQ _).comp (thetaN M Y Z be al hY hbe hal u hsch)

theorem Theta_apply (v : Fin (m + 1) → M.R) :
    Theta M Y Z be al hY hbe hal u hsch v =
      Submodule.Quotient.mk ⟨thetaRaw M Y Z u v, thetaRaw_mem M Y Z be al hY hbe hal u hsch v⟩ := rfl

include hY hbe hal hsch in
theorem Theta_surjective : Function.Surjective (Theta M Y Z be al hY hbe hal u hsch) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H p =>
    obtain ⟨⟨c, e⟩, hce⟩ := p
    induction c using Submodule.Quotient.induction_on with
    | H x =>
      have hce' := hce
      change _ ∈ LinearMap.ker _ at hce'
      rw [LinearMap.mem_ker] at hce'
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply] at hce'
      rw [linQ_mk, ← map_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hce'
      obtain ⟨r, hr⟩ := hce'
      change ((r : M.R) : E) = _ at hr
      refine ⟨Fin.snoc (α := fun _ => M.R) x r, ?_⟩
      rw [Theta_apply]
      congr 1
      apply Subtype.ext
      show thetaRaw M Y Z u (Fin.snoc (α := fun _ => M.R) x r) = (Submodule.Quotient.mk x, e)
      rw [thetaRaw_apply]
      have hs := schur_M M Y Z be al hY hbe hal u hsch (toE M (Fin.snoc (α := fun _ => M.R) x r))
      simp only [toE, Fin.snoc_castSucc, Fin.snoc_last] at hs
      refine Prod.ext ?_ ?_
      · show Submodule.Quotient.mk (fun a => Fin.snoc (α := fun _ => M.R) x r a.castSucc) =
          Submodule.Quotient.mk x
        congr 1
        funext a
        simp
      · show u * _ = e
        linear_combination hs + hr

end Theta

section Ker

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E)
  {m : ℕ} (Y : M.Mat m) (Z : M.Mat (m + 1)) (be al : Fin m → M.R)
  (hY : ∀ a b : Fin m, (Y.Z a b : E) = Z.Z.map M.R.subtype a.castSucc b.castSucc)
  (hbe : ∀ a : Fin m, (be a : E) = Z.Z.map M.R.subtype a.castSucc (Fin.last m))
  (hal : ∀ a : Fin m, (al a : E) = Z.Z.map M.R.subtype (Fin.last m) a.castSucc)
  (u : E) (hu : IsUnit u)
  (hsch : Z.Z.map M.R.subtype (Fin.last m) (Fin.last m) -
    lr (Z.Z.map M.R.subtype) ⬝ᵥ ((hd (Z.Z.map M.R.subtype))⁻¹ *ᵥ lc (Z.Z.map M.R.subtype)) = u)

theorem toE_mulVec {k : ℕ} (A : Matrix (Fin k) (Fin k) M.R) (x : Fin k → M.R) :
    toE M (A *ᵥ x) = A.map M.R.subtype *ᵥ toE M x := by
  funext j
  simp [toE, mulVec, dotProduct]

theorem toE_inj {k : ℕ} {x y : Fin k → M.R} (h : toE M x = toE M y) : x = y := by
  funext j
  exact Subtype.ext (congrFun h j)

include hY hbe in

theorem head_rows (x : Fin (m + 1) → M.R) :
    toE M (fun a => (Z.Z *ᵥ x) a.castSucc) = Y.Z.map M.R.subtype *ᵥ toE M (fun a => x a.castSucc) +
      (x (Fin.last m) : E) • toE M be := by
  funext a
  have h1 := mulVec_castSucc (Z.Z.map M.R.subtype) (toE M x) a
  have h2 : toE M (fun a => (Z.Z *ᵥ x) a.castSucc) a = (Z.Z.map M.R.subtype *ᵥ toE M x) a.castSucc :=
    congrFun (toE_mulVec M Z.Z x) a.castSucc
  rw [h2, h1, hd_eq M Y Z hY, lc_eq M Z be hbe]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

include hY hbe hal hsch hu in
theorem Theta_ker : LinearMap.ker (Theta M Y Z be al hY hbe hal u hsch) = LinearMap.range Z.Z.mulVecLin := by
  have hZu := Z.unit
  have hYu := Y.unit

  have hhead : ∀ w : Fin (m + 1) → E, (fun a => (Z.Z.map M.R.subtype *ᵥ w) a.castSucc) =
      Y.Z.map M.R.subtype *ᵥ (fun b => w b.castSucc) + w (Fin.last m) • toE M be := by
    intro w
    funext a
    rw [mulVec_castSucc, hd_eq M Y Z hY, lc_eq M Z be hbe]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker, Theta_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_span_singleton] at hv
    obtain ⟨t, ht⟩ := hv
    have h1 : t • ((Submodule.Quotient.mk be : M.Cok Y), u) = thetaRaw M Y Z u v := congrArg Subtype.val ht
    rw [thetaRaw_apply, Prod.smul_mk] at h1
    obtain ⟨h1a, h1b⟩ := Prod.mk.inj h1

    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h1a
    obtain ⟨y, hy⟩ := h1a
    rw [mulVecLin_apply] at hy

    set W := (Z.Z.map M.R.subtype)⁻¹ *ᵥ toE M v with hW
    have hWl : W (Fin.last m) = (t : E) := by
      have h2 : u * W (Fin.last m) = u * (t : E) := by
        rw [← h1b]
        show _ = u * ((t : M.R) : E)
        rw [Subring.smul_def, smul_eq_mul, mul_comm]
      exact hu.mul_left_cancel h2
    have hZW : Z.Z.map M.R.subtype *ᵥ W = toE M v := by
      rw [hW, mulVec_mulVec, mul_nonsing_inv _ hZu, one_mulVec]
    have hWh : (fun b => W b.castSucc) = toE M (-y) := by
      have h3 := hhead W
      rw [hZW] at h3
      have hvh : (fun a => v a.castSucc) = Y.Z *ᵥ (-y) + t • be := by
        rw [mulVec_neg, hy]
        abel
      have h4 : toE M (fun a => v a.castSucc) = Y.Z.map M.R.subtype *ᵥ toE M (-y) + (t : E) • toE M be := by
        rw [hvh, ← toE_mulVec]
        funext a
        simp [toE, Subring.smul_def]
      have h5 : Y.Z.map M.R.subtype *ᵥ ((fun b => W b.castSucc) - toE M (-y)) = 0 := by
        rw [mulVec_sub]
        have h6 : (fun a => toE M v a.castSucc) = toE M (fun a => v a.castSucc) := rfl
        rw [h6, h4, hWl] at h3
        rw [← add_right_cancel h3, sub_self]
      have h7 := congrArg ((Y.Z.map M.R.subtype)⁻¹ *ᵥ ·) h5
      simp only [mulVec_mulVec, nonsing_inv_mul _ hYu, one_mulVec, mulVec_zero] at h7
      exact sub_eq_zero.mp h7
    refine ⟨Fin.snoc (α := fun _ => M.R) (-y) t, ?_⟩
    rw [mulVecLin_apply]
    apply toE_inj M
    rw [toE_mulVec]
    have hx : toE M (Fin.snoc (α := fun _ => M.R) (-y) t) = W := by
      funext j
      refine Fin.lastCases ?_ (fun b => ?_) j
      · simp [toE, hWl]
      · simp only [toE, Fin.snoc_castSucc]
        exact (congrFun hWh b).symm
    rw [hx, hZW]
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, Theta_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_span_singleton]
    refine ⟨x (Fin.last m), ?_⟩
    apply Subtype.ext
    show x (Fin.last m) • ((Submodule.Quotient.mk be : M.Cok Y), u) = thetaRaw M Y Z u (Z.Z.mulVecLin x)
    rw [thetaRaw_apply, Prod.smul_mk, mulVecLin_apply]
    refine Prod.ext ?_ ?_
    · show x (Fin.last m) • (Submodule.Quotient.mk be : M.Cok Y) =
        Submodule.Quotient.mk (fun a => (Z.Z *ᵥ x) a.castSucc)
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      refine ⟨-(fun a => x a.castSucc), ?_⟩
      have hh := head_rows M Y Z be hY hbe x
      apply toE_inj M
      rw [mulVecLin_apply, toE_mulVec]
      have e1 : toE M (x (Fin.last m) • be - fun a => (Z.Z *ᵥ x) a.castSucc) =
          (x (Fin.last m) : E) • toE M be - toE M (fun a => (Z.Z *ᵥ x) a.castSucc) := by
        funext a
        simp [toE, Subring.smul_def]
      have e2 : toE M (-(fun a => x a.castSucc)) = -toE M (fun a => x a.castSucc) := by
        funext a
        simp [toE]
      rw [e1, e2, hh, mulVec_neg]
      abel
    · show x (Fin.last m) • u = u * ((Z.Z.map M.R.subtype)⁻¹ *ᵥ toE M (Z.Z *ᵥ x)) (Fin.last m)
      rw [toE_mulVec, mulVec_mulVec, nonsing_inv_mul _ hZu, one_mulVec, Subring.smul_def, smul_eq_mul,
        mul_comm]

end Ker

section Final

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E)
  {m : ℕ} (Y : M.Mat m) (Z : M.Mat (m + 1)) (be al : Fin m → M.R)
  (hY : ∀ a b : Fin m, (Y.Z a b : E) = Z.Z.map M.R.subtype a.castSucc b.castSucc)
  (hbe : ∀ a : Fin m, (be a : E) = Z.Z.map M.R.subtype a.castSucc (Fin.last m))
  (hal : ∀ a : Fin m, (al a : E) = Z.Z.map M.R.subtype (Fin.last m) a.castSucc)
  (u : E) (hu : IsUnit u)
  (hsch : Z.Z.map M.R.subtype (Fin.last m) (Fin.last m) -
    lr (Z.Z.map M.R.subtype) ⬝ᵥ ((hd (Z.Z.map M.R.subtype))⁻¹ *ᵥ lc (Z.Z.map M.R.subtype)) = u)

def thetaEquiv : M.Cok Z ≃ₗ[M.R] CG (alQ M Y al) (Submodule.Quotient.mk be) u (hb_corner M Y Z be al hY hbe hal u hsch) :=
  (Submodule.quotEquivOfEq _ _ (Theta_ker M Y Z be al hY hbe hal u hu hsch).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (Theta_surjective M Y Z be al hY hbe hal u hsch))

def thetaIso : IsoT M.R (M.eCls Z) (eG (alQ M Y al) (Submodule.Quotient.mk be) u (hb_corner M Y Z be al hY hbe hal u hsch))
    (lamQ M Z) (lamG (alQ M Y al) (Submodule.Quotient.mk be) u (hb_corner M Y Z be al hY hbe hal u hsch) hu) :=
  ⟨thetaEquiv M Y Z be al hY hbe hal u hu hsch, by
    show Theta M Y Z be al hY hbe hal u hsch (Pi.single (Fin.last m) 1) = _
    rw [Theta_apply]
    unfold eG
    congr 1
    apply Subtype.ext
    show thetaRaw M Y Z u (Pi.single (Fin.last m) 1) = ((0 : M.Cok Y), (1 : E))
    rw [thetaRaw_apply]
    have h := schur_M M Y Z be al hY hbe hal u hsch (toE M (Pi.single (Fin.last m) 1))
    have e1 : (fun a : Fin m => (Pi.single (Fin.last m) (1 : M.R) : Fin (m + 1) → M.R) a.castSucc) = 0 := by
      funext a; simp [Fin.castSucc_ne_last]
    have e2 : (fun a : Fin m => toE M (Pi.single (Fin.last m) (1 : M.R)) a.castSucc) = 0 := by
      funext a; simp [toE, Fin.castSucc_ne_last]
    rw [e2, mulVec_zero, dotProduct_zero, zero_add] at h
    simp only [toE, Pi.single_eq_same, OneMemClass.coe_one] at h
    rw [e1, h]
    rfl,
  fun c => by
    induction c using Submodule.Quotient.induction_on with
    | H v =>
      show lamG (alQ M Y al) (Submodule.Quotient.mk be) u (hb_corner M Y Z be al hY hbe hal u hsch) hu
        (Theta M Y Z be al hY hbe hal u hsch v) = lamQ M Z (Submodule.Quotient.mk v)
      rw [Theta_apply, lamG_mk, lam_mk]
      show (Rs M.R).mkQ (((hu.unit⁻¹ : Eˣ) : E) * (u * _)) = _
      rw [← mul_assoc, show ((hu.unit⁻¹ : Eˣ) : E) * u = 1 by simp, one_mul]
      rfl⟩

end Final

section SchurEq

variable {E : Type} [CommRing E] {m : ℕ}

theorem hd_shift (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (n : E) :
    hd (P + n • (Formalism.L2.SG.Pf.AtPt.Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) E)) = hd P := by
  ext a b
  simp [hd, Formalism.L2.SG.Pf.AtPt.Ecorner, Fin.castSucc_ne_last]

theorem schur_eq {n s : E} {P X L U : Matrix (Fin (m + 1)) (Fin (m + 1)) E} (hL : Formalism.L2.SG.Pf.AtPt.IsLo L)
    (hU : Formalism.L2.SG.Pf.AtPt.IsUp U) (hP : P = L * X * U)
    (hX : ∀ a : Fin m, X a.castSucc (Fin.last m) = 0 ∧ X (Fin.last m) a.castSucc = 0)
    (hs : X (Fin.last m) (Fin.last m) = s) (Zm : Matrix (Fin (m + 1)) (Fin (m + 1)) E)
    (hZm : Zm = P + n • (Formalism.L2.SG.Pf.AtPt.Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) E)) (hZu : IsUnit Zm.det) (hYu : IsUnit (hd Zm).det) :
    Zm (Fin.last m) (Fin.last m) - lr Zm ⬝ᵥ ((hd Zm)⁻¹ *ᵥ lc Zm) = s + n := by
  have esgn : ((-1 : E)) ^ ((Fin.last m : ℕ) + (Fin.last m : ℕ)) = 1 := by
    rw [← two_mul, pow_mul, neg_one_sq, one_pow]
  set S := Zm (Fin.last m) (Fin.last m) - lr Zm ⬝ᵥ ((hd Zm)⁻¹ *ᵥ lc Zm) with hSdef

  have hS : S * (hd Zm).det = Zm.det := by
    have h1 := schur_identity Zm hZu hYu (Pi.single (Fin.last m) 1)
    have e0 : (fun a : Fin m => (Pi.single (Fin.last m) (1 : E) : Fin (m + 1) → E) a.castSucc) = 0 := by
      funext a
      simp [Fin.castSucc_ne_last]
    rw [e0, mulVec_zero, dotProduct_zero, zero_add, Pi.single_eq_same] at h1
    have e1 : (Zm⁻¹ *ᵥ Pi.single (Fin.last m) 1) (Fin.last m) = Zm⁻¹ (Fin.last m) (Fin.last m) := by
      simp [mulVec, dotProduct, Pi.single_apply]
    rw [e1, inv_last_last Zm hZu] at h1
    have key : S * (hd Zm).det = S * (Ring.inverse Zm.det * (hd Zm).det) * Zm.det := by
      rw [mul_comm (Ring.inverse Zm.det), mul_assoc, mul_assoc, Ring.inverse_mul_cancel _ hZu, mul_one]
    rw [key, h1, one_mul]

  have hdetL : L.det = 1 := by
    rw [det_of_lowerTriangular L (fun i j hij => hL.2 i j (OrderDual.toDual_lt_toDual.mp hij))]
    simp [hL.1]
  have hdetU : U.det = 1 := by
    rw [det_of_upperTriangular (fun i j hij => hU.2 j i hij)]
    simp [hU.1]
  have hdetLh : (hd L).det = 1 := by
    rw [det_of_lowerTriangular (hd L) (fun i j hij =>
      hL.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr (OrderDual.toDual_lt_toDual.mp hij)))]
    simp [hd, hL.1]
  have hdetUh : (hd U).det = 1 := by
    rw [det_of_upperTriangular (M := hd U) (fun i j hij =>
      hU.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij))]
    simp [hd, hU.1]

  have hhd : hd P = hd L * hd X * hd U := by
    rw [hP]
    ext a b
    simp [hd, mul_apply, Fin.sum_univ_castSucc, hL.2 _ _ (Fin.castSucc_lt_last a),
      hU.2 _ _ (Fin.castSucc_lt_last b)]
  have hdetP : P.det = X.det := by
    rw [hP, det_mul, det_mul, hdetL, hdetU, one_mul, mul_one]
  have hdetX : X.det = s * (hd X).det := by
    rw [det_succ_column X (Fin.last m), Fin.sum_univ_castSucc]
    simp only [(hX _).1, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, hs, Fin.succAbove_last, esgn,
      one_mul]
    rfl
  have hdetZ : Zm.det = P.det + n * (hd P).det := by
    rw [det_succ_column Zm (Fin.last m), det_succ_column P (Fin.last m), Fin.sum_univ_castSucc,
      Fin.sum_univ_castSucc]
    have hsub : ∀ i : Fin (m + 1), Zm.submatrix i.succAbove (Fin.last m).succAbove =
        P.submatrix i.succAbove (Fin.last m).succAbove := by
      intro i
      ext a b
      simp [hZm, Formalism.L2.SG.Pf.AtPt.Ecorner, Fin.succAbove_last, Fin.castSucc_ne_last]
    have hZl : ∀ a : Fin m, Zm a.castSucc (Fin.last m) = P a.castSucc (Fin.last m) := by
      intro a
      simp [hZm, Formalism.L2.SG.Pf.AtPt.Ecorner, Fin.castSucc_ne_last]
    have hZll : Zm (Fin.last m) (Fin.last m) = P (Fin.last m) (Fin.last m) + n := by
      simp [hZm, Formalism.L2.SG.Pf.AtPt.Ecorner]
    simp only [hZl, hZll]
    simp only [hsub]
    rw [esgn, one_mul, one_mul, Fin.succAbove_last]
    simp only [hd]
    ring
  have hhdZ : hd Zm = hd P := by
    rw [hZm, hd_shift]
  have hD : (hd Zm).det = (hd X).det := by
    rw [hhdZ, hhd, det_mul, det_mul, hdetLh, hdetUh, one_mul, mul_one]
  rw [hdetZ, hdetP, hdetX, hhd, det_mul, det_mul, hdetLh, hdetUh, one_mul, mul_one, ← hD] at hS
  have hfin : S * (hd Zm).det = (s + n) * (hd Zm).det := by
    rw [hS]
    ring
  exact (hYu.mul_left_inj).mp hfin

end SchurEq

theorem integralIsomorphism_holds : Formalism.L2.SG.Pf.PCount.BridgeIso := by
  intro F _ _ _ E _ _ _ _ M m n s P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ hL₁ hU₁ hL₂ hU₂ hP₁ hP₂ hX hs₁ hs₂ hu hn
    Y₁ Y₂ be₁ be₂ al₁ al₂ hY hbal hR₁ hR₂ Z₁ Z₂ hZ₁ hZ₂

  have hY1 : ∀ a b : Fin m, (Y₁.Z a b : E) = Z₁.Z.map M.R.subtype a.castSucc b.castSucc := by
    intro a b
    rw [hZ₁]
    simp [Formalism.L2.SG.Pf.AtPt.Ecorner, Fin.castSucc_ne_last, (hY a b).1]
  have hY2 : ∀ a b : Fin m, (Y₂.Z a b : E) = Z₂.Z.map M.R.subtype a.castSucc b.castSucc := by
    intro a b
    rw [hZ₂]
    simp [Formalism.L2.SG.Pf.AtPt.Ecorner, Fin.castSucc_ne_last, (hY a b).2]
  have hbe1 : ∀ a : Fin m, (be₁ a : E) = Z₁.Z.map M.R.subtype a.castSucc (Fin.last m) := by
    intro a
    rw [hZ₁]
    simp [Formalism.L2.SG.Pf.AtPt.Ecorner, Fin.castSucc_ne_last, (hbal a).1]
  have hbe2 : ∀ a : Fin m, (be₂ a : E) = Z₂.Z.map M.R.subtype a.castSucc (Fin.last m) := by
    intro a
    rw [hZ₂]
    simp [Formalism.L2.SG.Pf.AtPt.Ecorner, Fin.castSucc_ne_last, (hbal a).2.1]
  have hal1 : ∀ a : Fin m, (al₁ a : E) = Z₁.Z.map M.R.subtype (Fin.last m) a.castSucc := by
    intro a
    rw [hZ₁]
    simp [Formalism.L2.SG.Pf.AtPt.Ecorner, Fin.castSucc_ne_last, (hbal a).2.2.1]
  have hal2 : ∀ a : Fin m, (al₂ a : E) = Z₂.Z.map M.R.subtype (Fin.last m) a.castSucc := by
    intro a
    rw [hZ₂]
    simp [Formalism.L2.SG.Pf.AtPt.Ecorner, Fin.castSucc_ne_last, (hbal a).2.2.2]

  have hsch1 := schur_eq hL₁ hU₁ hP₁ (fun a => ⟨(hX a).1, (hX a).2.1⟩) hs₁ _ hZ₁ Z₁.unit
    (by rw [hd_eq M Y₁ Z₁ hY1]; exact Y₁.unit)
  have hsch2 := schur_eq hL₂ hU₂ hP₂ (fun a => ⟨(hX a).2.2.1, (hX a).2.2.2⟩) hs₂ _ hZ₂ Z₂.unit
    (by rw [hd_eq M Y₂ Z₂ hY2]; exact Y₂.unit)
  have θ₁ := thetaIso M Y₁ Z₁ be₁ al₁ hY1 hbe1 hal1 (s + n) hu hsch1
  have θ₂ := thetaIso M Y₂ Z₂ be₂ al₂ hY2 hbe2 hal2 (s + n) hu hsch2
  show Nat.card (IsoT M.R (Submodule.Quotient.mk be₁ : M.Cok Y₁) (Submodule.Quotient.mk be₂ : M.Cok Y₂)
    (alQ M Y₁ al₁) (alQ M Y₂ al₂)) = Nat.card (M.Iso Z₁ Z₂)
  rw [card_isoT_G (hu := hu) (hb₁ := hb_corner M Y₁ Z₁ be₁ al₁ hY1 hbe1 hal1 (s + n) hsch1)
    (hb₂ := hb_corner M Y₂ Z₂ be₂ al₂ hY2 hbe2 hal2 (s + n) hsch2)]
  exact (card_isoT_congr θ₁ θ₂).symm

end Formalism.L2.SG.Pf.PCount.BI
