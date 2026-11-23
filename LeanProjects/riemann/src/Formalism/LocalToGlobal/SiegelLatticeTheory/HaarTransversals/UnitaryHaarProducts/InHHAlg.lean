import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHCut
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace TensorProduct Classical ENNReal NNReal
open Matrix

namespace Formalism.L2.SG.PoincareInHH.Cut

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M : Matrix n n A) (hM : Formalism.UG.cT σ M * J * M = J) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := by
  have key : ∀ a b : n → A, Formalism.UG.hform σ J a b = (fun i => σ (a i)) ⬝ᵥ (J *ᵥ b) := by
    intro a b
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hx : (fun i => σ ((M *ᵥ x) i)) = (fun i => σ (x i)) ᵥ* Formalism.UG.cT σ M := by
    funext i
    simp [Formalism.UG.cT, vecMul, mulVec, dotProduct, mul_comm]
  rw [key, key, hx, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hM]

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hA_fmat (g : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I (X.B.I.fmat g *ᵥ x) (X.B.I.fmat g *ᵥ y) = hA X.B.I x y := by
  show Formalism.UG.hform _ _ _ _ = Formalism.UG.hform _ _ _ _
  exact hform_mulVec (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)))
    (X.B.I.fmat g) g.2 x y

theorem fmat_mul (a b : X.B.I.Gf) : X.B.I.fmat (a * b) = X.B.I.fmat a * X.B.I.fmat b := by
  simp [AutInst.fmat]

theorem fmat_inv_mul (a : X.B.I.Gf) : X.B.I.fmat a⁻¹ * X.B.I.fmat a = 1 := by
  simp [AutInst.fmat]

theorem fmat_mul_inv (a : X.B.I.Gf) : X.B.I.fmat a * X.B.I.fmat a⁻¹ = 1 := by
  simp [AutInst.fmat]

theorem hfin_fix (h : Hfin X u) (v : Fin X.B.I.n → X.B.I.E) (hv : v ∈ fixSet X u) :
    X.B.I.fmat (h : X.B.I.Gf) *ᵥ incl X.B.I v = incl X.B.I v := h.2 v hv

theorem hfin_fix_inv (h : Hfin X u) (v : Fin X.B.I.n → X.B.I.E) (hv : v ∈ fixSet X u) :
    X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I v = incl X.B.I v := by
  exact (Subgroup.inv_mem (Hfin X u) h.2) v hv

theorem eR_mem_fix (a : Fin D.R.rS) : X.eR a ∈ fixSet X u := Or.inl (Or.inl ⟨a, rfl⟩)
theorem fR_mem_fix (a : Fin D.R.rS) : X.fR a ∈ fixSet X u := Or.inl (Or.inr ⟨a, rfl⟩)
theorem zR_mem_fix : X.zR u ∈ fixSet X u := Or.inr rfl

theorem nxt_mem_fix (a : Fin D.R.rS) : nxt X.eR (X.zR u) a ∈ fixSet X u := by
  unfold Formalism.L2.SG.HidaSetting.nxt
  split_ifs
  · exact eR_mem_fix X u _
  · exact zR_mem_fix X u

theorem mulVec_mem_span_of_fix {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n A) (s : Set (n → A)) (hs : ∀ v ∈ s, M *ᵥ v = v) (y : n → A)
    (hy : y ∈ Submodule.span A s) : M *ᵥ y ∈ Submodule.span A s := by
  have key : Submodule.span A s ≤ (Submodule.span A s).comap M.mulVecLin := by
    refine Submodule.span_le.2 fun v hv => ?_
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, hs v hv]
    exact Submodule.subset_span hv
  simpa only [Submodule.mem_comap, Matrix.mulVecLin_apply] using key hy

theorem conj_sub_mulVec (h n : X.B.I.Gf) (y : VA X.B.I) :
    (X.B.I.fmat (h * n * h⁻¹) - 1) *ᵥ y =
      X.B.I.fmat h *ᵥ ((X.B.I.fmat n - 1) *ᵥ (X.B.I.fmat h⁻¹ *ᵥ y)) := by
  rw [fmat_mul, fmat_mul, mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    fmat_mul_inv]

theorem nfinConj_holds : NfinConj X u := by
  intro h n hn
  have hfixE : ∀ b, X.B.I.fmat (h : X.B.I.Gf) *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) :=
    fun b => hfin_fix X u h _ (eR_mem_fix X u b)
  have hpresI : ∀ T : Set (Fin D.R.rS), ∀ y ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
      ((fun b => incl X.B.I (X.eR b)) '' T), X.B.I.fmat (h : X.B.I.Gf) *ᵥ y ∈
        Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' T) :=
    fun T y hy => mulVec_mem_span_of_fix _ _ (by rintro _ ⟨b, _, rfl⟩; exact hfixE b) y hy
  have hpresR : ∀ y ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)),
      X.B.I.fmat (h : X.B.I.Gf) *ᵥ y ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)) :=
    fun y hy => mulVec_mem_span_of_fix _ _ (by rintro _ ⟨b, rfl⟩; exact hfixE b) y hy
  have hinvfix : ∀ v ∈ fixSet X u, X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I v = incl X.B.I v :=
    fun v hv => hfin_fix_inv X u h v hv
  refine ⟨⟨fun a => ?_, ?_, fun y hy => ?_⟩, ?_⟩
  · rw [conj_sub_mulVec, hinvfix _ (eR_mem_fix X u a)]
    exact hpresI _ _ (hn.1 a)
  · rw [conj_sub_mulVec, hinvfix _ (zR_mem_fix X u)]
    exact hpresR _ hn.2.1
  · rw [conj_sub_mulVec]
    refine hpresR _ (hn.2.2 _ fun a => ?_)
    have e1 := hA_fmat X (h : X.B.I.Gf)⁻¹ (incl X.B.I (X.eR a)) y
    rw [hinvfix _ (eR_mem_fix X u a)] at e1
    rw [e1]
    exact hy a
  · simp only [Formalism.L2.SG.HidaSetting.HidaSetting.psiFinU, Formalism.L2.SG.HidaSetting.psiFin]
    congr 2
    refine Finset.sum_congr rfl fun a _ => ?_
    calc hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat ((h : X.B.I.Gf) * n * (h : X.B.I.Gf)⁻¹) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a))
        = hA X.B.I (X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I (X.fR a))
            (X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ (X.B.I.fmat ((h : X.B.I.Gf) * n * (h : X.B.I.Gf)⁻¹) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a))) :=
          (hA_fmat X _ _ _).symm
      _ = hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat n *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) := by
          rw [hinvfix _ (fR_mem_fix X u a), mulVec_mulVec, fmat_mul, fmat_mul, ← mul_assoc, ← mul_assoc,
            fmat_inv_mul, one_mul, ← mulVec_mulVec, hinvfix _ (nxt_mem_fix X u a)]

theorem level_subgroup_eq_support (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized) : X.K2 = {x | X.B.e x ≠ 0} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [X.e_eq x]
  constructor
  · intro hx
    have hx' : x ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hx
    rw [if_pos hx']
    have hn : ‖X.chi2 x‖ = 1 := hK.2.2.2.2 x hx
    have hvol : (X.B.μf X.K2).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKL.2.2.1.ne', hKL.2.2.2.ne⟩
    have hc : star (X.chi2 x) ≠ 0 := by
      intro h0; rw [star_eq_zero] at h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
    exact div_ne_zero hc (by exact_mod_cast hvol)
  · intro hx
    by_contra hnot
    have hnot' : x ∉ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hnot
    rw [if_neg hnot'] at hx
    exact hx rfl

theorem level_subgroup_isClopen (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized) : IsClopen X.K2 := by
  rw [level_subgroup_eq_support X hK hKL]
  have h := (X.B.e_adm.1).isClopen_fiber 0
  have : {x | X.B.e x ≠ 0} = (X.B.e ⁻¹' {0})ᶜ := by ext; simp
  rw [this]
  exact h.compl

theorem level_subgroup_measurable (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized) : MeasurableSet X.K2 := (level_subgroup_isClopen X hK hKL).isOpen.measurableSet

section KuK0

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem kset_of_conj (h : X.B.I.Gf) (hh : (X.xu u)⁻¹ * h * X.xu u ∈ X.K2) : h ∈ X.B.I.Kset := by
  have hx : ((X.xu u : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈
      Formalism.UG.stabGL X.B.I.Lf := X.xu_K u
  have hk : (((X.xu u)⁻¹ * h * X.xu u : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈
      Formalism.UG.stabGL X.B.I.Lf := hh.1
  have e : (h : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) =
      (X.xu u : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) *
        (((X.xu u)⁻¹ * h * X.xu u : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) *
          (X.xu u : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))⁻¹ := by
    push_cast; group
  show (h : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ Formalism.UG.stabGL X.B.I.Lf
  rw [e]
  exact mul_mem (mul_mem hx hk) (inv_mem hx)

theorem Ku_le_K0 (hK : X.LevelSubgroupCharacter) : Ku X u hK ≤ K0 X u := by
  intro h hh
  apply Subgroup.subset_closure
  have hh' : (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u ∈ X.K2 := hh
  have hKs : (h : X.B.I.Gf) ∈ X.B.I.Kset := kset_of_conj X u _ hh'
  have hKs' : (h : X.B.I.Gf)⁻¹ ∈ X.B.I.Kset := by
    show ((((h : X.B.I.Gf)⁻¹ : X.B.I.Gf)) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈
      Formalism.UG.stabGL X.B.I.Lf
    push_cast
    exact inv_mem hKs
  refine ⟨fun y hy => ⟨⟨(hKs y).1 hy.1, fun a => ⟨?_, ?_, ?_⟩⟩, ⟨(hKs' y).1 hy.1, fun a => ⟨?_, ?_, ?_⟩⟩⟩, ?_⟩
  · rw [← hfin_fix X u h _ (eR_mem_fix X u a), hA_fmat]; exact (hy.2 a).1
  · rw [← hfin_fix X u h _ (fR_mem_fix X u a), hA_fmat]; exact (hy.2 a).2.1
  · rw [← hfin_fix X u h _ (zR_mem_fix X u), hA_fmat]; exact (hy.2 a).2.2
  · rw [← hfin_fix_inv X u h _ (eR_mem_fix X u a), hA_fmat]; exact (hy.2 a).1
  · rw [← hfin_fix_inv X u h _ (fR_mem_fix X u a), hA_fmat]; exact (hy.2 a).2.1
  · rw [← hfin_fix_inv X u h _ (zR_mem_fix X u), hA_fmat]; exact (hy.2 a).2.2
  · refine ⟨fun a => ⟨1, Nat.coprime_one_left _, ?_⟩, ⟨1, Nat.coprime_one_left _, ?_⟩,
      fun i => ⟨1, Nat.coprime_one_left _, ?_⟩⟩
    · simpa using hh'.2.1 a
    · simpa using hh'.2.2.1
    · simpa using hh'.2.2.2 i

end KuK0

section NGroup

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem sigA_inclE (e : X.B.I.E) :
    sigA X.B.I (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) e) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (starRingEnd X.B.I.E e) := by
  simp [Formalism.UG.sigR, Formalism.UG.inclE] <;> rfl

theorem hA_incl (x y : Fin X.B.I.n → X.B.I.E) :
    hA X.B.I (incl X.B.I x) (incl X.B.I y) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x y) := by
  simp only [hA, Formalism.UG.hform, incl, Matrix.map_apply, map_sum, map_mul, sigA_inclE]

theorem hform_crd (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w)) = (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, HidaSetting.crd, crdOf, starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply,
    X.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem hA_crd (v w : (VS D).V) :
    hA X.B.I (incl X.B.I (X.crd v)) (incl X.B.I (X.crd w)) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((VS D).hT v w)) := by
  rw [hA_incl, ← hform_crd X v w, RingEquiv.symm_apply_apply]

theorem hA_f_e (a c : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I (X.eR c)) = if c = a then 1 else 0 := by
  have h := ((VS D).herm.eq (X.eX c) (X.fY a))
  simp only [X.ef] at h
  rw [HidaSetting.fR, HidaSetting.eR, hA_crd, ← h]
  split_ifs <;> simp

theorem adelicHermitian_hyperbolicF_anisotropic_eq_zero (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I (X.zR u)) = 0 := by
  rw [HidaSetting.fR, HidaSetting.zR, hA_crd, (X.zu_orth u a).2]
  simp

def hAlin (x : VA X.B.I) : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] X.B.I.E ⊗[X.B.I.F] Af X.B.I.F where
  toFun := hA X.B.I x
  map_add' y z := by
    simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem hAlin_apply (x y : VA X.B.I) : hAlin X x y = hA X.B.I x y := rfl

def Usp (m : ℕ) : Submodule (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (VA X.B.I) :=
  Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' {b : Fin D.R.rS | b.1 < m})

theorem usp_mono {m m' : ℕ} (h : m ≤ m') : Usp X m ≤ Usp X m' := by
  unfold Usp
  exact Submodule.span_mono (by rintro _ ⟨b, hb, rfl⟩; exact ⟨b, by simp only [Set.mem_setOf_eq] at hb ⊢; omega, rfl⟩)

theorem usp_range : Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)) =
    Usp X D.R.rS := by
  unfold Usp
  congr 1
  ext v
  simp

theorem usp_zero : Usp X 0 = ⊥ := by
  simp [Usp]

theorem hA_f_usp (a : Fin D.R.rS) : ∀ y ∈ Usp X a.1, hA X.B.I (incl X.B.I (X.fR a)) y = 0 := by
  intro y hy
  have key : Usp X a.1 ≤ LinearMap.ker (hAlin X (incl X.B.I (X.fR a))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    simp only [Set.mem_setOf_eq] at hb
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hAlin_apply, hA_f_e]
    rw [if_neg]
    rintro rfl
    exact lt_irrefl _ hb
  simpa only [LinearMap.mem_ker, hAlin_apply] using key hy

variable {X u}

theorem nfin_sub_le {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) (m : ℕ) :
    ∀ y ∈ Usp X m, (X.B.I.fmat n - 1) *ᵥ y ∈ Usp X (m - 1) := by
  intro y hy
  have key : Usp X m ≤ (Usp X (m - 1)).comap (X.B.I.fmat n - 1).mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    simp only [Set.mem_setOf_eq] at hb
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    exact usp_mono X (show b.1 ≤ m - 1 by omega) (hn.1 b)
  simpa only [Submodule.mem_comap, Matrix.mulVecLin_apply] using key hy

theorem nfin_pres {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) (m : ℕ) :
    ∀ y ∈ Usp X m, X.B.I.fmat n *ᵥ y ∈ Usp X m := by
  intro y hy
  have h1 : X.B.I.fmat n *ᵥ y = (X.B.I.fmat n - 1) *ᵥ y + y := by rw [sub_mulVec, one_mulVec, sub_add_cancel]
  rw [h1]
  exact add_mem (usp_mono X (Nat.sub_le m 1) (nfin_sub_le hn m y hy)) hy

theorem nfin_inv_pres {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) :
    ∀ m, ∀ y ∈ Usp X m, X.B.I.fmat n⁻¹ *ᵥ y ∈ Usp X m := by
  intro m
  induction m with
  | zero =>
    intro y hy
    rw [usp_zero, Submodule.mem_bot] at hy
    subst hy
    rw [mulVec_zero]
    exact zero_mem _
  | succ k ih =>
    intro y hy
    have h1 : X.B.I.fmat n⁻¹ *ᵥ y = y - X.B.I.fmat n⁻¹ *ᵥ ((X.B.I.fmat n - 1) *ᵥ y) := by
      rw [mulVec_mulVec, Matrix.mul_sub, fmat_inv_mul, Matrix.mul_one, sub_mulVec, one_mulVec, sub_sub_cancel]
    rw [h1]
    exact sub_mem hy (usp_mono X (Nat.le_succ k) (ih _ (by simpa using nfin_sub_le hn (k + 1) y hy)))

theorem mul_sub_one_mulVec (a b : X.B.I.Gf) (y : VA X.B.I) :
    (X.B.I.fmat (a * b) - 1) *ᵥ y = X.B.I.fmat a *ᵥ ((X.B.I.fmat b - 1) *ᵥ y) + (X.B.I.fmat a - 1) *ᵥ y := by
  rw [fmat_mul]
  simp only [sub_mulVec, mulVec_sub, mulVec_mulVec, one_mulVec, Matrix.mul_sub, Matrix.mul_one]
  abel

theorem inv_sub_one_mulVec (a : X.B.I.Gf) (y : VA X.B.I) :
    (X.B.I.fmat a⁻¹ - 1) *ᵥ y = -(X.B.I.fmat a⁻¹ *ᵥ ((X.B.I.fmat a - 1) *ᵥ y)) := by
  rw [mulVec_mulVec, Matrix.mul_sub, fmat_inv_mul, Matrix.mul_one, sub_mulVec, sub_mulVec, one_mulVec, neg_sub]

theorem nfin_ca_mul {n n' : X.B.I.Gf} (hn : n ∈ X.NfinU u) (hn' : n' ∈ X.NfinU u) (a : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat (n * n') *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) =
      hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat n *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) +
        hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat n' *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) := by
  have hadd : ∀ p q : VA X.B.I, hA X.B.I (incl X.B.I (X.fR a)) (p + q) = hA X.B.I (incl X.B.I (X.fR a)) p + hA X.B.I (incl X.B.I (X.fR a)) q :=
    fun p q => by simpa only [hAlin_apply] using (hAlin X (incl X.B.I (X.fR a))).map_add p q
  have hsub : ∀ p q : VA X.B.I, hA X.B.I (incl X.B.I (X.fR a)) (p - q) = hA X.B.I (incl X.B.I (X.fR a)) p - hA X.B.I (incl X.B.I (X.fR a)) q :=
    fun p q => by simpa only [hAlin_apply] using (hAlin X (incl X.B.I (X.fR a))).map_sub p q
  have hw : (X.B.I.fmat n' - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a) ∈ Usp X (a.1 + 1) := by
    unfold Formalism.L2.SG.HidaSetting.nxt
    split_ifs with h
    · exact hn'.1 ⟨a.1 + 1, h⟩
    · have hr : a.1 + 1 = D.R.rS := by have := a.2; omega
      rw [hr, ← usp_range]
      exact hn'.2.1
  have hv0 : hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I (nxt X.eR (X.zR u) a)) = 0 := by
    unfold Formalism.L2.SG.HidaSetting.nxt
    split_ifs with h
    · rw [hA_f_e, if_neg]
      intro h'
      have := congrArg Fin.val h'
      simp at this
    · exact adelicHermitian_hyperbolicF_anisotropic_eq_zero X u a
  have hfix : hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat n *ᵥ ((X.B.I.fmat n' - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a))) =
      hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat n' - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) := by
    have e1 : X.B.I.fmat n *ᵥ ((X.B.I.fmat n' - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) =
        (X.B.I.fmat n - 1) *ᵥ ((X.B.I.fmat n' - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) + (X.B.I.fmat n' - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a) := by
      rw [sub_mulVec (X.B.I.fmat n), one_mulVec, sub_add_cancel]
    rw [e1, hadd, hA_f_usp X a _ (by simpa using nfin_sub_le hn (a.1 + 1) _ hw), zero_add]
  have e2 : X.B.I.fmat (n * n') *ᵥ incl X.B.I (nxt X.eR (X.zR u) a) = X.B.I.fmat n *ᵥ incl X.B.I (nxt X.eR (X.zR u) a) + X.B.I.fmat n *ᵥ ((X.B.I.fmat n' - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) := by
    rw [fmat_mul, ← mulVec_mulVec, sub_mulVec (X.B.I.fmat n'), one_mulVec, mulVec_sub]
    abel
  rw [e2, hadd, hfix, sub_mulVec, one_mulVec, hsub, hv0, sub_zero]

theorem nfinGroup_holds : NfinGroup X u := by
  refine ⟨fun n hn n' hn' => ⟨?_, ?_⟩, fun n hn => ?_⟩
  · refine ⟨fun a => ?_, ?_, fun y hy => ?_⟩
    · rw [mul_sub_one_mulVec]
      exact add_mem (nfin_pres hn a.1 _ (hn'.1 a)) (hn.1 a)
    · rw [mul_sub_one_mulVec, usp_range]
      exact add_mem (nfin_pres hn _ _ (by rw [← usp_range]; exact hn'.2.1)) (by rw [← usp_range]; exact hn.2.1)
    · rw [mul_sub_one_mulVec, usp_range]
      exact add_mem (nfin_pres hn _ _ (by rw [← usp_range]; exact hn'.2.2 y hy))
        (by rw [← usp_range]; exact hn.2.2 y hy)
  · simp only [Formalism.L2.SG.HidaSetting.HidaSetting.psiFinU, Formalism.L2.SG.HidaSetting.psiFin, Formalism.L2.SG.HidaSetting.divN]
    rw [← X.psiEf_add, ← mul_add, ← Finset.sum_add_distrib]
    congr 2
    exact Finset.sum_congr rfl fun a _ => nfin_ca_mul hn hn' a
  · refine ⟨fun a => ?_, ?_, fun y hy => ?_⟩
    · rw [inv_sub_one_mulVec]
      exact neg_mem (nfin_inv_pres hn a.1 _ (hn.1 a))
    · rw [inv_sub_one_mulVec, usp_range]
      exact neg_mem (nfin_inv_pres hn _ _ (by rw [← usp_range]; exact hn.2.1))
    · rw [inv_sub_one_mulVec, usp_range]
      exact neg_mem (nfin_inv_pres hn _ _ (by rw [← usp_range]; exact hn.2.2 y hy))

end NGroup

section Level

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def KsetSplit : Prop :=
  ∀ n ∈ X.NfinU u, ∀ h : Hfin X u, n * (h : X.B.I.Gf) ∈ X.B.I.Kset → (h : X.B.I.Gf) ∈ X.B.I.Kset

def UnipotentConjugateInLevel : Prop :=
  ∀ n ∈ X.NfinU u, n ∈ X.B.I.Kset →
    (X.xu u)⁻¹ * n * X.xu u ∈ X.K2 ∧ X.chi2 ((X.xu u)⁻¹ * n * X.xu u) = X.psiFinU u n

theorem kset_mul {a b : X.B.I.Gf} (ha : a ∈ X.B.I.Kset) (hb : b ∈ X.B.I.Kset) : a * b ∈ X.B.I.Kset := by
  simp only [AutInst.Kset, Set.mem_setOf_eq, Subgroup.coe_mul] at ha hb ⊢
  exact Subgroup.mul_mem _ ha hb

theorem kset_inv {a : X.B.I.Gf} (ha : a ∈ X.B.I.Kset) : a⁻¹ ∈ X.B.I.Kset := by
  simp only [AutInst.Kset, Set.mem_setOf_eq, Subgroup.coe_inv] at ha ⊢
  exact Subgroup.inv_mem _ ha

theorem levelDec_of (hK : X.LevelSubgroupCharacter) (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u) : LevelDec X u := by
  intro n hn h hnh
  have hnhK : n * (h : X.B.I.Gf) ∈ X.B.I.Kset := kset_of_conj X u _ hnh
  have hhK : (h : X.B.I.Gf) ∈ X.B.I.Kset := hS n hn h hnhK
  have hnK : n ∈ X.B.I.Kset := by
    have := kset_mul X hnhK (kset_inv X hhK)
    simpa using this
  obtain ⟨hn2, hchi⟩ := hN n hn hnK
  have e1 : (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u =
      ((X.xu u)⁻¹ * n * X.xu u)⁻¹ * ((X.xu u)⁻¹ * (n * (h : X.B.I.Gf)) * X.xu u) := by group
  have hh2 : (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u ∈ X.K2 := by
    rw [e1]
    exact hK.2.1 _ (hK.2.2.1 _ hn2) _ hnh
  refine ⟨hh2, ?_⟩
  have e2 : (X.xu u)⁻¹ * (n * (h : X.B.I.Gf)) * X.xu u =
      ((X.xu u)⁻¹ * n * X.xu u) * ((X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u) := by group
  rw [e2, hK.2.2.2.1 _ hn2 _ hh2, hchi]

theorem phWellDef_of_steps (hK : X.LevelSubgroupCharacter) (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u) : PhWellDef X u hK :=
  phWellDef_of X u hK nfinGroup_holds (nfinConj_holds X u) (levelDec_of X u hK hS hN)

end Level

section SpL

variable {R : Type} [CommRing R] {n r : ℕ} (e : Fin r → Fin n → R)

def SpL (m : ℕ) : Submodule R (Fin n → R) := Submodule.span R (e '' {b | b.1 < m})

theorem spL_mono {m m' : ℕ} (h : m ≤ m') : SpL e m ≤ SpL e m' := by
  unfold SpL
  exact Submodule.span_mono (by rintro _ ⟨b, hb, rfl⟩; exact ⟨b, by simp only [Set.mem_setOf_eq] at hb ⊢; omega, rfl⟩)

theorem spL_range : Submodule.span R (Set.range e) = SpL e r := by
  unfold SpL
  congr 1
  ext v
  simp

theorem spL_zero : SpL e 0 = ⊥ := by
  simp [SpL]

def C1 (M : Matrix (Fin n) (Fin n) R) : Prop := ∀ a : Fin r, (M - 1) *ᵥ e a ∈ SpL e a.1

variable {e}

theorem sub_one_mulVec_mem_SpL_pred_of_C1 {M : Matrix (Fin n) (Fin n) R} (hM : C1 e M) (m : ℕ) :
    ∀ y ∈ SpL e m, (M - 1) *ᵥ y ∈ SpL e (m - 1) := by
  intro y hy
  have key : SpL e m ≤ (SpL e (m - 1)).comap (M - 1).mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    simp only [Set.mem_setOf_eq] at hb
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    exact spL_mono e (show b.1 ≤ m - 1 by omega) (hM b)
  simpa only [Submodule.mem_comap, Matrix.mulVecLin_apply] using key hy

theorem mulVec_mem_SpL_of_C1 {M : Matrix (Fin n) (Fin n) R} (hM : C1 e M) (m : ℕ) : ∀ y ∈ SpL e m, M *ᵥ y ∈ SpL e m := by
  intro y hy
  have h1 : M *ᵥ y = (M - 1) *ᵥ y + y := by rw [sub_mulVec, one_mulVec, sub_add_cancel]
  rw [h1]
  exact add_mem (spL_mono e (Nat.sub_le m 1) (sub_one_mulVec_mem_SpL_pred_of_C1 hM m y hy)) hy

theorem mulVec_inverse_mem_SpL_of_C1 {M M' : Matrix (Fin n) (Fin n) R} (hM : C1 e M) (hMM : M' * M = 1) :
    ∀ m, ∀ y ∈ SpL e m, M' *ᵥ y ∈ SpL e m := by
  intro m
  induction m with
  | zero =>
    intro y hy
    rw [spL_zero, Submodule.mem_bot] at hy
    subst hy
    rw [mulVec_zero]
    exact zero_mem _
  | succ k ih =>
    intro y hy
    have h1 : M' *ᵥ y = y - M' *ᵥ ((M - 1) *ᵥ y) := by
      rw [mulVec_mulVec, Matrix.mul_sub, hMM, Matrix.mul_one, sub_mulVec, one_mulVec, sub_sub_cancel]
    rw [h1]
    exact sub_mem hy (spL_mono e (Nat.le_succ k) (ih _ (by simpa using sub_one_mulVec_mem_SpL_pred_of_C1 hM (k + 1) y hy)))

theorem mul_sub_one_mulVec' (M N : Matrix (Fin n) (Fin n) R) (y : Fin n → R) :
    (M * N - 1) *ᵥ y = M *ᵥ ((N - 1) *ᵥ y) + (M - 1) *ᵥ y := by
  simp only [sub_mulVec, mulVec_sub, mulVec_mulVec, one_mulVec, Matrix.mul_sub, Matrix.mul_one]
  abel

theorem inv_sub_one_mulVec' (M M' : Matrix (Fin n) (Fin n) R) (hMM : M' * M = 1) (y : Fin n → R) :
    (M' - 1) *ᵥ y = -(M' *ᵥ ((M - 1) *ᵥ y)) := by
  rw [mulVec_mulVec, Matrix.mul_sub, hMM, Matrix.mul_one, sub_mulVec, sub_mulVec, one_mulVec, neg_sub]

theorem C1_mul {M N : Matrix (Fin n) (Fin n) R} (hM : C1 e M) (hN : C1 e N) : C1 e (M * N) := by
  intro a
  rw [mul_sub_one_mulVec']
  exact add_mem (mulVec_mem_SpL_of_C1 hM a.1 _ (hN a)) (hM a)

theorem C1_of_left_inverse {M M' : Matrix (Fin n) (Fin n) R} (hM : C1 e M) (hMM : M' * M = 1) : C1 e M' := by
  intro a
  rw [inv_sub_one_mulVec' M M' hMM]
  exact neg_mem (mulVec_inverse_mem_SpL_of_C1 hM hMM a.1 _ (hM a))

theorem C1_one_matrix : C1 e (1 : Matrix (Fin n) (Fin n) R) := by
  intro a
  rw [sub_self, zero_mulVec]
  exact zero_mem _

theorem mul_sub_one_mulVec_mem_spL {M N : Matrix (Fin n) (Fin n) R} (hM : C1 e M) (z : Fin n → R)
    (hMz : (M - 1) *ᵥ z ∈ SpL e r) (hNz : (N - 1) *ᵥ z ∈ SpL e r) : (M * N - 1) *ᵥ z ∈ SpL e r := by
  rw [mul_sub_one_mulVec']
  exact add_mem (mulVec_mem_SpL_of_C1 hM r _ hNz) hMz

theorem inverse_sub_one_mulVec_mem_SpL_of_C1 {M M' : Matrix (Fin n) (Fin n) R} (hM : C1 e M) (hMM : M' * M = 1) (z : Fin n → R)
    (hMz : (M - 1) *ᵥ z ∈ SpL e r) : (M' - 1) *ᵥ z ∈ SpL e r := by
  rw [inv_sub_one_mulVec' M M' hMM]
  exact neg_mem (mulVec_inverse_mem_SpL_of_C1 hM hMM r _ hMz)

end SpL

section SGrp

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem uMat_mul {m : ℕ} {ε : Fin m → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := by
  simp [uMat]

theorem uMat_inv_mul {m : ℕ} {ε : Fin m → Bool} (a : Formalism.REAL.UJ ε) : uMat a⁻¹ * uMat a = 1 := by
  simp [uMat]

theorem sfin_iff (x : X.B.I.Gf) : x ∈ SfinU X u ↔
    C1 (fun b => incl X.B.I (X.eR b)) (X.B.I.fmat x) ∧
      (X.B.I.fmat x - 1) *ᵥ incl X.B.I (X.zR u) ∈ SpL (fun b => incl X.B.I (X.eR b)) D.R.rS := by
  rw [← spL_range]
  rfl

theorem sinf_iff (s : X.B.I.Ginf) : s ∈ X.SinfU u ↔ ∀ v,
    C1 (fun a => rv X.B.I v (X.eR a)) (uMat (s v)) ∧
      (uMat (s v) - 1) *ᵥ rv X.B.I v (X.zR u) ∈ SpL (fun a => rv X.B.I v (X.eR a)) D.R.rS := by rfl

def SSub : Subgroup X.B.I.GA where
  carrier := {y | y.1 ∈ X.SinfU u ∧ y.2 ∈ SfinU X u}
  one_mem' := by
    refine ⟨(sinf_iff X u 1).2 fun v => ?_, (sfin_iff X u 1).2 ?_⟩
    · have : uMat ((1 : X.B.I.Ginf) v) = 1 := by simp [uMat]
      rw [this]; exact ⟨C1_one_matrix, by simp⟩
    · have : X.B.I.fmat 1 = 1 := by simp [AutInst.fmat]
      rw [this]; exact ⟨C1_one_matrix, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨(sinf_iff X u _).2 fun v => ?_, (sfin_iff X u _).2 ?_⟩
    · obtain ⟨hc, hz⟩ := (sinf_iff X u _).1 ha1 v
      obtain ⟨hc', hz'⟩ := (sinf_iff X u _).1 hb1 v
      have e1 : uMat ((a * b).1 v) = uMat (a.1 v) * uMat (b.1 v) := by
        rw [Prod.fst_mul, Pi.mul_apply, uMat_mul]
      rw [e1]
      exact ⟨C1_mul hc hc', mul_sub_one_mulVec_mem_spL hc _ hz hz'⟩
    · obtain ⟨hc, hz⟩ := (sfin_iff X u _).1 ha2
      obtain ⟨hc', hz'⟩ := (sfin_iff X u _).1 hb2
      rw [Prod.snd_mul, fmat_mul]
      exact ⟨C1_mul hc hc', mul_sub_one_mulVec_mem_spL hc _ hz hz'⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨(sinf_iff X u _).2 fun v => ?_, (sfin_iff X u _).2 ?_⟩
    · obtain ⟨hc, hz⟩ := (sinf_iff X u _).1 ha1 v
      have e1 : uMat ((a⁻¹).1 v) = uMat ((a.1 v)⁻¹) := by rw [Prod.fst_inv, Pi.inv_apply]
      rw [e1]
      exact ⟨C1_of_left_inverse hc (uMat_inv_mul _), inverse_sub_one_mulVec_mem_SpL_of_C1 hc (uMat_inv_mul _) _ hz⟩
    · obtain ⟨hc, hz⟩ := (sfin_iff X u _).1 ha2
      rw [Prod.snd_inv]
      exact ⟨C1_of_left_inverse hc (fmat_inv_mul X _), inverse_sub_one_mulVec_mem_SpL_of_C1 hc (fmat_inv_mul X _) _ hz⟩

theorem sGroup_holds : SGroup X u := by
  show ((Subgroup.closure (SSub X u : Set X.B.I.GA) : Subgroup X.B.I.GA) : Set X.B.I.GA) = (SSub X u : Set X.B.I.GA)
  rw [Subgroup.closure_eq]

def SratComp : Prop := ∀ γ ∈ Srat X u, γ.1 ∈ X.SinfU u ∧ γ.2 ∈ SfinU X u

theorem sratComp_holds : SratComp X u := by
  intro γ hγ
  have hS : ((Subgroup.closure {y : X.B.I.GA | y.1 ∈ X.SinfU u ∧ y.2 ∈ SfinU X u} : Subgroup X.B.I.GA) :
      Set X.B.I.GA) = {y | y.1 ∈ X.SinfU u ∧ y.2 ∈ SfinU X u} := sGroup_holds X u
  have h3 : γ ∈ ((Subgroup.closure {y : X.B.I.GA | y.1 ∈ X.SinfU u ∧ y.2 ∈ SfinU X u} : Subgroup X.B.I.GA) :
      Set X.B.I.GA) := (Subgroup.mem_inf.1 hγ).2
  rw [hS] at h3
  exact h3

end SGrp

section LeftInv

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def RatLevi : Prop :=
  ∀ γ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, γ.1 ∈ X.SinfU u → γ.2 ∈ SfinU X u →
    ∃ ν η : X.B.I.GA, γ = ν * η ∧ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ∧ ν.1 ∈ X.NinfU u ∧
      ν.2 ∈ X.NfinU u ∧ η ∈ Gam X u

def PsiProd : Prop :=
  ∀ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u → ν.2 ∈ X.NfinU u →
    X.psiInfU u ν.1 * X.psiFinU u ν.2 = 1

theorem hinf_fix_nxt (η : X.B.I.Ginf) (hη : η ∈ Hinf X u) (v : InfinitePlace X.B.I.F) (a : Fin D.R.rS) :
    uMat (η v) *ᵥ nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a =
      nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a := by
  unfold Formalism.L2.SG.HidaSetting.nxt
  split_ifs
  · exact hη v _ (eR_mem_fix X u _)
  · exact hη v _ (zR_mem_fix X u)

theorem psiInf_mul_H (s η : X.B.I.Ginf) (hη : η ∈ Hinf X u) : X.psiInfU u (s * η) = X.psiInfU u s := by
  unfold HidaSetting.psiInfU psiInf psiR rootCoord
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Pi.mul_apply, uMat_mul, ← mulVec_mulVec, hinf_fix_nxt X u η hη v]

theorem phLeftInv_of (hK : X.LevelSubgroupCharacter) (hWD : PhWellDef X u hK) (hL : RatLevi X u) (hP : PsiProd X u) :
    PhLeftInv X u hK := by
  have hN := nfinGroup_holds (X := X) (u := u)
  have hCj := nfinConj_holds X u
  have hC := sratComp_holds X u
  have fwd : ∀ γ ∈ Srat X u, ∀ (y : X.B.I.GA) (n : X.B.I.Gf) (h : Hfin X u) (k : X.B.I.Gf),
      IsDec X u y.2 n h k → ∃ (n' : X.B.I.Gf) (h' : Hfin X u), IsDec X u (γ * y).2 n' h' k := by
    intro γ hγ y n h k hd
    obtain ⟨hγI, hγf⟩ := hC γ hγ
    obtain ⟨ν, η, hνη, -, -, hνf, hη⟩ := hL γ (Subgroup.mem_inf.1 hγ).1 hγI hγf
    set ηf : Hfin X u := iotaF X u ⟨η, hη⟩ with hηf
    have hηf' : (ηf : X.B.I.Gf) = η.2 := rfl
    refine ⟨ν.2 * ((ηf : X.B.I.Gf) * n * (ηf : X.B.I.Gf)⁻¹), ηf * h,
      (hN.1 _ hνf _ (hCj ηf n hd.1).1).1, hd.2.1, ?_⟩
    rw [hνη, Prod.snd_mul, Prod.snd_mul, hd.2.2, Subgroup.coe_mul, hηf']
    group
  intro T γ hγ y
  by_cases hex : ∃ n h k, IsDec X u y.2 n h k
  · obtain ⟨n, h, k, hd⟩ := hex
    obtain ⟨hγI, hγf⟩ := hC γ hγ
    obtain ⟨ν, η, hνη, hνF, hνI, hνf, hη⟩ := hL γ (Subgroup.mem_inf.1 hγ).1 hγI hγf
    subst hνη
    set ηG : Gam X u := ⟨η, hη⟩
    set ηf : Hfin X u := iotaF X u ηG with hηf
    set ηi : Hinf X u := iotaI X u ηG with hηi
    have hηf' : (ηf : X.B.I.Gf) = η.2 := rfl
    have hηi' : (ηi : X.B.I.Ginf) = η.1 := rfl
    have hn' : (ηf : X.B.I.Gf) * n * (ηf : X.B.I.Gf)⁻¹ ∈ X.NfinU u := (hCj ηf n hd.1).1
    have hd' : IsDec X u ((ν * η) * y).2 (ν.2 * ((ηf : X.B.I.Gf) * n * (ηf : X.B.I.Gf)⁻¹)) (ηf * h) k := by
      refine ⟨(hN.1 _ hνf _ hn').1, hd.2.1, ?_⟩
      rw [Prod.snd_mul, Prod.snd_mul, hd.2.2, Subgroup.coe_mul, hηf']
      group
    rw [ph_eq X u hK hWD T _ _ _ _ hd', ph_eq X u hK hWD T y n h k hd]
    unfold phVal
    have hψf : X.psiFinU u (ν.2 * ((ηf : X.B.I.Gf) * n * (ηf : X.B.I.Gf)⁻¹)) =
        X.psiFinU u ν.2 * X.psiFinU u n := by
      rw [(hN.1 _ hνf _ hn').2, (hCj ηf n hd.1).2]
    have hνIS : ν.1 ∈ X.SinfU u := fun v => (hνI v).1
    have hηIS : η.1 ∈ X.SinfU u := hinf_le_sinf X u η.1 ηi.2
    have hprodS : ν.1 * η.1 ∈ X.SinfU u := by
      have := hγI; rwa [Prod.fst_mul] at this
    have hW : X.Wu u ((ν * η) * y).1 = X.psiInfU u ν.1 • X.piU u η.1 (X.Wu u y.1) := by
      rw [Prod.fst_mul, Prod.fst_mul, (X.Wu_spec u).1 _ hprodS]
      change X.psiInfU u (ν.1 * η.1) • X.piU u (ν.1 * η.1) (X.Wu u y.1) = _
      rw [psiInf_mul_H X u ν.1 η.1 ηi.2, (X.piU_rep u).2.1 _ hνIS _ hηIS, (X.piU_rep u).2.2.2.1 _ hνI, one_mul]
    have hT1 : (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.piU u η.1 (X.Wu u y.1)) (1, ηf * h) =
        (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y.1) (1, h) := by
      have h1 := T.2.2 ηi (X.Wu u y.1) (1, ηf * h)
      have h2 := (T.2.1 (X.Wu u y.1)).1 ηG (1, h)
      have e1 : ((1 : Hinf X u), ηf * h) * (ηi, 1) = (iotaI X u ηG, iotaF X u ηG) * (1, h) := by
        simp [hηi, hηf]
      rw [e1, h2] at h1
      exact h1
    rw [hW, map_smul, Pi.smul_apply, smul_eq_mul, hT1, hψf]
    have hP' := hP ν hνF hνI hνf
    linear_combination (X.psiFinU u n * X.chi2 k *
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y.1) (1, h)) * hP'
  · have hnd : ¬ ∃ n h k, IsDec X u (γ * y).2 n h k := by
      rintro ⟨n', h', k', hd'⟩
      obtain ⟨n'', h'', hd''⟩ := fwd γ⁻¹ (inv_mem hγ) (γ * y) n' h' k' hd'
      rw [← mul_assoc, inv_mul_cancel, one_mul] at hd''
      exact hex ⟨n'', h'', k', hd''⟩
    rw [ph_eq_zero X u hK T _ hnd, ph_eq_zero X u hK T _ hex]

end LeftInv

section Reprod

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem ph_conv (hK : X.LevelSubgroupCharacter) (hWD : PhWellDef X u hK) (β : X.B.I.Ginf → ℂ)
    (hβ : ∀ x, Integrable (fun z => β z • X.Wu u (x * z)) (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
      ∫ z, β z • X.Wu u (x * z) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = X.Wu u x)
    (T : Cu X u hK) (y : X.B.I.GA) :
    ∫ z, β z * Ph X u hK T (y * (z, 1)) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = Ph X u hK T y := by
  have h2 : ∀ z : X.B.I.Ginf, (y * (z, 1)).2 = y.2 := fun z => by simp
  by_cases hex : ∃ n h k, IsDec X u y.2 n h k
  · obtain ⟨n, h, k, hd⟩ := hex
    set c := X.psiFinU u n * X.chi2 k
    have hfun : (fun z => β z * Ph X u hK T (y * (z, 1))) =
        fun z => c * evL X u hK T h (β z • X.Wu u (y.1 * z)) := by
      funext z
      have hd' : IsDec X u (y * (z, 1)).2 n h k := by rw [h2]; exact hd
      rw [ph_eq X u hK hWD T _ n h k hd', map_smul, evL_apply]
      unfold phVal
      simp only [Prod.fst_mul, smul_eq_mul, c]
      ring
    rw [hfun, integral_const_mul, (evL X u hK T h).integral_comp_comm (hβ y.1).1, (hβ y.1).2,
      ph_eq X u hK hWD T y n h k hd, evL_apply]
    rfl
  · have hz : ∀ z : X.B.I.Ginf, Ph X u hK T (y * (z, 1)) = 0 := fun z =>
      ph_eq_zero X u hK T _ (by rw [h2]; exact hex)
    simp only [hz, mul_zero, integral_zero, ph_eq_zero X u hK T y hex]

theorem exists_compact_nhds_level (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized) (hR : FoldReadyX X) :
    ∃ C : Set X.B.I.Gf, IsCompact C ∧ C ∈ nhds (1 : X.B.I.Gf) ∧ C ⊆ X.K2 ∧ MeasurableSet C ∧
      0 < X.B.μf C ∧ X.B.μf C < ⊤ := by
  have := hR.1
  have := hR.2.2.1
  haveI : T2Space X.B.I.Gf :=
    T2Space.of_injective_continuous (f := fun x : X.B.I.Gf => ((1 : X.B.I.Ginf), x))
      (fun a b h => (Prod.mk.inj h).2) (continuous_const.prodMk continuous_id)
  have := X.B.haar
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (1 : X.B.I.GA)
  have hK1 : K ∈ nhds ((1 : X.B.I.Ginf), (1 : X.B.I.Gf)) := hKn
  rw [mem_nhds_prod_iff] at hK1
  obtain ⟨U, hU, V, hV, hUV⟩ := hK1
  have hC'n : Prod.snd '' K ∈ nhds (1 : X.B.I.Gf) := by
    refine Filter.mem_of_superset hV fun v hv => ⟨((1 : X.B.I.Ginf), v), hUV ⟨mem_of_mem_nhds hU, hv⟩, rfl⟩
  have hC'c : IsCompact (Prod.snd '' K) := hKc.image continuous_snd
  have hKo := (level_subgroup_isClopen X hK hKL)
  refine ⟨Prod.snd '' K ∩ X.K2, hC'c.inter_right hKo.isClosed,
    Filter.inter_mem hC'n (hKo.isOpen.mem_nhds hK.1), Set.inter_subset_right,
    (hC'c.inter_right hKo.isClosed).isClosed.measurableSet, ?_, (hC'c.inter_right hKo.isClosed).measure_lt_top⟩
  exact X.B.μf.measure_pos_of_mem_nhds (Filter.inter_mem hC'n (hKo.isOpen.mem_nhds hK.1))

theorem phReprod_of (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized) (hWD : PhWellDef X u hK) (hM : PhMeas X u hK)
    (hR : FoldReadyX X) (hW : WuDecay.WuReprod X u) : PhReprod X u hK := by
  obtain ⟨α, Ωi, a, hΩc, hΩ1, hαm, hsupp, hbd, hrep⟩ := hW
  obtain ⟨C, hCc, hCn, hCK, hCm, hCpos, hCtop⟩ := exists_compact_nhds_level X hK hKL hR
  have := hR.2.2.2.1
  set c : ℝ≥0 := (X.B.μf C).toNNReal
  have hc : ((c : ℝ≥0∞)) = X.B.μf C := ENNReal.coe_toNNReal hCtop.ne
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, ENNReal.coe_zero] at hc; exact hCpos.ne' hc.symm
  refine ⟨Ωi ×ˢ C, a / c, hΩc.prod hCc, ⟨hΩ1, mem_of_mem_nhds hCn⟩, fun T y => ?_⟩

  have hreal : ‖Ph X u hK T y‖ₑ ≤ (a : ℝ≥0∞) *
      ∫⁻ z in Ωi, ‖Ph X u hK T (y * (z, 1))‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
    rw [← ph_conv X u hK hWD α hrep T y]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← setLIntegral_eq_of_support_subset (s := Ωi)]
    · rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      refine lintegral_mono fun z => ?_
      rw [enorm_mul]
      gcongr
      have h1 : ‖α z‖₊ ≤ a := by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hbd z
      rw [enorm_eq_nnnorm]; exact ENNReal.coe_le_coe.2 h1
    · intro z hz
      by_contra hzΩ
      apply hz
      have : α z = 0 := by
        by_contra h0; exact hzΩ (hsupp z h0)
      simp [this]

  have hmeas : Measurable fun ω : X.B.I.GA => ‖Ph X u hK T (y * ω)‖ₑ :=
    ((hM T).comp (continuous_const.mul continuous_id).measurable).enorm
  have hfin : ∫⁻ ω in Ωi ×ˢ C, ‖Ph X u hK T (y * ω)‖ₑ ∂(X.B.I.muA X.B.μf) =
      X.B.μf C * ∫⁻ z in Ωi, ‖Ph X u hK T (y * (z, 1))‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
    unfold AutInst.muA
    rw [← Measure.prod_restrict, lintegral_prod _ hmeas.aemeasurable, ← lintegral_const_mul' _ _ hCtop.ne]
    refine lintegral_congr fun z => ?_
    rw [setLIntegral_congr_fun hCm (g := fun _ => ‖Ph X u hK T (y * (z, 1))‖ₑ), setLIntegral_const, mul_comm]
    intro κ hκ
    have e1 : y * (z, κ) = y * (z, 1) * (1, κ) := by
      rw [mul_assoc]; congr 1; ext <;> simp
    simp only
    rw [e1, ph_right_K X u hK hWD T _ κ (hCK hκ), enorm_mul]
    have hn : ‖X.chi2 κ‖ₑ = 1 := by
      rw [enorm_eq_nnnorm]; simp [← NNReal.coe_eq_one, hK.2.2.2.2 κ (hCK hκ)]
    rw [hn, one_mul]
  rw [hfin]
  calc ‖Ph X u hK T y‖ₑ ≤ (a : ℝ≥0∞) * ∫⁻ z in Ωi, ‖Ph X u hK T (y * (z, 1))‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := hreal
    _ = ((a / c : ℝ≥0) : ℝ≥0∞) * (X.B.μf C *
          ∫⁻ z in Ωi, ‖Ph X u hK T (y * (z, 1))‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)) := by
      rw [← mul_assoc, ← hc, ← ENNReal.coe_mul, div_mul_cancel₀ _ hc0]

end Reprod

section Meas

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem level_character_eq_conj_idempotent (hKL : X.LevelSubgroupNormalized) (κ : X.B.I.Gf) (hκ : κ ∈ X.K2) :
    X.chi2 κ = star (X.B.e κ) * ((X.B.μf X.K2).toReal : ℂ) := by
  have hκ' : κ ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hκ
  have hvol : (X.B.μf X.K2).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKL.2.2.1.ne', hKL.2.2.2.ne⟩
  have hv : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by exact_mod_cast hvol
  rw [X.e_eq κ, if_pos hκ', star_div₀, star_star]
  have hs : star (((X.B.μf (K2set X.B.I X.B.g X.e0 X.z0 X.bw)).toReal : ℝ) : ℂ) =
      (((X.B.μf X.K2).toReal : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hs, div_mul_cancel₀ _ hv]
  rfl

theorem ph_continuous (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized) (hWD : PhWellDef X u hK) (T : Cu X u hK) :
    Continuous (Ph X u hK T) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hKo : IsOpen X.K2 := (level_subgroup_isClopen X hK hKL).isOpen
  set N : Set X.B.I.GA := {y' | y.2⁻¹ * y'.2 ∈ X.K2} with hNdef
  have hNo : IsOpen N := hKo.preimage (continuous_const.mul continuous_snd)
  have hyN : y ∈ N := by
    show y.2⁻¹ * y.2 ∈ X.K2
    rw [inv_mul_cancel]; exact hK.1
  have hsplit : ∀ y' : X.B.I.GA, y' = ((y'.1, y.2) : X.B.I.GA) * (1, y.2⁻¹ * y'.2) := fun y' => by
    ext <;> simp
  by_cases hex : ∃ n h k, IsDec X u y.2 n h k
  · obtain ⟨n, h, k, hd⟩ := hex
    set v : ℂ := ((X.B.μf X.K2).toReal : ℂ)
    let G : X.B.I.GA → ℂ := fun y' => (star (X.B.e (y.2⁻¹ * y'.2)) * v) *
      (X.psiFinU u n * X.chi2 k * evL X u hK T h (X.Wu u y'.1))
    have hG : Continuous G := by
      have he : Continuous X.B.e := (X.B.e_adm.1).continuous
      exact ((continuous_star.comp (he.comp (continuous_const.mul continuous_snd))).mul continuous_const).mul
        (continuous_const.mul ((evL X u hK T h).continuous.comp ((X.Wu_spec u).2.2.1.comp continuous_fst)))
    have heq : ∀ y' ∈ N, G y' = Ph X u hK T y' := by
      intro y' hy'
      have hy'' : y.2⁻¹ * y'.2 ∈ X.K2 := hy'
      rw [hsplit y', ph_right_K X u hK hWD T _ _ hy'', level_character_eq_conj_idempotent X hKL _ hy'']
      have hd' : IsDec X u ((y'.1, y.2) : X.B.I.GA).2 n h k := hd
      rw [ph_eq X u hK hWD T _ n h k hd']
      simp only [G, phVal, evL_apply]
      have e1 : (((y'.1, y.2) : X.B.I.GA) * (1, y.2⁻¹ * y'.2)).2 = y'.2 := by simp
      have e2 : (((y'.1, y.2) : X.B.I.GA) * (1, y.2⁻¹ * y'.2)).1 = y'.1 := by simp
      rw [e1, e2]
    exact hG.continuousAt.congr (Filter.eventuallyEq_of_mem (hNo.mem_nhds hyN) heq)
  · have h0 : ∀ y' ∈ N, (fun _ => (0 : ℂ)) y' = Ph X u hK T y' := by
      intro y' hy'
      have hy'' : y.2⁻¹ * y'.2 ∈ X.K2 := hy'
      refine (ph_eq_zero X u hK T _ ?_).symm
      rintro ⟨n, h, k, hn, hk, hy2⟩
      refine hex ⟨n, h, k * (y.2⁻¹ * y'.2)⁻¹, hn, hK.2.1 _ hk _ (hK.2.2.1 _ hy''), ?_⟩
      rw [show y.2 = y'.2 * (y.2⁻¹ * y'.2)⁻¹ by group, hy2]
      group
    exact continuousAt_const.congr (Filter.eventuallyEq_of_mem (hNo.mem_nhds hyN) h0)

theorem phMeas_of (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized) (hWD : PhWellDef X u hK) (hR : FoldReadyX X) :
    PhMeas X u hK := by
  have := hR.2.2.2.1
  exact fun T => (ph_continuous X u hK hKL hWD T).measurable

end Meas

section Final

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem phProps_of_steps (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized) (hR : FoldReadyX X) (hS : KsetSplit X u)
    (hN : UnipotentConjugateInLevel X u) (hL : RatLevi X u) (hP : PsiProd X u) : PhProps X u hK := by
  have hWD := phWellDef_of_steps X u hK hS hN
  exact phProps_of X u hK hWD (phMeas_of X u hK hKL hWD hR) (phLeftInv_of X u hK hWD hL hP) (wuRph_of_spec X u)

theorem foldOK_of_steps (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized) (hR : FoldReadyX X) (hS : KsetSplit X u)
    (hN : UnipotentConjugateInLevel X u) (hL : RatLevi X u) (hP : PsiProd X u) (hW : WuDecay.WuDecay X) (hF : SratFund X u)
    (hM : MultPoly X) (hU : IUnfold X u hK) : WuDecay.FoldOK X u hK := by
  have hWD := phWellDef_of_steps X u hK hS hN
  exact foldOK_of X u hK (phProps_of_steps X u hK hKL hR hS hN hL hP) (iFinite_of X u hK hF hM hW hWD hU)
    (phReprod_of X u hK hKL hWD (phMeas_of X u hK hKL hWD hR) hR (hW u).1)

theorem inHH_of_steps (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized) (hR : FoldReadyX X)
    (ha : @PoincareSeriesSquareIntegrable.PoincareSeriesFinite X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    (hb : @PoincareSeriesSquareIntegrable.PoincareSeriesMemLp X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u) (hL : RatLevi X u) (hP : PsiProd X u) (hW : WuDecay.WuDecay X)
    (hF : SratFund X u) (hM : MultPoly X) (hU : IUnfold X u hK) (hFB : FundBridge X) (hPM : PserMeas X u hK)
    (hRph : PserRph X u hK) (hPI : PhInt X) (hRF : ArchimedeanConvolutionFixesInvariantL2 X) (hEF : IdempotentFixesInvariantL2 X) : InHH X u hK :=
  inHH_of X u hK hR ha hb hFB (foldOK_of_steps X u hK hKL hR hS hN hL hP hW hF hM hU)
    (phProps_of_steps X u hK hKL hR hS hN hL hP) (phWellDef_of_steps X u hK hS hN) hPM hRph hPI hRF hEF hKL
    (level_subgroup_measurable X hK hKL)

end Final

section Cols

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def BaseLevelSetClosed : Prop := ∀ h ∈ K0 X u, h ∈ HaarTransversal X u

def GamFinOrd : Prop :=
  ∀ (r : Hfin X u) (γ : Gam X u),
    (∀ y ∈ frameOrthogonalLattice X u, X.B.I.fmat ((r : X.B.I.Gf)⁻¹ * (iotaF X u γ : X.B.I.Gf) * r) *ᵥ y ∈ frameOrthogonalLattice X u) →
      IsOfFinOrder γ

def GamUnip : Prop :=
  ∀ (r : Hfin X u) (γ : Gam X u), (r⁻¹ * iotaF X u γ * r) ∈ HaarTransversal X u → IsOfFinOrder γ → γ = 1

def ClassFin (hK : X.LevelSubgroupCharacter) : Prop := Finite (Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK))

theorem stabTriv_of (hC : BaseLevelSetClosed X u) (hF : GamFinOrd X u) (hU : GamUnip X u) :
    Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (K0 X u) := by
  intro r γ hγ
  have hs := hC _ hγ
  refine hU r γ hs (hF r γ fun y hy => ?_)
  have := (hs.1 y hy).1
  simpa using this

theorem colsLink_of (hK : X.LevelSubgroupCharacter) (hC : BaseLevelSetClosed X u) (hF : GamFinOrd X u) (hU : GamUnip X u)
    (hCF : ClassFin X u hK) : ColsLink X u hK :=
  ⟨Ku_le_K0 X u hK, stabTriv_of X u hC hF hU, hCF⟩

end Cols

section ClassIn

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem one_le_g : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

def WuDefinite : Prop :=
  ∀ ι : X.B.I.F →+* ℝ,
    (∀ x : Fin X.B.I.n → X.B.I.E, x ≠ 0 → (∀ s ∈ fixSet X u, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J s x = 0) →
      ∃ a : X.B.I.F, algebraMap X.B.I.F X.B.I.E a = Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x x ∧ 0 < ι a) ∨
    (∀ x : Fin X.B.I.n → X.B.I.E, x ≠ 0 → (∀ s ∈ fixSet X u, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J s x = 0) →
      ∃ a : X.B.I.F, algebraMap X.B.I.F X.B.I.E a = Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x x ∧ ι a < 0)

end ClassIn

end Formalism.L2.SG.PoincareInHH.Cut
