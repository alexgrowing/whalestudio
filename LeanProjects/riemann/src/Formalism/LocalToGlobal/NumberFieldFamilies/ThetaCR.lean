import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCX
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.DIV.Inh

section Cover

variable (p q : ℕ)

def covHom : covSub p q →* UpqT p q where
  toFun x := (⟨x.1.1, x.2.1⟩ : Formalism.UG.Upq p q)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem norm_sq_one (x : covSub p q) : ‖((x.1.2 : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := x.2.2
  have h2 := congrArg Matrix.det ((mem_Upq_iff p q _).1 x.2.1)
  have hJ : (Jm p q).det ≠ 0 := fun h => by
    have := congrArg Matrix.det (Jm_sq p q)
    rw [Matrix.det_mul, h, Matrix.det_one, zero_mul] at this
    exact zero_ne_one this
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_right_comm, mul_eq_right₀ hJ] at h2
  have h3 := congrArg norm h2
  rw [norm_mul, norm_star, ← h1, norm_pow, norm_one, ← pow_add] at h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h3

theorem cov_haar (ν : Measure (UpqT p q)) (hν : ν.IsHaarMeasure) : ∃ c : NNReal, 0 < c ∧
    Measure.map (stdGrp p q).covU (c • (stdGrp p q).haar) = ν := by
  have i1 : BorelSpace (UpqT p q) := ⟨rfl⟩
  have i2 : IsTopologicalGroup (UpqT p q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq p q))
  have hcl : IsClosed (Formalism.UG.Upq p q : Set (GL (Ix p q) ℂ)) := by
    have hv : Continuous fun x : GL (Ix p q) ℂ => (x : Mat p q) := Units.continuous_val
    exact isClosed_eq ((hv.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hv) continuous_const
  have i3 : LocallyCompactSpace (UpqT p q) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have i5 : SecondCountableTopology (Mat p q) := inferInstanceAs (SecondCountableTopology (Ix p q → Ix p q → ℂ))
  have i7 : SecondCountableTopology (Mat p q)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  have i6 : SecondCountableTopology (GL (Ix p q) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  have i4 : SecondCountableTopology (UpqT p q) := (Topology.IsEmbedding.subtypeVal (p := fun g : GL (Ix p q) ℂ => g ∈ Formalism.UG.Upq p q)).secondCountableTopology
  let f : (stdGrp p q).G →* UpqT p q := covHom p q
  have fc : Continuous f := Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _
  have fs : Function.Surjective f := by
    intro g
    let g' : Formalism.UG.Upq p q := g
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self ((g'.1 : Mat p q).det)
    have h0 : z ≠ 0 := fun h => (Matrix.isUnits_det_units g'.1).ne_zero (by rw [hz, h, zero_mul])
    exact ⟨(⟨(g'.1, Units.mk0 z h0), g'.2, by rw [hz, sq]; rfl⟩ : covSub p q), rfl⟩
  have fp : Filter.Tendsto f (Filter.cocompact _) (Filter.cocompact _) := by
    refine Filter.hasBasis_cocompact.tendsto_right_iff.2 fun K hK => ?_
    have hS : IsCompact (Set.range Circle.toUnits) := isCompact_range AdBC.toUnits_cont
    have hK' : IsCompact ((fun g : Formalism.UG.Upq p q => g.1) '' K) := hK.image continuous_subtype_val
    have hc := (covSub_closed p q).isClosedEmbedding_subtypeVal.isCompact_preimage (hK'.prod hS)
    refine Filter.mem_of_superset hc.compl_mem_cocompact fun x hx hx' => hx ⟨⟨f x, hx', rfl⟩, ?_⟩
    exact ⟨⟨_, mem_sphere_zero_iff_norm.2 (norm_sq_one p q x)⟩, Units.ext rfl⟩
  have hm := Measure.isHaarMeasure_map (stdGrp p q).haar f fc fs fp
  refine ⟨Measure.haarScalarFactor ν (Measure.map f (stdGrp p q).haar),
    Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩
  have e := Measure.isMulLeftInvariant_eq_smul ν (Measure.map f (stdGrp p q).haar)
  conv_rhs => rw [e]
  exact Measure.map_smul _ _ _

def grpCd (cd : CDHaar) : GrpData p q :=
  { stdGrp p q with
    haar := (cov_haar p q (cd.cd p q) (cd.haar p q)).choose • (stdGrp p q).haar
    isHaar := Measure.IsHaarMeasure.nnreal_smul _ (cov_haar p q (cd.cd p q) (cd.haar p q)).choose_spec.1.ne' }

end Cover

def DSPar (cd : CDHaar) : Prop :=
  ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep (grpCd p q cd), HasParam R lam

theorem param_ex (p q : ℕ) : ∃ lam : Ix p q → ℚ, IsParam lam := by
  refine ⟨fun a => -((finSumFinEquiv a : Fin (p + q)) : ℕ), fun a b h => ?_, fun a b h => ?_,
    fun a => ⟨-(2 * ((finSumFinEquiv a : Fin (p + q)) : ℕ)), by push_cast; ring⟩,
    fun a b => ⟨-((finSumFinEquiv a : Fin (p + q)) : ℕ) + ((finSumFinEquiv b : Fin (p + q)) : ℕ), by push_cast; ring⟩⟩
  · apply finSumFinEquiv.injective
    apply Fin.ext
    exact_mod_cast neg_injective h
  · rcases a with a | a <;> rcases b with b | b <;> simp only [posC] at h <;> simp <;> exact h

open Classical in

def provC (cd : CDHaar) (hF : FockExists) (hD : DSPar cd) : ProvA where
  grp := fun p q => grpCd p q cd
  fock := fun p q r s =>
    let C := (hF p q r s).some
    { H := C.H, Om := C.Om, isom := C.isom, cont := C.cont, ι := C.ι, ι_inj := C.ι_inj, dense := C.dense,
      fockIP := C.fockIP, der := C.der, emb := embStd p q r s, emb_cov := fun _ _ => rfl, emb_sq := fun _ _ => rfl }
  ds := fun p q lam => if h : IsParam lam then (hD p q lam h).choose else (hD p q _ (param_ex p q).choose_spec).choose

variable {D : D7}

theorem gram_coord (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.repr x i) * V.gram i j * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
    RingHom.id_apply, HSpace.gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

def colM (V : HSp D) {n : ℕ} (v : Fin n → V.V) : Matrix (Fin V.rank) (Fin n) D.host.E := fun i k => V.frame.repr (v k) i

theorem colM_gram (V : HSp D) {n m : ℕ} (v : Fin n → V.V) (w : Fin m → V.V) (a : Fin n) (b : Fin m) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (colM V v) * V.gram * colM V w) a b = V.hT (v a) (w b) := by
  rw [gram_coord, Matrix.mul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  rfl

theorem colM_vec (V : HSp D) {n : ℕ} (v : Fin n → V.V) (z : V.V) (a : Fin n) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (colM V v) * V.gram).mulVec (V.frame.repr z) a = V.hT (v a) z :=
  (colM_gram V v (fun _ : Fin 1 => z) a 0)

theorem frameMat_eq (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : frameMat A B ι = colM A fun k => ι (B.frame k) := by
  ext i k
  rw [frameMat, LinearMap.toMatrix_apply]
  rfl

theorem frame_rel {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : HSpace.IsIsomEmb B A ι) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram * frameMat A B ι = B.gram := by
  ext a b
  rw [frameMat_eq, colM_gram, h]
  rfl

def besselFlagHyperbolic (D : D7) (c : Fin D.R.rS → D.host.E) (hc : ∀ i, c i ≠ 0) (y : GfC (D.sp.Y 0)) :
    BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) where
  ρ := D.R.rS
  codim := by
    rw [D.sp.X_rank 0 (Nat.zero_le _), D.sp.Y_rank 0 (Nat.zero_le _)]
    have := D.R.rS_two
    show D.R.k + 0 * (D.R.t + 1) + 2 * D.R.rS + 1 = D.R.k + D.R.m - 1 + 0 * D.R.t
    omega
  e := colM (D.sp.Y 0) D.sp.hypE
  e_iso := ⟨by
    have h1 : LinearIndependent D.host.E D.sp.hypE := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have e := congrArg (fun x => (D.sp.Y 0).hT (D.sp.hypF i) x) hg
      have hfe : ∀ k, (D.sp.Y 0).hT (D.sp.hypF i) (D.sp.hypE k) = if k = i then 1 else 0 := fun k => by
        rw [← (D.sp.Y 0).herm.eq, D.sp.hyp_ef]
        split_ifs <;> simp
      simpa [map_sum, hfe] using e
    exact h1.map' (D.sp.Y 0).frame.equivFun.toLinearMap (LinearEquiv.ker _),
    by ext a b; rw [colM_gram, D.sp.hyp_ee]; rfl⟩
  e_perp := by ext a b; rw [frameMat_eq, colM_gram, (D.sp.hyp_orthX b _).1]; rfl
  z := (D.sp.Y 0).frame.repr D.sp.zm
  z_perpA := by funext a; rw [frameMat_eq, colM_vec, D.sp.zm_orth]; rfl
  z_perpE := by
    funext a
    rw [colM_vec, ← (D.sp.Y 0).herm.eq, (D.sp.hyp_orthz a).1]
    simp
  z_ne := by
    have e : Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.Y 0).gram ((D.sp.Y 0).frame.repr D.sp.zm)
      ((D.sp.Y 0).frame.repr D.sp.zm) = (D.sp.Y 0).hT D.sp.zm D.sp.zm := (gram_coord _ _ _).symm
    rw [e, D.sp.zm_norm, neg_ne_zero]
    exact Nat.cast_ne_zero.2 D.sp.T_prime.ne_zero
  c := c
  c_ne := hc
  y := y

theorem bessel_flag_dual : IsDualFlag (besselFlagHyperbolic D (fun _ => 1) (fun _ => one_ne_zero) 1) (colM (D.sp.Y 0) D.sp.hypF) := by
  have hfe : ∀ i k, (D.sp.Y 0).hT (D.sp.hypF i) (D.sp.hypE k) = if k = i then 1 else 0 := fun i k => by
    rw [← (D.sp.Y 0).herm.eq, D.sp.hyp_ef]
    split_ifs <;> simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have h1 : LinearIndependent D.host.E D.sp.hypF := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have e := congrArg (fun x => (D.sp.Y 0).hT (D.sp.hypE i) x) hg
      simpa [map_sum, D.sp.hyp_ef] using e
    exact h1.map' (D.sp.Y 0).frame.equivFun.toLinearMap (LinearEquiv.ker _)
  · refine Matrix.ext fun a b => (colM_gram (D.sp.Y 0) D.sp.hypF D.sp.hypF a b).trans ?_
    exact D.sp.hyp_ff a b
  · refine Matrix.ext fun a b => (colM_gram (D.sp.Y 0) D.sp.hypE D.sp.hypF a b).trans ?_
    by_cases h : a = b
    · subst h; rw [Matrix.one_apply_eq]; exact (D.sp.hyp_ef a a).trans (if_pos rfl)
    · rw [Matrix.one_apply_ne h]; exact (D.sp.hyp_ef a b).trans (if_neg h)
  · refine Matrix.ext fun a b => ?_
    rw [frameMat_eq]
    refine (colM_gram (D.sp.Y 0) (fun k => D.sp.iXY 0 ((D.sp.X 0).frame k)) D.sp.hypF a b).trans ?_
    rw [(D.sp.hyp_orthX b _).2]; rfl
  · funext a
    refine (colM_vec (D.sp.Y 0) D.sp.hypF D.sp.zm a).trans ?_
    rw [← (D.sp.Y 0).herm.eq, (D.sp.hyp_orthz a).2]; simp

variable {ψ : AddChar (AF D.host.F) ℂ}

def freeOf (Om : WeilC ψ) (petF : HSp D → ℝ) (hp : ∀ V, 0 < petF V)
    (rowAF : ∀ (μ : D.what₂.Tup) (j : ℕ), D.what₂.Mult μ j →ₗ[ℂ] cuspC D (D.sp.Y j))
    (PhiY : ∀ (_μ : D.what₂.Tup) (j : ℕ), schC ψ (D.sp.Y (j + 1)) (D.sp.Y j))
    (mY : D.what₂.Tup → ℕ → ℝ) (h1 : ∀ μ j, 0 < mY μ j) (h2 : ∀ j, mY D.what₂.mu0 j = 1) (h3 : ∀ μ, mY μ 0 = 1) : Free Om where
  petF := petF
  petF_pos := hp
  fact := fun _ _ => Set.univ
  conjS := fun V W => (conj_ex (kfinC ψ V W)).choose
  conjS_add := fun V W => (conj_ex (kfinC ψ V W)).choose_spec.1
  conjS_smul := fun V W => (conj_ex (kfinC ψ V W)).choose_spec.2.1
  conjS_conjS := fun V W => (conj_ex (kfinC ψ V W)).choose_spec.2.2.1
  conjS_fact := fun _ _ _ _ => Set.mem_univ _
  conjS_kfin := fun V W => (conj_ex (kfinC ψ V W)).choose_spec.2.2.2
  PosE := fun _ _ _ => PUnit
  FJd := fun _ _ _ => PUnit
  BE := fun _ _ _ _ _ _ _ => 0
  BE_right := fun _ _ _ _ _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  BE_add := fun _ _ _ _ _ _ _ _ => by simp
  BE_smul := fun _ _ _ _ _ _ _ _ => by simp
  pos1 := fun _ => ⟨besselFlagHyperbolic D (fun _ => 1) (fun _ => one_ne_zero) 1, rfl⟩
  posSym := fun _ => ⟨besselFlagHyperbolic D (fun _ => 1) (fun _ => one_ne_zero) 1, rfl⟩
  f1 := fun _ => colM (D.sp.Y 0) D.sp.hypF
  free_flag_dual := fun _ => bessel_flag_dual
  colAF := fun _ _ _ => 0
  PhiX := fun _ _ _ => 0
  rowAF := rowAF
  PhiY := PhiY
  PhiYLow := fun _ _ _ => 0
  PhiYupLow := fun _ _ _ => 0
  mY := mY
  mY_pos := h1
  adelicDataRowMeasureScale_trivialTuple := h2
  mY_zero := h3

section Emb

variable {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V}

def prM (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : Matrix (Fin B.rank) (Fin A.rank) D.host.E :=
  B.gram⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram)

theorem perp_rel (h : HSpace.IsIsomEmb B A ι) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram * (1 - frameMat A B ι * prM A B ι) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, frame_rel h, prM, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (gram_det_ne B).isUnit, Matrix.one_mul, sub_self]

theorem emb_gen {E R : Type} [CommRing E] [CommRing R] {a b : ℕ} (f : E →+* R) (M : Matrix (Fin a) (Fin b) E)
    (P : Matrix (Fin b) (Fin a) E) (Q : Matrix (Fin a) (Fin a) E) (hQ : M * P + Q = 1) (g : Matrix (Fin a) (Fin a) R)
    (x : Matrix (Fin b) (Fin b) R) (e1 : g * M.map f = M.map f * x)
    (e2 : ∀ j, g.mulVec (fun i => f (Q i j)) = fun i => f (Q i j)) : g = M.map f * x * P.map f + Q.map f := by
  have e2' : g * Q.map f = Q.map f := by
    ext i j
    exact congrFun (e2 j) i
  have e3 : M.map f * P.map f + Q.map f = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_add _ f.map_add, hQ, Matrix.map_one _ f.map_zero f.map_one]
  rw [← e1, ← e2', Matrix.mul_assoc, ← Matrix.mul_add, e3, Matrix.mul_one]

def coM (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : Matrix (Fin A.rank) (Fin A.rank) D.host.E :=
  1 - frameMat A B ι * prM A B ι

theorem embU (D : D7) : EmbU D := by
  intro A B ι h g g' x a b
  have hQ : frameMat A B ι * prM A B ι + coM A B ι = 1 := add_sub_cancel _ _
  have hp : ∀ j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram).mulVec
      (fun k => coM A B ι k j) = 0 := fun j => funext fun i => congrFun (congrFun (perp_rel h) i) j
  exact Subtype.ext (Units.ext ((emb_gen (incA D) _ _ _ hQ (mt A g) (mt B x) a.1 fun j => a.2 _ (hp j)).trans
    (emb_gen (incA D) _ _ _ hQ (mt A g') (mt B x) b.1 fun j => b.2 _ (hp j)).symm))

end Emb

section Rows

variable (X : ThetaX D)

def ioOf (μ : D.what₂.Tup) (j : ℕ) (y : D.what₂.Mult μ (j + 1)) : D.what₂.Mult μ j :=
  haveI : CompleteSpace (D.what₂.Mult μ j) := FiniteDimensional.complete ℂ _
  (InnerProductSpace.toDual ℂ (D.what₂.Mult μ j)).symm (LinearMap.toContinuousLinearMap
    ((X.mY μ j : ℂ) • ((X.pet_right _ (X.dnY μ j (X.rowAF μ (j + 1) y))).mk' _) ∘ₗ X.rowAF μ j))

end Rows

end Formalism.L2.Fam.ThC

end
