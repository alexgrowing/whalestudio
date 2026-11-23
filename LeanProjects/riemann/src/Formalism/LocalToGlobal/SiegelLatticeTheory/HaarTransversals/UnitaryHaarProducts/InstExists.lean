import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.LocalToGlobal.UnitaryNorms.RealPl
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas
open scoped Matrix

namespace Formalism.L2.SG.InstExistsPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev Jv : Matrix (Fin (VS D).rank) (Fin (VS D).rank) D.host.E := (VS D).gram

abbrev crdE : (Fin (VS D).rank → D.host.E) ≃ₗ[D.host.E] (VS D).V := (VS D).frame.equivFun.symm

def Lv : Submodule (𝓞 D.host.E) (Fin (VS D).rank → D.host.E) :=
  (VS D).L0.comap ((crdE D).toLinearMap.restrictScalars (𝓞 D.host.E))

theorem mem_Lv (x : Fin (VS D).rank → D.host.E) :
    x ∈ Lv D ↔ (∑ i, x i • (VS D).frame i) ∈ (VS D).L0 := by
  simp only [Lv, Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, crdE,
    Module.Basis.equivFun_symm_apply]

theorem hform_eq (x y : Fin (VS D).rank → D.host.E) :
    Formalism.UG.hform (starRingEnd D.host.E) (Jv D) x y =
      (VS D).hT (∑ i, x i • (VS D).frame i) (∑ j, y j • (VS D).frame j) := by
  unfold Formalism.UG.hform Jv
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    Finset.mul_sum, RingHom.id_apply]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (VS D).gram i j = (VS D).hT ((VS D).frame i) ((VS D).frame j) from rfl]
  ring

end Formalism.L2.SG.InstExistsPf

namespace Formalism.L2.SG.InstExistsPf

variable (D : D7)

theorem J_herm : Formalism.UG.IsHerm (starRingEnd D.host.E) (Jv D) := by
  unfold Formalism.UG.IsHerm Formalism.UG.cT
  ext i j
  exact (VS D).herm.eq ((VS D).frame j) ((VS D).frame i)

theorem J_det : (Jv D).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  have hrow : ∀ i, ∑ j, Jv D i j * v j = 0 := fun i => by
    have := congrFun hJv i
    simpa [Matrix.mulVec, dotProduct] using this
  have hy : ∀ x, (VS D).hT x (∑ j, v j • (VS D).frame j) = 0 := by
    intro x
    rw [← (VS D).frame.sum_repr x, ← hform_eq D (⇑((VS D).frame.repr x)) v]
    unfold Formalism.UG.hform
    simp only [mul_assoc, ← Finset.mul_sum, hrow, mul_zero, Finset.sum_const_zero]
  have h0 := (VS D).nondeg.2 _ hy
  funext i
  exact Fintype.linearIndependent_iff.mp (VS D).frame.linearIndependent v h0 i

theorem Lv_eq_map : Lv D = (VS D).L0.map ((crdE D).symm.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
  ext x
  simp only [Lv, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · intro h
    exact ⟨_, h, (crdE D).symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [LinearEquiv.apply_symm_apply]

theorem L_fg : (Lv D).FG := by
  rw [Lv_eq_map]
  exact Submodule.FG.map _ (VS D).standardTuple_isLattice.fg

theorem L_span : Submodule.span D.host.E ((Lv D : Set (Fin (VS D).rank → D.host.E))) = ⊤ := by
  rw [Lv_eq_map, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image,
    (VS D).standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem L_dual (x : Fin (VS D).rank → D.host.E) : x ∈ Lv D ↔
    ∀ y ∈ Lv D, Formalism.UG.hform (starRingEnd D.host.E) (Jv D) y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hU := (VS D).baseLattice_isUnimodular
  unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at hU
  rw [mem_Lv]
  conv_lhs => rw [← hU]
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Submodule.mem_one, RingHom.mem_range]
  constructor
  · intro h y hy
    rw [mem_Lv] at hy
    rw [hform_eq]
    obtain ⟨a, ha⟩ := h _ hy
    exact ⟨a, ha⟩
  · intro h w hw
    have hw' : (⇑((VS D).frame.repr w)) ∈ Lv D := by
      rw [mem_Lv, (VS D).frame.sum_repr]
      exact hw
    obtain ⟨a, ha⟩ := h _ hw'
    rw [hform_eq, (VS D).frame.sum_repr] at ha
    exact ⟨a, ha⟩

end Formalism.L2.SG.InstExistsPf

namespace Formalism.L2.SG.InstExistsPf

variable (D : D7)

theorem rank_eq : (VS D).rank = D.R.r := by
  unfold VS
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Ranks.rankY]

def epsV : Fin (VS D).rank → Bool := fun i => epsS D.R (Fin.cast (rank_eq D) i)

private theorem card_range_filter_lt_or_even_eq (a b : ℕ) :
    ∑ n ∈ Finset.range (a + 2 * b),
      (if (if n < a then true else decide ((n - a) % 2 = 0)) = true then 1 else 0 : ℕ) = a + b := by
  induction b with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℕ)) (fun n hn => by simp [Finset.mem_range.mp hn])]
    simp
  | succ b ih =>
    rw [show a + 2 * (b + 1) = a + 2 * b + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    split_ifs <;> simp_all <;> omega

theorem card_epsV : (Finset.univ.filter fun i => epsV D i = true).card = D.R.k + D.R.rS := by
  unfold epsV epsS
  rw [Finset.card_filter]
  simp only [Fin.coe_cast]
  rw [Fin.sum_univ_eq_sum_range
    (fun n => if (if n < D.R.k - 1 then true else decide ((n - (D.R.k - 1)) % 2 = 0)) = true then 1 else 0)
    (VS D).rank]
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  obtain ⟨j, hj⟩ := D.R.m_even
  have hr0 := rank_eq D
  unfold Ranks.r at hr0
  have hr : (VS D).rank = (D.R.k - 1) + 2 * (D.R.m / 2) := by omega
  rw [hr, card_range_filter_lt_or_even_eq]
  unfold Ranks.rS
  omega

theorem card_not_epsV : Fintype.card {i // ¬ epsV D i = true} = D.R.rS + 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype, card_epsV, Fintype.card_fin]
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  obtain ⟨j, hj⟩ := D.R.m_even
  have hr0 := rank_eq D
  unfold Ranks.r at hr0
  unfold Ranks.rS
  omega

def eSgn : Fin (VS D).rank ≃ Fin (D.R.k + D.R.rS) ⊕ Fin (D.R.rS + 1) :=
  (Equiv.sumCompl (fun i => epsV D i = true)).symm.trans
    (Equiv.sumCongr
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype, card_epsV]))
      (Fintype.equivFinOfCardEq (card_not_epsV D)))

theorem eSgn_isLeft (i : Fin (VS D).rank) : (eSgn D i).isLeft = epsV D i := by
  by_cases h : epsV D i = true
  · rw [h]
    simp [eSgn, h]
  · simp only [Bool.not_eq_true] at h
    rw [h]
    simp [eSgn, h]

theorem cT_eq {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT]

theorem Jpq_sub (p q : ℕ) {n : Type} [DecidableEq n] (e : n ≃ Fin p ⊕ Fin q) (ε : n → Bool) (he : ∀ i, (e i).isLeft = ε i) :
    (Formalism.UG.Jpq p q).submatrix e e = Matrix.diagonal fun a => if ε a then (1 : ℂ) else -1 := by
  ext a b
  simp only [Matrix.submatrix_apply, Formalism.UG.Jpq, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    have ha := he a
    rcases hea : e a with x | x <;> simp_all [Matrix.one_apply]
  · rw [if_neg hab]
    have hne : e a ≠ e b := fun h => hab (e.injective h)
    rcases hea : e a with x | x <;> rcases heb : e b with y | y <;> simp_all [Matrix.one_apply]

theorem exists_P (τ : D.what₂.Tau) : ∃ P : Matrix (Fin (VS D).rank) (Fin (VS D).rank) ℂ, IsUnit P ∧
    Pᴴ * (Jv D).map (embS D τ) * P = Formalism.REAL.Jm (epsV D) := by
  have hs : Formalism.UG.HasSignature ((VS D).gram.map (embS D τ)) (D.R.k + D.R.rS) (D.R.rS + 1) := by
    have h0 := D.sp.Y_sig 0 (embS D τ)
    rw [D.sp.baseSpace_signature_eq] at h0
    exact h0
  obtain ⟨e, P, hP⟩ := hs
  rw [cT_eq] at hP
  refine ⟨P.val.submatrix e (eSgn D), ?_, ?_⟩
  · have h1 : P.val.submatrix e (eSgn D) * (P⁻¹).val.submatrix (eSgn D) e = 1 := by
      rw [Matrix.submatrix_mul_equiv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.submatrix_one_equiv]
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h1)
  · rw [show (Jv D).map (embS D τ) = (VS D).gram.map (embS D τ) from rfl]
    have hGe : (VS D).gram.map (embS D τ) =
        (Matrix.reindex e e ((VS D).gram.map (embS D τ))).submatrix e e := by
      simp [Matrix.reindex_apply, Matrix.submatrix_submatrix]
    rw [hGe, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hP]
    exact Jpq_sub _ _ (eSgn D) (epsV D) (eSgn_isLeft D)

end Formalism.L2.SG.InstExistsPf

namespace Formalism.L2.SG.InstExistsPf

variable (D : D7)

theorem embS_over (τ : D.what₂.Tau) (a : D.host.F) :
    embS D τ (algebraMap D.host.F D.host.E a) = (Formalism.L2.Host.tauPl D τ).embedding a := by
  unfold embS
  change _ = (Formalism.L2.Host.realPl D.host (D.eTau τ)).embedding a
  unfold Formalism.L2.Host.realPl
  rw [InfinitePlace.embedding_mk_eq_of_isReal]
  · rfl
  · rw [← InfinitePlace.isReal_mk_iff]
    exact NumberField.IsTotallyReal.isReal _

def instOf : AutInst :=
  let hT := Formalism.MainNotions.S.Inh.aut_HTop_holds D.sp.cm (Jv D) (Lv D) (L_fg D) (L_span D)
  { F := D.host.F, E := D.host.E, cm := D.sp.cm, n := (VS D).rank, J := Jv D
    J_herm := J_herm D
    J_det := J_det D
    L := Lv D
    L_span := L_span D
    L_fg := L_fg D
    L_dual := L_dual D
    ε := fun _ => epsV D
    φ := fun v => embS D ((Formalism.L2.Host.tauPl D).symm v)
    φ_over := fun v a => by
      rw [embS_over, Equiv.apply_symm_apply]
    P := fun v => (exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose
    P_unit := fun v => (exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose_spec.1
    P_spec := fun v => (exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose_spec.2
    topf := hT.choose
    topf_group := hT.choose_spec.1
    topf_open := hT.choose_spec.2.1
    topf_basis := hT.choose_spec.2.2 }

def instanceOfRecord : UnitaryGroupInstance D where
  I := instOf D
  ιE := RingEquiv.refl _
  ιE_conj := fun x => Formalism.MainNotions.S.Inh.tie_star D x
  ιE_F := fun y => ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  bas := (VS D).frame
  J_eq := fun _ _ => rfl
  L_eq := fun x => mem_Lv D x
  pl := (Formalism.L2.Host.tauPl D).symm
  φ_eq := fun _ _ => rfl
  n_eq := rank_eq D
  eps_eq := fun _ _ => rfl

theorem instExists : InstExists D := ⟨instanceOfRecord D⟩

end Formalism.L2.SG.InstExistsPf
