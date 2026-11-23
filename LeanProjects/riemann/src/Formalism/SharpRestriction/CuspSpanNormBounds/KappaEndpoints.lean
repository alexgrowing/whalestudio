import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdentityCellAdmissibleOfNormalisation
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeIndexAndWeightTheory
import Formalism.FlagUnipotentLattices.AutBoundOfMinkowskiBound
import Formalism.FlagUnipotentLattices.LiftFixesBaseVector
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ParabolicSumAdmissibleOfParabolic
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.HypothesesNumericalConsequences
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
import Formalism.FlagUnipotentLattices.IdealCountLeWAsm
import Formalism.FlagUnipotentLattices.IotaCountFullAsm
import Formalism.FlagUnipotentLattices.ValuationProductBound
import Formalism.FlagUnipotentLattices.GramSubmersionSplit

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def nfH (S : HSpace E) : Formalism.HermitianLatticeCounting.S6.HermSpace E S.V where
  B := S.hT.flip
  herm x y := (a_herm y x).symm
  nondeg x h := S.nondeg.2 x h

def nfF (F : FlagG S r T) (hT : T ≠ 0) : Formalism.HermitianLatticeCounting.S6.FlagD (nfH S) r where
  e := F.fvec
  T := T
  indep := by
    have h : (fun a : Fin r => F.fvec a.castSucc) = F.e := funext (geo_fvec_cast F)
    rw [h]; exact F.e_indep
  iso a b := by rw [geo_fvec_cast, geo_fvec_cast]; exact F.e_iso b a
  zperp a := by rw [geo_fvec_cast, geo_fvec_last]; exact p_symm_zero S (F.z_orth a)
  zz := by rw [geo_fvec_last]; exact F.z_norm
  hT := hT

theorem nf_mem_perp {U : Submodule E S.V} {y : S.V} : y ∈ perpS S U ↔ ∀ x ∈ U, S.hT x y = 0 := Iff.rfl

theorem nf_Xa (F : FlagG S r T) (hT : T ≠ 0) (a : ℕ) : (nfF F hT).Xa a = F.Xa a := by
  have h : (fun b : Fin r => F.fvec b.castSucc) = F.e := funext (geo_fvec_cast F)
  show Submodule.span E ((fun b : Fin r => F.fvec b.castSucc) '' {b | b.val < a}) = _
  rw [h]; rfl

theorem nf_X_eq (F : FlagG S r T) : F.X = F.Xa r := by
  unfold FlagG.X FlagG.Xa
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩

theorem nf_X (F : FlagG S r T) (hT : T ≠ 0) : (nfF F hT).X = F.X := by
  show (nfF F hT).Xa r = _
  rw [nf_Xa, nf_X_eq]

theorem normal_form_z_eq (F : FlagG S r T) (hT : T ≠ 0) : (nfF F hT).z = F.z := geo_fvec_last F

theorem nf_II (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) :
    Formalism.HermitianLatticeCounting.S6.II (nfF F hT) (nfF F' hT') = Isp F F' := by
  show (nfF F hT).X ⊓ (nfF F' hT').X = _
  rw [nf_X, nf_X]; rfl

theorem normal_form_V0_eq (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) :
    Formalism.HermitianLatticeCounting.S6.V0 (nfF F hT) (nfF F' hT') = F.Xplus ⊔ F'.Xplus := by
  show (nfF F hT).X ⊔ (nfF F' hT').X ⊔ Submodule.span E {(nfF F hT).z, (nfF F' hT').z} = _
  rw [nf_X, nf_X, normal_form_z_eq, normal_form_z_eq, Submodule.span_insert]
  unfold FlagG.Xplus
  exact sup_sup_sup_comm _ _ _ _

theorem nf_Dl (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) (l : ℕ) (hl : l ≤ r + 1) :
    Dl F F' l = star (Formalism.HermitianLatticeCounting.S6.Dl (nfF F hT) (nfF F' hT') l hl) := by
  rw [tie_Dl_eq' F F' l hl]
  unfold Formalism.HermitianLatticeCounting.S6.Dl
  rw [← starRingEnd_apply, RingHom.map_det]
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Formalism.HermitianLatticeCounting.S6.Zhat, Matrix.of_apply, Zhat,
    brS, starRingEnd_apply]
  exact a_herm _ _

theorem nf_G (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) :
    Formalism.HermitianLatticeCounting.S6.Gval (nfF F hT) (nfF F' hT') = Gflag F F' := by
  unfold Formalism.HermitianLatticeCounting.S6.Gval Gflag
  rw [nf_Dl F F' hT hT' (r + 1) le_rfl, nf_Dl F F' hT hT' r (Nat.le_succ r), star_star, star_star]
  show _ - T * T' * _ = _
  ring

theorem nf_LieN (F : FlagG S r T) (hT : T ≠ 0) (Y : S.V →ₗ[E] S.V) (h : (nfF F hT).LieN Y) : Y ∈ F.LieN := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun x y => ?_, fun a _ _ => ?_, fun x hx => ?_⟩
  · have h := h1 y x
    rw [add_comm]; exact h
  · have hle : F.Xa a ≤ (F.Xa (a - 1)).comap Y := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      have h := h2 i
      rw [nf_Xa] at h
      have h' : Y (F.e i) ∈ F.Xa i.val := by rw [← geo_fvec_cast]; exact h
      have hi' : i.val < a := hi
      exact geo_Xa_mono F (by omega) h'
    exact fun x hx => hle hx
  · have h := h3 x (fun a => p_symm_zero S (hx (F.fvec a.castSucc)
      (by rw [geo_fvec_cast]; exact Submodule.subset_span ⟨a, rfl⟩)))
    rw [nf_X] at h; exact h

theorem nf_ell (F : FlagG S r T) (hT : T ≠ 0) (Y : S.V →ₗ[E] S.V) (s : E) (h : (nfF F hT).DPsi Y s) : F.ell Y = s := by
  obtain ⟨c, hc, h⟩ := h
  rw [← hc]
  unfold FlagG.ell
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h1 := h a
  rw [nf_Xa] at h1
  have h2 : Y (F.fvec a.succ) = c a • F.e a + (Y (F.fvec a.succ) - c a • F.e a) := by abel
  rw [h2]
  refine geo_coefX F a (c a) _ ?_
  rw [← geo_fvec_cast]; exact h1

theorem nf_rel (K : Type) [Field K] [Algebra K E] (htr : ∀ x : E, algebraMap K E (Algebra.trace K E x) = x + star x)
    (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) (h : Relevant K F F') :
    Formalism.HermitianLatticeCounting.S6.Relevant (nfF F hT) (nfF F' hT') := by
  intro Y hY hY' s s' hs hs'
  have h0 := h Y ⟨nf_LieN F hT Y hY, nf_LieN F' hT' Y hY'⟩
  unfold FlagG.dpsi at h0
  rw [nf_ell F hT Y s hs, nf_ell F' hT' Y s' hs'] at h0
  rw [← htr, ← htr, h0]

theorem nf_pos (F : LFlag S r T) (hT : T ≠ 0) (hP : PosX F) (σ : E →+* ℂ) : (nfF F.fl hT).PosDefAt σ := by
  intro w hw hX
  rw [nf_X] at hX
  refine hP σ w ?_ hX
  rw [← a_span_frame]
  exact a_orth_of_frame _ _ (fun i => p_symm_zero S (hw i))

theorem nf_level (F : FlagG S r T) (hT : T ≠ 0) (x : S.V) (a : Fin r) (al : E) (h : (nfF F hT).HasLevel x a al) :
    F.level x = a.val + 1 := by
  obtain ⟨hal, hx⟩ := h
  rw [nf_Xa] at hx
  have hx' : x - al • F.e a ∈ F.Xa a.val := by rw [← geo_fvec_cast]; exact hx
  have hmem : x ∈ F.Xa (a.val + 1) := by
    have h : x = (x - al • F.e a) + al • F.e a := by abel
    rw [h]
    exact Submodule.add_mem _ (geo_Xa_mono F (Nat.le_succ _) hx')
      (Submodule.smul_mem _ _ (geo_e_mem_Xa F a _ (Nat.lt_succ_self _)))
  have hnot : ∀ n ∈ {n | x ∈ F.Xa n}, a.val + 1 ≤ n := by
    intro n hn
    by_contra hlt
    have hn' : x ∈ F.Xa a.val := geo_Xa_mono F (by omega) hn
    have h1 : al • F.e a ∈ F.Xa a.val := by
      have h : al • F.e a = x - (x - al • F.e a) := by abel
      rw [h]; exact Submodule.sub_mem _ hn' hx'
    have h2 : F.e a ∈ F.Xa a.val := by
      have h := Submodule.smul_mem _ al⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hal, one_smul] at h
    exact F.e_indep.notMem_span_image (s := {i | i.1 < a.val}) (by simp) h2
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ hnot)

theorem nf_levels (F : FlagG S r T) (hT : T ≠ 0) (I : Submodule E S.V) (j : ℕ)
    (h1 : ∀ x ∈ I, x ≠ 0 → ∃ (a : Fin r) (al : E), (nfF F hT).HasLevel x a al ∧ j ≤ a.val)
    (h2 : ∀ a : Fin r, j ≤ a.val → ∃ x ∈ I, ∃ al : E, (nfF F hT).HasLevel x a al) (a : ℕ) :
    (∃ x ∈ I, x ≠ 0 ∧ F.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ r) := by
  constructor
  · rintro ⟨x, hx, hx0, rfl⟩
    obtain ⟨b, al, hl, hjb⟩ := h1 x hx hx0
    rw [nf_level F hT x b al hl]
    exact ⟨by omega, b.2⟩
  · rintro ⟨h1a, h2a⟩
    obtain ⟨x, hx, al, hl⟩ := h2 ⟨a - 1, by omega⟩ (by show j ≤ a - 1; omega)
    have hlev := nf_level F hT x _ al hl
    have hlev' : F.level x = a := by rw [hlev]; show a - 1 + 1 = a; omega
    refine ⟨x, hx, ?_, hlev'⟩
    rintro rfl
    have h0 : F.level 0 = 0 := Nat.sInf_eq_zero.2 (Or.inl (by show (0 : S.V) ∈ F.Xa 0; exact Submodule.zero_mem _))
    omega

theorem nf_fvec_mem (F : FlagG S r T) (a : Fin (r + 1)) : F.fvec a ∈ F.Xplus := by
  have h := a_span_frame (⟨F, F.z⟩ : LFlag S r T)
  have h' : F.fvec a ∈ Submodule.span E (Set.range (frame (⟨F, F.z⟩ : LFlag S r T))) := Submodule.subset_span ⟨a, rfl⟩
  rw [h] at h'; exact h'

theorem nf_perp (F : FlagG S r T) (U I : Submodule E S.V) (hU : F.Xplus ≤ U) (hIX : I ≤ F.X)
    (hk : ∀ x ∈ F.X, (∀ w ∈ U, S.hT x w = 0) ↔ x ∈ I)
    (hs : ∀ w : S.V, (∀ a, S.hT w (F.fvec a) = 0) → ∃ x ∈ F.X, ∀ v ∈ U, S.hT (w - x) v = 0) :
    perpS S U ⊓ F.X = I ∧ perpS S U ⊔ F.X = F.XplusPerp := by
  constructor
  · ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact (hk x h2).1 (fun w hw => p_symm_zero S (h1 w hw))
    · intro hx
      exact ⟨fun w hw => p_symm_zero S ((hk x (hIX hx)).2 hx w hw), hIX hx⟩
  · apply le_antisymm
    · refine sup_le (fun y hy x hx => hy x (hU hx)) ?_
      intro y hy x hx
      exact p_mem_orth.1 (a_X_le_orth_Xplus (⟨F, F.z⟩ : LFlag S r T) hy) x hx
    · intro w hw
      obtain ⟨x, hx, h⟩ := hs w (fun a => p_symm_zero S (hw _ (nf_fvec_mem F a)))
      have h' : w = (w - x) + x := by abel
      rw [h']
      exact Submodule.add_mem_sup (nf_mem_perp.2 (fun v hv => p_symm_zero S (h v hv))) hx

theorem nf_gen (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) (j : ℕ) (hj : j ≤ r) (c : E)
    (h : Formalism.HermitianLatticeCounting.S6.NFFull (nfF F hT) (nfF F' hT') j hj c) :
    (∀ a : ℕ, (∃ x ∈ Isp F F', x ≠ 0 ∧ F.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ r)) ∧
    (∀ a : ℕ, (∃ x ∈ Isp F F', x ≠ 0 ∧ F'.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ r)) ∧
    (F'.z - c • F.z ∈ F.X ⊔ F'.X ∧ c * star c * T = T') ∧
    Dl F F' j ≠ 0 ∧
    (perpS S (F.Xplus ⊔ F'.Xplus) ⊓ F.X = Isp F F' ∧ perpS S (F.Xplus ⊔ F'.Xplus) ⊔ F.X = F.XplusPerp) ∧
    (perpS S (F.Xplus ⊔ F'.Xplus) ⊓ F'.X = Isp F F' ∧ perpS S (F.Xplus ⊔ F'.Xplus) ⊔ F'.X = F'.XplusPerp) := by
  obtain ⟨⟨-, -, hlev, hall, -, -, -, -, hz⟩, hcc, hD, -, -, hk, hk', hs, hs'⟩ := h
  rw [nf_II] at hlev hall
  rw [nf_X, nf_X, normal_form_z_eq, normal_form_z_eq] at hz
  simp only [normal_form_V0_eq, nf_II, nf_X] at hk hk' hs hs'
  refine ⟨nf_levels F hT _ j ?_ ?_, nf_levels F' hT' _ j ?_ ?_, ⟨hz, hcc⟩, ?_,
    nf_perp F _ _ le_sup_left inf_le_left hk hs, nf_perp F' _ _ le_sup_right inf_le_right hk' hs'⟩
  · intro x hx hx0
    obtain ⟨a, al, al', h1, -, h3, -⟩ := hlev x hx hx0
    exact ⟨a, al, h1, h3⟩
  · intro a ha
    obtain ⟨x, hx, al, al', h1, -⟩ := hall a ha
    exact ⟨x, hx, al, h1⟩
  · intro x hx hx0
    obtain ⟨a, al, al', -, h2, h3, -⟩ := hlev x hx hx0
    exact ⟨a, al', h2, h3⟩
  · intro a ha
    obtain ⟨x, hx, al, al', -, h2⟩ := hall a ha
    exact ⟨x, hx, al', h2⟩
  · rw [nf_Dl F F' hT hT' j (hj.trans (Nat.le_succ r))]
    exact star_ne_zero.2 hD

theorem nf_Xplus_eq (F : FlagG S r T) (F' : FlagG S r T') (hX : F'.X = F.X) (c : E) (hc : c ≠ 0)
    (hz : F'.z - c • F.z ∈ F.X) : F'.Xplus = F.Xplus := by
  unfold FlagG.Xplus
  rw [hX]
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_le.2 ?_)
    rintro _ rfl
    have h : F'.z = (F'.z - c • F.z) + c • F.z := by abel
    show F'.z ∈ _
    rw [h]
    exact Submodule.add_mem_sup hz (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · refine sup_le le_sup_left (Submodule.span_le.2 ?_)
    rintro _ rfl
    have h : F.z = (-c⁻¹) • (F'.z - c • F.z) + c⁻¹ • F'.z := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hc, neg_smul, neg_smul, one_smul]; abel
    show F.z ∈ _
    rw [h]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ hz) (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

end Gen

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : TermTie D)

theorem nf_T_ne (D : D7) (u : D.what₂.Word) : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (tie_Tu_pos D u).ne'

theorem nf_core {u u' : D.what₂.Word} (t : D.s.Term u u') (hr : D.s.relevant t) (hG : D.s.Gterm t = 0) :
    ∃ (j : ℕ) (hj : j ≤ D.R.rS) (c : D.host.E),
      Formalism.HermitianLatticeCounting.S6.NFFull (nfF (X.fl t).fl (nf_T_ne D u)) (nfF (X.fl' t).fl (nf_T_ne D u')) j hj c := by
  obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hpos : ∀ v : D.what₂.Word, 0 < (σ ((Tu D v : ℕ) : D.host.E)).re := by
    intro v
    rw [map_natCast, Complex.natCast_re]
    exact_mod_cast tie_Tu_pos D v
  refine Formalism.HermitianLatticeCounting.Final.S6.normalForm D.host.E (hS D).V σ (nfH (hS D)) D.R.rS _ _ (fun x => p_starConj D σ x)
    (hpos u) (hpos u') (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ) (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u') _) σ)
    (nf_rel D.host.F (tie_trace D.sp.cm) _ _ _ _ ((X.rel_iff t).1 hr)) ?_
  rw [nf_G]
  have h := X.G_eq t
  rw [hG, map_zero] at h
  exact h.symm

theorem nf_j_pos (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    {u : D.what₂.Word} (t : D.s.Term u u) (hr : D.s.relevant t) (hid : ¬ D.s.isId t) (j : ℕ) (hj : j ≤ D.R.rS) (c : D.host.E)
    (hN : Formalism.HermitianLatticeCounting.S6.NFFull (nfF (X.fl t).fl (nf_T_ne D u)) (nfF (X.fl' t).fl (nf_T_ne D u)) j hj c) : 1 ≤ j := by
  by_contra hj0
  have hj0 : j = 0 := by omega
  subst hj0
  obtain ⟨k1, -, k3⟩ := Formalism.HermitianLatticeCounting.Final.S6.nFJZero _ _ _ _ _ _ c hN.1
  apply hid
  have hXa : ∀ a, (X.fl' t).fl.Xa a = (X.fl t).fl.Xa a := fun a => by
    have h := k1 a; rwa [nf_Xa, nf_Xa] at h
  refine cIdFlag_of_tie X hTg u t ⟨hXa, ?_⟩ hr
  rw [nf_X, normal_form_z_eq, normal_form_z_eq] at k3
  exact nf_Xplus_eq _ _ (by rw [nf_X_eq, nf_X_eq]; exact hXa _) c hN.1.1 k3

theorem normal_form_of_identity_cell (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    {u u' : D.what₂.Word} (t : D.s.Term u u') (h : LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t) : LatticeIndexAndWeightTheory.NF X t := by
  obtain ⟨hr, hG, hid⟩ := h
  obtain ⟨j, hj, c, hN⟩ := nf_core X t hr hG
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := nf_gen _ _ _ _ j hj c hN
  unfold LatticeIndexAndWeightTheory.NF
  refine ⟨j, hj, ?_, g1, g2, ⟨c, g3.1, g3.2⟩, g4, g5, g6⟩
  intro huu
  subst huu
  exact nf_j_pos X hTg t hr hid j hj c hN

end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.HermitianLatticeCounting.S6

section Cov

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem tj_symm {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by rw [← H.herm, h, star_zero]

theorem tj_X_perp (F : FlagD H r) {x y : V} (hx : x ∈ F.X) (hy : ∀ a : Fin (r + 1), H.B (F.e a) y = 0) : H.B x y = 0 := by
  have hle : F.X ≤ LinearMap.ker (H.B.flip y) := by
    unfold FlagD.X FlagD.Xa
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    exact LinearMap.mem_ker.2 (hy b.castSucc)
  exact LinearMap.mem_ker.1 (hle hx)

theorem tj_e_mem (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert_iff.2 (Or.inl rfl)))
  | cast b => exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))

theorem tj_e_mem' (F F' : FlagD H r) (a : Fin (r + 1)) : F'.e a ∈ V0 F F' := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert_iff.2 (Or.inr rfl)))
  | cast b => exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨b, b.2, rfl⟩))

theorem tj_X_le (F F' : FlagD H r) : F.X ≤ V0 F F' := le_sup_of_le_left le_sup_left

theorem tj_X_le' (F F' : FlagD H r) : F'.X ≤ V0 F F' := le_sup_of_le_left le_sup_right

theorem tj_mk {U : Type} [AddCommGroup U] [Module K U] (Wt X : Submodule K V) (κ : U →ₗ[K] V)
    (hex : ∀ w, ∃! wt : V, wt ∈ Wt ∧ κ w - wt ∈ X) : ∃ b : U →ₗ[K] Wt, ∀ w, κ w - (b w : V) ∈ X := by
  have hex' : ∀ w, ∃ wt : V, (wt ∈ Wt ∧ κ w - wt ∈ X) ∧ ∀ y : V, (y ∈ Wt ∧ κ w - y ∈ X) → y = wt := hex
  choose f hf hu using hex'
  refine ⟨{ toFun := fun w => ⟨f w, (hf w).1⟩, map_add' := ?_, map_smul' := ?_ }, fun w => (hf w).2⟩
  · intro w w'
    apply Subtype.ext
    show f (w + w') = f w + f w'
    symm
    refine hu _ _ ⟨Wt.add_mem (hf w).1 (hf w').1, ?_⟩
    have e : κ (w + w') - (f w + f w') = (κ w - f w) + (κ w' - f w') := by rw [map_add]; abel
    rw [e]
    exact X.add_mem (hf w).2 (hf w').2
  · intro c w
    apply Subtype.ext
    show f (c • w) = c • f w
    symm
    refine hu _ _ ⟨Wt.smul_mem _ (hf w).1, ?_⟩
    rw [map_smul, ← smul_sub]
    exact X.smul_mem _ (hf w).2

theorem tj_side (G : FlagD H r) (Wt : Submodule K V) (hW : ∀ w ∈ Wt, ∀ a, H.B (G.e a) w = 0)
    (hex : ∀ w : V, (∀ a, H.B (G.e a) w = 0) → ∃! wt : V, wt ∈ Wt ∧ w - wt ∈ G.X)
    {U : Type} [AddCommGroup U] [Module K U] (q : U → U → K) (hq : ∀ w, (∀ w', q w w' = 0) → w = 0)
    (κ : U →ₗ[K] V) (hκ : ∀ w w', H.B (κ w) (κ w') = q w w') (hp : ∀ w a, H.B (G.e a) (κ w) = 0)
    (hs : ∀ y, (∀ a, H.B (G.e a) y = 0) → ∃ w, y - κ w ∈ G.X) :
    ∃ b : U ≃ₗ[K] Wt, (∀ w, κ w - (b w : V) ∈ G.X) ∧ (∀ w w', H.B (b w : V) (b w' : V) = q w w') ∧
      ∀ w (p : V), p ∈ Wt → κ w - p ∈ G.X → p = b w := by
  obtain ⟨b, hb⟩ := tj_mk Wt G.X κ (fun w => hex (κ w) (hp w))
  have huniq : ∀ w (p : V), p ∈ Wt → κ w - p ∈ G.X → p = b w := fun w p h1 h2 =>
    (hex (κ w) (hp w)).unique ⟨h1, h2⟩ ⟨(b w).2, hb w⟩
  have hiso : ∀ w w', H.B (b w : V) (b w' : V) = q w w' := by
    intro w w'
    have e : H.B (κ w) (κ w') = H.B (b w : V) (b w' : V) + H.B (κ w - b w) (κ w') + H.B (b w : V) (κ w' - b w') := by
      simp only [map_sub, LinearMap.sub_apply]; abel
    rw [← hκ, e, tj_X_perp G (hb w) (hp w'), tj_symm (tj_X_perp G (hb w') (hW _ (b w).2)), add_zero, add_zero]
  have hinj : Function.Injective b := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hq
    intro w'
    have h1 := hb w
    rw [hw] at h1
    simp only [ZeroMemClass.coe_zero, sub_zero] at h1
    rw [← hκ]
    exact tj_X_perp G h1 (hp w')
  have hsurj : Function.Surjective b := by
    intro p
    obtain ⟨w, hw⟩ := hs p (hW p p.2)
    refine ⟨w, Subtype.ext (huniq w p p.2 ?_).symm⟩
    rw [← neg_sub]
    exact G.X.neg_mem hw
  exact ⟨LinearEquiv.ofBijective b ⟨hinj, hsurj⟩, hb, hiso, huniq⟩

theorem tj_lift [FiniteDimensional K V] (F F' : FlagD H r) (hI : ∀ i ∈ II F F', ∀ y ∈ V0 F F', H.B y i = 0) :
    ∃ Wt : Submodule K V, IsLift F F' Wt := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (II F F')
  let P : Submodule K V := ⨅ y ∈ V0 F F', LinearMap.ker (H.B y)
  have hP : ∀ w, w ∈ P ↔ ∀ y ∈ V0 F F', H.B y w = 0 := fun w => by
    simp only [P, Submodule.mem_iInf, LinearMap.mem_ker]
  refine ⟨C ⊓ P, fun w hw => (hP w).1 hw.2, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    exact (Submodule.disjoint_def.1 hC.disjoint x hx.2 hx.1.1) ▸ Submodule.zero_mem _
  · intro w hw
    have hw' : w ∈ II F F' ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨i, hi, c, hc, rfl⟩ := Submodule.mem_sup.1 hw'
    refine Submodule.add_mem _ (Submodule.mem_sup_right hi) (Submodule.mem_sup_left ⟨hc, (hP c).2 ?_⟩)
    intro y hy
    have h1 := hw y hy
    rw [map_add, hI i hi y hy, zero_add] at h1
    exact h1

theorem tj_cov [FiniteDimensional K V] (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K) (hN : NFFull F F' j hj c)
    (hA : F.Aniso) (hA' : F'.Aniso) {U : Type} [AddCommGroup U] [Module K U] (q : U → U → K)
    (hq : ∀ w, (∀ w', q w w' = 0) → w = 0) (κ κ' : U →ₗ[K] V)
    (hκ : ∀ w w', H.B (κ w) (κ w') = q w w') (hκ' : ∀ w w', H.B (κ' w) (κ' w') = q w w')
    (hp : ∀ w a, H.B (F.e a) (κ w) = 0) (hp' : ∀ w a, H.B (F'.e a) (κ' w) = 0)
    (hs : ∀ y, (∀ a, H.B (F.e a) y = 0) → ∃ w, y - κ w ∈ F.X)
    (hs' : ∀ y, (∀ a, H.B (F'.e a) y = 0) → ∃ w, y - κ' w ∈ F'.X) :
    ∃ θ : U ≃ₗ[K] U, (∀ w w', q (θ w) (θ w') = q w w') ∧
      ((∀ w p, (∀ y ∈ V0 F F', H.B y p = 0) → κ w - p ∈ F.X → κ' w - p ∈ F'.X) → ∀ w, θ w = w) ∧
      ∀ h : U ≃ₗ[K] U, (∀ w w', q (h w) (h w') = q w w') →
        ∃ σ : V ≃ₗ[K] V, (∀ x y, H.B (σ x) (σ y) = H.B x y) ∧ (∀ y ∈ V0 F F', σ y = y) ∧
          (∀ w, σ (κ w) - κ (h w) ∈ F.X) ∧ (∀ w, σ (κ' w) - κ' (θ.symm (h (θ w))) ∈ F'.X) := by
  have hI : ∀ i ∈ II F F', ∀ y ∈ V0 F F', H.B y i = 0 := fun i hi y hy =>
    tj_symm ((hN.2.2.2.1 i (tj_X_le F F' hi.1)).2 hi y hy)
  obtain ⟨Wt, hL⟩ := tj_lift F F' hI
  obtain ⟨L1, L2⟩ := Formalism.HermitianLatticeCounting.Final.S6.liftIsoW K V H r F F' j hj c Wt hN hL
  obtain ⟨b, hb1, hb2, hb3⟩ := tj_side F Wt (fun w hw a => hL.1 w hw _ (tj_e_mem F F' a)) L1 q hq κ hκ hp hs
  obtain ⟨b', hb1', hb2', hb3'⟩ := tj_side F' Wt (fun w hw a => hL.1 w hw _ (tj_e_mem' F F' a)) L2 q hq κ' hκ' hp' hs'
  refine ⟨b'.trans b.symm, ?_, ?_, ?_⟩
  · intro w w'
    rw [← hb2, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, hb2']
  · intro hn w
    have h1 : ((b w : Wt) : V) = b' w := hb3' w _ (b w).2 (hn w _ (hL.1 _ (b w).2) (hb1 w))
    rw [LinearEquiv.trans_apply, ← Subtype.ext h1, LinearEquiv.symm_apply_apply]
  · intro h hh
    let ht : Wt →ₗ[K] Wt := (b.symm.trans (h.trans b)).toLinearMap
    have hta : ∀ x, ht x = b (h (b.symm x)) := fun x => rfl
    have hti : ∀ x y : Wt, H.B (ht x : V) (ht y : V) = H.B (x : V) (y : V) := by
      intro x y
      rw [hta, hta, hb2, hh, ← hb2, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    obtain ⟨g, ⟨hg1, hg2, hg3⟩, -⟩ := Formalism.HermitianLatticeCounting.Final.S6.liftUnitary K V H r F F' Wt ht hA hA' hL hti
    have hfix := (Formalism.HermitianLatticeCounting.Final.S6.lift_fixes_base_vector K V H r F F' Wt g hL hg1).1
    refine ⟨LinearEquiv.ofBijective g hg2, hg1.1, hfix, ?_, ?_⟩
    · intro w
      show g (κ w) - κ (h w) ∈ F.X
      have e0 : κ w = (κ w - b w) + b w := by abel
      have e1 : g (κ w) = (κ w - b w) + b (h w) := by
        conv_lhs => rw [e0]
        rw [map_add, hfix _ (tj_X_le F F' (hb1 w)), hg3 (b w), hta, LinearEquiv.symm_apply_apply]
      have e2 : g (κ w) - κ (h w) = (κ w - b w) - (κ (h w) - b (h w)) := by rw [e1]; abel
      rw [e2]
      exact F.X.sub_mem (hb1 w) (hb1 (h w))
    · intro w
      show g (κ' w) - κ' ((b'.trans b.symm).symm (h ((b'.trans b.symm) w))) ∈ F'.X
      set v := (b'.trans b.symm).symm (h ((b'.trans b.symm) w)) with hv
      have hbv : b' v = b (h (b.symm (b' w))) := by
        rw [hv]
        simp [LinearEquiv.trans_apply]
      have e0 : κ' w = (κ' w - b' w) + b' w := by abel
      have e1 : g (κ' w) = (κ' w - b' w) + b' v := by
        conv_lhs => rw [e0]
        rw [map_add, hfix _ (tj_X_le' F F' (hb1' w)), hg3 (b' w), hta, hbv]
      have e2 : g (κ' w) - κ' v = (κ' w - b' w) - (κ' v - b' v) := by rw [e1]; abel
      rw [e2]
      exact F'.X.sub_mem (hb1' w) (hb1' v)

end Cov

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

section Schur

variable {G : Type} [Group G] (Sg : Subgroup G)
variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem tj_schur_off (ρ : G → A →L[ℂ] A) (ρ' : G → B →L[ℂ] B) (hone : ρ' 1 = ContinuousLinearMap.id ℂ B)
    (hmul : ∀ h ∈ Sg, ∀ h' ∈ Sg, ρ' (h * h') = (ρ' h).comp (ρ' h'))
    (hno : ∀ P : B →L[ℂ] A, (∀ h ∈ Sg, (ρ h).comp P = P.comp (ρ' h)) → P = 0)
    (J : B →L[ℂ] A) (θ : G) (hθ : θ ∈ Sg) (hcov : ∀ h ∈ Sg, (ρ h).comp J = J.comp (ρ' (θ⁻¹ * h * θ))) : J = 0 := by
  have hθ' : θ⁻¹ ∈ Sg := Sg.inv_mem hθ
  have hP : J.comp (ρ' θ⁻¹) = 0 := by
    apply hno
    intro h hh
    rw [← ContinuousLinearMap.comp_assoc, hcov h hh, ContinuousLinearMap.comp_assoc,
      ← hmul _ (Sg.mul_mem (Sg.mul_mem hθ' hh) hθ) _ hθ', ContinuousLinearMap.comp_assoc, ← hmul _ hθ' _ hh]
    congr 2
    group
  have h1 : J = (J.comp (ρ' θ⁻¹)).comp (ρ' θ) := by
    rw [ContinuousLinearMap.comp_assoc, ← hmul _ hθ' _ hθ, inv_mul_cancel, hone, ContinuousLinearMap.comp_id]
  rw [h1, hP, ContinuousLinearMap.zero_comp]

theorem tj_schur_diag [FiniteDimensional ℂ A] (ρ : G → A →L[ℂ] A)
    (hirr : ∀ K : Submodule ℂ A, (∀ h ∈ Sg, ∀ x ∈ K, ρ h x ∈ K) → K = ⊥ ∨ K = ⊤)
    (J : A →L[ℂ] A) (hc : ∀ h ∈ Sg, (ρ h).comp J = J.comp (ρ h)) : ∃ s : ℂ, J = s • ContinuousLinearMap.id ℂ A := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, ContinuousLinearMap.ext (fun x => Subsingleton.elim _ _)⟩
  · obtain ⟨s, hs⟩ := Module.End.exists_eigenvalue (J : A →ₗ[ℂ] A)
    refine ⟨s, ?_⟩
    have hinv : ∀ h ∈ Sg, ∀ x ∈ Module.End.eigenspace (J : A →ₗ[ℂ] A) s, ρ h x ∈ Module.End.eigenspace (J : A →ₗ[ℂ] A) s := by
      intro h hh x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      have h1 : J (ρ h x) = ρ h (J x) := (congrArg (fun T : A →L[ℂ] A => T x) (hc h hh)).symm
      show J (ρ h x) = s • ρ h x
      rw [h1, show J x = s • x from hx, map_smul]
    rcases hirr _ hinv with h0 | h1
    · exact absurd h0 hs
    · ext x
      have hx : x ∈ Module.End.eigenspace (J : A →ₗ[ℂ] A) s := by rw [h1]; exact Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hx
      simpa using hx

end Schur

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tj_Q (D : D7) (hind : LinearIndependent D.host.E D.sp.hypE) (y : (hS D).V)
    (h1 : ∀ a, (hS D).hT (D.sp.hypE a) y = 0) (h2 : (hS D).hT D.sp.zm y = 0) :
    ∃ w : (D.sp.X 0).V, y - D.sp.iXY 0 w ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
  classical
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hι : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y := D.sp.iXY_isom 0 hm
  have hinj : Function.Injective (D.sp.iXY 0) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    refine (D.sp.X 0).nondeg.2 w (fun w' => ?_)
    rw [← hι, hw, map_zero]
  have hT0 : ((D.sp.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 D.sp.T_prime.ne_zero
  let L : (hS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) × D.host.E :=
    (LinearMap.pi fun a => (hS D).hT (D.sp.hypE a)).prod ((hS D).hT D.sp.zm)
  have hL : ∀ v, L v = (fun a => (hS D).hT (D.sp.hypE a) v, (hS D).hT D.sp.zm v) := fun v => rfl
  have hsurj : Function.Surjective L := by
    rintro ⟨c, d⟩
    refine ⟨∑ a, c a • D.sp.hypF a + ((-(D.sp.T : D.host.E))⁻¹ * d) • D.sp.zm, ?_⟩
    rw [hL]
    apply Prod.ext
    · funext b
      have hz : (hS D).hT (D.sp.hypE b) D.sp.zm = 0 := p_symm_zero _ (D.sp.hyp_orthz b).1
      simp only [map_add, map_sum, map_smul, smul_eq_mul, D.sp.hyp_ef, hz, mul_zero, add_zero, mul_ite, mul_one,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · have hz : ∀ a, (hS D).hT D.sp.zm (D.sp.hypF a) = 0 := fun a => (D.sp.hyp_orthz a).2
      simp only [map_add, map_sum, map_smul, smul_eq_mul, hz, mul_zero, Finset.sum_const_zero, zero_add, D.sp.zm_norm]
      field_simp
  have hker : Module.finrank D.host.E (LinearMap.ker L) = D.R.k + D.R.rS := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self,
      p_rankV] at h
    omega
  have hinf : Submodule.span D.host.E (Set.range D.sp.hypE) ⊓ LinearMap.range (D.sp.iXY 0) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, ⟨w, rfl⟩⟩
    have hle : ∀ w', Submodule.span D.host.E (Set.range D.sp.hypE) ≤ LinearMap.ker ((hS D).hT (D.sp.iXY 0 w')) := by
      intro w'
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      exact LinearMap.mem_ker.2 (D.sp.hyp_orthX a w').1
    have hw : w = 0 := (D.sp.X 0).nondeg.2 w (fun w' => by rw [← hι]; exact LinearMap.mem_ker.1 (hle w' hx1))
    rw [hw, map_zero]
    exact Submodule.zero_mem _
  have hA : Module.finrank D.host.E
      ↥(Submodule.span D.host.E (Set.range D.sp.hypE) ⊔ LinearMap.range (D.sp.iXY 0)) = D.R.k + D.R.rS := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span D.host.E (Set.range D.sp.hypE))
      (LinearMap.range (D.sp.iXY 0))
    rw [hinf, finrank_bot, finrank_span_eq_card hind, Fintype.card_fin, LinearMap.finrank_range_of_inj hinj,
      (D.sp.X 0).rank_eq, D.sp.X_rank 0 (Nat.zero_le _)] at h
    simp only [Ranks.N, zero_mul, add_zero] at h
    omega
  have hle : Submodule.span D.host.E (Set.range D.sp.hypE) ⊔ LinearMap.range (D.sp.iXY 0) ≤ LinearMap.ker L := by
    refine sup_le (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨b, rfl⟩
      refine LinearMap.mem_ker.2 ?_
      rw [hL]
      exact Prod.ext (funext fun a => D.sp.hyp_ee a b) (D.sp.hyp_orthz b).1
    · rintro _ ⟨w, rfl⟩
      refine LinearMap.mem_ker.2 ?_
      rw [hL]
      exact Prod.ext (funext fun a => p_symm_zero _ (D.sp.hyp_orthX a w).1) (p_symm_zero _ (D.sp.zm_orth w))
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hA, hker])
  have hy : y ∈ LinearMap.ker L := by
    refine LinearMap.mem_ker.2 ?_
    rw [hL]
    exact Prod.ext (funext h1) h2
  rw [← heq] at hy
  obtain ⟨x, hx, _, ⟨w, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
  exact ⟨w, by rw [add_sub_cancel_right]; exact hx⟩

variable {D : D7} (X : TermTie D)

theorem tj_zm (D : D7) (u : D.what₂.Word) (y : (hS D).V) (h : (hS D).hT y (D.zmOf u) = 0) : (hS D).hT D.sp.zm y = 0 := by
  unfold D7.zmOf at h
  rw [map_smul, smul_eq_mul] at h
  rcases mul_eq_zero.1 h with h0 | h0
  · exact absurd h0 (inv_ne_zero (D.cOf_ne u))
  · exact p_symm_zero _ h0

theorem tj_W_zm (D : D7) (u : D.what₂.Word) (w : (D.sp.X 0).V) : (hS D).hT (D.sp.iXY 0 w) (D.zmOf u) = 0 := by
  unfold D7.zmOf
  rw [map_smul, D.sp.zm_orth, smul_zero]

theorem tj_tie {u u' : D.what₂.Word} (t : D.s.Term u u') (hr : D.s.relevant t) (hG : D.s.Gterm t = 0)
    (he : (X.fl t).fl.e = D.sp.hypE) (hz : (X.fl t).fl.z = D.zmOf u)
    (δ : (hS D).V ≃ₗ[D.host.E] (hS D).V) (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT)
    (hδe : ∀ a, δ (D.sp.hypE a) = (X.fl' t).fl.e a) (hδz : δ (D.zmOf u') = (X.fl' t).fl.z) :
    ∃ θ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
      ((∀ x ∈ perpS (hS D) (Xplus (X.fl t) ⊔ Xplus (X.fl' t)), δ x - x ∈ Xsp (X.fl' t)) → θ = 1) ∧
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∃ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT,
        (∀ x ∈ Xplus (X.fl t) ⊔ Xplus (X.fl' t), σ x = x) ∧
        (∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (h w) ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) ∧
        (∀ w, (δ⁻¹ * σ * δ) (D.sp.iXY 0 w) - D.sp.iXY 0 ((θ⁻¹ * h * θ) w) ∈
          Submodule.span D.host.E (Set.range D.sp.hypE)) := by
  obtain ⟨j, hj, c, hN⟩ := nf_core X t hr hG
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hι : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y := D.sp.iXY_isom 0 hm
  have hδi : ∀ x y, (hS D).hT (δ x) (δ y) = (hS D).hT x y := hδ
  have hind : LinearIndependent D.host.E D.sp.hypE := he ▸ (X.fl t).fl.e_indep
  have hX : (X.fl t).fl.X = Submodule.span D.host.E (Set.range D.sp.hypE) := by unfold FlagG.X; rw [he]
  have hδX : ∀ x ∈ Submodule.span D.host.E (Set.range D.sp.hypE), δ x ∈ (X.fl' t).fl.X := by
    have hle : Submodule.span D.host.E (Set.range D.sp.hypE) ≤ ((X.fl' t).fl.X).comap (δ : (hS D).V →ₗ[D.host.E] (hS D).V) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      show δ (D.sp.hypE a) ∈ (X.fl' t).fl.X
      rw [hδe]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact fun x hx => hle hx
  have hδX' : ∀ x ∈ (X.fl' t).fl.X, δ.symm x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
    have hle : (X.fl' t).fl.X ≤
        (Submodule.span D.host.E (Set.range D.sp.hypE)).comap (δ.symm : (hS D).V →ₗ[D.host.E] (hS D).V) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      show δ.symm ((X.fl' t).fl.e a) ∈ Submodule.span D.host.E (Set.range D.sp.hypE)
      rw [← hδe, LinearEquiv.symm_apply_apply]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact fun x hx => hle hx
  have hA : (nfF (X.fl t).fl (nf_T_ne D u)).Aniso := by
    intro w h1 h2
    rw [nf_X]
    exact tie_aniso D _ (tie_Tu_pos D u) (X.fl t) w (fun a => p_symm_zero _ (h1 a)) h2
  have hA' : (nfF (X.fl' t).fl (nf_T_ne D u')).Aniso := by
    intro w h1 h2
    rw [nf_X]
    exact tie_aniso D _ (tie_Tu_pos D u') (X.fl' t) w (fun a => p_symm_zero _ (h1 a)) h2
  obtain ⟨θ, hθ, hθ1, hall⟩ := tj_cov _ _ j hj c hN hA hA' (fun w w' : (D.sp.X 0).V => (D.sp.X 0).hT w' w)
    (fun w h => (D.sp.X 0).nondeg.2 w h) (D.sp.iXY 0) ((δ : (hS D).V →ₗ[D.host.E] (hS D).V).comp (D.sp.iXY 0))
    (fun w w' => hι w' w) (fun w w' => (hδi _ _).trans (hι w' w))
    (by
      intro w a
      show (hS D).hT (D.sp.iXY 0 w) ((X.fl t).fl.fvec a) = 0
      induction a using Fin.lastCases with
      | last => rw [geo_fvec_last, hz]; exact tj_W_zm D u w
      | cast b => rw [geo_fvec_cast, he]; exact (D.sp.hyp_orthX b w).1)
    (by
      intro w a
      show (hS D).hT (δ (D.sp.iXY 0 w)) ((X.fl' t).fl.fvec a) = 0
      induction a using Fin.lastCases with
      | last => rw [geo_fvec_last, ← hδz, hδi]; exact tj_W_zm D u' w
      | cast b => rw [geo_fvec_cast, ← hδe, hδi]; exact (D.sp.hyp_orthX b w).1)
    (by
      intro y hy
      rw [nf_X, hX]
      refine tj_Q D hind y (fun a => ?_) ?_
      · have h := hy a.castSucc
        have h' : (hS D).hT y ((X.fl t).fl.fvec a.castSucc) = 0 := h
        rw [geo_fvec_cast, he] at h'
        exact p_symm_zero _ h'
      · have h' : (hS D).hT y ((X.fl t).fl.fvec (Fin.last _)) = 0 := hy (Fin.last _)
        rw [geo_fvec_last, hz] at h'
        exact tj_zm D u y h')
    (by
      intro y hy
      rw [nf_X]
      have k1 : ∀ a, (hS D).hT (D.sp.hypE a) (δ.symm y) = 0 := by
        intro a
        have h' : (hS D).hT y ((X.fl' t).fl.fvec a.castSucc) = 0 := hy a.castSucc
        rw [geo_fvec_cast, ← hδe] at h'
        have h2 : (hS D).hT (δ (δ.symm y)) (δ (D.sp.hypE a)) = 0 := by rw [LinearEquiv.apply_symm_apply]; exact h'
        rw [hδi] at h2
        exact p_symm_zero _ h2
      have k2 : (hS D).hT D.sp.zm (δ.symm y) = 0 := by
        have h' : (hS D).hT y ((X.fl' t).fl.fvec (Fin.last _)) = 0 := hy (Fin.last _)
        rw [geo_fvec_last, ← hδz] at h'
        have h2 : (hS D).hT (δ (δ.symm y)) (δ (D.zmOf u')) = 0 := by rw [LinearEquiv.apply_symm_apply]; exact h'
        rw [hδi] at h2
        exact tj_zm D u' _ h2
      obtain ⟨w, hw⟩ := tj_Q D hind (δ.symm y) k1 k2
      refine ⟨w, ?_⟩
      have h := hδX _ hw
      rw [map_sub, LinearEquiv.apply_symm_apply] at h
      exact h)
  refine ⟨θ, fun x y => hθ y x, ?_, ?_⟩
  · intro hn
    refine LinearEquiv.ext (hθ1 ?_)
    intro w p hp hwp
    rw [nf_X] at hwp ⊢
    rw [hX] at hwp
    rw [normal_form_V0_eq] at hp
    have e : ((δ : (hS D).V →ₗ[D.host.E] (hS D).V).comp (D.sp.iXY 0)) w - p = δ (D.sp.iXY 0 w - p) + (δ p - p) := by
      show δ (D.sp.iXY 0 w) - p = _
      rw [map_sub]; abel
    rw [e]
    exact Submodule.add_mem _ (hδX _ hwp) (hn p (fun x hx => p_symm_zero _ (hp x hx)))
  · intro h hh
    obtain ⟨σ, hσ1, hσ2, hσ3, hσ4⟩ := hall h (fun w w' => hh w' w)
    refine ⟨σ, fun x y => hσ1 y x, ?_, ?_, ?_⟩
    · rw [normal_form_V0_eq] at hσ2; exact hσ2
    · intro w
      have h3 := hσ3 w
      rw [nf_X, hX] at h3; exact h3
    · intro w
      have h4 := hσ4 w
      rw [nf_X] at h4
      have h5 := hδX' _ h4
      rw [map_sub] at h5
      have e : δ.symm (((δ : (hS D).V →ₗ[D.host.E] (hS D).V).comp (D.sp.iXY 0)) (θ.symm (h (θ w)))) =
          D.sp.iXY 0 (θ.symm (h (θ w))) := LinearEquiv.symm_apply_apply δ _
      rw [e] at h5
      exact h5

end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : TermTie D)

theorem tj_Jt_off {u u' : D.what₂.Word} (t : D.s.Term u u') (hr : D.s.relevant t) (hG : D.s.Gterm t = 0)
    (he : (X.fl t).fl.e = D.sp.hypE) (hz : (X.fl t).fl.z = D.zmOf u)
    (ρ : ∀ u : D.what₂.Word, ((D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) → (X.Hpi u →L[ℂ] X.Hpi u))
    (δ : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hone : ρ u' 1 = ContinuousLinearMap.id ℂ (X.Hpi u'))
    (hmul : ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ρ u' (h * h') = (ρ u' h).comp (ρ u' h'))
    (hno : ∀ P : X.Hpi u' →L[ℂ] X.Hpi u,
      (∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, (ρ u h).comp P = P.comp (ρ u' h)) → P = 0)
    (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT) (hδe : ∀ a, δ (D.sp.hypE a) = (X.fl' t).fl.e a)
    (hδz : δ (D.zmOf u') = (X.fl' t).fl.z)
    (hcov : ∀ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT, (∀ x ∈ Xplus (X.fl t) ⊔ Xplus (X.fl' t), σ x = x) →
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
        (∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (h w) ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) →
        (∀ w, (δ⁻¹ * σ * δ) (D.sp.iXY 0 w) - D.sp.iXY 0 (h' w) ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) →
        (ρ u h).comp (X.Jt t) = (X.Jt t).comp (ρ u' h')) : X.Jt t = 0 := by
  obtain ⟨θ, hθ, -, hall⟩ := tj_tie X t hr hG he hz δ hδ hδe hδz
  refine tj_schur_off (Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT) (ρ u) (ρ u') hone hmul hno (X.Jt t) θ hθ ?_
  intro h hh
  obtain ⟨σ, hσ, hfix, h3, h4⟩ := hall h hh
  exact hcov σ hσ hfix h hh _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hθ) hh) hθ) h3 h4

theorem tj_Jt_diag {u : D.what₂.Word} (t : D.s.Term u u) (hr : D.s.relevant t) (hG : D.s.Gterm t = 0)
    (he : (X.fl t).fl.e = D.sp.hypE) (hz : (X.fl t).fl.z = D.zmOf u)
    (ρ : ((D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) → (X.Hpi u →L[ℂ] X.Hpi u))
    (δ : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hirr : ∀ K : Submodule ℂ (X.Hpi u), (∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ x ∈ K, ρ h x ∈ K) → K = ⊥ ∨ K = ⊤)
    (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT) (hδe : ∀ a, δ (D.sp.hypE a) = (X.fl' t).fl.e a)
    (hδz : δ (D.zmOf u) = (X.fl' t).fl.z)
    (hcov : ∀ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT, (∀ x ∈ Xplus (X.fl t) ⊔ Xplus (X.fl' t), σ x = x) →
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
        (∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (h w) ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) →
        (∀ w, (δ⁻¹ * σ * δ) (D.sp.iXY 0 w) - D.sp.iXY 0 (h' w) ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) →
        (ρ h).comp (X.Jt t) = (X.Jt t).comp (ρ h'))
    (hn : ∀ x ∈ perpS (hS D) (Xplus (X.fl t) ⊔ Xplus (X.fl' t)), δ x - x ∈ Xsp (X.fl' t)) :
    ∃ s : ℂ, X.Jt t = s • ContinuousLinearMap.id ℂ (X.Hpi u) := by
  obtain ⟨θ, hθ, hθ1, hall⟩ := tj_tie X t hr hG he hz δ hδ hδe hδz
  have h1 := hθ1 hn
  subst h1
  refine tj_schur_diag (Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT) ρ hirr (X.Jt t) ?_
  intro h hh
  obtain ⟨σ, hσ, hfix, h3, h4⟩ := hall h hh
  have h5 := hcov σ hσ hfix h hh _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hθ) hh) hθ) h3 h4
  rwa [inv_one, one_mul, mul_one] at h5

end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem tj_hs_zero (A : Wq →L[ℂ] Wp) (h : hsNormSq A ≤ 0) : A = 0 := by
  rw [Formalism.MainNotions.BridgeLemma.hsNormSq_eq_sum] at h
  have h0 : ∀ i ∈ Finset.univ, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1
      (le_antisymm h (Finset.sum_nonneg (fun i _ => by positivity)))
  apply ContinuousLinearMap.coe_injective
  refine (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => ?_)
  have h1 := h0 i (Finset.mem_univ i)
  rw [OrthonormalBasis.coe_toBasis]
  simpa using h1

end HS

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : TermTie D)

def Ineq2a (D : D7) {u u' : D.what₂.Word} (Φ : Set (D.s.Term u u')) (c : ℝ) : Prop :=
  Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) →
    hsNormSq (KOf D.s u u' Φ) ≤ c * (∑' p : pairsIn D.s Φ, D.s.pval p.1).re

theorem tj_KOf_zero {u u' : D.what₂.Word} (Φ : Set (D.s.Term u u')) (c : ℝ) (h2a : Ineq2a D Φ c)
    (hJ : ∀ t ∈ Φ, X.Jt t = 0) : KOf D.s u u' Φ = 0 := by
  have hp : ∀ p : pairsIn D.s Φ, D.s.pval p.1 = 0 := by
    intro p
    rw [X.pval_eq, hJ _ p.2.2]
    simp [hsInner]
  have h := h2a (by simp only [hp, norm_zero]; exact summable_zero)
  simp only [hp, tsum_zero, Complex.zero_re, mul_zero] at h
  exact tj_hs_zero _ h

end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : TermTie D)

theorem off_diagonal_amplitude_zero (hA : LatticeIndexAndWeightTheory.AmpOK X) {u u' : D.what₂.Word} (huu : u ≠ u') (t : D.s.Term u u')
    (hr : D.s.relevant t) (hG : D.s.Gterm t = 0) : X.Jt t = 0 := by
  obtain ⟨hfl, ρ, δ, hρ, -, hno, hδ, hcov, -⟩ := hA
  exact tj_Jt_off X t hr hG (hfl u u' t).1 (hfl u u' t).2 ρ (δ u u' t) (hρ u').1 (hρ u').2 (hno u u' huu)
    (hδ u u' t).1 (hδ u u' t).2.1 (hδ u u' t).2.2
    (fun σ hσ hfix h hh h' hh' h3 h4 => hcov u u' t σ hσ hfix h hh h' hh' h3 h4)

theorem amplitude_scalar_on_diagonal (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    (hA : LatticeIndexAndWeightTheory.AmpOK X) {u : D.what₂.Word} (t : D.s.Term u u) (h : LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t) :
    ∃ s : ℂ, X.Jt t = s • ContinuousLinearMap.id ℂ (X.Hpi u) := by
  have hNF := normal_form_of_identity_cell X hTg t h
  obtain ⟨hfl, ρ, δ, -, hirr, -, hδ, hcov, hnorm⟩ := hA
  exact tj_Jt_diag X t h.1 h.2.1 (hfl u u t).1 (hfl u u t).2 (ρ u) (δ u u t) (hirr u)
    (hδ u u t).1 (hδ u u t).2.1 (hδ u u t).2.2
    (fun σ hσ hfix h hh h' hh' h3 h4 => hcov u u t σ hσ hfix h hh h' hh' h3 h4) (hnorm u t h hNF)

def ATie (X : TermTie D) : Prop := ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), X.Jt t = 0 → D.s.aTerm u u' t = 0

theorem off_relation_of_tie (hT : ATie X) (hA : LatticeIndexAndWeightTheory.AmpOK X) : RelevantZeroTermsVanish D :=
  fun u u' huu t hr hG => hT u u' t (off_diagonal_amplitude_zero X hA huu t hr hG)

theorem off_kernel_sum_zero (hA : LatticeIndexAndWeightTheory.AmpOK X) {u u' : D.what₂.Word} (huu : u ≠ u') (Φ : Set (D.s.Term u u')) (c : ℝ)
    (hΦ : ∀ t ∈ Φ, D.s.relevant t ∧ D.s.Gterm t = 0) (h2a : Ineq2a D Φ c) : KOf D.s u u' Φ = 0 :=
  tj_KOf_zero X Φ c h2a (fun t ht => off_diagonal_amplitude_zero X hA huu t (hΦ t ht).1 (hΦ t ht).2)

variable (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)

theorem first_statement_iff_off_relation :
    LatticeIndexAndWeightTheory.Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0 ↔ (LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → RelevantZeroTermsVanish D) := by
  constructor
  · intro h hH u u' huu t hr hG
    exact ((h hH).2.1 u u' t huu hr hG).1
  · intro h hH
    have hTg := data_T_ne_g hH.1.2.1
    exact ⟨fun u u' t ht => normal_form_of_identity_cell X hTg t ht,
      fun u u' t huu hr hG => ⟨h hH u u' huu t hr hG, fun hA => off_diagonal_amplitude_zero X hA huu t hr hG⟩,
      fun hA u t ht => amplitude_scalar_on_diagonal X hTg hA t ht⟩

theorem off_diagonal_vanishing_of_tie (hT : ATie X) (hA : LatticeIndexAndWeightTheory.AmpOK X) : LatticeIndexAndWeightTheory.Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0 :=
  (first_statement_iff_off_relation X large₂ C' Cl Cg cb Cu cT CT C0).2 (fun _ => off_relation_of_tie X hT hA)

theorem firstStatement_of_admissible (hT : ATie X) : LatticeIndexAndWeightTheory.IntegralityFromMetric D large₂ X C' Cl Cg cb Cu cT CT C0 :=
  fun _ hA => off_diagonal_vanishing_of_tie X large₂ C' Cl Cg cb Cu cT CT C0 hT hA

theorem second_bound_of_tie (h11 : LatticeIndexAndWeightTheory.adm11 D large₂ C' Cl Cg cb Cu cT CT C0) (hT : ATie X) (hA : LatticeIndexAndWeightTheory.AmpOK X) :
    LatticeIndexAndWeightTheory.PairsWithFiniteGroup D large₂ C' Cl Cg cb Cu cT CT C0 :=
  LatticeIndexAndWeightTheory.pairs_with_finite_group_of_parameters_bounds h11 (off_diagonal_vanishing_of_tie X large₂ C' Cl Cg cb Cu cT CT C0 hT hA)

theorem third_statement_of_tie (h4 : NonGenericAndKTwoTheorems.ArchimedeanSignatureMatching D large₂ C' Cl Cg cb Cu cT CT C0) (hT : ATie X) (hA : LatticeIndexAndWeightTheory.AmpOK X) :
    NonGenericAndKTwoTheorems.PointsLemma D large₂ C' Cl Cg cb Cu cT CT C0 :=
  kernel_third_part_of_relevant_case D large₂ C' Cl Cg cb Cu cT CT C0 h4 (fun _ => off_relation_of_tie X hT hA)

end Rec

section Fam

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))

theorem first_statement_family_of_ties (hT : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ATie (At x hx i)) (hA : LatticeIndexAndWeightTheory.AmpF Fm At) :
    LatticeIndexAndWeightTheory.Conclusion1Family Fm At := fun Cg cb Cu cT CT C0 =>
  ⟨0, fun x _ i hx => off_diagonal_vanishing_of_tie (At x hx i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 (hT x hx i) (hA x hx i)⟩

theorem first_statement_family_of_tie (hT : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ATie (At x hx i)) : LatticeIndexAndWeightTheory.FamilyGlobalDerivation Fm At :=
  fun _ hA => first_statement_family_of_ties Fm At hT hA

end Fam

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : TermTie D)

def PFHost (D : D7) : Prop :=
  ∀ (l : ℕ) (x : D.host.E),
    ((Nloc (ddS D) D.R.rS l x : ℚ) : ℝ) = ∏ τ : D.what₂.Tau, absReal D.host.rdE (embS D τ) D.R.rS l x ^ 2

theorem rank_index_bounds (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    {u : D.what₂.Word} (t : D.s.Term u u) (h : LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t) :
    1 ≤ LatticeIndexAndWeightTheory.jOf X t ∧ LatticeIndexAndWeightTheory.jOf X t ≤ D.R.rS ∧ Dl (X.fl t).fl (X.fl' t).fl (LatticeIndexAndWeightTheory.jOf X t) ≠ 0 := by
  obtain ⟨j, hj, c, hN⟩ := nf_core X t h.1 h.2.1
  have hfin := hN.1.2.1
  rw [nf_II] at hfin
  have hjo : LatticeIndexAndWeightTheory.jOf X t = j := by
    unfold LatticeIndexAndWeightTheory.jOf LatticeIndexAndWeightTheory.Iof
    rw [hfin]; omega
  rw [hjo]
  exact ⟨nf_j_pos X hTg t h.1 h.2.2 j hj c hN, hj, (nf_gen _ _ _ _ j hj c hN).2.2.2.1⟩

theorem j_mem_ends (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    {u : D.what₂.Word} (t : D.s.Term u u) (h : LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t) : LatticeIndexAndWeightTheory.jOf X t ∈ LatticeIndexAndWeightTheory.ends X t := by
  obtain ⟨h1, -, h3⟩ := rank_index_bounds X hTg t h
  classical
  unfold LatticeIndexAndWeightTheory.ends blockEnds
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨h1, le_rfl⟩, h3⟩

theorem two_pow_le_height_bound (b CH C : ℝ) (r m f : ℕ) (hb : 2 ≤ b) (hm : 2 * r + 2 = m) (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C) :
    (2 * b ^ (CH * (m : ℝ))) ^ (4 * r * f) ≤ Hb b C m f := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have e1 : 2 * b ^ (CH * (m : ℝ)) ≤ b ^ (CH * (m : ℝ) + 1) := by
    rw [Real.rpow_add_one hb0.ne']
    have hp := Real.rpow_pos_of_pos hb0 (CH * (m : ℝ))
    nlinarith
  have e2 : (2 * b ^ (CH * (m : ℝ))) ^ (4 * r * f) ≤ (b ^ (CH * (m : ℝ) + 1)) ^ (4 * r * f) :=
    pow_le_pow_left₀ (by positivity) e1 _
  have e3 : (b ^ (CH * (m : ℝ) + 1)) ^ (4 * r * f) = b ^ ((CH * (m : ℝ) + 1) * ((4 * r * f : ℕ) : ℝ)) :=
    (Real.rpow_mul_natCast hb0.le _ _).symm
  refine e2.trans (e3.le.trans ?_)
  unfold Hb
  refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
  have hmr : (m : ℝ) = 2 * (r : ℝ) + 2 := by rw [← hm]; push_cast; ring
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg _
  push_cast
  have h1 : CH * (m : ℝ) + 1 ≤ (CH + 1) * (m : ℝ) := by nlinarith
  have h2 : 4 * (r : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  calc (CH * (m : ℝ) + 1) * (4 * (r : ℝ) * f) ≤ ((CH + 1) * (m : ℝ)) * (2 * (m : ℝ) * f) := by
        apply mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hf0) (by positivity) (by positivity)
    _ = 2 * (CH + 1) * (m : ℝ) ^ 2 * f := by ring
    _ ≤ C * (m : ℝ) ^ 2 * f := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) hf0

theorem end_norm_bound (hPF : PFHost D) (large₂ : SizeData₂ D) (CH C : ℝ) (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C) {u : D.what₂.Word}
    (t : D.s.Term u u) (l : ℕ) (hl : l ∈ LatticeIndexAndWeightTheory.ends X t) :
    LatticeIndexAndWeightTheory.NDl X t l ≤ Hb large₂.sc.b C D.R.m D.R.f * ∏ τ, LatticeIndexAndWeightTheory.sg X t (large₂.sc.b ^ (CH * (D.R.m : ℝ))) τ ^ 2 := by
  have hb : 2 ≤ large₂.sc.b := by
    have h1 : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
    have h2 : large₂.sc.L + 1 ≤ Real.exp large₂.sc.L := Real.add_one_le_exp _
    show 2 ≤ Real.exp large₂.sc.L
    linarith
  have hm : 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨a, ha⟩ := D.R.m_even
    have := D.R.two_le_m
    simp only [Ranks.rS]; omega
  have hH1 : 1 ≤ large₂.sc.b ^ (CH * (D.R.m : ℝ)) := Real.one_le_rpow (by linarith) (by positivity)
  have hrd : 0 ≤ D.host.rdE := by unfold Host.rdE; positivity
  unfold LatticeIndexAndWeightTheory.NDl
  rw [hPF]
  refine Formalism.HermitianLatticeCounting.Final.S6.normSgBound D.what₂.Tau D.R.rS D.R.f _ _ (large₂.sc.b ^ (CH * (D.R.m : ℝ))) _ D.what₂.card_Tau
    (by linarith) (two_pow_le_height_bound _ CH C _ _ _ hb hm hCH hC) (fun τ => ?_) (fun τ => ?_) (fun τ => ?_)
  · unfold absReal; positivity
  · exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  · exact (Finset.le_fold_max _).2 (Or.inr ⟨l, hl, le_rfl⟩)

def AmplitudeBoundWithoutNorms (large₂ : SizeData₂ D) (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (CH Cs C : ℝ) : Prop :=
  ∀ u : D.what₂.Word, LatticeIndexAndWeightTheory.TieOK X u → ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t →
    Real.sqrt (hsNormSq (X.Jt t)) ≤ Real.sqrt (Module.finrank ℂ (X.Hpi u) : ℝ) *
      (om u t * (C / D.R.k) ^ ((LatticeIndexAndWeightTheory.jOf X t : ℝ) * ((D.R.k : ℝ) - 1 - LatticeIndexAndWeightTheory.jOf X t) * D.R.f) *
        LatticeIndexAndWeightTheory.DelJ X t ^ (-(((D.R.k : ℝ) - 1 - LatticeIndexAndWeightTheory.jOf X t) / 2)) *
        Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        ∏ τ, LatticeIndexAndWeightTheory.sg X t (large₂.sc.b ^ (CH * (D.R.m : ℝ))) τ ^ (-(Cs * D.R.k)))

theorem second_statement_iff_amplitude (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1) (hPF : PFHost D)
    (large₂ : SizeData₂ D) (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (CH Cs C : ℝ) (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C) :
    LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C ↔ AmplitudeBoundWithoutNorms X large₂ om CH Cs C :=
  ⟨fun h u hu t ht => (h u hu t ht).1, fun h u hu t ht =>
    ⟨h u hu t ht, end_norm_bound X hPF large₂ CH C hCH hC t _ (j_mem_ends X hTg t ht), fun l hl => end_norm_bound X hPF large₂ CH C hCH hC t l hl⟩⟩

end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma
open scoped nonZeroDivisors NumberField

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def pfEmb : D.what₂.Tau ⊕ D.what₂.Tau → (D.host.E →+* ℂ)
  | Sum.inl τ => embS D τ
  | Sum.inr τ => (starRingEnd ℂ).comp (embS D τ)

theorem pf_conj_conj (φ : D.host.E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp φ) = φ := by
  ext x; simp

theorem pf_mem (τ : D.what₂.Tau) : embS D τ ∈ D.host.cmType :=
  ((factEmb D.R D.host).2 _).2 (D.eTau τ).2

theorem pf_inj {τ τ' : D.what₂.Tau} (h : embS D τ = embS D τ') : τ = τ' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem pf_bij : Function.Bijective (pfEmb D) := by
  have P1 := D.host.der.cmType.1
  have hsur : ∀ φ ∈ D.host.cmType, ∃ τ, embS D τ = φ := by
    intro φ hφ
    obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 φ
    have hg := ((factEmb D.R D.host).2 g).1 hφ
    refine ⟨D.eTau.symm ⟨g, hg⟩, ?_⟩
    unfold embS
    rw [Equiv.apply_symm_apply]
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg Sum.inl (pf_inj D h)
    · have h' : embS D τ = (starRingEnd ℂ).comp (embS D τ') := h
      exact absurd (h' ▸ pf_mem D τ) ((P1 _).1 (pf_mem D τ'))
    · have h' : (starRingEnd ℂ).comp (embS D τ) = embS D τ' := h
      exact absurd (h'.symm ▸ pf_mem D τ') ((P1 _).1 (pf_mem D τ))
    · have h' : embS D τ = embS D τ' := by
        have := congrArg (fun φ => (starRingEnd ℂ).comp φ) h
        simpa only [pfEmb, pf_conj_conj] using this
      exact congrArg Sum.inr (pf_inj D h')
  · intro φ
    by_cases hφ : φ ∈ D.host.cmType
    · obtain ⟨τ, rfl⟩ := hsur φ hφ
      exact ⟨Sum.inl τ, rfl⟩
    · have h2 : (starRingEnd ℂ).comp φ ∈ D.host.cmType := by
        rw [P1, pf_conj_conj]; exact hφ
      obtain ⟨τ, hτ⟩ := hsur _ h2
      refine ⟨Sum.inr τ, ?_⟩
      show (starRingEnd ℂ).comp (embS D τ) = φ
      rw [hτ, pf_conj_conj]

theorem pf_norm (x : D.host.E) : ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ∏ τ : D.what₂.Tau, ‖embS D τ x‖ ^ 2 := by
  rw [Formalism.MainNotions.LatticeGluingRadicals.j_norm_prod, ← (pf_bij D).prod_comp (fun φ : D.host.E →+* ℂ => ‖φ x‖), Fintype.prod_sum_type,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  have h : ‖pfEmb D (Sum.inr τ) x‖ = ‖embS D τ x‖ := by
    show ‖(starRingEnd ℂ) (embS D τ x)‖ = _
    exact RCLike.norm_conj _
  rw [h, sq]
  rfl

theorem pf_rd_pos : 0 < D.host.rdE := by
  unfold Host.rdE
  have h : (NumberField.discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
  positivity

theorem PFHost_of_discr (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) : PFHost D := by
  intro l x
  have hdd : ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = (D.host.rdE ^ D.R.f) ^ 2 := szf_normDD D hd
  have hrd := pf_rd_pos D
  unfold Nloc absReal
  rw [map_mul, map_zpow₀, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, Rat.cast_zpow, hdd, pf_norm]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, D.what₂.card_Tau]
  congr 1
  have e1 : (D.host.rdE ^ D.R.f) ^ 2 = D.host.rdE ^ ((2 * D.R.f : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, ← pow_mul, mul_comm]
  have e2 : ((D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ)))) ^ 2) ^ D.R.f =
      D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ)) * ((2 * D.R.f : ℕ) : ℝ)) := by
    rw [← pow_mul, Real.rpow_mul_natCast hrd.le]
  rw [e1, e2, ← Real.rpow_intCast, ← Real.rpow_mul hrd.le]
  congr 1
  push_cast
  ring

theorem PFHost_of_data {C0 : ℝ} (h : StandingNumericalData D C0) : PFHost D := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := h
  exact PFHost_of_discr D d13

variable {D} (X : TermTie D)

theorem second_statement_iff_amplitude_form (large₂ : SizeData₂ D) (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (C' Cl Cg cb Cu cT CT C0 CH Cs C : ℝ)
    (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C) :
    LatticeIndexAndWeightTheory.Conclusion2 D large₂ X om C' Cl Cg cb Cu cT CT C0 CH Cs C ↔
      (LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → AmplitudeBoundWithoutNorms X large₂ om CH Cs C) :=
  ⟨fun h hH => (second_statement_iff_amplitude X (data_T_ne_g hH.1.2.1) (PFHost_of_data D hH.1.2.1) large₂ om CH Cs C hCH hC).1 (h hH),
    fun h hH => (second_statement_iff_amplitude X (data_T_ne_g hH.1.2.1) (PFHost_of_data D hH.1.2.1) large₂ om CH Cs C hCH hC).2 (h hH)⟩

theorem amplitude_norm_bounds (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 CH C : ℝ) (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C)
    (hH : LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0) {u : D.what₂.Word} (t : D.s.Term u u) (ht : LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t) :
    LatticeIndexAndWeightTheory.DelJ X t ≤ Hb large₂.sc.b C D.R.m D.R.f * ∏ τ, LatticeIndexAndWeightTheory.sg X t (large₂.sc.b ^ (CH * (D.R.m : ℝ))) τ ^ 2 ∧
    ∀ l ∈ LatticeIndexAndWeightTheory.ends X t, LatticeIndexAndWeightTheory.NDl X t l ≤ Hb large₂.sc.b C D.R.m D.R.f * ∏ τ, LatticeIndexAndWeightTheory.sg X t (large₂.sc.b ^ (CH * (D.R.m : ℝ))) τ ^ 2 :=
  ⟨end_norm_bound X (PFHost_of_data D hH.1.2.1) large₂ CH C hCH hC t _ (j_mem_ends X (data_T_ne_g hH.1.2.1) t ht),
    fun l hl => end_norm_bound X (PFHost_of_data D hH.1.2.1) large₂ CH C hCH hC t l hl⟩

end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

open NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem chk_rS_pos (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) :
    1 ≤ D.R.rS := by
  obtain ⟨-, -, a3, -, a5, -⟩ := h
  by_contra hc
  have h0 : D.R.rS = 0 := by omega
  rw [h0] at a5
  simp only [Nat.cast_zero, Real.sqrt_zero] at a5
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have h16 : 16 ≤ D.R.f := le_trans (by calc 16 = 2 ^ 4 := by norm_num
    _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm 4) a3
  have hf : (1 : ℝ) < D.R.f := by exact_mod_cast (by omega : 1 < D.R.f)
  have := Real.log_pos hf
  linarith

theorem chk_cf_le (f : ℕ) (hf : 2 ≤ f) : 1 + Real.logb 2 (2 * f) ≤ 5 * Real.log f := by
  have hf' : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log f := Real.log_le_log (by norm_num) hf'
  have h69 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have e : Real.logb 2 (2 * f) = 1 + Real.log f / Real.log 2 := by
    unfold Real.logb
    rw [Real.log_mul (by norm_num) (by positivity)]
    field_simp
  rw [e]
  have h3 : Real.log f / Real.log 2 ≤ Real.log f / 0.6931471803 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) h69.le
  have h4 : Real.log f / 0.6931471803 ≤ 1.45 * Real.log f := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  nlinarith

theorem chk_H_absorb (b cT C T : ℝ) (m f : ℕ) (hb : 1 < b) (hcT : 0 < cT) (hC : 0 ≤ C)
    (hT : b ^ (cT * (m : ℝ)) ≤ T) : Hb b C m f ≤ (T ^ f) ^ (C * m / cT) := by
  have hb0 : 0 < b := by linarith
  have h1 : (b ^ (cT * (m : ℝ))) ^ f ≤ T ^ f := pow_le_pow_left₀ (Real.rpow_nonneg hb0.le _) hT f
  have h2 : ((b ^ (cT * (m : ℝ))) ^ f) ^ (C * m / cT) ≤ (T ^ f) ^ (C * m / cT) :=
    Real.rpow_le_rpow (by positivity) h1 (by positivity)
  refine le_trans (le_of_eq ?_) h2
  have e1 : (b ^ (cT * (m : ℝ))) ^ f = b ^ (cT * (m : ℝ) * f) := by
    rw [← Real.rpow_natCast (b ^ (cT * (m : ℝ))) f, ← Real.rpow_mul hb0.le]
  unfold Hb
  rw [e1, ← Real.rpow_mul hb0.le]
  congr 1
  field_simp

theorem chk_SC_mono (C Cb A b NT de X : ℝ) (m f k s : ℕ) (hC : 0 ≤ C) (hCA : C ≤ A) (hCbA : Cb ≤ A) (hb : 1 ≤ b)
    (hd : 1 ≤ de * NT) (hf : 1 ≤ f) (hX : 0 ≤ X) :
    C ^ (s * k * f) * Hb b C m f ^ C * X * (de * NT) ^ (Cb * s + Cb * Real.log f) ≤
      A ^ (s * k * f) * Hb b A m f ^ A * X * (de * NT) ^ (A * s + A * Real.log f) := by
  have hb0 : 0 ≤ b := by linarith
  have hA : 0 ≤ A := le_trans hC hCA
  have hlf : 0 ≤ Real.log f := Real.log_nonneg (by exact_mod_cast hf)
  have h1 : C ^ (s * k * f) ≤ A ^ (s * k * f) := pow_le_pow_left₀ hC hCA _
  have h2 : Hb b C m f ^ C ≤ Hb b A m f ^ A := by
    unfold Hb
    rw [← Real.rpow_mul hb0, ← Real.rpow_mul hb0]
    refine Real.rpow_le_rpow_of_exponent_le hb ?_
    have e0 : 0 ≤ (m : ℝ) ^ 2 * f := by positivity
    have e1 : C * C ≤ A * A := mul_le_mul hCA hCA hC hA
    calc C * (m : ℝ) ^ 2 * f * C = (C * C) * ((m : ℝ) ^ 2 * f) := by ring
      _ ≤ (A * A) * ((m : ℝ) ^ 2 * f) := mul_le_mul_of_nonneg_right e1 e0
      _ = A * (m : ℝ) ^ 2 * f * A := by ring
  have h3 : (de * NT) ^ (Cb * s + Cb * Real.log f) ≤ (de * NT) ^ (A * s + A * Real.log f) := by
    refine Real.rpow_le_rpow_of_exponent_le hd ?_
    have : Cb * ((s : ℝ) + Real.log f) ≤ A * ((s : ℝ) + Real.log f) :=
      mul_le_mul_of_nonneg_right hCbA (by positivity)
    linarith
  have p1 : 0 ≤ Hb b C m f ^ C := Real.rpow_nonneg (Real.rpow_nonneg hb0 _) _
  have p2 : 0 ≤ (de * NT) ^ (Cb * s + Cb * Real.log f) := Real.rpow_nonneg (by linarith) _
  have p3 : 0 ≤ A ^ (s * k * f) := pow_nonneg hA _
  have p4 : 0 ≤ Hb b A m f ^ A := Real.rpow_nonneg (Real.rpow_nonneg hb0 _) _
  exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 p1 p3) hX) h3 p2
    (mul_nonneg (mul_nonneg p3 p4) hX)

theorem chk_SC_top (C A b NT de X : ℝ) (m f k : ℕ) (hC : 0 ≤ C) (hCA : 3 * C ≤ A) (hb : 1 ≤ b) (hde : 1 ≤ de)
    (hNT : 1 ≤ NT) (hk : 2 ≤ k) (hf : 1 ≤ f) (hX : 0 ≤ X)
    (hbig : C * k * b ^ (C ^ 2 * (m : ℝ) ^ 2) ≤ A ^ (k - 1)) :
    X * (de * NT) ^ (C * ((k - 1 : ℕ) : ℝ) + C * Real.log f) * ((C * k) ^ (k * f) * (Hb b C m f * NT) ^ (C * k)) ≤
      A ^ ((k - 1) * k * f) * Hb b A m f ^ A * X * (de * NT) ^ (A * ((k - 1 : ℕ) : ℝ) + A * Real.log f) := by
  have hb0 : 0 ≤ b := by linarith
  have hA : 0 ≤ A := by linarith
  have hlf : 0 ≤ Real.log f := Real.log_nonneg (by exact_mod_cast hf)
  have hNT0 : 0 ≤ NT := by linarith
  have hd : 1 ≤ de * NT := by nlinarith
  have hHb : 0 ≤ Hb b C m f := Real.rpow_nonneg hb0 _
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk

  have e1 : Hb b C m f ^ (C * k) = (b ^ (C ^ 2 * (m : ℝ) ^ 2)) ^ (k * f) := by
    unfold Hb
    rw [← Real.rpow_natCast (b ^ (C ^ 2 * (m : ℝ) ^ 2)) (k * f), ← Real.rpow_mul hb0, ← Real.rpow_mul hb0]
    congr 1
    push_cast
    ring
  have e2 : (C * k) ^ (k * f) * Hb b C m f ^ (C * k) ≤ A ^ ((k - 1) * k * f) := by
    rw [e1, ← mul_pow]
    calc (C * k * b ^ (C ^ 2 * (m : ℝ) ^ 2)) ^ (k * f) ≤ (A ^ (k - 1)) ^ (k * f) :=
          pow_le_pow_left₀ (mul_nonneg (mul_nonneg hC (by positivity)) (Real.rpow_nonneg hb0 _)) hbig _
      _ = A ^ ((k - 1) * k * f) := by rw [← pow_mul]; congr 1; ring

  have e3 : NT ^ (C * k) ≤ (de * NT) ^ (C * k) :=
    Real.rpow_le_rpow hNT0 (by nlinarith) (by positivity)
  have e4 : (de * NT) ^ (C * ((k - 1 : ℕ) : ℝ) + C * Real.log f) * (de * NT) ^ (C * k) ≤
      (de * NT) ^ (A * ((k - 1 : ℕ) : ℝ) + A * Real.log f) := by
    rw [← Real.rpow_add (by linarith)]
    refine Real.rpow_le_rpow_of_exponent_le hd ?_
    rw [hk1]
    have h5 : C * Real.log f ≤ A * Real.log f := mul_le_mul_of_nonneg_right (by linarith) hlf
    have h6 : 3 * C * ((k : ℝ) - 1) ≤ A * ((k : ℝ) - 1) := mul_le_mul_of_nonneg_right hCA (by linarith)
    nlinarith
  have e5 : 1 ≤ Hb b A m f ^ A := by
    unfold Hb
    rw [← Real.rpow_mul hb0]
    exact Real.one_le_rpow hb (by positivity)
  have p0 : 0 ≤ (de * NT) ^ (C * ((k - 1 : ℕ) : ℝ) + C * Real.log f) := Real.rpow_nonneg (by linarith) _
  have p1 : 0 ≤ A ^ ((k - 1) * k * f) := pow_nonneg hA _
  rw [Real.mul_rpow hHb hNT0]
  calc X * (de * NT) ^ (C * ((k - 1 : ℕ) : ℝ) + C * Real.log f) *
        ((C * k) ^ (k * f) * (Hb b C m f ^ (C * k) * NT ^ (C * k)))
      = ((C * k) ^ (k * f) * Hb b C m f ^ (C * k)) * X *
          ((de * NT) ^ (C * ((k - 1 : ℕ) : ℝ) + C * Real.log f) * NT ^ (C * k)) := by ring
    _ ≤ A ^ ((k - 1) * k * f) * X *
          ((de * NT) ^ (C * ((k - 1 : ℕ) : ℝ) + C * Real.log f) * (de * NT) ^ (C * k)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right e2 hX) (mul_le_mul_of_nonneg_left e3 p0)
          (mul_nonneg p0 (Real.rpow_nonneg hNT0 _)) (mul_nonneg p1 hX)
    _ ≤ A ^ ((k - 1) * k * f) * X * (de * NT) ^ (A * ((k - 1 : ℕ) : ℝ) + A * Real.log f) :=
        mul_le_mul_of_nonneg_left e4 (mul_nonneg p1 hX)
    _ ≤ A ^ ((k - 1) * k * f) * Hb b A m f ^ A * X * (de * NT) ^ (A * ((k - 1 : ℕ) : ℝ) + A * Real.log f) := by
        have q : 0 ≤ A ^ ((k - 1) * k * f) * X * (de * NT) ^ (A * ((k - 1 : ℕ) : ℝ) + A * Real.log f) :=
          mul_nonneg (mul_nonneg p1 hX) (Real.rpow_nonneg (by linarith) _)
        calc A ^ ((k - 1) * k * f) * X * (de * NT) ^ (A * ((k - 1 : ℕ) : ℝ) + A * Real.log f)
            = (A ^ ((k - 1) * k * f) * X * (de * NT) ^ (A * ((k - 1 : ℕ) : ℝ) + A * Real.log f)) * 1 := by ring
          _ ≤ (A ^ ((k - 1) * k * f) * X * (de * NT) ^ (A * ((k - 1 : ℕ) : ℝ) + A * Real.log f)) * Hb b A m f ^ A :=
              mul_le_mul_of_nonneg_left e5 q
          _ = _ := by ring

theorem chk_kexp (n : ℕ) : ((n : ℝ) + 5) * Real.exp ((n : ℝ) + 5) ≤ 40 ^ (n + 3) := by
  have h3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  induction n with
  | zero =>
    have e5 : Real.exp ((0 : ℕ) + 5 : ℝ) = Real.exp 1 ^ 5 := by
      rw [Real.exp_one_pow]; norm_num
    rw [e5]
    have : Real.exp 1 ^ 5 ≤ 3 ^ 5 := pow_le_pow_left₀ (Real.exp_pos 1).le h3 5
    norm_num at this ⊢
    linarith
  | succ n ih =>
    have e : Real.exp (((n + 1 : ℕ) : ℝ) + 5) = Real.exp ((n : ℝ) + 5) * Real.exp 1 := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [e]
    have hp : 0 < Real.exp ((n : ℝ) + 5) := Real.exp_pos _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h6 : (((n + 1 : ℕ) : ℝ) + 5) ≤ 2 * ((n : ℝ) + 5) := by push_cast; linarith
    calc (((n + 1 : ℕ) : ℝ) + 5) * (Real.exp ((n : ℝ) + 5) * Real.exp 1)
        ≤ (2 * ((n : ℝ) + 5)) * (Real.exp ((n : ℝ) + 5) * 3) :=
          mul_le_mul h6 (mul_le_mul_of_nonneg_left h3 hp.le) (by positivity) (by positivity)
      _ = 6 * (((n : ℝ) + 5) * Real.exp ((n : ℝ) + 5)) := by ring
      _ ≤ 6 * 40 ^ (n + 3) := by linarith
      _ ≤ 40 ^ (n + 1 + 3) := by
          have hpos : (0 : ℝ) < 40 ^ (n + 3) := by positivity
          have e' : (40 : ℝ) ^ (n + 1 + 3) = 40 ^ (n + 3) * 40 := by
            rw [show n + 1 + 3 = (n + 3) + 1 from by ring]; exact pow_succ _ _
          rw [e']
          linarith

theorem chk_big (C A Cl L : ℝ) (m k : ℕ) (hC : 0 ≤ C) (hCA : C ≤ A) (hA : 40 ≤ A) (hCl : C ^ 2 ≤ Cl) (hL : 0 ≤ L)
    (hk : Cl * ((m : ℝ) ^ 2 * L) ≤ k) (hk5 : 5 ≤ k) :
    C * k * Real.exp L ^ (C ^ 2 * (m : ℝ) ^ 2) ≤ A ^ (k - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 5 := ⟨k - 5, by omega⟩
  have e1 : Real.exp L ^ (C ^ 2 * (m : ℝ) ^ 2) = Real.exp (L * (C ^ 2 * (m : ℝ) ^ 2)) := (Real.exp_mul _ _).symm
  have e2 : L * (C ^ 2 * (m : ℝ) ^ 2) ≤ ((n + 5 : ℕ) : ℝ) := by
    have : C ^ 2 * ((m : ℝ) ^ 2 * L) ≤ Cl * ((m : ℝ) ^ 2 * L) := mul_le_mul_of_nonneg_right hCl (by positivity)
    calc L * (C ^ 2 * (m : ℝ) ^ 2) = C ^ 2 * ((m : ℝ) ^ 2 * L) := by ring
      _ ≤ _ := le_trans this hk
  have e3 : Real.exp (L * (C ^ 2 * (m : ℝ) ^ 2)) ≤ Real.exp ((n : ℝ) + 5) := by
    refine Real.exp_le_exp.2 (le_trans e2 (le_of_eq ?_)); push_cast; ring
  have e4 : (40 : ℝ) ^ (n + 3) ≤ A ^ (n + 3) := pow_le_pow_left₀ (by norm_num) hA _
  have hA0 : 0 ≤ A := by linarith
  rw [e1, show n + 5 - 1 = (n + 3) + 1 from by omega, pow_succ]
  have hk' : ((n + 5 : ℕ) : ℝ) = (n : ℝ) + 5 := by push_cast; ring
  rw [hk']
  calc C * ((n : ℝ) + 5) * Real.exp (L * (C ^ 2 * (m : ℝ) ^ 2))
      ≤ C * ((n : ℝ) + 5) * Real.exp ((n : ℝ) + 5) := mul_le_mul_of_nonneg_left e3 (by positivity)
    _ = (((n : ℝ) + 5) * Real.exp ((n : ℝ) + 5)) * C := by ring
    _ ≤ A ^ (n + 3) * A := mul_le_mul (le_trans (chk_kexp n) e4) hCA hC (by positivity)

theorem fourth_statement_middle (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C c : ℝ)
    (hH : Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 A)
    (h1 : UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u C' Cl Cg cb Cu cT CT C0 A C)
    (hX : UnitaryVolumeMass.stX D large₂ u u C' Cl Cg cb Cu cT CT C0 A C c)
    (hC : 0 ≤ C) (hc0 : 0 ≤ c) (hc : c ≤ D.R.k * D.host.v) (hkv : 0 < (D.R.k : ℝ) * D.host.v)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)
    (Λ : LatV D) (hΛ : IsRowLat D F0 Λ)
    (reps : Finset (Submodule (𝓞 D.host.E) (D.sp.X 0).V))
    (hr : Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ (lf D F0)) reps)
    (hMass : Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) =
      ∑ L' ∈ reps, ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℕ) : ℝ)⁻¹)
    (s : ℕ) (hs2 : 2 ≤ s) (hsk : s ≤ D.R.k - 2) (de : ℕ) (hde : 1 ≤ de) :
    (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ *
        (cntPrim (D.sp.X 0).hT L' (D.R.k - s) de : ℝ≥0∞)) ≤
      (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹) *
        ENNReal.ofReal (C ^ (s * D.R.k * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ C *
          ((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (C * s + C * Real.log D.R.f)) := by
  have hb0 : 0 ≤ large₂.sc.b := (Real.exp_pos _).le
  have hNT : 0 ≤ NT D u := by unfold NT; positivity
  have hHb : 0 ≤ Hb large₂.sc.b C D.R.m D.R.f := Real.rpow_nonneg hb0 _
  have k1 := h1 hH F0 he hz Λ hΛ reps hr s hs2 (by omega) de hde (Hb large₂.sc.b C D.R.m D.R.f) le_rfl
  have k2 := (hX hH).2 s hs2 hsk (Hb large₂.sc.b C D.R.m D.R.f)
  refine le_trans k1 ?_
  have hm0 : 0 ≤ Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
    rw [hMass]; exact Finset.sum_nonneg (fun _ _ => by positivity)
  rw [ENNReal.ofReal_mul hm0, hMass, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  have hq : (c / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) ≤ 1 :=
    pow_le_one₀ (div_nonneg hc0 hkv.le) ((div_le_one hkv).2 hc)
  have hP : 0 ≤ Hb large₂.sc.b C D.R.m D.R.f ^ C * C ^ (s * D.R.k * D.R.f) :=
    mul_nonneg (Real.rpow_nonneg hHb _) (pow_nonneg hC _)
  have k3 : XiS D u (Hb large₂.sc.b C D.R.m D.R.f) C s ≤ Hb large₂.sc.b C D.R.m D.R.f ^ C * C ^ (s * D.R.k * D.R.f) :=
    le_trans k2 (mul_le_of_le_one_right hP hq)
  have hQ : 0 ≤ ((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (C * s + C * Real.log D.R.f) :=
    mul_nonneg (pow_nonneg (div_nonneg (by positivity) hNT) _) (Real.rpow_nonneg (mul_nonneg (by positivity) hNT) _)
  calc ((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (C * s + C * Real.log D.R.f) *
        XiS D u (Hb large₂.sc.b C D.R.m D.R.f) C s
      ≤ ((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (C * s + C * Real.log D.R.f) *
        (Hb large₂.sc.b C D.R.m D.R.f ^ C * C ^ (s * D.R.k * D.R.f)) := mul_le_mul_of_nonneg_left k3 hQ
    _ = _ := by ring

theorem first_loop_bound_use (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ)
    (hH : Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 A)
    (h1 : UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u C' Cl Cg cb Cu cT CT C0 A C)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)
    (Λ : LatV D) (hΛ : IsRowLat D F0 Λ)
    (reps : Finset (Submodule (𝓞 D.host.E) (D.sp.X 0).V))
    (hr : Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ (lf D F0)) reps)
    (hMass : Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) =
      ∑ L' ∈ reps, ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℕ) : ℝ)⁻¹)
    (s : ℕ) (hs2 : 2 ≤ s) (hsk : s ≤ D.R.k) (de : ℕ) (hde : 1 ≤ de) (B : ℝ)
    (hB : ((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (C * s + C * Real.log D.R.f) *
      XiS D u (Hb large₂.sc.b C D.R.m D.R.f) C s ≤ B) :
    (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ *
        (cntPrim (D.sp.X 0).hT L' (D.R.k - s) de : ℝ≥0∞)) ≤
      (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹) * ENNReal.ofReal B := by
  have k1 := h1 hH F0 he hz Λ hΛ reps hr s hs2 hsk de hde (Hb large₂.sc.b C D.R.m D.R.f) le_rfl
  refine le_trans k1 ?_
  have hm0 : 0 ≤ Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
    rw [hMass]; exact Finset.sum_nonneg (fun _ _ => by positivity)
  rw [ENNReal.ofReal_mul hm0, hMass, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hB) _

def chk_SCone (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (A : ℝ) : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
    ∀ reps : Finset (Submodule (𝓞 D.host.E) (D.sp.X 0).V),
      Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ (lf D F0)) reps → ∀ de : ℕ, 1 ≤ de →
      (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ *
          (cntPrim (D.sp.X 0).hT L' (D.R.k - 1) de : ℝ≥0∞)) ≤
        (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹) *
          ENNReal.ofReal (A ^ (1 * D.R.k * D.R.f) * Hb large₂.sc.b A D.R.m D.R.f ^ A *
            ((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (A * (1 : ℕ) + A * Real.log D.R.f))

def chk_MassSum (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
    ∀ reps : Finset (Submodule (𝓞 D.host.E) (D.sp.X 0).V),
      Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ (lf D F0)) reps →
      Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) =
        ∑ L' ∈ reps, ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℕ) : ℝ)⁻¹

theorem fourth_statement_of_loops (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Aa C CX c A : ℝ)
    (hS5 : LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u, Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 Aa)
    (h1 : ∀ u, UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u C' Cl Cg cb Cu cT CT C0 Aa C)
    (hX : ∀ u, UnitaryVolumeMass.stX D large₂ u u C' Cl Cg cb Cu cT CT C0 Aa CX c)
    (hC : 0 ≤ C) (hCA : 3 * C ≤ A) (hCX : 0 ≤ CX) (hCXA : CX ≤ A) (hc0 : 0 ≤ c) (hc : c ≤ D.R.k * D.host.v) (hkv : 0 < (D.R.k : ℝ) * D.host.v)
    (hbig : C * D.R.k * large₂.sc.b ^ (C ^ 2 * (D.R.m : ℝ) ^ 2) ≤ A ^ (D.R.k - 1))
    (hM : ∀ u, chk_MassSum D u)
    (hone : LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u, chk_SCone D large₂ u A) :
    LatticeIndexAndWeightTheory.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A := by
  intro hH u F0 he hz Λ hΛ reps hr s hs1 hsk de hde
  have hb : 1 ≤ large₂.sc.b := (sc_one_lt_b large₂).le
  have hb0 : 0 ≤ large₂.sc.b := by linarith
  have hT1 : (1 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hNT : 1 ≤ NT D u := by unfold NT; exact one_le_pow₀ hT1
  have hde' : (1 : ℝ) ≤ de := by exact_mod_cast hde
  have hf : 1 ≤ D.R.f := by have := two_le_fR D; exact_mod_cast (by linarith : (1 : ℝ) ≤ D.R.f)
  have hX0 : 0 ≤ ((de : ℝ) / NT D u) ^ D.R.k := pow_nonneg (div_nonneg (by linarith) (by linarith)) _
  have hCA' : C ≤ A := by linarith
  rcases Nat.lt_or_ge s 2 with h2 | h2
  · have hs : s = 1 := by omega
    subst hs
    exact hone hH u F0 he hz Λ hΛ reps hr de hde
  refine first_loop_bound_use D large₂ u C' Cl Cg cb Cu cT CT C0 Aa C (hS5 hH u) (h1 u) F0 he hz Λ hΛ reps hr
    (hM u F0 he hz Λ hΛ reps hr) s h2 hsk.le de hde _ ?_
  rcases Nat.lt_or_ge (D.R.k - 2) s with h3 | h3
  ·
    have hs : s = D.R.k - 1 := by omega
    subst hs
    have hXi : XiS D u (Hb large₂.sc.b C D.R.m D.R.f) C (D.R.k - 1) =
        (C * D.R.k) ^ (D.R.k * D.R.f) * (Hb large₂.sc.b C D.R.m D.R.f * NT D u) ^ (C * D.R.k) := by
      unfold XiS Xi
      rw [if_neg (by omega), if_pos (Or.inl rfl)]
    rw [hXi]
    exact chk_SC_top C A large₂.sc.b (NT D u) de _ D.R.m D.R.f D.R.k hC hCA hb hde' hNT (by omega) hf hX0 hbig
  ·
    have k2 := (hX u (hS5 hH u)).2 s h2 h3 (Hb large₂.sc.b C D.R.m D.R.f)
    have hXi : XiS D u (Hb large₂.sc.b C D.R.m D.R.f) C s = XiS D u (Hb large₂.sc.b C D.R.m D.R.f) CX s := by
      unfold XiS Xi
      rw [if_pos ⟨h2, h3⟩, if_pos ⟨h2, h3⟩]
    have hHb : 0 ≤ Hb large₂.sc.b CX D.R.m D.R.f := Real.rpow_nonneg hb0 _
    have hq : (c / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) ≤ 1 :=
      pow_le_one₀ (div_nonneg hc0 hkv.le) ((div_le_one hkv).2 hc)
    have hP : 0 ≤ Hb large₂.sc.b CX D.R.m D.R.f ^ CX * CX ^ (s * D.R.k * D.R.f) :=
      mul_nonneg (Real.rpow_nonneg hHb _) (pow_nonneg hCX _)
    have k3 : XiS D u (Hb large₂.sc.b C D.R.m D.R.f) C s ≤ Hb large₂.sc.b CX D.R.m D.R.f ^ CX * CX ^ (s * D.R.k * D.R.f) := by
      rw [hXi]; exact le_trans k2 (mul_le_of_le_one_right hP hq)
    have hQ : 0 ≤ ((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (C * s + C * Real.log D.R.f) :=
      mul_nonneg hX0 (Real.rpow_nonneg (by nlinarith) _)
    calc ((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (C * s + C * Real.log D.R.f) *
          XiS D u (Hb large₂.sc.b C D.R.m D.R.f) C s
        ≤ ((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (C * s + C * Real.log D.R.f) *
          (Hb large₂.sc.b CX D.R.m D.R.f ^ CX * CX ^ (s * D.R.k * D.R.f)) := mul_le_mul_of_nonneg_left k3 hQ
      _ = CX ^ (s * D.R.k * D.R.f) * Hb large₂.sc.b CX D.R.m D.R.f ^ CX * ((de : ℝ) / NT D u) ^ D.R.k *
          ((de : ℝ) * NT D u) ^ (C * s + C * Real.log D.R.f) := by ring
      _ ≤ _ := chk_SC_mono CX C A large₂.sc.b (NT D u) de _ D.R.m D.R.f D.R.k s hCX hCXA hCA' hb (by nlinarith) hf hX0

theorem chk_S5Hyp_self (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Aa : ℝ)
    (hH : LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0) (hCl : 2 < Cl) (hC' : 1 ≤ C') (hA : 1 ≤ Aa) (u : D.what₂.Word) :
    Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 Aa := by
  obtain ⟨⟨hS, hD, h0⟩, -⟩ := hH
  have hT : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hv : ∀ τ, vand (uS D u τ) ≤ Aa ^ D.R.k * vand (uS D u τ) := fun τ =>
    le_mul_of_one_le_left (vand_uS_pos D u τ).le (one_le_pow₀ hA)
  exact ⟨⟨hS, hD, h0⟩, Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hD hS hCl u u, by rw [div_self hT.ne']; exact hA,
    by rw [div_self hT.ne']; exact hA, klogk_of D large₂ C' Cl Cg cb Cu cT CT hS hC',
    (logf_of D large₂ C' Cl Cg cb Cu cT CT Aa hS hA).1, (logf_of D large₂ C' Cl Cg cb Cu cT CT Aa hS hA).2,
    fun τ => ⟨hv τ, hv τ⟩⟩

theorem fourth_statement_of_loops_alt (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Aa C CX c A : ℝ)
    (hCl : 2 < Cl) (hC' : 1 ≤ C') (hA : 1 ≤ Aa)
    (h1 : ∀ u, UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u C' Cl Cg cb Cu cT CT C0 Aa C)
    (hX : ∀ u, UnitaryVolumeMass.stX D large₂ u u C' Cl Cg cb Cu cT CT C0 Aa CX c)
    (hC : 0 ≤ C) (hCA : 3 * C ≤ A) (hCX : 0 ≤ CX) (hCXA : CX ≤ A) (hc0 : 0 ≤ c) (hc : c ≤ D.R.k * D.host.v) (hkv : 0 < (D.R.k : ℝ) * D.host.v)
    (hbig : C * D.R.k * large₂.sc.b ^ (C ^ 2 * (D.R.m : ℝ) ^ 2) ≤ A ^ (D.R.k - 1))
    (hM : ∀ u, chk_MassSum D u)
    (hone : LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u, chk_SCone D large₂ u A) :
    LatticeIndexAndWeightTheory.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A :=
  fourth_statement_of_loops D large₂ C' Cl Cg cb Cu cT CT C0 Aa C CX c A
    (fun hH u => chk_S5Hyp_self D large₂ C' Cl Cg cb Cu cT CT C0 Aa hH hCl hC' hA u) h1 hX hC hCA hCX hCXA hc0 hc hkv hbig hM hone

theorem fourth_statement_of_previous (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Aa C CX c A : ℝ)
    (hCl : 2 < Cl) (hClC : C ^ 2 ≤ Cl) (hC' : 1 ≤ C') (hcC' : c ≤ C') (hA : 1 ≤ Aa)
    (hC : 0 ≤ C) (hCA : 3 * C ≤ A) (hCX : 0 ≤ CX) (hCXA : CX ≤ A) (hA40 : 40 ≤ A) (hc0 : 0 ≤ c)
    (h1 : ∀ u, VanishingOnXAndXPlusMass.Conclusion4 D large₂ u u C' Cl Cg cb Cu cT CT C0 Aa C)
    (hX : ∀ u, VanishingOnXAndXPlusMass.Conclusion1 D large₂ u u C' Cl Cg cb Cu cT CT C0 Aa CX c)
    (hM : ∀ u, chk_MassSum D u)
    (hone : LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u, chk_SCone D large₂ u A) :
    LatticeIndexAndWeightTheory.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A := by
  intro hH
  have hS := hH.1.1
  obtain ⟨-, a2, -, -, -, -, a7, -, -, -, -, -, -, -, -, -, -, -, a19, -⟩ := hS
  have hL : 1 < large₂.sc.L := sc_one_lt_L large₂
  have hm := two_le_mR D
  have hf := two_le_fR D
  have hk5 : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hkC : C' ≤ D.R.k := by
    have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      have : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := one_le_pow₀ (by linarith)
      nlinarith [mul_le_mul this (by linarith : (1 : ℝ) ≤ D.R.f) zero_le_one (by positivity)]
    calc C' = C' * 1 := by ring
      _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
      _ ≤ D.R.k := a2
  have hkv : 0 < (D.R.k : ℝ) * D.host.v := mul_pos hk0 (by linarith)
  have hc : c ≤ D.R.k * D.host.v := by nlinarith
  have hbig : C * D.R.k * large₂.sc.b ^ (C ^ 2 * (D.R.m : ℝ) ^ 2) ≤ A ^ (D.R.k - 1) :=
    chk_big C A Cl large₂.sc.L D.R.m D.R.k hC (by linarith) hA40 hClC (by linarith) a7 hk5
  exact fourth_statement_of_loops_alt D large₂ C' Cl Cg cb Cu cT CT C0 Aa C CX c A hCl hC' hA h1 hX hC hCA hCX hCXA hc0 hc hkv hbig hM hone hH

theorem cone_bound_of_fourth (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A : ℝ)
    (h : LatticeIndexAndWeightTheory.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A) (hH : LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0) (u : D.what₂.Word) :
    chk_SCone D large₂ u A := fun F0 he hz Λ hΛ reps hr de hde =>
  h hH u F0 he hz Λ hΛ reps hr 1 le_rfl (by have := D.R.m_add_three_le_k; omega) de hde

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

open NumberField

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem chk_mem_Hp (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T')
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (x : S.V) :
    x ∈ Hp Λ F F' ↔ x ∈ orth S (Xplus F) ∧ x ∈ orth S (Xplus F') := by
  unfold Hp
  rw [show UUE Λ F F' = U2 F F' from a_HU Λ hΛ F F' hz hz']
  simp only [a_mem_orth, U2]
  constructor
  · intro h
    exact ⟨fun w hw => h w (Submodule.mem_sup_left hw), fun w hw => h w (Submodule.mem_sup_right hw)⟩
  · rintro ⟨h1, h2⟩ w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add, LinearMap.add_apply, h1 a ha, h2 b hb, add_zero]

theorem chk_orth_parts (F : LFlag S r T) {x : S.V} (h : x ∈ orth S (Xplus F)) :
    x ∈ orth S (Xsp F) ∧ S.hT F.fl.z x = 0 := by
  rw [a_mem_orth] at h
  refine ⟨(a_mem_orth _ _).2 (fun w hw => h w (Submodule.mem_sup_left hw)), ?_⟩
  exact h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))

theorem chk_I_le_La (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T')
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) : toO S (Isp F.fl F'.fl) ≤ La Λ g F F' := by
  intro x hx
  have hX : x ∈ Xsp F := hx.1
  have hX' : x ∈ Xsp F' := hx.2
  have h1 := a_X_le_orth_Xplus F hX
  have h2 := a_X_le_orth_Xplus F' hX'
  refine Submodule.subset_span ⟨(chk_mem_Hp Λ hΛ F F' hz hz' x).2 ⟨h1, h2⟩, ?_, ?_, ?_⟩
  · exact ⟨⟨Submodule.mem_sup_right hX, (chk_orth_parts F h1).1⟩, (chk_orth_parts F h1).2⟩
  · exact ⟨⟨Submodule.mem_sup_right hX', (chk_orth_parts F' h2).1⟩, (chk_orth_parts F' h2).2⟩
  · exact ⟨0, Submodule.zero_mem _, by simpa using hX, 0, Submodule.zero_mem _, by simpa using hX',
      by simp⟩

theorem chk_Thp_le_La (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T')
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) : Thp Λ F F' ≤ La Λ g F F' := by
  intro x hx
  have hΛx : x ∈ Λ := hx.1
  have hH : x ∈ Hp Λ F F' := hx.2
  obtain ⟨h1, h2⟩ := (chk_mem_Hp Λ hΛ F F' hz hz' x).1 hH
  have l1 : x ∈ Lrep Λ F := ⟨hΛx, (chk_orth_parts F h1).1⟩
  have l2 : x ∈ Lrep Λ F' := ⟨hΛx, (chk_orth_parts F' h2).1⟩
  refine Submodule.subset_span ⟨hH, ?_, ?_, ?_⟩
  · exact ⟨⟨Submodule.mem_sup_left l1, (chk_orth_parts F h1).1⟩, (chk_orth_parts F h1).2⟩
  · exact ⟨⟨Submodule.mem_sup_left l2, (chk_orth_parts F' h2).1⟩, (chk_orth_parts F' h2).2⟩
  · exact ⟨x, l1, by simp, x, l2, by simp, by simp⟩

theorem chk_La_le (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') :
    La Λ g F F' ≤ L0sub Λ F ⊓ toO S (Hp Λ F F') :=
  Submodule.span_le.2 (fun _ hx => ⟨hx.2.1, hx.1⟩)

end Gen

theorem lattice_chain_inclusions {D : D7} (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') :
    toO (hS D) (LatticeIndexAndWeightTheory.Iof X t) ≤ LatticeIndexAndWeightTheory.ThP X t ∧ LatticeIndexAndWeightTheory.ThP X t ≤ LatticeIndexAndWeightTheory.LaP X t ∧ LatticeIndexAndWeightTheory.LaP X t ≤ LatticeIndexAndWeightTheory.SublatticeInterSubspace X t := by
  have hΛ := (X.fixed t).1
  have hz := (X.fixed t).2.2.1.2
  have hz' := (X.lift' t).2
  refine ⟨le_sup_right, sup_le ?_ ?_, ?_⟩
  · exact chk_Thp_le_La (X.abelian₂ t) hΛ (gS D) (X.fl t) (X.fl' t) hz hz'
  · exact chk_I_le_La (X.abelian₂ t) hΛ (gS D) (X.fl t) (X.fl' t) hz hz'
  · exact chk_La_le (X.abelian₂ t) (gS D) (X.fl t) (X.fl' t)

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem chk_MassSum_holds (D : D7) (u : D.what₂.Word) : chk_MassSum D u :=
  fun _ _ _ _ _ reps h => Formalism.MainNotions.BridgeLemma₂.mass_eq_sum_inv_aut_card _ _ reps h

theorem fourth_statement_of_previous_alt (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Aa C CX c A : ℝ)
    (hCl : 2 < Cl) (hClC : C ^ 2 ≤ Cl) (hC' : 1 ≤ C') (hcC' : c ≤ C') (hA : 1 ≤ Aa)
    (hC : 0 ≤ C) (hCA : 3 * C ≤ A) (hCX : 0 ≤ CX) (hCXA : CX ≤ A) (hA40 : 40 ≤ A) (hc0 : 0 ≤ c)
    (h1 : ∀ u, VanishingOnXAndXPlusMass.Conclusion4 D large₂ u u C' Cl Cg cb Cu cT CT C0 Aa C)
    (hX : ∀ u, VanishingOnXAndXPlusMass.Conclusion1 D large₂ u u C' Cl Cg cb Cu cT CT C0 Aa CX c)
    (hone : LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u, chk_SCone D large₂ u A) :
    LatticeIndexAndWeightTheory.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A :=
  fourth_statement_of_previous D large₂ C' Cl Cg cb Cu cT CT C0 Aa C CX c A hCl hClC hC' hcC' hA hC hCA hCX hCXA hA40 hc0 h1 hX
    (chk_MassSum_holds D) hone

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

theorem mk_core : Formalism.HermitianLatticeCounting.S6.MinkowskiBound := card_dvd_minkowskiNumber

theorem mk_autBound : Formalism.HermitianLatticeCounting.S6.AutBound := Formalism.HermitianLatticeCounting.Final.S6.autBound_of_minkowskiBound mk_core

theorem minkowski_bound_admissible_eleven : Formalism.MainNotions.NonGenericAndKTwoTheorems.adm11 := card_dvd_minkowskiNumber

theorem minkowski_bound_admissible : Formalism.MainNotions.LatticeIndexAndWeightTheory.adm5 := card_dvd_minkowskiNumber

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

open NumberField

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def t3Q (F : LFlag S r T) (F' : LFlag S r T') : Submodule E S.V := orth S (Xsp F ⊔ Xsp F')

def t3L (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  Lsub Λ F ⊓ toO S (t3Q F F')

def t3L' (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  Lsub Λ F' ⊓ toO S (t3Q F F')

def lamOneLattice (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  (Λ ⊓ toO S (t3Q F F')) ⊔ toO S (Isp F.fl F'.fl)

theorem lattice_index_eq_relIndex (A B : Submodule (𝓞 E) S.V) : idx S A B = B.toAddSubgroup.relIndex A.toAddSubgroup := rfl

variable (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T')
  (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z)

include hΛ hz hz'

theorem Hp_le_Q : Hp Λ F F' ≤ t3Q F F' := by
  intro x hx
  obtain ⟨h1, h2⟩ := (chk_mem_Hp Λ hΛ F F' hz hz' x).1 hx
  rw [t3Q, a_mem_orth]
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add, LinearMap.add_apply, (a_mem_orth _ _).1 (chk_orth_parts F h1).1 a ha,
    (a_mem_orth _ _).1 (chk_orth_parts F' h2).1 b hb, add_zero]

theorem I_le_Hp : Isp F.fl F'.fl ≤ Hp Λ F F' := by
  intro x hx
  exact (chk_mem_Hp Λ hΛ F F' hz hz' x).2 ⟨a_X_le_orth_Xplus F hx.1, a_X_le_orth_Xplus F' hx.2⟩

theorem L0_inf_W_eq : L0sub Λ F ⊓ toO S (Hp Λ F F') = t3L Λ F F' ⊓ toO S (Hp Λ F F') := by
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.1, Hp_le_Q Λ hΛ F F' hz hz' h2⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.1, (chk_orth_parts F ((chk_mem_Hp Λ hΛ F F' hz hz' x).1 h2).1).2⟩, h2⟩

theorem Th_eq_Lam_one_inf_W : Thp Λ F F' ⊔ toO S (Isp F.fl F'.fl) = lamOneLattice Λ F F' ⊓ toO S (Hp Λ F F') := by
  have hI : toO S (Isp F.fl F'.fl) ≤ toO S (Hp Λ F F') := fun x hx => I_le_Hp Λ hΛ F F' hz hz' hx
  unfold lamOneLattice
  rw [sup_comm (Λ ⊓ toO S (t3Q F F')), sup_inf_assoc_of_le _ hI, sup_comm]
  congr 1
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, Hp_le_Q Λ hΛ F F' hz hz' h2⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.1, h2⟩

theorem La_le_intersection (g : ℕ) : La Λ g F F' ≤ (t3L Λ F F' ⊓ t3L' Λ F F') ⊓ toO S (Hp Λ F F') := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨h1, h2, h3, -⟩
  have hQ := Hp_le_Q Λ hΛ F F' hz hz' h1
  exact ⟨⟨⟨h2.1, hQ⟩, ⟨h3.1, hQ⟩⟩, h1⟩

theorem lattice_index_chain (g : ℕ) (h0 : idx S (t3L Λ F F') (lamOneLattice Λ F F') ≠ 0) :
    0 < idx S (L0sub Λ F ⊓ toO S (Hp Λ F F')) (La Λ g F F') ∧
    0 < idx S (La Λ g F F') (Thp Λ F F' ⊔ toO S (Isp F.fl F'.fl)) ∧
    idx S (L0sub Λ F ⊓ toO S (Hp Λ F F')) (La Λ g F F') * idx S (La Λ g F F') (Thp Λ F F' ⊔ toO S (Isp F.fl F'.fl)) ≤
      idx S (t3L Λ F F') (lamOneLattice Λ F F') ∧
    idx S (t3L Λ F F' ⊓ t3L' Λ F F') (lamOneLattice Λ F F') ≠ 0 ∧
    idx S (La Λ g F F') (Thp Λ F F' ⊔ toO S (Isp F.fl F'.fl)) ≤ idx S (t3L Λ F F' ⊓ t3L' Λ F F') (lamOneLattice Λ F F') := by
  rw [L0_inf_W_eq Λ hΛ F F' hz hz', Th_eq_Lam_one_inf_W Λ hΛ F F' hz hz']
  have hTh : lamOneLattice Λ F F' ⊓ toO S (Hp Λ F F') ≤ La Λ g F F' := by
    rw [← Th_eq_Lam_one_inf_W Λ hΛ F F' hz hz']
    exact sup_le (chk_Thp_le_La Λ hΛ g F F' hz hz') (chk_I_le_La Λ hΛ g F F' hz hz')
  have hLa := La_le_intersection Λ hΛ F F' hz hz' g
  have hLa1 : La Λ g F F' ≤ t3L Λ F F' ⊓ toO S (Hp Λ F F') := fun x hx => ⟨(hLa hx).1.1, (hLa hx).2⟩
  obtain ⟨c1, c2⟩ := Formalism.HermitianLatticeCounting.Final.S6.indexChain S.V (lamOneLattice Λ F F').toAddSubgroup (t3L Λ F F').toAddSubgroup
    (toO S (Hp Λ F F')).toAddSubgroup (La Λ g F F').toAddSubgroup hTh hLa1 h0
  have d1 := Formalism.HermitianLatticeCounting.Final.S6.relIndexInter S.V (lamOneLattice Λ F F').toAddSubgroup (t3L Λ F F').toAddSubgroup
    (toO S (Hp Λ F F')).toAddSubgroup ((t3L Λ F F').toAddSubgroup ⊓ (toO S (Hp Λ F F')).toAddSubgroup) le_rfl
  have d2 := Formalism.HermitianLatticeCounting.Final.S6.relIndexInter S.V (lamOneLattice Λ F F').toAddSubgroup
    ((t3L Λ F F' ⊓ t3L' Λ F F').toAddSubgroup) (toO S (Hp Λ F F')).toAddSubgroup (La Λ g F F').toAddSubgroup hLa
  have d3 := Formalism.HermitianLatticeCounting.Final.S6.relIndexInter S.V (lamOneLattice Λ F F').toAddSubgroup (t3L Λ F F').toAddSubgroup ⊤
    ((t3L Λ F F' ⊓ t3L' Λ F F').toAddSubgroup) (fun x hx => ⟨hx.1, trivial⟩)
  rw [inf_top_eq] at d3
  have n3 : (lamOneLattice Λ F F').toAddSubgroup.relIndex (t3L Λ F F' ⊓ t3L' Λ F F').toAddSubgroup ≠ 0 :=
    fun h => h0 (Nat.eq_zero_of_zero_dvd (h ▸ d3))
  have n1 : ((lamOneLattice Λ F F').toAddSubgroup ⊓ (toO S (Hp Λ F F')).toAddSubgroup).relIndex
      ((t3L Λ F F').toAddSubgroup ⊓ (toO S (Hp Λ F F')).toAddSubgroup) ≠ 0 :=
    fun h => h0 (Nat.eq_zero_of_zero_dvd (h ▸ d1))
  rw [← c1] at n1
  refine ⟨Nat.pos_of_ne_zero (left_ne_zero_of_mul n1), Nat.pos_of_ne_zero (right_ne_zero_of_mul n1), ?_, n3,
    Nat.le_of_dvd (Nat.pos_of_ne_zero n3) d2⟩
  exact c1.le.trans c2

end Gen

section Emb

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def t3BN (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  Λ ⊓ toO S (Xsp F ⊔ Xsp F')

def t3BD (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  XLam Λ F ⊔ XLam Λ F'

theorem lattice_index_le_of_map {A B A' B' : Submodule (𝓞 E) S.V} (R : S.V → S.V → Prop) (hfin : idx S A' B' ≠ 0)
    (hex : ∀ y ∈ A, ∃ b ∈ A', R y b)
    (hinj : ∀ y₁ ∈ A, ∀ y₂ ∈ A, ∀ b₁ b₂, R y₁ b₁ → R y₂ b₂ → b₁ - b₂ ∈ B' → y₁ - y₂ ∈ B) :
    idx S A B ≤ idx S A' B' := by
  classical
  have hF : Finite (A' ⧸ B'.comap A'.subtype) := Nat.finite_of_card_ne_zero hfin
  choose f hf hR using hex
  let φ : (A ⧸ B.comap A.subtype) → (A' ⧸ B'.comap A'.subtype) := fun q =>
    Submodule.Quotient.mk ⟨f (Quotient.out q).1 (Quotient.out q).2, hf _ _⟩
  refine Nat.card_le_card_of_injective φ ?_
  intro q₁ q₂ h
  have h1 : (⟨f (Quotient.out q₁).1 (Quotient.out q₁).2, hf _ _⟩ : A') -
      ⟨f (Quotient.out q₂).1 (Quotient.out q₂).2, hf _ _⟩ ∈ B'.comap A'.subtype := (Submodule.Quotient.eq _).1 h
  have h2 := hinj _ (Quotient.out q₁).2 _ (Quotient.out q₂).2 _ _ (hR _ _) (hR _ _) h1
  have h3 : (Submodule.Quotient.mk (Quotient.out q₁) : A ⧸ B.comap A.subtype) = Submodule.Quotient.mk (Quotient.out q₂) :=
    (Submodule.Quotient.eq _).2 h2
  have e1 : (Submodule.Quotient.mk (Quotient.out q₁) : A ⧸ B.comap A.subtype) = q₁ := Quotient.out_eq q₁
  have e2 : (Submodule.Quotient.mk (Quotient.out q₂) : A ⧸ B.comap A.subtype) = q₂ := Quotient.out_eq q₂
  rw [← e1, ← e2, h3]

theorem intersection_index_le_card_B (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    (hfin : idx S (t3BN Λ F F') (t3BD Λ F F') ≠ 0) :
    idx S (t3L Λ F F' ⊓ t3L' Λ F F') (lamOneLattice Λ F F') ≤ idx S (t3BN Λ F F') (t3BD Λ F F') := by
  have hIQ : Isp F.fl F'.fl ≤ t3Q F F' := by
    intro x hx
    rw [t3Q, a_mem_orth]
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add, LinearMap.add_apply, b_X_X F ha hx.1, b_X_X F' hb hx.2, add_zero]
  refine lattice_index_le_of_map (fun y b => ∃ l ∈ Λ, ∃ l' ∈ Λ, y - l ∈ Xsp F ∧ y - l' ∈ Xsp F' ∧ b = l - l') hfin ?_ ?_
  · rintro y ⟨⟨⟨h1, -⟩, -⟩, ⟨⟨h2, -⟩, -⟩⟩
    obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 h1
    obtain ⟨l', hl', x', hx', e⟩ := Submodule.mem_sup.1 h2
    have hx1 : x ∈ Xsp F := hx
    have hx1' : x' ∈ Xsp F' := hx'
    refine ⟨l - l', ⟨Λ.sub_mem hl.1 hl'.1, ?_⟩, l, hl.1, l', hl'.1, by simpa using hx1, ?_, rfl⟩
    · have e2 : l - l' = x' - x := by
        have : l' + x' - x = l := by rw [e]; abel
        rw [← this]; abel
      show l - l' ∈ Xsp F ⊔ Xsp F'
      rw [e2, sub_eq_add_neg, add_comm]
      exact Submodule.add_mem_sup (Submodule.neg_mem _ hx1) hx1'
    · rw [← e]; simpa using hx1'
  · rintro y₁ hy₁ y₂ hy₂ b₁ b₂ ⟨l₁, hl₁, l₁', hl₁', a₁, a₁', rfl⟩ ⟨l₂, hl₂, l₂', hl₂', a₂, a₂', rfl⟩ hb
    obtain ⟨a, ha, a', ha', e⟩ := Submodule.mem_sup.1 hb

    have hμ : (l₁ - l₂) - a ∈ Λ := Λ.sub_mem (Λ.sub_mem hl₁ hl₂) ha.1
    have hX : (y₁ - y₂) - ((l₁ - l₂) - a) ∈ Xsp F := by
      have e1 : (y₁ - y₂) - ((l₁ - l₂) - a) = (y₁ - l₁) - (y₂ - l₂) + a := by abel
      rw [e1]
      exact Submodule.add_mem _ (Submodule.sub_mem _ a₁ a₂) ha.2
    have hX' : (y₁ - y₂) - ((l₁ - l₂) - a) ∈ Xsp F' := by
      have e1 : (y₁ - y₂) - ((l₁ - l₂) - a) = (y₁ - l₁') - (y₂ - l₂') - a' := by
        have e2 : a' = (l₁ - l₁' - (l₂ - l₂')) - a := by rw [← e]; abel
        rw [e2]; abel
      rw [e1]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ a₁' a₂') ha'.2
    have hI : (y₁ - y₂) - ((l₁ - l₂) - a) ∈ Isp F.fl F'.fl := ⟨hX, hX'⟩
    have hyQ : y₁ - y₂ ∈ t3Q F F' := Submodule.sub_mem _ hy₁.1.2 hy₂.1.2
    have hμQ : (l₁ - l₂) - a ∈ t3Q F F' := by
      have e1 : (l₁ - l₂) - a = (y₁ - y₂) - ((y₁ - y₂) - ((l₁ - l₂) - a)) := by abel
      rw [e1]
      exact Submodule.sub_mem _ hyQ (hIQ hI)
    have e3 : y₁ - y₂ = ((l₁ - l₂) - a) + ((y₁ - y₂) - ((l₁ - l₂) - a)) := by abel
    rw [e3]
    exact Submodule.add_mem_sup ⟨hμ, hμQ⟩ hI

theorem index_B_finite (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') :
    idx S (t3BN Λ F F') (t3BD Λ F F') ≠ 0 := by
  have hfg : (t3BN Λ F F').FG := g_fg_le hΛ.fg inf_le_left
  refine (g_idx_pos hfg (g_Comm_of_span hfg ?_)).ne'
  unfold t3BN t3BD XLam spanE
  rw [a_span_inf Λ hΛ, a_span_sup, a_span_inf Λ hΛ, a_span_inf Λ hΛ]

end Emb

section Fin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem I_le_Q (F : LFlag S r T) (F' : LFlag S r T') : Isp F.fl F'.fl ≤ t3Q F F' := by
  intro x hx
  rw [t3Q, a_mem_orth]
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add, LinearMap.add_apply, b_X_X F ha hx.1, b_X_X F' hb hx.2, add_zero]

theorem Q_le_orth_X (F : LFlag S r T) (F' : LFlag S r T') : t3Q F F' ≤ orth S (Xsp F) := by
  intro x hx
  rw [a_mem_orth]
  exact fun w hw => (a_mem_orth _ _).1 hx w (Submodule.mem_sup_left hw)

theorem Q_inf_X_le_I (F : LFlag S r T) (F' : LFlag S r T') (c : E) (hzc : F'.fl.z - c • F.fl.z ∈ Xsp F ⊔ Xsp F')
    (hk : perpS S (Xplus F ⊔ Xplus F') ⊓ Xsp F = Isp F.fl F'.fl) : t3Q F F' ⊓ Xsp F ≤ Isp F.fl F'.fl := by
  rintro x ⟨hQ, hX⟩
  rw [← hk]
  refine ⟨?_, hX⟩
  have hQ' := (a_mem_orth _ _).1 hQ
  have hzx : S.hT F.fl.z x = 0 := LinearMap.mem_ker.1 (a_z_X F hX)
  have hz'x : S.hT F'.fl.z x = 0 := by
    have e : F'.fl.z = c • F.fl.z + (F'.fl.z - c • F.fl.z) := by abel
    rw [e, map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, hzx, smul_zero, zero_add]
    exact hQ' _ hzc
  have hle : F.fl.X ⊔ Submodule.span E {F.fl.z} ⊔ (F'.fl.X ⊔ Submodule.span E {F'.fl.z}) ≤ LinearMap.ker (S.hT.flip x) := by
    refine sup_le (sup_le ?_ (Submodule.span_le.2 ?_)) (sup_le ?_ (Submodule.span_le.2 ?_))
    · intro v hv; exact LinearMap.mem_ker.2 (hQ' v (Submodule.mem_sup_left hv))
    · rintro _ rfl; exact LinearMap.mem_ker.2 hzx
    · intro v hv; exact LinearMap.mem_ker.2 (hQ' v (Submodule.mem_sup_right hv))
    · rintro _ rfl; exact LinearMap.mem_ker.2 hz'x
  exact fun w hw => LinearMap.mem_ker.1 (hle hw)

theorem orth_X_le_Q_sup_X (F : LFlag S r T) (F' : LFlag S r T') (hT : T ≠ 0) (c : E) (hc : c ≠ 0)
    (hzc : F'.fl.z - c • F.fl.z ∈ Xsp F ⊔ Xsp F')
    (hs : perpS S (Xplus F ⊔ Xplus F') ⊔ Xsp F = F.fl.XplusPerp) : orth S (Xsp F) ≤ t3Q F F' ⊔ Xsp F := by
  intro y hy
  have hy' := (a_mem_orth _ _).1 hy
  obtain ⟨a, ha, a', ha', e⟩ := Submodule.mem_sup.1 hzc
  have e1 : F.fl.z + c⁻¹ • a = c⁻¹ • (F'.fl.z - a') := by
    have e2 : F'.fl.z - a' = c • F.fl.z + a := by rw [← sub_eq_iff_eq_add'.2 e.symm]; abel
    rw [e2, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hzQ : F.fl.z + c⁻¹ • a ∈ t3Q F F' := by
    rw [t3Q, a_mem_orth]
    intro w hw
    obtain ⟨v, hv, v', hv', rfl⟩ := Submodule.mem_sup.1 hw
    have h1 : S.hT v (F.fl.z + c⁻¹ • a) = 0 := by
      rw [map_add, map_smul, (flag_span_orth_normal F hv).1, b_X_X F hv ha, smul_zero, add_zero]
    have h2 : S.hT v' (F.fl.z + c⁻¹ • a) = 0 := by
      rw [e1, map_smul, map_sub, (flag_span_orth_normal F' hv').1, b_X_X F' hv' ha', sub_zero, smul_zero]
    rw [LinearMap.map_add₂, h1, h2, add_zero]
  set α : E := -(S.hT F.fl.z y) / T with hα
  have hw : y - α • F.fl.z ∈ F.fl.XplusPerp := by
    have hle : F.fl.X ⊔ Submodule.span E {F.fl.z} ≤ LinearMap.ker (S.hT.flip (y - α • F.fl.z)) := by
      refine sup_le ?_ (Submodule.span_le.2 ?_)
      · intro v hv
        refine LinearMap.mem_ker.2 ?_
        show S.hT v (y - α • F.fl.z) = 0
        rw [map_sub, map_smul, hy' v hv, (flag_span_orth_normal F hv).1, smul_zero, sub_zero]
      · rintro _ rfl
        refine LinearMap.mem_ker.2 ?_
        show S.hT F.fl.z (y - α • F.fl.z) = 0
        rw [map_sub, map_smul, F.fl.z_norm, hα, smul_eq_mul]
        field_simp
        ring
    exact fun v hv => LinearMap.mem_ker.1 (hle hv)
  rw [← hs] at hw
  obtain ⟨p, hp, x, hx, e3⟩ := Submodule.mem_sup.1 hw
  have hpQ : p ∈ t3Q F F' := by
    rw [t3Q, a_mem_orth]
    intro w hw
    refine hp w ?_
    obtain ⟨v, hv, v', hv', rfl⟩ := Submodule.mem_sup.1 hw
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left hv))
      (Submodule.mem_sup_right (Submodule.mem_sup_left hv'))
  have e4 : y = (p + α • (F.fl.z + c⁻¹ • a)) + (x - α • c⁻¹ • a) := by
    have : y = p + x + α • F.fl.z := by rw [e3]; abel
    rw [this, smul_add]; abel
  rw [e4]
  exact Submodule.add_mem_sup (Submodule.add_mem _ hpQ (Submodule.smul_mem _ _ hzQ))
    (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ha)))

theorem lattice_index_L_finite (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T')
    (hQX : t3Q F F' ⊓ Xsp F ≤ Isp F.fl F'.fl) (hXQ : orth S (Xsp F) ≤ t3Q F F' ⊔ Xsp F) :
    idx S (t3L Λ F F') (lamOneLattice Λ F F') ≠ 0 := by
  obtain ⟨C0, hC0⟩ := Submodule.exists_isCompl (Isp F.fl F'.fl)
  set C : Submodule E S.V := C0 ⊓ t3Q F F' with hC
  have hIQ := I_le_Q F F'
  have hCQ : t3Q F F' ≤ C ⊔ Isp F.fl F'.fl := by
    intro q hq
    have hq' : q ∈ Isp F.fl F'.fl ⊔ C0 := by rw [hC0.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨i, hi, c0, hc0, rfl⟩ := Submodule.mem_sup.1 hq'
    have hc0Q : c0 ∈ t3Q F F' := by
      have e : c0 = (i + c0) - i := by abel
      rw [e]; exact Submodule.sub_mem _ hq (hIQ hi)
    rw [add_comm]
    exact Submodule.add_mem_sup ⟨hc0, hc0Q⟩ hi
  have hCX : C ⊓ Xsp F = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact (Submodule.disjoint_def.1 hC0.disjoint x (hQX ⟨h2, h3⟩) h1) ▸ Submodule.zero_mem _
  obtain ⟨N, hN⟩ := Submodule.exists_isCompl (C ⊔ Xsp F)
  have hCK : IsCompl C (Xsp F ⊔ N) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx2
      obtain ⟨a, ha, n, hn, rfl⟩ := Submodule.mem_sup.1 hx2
      have hn0 : n = 0 := by
        refine Submodule.disjoint_def.1 hN.disjoint n ?_ hn
        have e : n = (a + n) - a := by abel
        rw [e]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hx) (Submodule.mem_sup_right ha)
      rw [hn0, add_zero] at hx ⊢
      have : a ∈ C ⊓ Xsp F := ⟨hx, ha⟩
      rw [hCX] at this
      exact (Submodule.mem_bot E).1 this
    · rw [codisjoint_iff, ← sup_assoc, hN.sup_eq_top]
  let p : S.V →ₗ[E] S.V := C.subtype ∘ₗ C.projectionOnto (Xsp F ⊔ N) hCK
  have hp1 : ∀ c ∈ C, p c = c := fun c hc =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hCK ⟨c, hc⟩)
  have hp2 : ∀ x ∈ Xsp F, p x = 0 := fun x hx =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_of_mem_right hCK (Submodule.mem_sup_left hx))
  have key : ∀ l ∈ orth S (Xsp F), p l ∈ C ∧ l - p l ∈ Xsp F := by
    intro l hl
    obtain ⟨q, hq, x, hx, rfl⟩ := Submodule.mem_sup.1 (hXQ hl)
    obtain ⟨c, hc, i, hi, rfl⟩ := Submodule.mem_sup.1 (hCQ hq)
    have e : p (c + i + x) = c := by rw [map_add, map_add, hp1 c hc, hp2 i hi.1, hp2 x hx, add_zero, add_zero]
    rw [e]
    refine ⟨hc, ?_⟩
    have e2 : c + i + x - c = i + x := by abel
    rw [e2]
    exact Submodule.add_mem _ hi.1 hx
  set A : Submodule (𝓞 E) S.V := (Lrep Λ F).map (p.restrictScalars (𝓞 E)) with hA
  have hAfg : A.FG := (g_fg_le hΛ.fg inf_le_left).map _
  have hAQ : A ≤ toO S (t3Q F F') := by
    rintro _ ⟨l, hl, rfl⟩
    exact (key l hl.2).1.2
  have hAL : A ≤ t3L Λ F F' := by
    rintro _ ⟨l, hl, rfl⟩
    have hk := key l hl.2
    refine ⟨⟨?_, Q_le_orth_X F F' hk.1.2⟩, hk.1.2⟩
    have e : (p.restrictScalars (𝓞 E)) l = l + -(l - p l) := by
      show p l = _
      abel
    rw [e]
    exact Submodule.add_mem_sup hl (Submodule.neg_mem _ hk.2)
  have hsurj : t3L Λ F F' ≤ A ⊔ lamOneLattice Λ F F' := by
    rintro y ⟨⟨h1, -⟩, hyQ⟩
    obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 h1
    have hk := key l hl.2
    have hx1 : x ∈ Xsp F := hx
    have hd : l + x - p l ∈ Isp F.fl F'.fl := by
      refine hQX ⟨Submodule.sub_mem _ hyQ hk.1.2, ?_⟩
      have e : l + x - p l = (l - p l) + x := by abel
      rw [e]
      exact Submodule.add_mem _ hk.2 hx1
    have e : l + x = p l + (l + x - p l) := by abel
    rw [e]
    exact Submodule.add_mem_sup ⟨l, hl, rfl⟩ (Submodule.mem_sup_right hd)
  have hcong := h_idx_congr (A := A) (B := A ⊓ lamOneLattice Λ F F') (A' := t3L Λ F F') (B' := lamOneLattice Λ F F') hAL inf_le_right
    hsurj le_rfl
  have hspan : spanE S A ≤ spanE S (lamOneLattice Λ F F') := by
    have h1 : spanE S A ≤ t3Q F F' := Submodule.span_le.2 hAQ
    have h2 : t3Q F F' ≤ spanE S (lamOneLattice Λ F F') := by
      have h3 := a_span_inf Λ hΛ (t3Q F F')
      calc t3Q F F' = Submodule.span E ((Λ ⊓ toO S (t3Q F F') : Submodule (𝓞 E) S.V) : Set S.V) := h3.symm
        _ ≤ spanE S (lamOneLattice Λ F F') := Submodule.span_mono (by
            intro x hx
            exact (le_sup_left : Λ ⊓ toO S (t3Q F F') ≤ lamOneLattice Λ F F') hx)
    exact h1.trans h2
  have hpos := g_idx_pos hAfg (g_Comm_inf (A := A) (B := A) ⟨1, one_ne_zero, fun x hx => by simpa using hx⟩
    (g_Comm_of_span hAfg hspan))
  rw [hcong] at hpos
  exact hpos.ne'

theorem b_one_index_pos (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (I : Submodule E S.V) (j : ℕ)
    (hX : Xsp F ≤ Xflag F j ⊔ I) :
    0 < idx S (XLam Λ F) ((Λ ⊓ toO S (Xflag F j)) ⊔ (Λ ⊓ toO S I)) := by
  have hfg : (XLam Λ F).FG := g_fg_le hΛ.fg inf_le_left
  refine g_idx_pos hfg (g_Comm_of_span hfg ?_)
  unfold XLam spanE
  rw [a_span_inf Λ hΛ, a_span_sup, a_span_inf Λ hΛ, a_span_inf Λ hΛ]
  exact hX

end Fin

section Rec

variable {D : D7} (X : TermTie D)

def DiscriminantBound {u : D.what₂.Word} (t : D.s.Term u u) : Prop :=
  (idx (hS D) (t3L (X.abelian₂ t) (X.fl t) (X.fl' t)) (lamOneLattice (X.abelian₂ t) (X.fl t) (X.fl' t)) : ℝ) *
      (idx (hS D) (t3BN (X.abelian₂ t) (X.fl t) (X.fl' t)) (t3BD (X.abelian₂ t) (X.fl t) (X.fl' t)) : ℝ) ≤
    LatticeIndexAndWeightTheory.DelJ X t / (LatticeIndexAndWeightTheory.b1T X t : ℝ) ^ 2

theorem lattice_indices_pos {u : D.what₂.Word} (t : D.s.Term u u) (h : LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t) :
    0 < LatticeIndexAndWeightTheory.b1T X t ∧ 0 < LatticeIndexAndWeightTheory.gT X t ∧ 0 < LatticeIndexAndWeightTheory.iT X t ∧
      (LatticeIndexAndWeightTheory.gT X t : ℝ) * (LatticeIndexAndWeightTheory.iT X t : ℝ) ^ 2 ≤
        (idx (hS D) (t3L (X.abelian₂ t) (X.fl t) (X.fl' t)) (lamOneLattice (X.abelian₂ t) (X.fl t) (X.fl' t)) : ℝ) *
          (idx (hS D) (t3BN (X.abelian₂ t) (X.fl t) (X.fl' t)) (t3BD (X.abelian₂ t) (X.fl t) (X.fl' t)) : ℝ) := by
  have hΛ := (X.fixed t).1
  have hz := (X.fixed t).2.2.1.2
  have hz' := (X.lift' t).2
  obtain ⟨j, hj, c, hN⟩ := nf_core X t h.1 h.2.1
  obtain ⟨-, -, g3, -, g5, -⟩ := nf_gen _ _ _ _ j hj c hN
  have hfin := hN.1.2.1
  rw [nf_II] at hfin
  have hjo : LatticeIndexAndWeightTheory.jOf X t = j := by
    unfold LatticeIndexAndWeightTheory.jOf LatticeIndexAndWeightTheory.Iof
    rw [hfin]; omega
  have hXj := hN.1.2.2.2.2.2.2.1
  rw [nf_X, nf_Xa, nf_II] at hXj
  have h0 := lattice_index_L_finite (X.abelian₂ t) hΛ (X.fl t) (X.fl' t) (Q_inf_X_le_I (X.fl t) (X.fl' t) c g3.1 g5.1)
    (orth_X_le_Q_sup_X (X.fl t) (X.fl' t) (nf_T_ne D u) c hN.1.1 g3.1 g5.2)
  obtain ⟨c1, c2, c3, -, c5⟩ := lattice_index_chain (X.abelian₂ t) hΛ (X.fl t) (X.fl' t) hz hz' (gS D) h0
  have hB := intersection_index_le_card_B (X.abelian₂ t) (X.fl t) (X.fl' t) (index_B_finite (X.abelian₂ t) hΛ (X.fl t) (X.fl' t))
  refine ⟨?_, c1, c2, ?_⟩
  · unfold LatticeIndexAndWeightTheory.b1T
    rw [hjo]
    exact b_one_index_pos (X.abelian₂ t) hΛ (X.fl t) _ j hXj.le
  · have e1 : (LatticeIndexAndWeightTheory.gT X t : ℝ) * (LatticeIndexAndWeightTheory.iT X t : ℝ) ^ 2 = ((LatticeIndexAndWeightTheory.gT X t * LatticeIndexAndWeightTheory.iT X t : ℕ) : ℝ) * (LatticeIndexAndWeightTheory.iT X t : ℝ) := by
      push_cast; ring
    rw [e1]
    exact mul_le_mul (by exact_mod_cast c3) (by exact_mod_cast c5.trans hB) (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem discriminant_first_part_of_bound
    (hD : ∀ u : D.what₂.Word, LatticeIndexAndWeightTheory.TieOK X u → ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t → DiscriminantBound X t) : LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X := by
  intro u hu t ht
  obtain ⟨h1, h2, h3, h4⟩ := lattice_indices_pos X t ht
  exact ⟨h1, h2, h3, h4.trans (hD u hu t ht)⟩

end Rec

section Halves

variable {D : D7} (X : TermTie D)

def pairingDiscriminantIndex {u : D.what₂.Word} (t : D.s.Term u u) : ℕ :=
  idx (hS D) (Formalism.HermitianLatticesTheory.dual (hS D).hT (XLam (X.abelian₂ t) (X.fl t)) ⊓ toO (hS D) (Xsp (X.fl' t)))
    (XLam (X.abelian₂ t) (X.fl' t) ⊔ toO (hS D) (LatticeIndexAndWeightTheory.Iof X t))

def DiscriminantIndexHalf {u : D.what₂.Word} (t : D.s.Term u u) : Prop :=
  idx (hS D) (t3L (X.abelian₂ t) (X.fl t) (X.fl' t)) (lamOneLattice (X.abelian₂ t) (X.fl t) (X.fl' t)) *
      idx (hS D) (t3BN (X.abelian₂ t) (X.fl t) (X.fl' t)) (t3BD (X.abelian₂ t) (X.fl t) (X.fl' t)) ≤ pairingDiscriminantIndex X t

def DiscriminantIndexSecondHalf {u : D.what₂.Word} (t : D.s.Term u u) : Prop :=
  (pairingDiscriminantIndex X t : ℝ) ≤ LatticeIndexAndWeightTheory.DelJ X t / (LatticeIndexAndWeightTheory.b1T X t : ℝ) ^ 2

theorem discriminant_of_halves {u : D.what₂.Word} (t : D.s.Term u u) (hA : DiscriminantIndexHalf X t) (hC : DiscriminantIndexSecondHalf X t) : DiscriminantBound X t := by
  unfold DiscriminantBound
  refine le_trans ?_ hC
  exact_mod_cast hA

end Halves

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

open NumberField

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Det

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem side_index_identity (Λ : Submodule (𝓞 E) S.V) (Xs Xj I : Submodule E S.V) (hXj : Xj ≤ Xs) (hI : I ≤ Xs) (hsum : Xs ≤ Xj ⊔ I)
    (hd : Xj ⊓ I = ⊥) (P : Submodule (𝓞 E) S.V) (hIP : toO S I ≤ P) (hPX : P ≤ toO S Xs) (hAP : Λ ⊓ toO S Xs ≤ P) :
    g_idx (Λ ⊓ toO S Xs) ((Λ ⊓ toO S Xj) ⊔ (Λ ⊓ toO S I)) * g_idx P ((Λ ⊓ toO S Xs) ⊔ toO S I) =
      g_idx (P ⊓ toO S Xj) (Λ ⊓ toO S Xj) := by
  have hAIX : (Λ ⊓ toO S Xs) ⊔ toO S I ≤ toO S Xs := sup_le inf_le_right (fun x hx => hI hx)
  have hAIP : (Λ ⊓ toO S Xs) ⊔ toO S I ≤ P := sup_le hAP hIP
  have dec : ∀ v ∈ toO S Xs, ∃ xj ∈ Xj, ∃ i ∈ I, xj + i = v := fun v hv => Submodule.mem_sup.1 (hsum hv)
  have e1 : g_idx (Λ ⊓ toO S Xs) ((Λ ⊓ toO S Xj) ⊔ (Λ ⊓ toO S I)) =
      g_idx ((Λ ⊓ toO S Xs) ⊔ toO S I) ((Λ ⊓ toO S Xj) ⊔ toO S I) := by
    refine h_idx_congr le_sup_left (sup_le_sup_left inf_le_right _)
      (sup_le le_sup_left (le_sup_of_le_right le_sup_right)) ?_
    rintro x ⟨hx, hx2⟩
    obtain ⟨f, hf, i, hi, rfl⟩ := Submodule.mem_sup.1 hx2
    refine Submodule.add_mem_sup hf ⟨?_, hi⟩
    have e : i = (f + i) - f := by abel
    rw [e]; exact Λ.sub_mem hx.1 hf.1
  have e2 : g_idx (((Λ ⊓ toO S Xs) ⊔ toO S I) ⊓ toO S Xj) (Λ ⊓ toO S Xj) =
      g_idx ((Λ ⊓ toO S Xs) ⊔ toO S I) ((Λ ⊓ toO S Xj) ⊔ toO S I) := by
    refine h_idx_congr inf_le_left le_sup_left ?_ ?_
    · intro v hv
      obtain ⟨xj, hxj, i, hi, rfl⟩ := dec v (hAIX hv)
      have hi' : i ∈ toO S I := hi
      refine Submodule.add_mem_sup ⟨?_, hxj⟩ (Submodule.mem_sup_right hi')
      have e : xj = (xj + i) - i := by abel
      rw [e]; exact Submodule.sub_mem _ hv (Submodule.mem_sup_right hi')
    · rintro v ⟨⟨-, hvj⟩, hv2⟩
      obtain ⟨f, hf, i, hi, rfl⟩ := Submodule.mem_sup.1 hv2
      have hvj' : f + i ∈ Xj := hvj
      have hf' : f ∈ Xj := hf.2
      have hi' : i ∈ I := hi
      have hi0 : i = 0 := by
        have h1 : i ∈ Xj := by
          have e : i = (f + i) - f := by abel
          rw [e]; exact Xj.sub_mem hvj' hf'
        have h2 : i ∈ Xj ⊓ I := ⟨h1, hi'⟩
        rw [hd] at h2; exact (Submodule.mem_bot E).1 h2
      rw [hi0, add_zero]; exact hf
  have e3 : g_idx (P ⊓ toO S Xj) (((Λ ⊓ toO S Xs) ⊔ toO S I) ⊓ toO S Xj) = g_idx P ((Λ ⊓ toO S Xs) ⊔ toO S I) := by
    refine h_idx_congr inf_le_left inf_le_left ?_ ?_
    · intro v hv
      obtain ⟨xj, hxj, i, hi, rfl⟩ := dec v (hPX hv)
      have hi' : i ∈ toO S I := hi
      refine Submodule.add_mem_sup ⟨?_, hxj⟩ (Submodule.mem_sup_right hi')
      have e : xj = (xj + i) - i := by abel
      rw [e]; exact P.sub_mem hv (hIP hi')
    · rintro v ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
  have hF : Λ ⊓ toO S Xj ≤ ((Λ ⊓ toO S Xs) ⊔ toO S I) ⊓ toO S Xj :=
    fun x hx => ⟨Submodule.mem_sup_left ⟨hx.1, hXj hx.2⟩, hx.2⟩
  have e4 := g_idx_mul hF (inf_le_inf_right (toO S Xj) hAIP)
  rw [e1, ← e2, ← e3, e4]

theorem frame_determinant_bound (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (j : ℕ)
    (hX : Xsp F ≤ Xflag F j ⊔ Isp F.fl F'.fl) (hX' : Xsp F' ≤ Xflag F' j ⊔ Isp F.fl F'.fl)
    (hd : Xflag F j ⊓ Isp F.fl F'.fl = ⊥) (hd' : Xflag F' j ⊓ Isp F.fl F'.fl = ⊥)
    (hQX : t3Q F F' ⊓ Xsp F ≤ Isp F.fl F'.fl) (hQX' : t3Q F F' ⊓ Xsp F' ≤ Isp F.fl F'.fl) :
    (((idx S (t3L Λ F F') (lamOneLattice Λ F F') * idx S (t3BN Λ F F') (t3BD Λ F F')) *
      (idx S (XLam Λ F) ((Λ ⊓ toO S (Xflag F j)) ⊔ (Λ ⊓ toO S (Isp F.fl F'.fl))) *
        idx S (XLam Λ F') ((Λ ⊓ toO S (Xflag F' j)) ⊔ (Λ ⊓ toO S (Isp F.fl F'.fl)))) : ℕ) : ℝ) ≤
      latDet S ((Λ ⊓ toO S (Xflag F j)) ⊔ (Λ ⊓ toO S (Xflag F' j))) := by
  have hXjX : Xflag F j ≤ Xsp F := geo_Xa_le_X F.fl j
  have hXjX' : Xflag F' j ≤ Xsp F' := geo_Xa_le_X F'.fl j
  have hIQ := I_le_Q F F'
  set PX : Submodule (𝓞 E) S.V := (Lrep Λ F ⊔ toO S (t3Q F F')) ⊓ toO S (Xsp F) with hPXd
  set BX : Submodule (𝓞 E) S.V := (Λ ⊔ toO S (Xsp F)) ⊓ toO S (Xsp F') with hBXd
  have hI_PX : toO S (Isp F.fl F'.fl) ≤ PX := fun x hx => ⟨Submodule.mem_sup_right (hIQ hx), hx.1⟩
  have hI_BX : toO S (Isp F.fl F'.fl) ≤ BX := fun x hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩
  have hA_PX : Λ ⊓ toO S (Xsp F) ≤ PX := fun x hx =>
    ⟨Submodule.mem_sup_left ⟨hx.1, (a_mem_orth _ _).2 (fun w hw => b_X_X F hw hx.2)⟩, hx.2⟩
  have hA_BX : Λ ⊓ toO S (Xsp F') ≤ BX := fun x hx => ⟨Submodule.mem_sup_left hx.1, hx.2⟩
  have int : ∀ x ∈ PX, ∀ y ∈ BX, ∃ o : 𝓞 E, (o : E) = S.hT x y := by
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
    obtain ⟨l, hl, q, hq, rfl⟩ := Submodule.mem_sup.1 hx1
    obtain ⟨m, hm, x0, hx0, rfl⟩ := Submodule.mem_sup.1 hy1
    have hq' := (a_mem_orth _ _).1 (show q ∈ orth S (Xsp F ⊔ Xsp F') from hq)
    have hx0' : x0 ∈ Xsp F := hx0
    have hx2' : l + q ∈ Xsp F := hx2
    have hy2' : m + x0 ∈ Xsp F' := hy2
    have h1 : S.hT (l + q) x0 = 0 := b_X_X F hx2' hx0'
    have h2 : S.hT q (m + x0) = 0 := p_symm_zero S (hq' _ (Submodule.mem_sup_right hy2'))
    have h3 : S.hT q x0 = 0 := p_symm_zero S (hq' _ (Submodule.mem_sup_left hx0'))
    have h4 : S.hT q m = 0 := by rw [map_add, h3, add_zero] at h2; exact h2
    have e : S.hT (l + q) (m + x0) = S.hT l m := by
      rw [map_add, h1, add_zero, LinearMap.map_add₂, h4, add_zero]
    rw [e]
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (i_int Λ hu hl.1 hm)
    exact ⟨o, ho⟩
  have hdisj : Xflag F j ⊓ Xflag F' j = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨h1, h2⟩
    have h3 : x ∈ Xflag F j ⊓ Isp F.fl F'.fl := ⟨h1, hXjX h1, hXjX' h2⟩
    rw [hd] at h3; exact h3
  have nd : (Xflag F j ⊔ Xflag F' j) ⊓ orth S (Xflag F j ⊔ Xflag F' j) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨h1, h2⟩
    have h2' := (a_mem_orth _ _).1 h2
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.1 h1
    have haQ : a ∈ t3Q F F' := by
      rw [t3Q, a_mem_orth]
      intro w hw
      obtain ⟨v, hv, v', hv', rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨y, hy, i, hi, rfl⟩ := Submodule.mem_sup.1 (hX' hv')
      have k1 : S.hT v a = 0 := b_X_X F hv (hXjX ha)
      have k2 : S.hT i a = 0 := b_X_X F hi.1 (hXjX ha)
      have k3 : S.hT y a = 0 := by
        have k4 := h2' y (Submodule.mem_sup_right hy)
        rw [map_add, b_X_X F' (hXjX' hy) (hXjX' ha'), add_zero] at k4
        exact k4
      rw [LinearMap.map_add₂, LinearMap.map_add₂, k1, k2, k3]; simp
    have haQ' : a' ∈ t3Q F F' := by
      rw [t3Q, a_mem_orth]
      intro w hw
      obtain ⟨v, hv, v', hv', rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨y, hy, i, hi, rfl⟩ := Submodule.mem_sup.1 (hX hv)
      have k1 : S.hT v' a' = 0 := b_X_X F' hv' (hXjX' ha')
      have k2 : S.hT i a' = 0 := b_X_X F' hi.2 (hXjX' ha')
      have k3 : S.hT y a' = 0 := by
        have k4 := h2' y (Submodule.mem_sup_left hy)
        rw [map_add, b_X_X F (hXjX hy) (hXjX ha), zero_add] at k4
        exact k4
      rw [LinearMap.map_add₂, LinearMap.map_add₂, k1, k2, k3]; simp
    have ha0 : a ∈ Xflag F j ⊓ Isp F.fl F'.fl := ⟨ha, hQX ⟨haQ, hXjX ha⟩⟩
    have ha0' : a' ∈ Xflag F' j ⊓ Isp F.fl F'.fl := ⟨ha', hQX' ⟨haQ', hXjX' ha'⟩⟩
    rw [hd] at ha0
    rw [hd'] at ha0'
    rw [(Submodule.mem_bot E).1 ha0, (Submodule.mem_bot E).1 ha0', add_zero]
    exact Submodule.zero_mem _
  set N0 : Submodule (𝓞 E) S.V := (Λ ⊓ toO S (Xflag F j)) ⊔ (Λ ⊓ toO S (Xflag F' j)) with hN0
  set M : Submodule (𝓞 E) S.V := (PX ⊓ toO S (Xflag F j)) ⊔ (BX ⊓ toO S (Xflag F' j)) with hM
  have hF1 : Λ ⊓ toO S (Xflag F j) ≤ PX ⊓ toO S (Xflag F j) := fun x hx => ⟨hA_PX ⟨hx.1, hXjX hx.2⟩, hx.2⟩
  have hF2 : Λ ⊓ toO S (Xflag F' j) ≤ BX ⊓ toO S (Xflag F' j) := fun x hx => ⟨hA_BX ⟨hx.1, hXjX' hx.2⟩, hx.2⟩
  have hN0M : N0 ≤ M := sup_le_sup hF1 hF2
  have sN0 : spanE S N0 = Xflag F j ⊔ Xflag F' j := by
    unfold spanE
    rw [hN0, a_span_sup, a_span_inf Λ hΛ, a_span_inf Λ hΛ]
  have hMU : M ≤ toO S (Xflag F j ⊔ Xflag F' j) :=
    sup_le (fun x hx => Submodule.mem_sup_left hx.2) (fun x hx => Submodule.mem_sup_right hx.2)
  have sM : spanE S M = Xflag F j ⊔ Xflag F' j :=
    le_antisymm (h_span_le hMU) (sN0 ▸ Submodule.span_mono hN0M)
  have intM : ∀ x ∈ M, ∀ y ∈ M, ∃ o : 𝓞 E, (o : E) = S.hT x y := by
    intro x hx y hy
    obtain ⟨p, hp, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨p', hp', b', hb', rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨o1, ho1⟩ := int p hp.1 b' hb'.1
    obtain ⟨o2, ho2⟩ := g_hT_swap_int g_starInt (int p' hp'.1 b hb.1)
    refine ⟨o1 + o2, ?_⟩
    have z1 : S.hT p p' = 0 := b_X_X F hp.1.2 hp'.1.2
    have z2 : S.hT b b' = 0 := b_X_X F' hb.1.2 hb'.1.2
    rw [LinearMap.map_add₂, map_add, map_add, z1, z2, ← ho1, ← ho2]
    push_cast
    ring
  have fN0 : N0.FG := (g_fg_of_le Λ hΛ inf_le_left).sup (g_fg_of_le Λ hΛ inf_le_left)
  obtain ⟨fdN, -, -⟩ := g_dual_facts g_starInt nd fN0 sN0
  have hMdN : M ≤ dualIn S N0 := fun x hx =>
    g_mem_dualIn.2 ⟨fun y hy => intM y (hN0M hy) x hx, by rw [sN0]; exact hMU hx⟩
  have fM : M.FG := g_fg_le fdN hMdN
  have logDerivLAtOne : latDet S N0 = latDet S M * (g_idx M N0 : ℝ) :=
    g_detIndexG g_starInt M N0 hN0M fM (sM.trans sN0.symm) (by rw [sM]; exact nd)
  obtain ⟨fdM, sdM, -⟩ := g_dual_facts g_starInt nd fM sM
  have hMM : M ≤ dualIn S M := fun x hx =>
    g_mem_dualIn.2 ⟨fun y hy => intM y hy x hx, by rw [sM]; exact hMU hx⟩
  have hdet1 : 1 ≤ latDet S M := by
    have g := g_genIdx_via fdM fM hMM le_rfl (g_Comm_of_span fdM (by rw [sdM, sM])) (g_Comm_of_span fM le_rfl)
    have p1 : 0 < g_idx M M := g_idx_pos fM (g_Comm_of_span fM le_rfl)
    have p2 : 0 < g_idx (dualIn S M) M := g_idx_pos fdM (g_Comm_of_span fdM (by rw [sdM, sM]))
    have h1 : g_idx M M = 1 := by
      have h2 := g_idx_mul (le_refl M) (le_refl M)
      exact Nat.eq_of_mul_eq_mul_left p1 (by rw [h2, mul_one])
    show 1 ≤ Real.sqrt (genIdx S (dualIn S M) M)
    rw [g, h1, Nat.cast_one, div_one, Real.one_le_sqrt]
    exact_mod_cast p2
  have hsup : g_idx M N0 = g_idx (PX ⊓ toO S (Xflag F j)) (Λ ⊓ toO S (Xflag F j)) *
      g_idx (BX ⊓ toO S (Xflag F' j)) (Λ ⊓ toO S (Xflag F' j)) :=
    h_idx_sup hdisj inf_le_right hF1 inf_le_right hF2
  have side1 := side_index_identity Λ (Xsp F) (Xflag F j) (Isp F.fl F'.fl) hXjX inf_le_left hX hd PX hI_PX inf_le_right hA_PX
  have side2 := side_index_identity Λ (Xsp F') (Xflag F' j) (Isp F.fl F'.fl) hXjX' inf_le_right hX' hd' BX hI_BX inf_le_right hA_BX
  have pos : 0 < g_idx M N0 := g_idx_pos fM (g_Comm_of_span fM (by rw [sM, sN0]))
  rw [hsup, ← side1, ← side2] at pos
  have nz1 : g_idx PX ((Λ ⊓ toO S (Xsp F)) ⊔ toO S (Isp F.fl F'.fl)) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul pos.ne')
  have nz2 : g_idx BX ((Λ ⊓ toO S (Xsp F')) ⊔ toO S (Isp F.fl F'.fl)) ≠ 0 :=
    right_ne_zero_of_mul (right_ne_zero_of_mul pos.ne')
  have le1 : idx S (t3L Λ F F') (lamOneLattice Λ F F') ≤ g_idx PX ((Λ ⊓ toO S (Xsp F)) ⊔ toO S (Isp F.fl F'.fl)) := by
    refine lattice_index_le_of_map (fun y x => x ∈ Xsp F ∧ y + x ∈ Λ) nz1 ?_ ?_
    · rintro y ⟨⟨h1, -⟩, hyQ⟩
      obtain ⟨l, hl, x0, hx0, rfl⟩ := Submodule.mem_sup.1 h1
      have hx0' : x0 ∈ Xsp F := hx0
      refine ⟨-x0, ⟨?_, Submodule.neg_mem _ hx0'⟩, Submodule.neg_mem _ hx0', by simpa using hl.1⟩
      have e : -x0 = l + -(l + x0) := by abel
      rw [e]
      exact Submodule.add_mem_sup hl (Submodule.neg_mem _ hyQ)
    · rintro y₁ hy₁ y₂ hy₂ x₁ x₂ ⟨-, k₁⟩ ⟨-, k₂⟩ hx
      obtain ⟨a, ha, i, hi, e⟩ := Submodule.mem_sup.1 hx
      have hi' : i ∈ Isp F.fl F'.fl := hi
      have hμ : (y₁ - y₂) + i ∈ Λ := by
        have e2 : (y₁ - y₂) + i = (y₁ + x₁) - (y₂ + x₂) - a := by
          have e3 : i = (x₁ - x₂) - a := by rw [← e]; abel
          rw [e3]; abel
        rw [e2]
        exact Λ.sub_mem (Λ.sub_mem k₁ k₂) ha.1
      have hμQ : (y₁ - y₂) + i ∈ t3Q F F' :=
        Submodule.add_mem _ (Submodule.sub_mem _ hy₁.2 hy₂.2) (hIQ hi')
      have e4 : y₁ - y₂ = ((y₁ - y₂) + i) + -i := by abel
      rw [e4]
      exact Submodule.add_mem_sup ⟨hμ, hμQ⟩ (Submodule.neg_mem _ hi)
  have le2 : idx S (t3BN Λ F F') (t3BD Λ F F') ≤ g_idx BX ((Λ ⊓ toO S (Xsp F')) ⊔ toO S (Isp F.fl F'.fl)) := by
    refine lattice_index_le_of_map (fun b x' => x' ∈ Xsp F' ∧ b + x' ∈ Xsp F) nz2 ?_ ?_
    · rintro b ⟨hb1, hb2⟩
      obtain ⟨x, hx, x'', hx'', rfl⟩ := Submodule.mem_sup.1 hb2
      refine ⟨-x'', ⟨?_, Submodule.neg_mem _ hx''⟩, Submodule.neg_mem _ hx'', by simpa using hx⟩
      have e : -x'' = -(x + x'') + x := by abel
      rw [e]
      exact Submodule.add_mem_sup (Λ.neg_mem hb1) hx
    · rintro b₁ hb₁ b₂ hb₂ x₁ x₂ ⟨-, k₁⟩ ⟨-, k₂⟩ hx
      obtain ⟨a', ha', i, hi, e⟩ := Submodule.mem_sup.1 hx
      have hi' : i ∈ Isp F.fl F'.fl := hi
      have hA : (b₁ - b₂) + a' ∈ XLam Λ F := by
        refine ⟨Λ.add_mem (Λ.sub_mem hb₁.1 hb₂.1) ha'.1, ?_⟩
        have e2 : (b₁ - b₂) + a' = (b₁ + x₁) - (b₂ + x₂) - i := by
          have e3 : a' = (x₁ - x₂) - i := by rw [← e]; abel
          rw [e3]; abel
        show (b₁ - b₂) + a' ∈ Xsp F
        rw [e2]
        exact Submodule.sub_mem _ (Submodule.sub_mem _ k₁ k₂) hi'.1
      have e4 : b₁ - b₂ = ((b₁ - b₂) + a') + -a' := by abel
      rw [e4]
      exact Submodule.add_mem_sup hA (Submodule.neg_mem _ ha')
  have hnat : (idx S (t3L Λ F F') (lamOneLattice Λ F F') * idx S (t3BN Λ F F') (t3BD Λ F F')) *
      (idx S (XLam Λ F) ((Λ ⊓ toO S (Xflag F j)) ⊔ (Λ ⊓ toO S (Isp F.fl F'.fl))) *
        idx S (XLam Λ F') ((Λ ⊓ toO S (Xflag F' j)) ⊔ (Λ ⊓ toO S (Isp F.fl F'.fl)))) ≤ g_idx M N0 := by
    rw [hsup, ← side1, ← side2]
    calc _ ≤ (g_idx PX ((Λ ⊓ toO S (Xsp F)) ⊔ toO S (Isp F.fl F'.fl)) *
          g_idx BX ((Λ ⊓ toO S (Xsp F')) ⊔ toO S (Isp F.fl F'.fl))) *
        (idx S (XLam Λ F) ((Λ ⊓ toO S (Xflag F j)) ⊔ (Λ ⊓ toO S (Isp F.fl F'.fl))) *
          idx S (XLam Λ F') ((Λ ⊓ toO S (Xflag F' j)) ⊔ (Λ ⊓ toO S (Isp F.fl F'.fl)))) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul le1 le2)
      _ = _ := by
          show _ = g_idx (XLam Λ F) _ * _ * (g_idx (XLam Λ F') _ * _)
          unfold idx g_idx
          ring
  rw [logDerivLAtOne]
  calc _ ≤ (g_idx M N0 : ℝ) := by exact_mod_cast hnat
    _ ≤ latDet S M * (g_idx M N0 : ℝ) := le_mul_of_one_le_left (Nat.cast_nonneg _) hdet1

end Det

section RecDet

variable {D : D7} (X : TermTie D)

def b1T' {u : D.what₂.Word} (t : D.s.Term u u) : ℕ :=
  idx (hS D) (XLam (X.abelian₂ t) (X.fl' t))
    ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl' t) (LatticeIndexAndWeightTheory.jOf X t))) ⊔ (X.abelian₂ t ⊓ toO (hS D) (LatticeIndexAndWeightTheory.Iof X t)))

def FrameDeterminantBound {u : D.what₂.Word} (t : D.s.Term u u) : Prop :=
  latDet (hS D) ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl t) (LatticeIndexAndWeightTheory.jOf X t))) ⊔
    (X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl' t) (LatticeIndexAndWeightTheory.jOf X t)))) ≤ LatticeIndexAndWeightTheory.DelJ X t

def BOneComparison {u : D.what₂.Word} (t : D.s.Term u u) : Prop := LatticeIndexAndWeightTheory.b1T X t ≤ b1T' X t

theorem discriminant_of_determinant {u : D.what₂.Word} (t : D.s.Term u u) (h : LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t) (hD : FrameDeterminantBound X t) (hB : BOneComparison X t) :
    DiscriminantBound X t := by
  have hΛ := (X.fixed t).1
  have hu := (X.fixed t).2.1
  obtain ⟨j, hj, c, hN⟩ := nf_core X t h.1 h.2.1
  obtain ⟨-, -, g3, -, g5, g6⟩ := nf_gen _ _ _ _ j hj c hN
  have hfin := hN.1.2.1
  rw [nf_II] at hfin
  have hjo : LatticeIndexAndWeightTheory.jOf X t = j := by
    unfold LatticeIndexAndWeightTheory.jOf LatticeIndexAndWeightTheory.Iof
    rw [hfin]; omega
  obtain ⟨hc, -, -, -, hIj, hIj', hXe, hXe', -⟩ := hN.1
  rw [nf_II, nf_Xa] at hIj hIj'
  rw [nf_X, nf_Xa, nf_II] at hXe hXe'
  have hd : Xflag (X.fl t) j ⊓ Isp (X.fl t).fl (X.fl' t).fl = ⊥ := by rw [inf_comm]; exact hIj
  have hd' : Xflag (X.fl' t) j ⊓ Isp (X.fl t).fl (X.fl' t).fl = ⊥ := by rw [inf_comm]; exact hIj'
  have hQX := Q_inf_X_le_I (X.fl t) (X.fl' t) c g3.1 g5.1
  have hzc' : (X.fl t).fl.z - c⁻¹ • (X.fl' t).fl.z ∈ Xsp (X.fl' t) ⊔ Xsp (X.fl t) := by
    have e : (X.fl t).fl.z - c⁻¹ • (X.fl' t).fl.z = (-c⁻¹) • ((X.fl' t).fl.z - c • (X.fl t).fl.z) := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hc, neg_smul, neg_smul, one_smul]; abel
    rw [e, sup_comm]
    exact Submodule.smul_mem _ _ g3.1
  have hk' : perpS (hS D) (Xplus (X.fl' t) ⊔ Xplus (X.fl t)) ⊓ Xsp (X.fl' t) = Isp (X.fl' t).fl (X.fl t).fl := by
    rw [sup_comm, g6.1]; exact inf_comm _ _
  have hQX'0 := Q_inf_X_le_I (X.fl' t) (X.fl t) c⁻¹ hzc' hk'
  have hQX' : t3Q (X.fl t) (X.fl' t) ⊓ Xsp (X.fl' t) ≤ Isp (X.fl t).fl (X.fl' t).fl := by
    intro x hx
    have hx' : x ∈ t3Q (X.fl' t) (X.fl t) ⊓ Xsp (X.fl' t) := by
      refine ⟨?_, hx.2⟩
      have h1 := hx.1
      unfold t3Q at h1 ⊢
      rw [sup_comm]; exact h1
    have h2 := hQX'0 hx'
    exact ⟨h2.2, h2.1⟩
  have key := frame_determinant_bound (X.abelian₂ t) hΛ hu (X.fl t) (X.fl' t) j hXe.le hXe'.le hd hd' hQX hQX'
  have hb := (lattice_indices_pos X t h).1
  unfold FrameDeterminantBound at hD
  unfold BOneComparison b1T' at hB
  unfold DiscriminantBound
  rw [hjo] at hD hB
  have hb1 : LatticeIndexAndWeightTheory.b1T X t = idx (hS D) (XLam (X.abelian₂ t) (X.fl t))
      ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl t) j)) ⊔ (X.abelian₂ t ⊓ toO (hS D) (Isp (X.fl t).fl (X.fl' t).fl))) := by
    unfold LatticeIndexAndWeightTheory.b1T; rw [hjo]; rfl
  rw [hb1] at hb hB ⊢
  have hbR : (0 : ℝ) < (idx (hS D) (XLam (X.abelian₂ t) (X.fl t))
      ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl t) j)) ⊔ (X.abelian₂ t ⊓ toO (hS D) (Isp (X.fl t).fl (X.fl' t).fl))) : ℝ) := by
    exact_mod_cast hb
  rw [le_div_iff₀ (by positivity)]
  have hBR : (idx (hS D) (XLam (X.abelian₂ t) (X.fl t))
      ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl t) j)) ⊔ (X.abelian₂ t ⊓ toO (hS D) (Isp (X.fl t).fl (X.fl' t).fl))) : ℝ) ≤
      (idx (hS D) (XLam (X.abelian₂ t) (X.fl' t))
      ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl' t) j)) ⊔ (X.abelian₂ t ⊓ toO (hS D) (LatticeIndexAndWeightTheory.Iof X t))) : ℝ) := by exact_mod_cast hB
  push_cast at key
  have hP : (0 : ℝ) ≤ (idx (hS D) (t3L (X.abelian₂ t) (X.fl t) (X.fl' t)) (lamOneLattice (X.abelian₂ t) (X.fl t) (X.fl' t)) : ℝ) *
      (idx (hS D) (t3BN (X.abelian₂ t) (X.fl t) (X.fl' t)) (t3BD (X.abelian₂ t) (X.fl t) (X.fl' t)) : ℝ) := by positivity
  calc _ = ((idx (hS D) (t3L (X.abelian₂ t) (X.fl t) (X.fl' t)) (lamOneLattice (X.abelian₂ t) (X.fl t) (X.fl' t)) : ℝ) *
        (idx (hS D) (t3BN (X.abelian₂ t) (X.fl t) (X.fl' t)) (t3BD (X.abelian₂ t) (X.fl t) (X.fl' t)) : ℝ)) *
        ((idx (hS D) (XLam (X.abelian₂ t) (X.fl t))
      ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl t) j)) ⊔ (X.abelian₂ t ⊓ toO (hS D) (Isp (X.fl t).fl (X.fl' t).fl))) : ℝ) *
        (idx (hS D) (XLam (X.abelian₂ t) (X.fl t))
      ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl t) j)) ⊔ (X.abelian₂ t ⊓ toO (hS D) (Isp (X.fl t).fl (X.fl' t).fl))) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBR hbR.le) hP
    _ ≤ _ := key
    _ ≤ _ := hD

theorem discriminant_first_part_of_frames
    (hD : ∀ u : D.what₂.Word, LatticeIndexAndWeightTheory.TieOK X u → ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t → FrameDeterminantBound X t ∧ BOneComparison X t) :
    LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X :=
  discriminant_first_part_of_bound X (fun u hu t ht => discriminant_of_determinant X t ht (hD u hu t ht).1 (hD u hu t ht).2)

end RecDet

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Same

variable (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)

theorem hypothesis_iff_K2_hypothesis : LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 ↔ NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 := Iff.rfl

theorem fifth_first_iff_second : LatticeIndexAndWeightTheory.RelativePresentationLiterature D large₂ C' Cl Cg cb Cu cT CT C0 ↔ NonGenericAndKTwoTheorems.Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 := Iff.rfl

theorem fifth_second_iff_third : LatticeIndexAndWeightTheory.PairsWithFiniteGroup D large₂ C' Cl Cg cb Cu cT CT C0 ↔ NonGenericAndKTwoTheorems.PointsLemma D large₂ C' Cl Cg cb Cu cT CT C0 := Iff.rfl

theorem off_relation_of_first_statement {D : D7} {large₂ : SizeData₂ D} (X : TermTie D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (h : LatticeIndexAndWeightTheory.Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0) (hH : NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0) : RelevantZeroTermsVanish D :=
  fun u u' hne t hr hG => ((h hH).2.1 u u' t hne hr hG).1

end Same

section Sizes

variable (D : D7) (large₂ : SizeData₂ D)

theorem log_scale_eq_L : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _

theorem one_lt_scale_L : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos

theorem two_le_scale_b : 2 ≤ large₂.sc.b := by
  have h1 := one_lt_scale_L D large₂
  have h2 : large₂.sc.L + 1 ≤ Real.exp large₂.sc.L := Real.add_one_le_exp _
  show 2 ≤ Real.exp large₂.sc.L
  linarith

theorem two_rank_add_two_eq_m : 2 * D.R.rS + 2 = D.R.m := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  simp only [Ranks.rS]; omega

theorem one_le_degree_f : 1 ≤ D.R.f := by
  have : 1 ≤ D.R.ord := D.R.ord_pos
  simp only [Ranks.f, Ranks.n]; omega

theorem prod_one_add_three_div_le_two (hfk : D.R.f ≤ D.R.k)
    (hg : ∀ i : Fin 2, ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g i : ℝ)) :
    (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f ≤ 2 := by
  have hk5 : (5 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m
    exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hb := two_le_scale_b D large₂
  have hkb : (D.R.k : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have hk0 : (0 : ℝ) < D.R.k := by linarith
  have h8 : (D.R.k : ℝ) * 12 ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    have h1 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := pow_le_pow_left₀ hk0.le hkb 8
    have h2 : (D.R.k : ℝ) * 12 ≤ (D.R.k : ℝ) ^ 8 := by
      have h3 : (12 : ℝ) ≤ (D.R.k : ℝ) ^ 7 := by
        calc (12 : ℝ) ≤ 5 ^ 7 := by norm_num
          _ ≤ (D.R.k : ℝ) ^ 7 := pow_le_pow_left₀ (by norm_num) hk5 7
      calc (D.R.k : ℝ) * 12 ≤ (D.R.k : ℝ) * (D.R.k : ℝ) ^ 7 := mul_le_mul_of_nonneg_left h3 hk0.le
        _ = (D.R.k : ℝ) ^ 8 := by ring
    linarith
  have hone : ∀ i : Fin 2, 1 + 3 / (D.host.g i : ℝ) ≤ Real.exp (1 / (4 * (D.R.k : ℝ))) := by
    intro i
    have hgi : (D.R.k : ℝ) * 12 ≤ (D.host.g i : ℝ) := le_trans h8 (hg i)
    have hgp : (0 : ℝ) < (D.host.g i : ℝ) := by nlinarith
    have h1 : 3 / (D.host.g i : ℝ) ≤ 1 / (4 * (D.R.k : ℝ)) := by
      rw [div_le_div_iff₀ hgp (by positivity)]
      nlinarith
    have h2 := Real.add_one_le_exp (1 / (4 * (D.R.k : ℝ)))
    linarith
  have hpos : ∀ i : Fin 2, 0 ≤ 1 + 3 / (D.host.g i : ℝ) := fun i => by positivity
  have hprod : ∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ)) ≤ Real.exp (1 / (2 * (D.R.k : ℝ))) := by
    rw [Fin.prod_univ_two]
    calc (1 + 3 / (D.host.g 0 : ℝ)) * (1 + 3 / (D.host.g 1 : ℝ))
        ≤ Real.exp (1 / (4 * (D.R.k : ℝ))) * Real.exp (1 / (4 * (D.R.k : ℝ))) :=
          mul_le_mul (hone 0) (hone 1) (hpos 1) (Real.exp_pos _).le
      _ = Real.exp (1 / (2 * (D.R.k : ℝ))) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
  calc (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f
      ≤ Real.exp (1 / (2 * (D.R.k : ℝ))) ^ D.R.f :=
        pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => hpos i) hprod _
    _ = Real.exp ((D.R.f : ℝ) * (1 / (2 * (D.R.k : ℝ)))) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (1 / 2) := by
        apply Real.exp_le_exp.2
        have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
    _ ≤ 2 := by
        have h := Real.exp_one_lt_d9
        have h2 : Real.exp (1 / 2) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
        have h3 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1 / 2 : ℝ)]

end Sizes

section Close

def k2C0 (C : ℝ) : ℝ := if h : 1 ≤ C then (Formalism.HermitianLatticeCounting.Final.S6.finalSum C h).choose else 0

def k2A (D : D7) (large₂ : SizeData₂ D) (C : ℝ) (j : ℕ) : ℝ :=
  Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L) * (C / D.R.k) ^ (j * (D.R.k - 1 - j) * D.R.f)

def k2B (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : ℝ := (∑ j ∈ Finset.Icc 1 D.R.rS, k2A D large₂ C j) ^ 2

theorem final_bound_closes (D : D7) (large₂ : SizeData₂ D) (C : ℝ) (hC : 1 ≤ C) (d : ℝ) (hd : 0 ≤ d)
    (hk : k2C0 C * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k) :
    2 * d * k2B D large₂ C ≤ d * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k)) := by
  have h := (Formalism.HermitianLatticeCounting.Final.S6.finalSum C hC).choose_spec.2 D.R.k D.R.rS D.R.f large₂.sc.b d (two_le_scale_b D large₂)
    (one_le_degree_f D) hd
  rw [two_rank_add_two_eq_m D, log_scale_eq_L D large₂] at h
  unfold k2C0 at hk
  rw [dif_pos hC] at hk
  exact h hk

end Close

section Main

variable {D : D7} {large₂ : SizeData₂ D} (X : TermTie D)

def RowPairWeightBound (u : D.what₂.Word) (Q : D.s.Pair u u → Prop) (M B : ℝ) : Prop :=
  ∀ S : Finset (D.s.Pair u u), (∀ p ∈ S, Q p) → ∑ p ∈ S, wP X p ≤ M * dimPi (hc := D.hcW) u * B

def k2Q (D : D7) (u : D.what₂.Word) (Φ : Set (D.s.Term u u)) (p : D.s.Pair u u) : Prop := p ∈ pairsIn D.s Φ

def PairBoundOnFamily (D : D7) (u : D.what₂.Word) (Φ : Set (D.s.Term u u)) : Prop :=
  Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) ∧
    (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f * gaG D * (∑' p : pairsIn D.s Φ, D.s.pval p.1).re ≤
      (D.duS u : ℝ) * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))

theorem pair_bound_on_all_iff (D : D7) (u : D.what₂.Word) : PairBoundOnFamily D u (NonGenericAndKTwoTheorems.TermsPP D u u) ↔ TheoremK2PairBound D u := Iff.rfl

def k2G0 (D : D7) (u : D.what₂.Word) : Set (D.s.Term u u) := {t | LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t}

theorem summable_of_row_bound (u : D.what₂.Word) (Φ : Set (D.s.Term u u)) {M B : ℝ}
    (hM : gaG D * M * dimPi (hc := D.hcW) u = D.duS u) (hR : RowPairWeightBound X u (k2Q D u Φ) M B) :
    Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) ∧
      gaG D * ∑' p : pairsIn D.s Φ, ‖D.s.pval p.1‖ ≤ (D.duS u : ℝ) * B := by
  have hfin : ∀ s : Finset (pairsIn D.s Φ),
      ∑ p ∈ s, ‖D.s.pval p.1‖ ≤ M * dimPi (hc := D.hcW) u * B := by
    intro s
    have h := hR (s.map (Function.Embedding.subtype _)) (by
      intro p hp
      obtain ⟨q, _, rfl⟩ := Finset.mem_map.1 hp
      exact q.2)
    rw [Finset.sum_map] at h
    exact le_trans (Finset.sum_le_sum fun p _ => norm_pval_le X p.1) h
  have hs : Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hfin
  refine ⟨hs, ?_⟩
  calc gaG D * ∑' p : pairsIn D.s Φ, ‖D.s.pval p.1‖
      ≤ gaG D * (M * dimPi (hc := D.hcW) u * B) :=
        mul_le_mul_of_nonneg_left (hs.tsum_le_of_sum_le hfin) (gaG_nonneg D)
    _ = (D.duS u : ℝ) * B := by rw [← hM]; ring

theorem pair_bound_of_row_bound {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0)
    (u : D.what₂.Word) (Φ : Set (D.s.Term u u)) {M C : ℝ} (hC : 1 ≤ C)
    (hk : k2C0 C * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k)
    (hM : gaG D * M * dimPi (hc := D.hcW) u = D.duS u)
    (hR : RowPairWeightBound X u (k2Q D u Φ) M (k2B D large₂ C)) : PairBoundOnFamily D u Φ := by
  obtain ⟨hs, hb⟩ := summable_of_row_bound X u Φ hM hR
  refine ⟨hs, ?_⟩
  have hfk : D.R.f ≤ D.R.k := hH.1.1.2.2.2.1
  have hP2 := prod_one_add_three_div_le_two D large₂ hfk (fun i => (hH.2.2.1 i).1)
  have hP0 : 0 ≤ (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f :=
    pow_nonneg (Finset.prod_nonneg fun i _ => by positivity) _
  have hd : (0 : ℝ) ≤ D.duS u := Nat.cast_nonneg _
  have hB0 : 0 ≤ k2B D large₂ C := by unfold k2B; positivity
  have hre : (∑' p : pairsIn D.s Φ, D.s.pval p.1).re ≤
      ∑' p : pairsIn D.s Φ, ‖D.s.pval p.1‖ :=
    le_trans (Complex.re_le_norm _) (norm_tsum_le_tsum_norm hs)
  calc (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f * gaG D *
        (∑' p : pairsIn D.s Φ, D.s.pval p.1).re
      = (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f *
          (gaG D * (∑' p : pairsIn D.s Φ, D.s.pval p.1).re) := by ring
    _ ≤ (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f * ((D.duS u : ℝ) * k2B D large₂ C) :=
        mul_le_mul_of_nonneg_left
          (le_trans (mul_le_mul_of_nonneg_left hre (gaG_nonneg D)) hb) hP0
    _ ≤ 2 * ((D.duS u : ℝ) * k2B D large₂ C) := mul_le_mul_of_nonneg_right hP2 (mul_nonneg hd hB0)
    _ = 2 * (D.duS u : ℝ) * k2B D large₂ C := by ring
    _ ≤ _ := final_bound_closes D large₂ C hC _ hd hk

theorem pair_bound_of_row_bound_hyp {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0)
    (u : D.what₂.Word) (Φ : Set (D.s.Term u u)) {M C : ℝ} (hC : 1 ≤ C) (hCl : k2C0 C ≤ Cl)
    (hM : gaG D * M * dimPi (hc := D.hcW) u = D.duS u)
    (hR : RowPairWeightBound X u (k2Q D u Φ) M (k2B D large₂ C)) : PairBoundOnFamily D u Φ := by
  refine pair_bound_of_row_bound X hH u Φ hC (le_trans ?_ hH.2.1) hM hR
  have hL : 0 ≤ large₂.sc.L := (lt_trans one_pos (one_lt_scale_L D large₂)).le
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 6 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCl hm) hL

theorem hs_norm_scalar_eq {u : D.what₂.Word} (t : D.s.Term u u) (s : ℂ)
    (h : X.Jt t = s • ContinuousLinearMap.id ℂ (X.Hpi u)) :
    aT X t = ‖s‖ * Real.sqrt (dimPi (hc := D.hcW) u) := by
  unfold aT
  rw [h, d_hsNormSq_eq]
  have h1 : ∀ i, ‖(s • ContinuousLinearMap.id ℂ (X.Hpi u)) (stdOrthonormalBasis ℂ (X.Hpi u) i)‖ ^ 2 = ‖s‖ ^ 2 := by
    intro i
    simp [norm_smul]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    X.Hpi_dim u, mul_comm, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

theorem pair_weight_of_scalars {u : D.what₂.Word} (p : D.s.Pair u u) (s' s'' : ℂ)
    (h' : X.Jt (D.s.pfst p) = s' • ContinuousLinearMap.id ℂ (X.Hpi u))
    (h'' : X.Jt (D.s.psnd p) = s'' • ContinuousLinearMap.id ℂ (X.Hpi u)) :
    wP X p = X.wRow p * (‖s'‖ * ‖s''‖) * dimPi (hc := D.hcW) u := by
  unfold wP
  rw [hs_norm_scalar_eq X _ s' h', hs_norm_scalar_eq X _ s'' h'']
  have hd : 0 ≤ dimPi (hc := D.hcW) u := by rw [← X.Hpi_dim u]; positivity
  have := Real.mul_self_sqrt hd
  calc X.wRow p * (‖s'‖ * Real.sqrt (dimPi (hc := D.hcW) u) * (‖s''‖ * Real.sqrt (dimPi (hc := D.hcW) u)))
      = X.wRow p * (‖s'‖ * ‖s''‖) * (Real.sqrt (dimPi (hc := D.hcW) u) * Real.sqrt (dimPi (hc := D.hcW) u)) := by ring
    _ = _ := by rw [this]

def IrrelevantAmplitudeZero (u : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u, D.s.Gterm t = 0 → ¬ D.s.relevant t → X.Jt t = 0

def k2QJ (u : D.what₂.Word) (j' j'' : ℕ) (p : D.s.Pair u u) : Prop :=
  LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.pfst p) ∧ LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.psnd p) ∧ LatticeIndexAndWeightTheory.jOf X (D.s.pfst p) = j' ∧ LatticeIndexAndWeightTheory.jOf X (D.s.psnd p) = j''

theorem hs_norm_zero_of_zero {u : D.what₂.Word} (t : D.s.Term u u) (h : X.Jt t = 0) : aT X t = 0 := by
  unfold aT
  rw [h, d_hsNormSq_eq]
  simp

open Classical in

theorem row_bound_of_rank_bounds (u : D.what₂.Word) (Φ : Set (D.s.Term u u)) {M : ℝ} (A : ℕ → ℝ)
    (hI : ∀ p ∈ pairsIn D.s Φ, (LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.pfst p) ∧ LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.psnd p)) ∨ wP X p = 0)
    (hj : ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t → 1 ≤ LatticeIndexAndWeightTheory.jOf X t)
    (hJ : ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, RowPairWeightBound X u (k2QJ X u j' j'') M (A j' * A j'')) :
    RowPairWeightBound X u (k2Q D u Φ) M ((∑ j ∈ Finset.Icc 1 D.R.rS, A j) ^ 2) := by
  intro S hS
  set I := Finset.Icc 1 D.R.rS with hIdef
  have key : ∀ p ∈ S, wP X p = ∑ j' ∈ I, ∑ j'' ∈ I, if k2QJ X u j' j'' p then wP X p else 0 := by
    intro p hp
    rcases hI p (hS p hp) with ⟨G1, G2⟩ | hz
    · have m1 : LatticeIndexAndWeightTheory.jOf X (D.s.pfst p) ∈ I := Finset.mem_Icc.2 ⟨hj _ G1, Nat.sub_le _ _⟩
      have m2 : LatticeIndexAndWeightTheory.jOf X (D.s.psnd p) ∈ I := Finset.mem_Icc.2 ⟨hj _ G2, Nat.sub_le _ _⟩
      rw [Finset.sum_eq_single (LatticeIndexAndWeightTheory.jOf X (D.s.pfst p)), Finset.sum_eq_single (LatticeIndexAndWeightTheory.jOf X (D.s.psnd p))]
      · rw [if_pos ⟨G1, G2, rfl, rfl⟩]
      · intro b _ hb
        exact if_neg (fun h => hb h.2.2.2.symm)
      · intro h; exact absurd m2 h
      · intro b _ hb
        exact Finset.sum_eq_zero fun c _ => if_neg (fun h => hb h.2.2.1.symm)
      · intro h; exact absurd m1 h
    · rw [hz]
      simp
  calc ∑ p ∈ S, wP X p = ∑ p ∈ S, ∑ j' ∈ I, ∑ j'' ∈ I, (if k2QJ X u j' j'' p then wP X p else 0) :=
        Finset.sum_congr rfl key
    _ = ∑ j' ∈ I, ∑ j'' ∈ I, ∑ p ∈ S, (if k2QJ X u j' j'' p then wP X p else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ j' ∈ I, ∑ j'' ∈ I, M * dimPi (hc := D.hcW) u * (A j' * A j'') := by
        refine Finset.sum_le_sum fun j' h' => Finset.sum_le_sum fun j'' h'' => ?_
        rw [← Finset.sum_filter]
        exact hJ j' h' j'' h'' _ (fun p hp => (Finset.mem_filter.1 hp).2)
    _ = M * dimPi (hc := D.hcW) u * (∑ j ∈ I, A j) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [Finset.mul_sum]

theorem split_identity_cell_pairs (u : D.what₂.Word) :
    ∀ p ∈ pairsIn D.s (k2G0 D u), (LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.pfst p) ∧ LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.psnd p)) ∨ wP X p = 0 :=
  fun _ hp => Or.inl hp

theorem split_all_pairs_identity_cell (u : D.what₂.Word) (hI : IrrelevantAmplitudeZero X u) :
    ∀ p ∈ pairsIn D.s (NonGenericAndKTwoTheorems.TermsPP D u u), (LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.pfst p) ∧ LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.psnd p)) ∨ wP X p = 0 := by
  rintro p ⟨⟨g1, i1⟩, ⟨g2, i2⟩⟩
  by_cases hr : D.s.relevant (D.s.pfst p) ∧ D.s.relevant (D.s.psnd p)
  · exact Or.inl ⟨⟨hr.1, g1, i1⟩, ⟨hr.2, g2, i2⟩⟩
  · right
    unfold wP
    rcases not_and_or.1 hr with h | h
    · rw [hs_norm_zero_of_zero X _ (hI _ g1 h)]; ring
    · rw [hs_norm_zero_of_zero X _ (hI _ g2 h)]; ring

end Main

section Abstract

open Classical in

theorem double_sum_weighted_le {P Λ : Type*} (S : Finset P) (w : P → ℝ) (l' l'' : P → Λ) (a' a'' e' e'' : Λ → ℝ) (M A' A'' : ℝ)
    (hM : 0 ≤ M) (ha' : ∀ x, 0 ≤ a' x) (ha'' : ∀ x, 0 ≤ a'' x) (he'' : ∀ x, 0 ≤ e'' x) (hA' : 0 ≤ A')
    (h1 : ∀ x y, ∑ p ∈ S.filter (fun p => l' p = x ∧ l'' p = y), w p ≤ M * (e' x * e'' y))
    (h2' : ∑ x ∈ S.image l', a' x * e' x ≤ A') (h2'' : ∑ y ∈ S.image l'', a'' y * e'' y ≤ A'') :
    ∑ p ∈ S, w p * (a' (l' p) * a'' (l'' p)) ≤ M * (A' * A'') := by
  have hmaps : ∀ p ∈ S, (l' p, l'' p) ∈ (S.image l') ×ˢ (S.image l'') := fun p hp =>
    Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_product]
  calc ∑ x ∈ S.image l', ∑ y ∈ S.image l'', ∑ p ∈ S with (l' p, l'' p) = (x, y), w p * (a' (l' p) * a'' (l'' p))
      ≤ ∑ x ∈ S.image l', ∑ y ∈ S.image l'', M * ((a' x * e' x) * (a'' y * e'' y)) := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        have e1 : ∑ p ∈ S with (l' p, l'' p) = (x, y), w p * (a' (l' p) * a'' (l'' p)) =
            (∑ p ∈ S.filter (fun p => l' p = x ∧ l'' p = y), w p) * (a' x * a'' y) := by
          rw [Finset.sum_mul]
          have : S.filter (fun p => (l' p, l'' p) = (x, y)) = S.filter (fun p => l' p = x ∧ l'' p = y) := by
            ext p; simp [Prod.ext_iff]
          rw [this]
          refine Finset.sum_congr rfl fun p hp => ?_
          obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
          rw [h1, h2]
        rw [e1]
        calc (∑ p ∈ S.filter (fun p => l' p = x ∧ l'' p = y), w p) * (a' x * a'' y)
            ≤ (M * (e' x * e'' y)) * (a' x * a'' y) :=
              mul_le_mul_of_nonneg_right (h1 x y) (mul_nonneg (ha' x) (ha'' y))
          _ = M * ((a' x * e' x) * (a'' y * e'' y)) := by ring
    _ = M * ((∑ x ∈ S.image l', a' x * e' x) * (∑ y ∈ S.image l'', a'' y * e'' y)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ ≤ M * (A' * A'') := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        exact mul_le_mul h2' h2'' (Finset.sum_nonneg fun y _ => mul_nonneg (ha'' y) (he'' y)) hA'

theorem label_real_inequality (k j : ℕ) (Q Del H S G1 G2 Cs Cp r3 : ℝ) (hQ : 0 ≤ Q) (hDel : 0 < Del) (hDH : Del ≤ H * S ^ 2)
    (hH : 1 ≤ H) (hS : 1 ≤ S) (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2)
    (hexp : ((j : ℝ) + 1) + Cp * k + r3 ≤ Cs * k) :
    (Q * Del ^ (-(((k : ℝ) - 1 - j) / 2)) * G1 * S ^ (-(Cs * k))) * (Del ^ ((k : ℝ) / 2) * G2 * S ^ (Cp * k)) ≤
      Q * G1 * G2 * H ^ (((j : ℝ) + 1) / 2) * S ^ (-r3) := by
  have hS0 : 0 < S := by linarith
  have hH0 : 0 < H := by linarith
  have e1 := Formalism.HermitianLatticeCounting.Final.S6.expIdentity k j Del hDel
  have e2 : Del ^ (((j : ℝ) + 1) / 2) ≤ H ^ (((j : ℝ) + 1) / 2) * S ^ ((j : ℝ) + 1) := by
    calc Del ^ (((j : ℝ) + 1) / 2) ≤ (H * S ^ 2) ^ (((j : ℝ) + 1) / 2) :=
          Real.rpow_le_rpow hDel.le hDH (by positivity)
      _ = H ^ (((j : ℝ) + 1) / 2) * (S ^ 2) ^ (((j : ℝ) + 1) / 2) := Real.mul_rpow hH0.le (by positivity)
      _ = H ^ (((j : ℝ) + 1) / 2) * S ^ ((j : ℝ) + 1) := by
          congr 1
          rw [← Real.rpow_natCast S 2, ← Real.rpow_mul hS0.le]
          congr 1; push_cast; ring
  have e3 : S ^ ((j : ℝ) + 1) * S ^ (-(Cs * k)) * S ^ (Cp * k) ≤ S ^ (-r3) := by
    rw [← Real.rpow_add hS0, ← Real.rpow_add hS0]
    exact Real.rpow_le_rpow_of_exponent_le hS (by linarith)
  have hSa : 0 ≤ S ^ (-(Cs * k)) * S ^ (Cp * k) := by positivity
  calc (Q * Del ^ (-(((k : ℝ) - 1 - j) / 2)) * G1 * S ^ (-(Cs * k))) * (Del ^ ((k : ℝ) / 2) * G2 * S ^ (Cp * k))
      = Q * G1 * G2 * (Del ^ ((k : ℝ) / 2) * Del ^ (-(((k : ℝ) - 1 - j) / 2))) * (S ^ (-(Cs * k)) * S ^ (Cp * k)) := by ring
    _ = Q * G1 * G2 * Del ^ (((j : ℝ) + 1) / 2) * (S ^ (-(Cs * k)) * S ^ (Cp * k)) := by rw [e1]
    _ ≤ Q * G1 * G2 * (H ^ (((j : ℝ) + 1) / 2) * S ^ ((j : ℝ) + 1)) * (S ^ (-(Cs * k)) * S ^ (Cp * k)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 (by positivity)) hSa
    _ = Q * G1 * G2 * H ^ (((j : ℝ) + 1) / 2) * (S ^ ((j : ℝ) + 1) * S ^ (-(Cs * k)) * S ^ (Cp * k)) := by ring
    _ ≤ Q * G1 * G2 * H ^ (((j : ℝ) + 1) / 2) * S ^ (-r3) :=
        mul_le_mul_of_nonneg_left e3 (by positivity)

def k2R0 (N : ℕ) : ℕ := if h : 1 ≤ N then (Formalism.HermitianLatticeCounting.Final.S6.ratioBound N h).choose else 0

theorem sum_over_coranks_real (N Cn k r f : ℕ) (b g NT D' D'' S' S'' : ℝ) (hN3 : 3 * Cn ≤ N) (hN : 11 ≤ N) (hb : 2 ≤ b) (hf : 1 ≤ f)
    (hlf : Real.log f ≤ (r : ℝ) ^ 2) (hk : k2R0 N * (2 * r + 2) ^ 2 ≤ k) (hg0 : 0 < g) (hg : ((k : ℝ) * b) ^ 8 ≤ g)
    (hS' : 1 ≤ S') (hS'' : 1 ≤ S'') (hD' : 0 ≤ D') (hD'' : 0 ≤ D'') (hNT : 0 ≤ NT)
    (hDH' : D' ≤ b ^ (N * (2 * r + 2) ^ 2 * f) * S' ^ 2) (hDH'' : D'' ≤ b ^ (N * (2 * r + 2) ^ 2 * f) * S'' ^ 2)
    (hNTH : NT ≤ b ^ (N * (2 * r + 2) ^ 2 * f)) :
    1 + ∑ s ∈ Finset.Icc 1 (k - 1), ((Cn : ℝ) / g) ^ (s * k * f) * (D' * D'' * NT) ^ (Cn * s) *
          ((Cn * s * f : ℕ) : ℝ) ^ (4 * s * f) +
        (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k *
          ((b ^ (N * (2 * r + 2) ^ 2 * f)) ^ (10 * k) * (S' * S'') ^ (10 * k)) ≤
      3 * (S' * S'') ^ ((2 * Cn + 10) * k) := by
  set Hn := b ^ (N * (2 * r + 2) ^ 2 * f) with hHn
  have hN1 : 1 ≤ N := by omega
  have hH1 : 1 ≤ Hn := one_le_pow₀ (by linarith)
  have hSS : 1 ≤ S' * S'' := by nlinarith
  have hratio : ((N : ℝ) / g) ^ (k * f) * Hn ^ N * ((N * k * f : ℕ) : ℝ) ^ (4 * f) ≤ 1 / 2 := by
    have h := (Formalism.HermitianLatticeCounting.Final.S6.ratioBound N hN1).choose_spec k r f b g hb hf hlf
    unfold k2R0 at hk
    rw [dif_pos hN1] at hk
    exact h hk hg
  have hmid : ∑ s ∈ Finset.Icc 1 (k - 1), ((Cn : ℝ) / g) ^ (s * k * f) * (D' * D'' * NT) ^ (Cn * s) *
      ((Cn * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ (S' * S'') ^ (2 * Cn * k) := by
    have hsum := Formalism.HermitianLatticeCounting.Final.S6.ratioSum N k f g Hn hg0 hH1 hratio
    calc _ ≤ ∑ s ∈ Finset.Icc 1 (k - 1), (((N : ℝ) / g) ^ (s * k * f) * Hn ^ (N * s) *
          ((N * s * f : ℕ) : ℝ) ^ (4 * s * f)) * (S' * S'') ^ (2 * Cn * k) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hsk : s ≤ k := by have := (Finset.mem_Icc.1 hs).2; omega
          have h1 := Formalism.HermitianLatticeCounting.Final.S6.pairsLoss Cn s k D' D'' NT Hn S' S'' hsk hH1 hS' hS'' hD' hD'' hNT hDH' hDH'' hNTH
          have h2 : Hn ^ (3 * Cn * s) ≤ Hn ^ (N * s) := pow_le_pow_right₀ hH1 (Nat.mul_le_mul_right s hN3)
          have hCN : (Cn : ℝ) ≤ N := by exact_mod_cast (by omega : Cn ≤ N)
          have h3 : ((Cn : ℝ) / g) ^ (s * k * f) ≤ ((N : ℝ) / g) ^ (s * k * f) :=
            pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hCN hg0.le) _
          have h4 : ((Cn * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ ((N * s * f : ℕ) : ℝ) ^ (4 * s * f) := by
            refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
            exact_mod_cast Nat.mul_le_mul_right f (Nat.mul_le_mul_right s (by omega : Cn ≤ N))
          have h5 : (D' * D'' * NT) ^ (Cn * s) ≤ Hn ^ (N * s) * (S' * S'') ^ (2 * Cn * k) :=
            le_trans h1 (mul_le_mul_of_nonneg_right h2 (by positivity))
          calc ((Cn : ℝ) / g) ^ (s * k * f) * (D' * D'' * NT) ^ (Cn * s) * ((Cn * s * f : ℕ) : ℝ) ^ (4 * s * f)
              ≤ ((N : ℝ) / g) ^ (s * k * f) * (Hn ^ (N * s) * (S' * S'') ^ (2 * Cn * k)) * ((N * s * f : ℕ) : ℝ) ^ (4 * s * f) :=
                mul_le_mul (mul_le_mul h3 h5 (by positivity) (by positivity)) h4 (by positivity) (by positivity)
            _ = _ := by ring
      _ = (∑ s ∈ Finset.Icc 1 (k - 1), ((N : ℝ) / g) ^ (s * k * f) * Hn ^ (N * s) *
          ((N * s * f : ℕ) : ℝ) ^ (4 * s * f)) * (S' * S'') ^ (2 * Cn * k) := by rw [Finset.sum_mul]
      _ ≤ 1 * (S' * S'') ^ (2 * Cn * k) := mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = _ := one_mul _
  have hlast : (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k * (Hn ^ (10 * k) * (S' * S'') ^ (10 * k)) ≤
      (S' * S'') ^ (10 * k) := by
    have h := Formalism.HermitianLatticeCounting.Final.S6.sEqKClose N k f g Hn NT (by omega) hg0 hH1 hNT hNTH hratio
    have h2 : Hn ^ (10 * k) ≤ Hn ^ ((N - 1) * k) := pow_le_pow_right₀ hH1 (Nat.mul_le_mul_right k (by omega))
    have h0 : 0 ≤ (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k := by positivity
    calc _ = ((2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k * Hn ^ (10 * k)) * (S' * S'') ^ (10 * k) := by ring
      _ ≤ ((2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k * Hn ^ ((N - 1) * k)) * (S' * S'') ^ (10 * k) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h0) (by positivity)
      _ ≤ 1 * (S' * S'') ^ (10 * k) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := one_mul _
  have e1 : (1 : ℝ) ≤ (S' * S'') ^ ((2 * Cn + 10) * k) := one_le_pow₀ hSS
  have e2 : (S' * S'') ^ (2 * Cn * k) ≤ (S' * S'') ^ ((2 * Cn + 10) * k) :=
    pow_le_pow_right₀ hSS (Nat.mul_le_mul_right k (by omega))
  have e3 : (S' * S'') ^ (10 * k) ≤ (S' * S'') ^ ((2 * Cn + 10) * k) :=
    pow_le_pow_right₀ hSS (Nat.mul_le_mul_right k (by omega))
  linarith

end Abstract

section Labels

variable {D : D7} (X : TermTie D) {u : D.what₂.Word}

def k2lab (t : D.s.Term u u) : ℕ → D.host.E :=
  fun l => if l ≤ LatticeIndexAndWeightTheory.jOf X t then Dl (X.fl t).fl (X.fl' t).fl l else 0

def k2ends (D : D7) (j : ℕ) (δ : ℕ → D.host.E) : Finset ℕ := by
  classical exact (Finset.Icc 1 j).filter (fun l => δ l ≠ 0)

def k2Del (D : D7) (j : ℕ) (δ : ℕ → D.host.E) : ℝ := (Nloc (ddS D) D.R.rS j (δ j) : ℝ)

def k2sg (D : D7) (H1 : ℝ) (j : ℕ) (δ : ℕ → D.host.E) (τ : D.what₂.Tau) : ℝ :=
  (k2ends D j δ).fold max 1 (fun l => absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS))

def k2S (D : D7) (H1 : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : ℝ := ∏ τ, k2sg D H1 j δ τ

theorem ends_eq_minor_ends (t : D.s.Term u u) : LatticeIndexAndWeightTheory.ends X t = k2ends D (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) := by
  unfold LatticeIndexAndWeightTheory.ends blockEnds k2ends k2lab
  ext l
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [if_pos h1.2]; exact h2⟩
  · rintro ⟨h1, h2⟩
    rw [if_pos h1.2] at h2
    exact ⟨h1, h2⟩

theorem sigma_eq_minor_sigma (t : D.s.Term u u) (H1 : ℝ) (τ : D.what₂.Tau) :
    LatticeIndexAndWeightTheory.sg X t H1 τ = k2sg D H1 (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) τ := by
  unfold LatticeIndexAndWeightTheory.sg k2sg
  rw [ends_eq_minor_ends]
  refine Finset.fold_congr fun l hl => ?_
  have hl' : l ≤ LatticeIndexAndWeightTheory.jOf X t := by
    classical
    unfold k2ends at hl
    exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hl).1).2
  unfold k2lab
  rw [if_pos hl']

theorem discriminant_eq_minor_norm (t : D.s.Term u u) : LatticeIndexAndWeightTheory.DelJ X t = k2Del D (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) := by
  unfold LatticeIndexAndWeightTheory.DelJ LatticeIndexAndWeightTheory.NDl k2Del k2lab
  rw [if_pos le_rfl]

theorem one_le_minor_sigma (H1 : ℝ) (j : ℕ) (δ : ℕ → D.host.E) (τ : D.what₂.Tau) : 1 ≤ k2sg D H1 j δ τ := by
  unfold k2sg
  exact (Finset.le_fold_max 1).2 (Or.inl le_rfl)

theorem one_le_sigma_product (H1 : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : 1 ≤ k2S D H1 j δ := by
  unfold k2S
  have h := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : D.what₂.Tau => (1 : ℝ)) (g := fun τ => k2sg D H1 j δ τ)
    (fun _ _ => zero_le_one) (fun τ _ => one_le_minor_sigma H1 j δ τ)
  simpa using h

theorem minor_norm_nonneg (j : ℕ) (δ : ℕ → D.host.E) : 0 ≤ k2Del D j δ := by
  unfold k2Del Nloc
  exact_mod_cast FractionalIdeal.absNorm_nonneg _

end Labels

section Steps

variable {D : D7} (large₂ : SizeData₂ D) (X : TermTie D)

def k2a (CH Cs C : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : ℝ :=
  (C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * k2Del D j δ ^ (-(((D.R.k : ℝ) - 1 - j) / 2)) *
    Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(Cs * D.R.k))

def k2e (CH Ch Cp : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : ℝ :=
  k2Del D j δ ^ ((D.R.k : ℝ) / 2) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) *
    k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (Cp * D.R.k)

def LabelledPairBound (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (u : D.what₂.Word) (M CH Ch Cp : ℝ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (S : Finset (D.s.Pair u u)),
    (∀ p ∈ S, k2QJ X u j' j'' p ∧ k2lab X (D.s.pfst p) = δ' ∧ k2lab X (D.s.psnd p) = δ'') →
    ∑ p ∈ S, X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p)) ≤ M * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')

def MinorCosetSum (u : D.what₂.Word) (CH Cc : ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
    (∀ δ ∈ T, ∃ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t ∧ LatticeIndexAndWeightTheory.jOf X t = j ∧ k2lab X t = δ) →
    ∑ δ ∈ T, k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
      Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ))

def k2A1 (C Ch Cc : ℝ) (j : ℕ) : ℝ :=
  (C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
    Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) *
    Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ))

theorem one_le_height_bound {C : ℝ} (hC : 0 ≤ C) : 1 ≤ Hb large₂.sc.b C D.R.m D.R.f := by
  unfold Hb
  exact Real.one_le_rpow (by linarith [two_le_scale_b D large₂]) (by positivity)

theorem amplitude_label_nonneg {CH Cs C : ℝ} (hC : 0 ≤ C) (j : ℕ) (δ : ℕ → D.host.E) : 0 ≤ k2a large₂ CH Cs C j δ := by
  unfold k2a
  have h1 : 0 ≤ C / (D.R.k : ℝ) := by positivity
  have h2 := minor_norm_nonneg (D := D) j δ
  have h3 : 0 ≤ Hb large₂.sc.b C D.R.m D.R.f := by linarith [one_le_height_bound large₂ hC]
  have h4 : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by linarith [one_le_sigma_product (D := D) (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ]
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)) (Real.rpow_nonneg h3 _))
    (Real.rpow_nonneg h4 _)

theorem amplitude_exponent_nonneg {CH Ch Cp : ℝ} (hC : 0 ≤ Ch) (j : ℕ) (δ : ℕ → D.host.E) : 0 ≤ k2e large₂ CH Ch Cp j δ := by
  unfold k2e
  have h2 := minor_norm_nonneg (D := D) j δ
  have h3 : 0 ≤ Hb large₂.sc.b Ch D.R.m D.R.f := by linarith [one_le_height_bound large₂ hC]
  have h4 : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by linarith [one_le_sigma_product (D := D) (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ]
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg h2 _) (Real.rpow_nonneg h3 _)) (Real.rpow_nonneg h4 _)

def AmplitudeNormBound (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (u : D.what₂.Word) (CH Cs C : ℝ) : Prop :=
  ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t →
    aT X t ≤ Real.sqrt (dimPi (hc := D.hcW) u) * (om u t * k2a large₂ CH Cs C (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t))

theorem coset_amplitude_of_norm_form {om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ} {CH Cs C : ℝ} (h2 : LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C)
    {u : D.what₂.Word} (hT : LatticeIndexAndWeightTheory.TieOK X u) : AmplitudeNormBound large₂ X om u CH Cs C := by
  intro t hG
  have h := (h2 u hT t hG).1
  rw [discriminant_eq_minor_norm, X.Hpi_dim u] at h
  simp only [sigma_eq_minor_sigma] at h
  rw [Real.finsetProd_rpow _ _ (fun τ _ => by linarith [one_le_minor_sigma (D := D) (large₂.sc.b ^ (CH * (D.R.m : ℝ))) (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) τ])] at h
  unfold k2a k2S aT
  calc _ ≤ _ := h
    _ = _ := by ring

theorem minor_norm_le_height {om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ} {CH Cs C : ℝ} (h2 : LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C)
    {u : D.what₂.Word} (hT : LatticeIndexAndWeightTheory.TieOK X u) (t : D.s.Term u u) (hG : LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t) :
    k2Del D (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) ≤
      Hb large₂.sc.b C D.R.m D.R.f * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) ^ 2 := by
  have h := (h2 u hT t hG).2.1
  rw [discriminant_eq_minor_norm] at h
  simp only [sigma_eq_minor_sigma] at h
  rw [Finset.prod_pow] at h
  exact h

theorem minor_norm_pos (h3 : LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X) {u : D.what₂.Word} (hT : LatticeIndexAndWeightTheory.TieOK X u) (t : D.s.Term u u) (hG : LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t) :
    0 < k2Del D (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) := by
  obtain ⟨hb, hg, hi, h⟩ := h3 u hT t hG
  rw [discriminant_eq_minor_norm] at h
  have hb' : (0 : ℝ) < (LatticeIndexAndWeightTheory.b1T X t : ℝ) ^ 2 := by positivity
  have h1 : (0 : ℝ) < (LatticeIndexAndWeightTheory.gT X t : ℝ) * (LatticeIndexAndWeightTheory.iT X t : ℝ) ^ 2 := by positivity
  have h2 := lt_of_lt_of_le h1 h
  by_contra hn
  have : k2Del D (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) / (LatticeIndexAndWeightTheory.b1T X t : ℝ) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) hb'.le
  linarith

theorem label_sum_bound {om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ} {CH Cs C Ch Cp Cc : ℝ} (hC : 0 ≤ C) (hCp : 0 ≤ Ch)
    (hCs : Cp + 4 ≤ Cs) (h2 : LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C) (h3 : LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X) {u : D.what₂.Word} (hT : LatticeIndexAndWeightTheory.TieOK X u)
    (hc : MinorCosetSum large₂ X u CH Cc) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.rS) (T : Finset (ℕ → D.host.E))
    (hTm : ∀ δ ∈ T, ∃ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t ∧ LatticeIndexAndWeightTheory.jOf X t = j ∧ k2lab X t = δ) :
    ∑ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ ≤ k2A1 large₂ C Ch Cc j := by
  set Q := (C / (D.R.k : ℝ)) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) with hQ
  set G1 := Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) with hG1
  set G2 := Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) with hG2
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg (by positivity) _
  have hH := one_le_height_bound large₂ hC (D := D)
  have hHp := one_le_height_bound large₂ hCp (D := D)
  have hG10 : 0 ≤ G1 := Real.rpow_nonneg (by linarith) _
  have hG20 : 0 ≤ G2 := Real.rpow_nonneg (by linarith) _
  have hjr : j ≤ D.R.rS := (Finset.mem_Icc.1 hj).2
  have hrk : (D.R.rS : ℝ) + 1 ≤ D.R.k := by
    have h1 := two_rank_add_two_eq_m D; have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.rS + 1 ≤ D.R.k)
  have hexp : ((j : ℝ) + 1) + Cp * D.R.k + 3 * (D.R.rS : ℝ) ≤ Cs * D.R.k := by
    have hj' : (j : ℝ) ≤ D.R.rS := by exact_mod_cast hjr
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have : (Cp + 4) * (D.R.k : ℝ) ≤ Cs * D.R.k := mul_le_mul_of_nonneg_right hCs hk0
    have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    nlinarith
  have each : ∀ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ ≤
      Q * G1 * G2 * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) *
        k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := by
    intro δ hδ
    obtain ⟨t, hG, rfl, rfl⟩ := hTm δ hδ
    exact label_real_inequality D.R.k (LatticeIndexAndWeightTheory.jOf X t) Q _ _ _ G1 G2 Cs Cp (3 * (D.R.rS : ℝ)) hQ0 (minor_norm_pos X h3 hT t hG)
      (minor_norm_le_height large₂ X h2 hT t hG) hH (one_le_sigma_product _ _ _) hG10 hG20 hexp
  calc ∑ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ
      ≤ ∑ δ ∈ T, Q * G1 * G2 * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) *
        k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := Finset.sum_le_sum each
    _ = Q * G1 * G2 * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) *
        ∑ δ ∈ T, k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ Q * G1 * G2 * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) *
        Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)) :=
        mul_le_mul_of_nonneg_left (hc j hj T hTm)
          (mul_nonneg (mul_nonneg (mul_nonneg hQ0 hG10) hG20) (Real.rpow_nonneg (by linarith) _))
    _ = k2A1 large₂ C Ch Cc j := rfl

end Steps

section Assembly

variable {D : D7} (large₂ : SizeData₂ D) (X : TermTie D)

open Classical in

theorem rank_pair_bound_of_steps {om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ} {CH Cs C Ch Cp Cc M : ℝ} (hC : 0 ≤ C) (hCp : 0 ≤ Ch)
    (hCc : 0 ≤ Cc) (hCs : Cp + 4 ≤ Cs) (hM : 0 ≤ M) (hom : ∀ u t, 0 < om u t) {u : D.what₂.Word}
    (h1 : AmplitudeNormBound large₂ X om u CH Cs C)
    (h2 : LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C) (h3 : LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X) (hT : LatticeIndexAndWeightTheory.TieOK X u)
    (hp : LabelledPairBound large₂ X om u M CH Ch Cp) (hc : MinorCosetSum large₂ X u CH Cc)
    (j' : ℕ) (hj' : j' ∈ Finset.Icc 1 D.R.rS) (j'' : ℕ) (hj'' : j'' ∈ Finset.Icc 1 D.R.rS) :
    RowPairWeightBound X u (k2QJ X u j' j'') M (k2A1 large₂ C Ch Cc j' * k2A1 large₂ C Ch Cc j'') := by
  intro S hS
  have hd : 0 ≤ dimPi (hc := D.hcW) u := by rw [← X.Hpi_dim u]; positivity
  have hA1 : ∀ j, 0 ≤ k2A1 large₂ C Ch Cc j := by
    intro j
    unfold k2A1
    have a1 : 0 ≤ C / (D.R.k : ℝ) := by positivity
    have a2 : 0 ≤ Hb large₂.sc.b C D.R.m D.R.f := by linarith [one_le_height_bound large₂ hC (D := D)]
    have a3 : 0 ≤ Hb large₂.sc.b Ch D.R.m D.R.f := by linarith [one_le_height_bound large₂ hCp (D := D)]
    have a4 : 0 ≤ Hb large₂.sc.b Cc D.R.m D.R.f := by linarith [one_le_height_bound large₂ hCc (D := D)]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg a1 _) (Real.rpow_nonneg a2 _))
      (Real.rpow_nonneg a3 _)) (Real.rpow_nonneg a2 _)) (Real.rpow_nonneg a4 _)
  have each : ∀ p ∈ S, wP X p ≤ dimPi (hc := D.hcW) u *
      ((X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p))) *
        (k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p)))) := by
    intro p hp'
    obtain ⟨G1, G2, e1, e2⟩ := hS p hp'
    have b1 := h1 _ G1
    have b2 := h1 _ G2
    rw [e1] at b1
    rw [e2] at b2
    have hsq := Real.mul_self_sqrt hd
    have b3 : aT X (D.s.pfst p) * aT X (D.s.psnd p) ≤
        (Real.sqrt (dimPi (hc := D.hcW) u) * (om u (D.s.pfst p) * k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)))) *
        (Real.sqrt (dimPi (hc := D.hcW) u) * (om u (D.s.psnd p) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p)))) :=
      mul_le_mul b1 b2 (aT_nonneg _ _)
        (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hom _ _).le (amplitude_label_nonneg large₂ hC _ _)))
    unfold wP
    calc X.wRow p * (aT X (D.s.pfst p) * aT X (D.s.psnd p))
        ≤ X.wRow p * ((Real.sqrt (dimPi (hc := D.hcW) u) * (om u (D.s.pfst p) * k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)))) *
        (Real.sqrt (dimPi (hc := D.hcW) u) * (om u (D.s.psnd p) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p))))) :=
          mul_le_mul_of_nonneg_left b3 (X.wRow_pos p).le
      _ = (Real.sqrt (dimPi (hc := D.hcW) u) * Real.sqrt (dimPi (hc := D.hcW) u)) *
          ((X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p))) *
        (k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p)))) := by ring
      _ = _ := by rw [hsq]
  have dbl := double_sum_weighted_le S (fun p => X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p)))
    (fun p => k2lab X (D.s.pfst p)) (fun p => k2lab X (D.s.psnd p))
    (k2a large₂ CH Cs C j') (k2a large₂ CH Cs C j'') (k2e large₂ CH Ch Cp j') (k2e large₂ CH Ch Cp j'') M
    (k2A1 large₂ C Ch Cc j') (k2A1 large₂ C Ch Cc j'') hM (amplitude_label_nonneg large₂ hC j') (amplitude_label_nonneg large₂ hC j'')
    (amplitude_exponent_nonneg large₂ hCp j'') (hA1 j')
    (fun x y => hp j' hj' j'' hj'' x y _ (fun p hp' => by
      obtain ⟨m1, m2, m3⟩ := Finset.mem_filter.1 hp'
      exact ⟨hS p m1, m2, m3⟩))
    (label_sum_bound large₂ X hC hCp hCs h2 h3 hT hc j' hj' _ (fun δ hδ => by
      obtain ⟨p, m1, rfl⟩ := Finset.mem_image.1 hδ
      exact ⟨_, (hS p m1).1, (hS p m1).2.2.1, rfl⟩))
    (label_sum_bound large₂ X hC hCp hCs h2 h3 hT hc j'' hj'' _ (fun δ hδ => by
      obtain ⟨p, m1, rfl⟩ := Finset.mem_image.1 hδ
      exact ⟨_, (hS p m1).2.1, (hS p m1).2.2.2, rfl⟩))
  calc ∑ p ∈ S, wP X p ≤ ∑ p ∈ S, dimPi (hc := D.hcW) u *
      ((X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p))) *
        (k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p)))) := Finset.sum_le_sum each
    _ = dimPi (hc := D.hcW) u * ∑ p ∈ S, ((X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p))) *
        (k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p)))) := by rw [Finset.mul_sum]
    _ ≤ dimPi (hc := D.hcW) u * (M * (k2A1 large₂ C Ch Cc j' * k2A1 large₂ C Ch Cc j'')) := mul_le_mul_of_nonneg_left dbl hd
    _ = _ := by ring

def k2Cf (C Ch Cc : ℝ) : ℝ := 1 + C + C ^ 2 + Ch ^ 2 + Cc ^ 2

theorem rank_contribution_le {C Ch Cc : ℝ} (hC : 0 ≤ C) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.rS) :
    k2A1 large₂ C Ch Cc j ≤ k2A D large₂ (k2Cf C Ch Cc) j := by
  have hjr : j ≤ D.R.rS := (Finset.mem_Icc.1 hj).2
  have hm := two_rank_add_two_eq_m D
  have hmk := D.R.m_add_three_le_k
  have hjk : j ≤ D.R.k - 1 := by omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hb0 : 0 < large₂.sc.b := by linarith [two_le_scale_b D large₂]
  have hcast : ((j * (D.R.k - 1 - j) * D.R.f : ℕ) : ℝ) = (j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hjk, Nat.cast_sub hk1, Nat.cast_one]
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast hk1
  have hCf : C ≤ k2Cf C Ch Cc := by unfold k2Cf; nlinarith [sq_nonneg C, sq_nonneg Ch, sq_nonneg Cc]
  have hQ : (C / (D.R.k : ℝ)) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) ≤
      (k2Cf C Ch Cc / D.R.k) ^ (j * (D.R.k - 1 - j) * D.R.f) := by
    rw [← hcast, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hCf hk0.le) _
  have hHb : ∀ c y : ℝ, Hb large₂.sc.b c D.R.m D.R.f ^ y = Real.exp (large₂.sc.L * (c * (D.R.m : ℝ) ^ 2 * D.R.f * y)) := by
    intro c y
    unfold Hb
    rw [← Real.rpow_mul hb0.le, Real.rpow_def_of_pos hb0, log_scale_eq_L D large₂]
  have hL : 0 < large₂.sc.L := lt_trans one_pos (one_lt_scale_L D large₂)
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hrm : (D.R.rS : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : D.R.rS ≤ D.R.m)
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hr4 : (D.R.rS : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ hr0 hrm 4
  have hm4 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hj2 : ((j : ℝ) + 1) / 2 ≤ (D.R.m : ℝ) ^ 4 := by
    have : (j : ℝ) ≤ D.R.rS := by exact_mod_cast hjr
    linarith
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hexp : Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) *
      Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)) ≤
      Real.exp (k2Cf C Ch Cc * (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L) := by
    rw [hHb, hHb, hHb, hHb, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have key : C * (C * (D.R.rS : ℝ) ^ 4) + Ch * (Ch * (D.R.rS : ℝ) ^ 4) + C * (((j : ℝ) + 1) / 2) + Cc * (Cc * (D.R.rS : ℝ)) ≤
        k2Cf C Ch Cc * (D.R.m : ℝ) ^ 4 := by
      unfold k2Cf
      have t1 : C * (C * (D.R.rS : ℝ) ^ 4) ≤ C ^ 2 * (D.R.m : ℝ) ^ 4 := by
        have := mul_le_mul_of_nonneg_left hr4 (sq_nonneg C); nlinarith
      have t2 : Ch * (Ch * (D.R.rS : ℝ) ^ 4) ≤ Ch ^ 2 * (D.R.m : ℝ) ^ 4 := by
        have := mul_le_mul_of_nonneg_left hr4 (sq_nonneg Ch); nlinarith
      have t3 : C * (((j : ℝ) + 1) / 2) ≤ C * (D.R.m : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hj2 hC
      have t4 : Cc * (Cc * (D.R.rS : ℝ)) ≤ Cc ^ 2 * (D.R.m : ℝ) ^ 4 := by
        have := mul_le_mul_of_nonneg_left (le_trans hrm hm4) (sq_nonneg Cc); nlinarith
      have t5 : 0 ≤ (D.R.m : ℝ) ^ 4 := by positivity
      nlinarith
    have hfac : 0 ≤ large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f) := by positivity
    have := mul_le_mul_of_nonneg_left key hfac
    calc _ = large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f) * (C * (C * (D.R.rS : ℝ) ^ 4) + Ch * (Ch * (D.R.rS : ℝ) ^ 4) +
          C * (((j : ℝ) + 1) / 2) + Cc * (Cc * (D.R.rS : ℝ))) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  unfold k2A1 k2A
  have hQ0 : 0 ≤ (C / (D.R.k : ℝ)) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) := Real.rpow_nonneg (by positivity) _
  calc _ = (C / (D.R.k : ℝ)) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) *
        (Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) *
      Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ))) := by ring
    _ ≤ (k2Cf C Ch Cc / D.R.k) ^ (j * (D.R.k - 1 - j) * D.R.f) * Real.exp (k2Cf C Ch Cc * (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L) :=
        mul_le_mul hQ hexp (by rw [hHb, hHb, hHb, hHb]; positivity) (by
          have : 0 ≤ k2Cf C Ch Cc / (D.R.k : ℝ) := div_nonneg (le_trans hC hCf) hk0.le
          positivity)
    _ = _ := by ring

end Assembly

section Final

variable {D : D7} (large₂ : SizeData₂ D) (X : TermTie D)

theorem rank_index_pos {u : D.what₂.Word} (t : D.s.Term u u) (h : LatticeIndexAndWeightTheory.NF X t) : 1 ≤ LatticeIndexAndWeightTheory.jOf X t := by
  obtain ⟨j, hjr, hj1, hlev, -⟩ := h
  have hj := hj1 rfl
  by_contra hn
  have h0 : D.R.rS ≤ Module.finrank D.host.E (LatticeIndexAndWeightTheory.Iof X t) := by
    unfold LatticeIndexAndWeightTheory.jOf at hn; omega
  have hle : LatticeIndexAndWeightTheory.Iof X t ≤ (X.fl t).fl.X := inf_le_left
  have hX : Module.finrank D.host.E (X.fl t).fl.X = D.R.rS := by
    unfold FlagG.X
    rw [finrank_span_eq_card (X.fl t).fl.e_indep, Fintype.card_fin]
  have hEq : LatticeIndexAndWeightTheory.Iof X t = (X.fl t).fl.X := Submodule.eq_of_le_of_finrank_le hle (by rw [hX]; exact h0)
  have hr : 0 < D.R.rS := by omega
  have he : (X.fl t).fl.e ⟨0, hr⟩ ∈ LatticeIndexAndWeightTheory.Iof X t := by
    rw [hEq]; exact Submodule.subset_span ⟨_, rfl⟩
  have hne : (X.fl t).fl.e ⟨0, hr⟩ ≠ 0 := (X.fl t).fl.e_indep.ne_zero _
  have h1 := ((hlev _).1 ⟨_, he, hne, rfl⟩).1
  have h2 : (X.fl t).fl.level ((X.fl t).fl.e ⟨0, hr⟩) ≤ 1 := by
    unfold FlagG.level
    refine Nat.sInf_le ?_
    show _ ∈ (X.fl t).fl.Xa 1
    exact Submodule.subset_span ⟨⟨0, hr⟩, by simp, rfl⟩
  omega

theorem row_bound_mono {u : D.what₂.Word} {Q : D.s.Pair u u → Prop} {M B B' : ℝ} (hM : 0 ≤ M) (hB : B ≤ B')
    (h : RowPairWeightBound X u Q M B) : RowPairWeightBound X u Q M B' := fun S hS =>
  le_trans (h S hS) (mul_le_mul_of_nonneg_left hB (mul_nonneg hM (by rw [← X.Hpi_dim u]; positivity)))

theorem mass_rows_nonneg {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (what₂ : Finset (LatV D)) :
    0 ≤ massRows D F0 what₂ := by
  unfold massRows
  exact Finset.sum_nonneg fun Λ _ => by unfold Formalism.MainNotions.S.wRow; positivity

theorem pair_bound_of_steps_family {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0)
    {om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ} {CH Cs C Ch Cp Cc M : ℝ} (hC : 0 ≤ C) (hCh : 0 ≤ Ch)
    (hCc : 0 ≤ Cc) (hCs : Cp + 4 ≤ Cs) (hM : 0 ≤ M) (hom : ∀ u t, 0 < om u t) (u : D.what₂.Word) (Φ : Set (D.s.Term u u))
    (hk : k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k)
    (hMf : gaG D * M * dimPi (hc := D.hcW) u = D.duS u)
    (hNF : ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t → LatticeIndexAndWeightTheory.NF X t)
    (h1 : AmplitudeNormBound large₂ X om u CH Cs C)
    (hI : ∀ p ∈ pairsIn D.s Φ, (LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.pfst p) ∧ LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.psnd p)) ∨ wP X p = 0)
    (h2 : LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C) (h3 : LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X) (hT : LatticeIndexAndWeightTheory.TieOK X u)
    (hp : LabelledPairBound large₂ X om u M CH Ch Cp) (hc : MinorCosetSum large₂ X u CH Cc) : PairBoundOnFamily D u Φ := by
  have hCf : 1 ≤ k2Cf C Ch Cc := by unfold k2Cf; nlinarith [sq_nonneg C, sq_nonneg Ch, sq_nonneg Cc]
  refine pair_bound_of_row_bound X hH u Φ hCf hk hMf ?_
  have hr := row_bound_of_rank_bounds X u Φ (M := M) (k2A1 large₂ C Ch Cc) hI (fun t ht => rank_index_pos X t (hNF t ht))
    (fun j' h' j'' h'' => rank_pair_bound_of_steps large₂ X hC hCh hCc hCs hM hom h1 h2 h3 hT hp hc j' h' j'' h'')
  refine row_bound_mono X hM ?_ hr
  unfold k2B
  have h0 : 0 ≤ ∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j := by
    refine Finset.sum_nonneg fun j _ => ?_
    unfold k2A1
    have a1 : 0 ≤ C / (D.R.k : ℝ) := by positivity
    have a2 : 0 ≤ Hb large₂.sc.b C D.R.m D.R.f := by linarith [one_le_height_bound large₂ hC (D := D)]
    have a3 : 0 ≤ Hb large₂.sc.b Ch D.R.m D.R.f := by linarith [one_le_height_bound large₂ hCh (D := D)]
    have a4 : 0 ≤ Hb large₂.sc.b Cc D.R.m D.R.f := by linarith [one_le_height_bound large₂ hCc (D := D)]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg a1 _) (Real.rpow_nonneg a2 _))
      (Real.rpow_nonneg a3 _)) (Real.rpow_nonneg a2 _)) (Real.rpow_nonneg a4 _)
  exact pow_le_pow_left₀ h0 (Finset.sum_le_sum fun j hj => rank_contribution_le large₂ hC j hj) 2

theorem kernel_identity_cell_eq_sum (D : D7) (u : D.what₂.Word) (hV : ∀ t : D.s.Term u u, ¬ D.s.relevant t → D.s.aTerm u u t = 0) :
    NonGenericAndKTwoTheorems.Kpp D u u = KOf D.s u u (k2G0 D u) := by
  unfold NonGenericAndKTwoTheorems.Kpp KOf
  rw [tsum_subtype ({t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} : Set (D.s.Term u u)) (fun t => D.s.aTerm u u t),
    tsum_subtype (k2G0 D u) (fun t => D.s.aTerm u u t)]
  refine tsum_congr fun t => ?_
  by_cases h1 : t ∈ k2G0 D u
  · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show t ∈ {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} from h1.2)]
  · rw [Set.indicator_of_notMem h1]
    by_cases h2 : t ∈ ({t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} : Set (D.s.Term u u))
    · rw [Set.indicator_of_mem h2]
      exact hV t (fun hr => h1 ⟨hr, h2⟩)
    · rw [Set.indicator_of_notMem h2]

def LineInequalityFamily (D : D7) (u : D.what₂.Word) : Prop :=
  Summable (fun p : pairsIn D.s (k2G0 D u) => ‖D.s.pval p.1‖) →
    hsNormSq (KOf D.s u u (k2G0 D u)) ≤
      (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f * gaG D * (∑' p : pairsIn D.s (k2G0 D u), D.s.pval p.1).re

theorem line_inequality_of_admissible {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (h1 : NonGenericAndKTwoTheorems.adm1 D large₂ C' Cl Cg cb Cu cT CT C0) (hH : Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u : D.what₂.Word) : LineInequalityFamily D u :=
  h1 hH u u (k2G0 D u) (Or.inr (Or.inr (Or.inr rfl)))

theorem pair_statement_of_line_bounds (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (h1 : Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u, LineInequalityFamily D u) (h2 : NonGenericAndKTwoTheorems.adm2 D large₂ C' Cl Cg cb Cu cT CT C0)
    (h4 : NonGenericAndKTwoTheorems.ArchimedeanSignatureMatching D large₂ C' Cl Cg cb Cu cT CT C0)
    (hB : NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u, PairBoundOnFamily D u (k2G0 D u)) :
    NonGenericAndKTwoTheorems.Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH u
  have := FiniteDimensional.complete ℂ (D.s.Cu u)
  refine ⟨?_, ?_⟩
  · have hs : Summable (fun t : D.s.Term u u => ‖D.s.aTerm u u t‖) := (h2 hH.1 u u).2
    exact (hs.subtype (NonGenericAndKTwoTheorems.TermsPP D u u)).of_norm
  · rw [kernel_identity_cell_eq_sum D u (fun t ht => h4 hH.1 u u t ht)]
    exact le_trans (h1 hH.1 u (hB hH u).1) (hB hH u).2

theorem pair_bound_of_steps_word {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0)
    {om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ} {CH Cs C Ch Cp Cc M : ℝ} (hC : 0 ≤ C) (hCh : 0 ≤ Ch)
    (hCc : 0 ≤ Cc) (hCs : Cp + 4 ≤ Cs) (hM : 0 ≤ M) (hom : ∀ u t, 0 < om u t) (u : D.what₂.Word)
    (hk : k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k)
    (hMf : gaG D * M * dimPi (hc := D.hcW) u = D.duS u)
    (hNF : ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t → LatticeIndexAndWeightTheory.NF X t) (hI : IrrelevantAmplitudeZero X u)
    (h2 : LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C) (h3 : LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X) (hT : LatticeIndexAndWeightTheory.TieOK X u)
    (hp : LabelledPairBound large₂ X om u M CH Ch Cp) (hc : MinorCosetSum large₂ X u CH Cc) : TheoremK2PairBound D u :=
  pair_bound_of_steps_family large₂ X hH hC hCh hCc hCs hM hom u (NonGenericAndKTwoTheorems.TermsPP D u u) hk hMf hNF (coset_amplitude_of_norm_form large₂ X h2 hT)
    (split_all_pairs_identity_cell X u hI) h2 h3 hT hp hc

def SingleTermRemainder (C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 Ch Cp Cc : ℝ) : Prop :=
  (∀ u, MinorCosetSum large₂ X u CH Cc) ∧
  ∀ u : D.what₂.Word, ∃ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (LatV D)),
    F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧
    ∀ om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ, (∀ u t, 0 < om u t) → LatticeIndexAndWeightTheory.TieOK X u → LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs ComplexParameterFamilyContinuity →
      LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X → LatticeIndexAndWeightTheory.TermWeightSumAboveBound D large₂ X om ComplexParameterFamilyContinuity →
      LatticeIndexAndWeightTheory.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 C4 → LatticeIndexAndWeightTheory.adm5 → LabelledPairBound large₂ X om u (massRows D F0 what₂) CH Ch Cp

theorem fifth_statement_of_remainder (C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 Ch Cp Cc : ℝ) (hC : 0 ≤ ComplexParameterFamilyContinuity) (hCh : 0 ≤ Ch) (hCc : 0 ≤ Cc)
    (hCs : Cp + 4 ≤ Cs)
    (hk : k2C0 (k2Cf ComplexParameterFamilyContinuity Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k)
    (hL : LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → SingleTermRemainder large₂ X C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 Ch Cp Cc) :
    LatticeIndexAndWeightTheory.GGFromIrreducibility D large₂ X C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 := by
  rintro ⟨a1, a3, a5, a11, a12⟩ hT p1 p23 p4
  refine ⟨?_, LatticeIndexAndWeightTheory.pairs_with_finite_group_of_parameters_bounds a11 p1⟩
  refine pair_statement_of_line_bounds D large₂ C' Cl Cg cb Cu cT CT C0 (fun h u => line_inequality_of_admissible a1 h u) (fun h => (a3 h).1) a11 (fun hH u => ?_)
  obtain ⟨hc, hrows⟩ := hL hH
  obtain ⟨F0, what₂, he, hz, hR, hp⟩ := hrows u
  obtain ⟨om, hom, t2, t3a, t3b⟩ := p23 hH
  obtain ⟨n1, -, -⟩ := p1 hH
  exact pair_bound_of_steps_family large₂ X hH hC hCh hCc hCs (mass_rows_nonneg F0 what₂) hom u (k2G0 D u) hk
    (a12 hH u F0 he hz what₂ hR) (fun t ht => n1 u u t ht) (coset_amplitude_of_norm_form large₂ X t2 (hT u)) (split_identity_cell_pairs X u) t2 t3a (hT u)
    (hp om hom (hT u) t2 t3a t3b p4 a5) (hc u)

end Final

section PairsS

variable {D : D7} (large₂ : SizeData₂ D) (X : TermTie D)

def k2s {u : D.what₂.Word} (p : D.s.Pair u u) : ℕ :=
  min D.R.k (Module.finrank D.host.E (Hp (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p))) -
    Module.finrank D.host.E
      (Lat.Th (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.beta p)))

def k2Fm (u : D.what₂.Word) (Cn : ℕ) (Dp Dpp : ℝ) (s : ℕ) : ℝ :=
  ((Cn : ℝ) / (gS D : ℝ)) ^ (s * D.R.k * D.R.f) * (Dp * Dpp * NT D u) ^ (Cn * s) * ((Cn * s * D.R.f : ℕ) : ℝ) ^ (4 * s * D.R.f)

def k2Fk (u : D.what₂.Word) (Hh SS : ℝ) : ℝ :=
  (2 / (gS D : ℝ)) ^ (D.R.k * D.R.k * D.R.f) * ((4 * D.R.k * D.R.f : ℕ) : ℝ) ^ (4 * D.R.k * D.R.f) * NT D u ^ D.R.k *
    (Hh ^ (10 * D.R.k) * SS ^ (10 * D.R.k))

def k2F (u : D.what₂.Word) (Cn : ℕ) (Dp Dpp Hh SS : ℝ) (s : ℕ) : ℝ :=
  if s = 0 then 1 else if s < D.R.k then k2Fm u Cn Dp Dpp s else if s = D.R.k then k2Fk u Hh SS else 0

def PairsOfCorank (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (u : D.what₂.Word) (M CH Ch Cp C : ℝ) (Cn : ℕ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (s : ℕ) (S : Finset (D.s.Pair u u)),
    (∀ p ∈ S, k2QJ X u j' j'' p ∧ k2lab X (D.s.pfst p) = δ' ∧ k2lab X (D.s.psnd p) = δ'' ∧ k2s X p = s) →
    ∑ p ∈ S, X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p)) ≤
      M * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'') *
        k2F u Cn (k2Del D j' δ') (k2Del D j'' δ'') (Hb large₂.sc.b C D.R.m D.R.f)
          (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j' δ' * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j'' δ'') s

open Classical in

theorem sum_corank_terms_le (u : D.what₂.Word) (Cn : ℕ) (Dp Dpp Hh SS : ℝ) (hm : ∀ s, 0 ≤ k2Fm u Cn Dp Dpp s) (hk : 0 ≤ k2Fk u Hh SS)
    (T : Finset ℕ) :
    ∑ s ∈ T, k2F u Cn Dp Dpp Hh SS s ≤ 1 + ∑ s ∈ Finset.Icc 1 (D.R.k - 1), k2Fm u Cn Dp Dpp s + k2Fk u Hh SS := by
  have each : ∀ s, k2F u Cn Dp Dpp Hh SS s ≤ (if s = 0 then 1 else 0) +
      (if s ∈ Finset.Icc 1 (D.R.k - 1) then k2Fm u Cn Dp Dpp s else 0) + (if s = D.R.k then k2Fk u Hh SS else 0) := by
    intro s
    unfold k2F
    by_cases h0 : s = 0
    · rw [if_pos h0, if_pos h0]
      have a1 : 0 ≤ (if s ∈ Finset.Icc 1 (D.R.k - 1) then k2Fm u Cn Dp Dpp s else 0) := by split_ifs <;> simp [hm]
      have a2 : 0 ≤ (if s = D.R.k then k2Fk u Hh SS else 0) := by split_ifs <;> simp [hk]
      linarith
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : s < D.R.k
      · rw [if_pos h1, if_pos (Finset.mem_Icc.2 ⟨by omega, by omega⟩), if_neg (by omega)]
        simp
      · have hnot : s ∉ Finset.Icc 1 (D.R.k - 1) := fun h => h1 (by have := (Finset.mem_Icc.1 h); omega)
        rw [if_neg h1, if_neg hnot]
        simp
  calc ∑ s ∈ T, k2F u Cn Dp Dpp Hh SS s ≤ ∑ s ∈ T, ((if s = 0 then (1 : ℝ) else 0) +
      (if s ∈ Finset.Icc 1 (D.R.k - 1) then k2Fm u Cn Dp Dpp s else 0) + (if s = D.R.k then k2Fk u Hh SS else 0)) :=
        Finset.sum_le_sum fun s _ => each s
    _ = ∑ s ∈ T, (if s = 0 then (1 : ℝ) else 0) + ∑ s ∈ T, (if s ∈ Finset.Icc 1 (D.R.k - 1) then k2Fm u Cn Dp Dpp s else 0) +
        ∑ s ∈ T, (if s = D.R.k then k2Fk u Hh SS else 0) := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := by
        have b1 : ∑ s ∈ T, (if s = 0 then (1 : ℝ) else 0) ≤ 1 := by
          rw [Finset.sum_ite_eq' T 0 (fun _ => (1 : ℝ))]; split_ifs <;> simp
        have b3 : ∑ s ∈ T, (if s = D.R.k then k2Fk u Hh SS else 0) ≤ k2Fk u Hh SS := by
          rw [Finset.sum_ite_eq' T D.R.k (fun _ => k2Fk u Hh SS)]; split_ifs <;> simp [hk]
        have b2 : ∑ s ∈ T, (if s ∈ Finset.Icc 1 (D.R.k - 1) then k2Fm u Cn Dp Dpp s else 0) ≤
            ∑ s ∈ Finset.Icc 1 (D.R.k - 1), k2Fm u Cn Dp Dpp s := by
          rw [← Finset.sum_filter]
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => (Finset.mem_filter.1 hs).2) (fun s _ _ => hm s)
        linarith

theorem exponent_weight_absorb {CH Ch Cp : ℝ} (hCh : 0 ≤ Ch) (hr : 1 ≤ D.R.rS) (Cn : ℕ) (j : ℕ) (δ : ℕ → D.host.E) :
    2 * k2e large₂ CH Ch Cp j δ * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((2 * Cn + 10) * D.R.k) ≤
      k2e large₂ CH (Ch + 1) (Cp + 2 * Cn + 10) j δ := by
  set S := k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ with hS
  have hS1 : 1 ≤ S := one_le_sigma_product _ _ _
  have hS0 : 0 < S := by linarith
  have hb0 : 0 < large₂.sc.b := by linarith [two_le_scale_b D large₂]
  have hHb : ∀ c y : ℝ, Hb large₂.sc.b c D.R.m D.R.f ^ y = Real.exp (large₂.sc.L * (c * (D.R.m : ℝ) ^ 2 * D.R.f * y)) := by
    intro c y
    unfold Hb
    rw [← Real.rpow_mul hb0.le, Real.rpow_def_of_pos hb0, log_scale_eq_L D large₂]
  have hL := one_lt_scale_L D large₂
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast one_le_degree_f D
  have hrR : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hr
  have hr4 : (1 : ℝ) ≤ (D.R.rS : ℝ) ^ 4 := one_le_pow₀ hrR
  have h2 : 2 * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) ≤
      Hb large₂.sc.b (Ch + 1) D.R.m D.R.f ^ ((Ch + 1) * (D.R.rS : ℝ) ^ 4) := by
    rw [hHb, hHb]
    have e1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    calc 2 * Real.exp (large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2 * D.R.f * (Ch * (D.R.rS : ℝ) ^ 4)))
        ≤ Real.exp 1 * Real.exp (large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2 * D.R.f * (Ch * (D.R.rS : ℝ) ^ 4))) :=
          mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
      _ = Real.exp (1 + large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2 * D.R.f * (Ch * (D.R.rS : ℝ) ^ 4))) := by rw [Real.exp_add]
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          have hq : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 * D.R.f * (D.R.rS : ℝ) ^ 4 := by
            have : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := one_le_pow₀ (by linarith)
            calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
              _ ≤ _ := mul_le_mul (mul_le_mul this hfR zero_le_one (by positivity)) hr4 zero_le_one (by positivity)
          have hq2 : 1 ≤ large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f * (D.R.rS : ℝ) ^ 4) := by nlinarith
          have hq3 : 0 ≤ large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f * (D.R.rS : ℝ) ^ 4) * (2 * Ch) := by positivity
          calc 1 + large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2 * D.R.f * (Ch * (D.R.rS : ℝ) ^ 4))
              ≤ large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f * (D.R.rS : ℝ) ^ 4) +
                large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f * (D.R.rS : ℝ) ^ 4) * (2 * Ch) +
                large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2 * D.R.f * (Ch * (D.R.rS : ℝ) ^ 4)) := by linarith
            _ = _ := by ring
  have h3 : S ^ ((Cp + 2 * Cn + 10) * (D.R.k : ℝ)) = S ^ (Cp * (D.R.k : ℝ)) * S ^ ((2 * Cn + 10) * D.R.k) := by
    rw [← Real.rpow_natCast S ((2 * Cn + 10) * D.R.k), ← Real.rpow_add hS0]
    congr 1; push_cast; ring
  unfold k2e
  rw [← hS, h3]
  have hD : 0 ≤ k2Del D j δ ^ ((D.R.k : ℝ) / 2) := Real.rpow_nonneg (minor_norm_nonneg j δ) _
  calc 2 * (k2Del D j δ ^ ((D.R.k : ℝ) / 2) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) * S ^ (Cp * (D.R.k : ℝ))) *
        S ^ ((2 * Cn + 10) * D.R.k)
      = (2 * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) *
        (k2Del D j δ ^ ((D.R.k : ℝ) / 2) * (S ^ (Cp * (D.R.k : ℝ)) * S ^ ((2 * Cn + 10) * D.R.k))) := by ring
    _ ≤ Hb large₂.sc.b (Ch + 1) D.R.m D.R.f ^ ((Ch + 1) * (D.R.rS : ℝ) ^ 4) *
        (k2Del D j δ ^ ((D.R.k : ℝ) / 2) * (S ^ (Cp * (D.R.k : ℝ)) * S ^ ((2 * Cn + 10) * D.R.k))) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring

theorem height_bound_le_nat_pow {C : ℝ} (N : ℕ) (hCN : C ≤ N) :
    Hb large₂.sc.b C D.R.m D.R.f ≤ large₂.sc.b ^ (N * (2 * D.R.rS + 2) ^ 2 * D.R.f) := by
  unfold Hb
  rw [two_rank_add_two_eq_m D, ← Real.rpow_natCast large₂.sc.b (N * D.R.m ^ 2 * D.R.f)]
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith [two_le_scale_b D large₂]
  refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
  push_cast
  have h0 : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f := by positivity
  have := mul_le_mul_of_nonneg_right hCN h0
  calc C * (D.R.m : ℝ) ^ 2 * D.R.f = C * ((D.R.m : ℝ) ^ 2 * D.R.f) := by ring
    _ ≤ N * ((D.R.m : ℝ) ^ 2 * D.R.f) := this
    _ = _ := by ring

open Classical in

theorem pairs_of_corank_pairs {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0)
    {om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ} {CH Cs C Ch Cp M : ℝ} (Cn N : ℕ) (hCh : 0 ≤ Ch) (hM : 0 ≤ M)
    (hN3 : 3 * Cn ≤ N) (hN : 11 ≤ N) (hCN : C ≤ N) (hCT : CT ≤ N) (hk : k2R0 N * D.R.m ^ 2 ≤ D.R.k) {u : D.what₂.Word}
    (h2 : LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C) (hT : LatticeIndexAndWeightTheory.TieOK X u) (hS : PairsOfCorank large₂ X om u M CH Ch Cp C Cn) :
    LabelledPairBound large₂ X om u M CH (Ch + 1) (Cp + 2 * Cn + 10) := by
  intro j' hj' j'' hj'' δ' δ'' S hSm
  have hCh1 : 0 ≤ Ch + 1 := by linarith
  rcases S.eq_empty_or_nonempty with rfl | ⟨p0, hp0⟩
  · simp only [Finset.sum_empty]
    exact mul_nonneg hM (mul_nonneg (amplitude_exponent_nonneg large₂ hCh1 _ _) (amplitude_exponent_nonneg large₂ hCh1 _ _))
  obtain ⟨⟨G1, G2, e1, e2⟩, l1, l2⟩ := hSm p0 hp0
  have hr : 1 ≤ D.R.rS := le_trans (Finset.mem_Icc.1 hj').1 (Finset.mem_Icc.1 hj').2
  set S' := k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j' δ' with hS'
  set S'' := k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j'' δ'' with hS''
  set Hn := large₂.sc.b ^ (N * (2 * D.R.rS + 2) ^ 2 * D.R.f) with hHn
  have hS'1 : 1 ≤ S' := one_le_sigma_product _ _ _
  have hS''1 : 1 ≤ S'' := one_le_sigma_product _ _ _
  have hHbn := height_bound_le_nat_pow large₂ (D := D) N hCN
  have hD' : k2Del D j' δ' ≤ Hn * S' ^ 2 := by
    have h := minor_norm_le_height large₂ X h2 hT _ G1
    rw [e1, l1] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hHbn (by positivity))
  have hD'' : k2Del D j'' δ'' ≤ Hn * S'' ^ 2 := by
    have h := minor_norm_le_height large₂ X h2 hT _ G2
    rw [e2, l2] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hHbn (by positivity))
  have hb := two_le_scale_b D large₂
  have hk5 : (5 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m
    exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hkb1 : (1 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := one_le_pow₀ (by nlinarith)
  have hg : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (gS D : ℝ) := by
    unfold gS
    push_cast
    have g0 := (hH.2.2.1 0).1
    have g1 := (hH.2.2.1 1).1
    nlinarith
  have hg0 : (0 : ℝ) < (gS D : ℝ) := by linarith
  have hNT0 : 0 ≤ NT D u := by unfold NT; positivity
  have hNT : NT D u ≤ Hn := by
    have hTu := (hH.2.2.2.2.2.2.1 u).1
    unfold NT
    calc ((D.mem u).A.T : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ (CT * (D.R.m : ℝ))) ^ D.R.f := pow_le_pow_left₀ (Nat.cast_nonneg _) hTu _
      _ = large₂.sc.b ^ (CT * (D.R.m : ℝ) * D.R.f) := by
          rw [← Real.rpow_natCast (large₂.sc.b ^ (CT * (D.R.m : ℝ))) D.R.f, ← Real.rpow_mul (by linarith)]
      _ ≤ Hn := by
          rw [hHn, two_rank_add_two_eq_m D, ← Real.rpow_natCast large₂.sc.b (N * D.R.m ^ 2 * D.R.f)]
          refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
          push_cast
          have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
          have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
          have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
          have a1 : CT * (D.R.m : ℝ) ≤ N * (D.R.m : ℝ) ^ 2 := by
            have : CT * (D.R.m : ℝ) ≤ N * (D.R.m : ℝ) := mul_le_mul_of_nonneg_right hCT (by linarith)
            have : (N : ℝ) * (D.R.m : ℝ) ≤ N * (D.R.m : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hN0
            linarith
          exact mul_le_mul_of_nonneg_right a1 hf0
  have hreal := sum_over_coranks_real N Cn D.R.k D.R.rS D.R.f large₂.sc.b (gS D : ℝ) (NT D u) (k2Del D j' δ') (k2Del D j'' δ'') S' S''
    hN3 hN hb (one_le_degree_f D) hH.2.2.2.2.2.1 (by rw [two_rank_add_two_eq_m D]; exact hk) hg0 hg hS'1 hS''1 (minor_norm_nonneg _ _) (minor_norm_nonneg _ _)
    hNT0 hD' hD'' hNT
  have hFm0 : ∀ s, 0 ≤ k2Fm u Cn (k2Del D j' δ') (k2Del D j'' δ'') s := by
    intro s
    unfold k2Fm
    have := minor_norm_nonneg (D := D) j' δ'
    have := minor_norm_nonneg (D := D) j'' δ''
    positivity
  have hHb0 : 0 ≤ Hb large₂.sc.b C D.R.m D.R.f := by unfold Hb; exact Real.rpow_nonneg (by linarith) _
  have hFk0 : 0 ≤ k2Fk u (Hb large₂.sc.b C D.R.m D.R.f) (S' * S'') := by unfold k2Fk; positivity
  have hFk : k2Fk u (Hb large₂.sc.b C D.R.m D.R.f) (S' * S'') ≤ k2Fk u Hn (S' * S'') := by
    unfold k2Fk
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hHb0 hHbn _) (by positivity)
  set E0 := k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'' with hE0
  have hE00 : 0 ≤ E0 := mul_nonneg (amplitude_exponent_nonneg large₂ hCh _ _) (amplitude_exponent_nonneg large₂ hCh _ _)
  have hmaps : ∀ p ∈ S, k2s X p ∈ S.image (k2s X) := fun p hp => Finset.mem_image_of_mem _ hp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ s ∈ S.image (k2s X), ∑ p ∈ S with k2s X p = s, X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p))
      ≤ ∑ s ∈ S.image (k2s X), M * E0 * k2F u Cn (k2Del D j' δ') (k2Del D j'' δ'') (Hb large₂.sc.b C D.R.m D.R.f) (S' * S'') s := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact hS j' hj' j'' hj'' δ' δ'' s _ (fun p hp => by
          obtain ⟨m1, m2⟩ := Finset.mem_filter.1 hp
          exact ⟨(hSm p m1).1, (hSm p m1).2.1, (hSm p m1).2.2, m2⟩)
    _ = M * E0 * ∑ s ∈ S.image (k2s X), k2F u Cn (k2Del D j' δ') (k2Del D j'' δ'') (Hb large₂.sc.b C D.R.m D.R.f) (S' * S'') s := by
        rw [Finset.mul_sum]
    _ ≤ M * E0 * (3 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hM hE00)
        refine le_trans (sum_corank_terms_le u Cn _ _ _ _ hFm0 hFk0 _) ?_
        refine le_trans ?_ hreal
        have : k2Fk u Hn (S' * S'') = (2 / (gS D : ℝ)) ^ (D.R.k * D.R.k * D.R.f) * ((4 * D.R.k * D.R.f : ℕ) : ℝ) ^ (4 * D.R.k * D.R.f) *
            NT D u ^ D.R.k * (Hn ^ (10 * D.R.k) * (S' * S'') ^ (10 * D.R.k)) := rfl
        rw [← this]
        have hmid : ∑ s ∈ Finset.Icc 1 (D.R.k - 1), k2Fm u Cn (k2Del D j' δ') (k2Del D j'' δ'') s =
            ∑ s ∈ Finset.Icc 1 (D.R.k - 1), ((Cn : ℝ) / (gS D : ℝ)) ^ (s * D.R.k * D.R.f) *
              (k2Del D j' δ' * k2Del D j'' δ'' * NT D u) ^ (Cn * s) * ((Cn * s * D.R.f : ℕ) : ℝ) ^ (4 * s * D.R.f) := rfl
        rw [← hmid]
        linarith
    _ ≤ M * (k2e large₂ CH (Ch + 1) (Cp + 2 * Cn + 10) j' δ' * k2e large₂ CH (Ch + 1) (Cp + 2 * Cn + 10) j'' δ'') := by
        have s1 := exponent_weight_absorb large₂ (CH := CH) (Cp := Cp) hCh hr Cn j' δ'
        have s2 := exponent_weight_absorb large₂ (CH := CH) (Cp := Cp) hCh hr Cn j'' δ''
        rw [← hS'] at s1
        rw [← hS''] at s2
        have n1 : 0 ≤ 2 * k2e large₂ CH Ch Cp j' δ' * S' ^ ((2 * Cn + 10) * D.R.k) :=
          mul_nonneg (mul_nonneg zero_le_two (amplitude_exponent_nonneg large₂ hCh _ _)) (by positivity)
        have n2 : 0 ≤ 2 * k2e large₂ CH Ch Cp j'' δ'' * S'' ^ ((2 * Cn + 10) * D.R.k) :=
          mul_nonneg (mul_nonneg zero_le_two (amplitude_exponent_nonneg large₂ hCh _ _)) (by positivity)
        have s3 := mul_le_mul s1 s2 n2 (amplitude_exponent_nonneg large₂ hCh1 _ _)
        have hpos : 0 ≤ E0 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k) := mul_nonneg hE00 (by positivity)
        have s4 : E0 * (3 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k)) ≤
            (2 * k2e large₂ CH Ch Cp j' δ' * S' ^ ((2 * Cn + 10) * D.R.k)) * (2 * k2e large₂ CH Ch Cp j'' δ'' * S'' ^ ((2 * Cn + 10) * D.R.k)) := by
          have : (2 * k2e large₂ CH Ch Cp j' δ' * S' ^ ((2 * Cn + 10) * D.R.k)) * (2 * k2e large₂ CH Ch Cp j'' δ'' * S'' ^ ((2 * Cn + 10) * D.R.k)) =
              4 * (E0 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k)) := by rw [hE0, mul_pow]; ring
          rw [this]; linarith
        calc M * E0 * (3 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k)) = M * (E0 * (3 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_trans s4 s3) hM

def CorankRemainder (C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 Ch Cp Cc : ℝ) (Cn : ℕ) : Prop :=
  (∀ u, MinorCosetSum large₂ X u CH Cc) ∧
  ∀ u : D.what₂.Word, ∃ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (LatV D)),
    F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧
    ∀ om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ, (∀ u t, 0 < om u t) → LatticeIndexAndWeightTheory.TieOK X u → LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs ComplexParameterFamilyContinuity →
      LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X → LatticeIndexAndWeightTheory.TermWeightSumAboveBound D large₂ X om ComplexParameterFamilyContinuity →
      LatticeIndexAndWeightTheory.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 C4 → LatticeIndexAndWeightTheory.adm5 → PairsOfCorank large₂ X om u (massRows D F0 what₂) CH Ch Cp ComplexParameterFamilyContinuity Cn

theorem remainder_of_corank_remainder {C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 Ch Cp Cc : ℝ} {Cn : ℕ} (N : ℕ)
    (hH : NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0) (hCh : 0 ≤ Ch) (hN3 : 3 * Cn ≤ N) (hN : 11 ≤ N) (hCN : ComplexParameterFamilyContinuity ≤ N) (hCT : CT ≤ N)
    (hk : k2R0 N * D.R.m ^ 2 ≤ D.R.k) (h : CorankRemainder large₂ X C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 Ch Cp Cc Cn) :
    SingleTermRemainder large₂ X C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 (Ch + 1) (Cp + 2 * Cn + 10) Cc := by
  refine ⟨h.1, fun u => ?_⟩
  obtain ⟨F0, what₂, he, hz, hR, hp⟩ := h.2 u
  exact ⟨F0, what₂, he, hz, hR, fun om hom hT t2 t3a t3b p4 a5 =>
    pairs_of_corank_pairs large₂ X hH Cn N hCh (mass_rows_nonneg F0 what₂) hN3 hN hCN hCT hk t2 hT (hp om hom hT t2 t3a t3b p4 a5)⟩

end PairsS

section Fam

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))

theorem eventually_k_log_k_dominates (K : ℝ) : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
    K * ((Fm.D x i).R.m : ℝ) ^ 6 * (Fm.L x i).sc.L ≤ ((Fm.D x i).R.k : ℝ) * Real.log (Fm.D x i).R.k := by
  have he := eps_pos Fm
  obtain ⟨x0, _, hx0⟩ := ev_rpow (show 0 < eps / 100 by positivity) K
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  have hs := (Fm.sizes x hx1 i).2.2.2.1.2.2.2.2.2.2.1
  unfold szTh at hs
  rw [Fm.L_x x i hx1, Fm.L_eps] at hs
  refine le_trans ?_ hs
  have hL : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (le_of_lt (lt_trans one_pos (Fm.L x i).sc.one_lt_alt)) _
  have := hx0 x hx
  gcongr

theorem fifth_family_iff_K2_family : LatticeIndexAndWeightTheory.SlopeLossFamily Fm ↔ NonGenericAndKTwoTheorems.FamilyNonIdentityTermSummability Fm := Iff.rfl

theorem K2_family_of_fifth (Gv : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, GaugeVol (Fm.D x i)) (h : LatticeIndexAndWeightTheory.SlopeLossFamily Fm) :
    NonGenericAndKTwoTheorems.FamilyNonIdentityTermSummabilityOfAdmissible Fm At Gv := fun _ => h

theorem fifth_family_of_remainder
    (hLF : ∀ Cg cb Cu cT CT C0 C4 : ℝ, 0 < C4 → ∃ Cp : ℝ, ∀ CH ComplexParameterFamilyContinuity : ℝ, 0 < ComplexParameterFamilyContinuity → ∃ Ch Cc : ℝ, 0 ≤ Ch ∧ 0 ≤ Cc ∧
      OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, LatticeIndexAndWeightTheory.Hyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
        SingleTermRemainder (Fm.L x i) (At x hx i) C' Cl Cg cb Cu cT CT C0 CH (Cp + 4) ComplexParameterFamilyContinuity C4 Ch Cp Cc) :
    LatticeIndexAndWeightTheory.FamilyProportionality Fm At := by
  rintro ⟨a1, a3, a5, a11, a12⟩ hT p1 p23 p4
  refine ⟨fun Cg cb Cu cT CT C0 => ?_, fun Cg cb Cu cT CT C0 => ?_⟩
  · obtain ⟨C4, hC4, e4⟩ := p4 Cg cb Cu cT CT C0
    obtain ⟨Cp, hCp⟩ := hLF Cg cb Cu cT CT C0 C4 hC4
    obtain ⟨CH, ComplexParameterFamilyContinuity, hC23, e23⟩ := p23 Cg cb Cu cT CT C0 (Cp + 4)
    obtain ⟨Ch, Cc, hCh, hCc, eL⟩ := hCp CH ComplexParameterFamilyContinuity hC23
    obtain ⟨xk, hxk⟩ := eventually_k_log_k_dominates Fm (k2C0 (k2Cf ComplexParameterFamilyContinuity Ch Cc))
    obtain ⟨x0, H⟩ := (((((((a1 Cg cb Cu cT CT C0).and (a3 Cg cb Cu cT CT C0)).and (a11 Cg cb Cu cT CT C0)).and
      (a12 Cg cb Cu cT CT C0)).and (p1 Cg cb Cu cT CT C0)).and e23).and e4).and eL
    refine ownEv_intro Fm (max x0 xk) (fun x hx hx1 i => ?_)
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h3⟩, h11⟩, h12⟩, hp1⟩, hp23⟩, hp4⟩, hl⟩ := H x (le_trans (le_max_left _ _) hx) i
    exact (fifth_statement_of_remainder (Fm.L x i) (At x hx1 i) _ _ Cg cb Cu cT CT C0 CH (Cp + 4) ComplexParameterFamilyContinuity C4 Ch Cp Cc hC23.le hCh hCc le_rfl
      (hxk x (le_trans (le_max_right _ _) hx) hx1 i) (hl hx1) ⟨h1, h3, a5, h11, h12⟩ (fun u => hT x hx1 i u) (hp1 hx1) (hp23 hx1)
      hp4).1
  · obtain ⟨x0, H⟩ := (a11 Cg cb Cu cT CT C0).and (p1 Cg cb Cu cT CT C0)
    refine ownEv_intro Fm x0 (fun x hx hx1 i => ?_)
    exact LatticeIndexAndWeightTheory.pairs_with_finite_group_of_parameters_bounds (H x hx i).1 ((H x hx i).2 hx1)

theorem eventually_k_dominates_m_sq (K : ℕ) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).R.m ^ 4 ≤ (Fm.D x i).R.f → (Fm.D x i).R.f ≤ (Fm.D x i).R.k →
    K * (Fm.D x i).R.m ^ 2 ≤ (Fm.D x i).R.k := by
  obtain ⟨x0, _, h⟩ := ev_m Fm K
  refine ⟨x0, fun x hx i h1 h2 => ?_⟩
  have hK : K ≤ (Fm.D x i).R.m := by exact_mod_cast h x hx i
  have hm : 1 ≤ (Fm.D x i).R.m := le_trans (by norm_num) (Fm.D x i).R.two_le_m
  calc K * (Fm.D x i).R.m ^ 2 ≤ (Fm.D x i).R.m * (Fm.D x i).R.m ^ 2 := Nat.mul_le_mul_right _ hK
    _ = (Fm.D x i).R.m ^ 3 := by ring
    _ ≤ (Fm.D x i).R.m ^ 4 := Nat.pow_le_pow_right hm (by norm_num)
    _ ≤ _ := le_trans h1 h2

theorem fifth_family_of_corank_remainder
    (hLF : ∀ Cg cb Cu cT CT C0 C4 : ℝ, 0 < C4 → ∃ (Cp : ℝ) (Cn : ℕ), ∀ CH ComplexParameterFamilyContinuity : ℝ, 0 < ComplexParameterFamilyContinuity → ∃ Ch Cc : ℝ, 0 ≤ Ch ∧ 0 ≤ Cc ∧
      OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, LatticeIndexAndWeightTheory.Hyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
        CorankRemainder (Fm.L x i) (At x hx i) C' Cl Cg cb Cu cT CT C0 CH (Cp + 2 * Cn + 10 + 4) ComplexParameterFamilyContinuity C4 Ch Cp Cc Cn) :
    LatticeIndexAndWeightTheory.FamilyProportionality Fm At := by
  refine fifth_family_of_remainder Fm At (fun Cg cb Cu cT CT C0 C4 hC4 => ?_)
  obtain ⟨Cp, Cn, h⟩ := hLF Cg cb Cu cT CT C0 C4 hC4
  refine ⟨Cp + 2 * Cn + 10, fun CH ComplexParameterFamilyContinuity hC23 => ?_⟩
  obtain ⟨Ch, Cc, hCh, hCc, ⟨x0, H⟩⟩ := h CH ComplexParameterFamilyContinuity hC23
  set N : ℕ := 11 + 3 * Cn + ⌈ComplexParameterFamilyContinuity⌉₊ + ⌈CT⌉₊ with hN
  obtain ⟨xk, hxk⟩ := eventually_k_dominates_m_sq Fm (k2R0 N)
  refine ⟨Ch + 1, Cc, by linarith, hCc, max x0 xk, fun x hx i hx1 hH => ?_⟩
  have hC23N : ComplexParameterFamilyContinuity ≤ N := le_trans (Nat.le_ceil ComplexParameterFamilyContinuity) (by exact_mod_cast (by omega : ⌈ComplexParameterFamilyContinuity⌉₊ ≤ N))
  have hCTN : CT ≤ N := le_trans (Nat.le_ceil CT) (by exact_mod_cast (by omega : ⌈CT⌉₊ ≤ N))
  exact remainder_of_corank_remainder (Fm.L x i) (At x hx1 i) N hH hCh (by omega) (by omega) hC23N hCTN
    (hxk x (le_trans (le_max_right _ _) hx) i hH.1.1.2.2.1 hH.1.1.2.2.2.1) (H x (le_trans (le_max_left _ _) hx) i hx1 hH)

end Fam

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section NGa

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

open MeasureTheory in

theorem ng_scale (hOK : M.OK) (x : Eˣ) :
    ∃ c : NNReal, ∀ s : Set E, IsOpen s → M.mu ((fun y => (x : E) * y) '' s) = c * M.mu s := by
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  have := hOK.borel
  have := hOK.haar.haar
  obtain ⟨hO, hC, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top M.L
  have hlc : LocallyCompactSpace E :=
    hC.locallyCompactSpace_of_mem_nhds_of_addGroup (hO.mem_nhds M.L.O.zero_mem)
  let e : E ≃+ E := AddAut.mulLeft (x⁻¹)
  have he : ∀ y, e y = ((x⁻¹ : Eˣ) : E) * y := fun y => rfl
  have hes : ∀ y, e.symm y = (x : E) * y := by
    intro y
    apply e.injective
    rw [AddEquiv.apply_symm_apply, he, ← mul_assoc, Units.inv_mul, one_mul]
  have hc1 : Continuous e := by
    have : (e : E → E) = fun y => ((x⁻¹ : Eˣ) : E) * y := funext he
    rw [this]; fun_prop
  have hc2 : Continuous e.symm := by
    have : (e.symm : E → E) = fun y => (x : E) * y := funext hes
    rw [this]; fun_prop
  have hH : (Measure.map e M.mu).IsAddHaarMeasure := e.isAddHaarMeasure_map M.mu hc1 hc2
  refine ⟨(Measure.map e M.mu).addHaarScalarFactor M.mu, fun s hs => ?_⟩
  have h1 := Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen (Measure.map e M.mu) M.mu hs
  rw [Measure.map_apply hc1.measurable hs.measurableSet] at h1
  have h2 : e ⁻¹' s = (fun y => (x : E) * y) '' s := by
    ext y
    constructor
    · intro hy
      exact ⟨e y, hy, by show (x : E) * e y = y; rw [he, ← mul_assoc, Units.mul_inv, one_mul]⟩
    · rintro ⟨z, hz, rfl⟩
      show e ((x : E) * z) ∈ s
      rw [he, ← mul_assoc, Units.inv_mul, one_mul]; exact hz
  rw [h2] at h1
  rw [h1]; rfl

theorem ng_modK (hOK : M.OK) {x : E} (hx : IsUnit x) : 0 < M.modK x ∧ (x ∈ M.L.O → M.modK x ≤ 1) := by
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  have := hOK.borel
  have := hOK.haar.haar
  obtain ⟨hO, hC, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top M.L
  obtain ⟨hRo, hRc, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.R_top M hOK
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨c, hc⟩ := ng_scale hOK u
  have hm : M.modK (u : E) = c := by
    unfold Model.modK
    rw [hc _ hRo, hOK.haar.volR, mul_one]; rfl
  have hOpos : 0 < M.mu (M.L.O : Set E) := hO.measure_pos M.mu ⟨0, M.L.O.zero_mem⟩
  have hOfin : M.mu (M.L.O : Set E) < ⊤ := hC.measure_lt_top
  constructor
  · rw [hm]
    have h1 : IsOpen ((fun y => (u : E) * y) '' (M.L.O : Set E)) := by
      have : (fun y => (u : E) * y) '' (M.L.O : Set E) = (fun y => ((u⁻¹ : Eˣ) : E) * y) ⁻¹' (M.L.O : Set E) := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          show ((u⁻¹ : Eˣ) : E) * ((u : E) * z) ∈ M.L.O
          rw [← mul_assoc, Units.inv_mul, one_mul]; exact hz
        · intro hy
          exact ⟨_, hy, by show (u : E) * (((u⁻¹ : Eˣ) : E) * y) = y; rw [← mul_assoc, Units.mul_inv, one_mul]⟩
      rw [this]
      exact hO.preimage (by fun_prop)
    have h2 : 0 < M.mu ((fun y => (u : E) * y) '' (M.L.O : Set E)) :=
      h1.measure_pos M.mu ⟨(u : E) * 0, 0, M.L.O.zero_mem, rfl⟩
    rw [hc _ hO] at h2
    have h3 : (c : ENNReal) ≠ 0 := fun h => by rw [h, zero_mul] at h2; exact lt_irrefl _ h2
    have h4 : c ≠ 0 := fun h => h3 (by rw [h]; rfl)
    exact_mod_cast pos_iff_ne_zero.2 h4
  · intro hx
    rw [hm]
    have h1 : (fun y => (u : E) * y) '' (M.L.O : Set E) ⊆ (M.L.O : Set E) := by
      rintro _ ⟨z, hz, rfl⟩
      exact M.L.O.mul_mem hx hz
    have h2 := MeasureTheory.measure_mono (μ := M.mu) h1
    rw [hc _ hO] at h2
    by_contra hlt
    push Not at hlt
    have h3 : (1 : ENNReal) < c := by exact_mod_cast hlt
    have h4 : M.mu (M.L.O : Set E) < c * M.mu (M.L.O : Set E) := by
      calc M.mu (M.L.O : Set E) = 1 * M.mu (M.L.O : Set E) := (one_mul _).symm
        _ < c * M.mu (M.L.O : Set E) := ENNReal.mul_lt_mul_left hOpos.ne' hOfin.ne h3
    exact absurd h2 (not_le.2 h4)

theorem norm_basic_character_eq_one (hOK : M.OK) (x : E) : ‖M.L.psi0 x‖ = 1 := by
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  obtain ⟨-, hC, hU⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top M.L
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hπ0 : (π : F) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)

  have key : ∀ y : E, ‖M.L.psi0 y‖ ≤ 1 := by
    intro y
    obtain ⟨m, hm⟩ := hU π hπ y
    have hm := hm m le_rfl
    set u : E := algebraMap F E ((π : F)⁻¹) ^ m with hu
    have huπ : u * algebraMap F E π ^ m = 1 := by
      rw [hu, ← mul_pow, ← map_mul, inv_mul_cancel₀ hπ0, map_one, one_pow]
    have hK : IsCompact ((fun z => u * z) '' (M.L.O : Set E)) := hC.image (by fun_prop)
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun z => M.L.psi0 z) M.L.local_additive_char_continuous.continuousOn
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hlt
    have hmem : (n : ℕ) • y ∈ (fun z => u * z) '' (M.L.O : Set E) := by
      refine ⟨n • (algebraMap F E π ^ m * y), M.L.O.nsmul_mem hm n, ?_⟩
      show u * (n • (algebraMap F E π ^ m * y)) = n • y
      rw [mul_smul_comm, ← mul_assoc, huπ, one_mul]
    have h1 := hB _ hmem
    rw [AddChar.map_nsmul_eq_pow, norm_pow] at h1
    exact absurd h1 (not_le.2 hn)
  have h1 := key x
  have h2 := key (-x)
  have h3 : M.L.psi0 x * M.L.psi0 (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h4 : ‖M.L.psi0 x‖ * ‖M.L.psi0 (-x)‖ = 1 := by rw [← norm_mul, h3, norm_one]
  have h5 : 0 ≤ ‖M.L.psi0 x‖ := norm_nonneg _
  nlinarith

theorem two_le_residue_card (hOK : M.OK) : 2 ≤ qF F := by
  have := hOK.loc
  unfold qF
  have : Finite 𝓀[F] := inferInstance
  exact Finite.one_lt_card

open MeasureTheory in
theorem ng_modK_nonunit (hOK : M.OK) (a : 𝒪[F]) (ha0 : (a : F) ≠ 0) (hau : ¬ IsUnit a) :
    M.modK (algebraMap F E a) ≤ (((qF F : ℝ)) ^ 2)⁻¹ := by
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  have := hOK.borel
  have := hOK.haar.haar
  have hnt := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
  obtain ⟨hO, hC, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top M.L
  obtain ⟨hRo, hRc, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.R_top M hOK
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  obtain ⟨θ, hθO, hθc, D, hD0, hD⟩ := Formalism.MainNotions.LocalModelPeriodLattices.exists_theta M.L
  have hua : IsUnit (algebraMap F E (a : F)) := ha0.isUnit.map _
  obtain ⟨u, hu⟩ := hua
  obtain ⟨c, hc⟩ := ng_scale hOK u
  have hm : M.modK (algebraMap F E (a : F)) = c := by
    unfold Model.modK
    rw [← hu, hc _ hRo, hOK.haar.volR, mul_one]; rfl

  let OO : AddSubgroup E := M.L.O.toAddSubgroup
  let am : E →+ E := AddMonoidHom.mulLeft (algebraMap F E (a : F))
  have ham : Function.Injective am := by
    intro x y hxy
    have h1 : (u : E) * x = (u : E) * y := by rw [hu]; exact hxy
    exact u.isUnit.mul_left_cancel h1
  let ψ : 𝒪[F] × 𝒪[F] →+ E :=
    { toFun := fun p => algebraMap F E (p.1 : F) + algebraMap F E (p.2 : F) * θ
      map_zero' := by simp
      map_add' := by
        intro p p'
        simp only [Prod.fst_add, Prod.snd_add, Subring.coe_add, map_add]
        ring }
  have hψ : ∀ p, ψ p = algebraMap F E (p.1 : F) + algebraMap F E (p.2 : F) * θ := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ h0
    rw [hψ] at h0
    simp only at h0
    have h1 : algebraMap F E (x : F) - algebraMap F E (y : F) * θ = 0 := by
      have := congrArg M.L.cj h0
      rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hθc, map_zero] at this
      rw [← this]; ring
    have h2 : algebraMap F E (2 * (x : F)) = 0 := by
      rw [map_mul, map_ofNat]
      linear_combination h0 + h1
    have hx : (x : F) = 0 := by
      have := hinj (h2.trans (map_zero _).symm)
      simpa using this
    have h3 : algebraMap F E ((y : F) * (D : F)) = 0 := by
      rw [map_mul, ← hD]
      have h4 : algebraMap F E (y : F) * θ = 0 := by rw [hx, map_zero, zero_add] at h0; exact h0
      rw [← mul_assoc, h4, zero_mul]
    have hy : (y : F) = 0 := by
      have := hinj (h3.trans (map_zero _).symm)
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hD0
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  let A' : AddSubgroup E := (⊤ : AddSubgroup (𝒪[F] × 𝒪[F])).map ψ
  let J : AddSubgroup 𝒪[F] := (Ideal.span {a}).toAddSubgroup
  have hA'O : A' ≤ OO := by
    rintro _ ⟨p, -, rfl⟩
    exact M.L.O.add_mem (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L p.1)
      (M.L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L p.2) hθO)

  have h2D : (2 * (D : F)) ≠ 0 := mul_ne_zero two_ne_zero hD0
  obtain ⟨w, hw⟩ := (h2D.isUnit.map (algebraMap F E))
  have hsub : (fun y => (w : E) * y) '' (M.L.O : Set E) ⊆ (A' : Set E) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, c', ht, hc', he⟩ := Formalism.MainNotions.LocalModelPeriodLattices.decomp M.L θ hθc D hD x
    have htO : t ∈ 𝒪[F] := Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L t (by
      rw [ht]; exact M.L.O.add_mem hx (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ hx))
    have hcO : c' ∈ 𝒪[F] := Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L c' (by
      rw [hc']; exact M.L.O.mul_mem (M.L.O.sub_mem hx (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ hx)) hθO)
    refine ⟨(D * ⟨t, htO⟩, ⟨c', hcO⟩), trivial, ?_⟩
    show algebraMap F E ((D : F) * t) + algebraMap F E c' * θ = (w : E) * x
    rw [hw, he]
  have hwo : IsOpen ((fun y => (w : E) * y) '' (M.L.O : Set E)) := by
    have : (fun y => (w : E) * y) '' (M.L.O : Set E) = (fun y => ((w⁻¹ : Eˣ) : E) * y) ⁻¹' (M.L.O : Set E) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show ((w⁻¹ : Eˣ) : E) * ((w : E) * z) ∈ M.L.O
        rw [← mul_assoc, Units.inv_mul, one_mul]; exact hz
      · intro hy
        exact ⟨_, hy, by show (w : E) * (((w⁻¹ : Eˣ) : E) * y) = y; rw [← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [this]
    exact hO.preimage (by fun_prop)
  have hA'o : IsOpen (A' : Set E) :=
    AddSubgroup.isOpen_of_mem_nhds A' (Filter.mem_of_superset (hwo.mem_nhds ⟨0, M.L.O.zero_mem, mul_zero _⟩) hsub)
  have hOOc : IsCompact (OO : Set E) := hC
  have hidx1 := (Formalism.MainNotions.LocalModelPeriodLattices.measure_eq_relIndex_mul M.mu A' OO hA'O hA'o hOOc).1

  have haO : OO.map am ≤ OO := by
    rintro _ ⟨x, hx, rfl⟩
    exact M.L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L a) hx
  have hset : ((OO.map am : AddSubgroup E) : Set E) = (fun y => (u : E) * y) '' (M.L.O : Set E) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [hu]; rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [hu]; rfl⟩
  have haOo : IsOpen ((OO.map am : AddSubgroup E) : Set E) := by
    rw [hset]
    have : (fun y => (u : E) * y) '' (M.L.O : Set E) = (fun y => ((u⁻¹ : Eˣ) : E) * y) ⁻¹' (M.L.O : Set E) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show ((u⁻¹ : Eˣ) : E) * ((u : E) * z) ∈ M.L.O
        rw [← mul_assoc, Units.inv_mul, one_mul]; exact hz
      · intro hy
        exact ⟨_, hy, by show (u : E) * (((u⁻¹ : Eˣ) : E) * y) = y; rw [← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [this]
    exact hO.preimage (by fun_prop)
  obtain ⟨hN0, hN⟩ := Formalism.MainNotions.LocalModelPeriodLattices.measure_eq_relIndex_mul M.mu (OO.map am) OO haO haOo hOOc

  have hmap : A'.map am = (J.prod J).map ψ := by
    ext z
    constructor
    · rintro ⟨_, ⟨p, -, rfl⟩, rfl⟩
      refine ⟨(a * p.1, a * p.2), ⟨Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a),
        Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)⟩, ?_⟩
      show algebraMap F E ((a : F) * (p.1 : F)) + algebraMap F E ((a : F) * (p.2 : F)) * θ =
        algebraMap F E (a : F) * (algebraMap F E (p.1 : F) + algebraMap F E (p.2 : F) * θ)
      rw [map_mul, map_mul]; ring
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      obtain ⟨x1, hx1⟩ := Ideal.mem_span_singleton'.1 hx
      obtain ⟨y1, hy1⟩ := Ideal.mem_span_singleton'.1 hy
      refine ⟨ψ (x1, y1), ⟨(x1, y1), trivial, rfl⟩, ?_⟩
      show algebraMap F E (a : F) * (algebraMap F E (x1 : F) + algebraMap F E (y1 : F) * θ) =
        algebraMap F E (x : F) + algebraMap F E (y : F) * θ
      have hx2 : (x : F) = (x1 : F) * (a : F) := by rw [← Subring.coe_mul]; exact congrArg Subtype.val hx1.symm
      have hy2 : (y : F) = (y1 : F) * (a : F) := by rw [← Subring.coe_mul]; exact congrArg Subtype.val hy1.symm
      rw [hx2, hy2, map_mul, map_mul]
      ring
  have e1 : (A'.map am).relIndex (OO.map am) = A'.relIndex OO :=
    AddSubgroup.relIndex_map_map_of_injective A' OO ham
  have e2 : (A'.map am).relIndex A' = J.index * J.index := by
    rw [hmap, AddSubgroup.relIndex_map_map_of_injective (J.prod J) ⊤ hψinj, AddSubgroup.relIndex_top_right,
      AddSubgroup.index_prod]
  have hle1 : A'.map am ≤ OO.map am := AddSubgroup.map_mono hA'O
  have hle2 : A'.map am ≤ A' := by
    rw [hmap]; exact AddSubgroup.map_mono le_top
  have e3 := AddSubgroup.relIndex_mul_relIndex (A'.map am) (OO.map am) OO hle1 haO
  have e4 := AddSubgroup.relIndex_mul_relIndex (A'.map am) A' OO hle2 hA'O
  have e5 : (OO.map am).relIndex OO = J.index * J.index := by
    rw [e1] at e3
    rw [e2] at e4
    have : A'.relIndex OO * (OO.map am).relIndex OO = A'.relIndex OO * (J.index * J.index) := by
      rw [e3, ← e4, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hidx1) this
  have hJ0 : J.index ≠ 0 := fun h => hN0 (by rw [e5, h, zero_mul])
  have hJm : J ≤ (IsLocalRing.maximalIdeal 𝒪[F]).toAddSubgroup := by
    intro x hx
    have h1 : Ideal.span {a} ≤ IsLocalRing.maximalIdeal 𝒪[F] := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact (IsLocalRing.mem_maximalIdeal a).2 hau
    exact h1 hx
  have hq : qF F ≤ J.index := by
    have h1 : (IsLocalRing.maximalIdeal 𝒪[F]).toAddSubgroup.index ∣ J.index := AddSubgroup.index_dvd_of_le hJm
    have h2 : (IsLocalRing.maximalIdeal 𝒪[F]).toAddSubgroup.index = qF F := rfl
    rw [h2] at h1
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hJ0) h1

  have hpos : 0 < M.mu ((OO.map am : AddSubgroup E) : Set E) := haOo.measure_pos M.mu ⟨0, (OO.map am).zero_mem⟩
  have hfin : M.mu ((OO.map am : AddSubgroup E) : Set E) < ⊤ :=
    lt_of_le_of_lt (measure_mono haO) hC.measure_lt_top
  have h7 : M.mu ((OO.map am : AddSubgroup E) : Set E) = c * M.mu (M.L.O : Set E) := by rw [hset, hc _ hO]
  have h8 : (c : ENNReal) * ((OO.map am).relIndex OO : ENNReal) = 1 := by
    have h9 : M.mu ((OO.map am : AddSubgroup E) : Set E) =
        (c * ((OO.map am).relIndex OO : ENNReal)) * M.mu ((OO.map am : AddSubgroup E) : Set E) := by
      conv_lhs => rw [h7]
      have : M.mu (M.L.O : Set E) = M.mu (OO : Set E) := rfl
      rw [this, hN, mul_assoc]
    have h10 : (1 : ENNReal) * M.mu ((OO.map am : AddSubgroup E) : Set E) =
        (c * ((OO.map am).relIndex OO : ENNReal)) * M.mu ((OO.map am : AddSubgroup E) : Set E) := by
      rw [one_mul]; exact h9
    exact ((ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h10).symm
  have h11 : (c : ℝ) * ((OO.map am).relIndex OO : ℝ) = 1 := by
    have := congrArg ENNReal.toReal h8
    simpa using this
  rw [hm]
  have hNq : ((qF F : ℝ)) ^ 2 ≤ ((OO.map am).relIndex OO : ℝ) := by
    rw [e5]; push_cast
    have : (qF F : ℝ) ≤ (J.index : ℝ) := by exact_mod_cast hq
    nlinarith [Nat.cast_nonneg (α := ℝ) (qF F)]
  have hq0 : (0 : ℝ) < (qF F : ℝ) ^ 2 := by
    have := two_le_residue_card hOK
    positivity
  rw [le_inv_comm₀ (by
    rcases (NNReal.coe_nonneg c).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at h11; exact absurd h11 zero_ne_one) hq0]
  have : ((c : ℝ))⁻¹ = ((OO.map am).relIndex OO : ℝ) := by
    exact inv_eq_of_mul_eq_one_right h11
  rw [this]; exact hNq

theorem ng_sum_castLE {n l : ℕ} (hl : l ≤ n) (g : Fin n → E) (hg : ∀ i : Fin n, l ≤ i.val → g i = 0) :
    ∑ i, g i = ∑ j : Fin l, g (Fin.castLE hl j) := by
  classical
  have h1 : ∑ j : Fin l, g (Fin.castLE hl j) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb hl), g i := by
    rw [Finset.sum_map]; rfl
  rw [h1]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply hg
  by_contra h
  push Not at h
  exact hi (Finset.mem_map.2 ⟨⟨i.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem ng_minor {n l : ℕ} (hl : l ≤ n) (Lo Z Up : Matrix (Fin n) (Fin n) E)
    (hLo : ∀ a d, a < d → Lo a d = 0) (hLo1 : ∀ a, Lo a a = 1)
    (hUp : ∀ c b, b < c → Up c b = 0) (hUp1 : ∀ a, Up a a = 1) :
    ((Lo * Z * Up).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have hsub : (Lo * Z * Up).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Lo.submatrix (Fin.castLE hl) (Fin.castLE hl) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Up.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [ng_sum_castLE hl _ (fun e he => by
      rw [hUp e (Fin.castLE hl b) (by
        rw [Fin.lt_def]; exact lt_of_lt_of_le b.2 he), mul_zero])]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [ng_sum_castLE hl _ (fun d hd => by
      rw [hLo (Fin.castLE hl a) d (by
        rw [Fin.lt_def]; exact lt_of_lt_of_le a.2 hd), zero_mul])]
  have hT1 : (Lo.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have h' : i < j := hij
    exact hLo _ _ (by rw [Fin.lt_def]; exact h')
  have hT2 : (Up.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id := by
    intro i j hij
    have h' : j < i := hij
    exact hUp _ _ (by rw [Fin.lt_def]; exact h')
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ hT1,
    Matrix.det_of_isUpperTriangular hT2]
  simp [hLo1, hUp1]

variable {H : HermSp M V} {r : ℕ}

theorem ng_Dl_term {P : FPair H r} {n n' : V ≃ₗ[E] V} (hn : n ∈ P.A.NSet) (hn' : n' ∈ P.B.NSet) (l : ℕ) :
    H.Dl (fun b => n (P.A.f b)) (fun b => n' (P.B.f b)) l = P.Dm l := by
  choose A h1 h2 h3 using N_row P.A hn
  choose B k1 k2 k3 using N_row P.B hn'
  unfold FPair.Dm HermSp.Dl
  by_cases hl : l ≤ r + 1
  · rw [dif_pos hl, dif_pos hl]
    have e : H.Zhat (fun b => n (P.A.f b)) (fun b => n' (P.B.f b)) =
        (Matrix.of fun a d => M.L.cj (A a d)) * H.Zhat P.A.f P.B.f * (Matrix.of fun c b => B b c) := by
      ext a b
      simp only [HermSp.Zhat, Matrix.of_apply, Matrix.mul_apply]
      rw [h3 a, k3 b, h_sum_left]
      simp only [h_sum_right]
      exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)
    rw [e]
    exact ng_minor hl _ _ _ (fun a d had => by simp [h1 a d had]) (fun a => by simp [h2 a])
      (fun c b hbc => by simp [k1 b c hbc]) (fun a => by simp [k2 a])
  · rw [dif_neg hl, dif_neg hl]

section Std

variable {Fr : FrameD H r} {L : Submodule M.L.O (H.Wb Fr.f)}

theorem ng_h_es_e (i b : Fin r) : H.h (Fr.es i) (Fr.e b) = if b = i then 1 else 0 := by
  show H.h (Fr.es i) (Fr.f b.castSucc) = _
  rw [H.h_herm (Fr.f b.castSucc) (Fr.es i), Fr.h_es]
  split_ifs <;> simp

theorem ng_prF_e (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.e b) = 0 := by
  classical
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  have z1 : ∑ i, H.h v (Fr.es i) * H.h (Fr.e i) (Fr.e b) = 0 :=
    Finset.sum_eq_zero (fun i _ => by
      rw [show H.h (Fr.e i) (Fr.e b) = 0 from Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last i).ne), mul_zero])
  have z2 : ∑ i, H.h v (Fr.e i) * H.h (Fr.es i) (Fr.e b) = H.h v (Fr.e b) := by
    rw [Finset.sum_eq_single b]
    · rw [ng_h_es_e, if_pos rfl, mul_one]
    · intro i _ hi; rw [ng_h_es_e, if_neg (Ne.symm hi), mul_zero]
    · intro h; exact absurd (Finset.mem_univ b) h
  rw [z1, z2]; ring

theorem ng_prF_es (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.es b) = 0 := by
  classical
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  have z1 : ∑ i, H.h v (Fr.es i) * H.h (Fr.e i) (Fr.es b) = H.h v (Fr.es b) := by
    rw [Finset.sum_eq_single b]
    · rw [show H.h (Fr.e b) (Fr.es b) = 1 from by have := Fr.h_es b b; rwa [if_pos rfl] at this, mul_one]
    · intro i _ hi
      rw [show H.h (Fr.e i) (Fr.es b) = 0 from by have := Fr.h_es i b; rwa [if_neg hi] at this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ b) h
  have z2 : ∑ i, H.h v (Fr.e i) * H.h (Fr.es i) (Fr.es b) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [Fr.h_ss, mul_zero])
  rw [z1, z2]; ring

theorem ng_expand (v y : V) : H.h v y = ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) y + H.h (Fr.prF v) y +
    ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) y := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]; ring

theorem ng_prF_prF (v w : V) : H.h (Fr.prF v) w = H.h (Fr.prF v) (Fr.prF w) := by
  rw [H.h_herm w (Fr.prF v), ng_expand (Fr := Fr) w (Fr.prF v)]
  have z1 : ∑ a, H.h w (Fr.es a) * H.h (Fr.e a) (Fr.prF v) = 0 :=
    Finset.sum_eq_zero (fun a _ => by rw [H.h_herm (Fr.prF v) (Fr.e a), ng_prF_e, map_zero, mul_zero])
  have z2 : ∑ a, H.h w (Fr.e a) * H.h (Fr.es a) (Fr.prF v) = 0 :=
    Finset.sum_eq_zero (fun a _ => by rw [H.h_herm (Fr.prF v) (Fr.es a), ng_prF_es, map_zero, mul_zero])
  rw [z1, z2, zero_add, add_zero, ← H.h_herm]

theorem ng_gen_int (hL : Fr.IsInner L) {v w : V}
    (hv : (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
      ∃ x : ↥(H.perp (H.X Fr.f)), (x : V) = Fr.prF v ∧ H.mkW Fr.f x ∈ L)
    (hw : (∀ a, H.h w (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h w (Fr.e a) ∈ M.L.O) ∧
      ∃ x : ↥(H.perp (H.X Fr.f)), (x : V) = Fr.prF w ∧ H.mkW Fr.f x ∈ L) : H.h v w ∈ M.L.O := by
  obtain ⟨v1, v2, x, hx, hxL⟩ := hv
  obtain ⟨w1, w2, y, hy, hyL⟩ := hw
  rw [ng_expand (Fr := Fr) v w, ng_prF_prF]
  refine M.L.O.add_mem (M.L.O.add_mem (M.L.O.sum_mem fun a _ => M.L.O.mul_mem (v1 a) ?_) ?_)
    (M.L.O.sum_mem fun a _ => M.L.O.mul_mem (v2 a) ?_)
  · rw [H.h_herm w (Fr.e a)]; exact Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (w2 a)
  · rw [← hx, ← hy]; exact (hL.2.1 x).1 hxL y hyL
  · rw [H.h_herm w (Fr.es a)]; exact Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (w1 a)

theorem ng_LamStd_int (hL : Fr.IsInner L) {v w : V} (hv : v ∈ Fr.LamStd L) (hw : w ∈ Fr.LamStd L) :
    H.h v w ∈ M.L.O := by
  have step : ∀ w', ((∀ a, H.h w' (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h w' (Fr.e a) ∈ M.L.O) ∧
      ∃ x : ↥(H.perp (H.X Fr.f)), (x : V) = Fr.prF w' ∧ H.mkW Fr.f x ∈ L) →
      ∀ v', v' ∈ Fr.LamStd L → H.h v' w' ∈ M.L.O := by
    intro w' hw' v' hv'
    unfold FrameD.LamStd at hv'
    induction hv' using Submodule.span_induction with
    | mem v hv => exact ng_gen_int hL hv hw'
    | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
    | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
    | smul c x _ hx =>
      have : H.h (c • x) w' = (c : E) * H.h x w' := H.h_smul_left (c : E) x _
      rw [this]; exact M.L.O.mul_mem c.2 hx
  rw [H.h_herm w v]
  apply Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O
  unfold FrameD.LamStd at hw
  induction hw using Submodule.span_induction with
  | mem w hw => rw [H.h_herm v w]; exact Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (step w hw v hv)
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
  | smul c x _ hx =>
    have : H.h (c • x) v = (c : E) * H.h x v := H.h_smul_left (c : E) x _
    rw [this]; exact M.L.O.mul_mem c.2 hx

end Std

theorem ng_norm_om {P : FPair H r} (hOK : M.OK) (t : Term V M r) : ‖om P t‖ = 1 := by
  unfold om FrameD.psiOf
  rw [norm_mul, norm_inv, norm_basic_character_eq_one hOK, norm_basic_character_eq_one hOK]
  simp

theorem ng_gram_base (P : FPair H r) : (H.gram (Sum.elim P.A.f P.B.f)).det = (-1) ^ (r + 1) * P.Gv := by
  set c : E →+* E := (M.L.cj : E ≃ₐ[F] E).toAlgHom.toRingHom with hc
  have hcx : ∀ x, c x = M.L.cj x := fun _ => rfl
  set Zh := H.Zhat P.A.f P.B.f with hZh
  have hG : H.gram (Sum.elim P.A.f P.B.f) =
      Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -(algebraMap F E P.A.T) else 0) Zh
        (Zh.transpose.map c) (Matrix.diagonal fun i => if i = Fin.last r then -(algebraMap F E P.B.T) else 0) := by
    ext i j
    rcases i with a | a <;> rcases j with b | b
    · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab
        by_cases ha : a = Fin.last r
        · subst ha; simp [P.A.h_zz]
        · simp [ha, P.A.h_iso a a (Or.inl ha)]
      · rw [if_neg hab]
        by_cases ha : a = Fin.last r
        · exact P.A.h_iso b a (Or.inl (fun h => hab (by rw [ha, h])))
        · exact P.A.h_iso b a (Or.inr ha)
    · simp [HermSp.gram, hZh, HermSp.Zhat]
    · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁, Matrix.map_apply,
        Matrix.transpose_apply, hZh, HermSp.Zhat, hcx]
      exact H.h_herm _ _
    · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab
        by_cases ha : a = Fin.last r
        · subst ha; simp [P.B.h_zz]
        · simp [ha, P.B.h_iso a a (Or.inl ha)]
      · rw [if_neg hab]
        by_cases ha : a = Fin.last r
        · exact P.B.h_iso b a (Or.inl (fun h => hab (by rw [ha, h])))
        · exact P.B.h_iso b a (Or.inr ha)
  rw [hG, Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.gramDetGen E r (Zh.transpose.map c) Zh]
  have d1 : (Zh.transpose.map c).det = M.L.cj Zh.det := by
    rw [← hcx, RingHom.map_det, ← Matrix.det_transpose]
    rfl
  have d2 : ((Zh.transpose.map c).submatrix Fin.castSucc Fin.castSucc).det =
      M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [← hcx, RingHom.map_det, ← Matrix.det_transpose]
    rfl
  have e1 : P.Dm (r + 1) = Zh.det := by
    unfold FPair.Dm HermSp.Dl
    rw [dif_pos le_rfl]
    rfl
  have e2 : P.Dm r = (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    unfold FPair.Dm HermSp.Dl
    rw [dif_pos (Nat.le_succ r)]
    rfl
  rw [d1, d2]
  unfold FPair.Gv HermSp.Gdet HermSp.normE
  change _ = (-1) ^ (r + 1) * (P.Dm (r + 1) * M.L.cj (P.Dm (r + 1)) - algebraMap F E (P.A.T * P.B.T) * (P.Dm r * M.L.cj (P.Dm r)))
  rw [e1, e2, map_mul]
  ring

theorem ng_theta_mem (M : Model F E) : ∃ a : 𝒪[F], (a : F) = theta M ∧ (a : F) ≠ 0 := by
  unfold theta
  split
  · exact ⟨1, rfl, one_ne_zero⟩
  · rename_i g _
    exact ⟨g.q, rfl, fun h => g.q_irr.ne_zero (Subtype.ext h)⟩

theorem ng_gram_MM (t : Term V M r) :
    (H.gram (H.MMfam t)).det =
      algebraMap F E (((theta M)⁻¹) ^ (2 * (r + 1))) * (H.gram (Sum.elim t.f t.f')).det := by
  rcases hs : M.split with _ | g
  · have hm : H.MMfam t = Sum.elim t.f t.f' := by
      unfold HermSp.MMfam
      split
      · rfl
      · rename_i g hg
        rw [hs] at hg
        cases hg
    rw [hm, theta_eq_one hs]; simp
  · have hm : H.MMfam t = Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
      unfold HermSp.MMfam
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    have hθ : theta M = (g.q : F) := by
      unfold theta
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    set c : E := algebraMap F E ((g.q : F)⁻¹) with hc
    rw [hm, hθ, gram_det_change (Sum.elim t.f t.f') _
      (Matrix.fromBlocks 1 0 (-(c • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) (c • 1))]
    · rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, one_mul,
        mul_one, map_pow, hc, AlgEquiv.commutes, map_pow]
      ring
    · classical
      rintro (a | a)
      · simp [Fintype.sum_sum_type, Matrix.one_apply]
      · simp [Fintype.sum_sum_type, Matrix.one_apply, smul_sub]
        abel

theorem ng_smulLat {c c' : E} (hcc : c' * c = 1) {abelian₂ : Submodule M.L.O V} {x : V} (hx : x ∈ H.smulLat c abelian₂) :
    c' • x ∈ abelian₂ := by
  unfold HermSp.smulLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    show c' • c • v ∈ abelian₂
    rw [smul_smul, hcc, one_smul]; exact hv
  | zero => rw [smul_zero]; exact abelian₂.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact abelian₂.add_mem hx hy
  | smul o x _ hx =>
    have : c' • (o • x) = o • (c' • x) := by
      show c' • ((o : E) • x) = (o : E) • (c' • x)
      rw [smul_smul, smul_smul, mul_comm]
    rw [this]; exact abelian₂.smul_mem o hx

theorem ng_det_mem {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι E) (h : ∀ a b, G a b ∈ M.L.O) :
    G.det ∈ M.L.O := by
  let G₀ : Matrix ι ι M.L.O := fun a b => ⟨G a b, h a b⟩
  have hG₀ : G = G₀.map M.L.O.subtype := by ext a b; rfl
  rw [hG₀, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact G₀.det.2

variable {P : FPair H r}

theorem ng_term_int {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {v w : V} (hv : v ∈ t.abelian₂)
    (hw : w ∈ t.abelian₂) : H.h v w ∈ M.L.O := by
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, _, _⟩ := ht
  have hnU := (mem_NSet_of_mem_N P.A hn).1
  rw [hL] at hv hw
  obtain ⟨v0, hv0, rfl⟩ := hv
  obtain ⟨w0, hw0, rfl⟩ := hw
  show H.h (n v0) (n w0) ∈ _
  rw [hnU]
  exact ng_LamStd_int d.hL hv0 hw0

theorem ng_term_f {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) (b : Fin (r + 1)) :
    t.f b ∈ t.abelian₂ ∧ t.f' b ∈ t.abelian₂ := by
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  constructor
  · rw [hf, hL]; exact ⟨P.A.f b, f_mem_LamStd d.hL b, rfl⟩
  · rw [hf', hL']; exact ⟨P.B.f b, f_mem_LamStd d.hL' b, rfl⟩

theorem ng_term_MM {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.MMfam t j ∈ t.abelian₂ := by
  have hf := ng_term_f ht
  rcases hs : M.split with _ | g
  · have hm : H.MMfam t = Sum.elim t.f t.f' := by
      unfold HermSp.MMfam
      split
      · rfl
      · rename_i g hg
        rw [hs] at hg
        cases hg
    rw [hm]
    rcases j with b | b
    · exact (hf b).1
    · exact (hf b).2
  · have hm : H.MMfam t = Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
      unfold HermSp.MMfam
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    rw [hm]
    rcases j with b | b
    · exact (hf b).1
    · have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
      exact ng_smulLat (H := H) (by rw [← map_mul, inv_mul_cancel₀ hq, map_one]) ((ht.2.2.2.2 g hs).1 b)

theorem ng_term_gram {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) :
    (H.gram (H.MMfam t)).det = (H.gram P.MMgen).det := by
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  obtain ⟨A, hA, hA'⟩ := N_matrix P.A (mem_NSet_of_mem_N P.A hn)
  obtain ⟨B, hB, hB'⟩ := N_matrix P.B (mem_NSet_of_mem_N P.B hn')
  unfold FPair.MMgen
  rw [ng_gram_MM, ng_gram_MM]
  congr 1
  show _ = (H.gram (Sum.elim P.A.f P.B.f)).det
  rw [gram_det_change (Sum.elim P.A.f P.B.f) (Sum.elim t.f t.f') (Matrix.fromBlocks A 0 0 B)]
  · rw [Matrix.det_fromBlocks_zero₂₁, hA, hB]; simp
  · rintro (a | a)
    · simp [Fintype.sum_sum_type, hf, hA' a]
    · simp [Fintype.sum_sum_type, hf', hB' a]

theorem ng_term_Dm {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) (l : ℕ) : P.Dm l ∈ M.L.O := by
  have hint := fun v hv w hw => ng_term_int ht (v := v) (w := w) hv hw
  have hff := ng_term_f ht
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  rw [← ng_Dl_term (mem_NSet_of_mem_N P.A hn) (mem_NSet_of_mem_N P.B hn') l, ← hf, ← hf']
  unfold HermSp.Dl
  split_ifs with hl
  · exact ng_det_mem _ (fun a b => hint _ (hff _).2 _ (hff _).1)
  · exact M.L.O.zero_mem

theorem ng_G_unit (hG : P.Gv ≠ 0) : IsUnit P.Gv := by
  have hfix : M.L.cj P.Gv = P.Gv := by
    unfold FPair.Gv HermSp.Gdet HermSp.normE
    simp only [map_sub, map_mul, M.L.cj_cj, AlgEquiv.commutes]
    ring
  obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
  have ha0 : a ≠ 0 := fun h => hG (by rw [← ha, h, map_zero])
  rw [← ha]
  exact ha0.isUnit.map (algebraMap F E)

theorem ng_gramMM_unit (hG : P.Gv ≠ 0) : IsUnit (H.gram P.MMgen).det := by
  obtain ⟨a, ha, ha0⟩ := ng_theta_mem M
  unfold FPair.MMgen
  rw [ng_gram_MM]
  show IsUnit (_ * (H.gram (Sum.elim P.A.f P.B.f)).det)
  rw [ng_gram_base]
  refine IsUnit.mul (IsUnit.map (algebraMap F E) ?_) (IsUnit.mul (IsUnit.pow _ isUnit_one.neg) (ng_G_unit hG))
  rw [← ha]
  exact (pow_ne_zero _ (inv_ne_zero ha0)).isUnit

theorem ng_factors (hOK : M.OK) (hG : P.Gv ≠ 0) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) :
    (0 < M.modK (algebraMap F E (theta M)) ∧ M.modK (algebraMap F E (theta M)) ≤ 1) ∧
    (0 < M.modK (H.gram P.MMgen).det ∧ M.modK (H.gram P.MMgen).det ≤ 1) ∧
    (0 < ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) ∧
      ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, ha, ha0⟩ := ng_theta_mem M
    have h := ng_modK hOK (x := algebraMap F E (theta M)) (by rw [← ha]; exact ha0.isUnit.map _)
    exact ⟨h.1, h.2 (by rw [← ha]; exact Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L a)⟩
  · have h := ng_modK hOK (ng_gramMM_unit (P := P) hG)
    refine ⟨h.1, h.2 ?_⟩
    rw [← ng_term_gram ht]
    exact ng_det_mem _ (fun a b => ng_term_int ht (ng_term_MM ht _) (ng_term_MM ht _))
  · have hl : ∀ l ∈ P.ends, 0 < M.modK (P.Dm l * M.L.cj (P.Dm l)) ∧ M.modK (P.Dm l * M.L.cj (P.Dm l)) ≤ 1 := by
      intro l hl
      have hu : IsUnit (P.Dm l) := by
        unfold FPair.ends at hl
        exact (((@Finset.mem_filter _ _ (Classical.decPred _) _ _).1 hl).2).2
      have h := ng_modK hOK (hu.mul (hu.map M.L.cj))
      exact ⟨h.1, h.2 (M.L.O.mul_mem (ng_term_Dm ht l) (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l)))⟩
    exact ⟨Finset.prod_pos (fun l h => (hl l h).1),
      Finset.prod_le_one (fun l h => (hl l h).1.le) (fun l h => (hl l h).2)⟩

omit [TopologicalSpace E] [MeasurableSpace E] [CommRing E] in
theorem ng_real_one {a b c : ℝ} (a0 : 0 < a) (a1 : a ≤ 1) (b0 : 0 < b) (b1 : b ≤ 1) (c0 : 0 < c) (c1 : c ≤ 1) :
    1 ≤ (a * b * c) ^ (-(1 / 2 : ℝ)) := by
  refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) ?_ (by norm_num)
  calc a * b * c ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

theorem ng_Hp_ge_one (hOK : M.OK) (hG : P.Gv ≠ 0) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) :
    1 ≤ P.Hp := by
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, c0, c1⟩ := ng_factors hOK hG ht
  unfold FPair.Hp
  exact ng_real_one a0 a1 b0 b1 c0 c1

omit [TopologicalSpace E] [MeasurableSpace E] [CommRing E] in
theorem ng_real_q {a b c q : ℝ} (hq : 0 < q) (a0 : 0 < a) (a1 : a ≤ 1) (b0 : 0 < b) (b1 : b ≤ 1) (c0 : 0 < c) (c1 : c ≤ 1)
    (h : a ≤ (q ^ 2)⁻¹ ∨ b ≤ (q ^ 2)⁻¹) : q ≤ (a * b * c) ^ (-(1 / 2 : ℝ)) := by
  have hx : a * b * c ≤ (q ^ 2)⁻¹ := by
    rcases h with h | h
    · calc a * b * c ≤ a * 1 * 1 := by gcongr
        _ = a := by ring
        _ ≤ _ := h
    · calc a * b * c ≤ 1 * b * 1 := by gcongr
        _ = b := by ring
        _ ≤ _ := h
  have e : ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) = q := by
    rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv, ← Real.sqrt_eq_rpow, Real.sqrt_sq hq.le]
  calc q = ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) := e.symm
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hx (by norm_num)

theorem ng_q_le_Hp (hOK : M.OK) (hG : P.Gv ≠ 0) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t)
    (hB : BBne (H := H) t) : (qF F : ℝ) ≤ P.Hp := by
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, c0, c1⟩ := ng_factors hOK hG ht
  have hq : (0 : ℝ) < qF F := by
    have := two_le_residue_card hOK
    exact_mod_cast (by omega : 0 < qF F)
  have hnt := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
  unfold FPair.Hp
  refine ng_real_q hq a0 a1 b0 b1 c0 c1 ?_
  rcases hs : M.split with _ | g
  · right
    have hfix : M.L.cj P.Gv = P.Gv := by
      unfold FPair.Gv HermSp.Gdet HermSp.normE
      simp only [map_sub, map_mul, M.L.cj_cj, AlgEquiv.commutes]
      ring
    obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
    have hdet : (H.gram P.MMgen).det = algebraMap F E ((-1) ^ (r + 1) * a) := by
      rw [gram_det_eq P hs, ← ha, map_mul, map_pow, map_neg, map_one]
    have hmem : (H.gram P.MMgen).det ∈ M.L.O := by
      rw [← ng_term_gram ht]
      exact ng_det_mem _ (fun a b => ng_term_int ht (ng_term_MM ht _) (ng_term_MM ht _))
    have haO : (-1) ^ (r + 1) * a ∈ 𝒪[F] := Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (by rw [← hdet]; exact hmem)
    have ha0 : (-1) ^ (r + 1) * a ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (fun h => hG ?_)
      rw [← ha, h, map_zero]
    rw [hdet]
    refine ng_modK_nonunit hOK ⟨_, haO⟩ ha0 (fun hu => ?_)
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    refine not_BBne_of (ng_term_MM ht) (fun v hv j => ng_term_int ht hv (ng_term_MM ht j)) ?_ hB
    rw [ng_term_gram ht]
    refine ⟨hmem, algebraMap F E (y : F), Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L y, ?_⟩
    rw [hdet, ← map_mul]
    have : ((-1) ^ (r + 1) * a) * (y : F) = 1 := congrArg Subtype.val hy
    rw [this, map_one]
  · left
    have hθ : theta M = (g.q : F) := by
      unfold theta
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    rw [hθ]
    exact ng_modK_nonunit hOK g.q (fun h => g.q_irr.ne_zero (Subtype.ext h)) g.q_irr.not_isUnit

def NgOrth (P : FPair H r) (k : V) : Prop := (∀ b, H.h k (P.A.f b) = 0) ∧ ∀ b, H.h k (P.B.f b) = 0

theorem ng_frame_back (Fr : FrameD H r) {g : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet) (a : Fin (r + 1)) :
    ∃ row : Fin (r + 1) → E, Fr.f a = ∑ b, row b • g (Fr.f b) := by
  obtain ⟨row, -, -, h⟩ := N_row Fr (NSet_inv Fr hg) a
  refine ⟨row, ?_⟩
  have h1 : g ((g⁻¹ : V ≃ₗ[E] V) (Fr.f a)) = Fr.f a := LinearEquiv.apply_symm_apply g _
  rw [← h1, h, map_sum]
  exact Finset.sum_congr rfl (fun b _ => by rw [map_smul])

theorem ng_orth_back (Fr : FrameD H r) {g : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet) {k : V}
    (h : ∀ b, H.h k (g (Fr.f b)) = 0) (a : Fin (r + 1)) : H.h k (Fr.f a) = 0 := by
  obtain ⟨row, hrow⟩ := ng_frame_back Fr hg a
  rw [hrow, h_sum_right]
  exact Finset.sum_eq_zero (fun b _ => by rw [h b, mul_zero])

theorem ng_mulVec_gram {ι : Type} [Fintype ι] (m : ι → V) (c : ι → E) (j : ι) :
    ((H.gram m).mulVec c) j = H.h (∑ i, c i • m i) (m j) := by
  rw [h_sum_left]
  simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem ng_split {ι : Type} [Fintype ι] [DecidableEq ι] (abelian₂ : Submodule M.L.O V) (m : ι → V)
    (hmem : ∀ j, m j ∈ abelian₂) (hint : ∀ v ∈ abelian₂, ∀ j, H.h v (m j) ∈ M.L.O) (hu : IsUnitO M (H.gram m).det)
    (v : V) (hv : v ∈ abelian₂) :
    ∃ m0 ∈ Submodule.span M.L.O (Set.range m), v - m0 ∈ abelian₂ ∧ ∀ j, H.h (v - m0) (m j) = 0 := by
  set G := H.gram m with hG
  let G₀ : Matrix ι ι M.L.O := fun a b => ⟨G a b, hint (m b) (hmem b) a⟩
  have hG₀ : G = G₀.map M.L.O.subtype := by ext a b; rfl
  have hadj : ∀ a b, G.adjugate a b ∈ M.L.O := by
    intro a b
    rw [hG₀, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    exact (G₀.adjugate a b).2
  obtain ⟨_, y0, hy0, hdy⟩ := hu
  set y : ι → E := fun j => H.h v (m j) with hy
  set c : ι → E := y0 • G.adjugate.mulVec y with hc
  have hcO : ∀ i, c i ∈ M.L.O := by
    intro i
    simp only [hc, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact M.L.O.mul_mem hy0 (M.L.O.sum_mem (fun j _ => M.L.O.mul_mem (hadj i j) (hint v hv j)))
  have hGc : G.mulVec c = y := by
    rw [hc, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, mul_comm y0, hdy, one_smul]
  have hm0 : ∑ i, c i • m i ∈ Submodule.span M.L.O (Set.range m) := by
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have : c i • m i = (⟨c i, hcO i⟩ : M.L.O) • m i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨_, hm0, abelian₂.sub_mem hv ?_, fun j => ?_⟩
  · exact (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hmem j)) hm0
  · rw [h_sub_left, ← ng_mulVec_gram, ← hG, hGc]
    simp [hy]

theorem ng_zero {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → V) (hu : IsUnit (H.gram m).det) {u : V}
    (hsp : u ∈ Submodule.span E (Set.range m)) (ho : ∀ j, H.h u (m j) = 0) : u = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hsp
  have h0 : (H.gram m).mulVec c = 0 := by
    funext j
    rw [ng_mulVec_gram]; exact ho j
  have h1 : (H.gram m).det • c = 0 := by
    have e : (H.gram m).adjugate.mulVec ((H.gram m).mulVec c) = (H.gram m).det • c := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← e, h0, Matrix.mulVec_zero]
  have h2 : c = 0 := by
    funext i
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact (hu.mul_right_eq_zero).1 this
  rw [h2]; simp

theorem ng_MM_L (hs : M.split = none) (t : Term V M r) : H.MMfam t = Sum.elim t.f t.f' := by
  unfold HermSp.MMfam
  split
  · rfl
  · rename_i g hg
    rw [hs] at hg
    cases hg

theorem ng_term_split (hP : P.PrimeTo) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {v : V}
    (hv : v ∈ t.abelian₂) :
    ∃ m0 ∈ Submodule.span M.L.O (Set.range (Sum.elim t.f t.f')), v - m0 ∈ t.abelian₂ ∧ NgOrth P (v - m0) := by
  have hs := hP.1
  have hu : IsUnitO M (H.gram (Sum.elim t.f t.f')).det := by
    rw [← ng_MM_L hs t, ng_term_gram ht, gram_det_eq P hs]
    exact isUnitO_mul (isUnitO_neg_one_pow _) hP.2.1
  have hmem : ∀ j, Sum.elim t.f t.f' j ∈ t.abelian₂ := by rw [← ng_MM_L hs t]; exact ng_term_MM ht
  obtain ⟨m0, h1, h2, h3⟩ := ng_split t.abelian₂ _ hmem (fun v hv j => ng_term_int ht hv (hmem j)) hu v hv
  refine ⟨m0, h1, h2, ?_⟩
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  constructor
  · refine ng_orth_back P.A (mem_NSet_of_mem_N P.A hn) (fun b => ?_)
    have := h3 (Sum.inl b)
    rwa [Sum.elim_inl, hf] at this
  · refine ng_orth_back P.B (mem_NSet_of_mem_N P.B hn') (fun b => ?_)
    have := h3 (Sum.inr b)
    rwa [Sum.elim_inr, hf'] at this

theorem ng_span_base {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {x : V}
    (hx : x ∈ Submodule.span M.L.O (Set.range (Sum.elim t.f t.f'))) :
    x ∈ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)) := by
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rcases j with b | b
    · obtain ⟨row, -, -, h⟩ := N_row P.A (mem_NSet_of_mem_N P.A hn) b
      rw [Sum.elim_inl, hf]
      show n (P.A.f b) ∈ _
      rw [h]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
    · obtain ⟨row, -, -, h⟩ := N_row P.B (mem_NSet_of_mem_N P.B hn') b
      rw [Sum.elim_inr, hf']
      show n' (P.B.f b) ∈ _
      rw [h]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul o x _ hx => exact Submodule.smul_mem _ (o : E) hx

theorem ng_K_eq (hP : P.PrimeTo) {d : Datum P} {t₁ t₂ : Term V M r} (h₁ : IsTermOver P d t₁) (h₂ : IsTermOver P d t₂)
    {w : V} (hw : w ∈ t₁.abelian₂) (ho : NgOrth P w) : w ∈ t₂.abelian₂ := by
  have hs := hP.1
  obtain ⟨_, _, ⟨n₁, hn₁, hf₁, hL₁⟩, _, _⟩ := h₁
  have h₂' := h₂
  obtain ⟨_, _, ⟨n₂, hn₂, hf₂, hL₂⟩, _, _⟩ := h₂'
  have hN₁ := mem_NSet_of_mem_N P.A hn₁
  have hN₂ := mem_NSet_of_mem_N P.A hn₂
  rw [hL₁] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  change NgOrth P (n₁ w0) at ho

  have hperp : n₁ w0 ∈ H.perp (H.X P.A.f) := by
    intro x hx
    unfold HermSp.X at hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact ho.1 _
    | zero => rw [H.h_herm 0 _, H.h_zero_left, map_zero]
    | add x y _ _ hx hy => rw [H.h_herm (x + y) _, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm, hx, hy, add_zero]
    | smul c x _ hx => rw [H.h_herm (c • x) _, H.h_smul_left, map_mul, ← H.h_herm, hx, mul_zero]
  have hx1 : w0 - n₁ w0 ∈ H.X P.A.f := by
    have := (NSet_inv P.A hN₁).2.2 _ hperp
    have e : (n₁⁻¹ : V ≃ₗ[E] V) (n₁ w0) = w0 := LinearEquiv.symm_apply_apply n₁ w0
    rwa [e] at this
  have hx2 : n₂ (n₁ w0) - n₁ w0 ∈ H.X P.A.f := hN₂.2.2 _ hperp
  have hx3 : n₂ (w0 - n₁ w0) ∈ H.X P.A.f := by
    rw [← Fj_r] at hx1 ⊢
    exact NSet_apply_Fj P.A hN₂ le_rfl hx1
  have hx : n₂ w0 - n₁ w0 ∈ H.X P.A.f := by
    have e : n₂ w0 - n₁ w0 = n₂ (w0 - n₁ w0) + (n₂ (n₁ w0) - n₁ w0) := by rw [map_sub]; abel
    rw [e]; exact Submodule.add_mem _ hx3 hx2
  have hu2 : n₂ w0 ∈ t₂.abelian₂ := by rw [hL₂]; exact ⟨w0, hw0, rfl⟩
  obtain ⟨m0, hm0, hk, hko⟩ := ng_term_split hP h₂ hu2
  have hXle : H.X P.A.f ≤ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)) := by
    unfold HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl a.castSucc, rfl⟩
  have hz : n₁ w0 - (n₂ w0 - m0) = 0 := by
    refine ng_zero (H := H) (Sum.elim P.A.f P.B.f) ?_ ?_ ?_
    · rw [ng_gram_base]
      exact IsUnit.mul (IsUnit.pow _ isUnit_one.neg) (ng_G_unit (by
        intro h0
        obtain ⟨_, y, _, hy⟩ := hP.2.1
        rw [h0, zero_mul] at hy
        have := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
        exact zero_ne_one hy))
    · have e : n₁ w0 - (n₂ w0 - m0) = m0 - (n₂ w0 - n₁ w0) := by abel
      rw [e]
      exact Submodule.sub_mem _ (ng_span_base h₂ hm0) (hXle hx)
    · rintro (b | b)
      · rw [Sum.elim_inl, h_sub_left, ho.1, hko.1, sub_zero]
      · rw [Sum.elim_inr, h_sub_left, ho.2, hko.2, sub_zero]
  have : (n₁ : V → V) w0 = n₂ w0 - m0 := sub_eq_zero.1 hz
  show n₁ w0 ∈ t₂.abelian₂
  rw [this]; exact hk

theorem ng_orth_perp (Fr : FrameD H r) {k : V} (h : ∀ b, H.h k (Fr.f b) = 0) : k ∈ H.perp (H.X Fr.f) := by
  intro x hx
  unfold HermSp.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h _
  | zero => rw [H.h_herm 0 _, H.h_zero_left, map_zero]
  | add x y _ _ hx hy => rw [H.h_herm (x + y) _, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_herm (c • x) _, H.h_smul_left, map_mul, ← H.h_herm, hx, mul_zero]

theorem ng_X_le_Xp (f : Fin (r + 1) → V) : H.X f ≤ H.Xp f := by
  unfold HermSp.X HermSp.Xp
  exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, rfl⟩)

theorem ng_St_fix (hX : H.Xp P.A.f ⊓ H.Xp P.B.f = ⊥) {s : V ≃ₗ[E] V} (hs : s ∈ P.St) {k : V} (ho : NgOrth P k) :
    s k = k := by
  have h1 := (mem_NSet_of_mem_N P.A hs.1).2.2 k (ng_orth_perp P.A ho.1)
  have h2 := (mem_NSet_of_mem_N P.B hs.2).2.2 k (ng_orth_perp P.B ho.2)
  have h3 : s k - k ∈ H.Xp P.A.f ⊓ H.Xp P.B.f := ⟨ng_X_le_Xp _ h1, ng_X_le_Xp _ h2⟩
  rw [hX, Submodule.mem_bot] at h3
  exact sub_eq_zero.1 h3

def NGOneClass (P : FPair H r) : Prop :=
  ∀ n₁ ∈ P.A.N, ∀ n₁' ∈ P.B.N, ∀ n₂ ∈ P.A.N, ∀ n₂' ∈ P.B.N,
    (∀ a b, H.h (n₁' (P.B.f b)) (n₁ (P.A.f a)) ∈ M.L.O) → (∀ a b, H.h (n₂' (P.B.f b)) (n₂ (P.A.f a)) ∈ M.L.O) →
    ∃ s ∈ P.St,
      Submodule.span M.L.O (Set.range fun b => s (n₁ (P.A.f b))) = Submodule.span M.L.O (Set.range fun b => n₂ (P.A.f b)) ∧
      Submodule.span M.L.O (Set.range fun b => s (n₁' (P.B.f b))) = Submodule.span M.L.O (Set.range fun b => n₂' (P.B.f b))

def NGMassOne (P : FPair H r) : Prop := ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → mu P t = 1

theorem ng_unique (hP : P.PrimeTo) (hX : H.Xp P.A.f ⊓ H.Xp P.B.f = ⊥) (hC : NGOneClass P) {d : Datum P}
    {t₁ t₂ : Term V M r} (h₁ : IsTermOver P d t₁) (h₂ : IsTermOver P d t₂) : TRel P t₁ t₂ := by
  have hs := hP.1
  have hf1 := ng_term_f h₁
  have hf2 := ng_term_f h₂
  have i1 := fun a b => ng_term_int h₁ (hf1 b).2 (hf1 a).1
  have i2 := fun a b => ng_term_int h₂ (hf2 b).2 (hf2 a).1
  have g₁ := h₁
  have g₂ := h₂
  obtain ⟨_, _, ⟨n₁, hn₁, e₁, -⟩, ⟨n₁', hn₁', e₁', -⟩, _⟩ := g₁
  obtain ⟨_, _, ⟨n₂, hn₂, e₂, -⟩, ⟨n₂', hn₂', e₂', -⟩, _⟩ := g₂
  obtain ⟨s, hsS, hA, hB⟩ := hC n₁ hn₁ n₁' hn₁' n₂ hn₂ n₂' hn₂'
    (fun a b => by have := i1 a b; rwa [e₁, e₁'] at this) (fun a b => by have := i2 a b; rwa [e₂, e₂'] at this)
  refine ⟨s, hsS, ?_⟩
  set sO : V →ₗ[M.L.O] V := ((s : V →ₗ[E] V).restrictScalars M.L.O) with hsO
  have hsv : ∀ v, sO v = s v := fun _ => rfl
  have hM : (Submodule.span M.L.O (Set.range (Sum.elim t₁.f t₁.f'))).map sO =
      Submodule.span M.L.O (Set.range (Sum.elim t₂.f t₂.f')) := by
    rw [Set.Sum.elim_range, Set.Sum.elim_range, Submodule.span_union, Submodule.span_union, Submodule.map_sup,
      Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp, e₁, e₁', e₂, e₂']
    exact congrArg₂ _ hA hB
  have hM1 : Submodule.span M.L.O (Set.range (Sum.elim t₁.f t₁.f')) ≤ t₁.abelian₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with b | b
    · exact (hf1 b).1
    · exact (hf1 b).2
  have hM2 : Submodule.span M.L.O (Set.range (Sum.elim t₂.f t₂.f')) ≤ t₂.abelian₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with b | b
    · exact (hf2 b).1
    · exact (hf2 b).2
  unfold img
  rw [← hsO]
  apply le_antisymm
  · intro v hv
    obtain ⟨m0, hm0, hk, hko⟩ := ng_term_split hP h₂ hv
    rw [← hM] at hm0
    obtain ⟨m0', hm0', rfl⟩ := hm0
    refine ⟨m0' + (v - sO m0'), t₁.abelian₂.add_mem (hM1 hm0') (ng_K_eq hP h₂ h₁ hk hko), ?_⟩
    rw [map_add, hsv (v - sO m0'), ng_St_fix hX hsS hko]
    abel
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨m0, hm0, hk, hko⟩ := ng_term_split hP h₁ hv
    have e : sO v = sO m0 + (v - m0) := by
      have : v = m0 + (v - m0) := by abel
      conv_lhs => rw [this]
      rw [map_add, hsv (v - m0), ng_St_fix hX hsS hko]
    rw [e]
    refine t₂.abelian₂.add_mem (hM2 ?_) (ng_K_eq hP h₁ h₂ hk hko)
    rw [← hM]
    exact ⟨m0, hm0, rfl⟩

theorem NGEqStep'_of (hP : P.PrimeTo) (hX : H.Xp P.A.f ⊓ H.Xp P.B.f = ⊥) (hC : NGOneClass P) (hm : NGMassOne P)
    (R : Reps P) : NGEqStep' P R := fun d =>
  ⟨fun t₁ ht₁ t₂ ht₂ => (R.hRT d).2.2 t₁ ht₁ t₂ ht₂ (ng_unique hP hX hC ((R.hRT d).1 ht₁) ((R.hRT d).1 ht₂)),
    fun t ht => hm d t ((R.hRT d).1 ht)⟩

theorem ng_img_mul (g g' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * g') Λ = img g (img g' Λ) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨g' x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

theorem ng_img_one (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hv; exact ⟨v, hv, rfl⟩

theorem ng_img_inv {g : V ≃ₗ[E] V} {Λ Λ' : Submodule M.L.O V} (h : img g Λ = Λ') : img g⁻¹ Λ' = Λ := by
  rw [← h, ← ng_img_mul, inv_mul_cancel, ng_img_one]

theorem ng_img_mono (g : V ≃ₗ[E] V) {Λ Λ' : Submodule M.L.O V} (h : Λ ≤ Λ') : img g Λ ≤ img g Λ' :=
  Submodule.map_mono h

theorem ng_mem_Aut {g : V ≃ₗ[E] V} {Λ : Submodule M.L.O V} : g ∈ Aut Λ ↔ img g Λ = Λ := by
  constructor
  · intro hg
    unfold Aut at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ng_img_one Λ
    | mul x y _ _ hx hy => rw [ng_img_mul, hy, hx]
    | inv x _ hx => exact ng_img_inv hx
  · intro h; exact Subgroup.subset_closure h

def ngM (f f' : Fin (r + 1) → V) : Submodule M.L.O V := Submodule.span M.L.O (Set.range (Sum.elim f f'))

theorem ng_img_M (s : V ≃ₗ[E] V) (f f' : Fin (r + 1) → V) :
    img s (ngM (M := M) f f') = ngM (M := M) (fun b => s (f b)) (fun b => s (f' b)) := by
  unfold img ngM
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext j
  rcases j with b | b <;> rfl

theorem ng_M_eq {f f' g g' : Fin (r + 1) → V}
    (h : Submodule.span M.L.O (Set.range f) = Submodule.span M.L.O (Set.range g))
    (h' : Submodule.span M.L.O (Set.range f') = Submodule.span M.L.O (Set.range g')) :
    ngM (M := M) f f' = ngM (M := M) g g' := by
  unfold ngM
  rw [Set.Sum.elim_range, Set.Sum.elim_range, Submodule.span_union, Submodule.span_union, h, h']

theorem ng_img_of_M (hP : P.PrimeTo) (hX : H.Xp P.A.f ⊓ H.Xp P.B.f = ⊥) {d : Datum P}
    {t₁ t₂ : Term V M r} (h₁ : IsTermOver P d t₁) (h₂ : IsTermOver P d t₂) {s : V ≃ₗ[E] V} (hsS : s ∈ P.St)
    (hM : img s (ngM (M := M) t₁.f t₁.f') = ngM (M := M) t₂.f t₂.f') : img s t₁.abelian₂ = t₂.abelian₂ := by
  have hf1 := ng_term_f h₁
  have hf2 := ng_term_f h₂
  have hM1 : ngM (M := M) t₁.f t₁.f' ≤ t₁.abelian₂ := by
    unfold ngM
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with b | b
    · exact (hf1 b).1
    · exact (hf1 b).2
  have hM2 : ngM (M := M) t₂.f t₂.f' ≤ t₂.abelian₂ := by
    unfold ngM
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with b | b
    · exact (hf2 b).1
    · exact (hf2 b).2
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨m0, hm0, hk, hko⟩ := ng_term_split hP h₁ hv
    show s v ∈ t₂.abelian₂
    have e : s v = s m0 + (v - m0) := by
      have : v = m0 + (v - m0) := by abel
      conv_lhs => rw [this]
      rw [map_add, ng_St_fix hX hsS hko]
    rw [e]
    refine t₂.abelian₂.add_mem (hM2 ?_) (ng_K_eq hP h₁ h₂ hk hko)
    rw [← hM]
    exact ⟨m0, hm0, rfl⟩
  · intro v hv
    obtain ⟨m0, hm0, hk, hko⟩ := ng_term_split hP h₂ hv
    change m0 ∈ ngM (M := M) t₂.f t₂.f' at hm0
    rw [← hM] at hm0
    obtain ⟨m0', hm0', hm⟩ := hm0
    have hm' : s m0' = m0 := hm
    refine ⟨m0' + (v - m0), t₁.abelian₂.add_mem (hM1 hm0') (ng_K_eq hP h₂ h₁ hk hko), ?_⟩
    show s (m0' + (v - m0)) = v
    rw [map_add, ng_St_fix hX hsS hko, hm']
    abel

def ngME (P : FPair H r) : Submodule E V := Submodule.span E (Set.range (Sum.elim P.A.f P.B.f))

theorem ng_St_ME {s : V ≃ₗ[E] V} (hs : s ∈ P.St) {x : V} (hx : x ∈ ngME P) : s x ∈ ngME P := by
  unfold ngME at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rcases j with b | b
    · obtain ⟨row, -, -, h⟩ := N_row P.A (mem_NSet_of_mem_N P.A hs.1) b
      rw [Sum.elim_inl, h]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
    · obtain ⟨row, -, -, h⟩ := N_row P.B (mem_NSet_of_mem_N P.B hs.2) b
      rw [Sum.elim_inr, h]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem ng_ME_le {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) :
    ngME P ≤ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  unfold ngME
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rcases j with a | a
  · obtain ⟨row, hrow⟩ := ng_frame_back P.A (mem_NSet_of_mem_N P.A hn) a
    rw [Sum.elim_inl, hrow]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, ?_⟩))
    rw [Sum.elim_inl, hf]
  · obtain ⟨row, hrow⟩ := ng_frame_back P.B (mem_NSet_of_mem_N P.B hn') a
    rw [Sum.elim_inr, hrow]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, ?_⟩))
    rw [Sum.elim_inr, hf']

theorem ng_Aut_iff (hP : P.PrimeTo) (hX : H.Xp P.A.f ⊓ H.Xp P.B.f = ⊥) {d : Datum P} {t : Term V M r}
    (ht : IsTermOver P d t) {s : V ≃ₗ[E] V} (hsS : s ∈ P.St) :
    s ∈ Aut t.abelian₂ ↔ img s (ngM (M := M) t.f t.f') = ngM (M := M) t.f t.f' := by
  rw [ng_mem_Aut]
  have hs := hP.1
  have hu : IsUnitO M (H.gram (Sum.elim t.f t.f')).det := by
    rw [← ng_MM_L hs t, ng_term_gram ht, gram_det_eq P hs]
    exact isUnitO_mul (isUnitO_neg_one_pow _) hP.2.1
  have hmem : ∀ j, Sum.elim t.f t.f' j ∈ t.abelian₂ := by rw [← ng_MM_L hs t]; exact ng_term_MM ht
  have hMle : ngM (M := M) t.f t.f' ≤ t.abelian₂ := by
    unfold ngM
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hmem j
  have half : ∀ s' : V ≃ₗ[E] V, s' ∈ P.St → img s' t.abelian₂ = t.abelian₂ → img s' (ngM (M := M) t.f t.f') ≤ ngM (M := M) t.f t.f' := by
    rintro s' hs' hΛ _ ⟨m, hm, rfl⟩
    show s' m ∈ ngM (M := M) t.f t.f'
    refine sat_of_unit_gram t.abelian₂ _ hmem (fun v hv j => ng_term_int ht hv (hmem j)) hu _ ?_ ?_
    · rw [← hΛ]; exact ⟨m, hMle hm, rfl⟩
    · exact ng_ME_le ht (ng_St_ME hs' (ng_span_base ht hm))
  constructor
  · intro hΛ
    refine le_antisymm (half s hsS hΛ) ?_
    have h2 := ng_img_mono s (half s⁻¹ (P.St.inv_mem hsS) (ng_img_inv hΛ))
    rwa [← ng_img_mul, mul_inv_cancel, ng_img_one] at h2
  · intro hM
    exact ng_img_of_M hP hX ht ht hsS hM

theorem ng_row_coef (Fr : FrameD H r) {y : V} {row : Fin (r + 1) → E} (h : y = ∑ i, row i • Fr.f i) (a : Fin r) :
    H.h y (Fr.es a) = row a.castSucc := by
  classical
  rw [h, h_sum_left, Fin.sum_univ_castSucc]
  have z : H.h (Fr.f (Fin.last r)) (Fr.es a) = 0 := h_z_es a
  rw [z, mul_zero, add_zero, Finset.sum_eq_single a]
  · rw [Fr.h_es, if_pos rfl, mul_one]
  · intro i _ hi; rw [Fr.h_es, if_neg hi, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ a) h'

theorem ng_span_frame (Fr : FrameD H r) {g : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet)
    (hint : ∀ (a : Fin r) (b : Fin (r + 1)), H.h (g (Fr.f b)) (Fr.es a) ∈ M.L.O) :
    Submodule.span M.L.O (Set.range fun b => g (Fr.f b)) = Submodule.span M.L.O (Set.range Fr.f) := by
  classical
  choose row h1 h2 h3 using N_row Fr hg
  have hO : ∀ b i, row b i ∈ M.L.O := by
    intro b i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
    · rw [← ng_row_coef Fr (h3 b) a]; exact hint a b
    · rcases eq_or_lt_of_le (Fin.le_last b) with hb | hb
      · rw [← hb, h2]; exact M.L.O.one_mem
      · rw [h1 b _ hb]; exact M.L.O.zero_mem
  have smulO : ∀ (S : Submodule M.L.O V) (c : E) (hc : c ∈ M.L.O) (x : V), x ∈ S → c • x ∈ S := by
    intro S c hc x hx
    have : c • x = (⟨c, hc⟩ : M.L.O) • x := rfl
    rw [this]; exact S.smul_mem _ hx
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    show g (Fr.f b) ∈ _
    rw [h3 b]
    exact Submodule.sum_mem _ (fun i _ => smulO _ _ (hO b i) _ (Submodule.subset_span ⟨i, rfl⟩))
  · rw [Submodule.span_le]
    have key : ∀ n : ℕ, ∀ b : Fin (r + 1), b.val < n →
        Fr.f b ∈ Submodule.span M.L.O (Set.range fun b => g (Fr.f b)) := by
      intro n
      induction n with
      | zero => intro b hb; exact absurd hb (Nat.not_lt_zero _)
      | succ n ih =>
        intro b hb
        have e : Fr.f b = g (Fr.f b) - ∑ i ∈ Finset.univ.erase b, row b i • Fr.f i := by
          rw [h3 b, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b), h2 b, one_smul]
          abel
        rw [e]
        refine Submodule.sub_mem _ (Submodule.subset_span ⟨b, rfl⟩) (Submodule.sum_mem _ (fun i hi => ?_))
        have hne : i ≠ b := (Finset.mem_erase.1 hi).1
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact smulO _ _ (hO b i) _ (ih i (lt_of_lt_of_le hlt (Nat.lt_succ_iff.1 hb)))
        · rw [h1 b i hgt, zero_smul]; exact Submodule.zero_mem _
    rintro _ ⟨b, rfl⟩
    exact key (b.val + 1) b (Nat.lt_succ_self _)

theorem ng_coef_of_M (hX : H.Xp P.A.f ⊓ H.Xp P.B.f = ⊥) {y : V} (hy : y ∈ ngM (M := M) P.A.f P.B.f) :
    (y ∈ H.Xp P.A.f → ∀ a, H.h y (P.A.es a) ∈ M.L.O) ∧ (y ∈ H.Xp P.B.f → ∀ a, H.h y (P.B.es a) ∈ M.L.O) := by
  unfold ngM at hy
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 hy
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hA : ∑ i, c (Sum.inl i) • P.A.f i ∈ H.Xp P.A.f :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ ((c (Sum.inl i) : M.L.O) : E) (Submodule.subset_span ⟨i, rfl⟩))
  have hB : ∑ i, c (Sum.inr i) • P.B.f i ∈ H.Xp P.B.f :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ ((c (Sum.inr i) : M.L.O) : E) (Submodule.subset_span ⟨i, rfl⟩))
  constructor
  · intro h a
    have h0 : ∑ i, c (Sum.inr i) • P.B.f i ∈ H.Xp P.A.f ⊓ H.Xp P.B.f := by
      refine ⟨?_, hB⟩
      have := Submodule.sub_mem _ h hA
      rwa [add_sub_cancel_left] at this
    rw [hX, Submodule.mem_bot] at h0
    rw [h0, add_zero]
    have e := ng_row_coef P.A (y := ∑ i, c (Sum.inl i) • P.A.f i) (row := fun i => ((c (Sum.inl i) : M.L.O) : E)) rfl a
    rw [e]
    exact (c (Sum.inl a.castSucc)).2
  · intro h a
    have h0 : ∑ i, c (Sum.inl i) • P.A.f i ∈ H.Xp P.A.f ⊓ H.Xp P.B.f := by
      refine ⟨hA, ?_⟩
      have := Submodule.sub_mem _ h hB
      rwa [add_sub_cancel_right] at this
    rw [hX, Submodule.mem_bot] at h0
    rw [h0, zero_add]
    have e := ng_row_coef P.B (y := ∑ i, c (Sum.inr i) • P.B.f i) (row := fun i => ((c (Sum.inr i) : M.L.O) : E)) rfl a
    rw [e]
    exact (c (Sum.inr a.castSucc)).2

theorem ng_N_Xp (Fr : FrameD H r) {g : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet) (b : Fin (r + 1)) : g (Fr.f b) ∈ H.Xp Fr.f := by
  obtain ⟨row, -, -, h⟩ := N_row Fr hg b
  rw [h]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem mem_normaliser_iff_stabiliser (hX : H.Xp P.A.f ⊓ H.Xp P.B.f = ⊥) {κ : V ≃ₗ[E] V} :
    κ ∈ P.K0 ↔ κ ∈ P.St ∧ img κ (ngM (M := M) P.A.f P.B.f) = ngM (M := M) P.A.f P.B.f := by
  constructor
  · intro hκ
    unfold FPair.K0 at hκ
    induction hκ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxS, hint⟩ := hx
      refine ⟨hxS, ?_⟩
      rw [ng_img_M]
      exact ng_M_eq (ng_span_frame P.A (mem_NSet_of_mem_N P.A hxS.1) (fun a b => (hint a b).1))
        (ng_span_frame P.B (mem_NSet_of_mem_N P.B hxS.2) (fun a b => (hint a b).2))
    | one => exact ⟨P.St.one_mem, ng_img_one _⟩
    | mul x y _ _ hx hy => exact ⟨P.St.mul_mem hx.1 hy.1, by rw [ng_img_mul, hy.2, hx.2]⟩
    | inv x _ hx => exact ⟨P.St.inv_mem hx.1, ng_img_inv hx.2⟩
  · rintro ⟨hS, hM⟩
    refine Subgroup.subset_closure ⟨hS, fun a b => ⟨?_, ?_⟩⟩
    · refine (ng_coef_of_M hX ?_).1 (ng_N_Xp P.A (mem_NSet_of_mem_N P.A hS.1) b) a
      rw [← hM]
      exact ⟨P.A.f b, Submodule.subset_span ⟨Sum.inl b, rfl⟩, rfl⟩
    · refine (ng_coef_of_M hX ?_).2 (ng_N_Xp P.B (mem_NSet_of_mem_N P.B hS.2) b) a
      rw [← hM]
      exact ⟨P.B.f b, Submodule.subset_span ⟨Sum.inr b, rfl⟩, rfl⟩

def NGBaseInt (P : FPair H r) : Prop := ∀ a b, H.h (P.B.f b) (P.A.f a) ∈ M.L.O

def NGUnimod (P : FPair H r) : Prop :=
  ∀ s ∈ P.St, volRel (P.K0.map (MulAut.conj s).toMonoidHom) P.K0 = 1

theorem NGMassOne_of (hP : P.PrimeTo) (hX : H.Xp P.A.f ⊓ H.Xp P.B.f = ⊥) (hC : NGOneClass P) (hB : NGBaseInt P)
    (hU : NGUnimod P) : NGMassOne P := by
  intro d t ht
  have hf := ng_term_f ht
  have it := fun a b => ng_term_int ht (hf b).2 (hf a).1
  have g := ht
  obtain ⟨_, _, ⟨n, hn, e, -⟩, ⟨n', hn', e', -⟩, _⟩ := g
  obtain ⟨s0, hs0, hA0, hB0⟩ := hC 1 P.A.N.one_mem 1 P.B.N.one_mem n hn n' hn' hB
    (fun a b => by have := it a b; rwa [e, e'] at this)
  have hM0 : img s0 (ngM (M := M) P.A.f P.B.f) = ngM (M := M) t.f t.f' := by
    rw [ng_img_M, e, e']
    exact ng_M_eq hA0 hB0
  have hEq : P.St ⊓ Aut t.abelian₂ = P.K0.map (MulAut.conj s0).toMonoidHom := by
    ext s
    constructor
    · rintro ⟨hsS, hsA⟩
      have h1 := (ng_Aut_iff hP hX ht hsS).1 hsA
      refine ⟨s0⁻¹ * s * s0, (mem_normaliser_iff_stabiliser hX).2 ⟨P.St.mul_mem (P.St.mul_mem (P.St.inv_mem hs0) hsS) hs0, ?_⟩, ?_⟩
      · rw [ng_img_mul, ng_img_mul, hM0, h1]
        exact ng_img_inv hM0
      · show s0 * (s0⁻¹ * s * s0) * s0⁻¹ = s
        group
    · rintro ⟨κ, hκ, rfl⟩
      obtain ⟨hκS, hκM⟩ := (mem_normaliser_iff_stabiliser hX).1 hκ
      have hS : s0 * κ * s0⁻¹ ∈ P.St := P.St.mul_mem (P.St.mul_mem hs0 hκS) (P.St.inv_mem hs0)
      refine ⟨hS, (ng_Aut_iff hP hX ht hS).2 ?_⟩
      rw [ng_img_mul, ng_img_mul, ng_img_inv hM0, hκM, hM0]
  unfold mu
  rw [hEq, hU s0 hs0]
  norm_num

def ngLm (e : ℕ → ℕ → E) (l : ℕ) : E := (Matrix.of fun a b : Fin l => e a b).det

def ngW (E : Type) [CommRing E] (s : ℕ) : Matrix (Fin s) (Fin s) E :=
  Matrix.of fun a b => if a.val + b.val + 1 = s then 1 else 0

omit [TopologicalSpace E] [MeasurableSpace E] in
theorem ng_W_sq (s : ℕ) : ngW E s * ngW E s = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have ha := a.2
  have hb := b.2
  rw [Finset.sum_eq_single (⟨s - 1 - a.val, by omega⟩ : Fin s)]
  · simp only [ngW, Matrix.of_apply]
    rw [if_pos (by omega), one_mul]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, if_pos (by omega)]
    · rw [if_neg hab, if_neg]
      intro h; apply hab; apply Fin.ext; omega
  · intro c _ hc'
    simp only [ngW, Matrix.of_apply]
    rw [if_neg, zero_mul]
    intro h; apply hc'; apply Fin.ext
    show c.val = s - 1 - a.val
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

omit [TopologicalSpace E] [MeasurableSpace E] in
theorem ng_lm_cons (t : Eˣ) (s : ℕ+) (bs : List (Eˣ × ℕ+)) (m : ℕ) :
    ngLm (ptEntryL ((t, s) :: bs)) ((s : ℕ) + m) = ((t : E) • ngW E (s : ℕ)).det * ngLm (ptEntryL bs) m := by
  unfold ngLm
  rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := (s : ℕ)) (n := m))]
  have e : (Matrix.of fun a b : Fin ((s : ℕ) + m) => ptEntryL ((t, s) :: bs) a b).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks ((t : E) • ngW E (s : ℕ)) 0 0 (Matrix.of fun a b : Fin m => ptEntryL bs a b) := by
    ext i j
    rcases i with a | a <;> rcases j with b | b
    · have ha := a.2
      have hb := b.2
      simp only [Matrix.submatrix_apply, Matrix.of_apply, finSumFinEquiv_apply_left, Fin.val_castAdd, ptEntryL,
        Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, ngW, smul_eq_mul]
      rw [if_pos ⟨ha, hb⟩]
      split_ifs <;> simp
    · have ha := a.2
      simp only [Matrix.submatrix_apply, Matrix.of_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd, ptEntryL, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      rw [if_neg (by omega), if_neg (by omega)]
    · have hb := b.2
      simp only [Matrix.submatrix_apply, Matrix.of_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd, ptEntryL, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [if_neg (by omega), if_neg (by omega)]
    · simp only [Matrix.submatrix_apply, Matrix.of_apply, finSumFinEquiv_apply_right,
        Fin.val_natAdd, ptEntryL, Matrix.fromBlocks_apply₂₂]
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  rw [e, Matrix.det_fromBlocks_zero₂₁]

theorem ng_isUnitO_of_mul {x y : E} (hxy : IsUnitO M (x * y)) (hx : IsUnitO M x) : IsUnitO M y := by
  obtain ⟨h1, z, hz, e⟩ := hxy
  obtain ⟨h2, x', hx', e'⟩ := hx
  refine ⟨?_, x * z, M.L.O.mul_mem h2 hz, by rw [← e]; ring⟩
  have : y = x' * (x * y) := by rw [← mul_assoc, mul_comm x', e', one_mul]
  rw [this]; exact M.L.O.mul_mem hx' h1

theorem ng_pt_int : ∀ (bs : List (Eˣ × ℕ+)),
    (∀ l, 1 ≤ l → l ≤ (bs.map (fun b => (b.2 : ℕ))).sum → IsUnit (ngLm (ptEntryL bs) l) →
      IsUnitO M (ngLm (ptEntryL bs) l)) → ∀ a b, ptEntryL bs a b ∈ M.L.O
  | [], _, a, b => by simp only [ptEntryL]; exact M.L.O.zero_mem
  | (t, s) :: bs, h, a, b => by
    have hW : (ngW E (s : ℕ)).det * (ngW E (s : ℕ)).det = 1 := by
      rw [← Matrix.det_mul, ng_W_sq, Matrix.det_one]
    have hWO : (ngW E (s : ℕ)).det ∈ M.L.O := ng_det_mem _ (fun a b => by
      simp only [ngW, Matrix.of_apply]
      split_ifs
      · exact M.L.O.one_mem
      · exact M.L.O.zero_mem)
    have hdet : ((t : E) • ngW E (s : ℕ)).det = (t : E) ^ (s : ℕ) * (ngW E (s : ℕ)).det := by
      rw [Matrix.det_smul, Fintype.card_fin]
    have hAu : IsUnit ((t : E) • ngW E (s : ℕ)).det := by
      rw [hdet]; exact (t.isUnit.pow _).mul (IsUnit.of_mul_eq_one _ hW)
    have h0 : ngLm (ptEntryL ((t, s) :: bs)) (s : ℕ) = ((t : E) • ngW E (s : ℕ)).det := by
      have := ng_lm_cons t s bs 0
      have e0 : ngLm (ptEntryL bs) 0 = 1 := by unfold ngLm; exact Matrix.det_isEmpty
      rw [e0, mul_one] at this
      exact this
    have hAO : IsUnitO M ((t : E) • ngW E (s : ℕ)).det := by
      rw [← h0]
      refine h _ s.pos (by simp) ?_
      rw [h0]; exact hAu
    have htO : (t : E) ∈ M.L.O := by
      have h1 : (t : E) ^ (s : ℕ) ∈ M.L.O := by
        have : (t : E) ^ (s : ℕ) = ((t : E) • ngW E (s : ℕ)).det * (ngW E (s : ℕ)).det := by
          rw [hdet, mul_assoc, hW, mul_one]
        rw [this]; exact M.L.O.mul_mem hAO.1 hWO
      exact (M.L.O_def _).2 (IsIntegral.of_pow s.pos ((M.L.O_def _).1 h1))
    have ih := ng_pt_int bs (fun l hl hle hu => by
      refine ng_isUnitO_of_mul ?_ hAO
      rw [← ng_lm_cons]
      refine h _ (by omega) (by simp only [List.map_cons, List.sum_cons]; omega) ?_
      rw [ng_lm_cons]; exact hAu.mul hu)
    simp only [ptEntryL]
    split_ifs
    · exact htO
    · exact M.L.O.zero_mem
    · exact ih _ _
    · exact M.L.O.zero_mem

theorem NGBaseInt_of (hP : P.PrimeTo) (hpt : P.IsPoint) : NGBaseInt P := by
  obtain ⟨w, hw⟩ := hpt
  have hsq : ∀ k : ℕ, ((-1 : E) ^ k) * ((-1 : E) ^ k) = 1 := fun k => by rw [← mul_pow]; simp
  have hZ : ∀ a b : Fin (r + 1), H.Zhat P.A.f P.B.f a b = (-1) ^ (r - b.val) * ptEntryL w.blocks a b := by
    intro a b
    have := hw a b
    unfold Pt.mat at this
    rw [← this, ← mul_assoc, hsq, one_mul]
  have hD : ∀ l, l ≤ r + 1 → P.Dm l = (∏ j : Fin l, (-1 : E) ^ (r - j.val)) * ngLm (ptEntryL w.blocks) l := by
    intro l hl
    unfold FPair.Dm HermSp.Dl ngLm
    rw [dif_pos hl, ← Matrix.det_mul_row]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    rw [hZ]
    rfl
  have hε : ∀ l, IsUnitO M (∏ j : Fin l, (-1 : E) ^ (r - j.val)) := by
    intro l
    refine ⟨M.L.O.prod_mem (fun j _ => (isUnitO_neg_one_pow (M := M) _).1), ∏ j : Fin l, (-1 : E) ^ (r - j.val),
      M.L.O.prod_mem (fun j _ => (isUnitO_neg_one_pow (M := M) _).1), ?_⟩
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun j _ => hsq _)
  have hint := ng_pt_int (M := M) w.blocks (fun l hl hle hu => by
    rw [w.size] at hle
    refine ng_isUnitO_of_mul ?_ (hε l)
    rw [← hD l hle]
    refine hP.2.2 l ?_
    unfold FPair.ends
    refine (@Finset.mem_filter _ _ (Classical.decPred _) _ _).2 ⟨Finset.mem_range.2 (by omega), hl, ?_⟩
    rw [hD l hle]
    obtain ⟨_, y, _, hy⟩ := hε l
    exact (IsUnit.of_mul_eq_one _ hy).mul hu)
  intro a b
  have : H.h (P.B.f b) (P.A.f a) = H.Zhat P.A.f P.B.f a b := rfl
  rw [this, hZ]
  exact M.L.O.mul_mem (isUnitO_neg_one_pow (M := M) _).1 (hint _ _)

def NGOrbit0 (P : FPair H r) : Prop :=
  ∀ n ∈ P.A.N, ∀ n' ∈ P.B.N, (∀ a b, H.h (n' (P.B.f b)) (n (P.A.f a)) ∈ M.L.O) →
    ∃ s ∈ P.St,
      Submodule.span M.L.O (Set.range fun b => s (P.A.f b)) = Submodule.span M.L.O (Set.range fun b => n (P.A.f b)) ∧
      Submodule.span M.L.O (Set.range fun b => s (P.B.f b)) = Submodule.span M.L.O (Set.range fun b => n' (P.B.f b))

theorem ng_img_span (s : V ≃ₗ[E] V) (f : Fin (r + 1) → V) :
    img s (Submodule.span M.L.O (Set.range f)) = Submodule.span M.L.O (Set.range fun b => s (f b)) := by
  unfold img
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem NGOneClass_of (h : NGOrbit0 P) : NGOneClass P := by
  intro n₁ hn₁ n₁' hn₁' n₂ hn₂ n₂' hn₂' i₁ i₂
  obtain ⟨s₁, hs₁, a₁, b₁⟩ := h n₁ hn₁ n₁' hn₁' i₁
  obtain ⟨s₂, hs₂, a₂, b₂⟩ := h n₂ hn₂ n₂' hn₂' i₂
  refine ⟨s₂ * s₁⁻¹, P.St.mul_mem hs₂ (P.St.inv_mem hs₁), ?_, ?_⟩
  · rw [← ng_img_span (s₂ * s₁⁻¹) (fun b => n₁ (P.A.f b)), ← a₁, ← ng_img_span s₁ P.A.f, ← ng_img_mul,
      inv_mul_cancel_right, ng_img_span, a₂]
  · rw [← ng_img_span (s₂ * s₁⁻¹) (fun b => n₁' (P.B.f b)), ← b₁, ← ng_img_span s₁ P.B.f, ← ng_img_mul,
      inv_mul_cancel_right, ng_img_span, b₂]

theorem NGEqStep'_of_orbit (hP : P.PrimeTo) (hR : P.RelG (theta M)) (hO : NGOrbit0 P) (hU : NGUnimod P) (R : Reps P) :
    NGEqStep' P R :=
  NGEqStep'_of hP hR.1 (NGOneClass_of hO)
    (NGMassOne_of hP hR.1 (NGOneClass_of hO) (NGBaseInt_of hP hR.2.2.2.2.2.1) hU) R

structure NGCore2 (k : ℕ) (R : Reps P) (d0 : Datum P) (c : ℕ) (S : Term V M r → Prop) where
  Ds : Finset R.RD
  off : ∀ d : R.RD, d ∉ Ds → R.RT d.1 = ∅
  summ : ∀ d : R.RD, Summable (fun t : R.RT d.1 => mu P t.1)
  Ty : Type
  fin : Fintype Ty
  typ : Term V M r → Ty
  be : Ty → ℝ
  I : Ty → ℝ
  card : (Fintype.card Ty : ℝ) ≤ P.Hp ^ (c * (r + 1) ^ 2)
  be1 : ∀ τ, 1 ≤ be τ
  I0 : ∀ τ, 0 ≤ I τ
  Ibe : ∀ τ, I τ ≤ be τ
  c2 : ∀ (τ : Ty) (d : Ds), massS R d.1.1 (fun t => S t ∧ typ t = τ) ≤ P.Hp ^ (c * (r + 1) ^ 2) * I τ ^ (k - 1)
  c1 : ∀ τ : Ty, ∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 (fun t => S t ∧ typ t = τ) ≤
    P.Hp ^ (c * (r + 1) ^ 2) * (be τ ^ (k - 1))⁻¹ * ∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1

structure NGCore1 (k : ℕ) (R : Reps P) (d0 : Datum P) (c : ℕ) (C₀ : ℝ) extends
    NGCore2 k R d0 c (BBne (H := H)) where
  isBe : Ty → Prop
  Ial : ∀ τ, ¬ isBe τ → I τ ≤ be τ / (qF F : ℝ)
  e : ∀ (τ : Ty) (d : Ds), isBe τ → ‖amp R d.1.1 (fun t => BBne (H := H) t ∧ typ t = τ)‖ ≤
    C₀ * (qF F : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * massS R d.1.1 (fun t => BBne (H := H) t ∧ typ t = τ)

def NGCore2.toSteps {k : ℕ} {R : Reps P} {d0 : Datum P} {c : ℕ} {S : Term V M r → Prop} (X : NGCore2 k R d0 c S)
    (hOK : M.OK) (hH : 1 ≤ P.Hp) : NGSteps2 k R d0 c S where
  Ds := X.Ds
  off := X.off
  summ := X.summ
  om1 := ng_norm_om hOK
  Ty := X.Ty
  fin := X.fin
  typ := X.typ
  be := X.be
  I := X.I
  H1 := hH
  card := X.card
  be1 := X.be1
  I0 := X.I0
  Ibe := X.Ibe
  c2 := X.c2
  c1 := X.c1

def NGCore1.toSteps {k : ℕ} {R : Reps P} {d0 : Datum P} {c : ℕ} {C₀ : ℝ} (X : NGCore1 k R d0 c C₀)
    (hOK : M.OK) (hG : P.Gv ≠ 0) (hH : 1 ≤ P.Hp) (hk : 4 * r + 7 ≤ k) : NGSteps1 k R d0 c C₀ where
  toNGSteps2 := X.toNGCore2.toSteps hOK hH
  hk := hk
  q2 := two_le_residue_card hOK
  qH := fun ⟨d, t, ht, hB⟩ => ng_q_le_Hp hOK hG ((R.hRT d.1).1 ht) hB
  isBe := X.isBe
  Ial := X.Ial
  e := X.e

end NGa

def NGStepsAll' (k r c : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) →
        (∀ (R : Reps P) (d0 : Datum P), Nonempty (NGCore1 k R d0 c C₀) ∧
            Nonempty (NGCore2 k R d0 c (fun t => ¬ BBne (H := H) t)) ∧ Nonempty (NGCore2 k R d0 c (fun _ => True))) ∧
          (P.PrimeTo → ∀ R : Reps P, NGEqStep' P R)

theorem NGStepsAll_of' {k r c : ℕ} {C₀ : ℝ} (hk : 4 * r + 7 ≤ k) (h : NGStepsAll' k r c C₀) : NGStepsAll k r c C₀ := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H hrk P hP
  by_cases hex : ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t
  · obtain ⟨hS, hE⟩ := h F E M hOK V H hrk P hP hex
    obtain ⟨d, t, ht⟩ := hex
    have hG : P.Gv ≠ 0 := hP.2.2.1
    have hH : 1 ≤ P.Hp := ng_Hp_ge_one hOK hG ht
    exact Or.inr ⟨hH, fun R d0 => ⟨⟨(hS R d0).1.some.toSteps hOK hG hH hk⟩, ⟨(hS R d0).2.1.some.toSteps hOK hH⟩,
      ⟨(hS R d0).2.2.some.toSteps hOK hH⟩⟩, hE⟩
  · refine Or.inl (fun R d => ?_)
    by_contra hne
    obtain ⟨t, ht⟩ := Set.nonempty_iff_ne_empty.2 hne
    exact hex ⟨d, t, (R.hRT d).1 ht⟩

theorem nongeneric_local_of_steps (k r c : ℕ) (C₀ C : ℝ) (hk : 4 * r + 7 ≤ k) (hC1 : (gainBoundConstant c C₀ : ℝ) ≤ C)
    (hC2 : (nongenericConstantNoGain c : ℝ) ≤ C) (h : NGStepsAll' k r c C₀) : NonGenericAndKTwoTheorems.NonGenericLocalBound k r C :=
  nongeneric_local_bound_of_estimates k r c C₀ C hC1 hC2 (NGStepsAll_of' hk h)

theorem nongeneric_family_of_steps {eps : ℝ} (Fm : FamP eps) (c : ℕ) (C₀ C : ℝ) (hC1 : (gainBoundConstant c C₀ : ℝ) ≤ C)
    (hC2 : (nongenericConstantNoGain c : ℝ) ≤ C)
    (h : ∀ x (i : Fm.Ix x), 4 * (Fm.D x i).R.rS + 7 ≤ (Fm.D x i).R.k → NGStepsAll' (Fm.D x i).R.k (Fm.D x i).R.rS c C₀) :
    NonGenericAndKTwoTheorems.FamilyNonGenericLocalBound Fm C :=
  nongeneric_family_bound_of_estimates Fm c C₀ C hC1 hC2 (fun x i hk => NGStepsAll_of' hk (h x i hk))

def NGLeft (k r c : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) →
        (P.PrimeTo → NGOrbit0 P ∧ NGUnimod P) ∧
        (¬ P.PrimeTo → ∀ (R : Reps P) (d0 : Datum P), Nonempty (NGCore1 k R d0 c C₀) ∧
            Nonempty (NGCore2 k R d0 c (fun t => ¬ BBne (H := H) t)) ∧ Nonempty (NGCore2 k R d0 c (fun _ => True)))

theorem nongeneric_local_of_remainder (k r c : ℕ) (C₀ C : ℝ) (hk : 4 * r + 7 ≤ k) (hC1 : (gainBoundConstant c C₀ : ℝ) ≤ C)
    (hC2 : (nongenericConstantNoGain c : ℝ) ≤ C) (h : NGLeft k r c C₀) : NonGenericAndKTwoTheorems.NonGenericLocalBound k r C := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H hrk P hP
  by_cases hex : ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t
  · obtain ⟨hgood, hbad⟩ := h F E M hOK V H hrk P hP hex
    obtain ⟨d, t, ht⟩ := hex
    have hG : P.Gv ≠ 0 := hP.2.2.1
    have hH : 1 ≤ P.Hp := ng_Hp_ge_one hOK hG ht
    by_cases hp : P.PrimeTo
    · exact NGAt_of_primeTo' hOK k C hp (fun R => NGEqStep'_of_orbit hp hP (hgood hp).1 (hgood hp).2 R)
    · exact NGAt_of_steps hOK k c C₀ C hH hC1 hC2 (fun R d0 => (hbad hp R d0).1.some.toSteps hOK hG hH hk)
        (fun R d0 => (hbad hp R d0).2.1.some.toSteps hOK hH) (fun R d0 => (hbad hp R d0).2.2.some.toSteps hOK hH)
        (fun h' => absurd h' hp)
  · refine NGAt_of_noTerms hOK k C (fun R d => ?_)
    by_contra hne
    obtain ⟨t, ht⟩ := Set.nonempty_iff_ne_empty.2 hne
    exact hex ⟨d, t, (R.hRT d).1 ht⟩

theorem nongeneric_family_of_remainder {eps : ℝ} (Fm : FamP eps) (c : ℕ) (C₀ C : ℝ) (hC1 : (gainBoundConstant c C₀ : ℝ) ≤ C)
    (hC2 : (nongenericConstantNoGain c : ℝ) ≤ C)
    (h : ∀ x (i : Fm.Ix x), 4 * (Fm.D x i).R.rS + 7 ≤ (Fm.D x i).R.k → NGLeft (Fm.D x i).R.k (Fm.D x i).R.rS c C₀) :
    NonGenericAndKTwoTheorems.FamilyNonGenericLocalBound Fm C := fun x i hk => nongeneric_local_of_remainder _ _ c C₀ C hk hC1 hC2 (h x i hk)

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section NGb

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

def NgLow {R : Type} [Zero R] [One R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ a b, a < b → A a b = 0) ∧ ∀ a, A a a = 1

def NgUp {R : Type} [Zero R] [One R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ a b, b < a → A a b = 0) ∧ ∀ a, A a a = 1

def NGMat (P : FPair H r) : Prop :=
  ∀ Lo Up : Matrix (Fin (r + 1)) (Fin (r + 1)) E, NgLow Lo → NgUp Up →
    (∀ a b, (Lo * H.Zhat P.A.f P.B.f * Up) a b ∈ M.L.O) →
    ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, NgLow A ∧ NgUp A' ∧ (∀ a b, A a b ∈ M.L.O) ∧ (∀ a b, A' a b ∈ M.L.O) ∧
      A * (Lo * H.Zhat P.A.f P.B.f * Up) * A' = H.Zhat P.A.f P.B.f

end NGb

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

section Mat

variable {E : Type} [CommRing E] {n : ℕ}

def NgmLow (A : Matrix (Fin n) (Fin n) E) : Prop := (∀ a, A a a = 1) ∧ ∀ a b, a < b → A a b = 0

def NgmUp (A : Matrix (Fin n) (Fin n) E) : Prop := (∀ a, A a a = 1) ∧ ∀ a b, b < a → A a b = 0

def NgmInt (O : Subring E) (A : Matrix (Fin n) (Fin n) E) : Prop := ∀ a b, A a b ∈ O

def ngmMono (σ : Fin n → Fin n) (t : Fin n → E) : Matrix (Fin n) (Fin n) E := fun a b => if b = σ a then t a else 0

theorem NgmLow.mul {A B : Matrix (Fin n) (Fin n) E} (hA : NgmLow A) (hB : NgmLow B) : NgmLow (A * B) := by
  constructor
  · intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.1, hB.1, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hB.2 k a h, mul_zero]
      · rw [hA.2 a k h, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a b hab
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases le_or_gt k a with h | h
    · rw [hB.2 k b (lt_of_le_of_lt h hab), mul_zero]
    · rw [hA.2 a k h, zero_mul]

theorem ngm_up_iff {A : Matrix (Fin n) (Fin n) E} : NgmUp A ↔ NgmLow A.transpose :=
  ⟨fun h => ⟨h.1, fun a b hab => h.2 b a hab⟩, fun h => ⟨h.1, fun a b hab => h.2 b a hab⟩⟩

theorem NgmUp.mul {A B : Matrix (Fin n) (Fin n) E} (hA : NgmUp A) (hB : NgmUp B) : NgmUp (A * B) := by
  rw [ngm_up_iff, Matrix.transpose_mul]
  exact (ngm_up_iff.1 hB).mul (ngm_up_iff.1 hA)

theorem NgmInt.mul {O : Subring E} {A B : Matrix (Fin n) (Fin n) E} (hA : NgmInt O A) (hB : NgmInt O B) :
    NgmInt O (A * B) := fun a b => by
  rw [Matrix.mul_apply]
  exact O.sum_mem (fun k _ => O.mul_mem (hA a k) (hB k b))

theorem ngm_low_one : NgmLow (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => Matrix.one_apply_eq a, fun _ _ h => Matrix.one_apply_ne (ne_of_lt h)⟩

theorem ngm_up_one : NgmUp (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => Matrix.one_apply_eq a, fun _ _ h => Matrix.one_apply_ne (ne_of_gt h)⟩

theorem ngm_int_one (O : Subring E) : NgmInt O (1 : Matrix (Fin n) (Fin n) E) := fun a b => by
  rw [Matrix.one_apply]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

def NgmLP (O : Subring E) (A B : Matrix (Fin n) (Fin n) E) : Prop :=
  NgmLow A ∧ NgmInt O A ∧ NgmLow B ∧ NgmInt O B ∧ A * B = 1 ∧ B * A = 1

def NgmUP (O : Subring E) (A B : Matrix (Fin n) (Fin n) E) : Prop :=
  NgmUp A ∧ NgmInt O A ∧ NgmUp B ∧ NgmInt O B ∧ A * B = 1 ∧ B * A = 1

theorem ngmLP_one (O : Subring E) : NgmLP O (1 : Matrix (Fin n) (Fin n) E) 1 :=
  ⟨ngm_low_one, ngm_int_one O, ngm_low_one, ngm_int_one O, Matrix.one_mul _, Matrix.one_mul _⟩

theorem ngmUP_one (O : Subring E) : NgmUP O (1 : Matrix (Fin n) (Fin n) E) 1 :=
  ⟨ngm_up_one, ngm_int_one O, ngm_up_one, ngm_int_one O, Matrix.one_mul _, Matrix.one_mul _⟩

theorem ngm_inv_mul {A₁ B₁ A₂ B₂ : Matrix (Fin n) (Fin n) E} (h₁ : A₁ * B₁ = 1) (h₂ : A₂ * B₂ = 1) :
    (A₂ * A₁) * (B₁ * B₂) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc A₁, h₁, Matrix.one_mul, h₂]

theorem NgmLP.mul {O : Subring E} {A₁ B₁ A₂ B₂ : Matrix (Fin n) (Fin n) E} (h₂ : NgmLP O A₂ B₂) (h₁ : NgmLP O A₁ B₁) :
    NgmLP O (A₂ * A₁) (B₁ * B₂) :=
  ⟨h₂.1.mul h₁.1, h₂.2.1.mul h₁.2.1, h₁.2.2.1.mul h₂.2.2.1, h₁.2.2.2.1.mul h₂.2.2.2.1,
    ngm_inv_mul h₁.2.2.2.2.1 h₂.2.2.2.2.1, ngm_inv_mul h₂.2.2.2.2.2 h₁.2.2.2.2.2⟩

theorem NgmUP.mul {O : Subring E} {A₁ B₁ A₂ B₂ : Matrix (Fin n) (Fin n) E} (h₂ : NgmUP O A₂ B₂) (h₁ : NgmUP O A₁ B₁) :
    NgmUP O (A₂ * A₁) (B₁ * B₂) :=
  ⟨h₂.1.mul h₁.1, h₂.2.1.mul h₁.2.1, h₁.2.2.1.mul h₂.2.2.1, h₁.2.2.2.1.mul h₂.2.2.2.1,
    ngm_inv_mul h₁.2.2.2.2.1 h₂.2.2.2.2.1, ngm_inv_mul h₂.2.2.2.2.2 h₁.2.2.2.2.2⟩

theorem ngm_entry (σ : Fin n → Fin n) (t : Fin n → E) (Lo Up : Matrix (Fin n) (Fin n) E) (a b : Fin n) :
    (Lo * ngmMono σ t * Up) a b = ∑ a', Lo a a' * t a' * Up (σ a') b := by
  simp only [Matrix.mul_apply, ngmMono, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  simp [mul_ite, ite_mul]

def ngmR (p : Fin n) (v : Fin n → E) : Matrix (Fin n) (Fin n) E := fun a a' => if a' = p then v a else 0

def ngmC (c : Fin n) (u : Fin n → E) : Matrix (Fin n) (Fin n) E := fun b' b => if b' = c then u b else 0

theorem ngm_R_mul (p : Fin n) (v : Fin n → E) (Z : Matrix (Fin n) (Fin n) E) (a b : Fin n) :
    (ngmR p v * Z) a b = v a * Z p b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · simp [ngmR]
  · intro k _ hk; simp [ngmR, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem ngm_mul_C (c : Fin n) (u : Fin n → E) (Z : Matrix (Fin n) (Fin n) E) (a b : Fin n) :
    (Z * ngmC c u) a b = Z a c * u b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · simp [ngmC]
  · intro k _ hk; simp [ngmC, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem ngm_R_inv (p : Fin n) (v : Fin n → E) (hv : v p = 0) : (1 - ngmR p v) * (1 - ngmR p (-v)) = 1 := by
  ext a b
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.sub_apply, ngm_R_mul, Matrix.sub_apply]
  by_cases hb : b = p
  · simp [ngmR, hb, hv, Matrix.one_apply]
  · simp [ngmR, hb, Matrix.one_apply, Ne.symm hb]

theorem ngm_C_inv (c : Fin n) (u : Fin n → E) (hu : u c = 0) : (1 - ngmC c u) * (1 - ngmC c (-u)) = 1 := by
  ext a b
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.sub_apply, ngm_mul_C, Matrix.sub_apply]
  by_cases ha : a = c
  · simp [ngmC, ha, hu, Matrix.one_apply]
  · simp [ngmC, ha, Matrix.one_apply]

theorem ngm_R_low (p : Fin n) (v : Fin n → E) (hv : ∀ a, a ≤ p → v a = 0) : NgmLow (1 - ngmR p v) := by
  constructor
  · intro a
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
    by_cases ha : a = p
    · simp [ngmR, ha, hv p le_rfl]
    · simp [ngmR, ha]
  · intro a b hab
    rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hab)]
    by_cases hb : b = p
    · simp [ngmR, hb, hv a (hb ▸ le_of_lt hab)]
    · simp [ngmR, hb]

theorem ngm_C_up (c : Fin n) (u : Fin n → E) (hu : ∀ b, b ≤ c → u b = 0) : NgmUp (1 - ngmC c u) := by
  constructor
  · intro a
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
    by_cases ha : a = c
    · simp [ngmC, ha, hu c le_rfl]
    · simp [ngmC, ha]
  · intro a b hab
    rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hab)]
    by_cases ha : a = c
    · simp [ngmC, ha, hu b (ha ▸ le_of_lt hab)]
    · simp [ngmC, ha]

theorem ngm_R_int (O : Subring E) (p : Fin n) (v : Fin n → E) (hv : ∀ a, v a ∈ O) : NgmInt O (1 - ngmR p v) := fun a b => by
  rw [Matrix.sub_apply]
  refine O.sub_mem (ngm_int_one O a b) ?_
  unfold ngmR
  split_ifs
  · exact hv a
  · exact O.zero_mem

theorem ngm_C_int (O : Subring E) (c : Fin n) (u : Fin n → E) (hu : ∀ a, u a ∈ O) : NgmInt O (1 - ngmC c u) := fun a b => by
  rw [Matrix.sub_apply]
  refine O.sub_mem (ngm_int_one O a b) ?_
  unfold ngmC
  split_ifs
  · exact hu b
  · exact O.zero_mem

theorem ngm_R_LP (O : Subring E) (p : Fin n) (v : Fin n → E) (hv : ∀ a, a ≤ p → v a = 0) (hO : ∀ a, v a ∈ O) :
    NgmLP O (1 - ngmR p v) (1 - ngmR p (-v)) := by
  refine ⟨ngm_R_low p v hv, ngm_R_int O p v hO, ngm_R_low p (-v) (fun a ha => by simp [hv a ha]),
    ngm_R_int O p (-v) (fun a => O.neg_mem (hO a)), ngm_R_inv p v (hv p le_rfl), ?_⟩
  have h := ngm_R_inv p (-v) (by simp [hv p le_rfl])
  rwa [neg_neg] at h

theorem ngm_C_UP (O : Subring E) (c : Fin n) (u : Fin n → E) (hu : ∀ a, a ≤ c → u a = 0) (hO : ∀ a, u a ∈ O) :
    NgmUP O (1 - ngmC c u) (1 - ngmC c (-u)) := by
  refine ⟨ngm_C_up c u hu, ngm_C_int O c u hO, ngm_C_up c (-u) (fun a ha => by simp [hu a ha]),
    ngm_C_int O c (-u) (fun a => O.neg_mem (hO a)), ngm_C_inv c u (hu c le_rfl), ?_⟩
  have h := ngm_C_inv c (-u) (by simp [hu c le_rfl])
  rwa [neg_neg] at h

def NgmInv (σ : Fin n → Fin n) (i : ℕ) (Lo Up : Matrix (Fin n) (Fin n) E) : Prop :=
  NgmLow Lo ∧ NgmUp Up ∧ (∀ a a' : Fin n, a'.val < i → a ≠ a' → Lo a a' = 0) ∧
    (∀ a' b : Fin n, a'.val < i → b ≠ σ a' → Up (σ a') b = 0) ∧ (∀ a' b' : Fin n, a'.val < i → b' ≠ σ a' → Up b' (σ a') = 0)

theorem ngm_row {σ : Fin n → Fin n} (t : Fin n → E) {i : ℕ} {Lo Up : Matrix (Fin n) (Fin n) E} (h : NgmInv σ i Lo Up)
    (a : Fin n) (ha : a.val ≤ i) (b : Fin n) : (Lo * ngmMono σ t * Up) a b = t a * Up (σ a) b := by
  rw [ngm_entry, Finset.sum_eq_single a]
  · rw [h.1.1, one_mul]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [h.2.2.1 a k (lt_of_lt_of_le hlt ha) (Ne.symm hk), zero_mul, zero_mul]
    · rw [h.1.2 a k hgt, zero_mul, zero_mul]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem ngm_step (O : Subring E) {σ : Fin n → Fin n} (hσ : Function.Injective σ) {t ti : Fin n → E}
    (hti : ∀ a, ti a ∈ O) (h1 : ∀ a, ti a * t a = 1) {i : ℕ} (hi : i < n) {Lo Up : Matrix (Fin n) (Fin n) E}
    (h : NgmInv σ i Lo Up) (hZ : NgmInt O (Lo * ngmMono σ t * Up)) :
    ∃ A B A' B' Lo' Up', NgmLP O A B ∧ NgmUP O A' B' ∧ NgmInv σ (i + 1) Lo' Up' ∧
      A * (Lo * ngmMono σ t * Up) * A' = Lo' * ngmMono σ t * Up' := by
  classical
  obtain ⟨Z, hZe⟩ : ∃ Z, Z = Lo * ngmMono σ t * Up := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Fin n, p = ⟨i, hi⟩ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin n, c = σ p := ⟨_, rfl⟩
  have hpv : p.val = i := by rw [hp]
  rw [← hZe] at hZ ⊢
  have hrow : ∀ a : Fin n, a.val ≤ i → ∀ b, Z a b = t a * Up (σ a) b := fun a ha b => by
    rw [hZe]; exact ngm_row t h a ha b
  have hent : ∀ a b, Z a b = ∑ a', Lo a a' * t a' * Up (σ a') b := fun a b => by rw [hZe]; exact ngm_entry σ t Lo Up a b
  have hZp : ∀ b, Z p b = t p * Up c b := fun b => by rw [hrow p (le_of_eq hpv) b, hc]
  have hUcc : Up c c = 1 := h.2.1.1 c
  have hUc : ∀ b, Up c b = ti p * Z p b := fun b => by rw [hZp, ← mul_assoc, h1, one_mul]
  have hne : ∀ a' : Fin n, a' ≠ p → σ a' ≠ c := fun a' ha' he => ha' (hσ (he.trans hc))
  have hlt : ∀ a' : Fin n, a'.val < i + 1 → a' ≠ p → a'.val < i := fun a' h1' h2' => by
    have : a'.val ≠ i := fun he => h2' (Fin.ext (he.trans hpv.symm))
    omega
  obtain ⟨v, hv⟩ : ∃ v : Fin n → E, v = fun a => if p < a then ti p * Z a c else 0 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin n → E, u = fun b => if b = c then 0 else Up c b := ⟨_, rfl⟩
  obtain ⟨Lo', hLo'⟩ : ∃ Lo' : Matrix (Fin n) (Fin n) E,
      Lo' = fun a a' => if a' = p then (if a = p then 1 else 0) else Lo a a' := ⟨_, rfl⟩
  obtain ⟨Up', hUp'⟩ : ∃ Up' : Matrix (Fin n) (Fin n) E,
      Up' = fun b' b => if b' = c then (if b = c then 1 else 0) else if b = c then 0 else Up b' b - Up b' c * Up c b :=
    ⟨_, rfl⟩
  have eLo : ∀ a a', Lo' a a' = if a' = p then (if a = p then 1 else 0) else Lo a a' := fun a a' => by rw [hLo']
  have eUp : ∀ b' b, Up' b' b = if b' = c then (if b = c then 1 else 0) else if b = c then 0 else
      Up b' b - Up b' c * Up c b := fun b' b => by rw [hUp']
  have ev : ∀ a, v a = if p < a then ti p * Z a c else 0 := fun a => by rw [hv]
  have eu : ∀ b, u b = if b = c then 0 else Up c b := fun b => by rw [hu]
  refine ⟨1 - ngmR p v, 1 - ngmR p (-v), 1 - ngmC c u, 1 - ngmC c (-u), Lo', Up', ngm_R_LP O p v ?_ ?_,
    ngm_C_UP O c u ?_ ?_, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro a ha
    rw [ev, if_neg (not_lt.2 ha)]
  · intro a
    rw [ev]
    split_ifs
    · exact O.mul_mem (hti p) (hZ a c)
    · exact O.zero_mem
  · intro b hb
    rw [eu]
    split_ifs with hbc
    · rfl
    · exact h.2.1.2 c b (lt_of_le_of_ne hb hbc)
  · intro b
    rw [eu]
    split_ifs
    · exact O.zero_mem
    · rw [hUc]; exact O.mul_mem (hti p) (hZ p b)
  · intro a
    rw [eLo]
    split_ifs
    · rfl
    · exact h.1.1 a
  · intro a b hab
    rw [eLo]
    split_ifs with hb ha
    · exact absurd hab (by rw [ha, hb]; exact lt_irrefl _)
    · rfl
    · exact h.1.2 a b hab
  · intro b
    rw [eUp]
    split_ifs with hb
    · rfl
    · rw [h.2.1.1 b]
      rcases lt_or_gt_of_ne hb with hlt' | hgt'
      · rw [h.2.1.2 c b hlt', mul_zero, sub_zero]
      · rw [h.2.1.2 b c hgt', zero_mul, sub_zero]
  · intro a b hab
    rw [eUp]
    split_ifs with ha hb hb
    · exact absurd hab (by rw [ha, hb]; exact lt_irrefl _)
    · rfl
    · rfl
    · rw [h.2.1.2 a b hab, zero_sub, neg_eq_zero]
      rcases lt_or_gt_of_ne ha with hlt' | hgt'
      · rw [h.2.1.2 c b (lt_trans hab hlt'), mul_zero]
      · rw [h.2.1.2 a c hgt', zero_mul]
  · intro a a' ha' hne'
    rw [eLo]
    split_ifs with h2 h3
    · exact absurd (h3.trans h2.symm) hne'
    · rfl
    · exact h.2.2.1 a a' (hlt a' ha' h2) hne'
  · intro a' b ha' hb
    rw [eUp]
    by_cases hap : a' = p
    · rw [hap, ← hc, if_pos rfl, if_neg (by rw [hc, ← hap]; exact hb)]
    · rw [if_neg (hne a' hap)]
      split_ifs
      · rfl
      · rw [h.2.2.2.1 a' b (hlt a' ha' hap) hb, h.2.2.2.1 a' c (hlt a' ha' hap) (Ne.symm (hne a' hap)), zero_mul, sub_zero]
  · intro a' b' ha' hb'
    rw [eUp]
    by_cases hap : a' = p
    · rw [hap, ← hc, if_neg (by rw [hc, ← hap]; exact hb'), if_pos rfl]
    · by_cases h2 : b' = c
      · rw [if_pos h2, if_neg (hne a' hap)]
      · rw [if_neg h2, if_neg (hne a' hap), h.2.2.2.2 a' b' (hlt a' ha' hap) hb',
          h.2.2.2.2 a' c (hlt a' ha' hap) (Ne.symm (hne a' hap)), mul_zero, sub_zero]
  · ext a b
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, ngm_mul_C, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply,
      Matrix.sub_apply, ngm_R_mul, ngm_R_mul, ngm_entry]
    by_cases hb : b = c
    · rw [hb, eu, if_pos rfl, mul_zero, sub_zero, Finset.sum_eq_single p]
      · rw [eLo, if_pos rfl, ← hc, eUp, if_pos rfl, if_pos rfl, mul_one, hZp, hUcc, mul_one, ev]
        rcases lt_trichotomy a p with hlt' | heq | hgt'
        · rw [if_neg (not_lt.2 (le_of_lt hlt')), if_neg (ne_of_lt hlt'), zero_mul, sub_zero,
            hrow a (by have : a.val < p.val := hlt'; omega) c,
            h.2.2.2.1 a c (by have : a.val < p.val := hlt'; omega) (Ne.symm (hne a (ne_of_lt hlt'))), mul_zero]
        · rw [heq, if_neg (lt_irrefl _), if_pos rfl, zero_mul, sub_zero, one_mul, hZp, hUcc, mul_one]
        · rw [if_pos hgt', if_neg (ne_of_gt hgt'), zero_mul]
          have e : ti p * Z a c * t p = (ti p * t p) * Z a c := by ring
          rw [e, h1, one_mul, sub_self]
      · intro a' _ ha'
        rw [eUp, if_neg (hne a' ha'), if_pos rfl, mul_zero]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · have e1 : ∀ a', Lo' a a' * t a' * Up' (σ a') b = Lo a a' * t a' * Up (σ a') b - Lo a a' * t a' * Up (σ a') c * Up c b := by
        intro a'
        by_cases hap : a' = p
        · rw [hap, ← hc, eUp, if_pos rfl, if_neg hb, mul_zero, hUcc, mul_one, sub_self]
        · rw [eLo, if_neg hap, eUp, if_neg (hne a' hap), if_neg hb]
          ring
      rw [Finset.sum_congr rfl (fun a' _ => e1 a'), Finset.sum_sub_distrib, ← Finset.sum_mul, ← hent, ← hent, eu, if_neg hb,
        hZp, hZp, hUcc]
      ring

theorem ngm_ind (O : Subring E) {σ : Fin n → Fin n} (hσ : Function.Injective σ) {t ti : Fin n → E}
    (hti : ∀ a, ti a ∈ O) (h1 : ∀ a, ti a * t a = 1) :
    ∀ (m i : ℕ), i + m = n → ∀ Lo Up : Matrix (Fin n) (Fin n) E, NgmInv σ i Lo Up → NgmInt O (Lo * ngmMono σ t * Up) →
      ∃ A B A' B', NgmLP O A B ∧ NgmUP O A' B' ∧ A * (Lo * ngmMono σ t * Up) * A' = ngmMono σ t := by
  intro m
  induction m with
  | zero =>
    intro i hi Lo Up h _
    have hin : i = n := by omega
    have hLo : Lo = 1 := by
      ext a b
      by_cases hab : a = b
      · rw [hab, h.1.1, Matrix.one_apply_eq]
      · rw [h.2.2.1 a b (by rw [hin]; exact b.2) hab, Matrix.one_apply_ne hab]
    have hsur : Function.Surjective σ := Finite.injective_iff_surjective.1 hσ
    have hUp : Up = 1 := by
      ext a b
      by_cases hab : a = b
      · rw [hab, h.2.1.1, Matrix.one_apply_eq]
      · obtain ⟨a', rfl⟩ := hsur a
        rw [h.2.2.2.1 a' b (by rw [hin]; exact a'.2) (Ne.symm hab), Matrix.one_apply_ne hab]
    exact ⟨1, 1, 1, 1, ngmLP_one O, ngmUP_one O, by rw [hLo, hUp]; simp⟩
  | succ m ih =>
    intro i hi Lo Up h hZ
    obtain ⟨A₁, B₁, A₁', B₁', Lo', Up', hL, hU, hInv, he⟩ := ngm_step O hσ hti h1 (by omega : i < n) h hZ
    have hZ' : NgmInt O (Lo' * ngmMono σ t * Up') := by
      rw [← he]; exact (hL.2.1.mul hZ).mul hU.2.1
    obtain ⟨A₂, B₂, A₂', B₂', hL2, hU2, he2⟩ := ih (i + 1) (by omega) Lo' Up' hInv hZ'
    refine ⟨A₂ * A₁, B₁ * B₂, A₁' * A₂', B₂' * B₁', hL2.mul hL, hU.mul hU2, ?_⟩
    have e : A₂ * A₁ * (Lo * ngmMono σ t * Up) * (A₁' * A₂') = A₂ * (A₁ * (Lo * ngmMono σ t * Up) * A₁') * A₂' := by
      simp only [Matrix.mul_assoc]
    rw [e, he, he2]

theorem ngm_main (O : Subring E) {σ : Fin n → Fin n} (hσ : Function.Injective σ) {t ti : Fin n → E}
    (hti : ∀ a, ti a ∈ O) (h1 : ∀ a, ti a * t a = 1) (Lo Up : Matrix (Fin n) (Fin n) E) (hLo : NgmLow Lo) (hUp : NgmUp Up)
    (hZ : NgmInt O (Lo * ngmMono σ t * Up)) :
    ∃ A B A' B', NgmLP O A B ∧ NgmUP O A' B' ∧ A * (Lo * ngmMono σ t * Up) * A' = ngmMono σ t :=
  ngm_ind O hσ hti h1 n 0 (by omega) Lo Up
    ⟨hLo, hUp, fun _ a' h => absurd h (Nat.not_lt_zero _), fun a' _ h => absurd h (Nat.not_lt_zero _),
      fun a' _ h => absurd h (Nat.not_lt_zero _)⟩ hZ

end Mat

section Pt

open Formalism.MainNotions.S.Loc

variable {E : Type} [CommRing E]

def ngmSig : List (Eˣ × ℕ+) → ℕ → ℕ
  | [], i => i
  | (_, s) :: bs, i => if i < (s : ℕ) then (s : ℕ) - 1 - i else (s : ℕ) + ngmSig bs (i - s)

def ngmT : List (Eˣ × ℕ+) → ℕ → Eˣ
  | [], _ => 1
  | (t, s) :: bs, i => if i < (s : ℕ) then t else ngmT bs (i - s)

theorem ngm_sig_lt : ∀ (bs : List (Eˣ × ℕ+)) (i : ℕ), i < (bs.map (fun b => (b.2 : ℕ))).sum →
    ngmSig bs i < (bs.map (fun b => (b.2 : ℕ))).sum
  | [], i, h => h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h ⊢
    simp only [ngmSig]
    split_ifs with his
    · omega
    · have := ngm_sig_lt bs (i - s) (by omega)
      omega

theorem ngm_sig_inj : ∀ (bs : List (Eˣ × ℕ+)) (i i' : ℕ), i < (bs.map (fun b => (b.2 : ℕ))).sum →
    i' < (bs.map (fun b => (b.2 : ℕ))).sum → ngmSig bs i = ngmSig bs i' → i = i'
  | [], i, i', _, _, h => h
  | (t, s) :: bs, i, i', h, h', he => by
    simp only [List.map_cons, List.sum_cons] at h h'
    simp only [ngmSig] at he
    split_ifs at he with h1 h2 h2
    · omega
    · omega
    · omega
    · have := ngm_sig_inj bs (i - s) (i' - s) (by omega) (by omega) (by omega)
      omega

theorem ngm_entryL : ∀ (bs : List (Eˣ × ℕ+)) (i j : ℕ), i < (bs.map (fun b => (b.2 : ℕ))).sum →
    ptEntryL bs i j = if j = ngmSig bs i then ((ngmT bs i : Eˣ) : E) else 0
  | [], i, j, h => by simp at h
  | (t, s) :: bs, i, j, h => by
    simp only [List.map_cons, List.sum_cons] at h
    simp only [ptEntryL]
    by_cases his : i < (s : ℕ)
    · have e1 : ngmSig ((t, s) :: bs) i = (s : ℕ) - 1 - i := by simp only [ngmSig, if_pos his]
      have e2 : ngmT ((t, s) :: bs) i = t := by simp only [ngmT, if_pos his]
      rw [e1, e2]
      by_cases hjs : j < (s : ℕ)
      · rw [if_pos ⟨his, hjs⟩]
        by_cases hij : i + j + 1 = (s : ℕ)
        · rw [if_pos hij, if_pos (by omega)]
        · rw [if_neg hij, if_neg (by omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · have e1 : ngmSig ((t, s) :: bs) i = (s : ℕ) + ngmSig bs (i - s) := by simp only [ngmSig, if_neg his]
      have e2 : ngmT ((t, s) :: bs) i = ngmT bs (i - s) := by simp only [ngmT, if_neg his]
      rw [e1, e2, if_neg (by omega)]
      by_cases hjs : (s : ℕ) ≤ j
      · rw [if_pos ⟨by omega, hjs⟩, ngm_entryL bs (i - s) (j - s) (by omega)]
        by_cases hij : j - (s : ℕ) = ngmSig bs (i - s)
        · rw [if_pos hij, if_pos (by omega)]
        · rw [if_neg hij, if_neg (by omega)]
      · rw [if_neg (by omega), if_neg (by omega)]

end Pt

section NGc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

theorem ngm_pt_inv : ∀ (bs : List (Eˣ × ℕ+)),
    (∀ l, 1 ≤ l → l ≤ (bs.map (fun b => (b.2 : ℕ))).sum → IsUnit (ngLm (ptEntryL bs) l) →
      IsUnitO M (ngLm (ptEntryL bs) l)) → ∀ i, (((ngmT bs i)⁻¹ : Eˣ) : E) ∈ M.L.O
  | [], _, i => by simp only [ngmT, inv_one, Units.val_one]; exact M.L.O.one_mem
  | (t, s) :: bs, h, i => by
    have hW : (ngW E (s : ℕ)).det * (ngW E (s : ℕ)).det = 1 := by
      rw [← Matrix.det_mul, ng_W_sq, Matrix.det_one]
    have hWO : (ngW E (s : ℕ)).det ∈ M.L.O := ng_det_mem _ (fun a b => by
      simp only [ngW, Matrix.of_apply]
      split_ifs
      · exact M.L.O.one_mem
      · exact M.L.O.zero_mem)
    have hdet : ((t : E) • ngW E (s : ℕ)).det = (t : E) ^ (s : ℕ) * (ngW E (s : ℕ)).det := by
      rw [Matrix.det_smul, Fintype.card_fin]
    have hAu : IsUnit ((t : E) • ngW E (s : ℕ)).det := by
      rw [hdet]; exact (t.isUnit.pow _).mul (IsUnit.of_mul_eq_one _ hW)
    have h0 : ngLm (ptEntryL ((t, s) :: bs)) (s : ℕ) = ((t : E) • ngW E (s : ℕ)).det := by
      have := ng_lm_cons t s bs 0
      have e0 : ngLm (ptEntryL bs) 0 = 1 := by unfold ngLm; exact Matrix.det_isEmpty
      rw [e0, mul_one] at this
      exact this
    have hAO : IsUnitO M ((t : E) • ngW E (s : ℕ)).det := by
      rw [← h0]
      refine h _ s.pos (by simp) ?_
      rw [h0]; exact hAu
    have htI : ((t⁻¹ : Eˣ) : E) ∈ M.L.O := by
      obtain ⟨_, y, hy, hyy⟩ := hAO
      have h1 : ((t⁻¹ : Eˣ) : E) ^ (s : ℕ) ∈ M.L.O := by
        have e : (t : E) ^ (s : ℕ) * ((ngW E (s : ℕ)).det * y) = 1 := by rw [← mul_assoc, ← hdet]; exact hyy
        have e2 : ((t⁻¹ : Eˣ) : E) ^ (s : ℕ) = (ngW E (s : ℕ)).det * y := by
          calc ((t⁻¹ : Eˣ) : E) ^ (s : ℕ) = ((t⁻¹ : Eˣ) : E) ^ (s : ℕ) * ((t : E) ^ (s : ℕ) * ((ngW E (s : ℕ)).det * y)) := by
                rw [e, mul_one]
            _ = (((t⁻¹ : Eˣ) : E) * (t : E)) ^ (s : ℕ) * ((ngW E (s : ℕ)).det * y) := by rw [mul_pow]; ring
            _ = (ngW E (s : ℕ)).det * y := by rw [Units.inv_mul, one_pow, one_mul]
        rw [e2]; exact M.L.O.mul_mem hWO hy
      exact (M.L.O_def _).2 (IsIntegral.of_pow s.pos ((M.L.O_def _).1 h1))
    have ih := ngm_pt_inv bs (fun l hl hle hu => by
      refine ng_isUnitO_of_mul ?_ hAO
      rw [← ng_lm_cons]
      refine h _ (by omega) (by simp only [List.map_cons, List.sum_cons]; omega) ?_
      rw [ng_lm_cons]; exact hAu.mul hu)
    simp only [ngmT]
    split_ifs
    · exact htI
    · exact ih _

theorem NGMat_of (hP : P.PrimeTo) (hR : P.RelG (theta M)) : NGMat P := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.2.1
  have hsq : ∀ k : ℕ, ((-1 : E) ^ k) * ((-1 : E) ^ k) = 1 := fun k => by rw [← mul_pow]; simp
  have hZ : ∀ a b : Fin (r + 1), H.Zhat P.A.f P.B.f a b = (-1) ^ (r - b.val) * ptEntryL w.blocks a b := by
    intro a b
    have := hw a b
    unfold Pt.mat at this
    rw [← this, ← mul_assoc, hsq, one_mul]
  have hD : ∀ l, l ≤ r + 1 → P.Dm l = (∏ j : Fin l, (-1 : E) ^ (r - j.val)) * ngLm (ptEntryL w.blocks) l := by
    intro l hl
    unfold FPair.Dm HermSp.Dl ngLm
    rw [dif_pos hl, ← Matrix.det_mul_row]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    rw [hZ]
    rfl
  have hε : ∀ l, IsUnitO M (∏ j : Fin l, (-1 : E) ^ (r - j.val)) := by
    intro l
    refine ⟨M.L.O.prod_mem (fun j _ => (isUnitO_neg_one_pow (M := M) _).1), ∏ j : Fin l, (-1 : E) ^ (r - j.val),
      M.L.O.prod_mem (fun j _ => (isUnitO_neg_one_pow (M := M) _).1), ?_⟩
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun j _ => hsq _)
  have hinv := ngm_pt_inv (M := M) w.blocks (fun l hl hle hu => by
    rw [w.size] at hle
    refine ng_isUnitO_of_mul ?_ (hε l)
    rw [← hD l hle]
    refine hP.2.2 l ?_
    unfold FPair.ends
    refine (@Finset.mem_filter _ _ (Classical.decPred _) _ _).2 ⟨Finset.mem_range.2 (by omega), hl, ?_⟩
    rw [hD l hle]
    obtain ⟨_, y, _, hy⟩ := hε l
    exact (IsUnit.of_mul_eq_one _ hy).mul hu)
  have hlt : ∀ a : Fin (r + 1), a.val < (w.blocks.map (fun b => (b.2 : ℕ))).sum := fun a => by rw [w.size]; exact a.2
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin (r + 1) → Fin (r + 1), ∀ a, (σ a).val = ngmSig w.blocks a.val :=
    ⟨fun a => ⟨ngmSig w.blocks a.val, by have := ngm_sig_lt w.blocks a.val (hlt a); rwa [w.size] at this⟩, fun _ => rfl⟩
  have hσi : Function.Injective σ := fun a a' he =>
    Fin.ext (ngm_sig_inj w.blocks a.val a'.val (hlt a) (hlt a') (by rw [← hσ, ← hσ, he]))
  have hmono : H.Zhat P.A.f P.B.f =
      ngmMono σ (fun a => (-1) ^ (r - (σ a).val) * ((ngmT w.blocks a.val : Eˣ) : E)) := by
    ext a b
    rw [hZ, ngm_entryL w.blocks a.val b.val (hlt a)]
    unfold ngmMono
    by_cases hb : b = σ a
    · rw [if_pos hb, if_pos (by rw [hb, hσ]), hb]
    · rw [if_neg hb, if_neg (fun he => hb (Fin.ext (he.trans (hσ a).symm))), mul_zero]
  intro Lo Up hLo hUp hint
  rw [hmono] at hint ⊢
  obtain ⟨A, B, A', B', hL, hU, he⟩ := ngm_main M.L.O hσi
    (ti := fun a => (-1) ^ (r - (σ a).val) * (((ngmT w.blocks a.val)⁻¹ : Eˣ) : E))
    (fun a => M.L.O.mul_mem (isUnitO_neg_one_pow (M := M) _).1 (hinv _))
    (fun a => by
      have e : (-1 : E) ^ (r - (σ a).val) * (((ngmT w.blocks a.val)⁻¹ : Eˣ) : E) *
          ((-1) ^ (r - (σ a).val) * ((ngmT w.blocks a.val : Eˣ) : E)) =
          ((-1 : E) ^ (r - (σ a).val) * (-1) ^ (r - (σ a).val)) *
            ((((ngmT w.blocks a.val)⁻¹ : Eˣ) : E) * ((ngmT w.blocks a.val : Eˣ) : E)) := by ring
      rw [e, hsq, Units.inv_mul, one_mul])
    Lo Up ⟨hLo.2, hLo.1⟩ ⟨hUp.2, hUp.1⟩ hint
  exact ⟨A, A', ⟨hL.1.2, hL.1.1⟩, ⟨hU.1.2, hU.1.1⟩, hL.2.1, hU.2.1, he⟩

end NGc

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section NGc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

theorem ngs_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

theorem ngs_perp_span {ι : Type} (m : ι → V) {x y : V} (hx : ∀ j, H.h x (m j) = 0)
    (hy : y ∈ Submodule.span E (Set.range m)) : H.h x y = 0 := by
  have h0 : H.h y x = 0 := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [H.h_herm x (m j), hx, map_zero]
    | zero => exact H.h_zero_left _
    | add a b _ _ ha hb => rw [H.h_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [H.h_smul_left, ha, mul_zero]
  rw [H.h_herm y x, h0, map_zero]

section Glue

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def ngsC (H : HermSp M V) (m : ι → V) (v : V) : ι → E := (H.gram m)⁻¹.mulVec (fun j => H.h v (m j))

theorem ngsC_add (m : ι → V) (v w : V) : ngsC H m (v + w) = ngsC H m v + ngsC H m w := by
  unfold ngsC
  rw [← Matrix.mulVec_add]
  congr 1
  funext j
  exact H.h_add_left _ _ _

theorem ngsC_smul (m : ι → V) (c : E) (v : V) : ngsC H m (c • v) = c • ngsC H m v := by
  unfold ngsC
  rw [← Matrix.mulVec_smul]
  congr 1
  funext j
  exact H.h_smul_left _ _ _

def ngsT (H : HermSp M V) (m m' : ι → V) : V →ₗ[E] V where
  toFun v := v - ∑ i, ngsC H m v i • m i + ∑ i, ngsC H m v i • m' i
  map_add' v w := by
    simp only [ngsC_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c v := by
    simp only [ngsC_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, ← Finset.smul_sum, smul_add, smul_sub]

theorem ngsT_apply (m m' : ι → V) (v : V) :
    ngsT H m m' v = v - ∑ i, ngsC H m v i • m i + ∑ i, ngsC H m v i • m' i := rfl

theorem ngs_pi (m : ι → V) (hu : IsUnit (H.gram m).det) (v : V) (j : ι) :
    H.h (∑ i, ngsC H m v i • m i) (m j) = H.h v (m j) := by
  rw [← ng_mulVec_gram]
  unfold ngsC
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]

theorem ngs_pi' (m m' : ι → V) (hu : IsUnit (H.gram m).det) (hg : H.gram m' = H.gram m) (v : V) (j : ι) :
    H.h (∑ i, ngsC H m v i • m' i) (m' j) = H.h v (m j) := by
  rw [← ng_mulVec_gram, hg, ng_mulVec_gram, ngs_pi m hu]

theorem ngs_perp (m : ι → V) (hu : IsUnit (H.gram m).det) (v : V) (j : ι) :
    H.h (v - ∑ i, ngsC H m v i • m i) (m j) = 0 := by
  rw [h_sub_left, ngs_pi m hu, sub_self]

theorem ngs_dec (m : ι → V) (hu : IsUnit (H.gram m).det) (v : V) :
    ∃ p ∈ Submodule.span E (Set.range m), ∀ j, H.h (v - p) (m j) = 0 :=
  ⟨∑ i, ngsC H m v i • m i,
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)), ngs_perp m hu v⟩

theorem ngs_T_pair (m m' : ι → V) (hu : IsUnit (H.gram m).det) (hg : H.gram m' = H.gram m)
    (h1 : ∀ i, m' i ∈ Submodule.span E (Set.range m)) (v : V) (j : ι) :
    H.h (ngsT H m m' v) (m' j) = H.h v (m j) := by
  rw [ngsT_apply, H.h_add_left, ngs_pi' m m' hu hg, ngs_perp_span m (ngs_perp m hu v) (h1 j), zero_add]

theorem gram_transfer_involutive (m m' : ι → V) (hu : IsUnit (H.gram m).det) (hg : H.gram m' = H.gram m)
    (h1 : ∀ i, m' i ∈ Submodule.span E (Set.range m)) (v : V) : ngsT H m' m (ngsT H m m' v) = v := by
  have hc : ngsC H m' (ngsT H m m' v) = ngsC H m v := by
    unfold ngsC
    rw [hg]
    congr 1
    funext j
    exact ngs_T_pair m m' hu hg h1 v j
  rw [ngsT_apply m' m, hc, ngsT_apply m m']
  abel

theorem ngs_T_unit (m m' : ι → V) (hu : IsUnit (H.gram m).det) (hg : H.gram m' = H.gram m)
    (h1 : ∀ i, m' i ∈ Submodule.span E (Set.range m)) (v w : V) :
    H.h (ngsT H m m' v) (ngsT H m m' w) = H.h v w := by
  have hsp : ∀ x : V, ∑ i, ngsC H m x i • m' i ∈ Submodule.span E (Set.range m) := fun x =>
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (h1 i))
  have hsp0 : ∀ x : V, ∑ i, ngsC H m x i • m i ∈ Submodule.span E (Set.range m) := fun x =>
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have z1 : ∀ x y p : V, p ∈ Submodule.span E (Set.range m) →
      H.h (x - ∑ i, ngsC H m x i • m i) p = 0 := fun x _ p hp => ngs_perp_span m (ngs_perp m hu x) hp
  have z2 : ∀ x p : V, p ∈ Submodule.span E (Set.range m) → H.h p (x - ∑ i, ngsC H m x i • m i) = 0 := fun x p hp => by
    rw [H.h_herm _ p, z1 x x p hp, map_zero]
  have e1 : H.h (∑ i, ngsC H m v i • m' i) (∑ i, ngsC H m w i • m' i) =
      H.h (∑ i, ngsC H m v i • m i) (∑ i, ngsC H m w i • m i) := by
    rw [h_sum_left, h_sum_left]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [H.h_herm _ (m' i), ngs_pi' m m' hu hg, H.h_herm _ (m i), ngs_pi m hu]
  have e2 : H.h v w = H.h (v - ∑ i, ngsC H m v i • m i) (w - ∑ i, ngsC H m w i • m i) +
      H.h (∑ i, ngsC H m v i • m i) (∑ i, ngsC H m w i • m i) := by
    have hv : v = (v - ∑ i, ngsC H m v i • m i) + ∑ i, ngsC H m v i • m i := by abel
    have hw : w = (w - ∑ i, ngsC H m w i • m i) + ∑ i, ngsC H m w i • m i := by abel
    conv_lhs => rw [hv, hw]
    rw [H.h_add_left, ngs_add_right, ngs_add_right, z1 v v _ (hsp0 w), z2 w _ (hsp0 v)]
    ring
  rw [ngsT_apply, ngsT_apply, H.h_add_left, ngs_add_right, ngs_add_right, z1 v v _ (hsp w), z2 w _ (hsp v), e1, e2]
  ring

theorem ngs_glue (m m' : ι → V) (hu : IsUnit (H.gram m).det) (hg : H.gram m' = H.gram m)
    (h1 : ∀ i, m' i ∈ Submodule.span E (Set.range m)) (h2 : ∀ i, m i ∈ Submodule.span E (Set.range m')) :
    ∃ s : V ≃ₗ[E] V, IsUnitary H s ∧ (∀ i, s (m i) = m' i) ∧ ∀ k, (∀ j, H.h k (m j) = 0) → s k = k := by
  have hu' : IsUnit (H.gram m').det := by rw [hg]; exact hu
  refine ⟨LinearEquiv.ofLinearMap (ngsT H m m') (ngsT H m' m)
    (LinearMap.ext (fun v => gram_transfer_involutive m' m hu' hg.symm h2 v)) (LinearMap.ext (fun v => gram_transfer_involutive m m' hu hg h1 v)),
    fun v w => ngs_T_unit m m' hu hg h1 v w, fun i => ?_, fun k hk => ?_⟩
  · show ngsT H m m' (m i) = m' i
    have hc : ngsC H m (m i) = Pi.single i 1 := by
      have e : (fun j => H.h (m i) (m j)) = (H.gram m).mulVec (Pi.single i 1) := by
        funext j
        rw [ng_mulVec_gram]
        simp [Pi.single_apply, ite_smul]
      unfold ngsC
      rw [e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    rw [ngsT_apply, hc]
    simp [Pi.single_apply, ite_smul]
  · show ngsT H m m' k = k
    have hc : ngsC H m k = 0 := by
      unfold ngsC
      have e : (fun j => H.h k (m j)) = 0 := funext hk
      rw [e, Matrix.mulVec_zero]
    rw [ngsT_apply, hc]
    simp

end Glue

theorem ngs_low_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) (hA : NgLow A) (hB : NgLow B) : NgLow (A * B) := by
  constructor
  · intro a b hab
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    by_cases h : a < c
    · rw [hA.1 a c h, zero_mul]
    · rw [hB.1 c b (lt_of_le_of_lt (not_lt.1 h) hab), mul_zero]
  · intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2, hB.2, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hB.1 c a h, mul_zero]
      · rw [hA.1 a c h, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem ngs_low_det {n : ℕ} (C : Matrix (Fin n) (Fin n) E) (hC : NgLow C) : C.det = 1 := by
  have hT : C.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have h' : i < j := hij
    exact hC.1 i j h'
  rw [Matrix.det_of_isLowerTriangular _ hT]
  exact Finset.prod_eq_one (fun i _ => hC.2 i)

theorem ngs_comb {n : ℕ} (X R : Matrix (Fin n) (Fin n) E) (f : Fin n → V) (a : Fin n) :
    ∑ c, X a c • (∑ e, R c e • f e) = ∑ e, (X * R) a e • f e := by
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem ngs_back {n : ℕ} (C : Matrix (Fin n) (Fin n) E) (hC : NgLow C) (f g : Fin n → V)
    (hg : ∀ a, g a = ∑ c, C a c • f c) (a : Fin n) : f a ∈ Submodule.span E (Set.range g) := by
  classical
  have hdet : IsUnit C.det := by rw [ngs_low_det C hC]; exact isUnit_one
  have e : f a = ∑ c, C⁻¹ a c • g c := by
    simp only [hg]
    rw [ngs_comb, Matrix.nonsing_inv_mul _ hdet]
    simp [Matrix.one_apply, ite_smul]
  rw [e]
  exact Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩))

theorem ngs_inj {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) (hZ : IsUnit Z.det) (γ : Fin n → E) (h : Z.mulVec γ = 0) : γ = 0 := by
  have h1 := congrArg (Z⁻¹.mulVec) h
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hZ, Matrix.one_mulVec, Matrix.mulVec_zero] at h1

theorem ngs_f_mem_Fj (Fr : FrameD H r) {c : Fin (r + 1)} {n : ℕ} (h : c.val < n) (hn : n ≤ r) : Fr.f c ∈ Fr.Fj n :=
  Submodule.subset_span ⟨⟨c.val, lt_of_lt_of_le h hn⟩, h, congrArg Fr.f (Fin.ext rfl)⟩

theorem ngs_low_sub (Fr : FrameD H r) (C : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hC : NgLow C) (a : Fin (r + 1)) :
    ∑ c, C a c • Fr.f c - Fr.f a ∈ Fr.Fj a.val := by
  classical
  have e : ∑ c, C a c • Fr.f c - Fr.f a = ∑ c, (C a c - if c = a then 1 else 0) • Fr.f c := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [e]
  refine Submodule.sum_mem _ (fun c _ => ?_)
  rcases lt_trichotomy c a with h | h | h
  · exact Submodule.smul_mem _ _ (ngs_f_mem_Fj Fr h (Nat.lt_succ_iff.1 a.2))
  · subst h
    rw [if_pos rfl, hC.2, sub_self, zero_smul]
    exact Submodule.zero_mem _
  · rw [if_neg h.ne', hC.1 a c h, sub_zero, zero_smul]
    exact Submodule.zero_mem _

theorem ngs_low_X (Fr : FrameD H r) (C : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hC : NgLow C) (a : Fin (r + 1)) :
    ∑ c, C a c • Fr.f c - Fr.f a ∈ H.X Fr.f := by
  rw [← Fj_r]
  exact Fj_mono Fr (Nat.lt_succ_iff.1 a.2) (ngs_low_sub Fr C hC a)

theorem ngs_same (Fr : FrameD H r) (C : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hC : NgLow C) (a b : Fin (r + 1)) :
    H.h (∑ c, C a c • Fr.f c) (∑ c, C b c • Fr.f c) = H.h (Fr.f a) (Fr.f b) := by
  have ha := ngs_low_X Fr C hC a
  have hb := ngs_low_X Fr C hC b
  have ea : ∑ c, C a c • Fr.f c = Fr.f a + (∑ c, C a c • Fr.f c - Fr.f a) := by abel
  have eb : ∑ c, C b c • Fr.f c = Fr.f b + (∑ c, C b c • Fr.f c - Fr.f b) := by abel
  rw [ea, eb, H.h_add_left, ngs_add_right, ngs_add_right, h_f_X Fr hb, h_X_f Fr ha, h_X_X Fr ha hb]
  ring

theorem ngs_fix (Fr : FrameD H r) (f' : Fin (r + 1) → V) (s : V ≃ₗ[E] V) (hs : IsUnitary H s)
    (C : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hC : NgLow C) (hsf : ∀ a, s (Fr.f a) = ∑ c, C a c • Fr.f c)
    (hsf' : ∀ b, s (f' b) ∈ Submodule.span E (Set.range f'))
    (hinj : ∀ γ : Fin (r + 1) → E, (∀ a, ∑ b, γ b * H.h (f' b) (Fr.f a) = 0) → γ = 0)
    {y : V} (hy : y ∈ Submodule.span E (Set.range f')) (hye : ∀ a : Fin (r + 1), a.val < r → H.h y (Fr.f a) = 0) :
    s y = y := by
  have step : ∀ a : Fin (r + 1), (∀ c : Fin (r + 1), c < a → H.h (s y) (Fr.f c) = 0) →
      H.h (s y) (Fr.f a) = H.h y (Fr.f a) := by
    intro a hlow
    have h1 : H.h (s y) (s (Fr.f a)) = H.h y (Fr.f a) := hs _ _
    rw [hsf, h_sum_right, Finset.sum_eq_single a] at h1
    · rwa [hC.2, map_one, one_mul] at h1
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hlow c h, mul_zero]
      · rw [hC.1 a c h, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hα0 : ∀ n : ℕ, ∀ a : Fin (r + 1), a.val = n → a.val < r → H.h (s y) (Fr.f a) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a han har
      rw [step a (fun c hc => ih c.val (by rw [← han]; exact hc) c rfl (lt_trans hc har)), hye a har]
  have hα : ∀ a, H.h (s y) (Fr.f a) = H.h y (Fr.f a) := fun a =>
    step a (fun c hc => hα0 _ c rfl (lt_of_lt_of_le hc (Nat.lt_succ_iff.1 a.2)))
  have hsy : s y ∈ Submodule.span E (Set.range f') := by
    have hle : Submodule.span E (Set.range f') ≤ (Submodule.span E (Set.range f')).comap (s : V →ₗ[E] V) :=
      Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact hsf' b)
    exact hle hy
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 (Submodule.sub_mem _ hsy hy)
  have hγ0 : γ = 0 := hinj γ (fun a => by rw [← h_sum_left, hγ, h_sub_left, hα, sub_self])
  rw [hγ0] at hγ
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hγ
  exact sub_eq_zero.1 hγ.symm

theorem ngs_mem_NSet (Fr : FrameD H r) (f' : Fin (r + 1) → V) (s : V ≃ₗ[E] V) (hs : IsUnitary H s)
    (C : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hC : NgLow C) (hsf : ∀ a, s (Fr.f a) = ∑ c, C a c • Fr.f c)
    (hsf' : ∀ b, s (f' b) ∈ Submodule.span E (Set.range f'))
    (hinj : ∀ γ : Fin (r + 1) → E, (∀ a, ∑ b, γ b * H.h (f' b) (Fr.f a) = 0) → γ = 0)
    (hdec : ∀ v : V, ∃ μ ∈ Submodule.span E (Set.range Fr.f), ∃ μ' ∈ Submodule.span E (Set.range f'), ∃ k : V,
      v = μ + μ' + k ∧ (∀ b, H.h k (Fr.f b) = 0) ∧ s k = k) : s ∈ Fr.NSet := by
  have L1 : ∀ a, s (Fr.f a) - Fr.f a ∈ Fr.Fj a.val := fun a => by rw [hsf]; exact ngs_low_sub Fr C hC a
  refine ⟨hs, fun j hj v hv => ?_, fun v hv => ?_⟩
  · have hle : Fr.Fj j ≤ (Fr.Fj (j - 1)).comap ((s : V →ₗ[E] V) - LinearMap.id) := by
      show Submodule.span E (Fr.e '' {a | a.val < j}) ≤ _
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      show s (Fr.e a) - Fr.e a ∈ Fr.Fj (j - 1)
      have ha' : a.val < j := ha
      exact Fj_mono Fr (by show a.val ≤ j - 1; omega) (L1 a.castSucc)
    exact hle hv
  · obtain ⟨μ, hμ, μ', hμ', k, rfl, hk, hsk⟩ := hdec v
    have hμX : s μ - μ ∈ H.X Fr.f := by
      have hle : Submodule.span E (Set.range Fr.f) ≤ (H.X Fr.f).comap ((s : V →ₗ[E] V) - LinearMap.id) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨a, rfl⟩
        show s (Fr.f a) - Fr.f a ∈ H.X Fr.f
        rw [← Fj_r]
        exact Fj_mono Fr (Nat.lt_succ_iff.1 a.2) (L1 a)
      exact hle hμ
    have hμ'e : ∀ a : Fin (r + 1), a.val < r → H.h μ' (Fr.f a) = 0 := by
      intro a har
      have hne : a ≠ Fin.last r := fun h => by rw [h] at har; exact lt_irrefl _ har
      have hmem : Fr.f a ∈ H.X Fr.f := Submodule.subset_span ⟨⟨a.val, har⟩, congrArg Fr.f (Fin.ext rfl)⟩
      have h0 := hv (Fr.f a) hmem
      rw [H.h_add_left, H.h_add_left, hk, add_zero] at h0
      have h1 : H.h μ (Fr.f a) = 0 := by
        rw [H.h_herm (Fr.f a) μ, ngs_perp_span Fr.f (fun j => Fr.h_iso a j (Or.inl hne)) hμ, map_zero]
      rwa [h1, zero_add] at h0
    have hfix : s μ' = μ' := ngs_fix Fr f' s hs C hC hsf hsf' hinj hμ' hμ'e
    have e : s (μ + μ' + k) - (μ + μ' + k) = s μ - μ := by rw [map_add, map_add, hfix, hsk]; abel
    rw [e]
    exact hμX

variable {P : FPair H r}

theorem ngs_Dm_last (P : FPair H r) : P.Dm (r + 1) = (H.Zhat P.A.f P.B.f).det := by
  unfold FPair.Dm HermSp.Dl
  rw [dif_pos le_rfl]
  congr 1

theorem NGOrbit0_of_mat (hR : P.RelG (theta M)) (hMat : NGMat P) : NGOrbit0 P := by
  classical
  intro n hn n' hn' hint
  have hnS := mem_NSet_of_mem_N P.A hn
  have hnS' := mem_NSet_of_mem_N P.B hn'
  choose R hR1 hR2 hR3 using N_row P.A hnS
  choose R' hR1' hR2' hR3' using N_row P.B hnS'
  have hRl : NgLow (Matrix.of R) := ⟨fun a b h => hR1 a b h, hR2⟩
  have hRl' : NgLow (Matrix.of R') := ⟨fun a b h => hR1' a b h, hR2'⟩
  have hLo : NgLow ((Matrix.of R).map M.L.cj) :=
    ⟨fun a b h => by rw [Matrix.map_apply, Matrix.of_apply, hR1 a b h, map_zero],
      fun a => by rw [Matrix.map_apply, Matrix.of_apply, hR2 a, map_one]⟩
  have hUp : NgUp (Matrix.of R').transpose := ⟨fun a b h => hR1' b a h, fun a => hR2' a⟩
  have hZ : ∀ a b, ((Matrix.of R).map M.L.cj * H.Zhat P.A.f P.B.f * (Matrix.of R').transpose) a b =
      H.h (n' (P.B.f b)) (n (P.A.f a)) := by
    intro a b
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, HermSp.Zhat]
    rw [hR3 a, hR3' b, h_sum_left]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [h_sum_right, mul_comm]
  obtain ⟨A, A', hA, hA', hAi, hAi', hEq⟩ := hMat _ _ hLo hUp (fun a b => by rw [hZ]; exact hint a b)
  generalize hZm : (Matrix.of R).map M.L.cj * H.Zhat P.A.f P.B.f * (Matrix.of R').transpose = Zm at hZ hEq
  have hAc : NgLow (A.map M.L.cj) :=
    ⟨fun a b h => by rw [Matrix.map_apply, hA.1 a b h, map_zero], fun a => by rw [Matrix.map_apply, hA.2 a, map_one]⟩
  have hAt : NgLow A'.transpose := ⟨fun a b h => hA'.1 b a h, fun a => hA'.2 a⟩
  have hC := ngs_low_mul _ _ hAc hRl
  have hC' := ngs_low_mul _ _ hAt hRl'
  set C := A.map M.L.cj * Matrix.of R with hCdef
  set C' := A'.transpose * Matrix.of R' with hCdef'
  have hgn : ∀ a, ∑ c, C a c • P.A.f c = ∑ c, M.L.cj (A a c) • n (P.A.f c) := by
    intro a
    rw [hCdef, ← ngs_comb]
    exact Finset.sum_congr rfl (fun c _ => by rw [hR3 c]; rfl)
  have hgn' : ∀ b, ∑ d, C' b d • P.B.f d = ∑ d, A' d b • n' (P.B.f d) := by
    intro b
    rw [hCdef', ← ngs_comb]
    exact Finset.sum_congr rfl (fun d _ => by rw [hR3' d]; rfl)
  have hpair : ∀ a b, H.h (∑ d, C' b d • P.B.f d) (∑ c, C a c • P.A.f c) = H.h (P.B.f b) (P.A.f a) := by
    intro a b
    have e := congrFun (congrFun hEq a) b
    simp only [Matrix.mul_apply] at e
    rw [hgn, hgn', h_sum_left]
    simp only [h_sum_right, ← hZ, M.L.cj_cj]
    rw [show H.h (P.B.f b) (P.A.f a) = H.Zhat P.A.f P.B.f a b from rfl, ← e]
    exact Finset.sum_congr rfl (fun d _ => mul_comm _ _)
  have hgram : H.gram (Sum.elim (fun a => ∑ c, C a c • P.A.f c) (fun b => ∑ d, C' b d • P.B.f d)) =
      H.gram (Sum.elim P.A.f P.B.f) := by
    ext x y
    simp only [HermSp.gram, Matrix.of_apply]
    rcases x with a | a <;> rcases y with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact ngs_same P.A C hC b a
    · exact hpair a b
    · rw [H.h_herm _ (∑ c, C b c • P.A.f c), hpair b a, ← H.h_herm]
    · exact ngs_same P.B C' hC' b a
  have hu : IsUnit (H.gram (Sum.elim P.A.f P.B.f)).det := by
    rw [ng_gram_base]
    exact ((isUnit_one.neg).pow _).mul (ng_G_unit hR.2.2.1)
  have hl : Submodule.span E (Set.range P.A.f) ≤ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)) :=
    Submodule.span_mono (by rintro _ ⟨c, rfl⟩; exact ⟨Sum.inl c, rfl⟩)
  have hr : Submodule.span E (Set.range P.B.f) ≤ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)) :=
    Submodule.span_mono (by rintro _ ⟨c, rfl⟩; exact ⟨Sum.inr c, rfl⟩)
  have hgA : ∀ a, ∑ c, C a c • P.A.f c ∈ Submodule.span E (Set.range P.A.f) := fun a =>
    Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩))
  have hgB : ∀ b, ∑ d, C' b d • P.B.f d ∈ Submodule.span E (Set.range P.B.f) := fun b =>
    Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩))
  obtain ⟨s, hsU, hsm, hsk⟩ := ngs_glue (Sum.elim P.A.f P.B.f)
    (Sum.elim (fun a => ∑ c, C a c • P.A.f c) (fun b => ∑ d, C' b d • P.B.f d)) hu hgram
    (by
      rintro (a | b)
      · exact hl (hgA a)
      · exact hr (hgB b))
    (by
      rintro (a | b)
      · exact Submodule.span_mono (by rintro _ ⟨c, rfl⟩; exact ⟨Sum.inl c, rfl⟩)
          (ngs_back C hC P.A.f _ (fun _ => rfl) a)
      · exact Submodule.span_mono (by rintro _ ⟨c, rfl⟩; exact ⟨Sum.inr c, rfl⟩)
          (ngs_back C' hC' P.B.f _ (fun _ => rfl) b))
  have hsA : ∀ a, s (P.A.f a) = ∑ c, C a c • P.A.f c := fun a => hsm (Sum.inl a)
  have hsB : ∀ b, s (P.B.f b) = ∑ d, C' b d • P.B.f d := fun b => hsm (Sum.inr b)
  have hdetZ : IsUnit (H.Zhat P.A.f P.B.f).det := by rw [← ngs_Dm_last]; exact hR.2.1
  have hdec : ∀ v : V, ∃ μ ∈ Submodule.span E (Set.range P.A.f), ∃ μ' ∈ Submodule.span E (Set.range P.B.f),
      ∀ j, H.h (v - (μ + μ')) (Sum.elim P.A.f P.B.f j) = 0 := by
    intro v
    obtain ⟨p, hp, hk⟩ := ngs_dec (Sum.elim P.A.f P.B.f) hu v
    rw [Set.Sum.elim_range, Submodule.span_union] at hp
    obtain ⟨μ, hμ, μ', hμ', rfl⟩ := Submodule.mem_sup.1 hp
    exact ⟨μ, hμ, μ', hμ', hk⟩
  have hsNA : s ∈ P.A.NSet := by
    refine ngs_mem_NSet P.A P.B.f s hsU C hC hsA (fun b => by rw [hsB]; exact hgB b) (fun γ hγ => ?_) (fun v => ?_)
    · refine ngs_inj _ hdetZ γ (funext fun a => ?_)
      have h0 := hγ a
      simp only [Matrix.mulVec, dotProduct, HermSp.Zhat, Matrix.of_apply, Pi.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
    · obtain ⟨μ, hμ, μ', hμ', hk⟩ := hdec v
      exact ⟨μ, hμ, μ', hμ', v - (μ + μ'), by abel, fun b => hk (Sum.inl b), hsk _ hk⟩
  have hsNB : s ∈ P.B.NSet := by
    refine ngs_mem_NSet P.B P.A.f s hsU C' hC' hsB (fun a => by rw [hsA]; exact hgA a) (fun γ hγ => ?_) (fun v => ?_)
    · have hz : (fun b => M.L.cj (γ b)) = 0 := by
        refine ngs_inj (H.Zhat P.A.f P.B.f).transpose (by rw [Matrix.det_transpose]; exact hdetZ) _ (funext fun a => ?_)
        have h0 := congrArg M.L.cj (hγ a)
        rw [map_sum, map_zero] at h0
        simp only [Matrix.mulVec, dotProduct, HermSp.Zhat, Matrix.of_apply, Matrix.transpose_apply, Pi.zero_apply]
        rw [← h0]
        exact Finset.sum_congr rfl (fun b _ => by rw [map_mul, ← H.h_herm, mul_comm])
      funext b
      have h1 := congrFun hz b
      have h2 := congrArg M.L.cj h1
      rwa [M.L.cj_cj, Pi.zero_apply, map_zero] at h2
    · obtain ⟨μ, hμ, μ', hμ', hk⟩ := hdec v
      exact ⟨μ', hμ', μ, hμ, v - (μ + μ'), by abel, fun b => hk (Sum.inr b), hsk _ hk⟩
  refine ⟨s, ⟨Subgroup.subset_closure hsNA, Subgroup.subset_closure hsNB⟩, ?_, ?_⟩
  · have hm : n⁻¹ * s ∈ P.A.NSet := NSet_mul P.A (NSet_inv P.A hnS) hsNA
    have e : ∀ b, (n⁻¹ * s) (P.A.f b) = ∑ c, M.L.cj (A b c) • P.A.f c := by
      intro b
      show n.symm (s (P.A.f b)) = _
      rw [hsA, hgn, map_sum]
      exact Finset.sum_congr rfl (fun c _ => by rw [map_smul, LinearEquiv.symm_apply_apply])
    have h0 := ng_span_frame P.A hm (fun a b => by
      rw [ng_row_coef P.A (e b) a]; exact Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (hAi _ _))
    have h1 := congrArg (img n) h0
    rw [ng_img_span, ng_img_span] at h1
    have e2 : (fun b => n ((n⁻¹ * s) (P.A.f b))) = fun b => s (P.A.f b) := by
      funext b
      show n (n.symm (s (P.A.f b))) = _
      rw [LinearEquiv.apply_symm_apply]
    rw [e2] at h1
    exact h1
  · have hm : n'⁻¹ * s ∈ P.B.NSet := NSet_mul P.B (NSet_inv P.B hnS') hsNB
    have e : ∀ b, (n'⁻¹ * s) (P.B.f b) = ∑ d, A' d b • P.B.f d := by
      intro b
      show n'.symm (s (P.B.f b)) = _
      rw [hsB, hgn', map_sum]
      exact Finset.sum_congr rfl (fun c _ => by rw [map_smul, LinearEquiv.symm_apply_apply])
    have h0 := ng_span_frame P.B hm (fun a b => by
      rw [ng_row_coef P.B (e b) a]; exact hAi' _ _)
    have h1 := congrArg (img n') h0
    rw [ng_img_span, ng_img_span] at h1
    have e2 : (fun b => n' ((n'⁻¹ * s) (P.B.f b))) = fun b => s (P.B.f b) := by
      funext b
      show n' (n'.symm (s (P.B.f b))) = _
      rw [LinearEquiv.apply_symm_apply]
    rw [e2] at h1
    exact h1

end NGc

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.MainNotions.S.LocNG

section Grp

variable {G : Type*} [Group G]

theorem ngu_group (K K1 : Subgroup G) (s : G) (hs : s ∈ K1) (h1 : K1.relIndex K ≠ 0) (h2 : K.relIndex K1 ≠ 0) :
    volRel (K.map (MulAut.conj s).toMonoidHom) K = 1 := by
  have hinj : Function.Injective (MulAut.conj s).toMonoidHom := (MulAut.conj s).injective
  have hK1 : K1.map (MulAut.conj s).toMonoidHom = K1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show s * y * s⁻¹ ∈ K1
      exact K1.mul_mem (K1.mul_mem hs hy) (K1.inv_mem hs)
    · intro hx
      exact ⟨s⁻¹ * x * s, K1.mul_mem (K1.mul_mem (K1.inv_mem hs) hx) hs, by
        show s * (s⁻¹ * x * s) * s⁻¹ = x
        group⟩
  obtain ⟨Ks, hKs⟩ : ∃ Ks, Ks = K.map (MulAut.conj s).toMonoidHom := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = K ⊓ K1 := ⟨_, rfl⟩
  obtain ⟨Ls, hLs0⟩ : ∃ Ls, Ls = L.map (MulAut.conj s).toMonoidHom := ⟨_, rfl⟩
  rw [← hKs]
  have hLs : Ls = Ks ⊓ K1 := by rw [hLs0, hL, Subgroup.map_inf _ _ _ hinj, hK1, hKs]
  have hLK : L ≤ K := hL ▸ inf_le_left
  have hLK1 : L ≤ K1 := hL ▸ inf_le_right
  have hLsK : Ls ≤ Ks := hLs ▸ inf_le_left
  have hLsK1 : Ls ≤ K1 := hLs ▸ inf_le_right
  have a1 : L.relIndex K1 ≠ 0 := by rw [hL, Subgroup.inf_relIndex_right]; exact h2
  have a2 : Ls.relIndex K1 = L.relIndex K1 := by
    have h := Subgroup.relIndex_map_map_of_injective L K1 hinj
    rwa [hK1, ← hLs0] at h
  have b1 : L.relIndex K ≠ 0 := by rw [hL, Subgroup.inf_relIndex_left]; exact h1
  have b2 : Ls.relIndex Ks = L.relIndex K := by
    rw [hLs0, hKs]; exact Subgroup.relIndex_map_map_of_injective L K hinj
  have d0 : (L ⊓ Ls).relIndex K1 ≠ 0 := Subgroup.relIndex_inf_ne_zero a1 (a2 ▸ a1)
  have e1 : (L ⊓ Ls).relIndex L * L.relIndex K1 = (L ⊓ Ls).relIndex K1 :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left hLK1
  have e2 : (L ⊓ Ls).relIndex Ls * Ls.relIndex K1 = (L ⊓ Ls).relIndex K1 :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right hLsK1
  have e3 : (L ⊓ Ls).relIndex L = (L ⊓ Ls).relIndex Ls := by
    rw [a2] at e2
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero a1) (e1.trans e2.symm)
  have e4 : (L ⊓ Ls).relIndex L ≠ 0 := by
    intro h
    rw [h, zero_mul] at e1
    exact d0 e1.symm
  have f1 : (L ⊓ Ls).relIndex L * L.relIndex K = (L ⊓ Ls).relIndex K :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left hLK
  have f2 : (L ⊓ Ls).relIndex Ls * Ls.relIndex Ks = (L ⊓ Ls).relIndex Ks :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right hLsK
  have f3 : (L ⊓ Ls).relIndex K = (L ⊓ Ls).relIndex Ks := by rw [← f1, ← f2, e3, b2]
  have f0 : (L ⊓ Ls).relIndex K ≠ 0 := by rw [← f1]; exact mul_ne_zero e4 b1
  have hDI : L ⊓ Ls ≤ K ⊓ Ks := le_inf (inf_le_left.trans hLK) (inf_le_right.trans hLsK)
  have g1 : (L ⊓ Ls).relIndex (K ⊓ Ks) * (K ⊓ Ks).relIndex K = (L ⊓ Ls).relIndex K :=
    Subgroup.relIndex_mul_relIndex _ _ _ hDI inf_le_left
  have g2 : (L ⊓ Ls).relIndex (K ⊓ Ks) * (K ⊓ Ks).relIndex Ks = (L ⊓ Ls).relIndex Ks :=
    Subgroup.relIndex_mul_relIndex _ _ _ hDI inf_le_right
  have g0 : (L ⊓ Ls).relIndex (K ⊓ Ks) ≠ 0 := by
    intro h
    rw [h, zero_mul] at g1
    exact f0 g1.symm
  have g3 : (K ⊓ Ks).relIndex K = (K ⊓ Ks).relIndex Ks :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero g0) (g1.trans (f3.trans g2.symm))
  have g4 : (K ⊓ Ks).relIndex K ≠ 0 := by
    intro h
    rw [h, mul_zero] at g1
    exact f0 g1.symm
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_right] at g3
  rw [Subgroup.inf_relIndex_left] at g4
  unfold volRel
  rw [← g3]
  exact div_self (by exact_mod_cast g4)

theorem ngu_finite_index {α : Type*} [Finite α] (K N : Subgroup G) (f : K → α)
    (h : ∀ a b : K, f a = f b → (a : G)⁻¹ * b ∈ N) : N.relIndex K ≠ 0 := by
  classical
  have hfin : Finite (K ⧸ N.subgroupOf K) := by
    have hsurj : Function.Surjective
        (fun y : Set.range f => (QuotientGroup.mk (Classical.choose y.2) : K ⧸ N.subgroupOf K)) := by
      intro q
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨⟨f a, a, rfl⟩, ?_⟩
      have hc : f (Classical.choose (⟨a, rfl⟩ : ∃ x, f x = f a)) = f a := Classical.choose_spec (⟨a, rfl⟩ : ∃ x, f x = f a)
      exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (by simpa using h _ _ hc))
    exact Finite.of_surjective _ hsurj
  unfold Subgroup.relIndex Subgroup.index
  exact Nat.card_pos.ne'

end Grp

section Lat

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem ngu_smulO (S : Submodule M.L.O V) {c : E} (hc : c ∈ M.L.O) {x : V} (hx : x ∈ S) : c • x ∈ S := by
  have h : c • x = (⟨c, hc⟩ : M.L.O) • x := rfl
  rw [h]; exact S.smul_mem _ hx

def NguFinRep (M : Model F E) (c : E) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (rep : Q → E), ∀ o ∈ M.L.O, ∃ q, ∃ o' ∈ M.L.O, o - rep q = c * o'

theorem ngu_finRep (hOK : M.OK) (a : 𝒪[F]) (ha0 : (a : F) ≠ 0) : NguFinRep M (algebraMap F E (a : F)) := by
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  have := hOK.borel
  have := hOK.haar.haar
  obtain ⟨hO, hC, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top M.L
  obtain ⟨u, hu⟩ := (ha0.isUnit.map (algebraMap F E))
  let OO : AddSubgroup E := M.L.O.toAddSubgroup
  let am : E →+ E := AddMonoidHom.mulLeft (algebraMap F E (a : F))
  have haO : OO.map am ≤ OO := by
    rintro _ ⟨x, hx, rfl⟩
    exact M.L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L a) hx
  have hset : ((OO.map am : AddSubgroup E) : Set E) = (fun y => (u : E) * y) '' (M.L.O : Set E) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [hu]; rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [hu]; rfl⟩
  have haOo : IsOpen ((OO.map am : AddSubgroup E) : Set E) := by
    rw [hset]
    have h : (fun y => (u : E) * y) '' (M.L.O : Set E) = (fun y => ((u⁻¹ : Eˣ) : E) * y) ⁻¹' (M.L.O : Set E) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show ((u⁻¹ : Eˣ) : E) * ((u : E) * z) ∈ M.L.O
        rw [← mul_assoc, Units.inv_mul, one_mul]; exact hz
      · intro hy
        exact ⟨_, hy, by show (u : E) * (((u⁻¹ : Eˣ) : E) * y) = y; rw [← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [h]
    exact hO.preimage (by fun_prop)
  have hN0 := (Formalism.MainNotions.LocalModelPeriodLattices.measure_eq_relIndex_mul M.mu (OO.map am) OO haO haOo hC).1
  have hfin : Finite (OO ⧸ (OO.map am).addSubgroupOf OO) := Nat.finite_of_card_ne_zero hN0
  refine ⟨OO ⧸ (OO.map am).addSubgroupOf OO, hfin, fun q => ((Quotient.out q : OO) : E), ?_⟩
  intro o ho
  refine ⟨QuotientAddGroup.mk (⟨o, ho⟩ : OO), ?_⟩
  have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk (⟨o, ho⟩ : OO) : OO ⧸ (OO.map am).addSubgroupOf OO)) :
      OO ⧸ (OO.map am).addSubgroupOf OO) = QuotientAddGroup.mk (⟨o, ho⟩ : OO) := QuotientAddGroup.out_eq' _
  have h2 := QuotientAddGroup.eq.1 h1
  obtain ⟨o', ho', he⟩ := AddSubgroup.mem_addSubgroupOf.1 h2
  refine ⟨o', ho', ?_⟩
  have he' : algebraMap F E (a : F) * o' =
      -((Quotient.out (QuotientAddGroup.mk (⟨o, ho⟩ : OO) : OO ⧸ (OO.map am).addSubgroupOf OO) : OO) : E) + o := he
  rw [he']; ring

theorem ngu_congr_index {ι : Type} [Fintype ι] (m : ι → V) (c : E) (hfin : NguFinRep M c) (S T : Subgroup (V ≃ₗ[E] V))
    (hT : ∀ κ ∈ S ⊓ Aut (Submodule.span M.L.O (Set.range m)),
      (∀ x ∈ Submodule.span M.L.O (Set.range m), ∃ w ∈ Submodule.span M.L.O (Set.range m), κ x - x = c • w) → κ ∈ T) :
    T.relIndex (S ⊓ Aut (Submodule.span M.L.O (Set.range m))) ≠ 0 := by
  classical
  obtain ⟨Q, hQ, rep, hrep⟩ := hfin
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = Submodule.span M.L.O (Set.range m) := ⟨_, rfl⟩
  rw [← hΛ] at hT ⊢
  have hgen : ∀ j, m j ∈ Λ := fun j => hΛ ▸ Submodule.subset_span ⟨j, rfl⟩
  have step1 : ∀ x ∈ Λ, ∃ ρ : ι → Q, ∃ w ∈ Λ, x - ∑ j, rep (ρ j) • m j = c • w := by
    intro x hx
    rw [hΛ] at hx
    obtain ⟨o, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 hx
    choose q o' ho' he using fun j => hrep (o j : E) (o j).2
    refine ⟨q, ∑ j, o' j • m j, Submodule.sum_mem _ (fun j _ => ngu_smulO Λ (ho' j) (hgen j)), ?_⟩
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show (o j : E) • m j - rep (q j) • m j = c • (o' j • m j)
    rw [← sub_smul, he j, mul_smul]
  have hmem : ∀ κ : ↥(S ⊓ Aut Λ), ∀ x ∈ Λ, (κ : V ≃ₗ[E] V) x ∈ Λ := by
    intro κ x hx
    have h := ng_mem_Aut.1 κ.2.2
    exact h.le ⟨x, hx, rfl⟩
  choose ρ w hw he using step1
  refine ngu_finite_index (α := ι → ι → Q) _ _ (fun κ j => ρ ((κ : V ≃ₗ[E] V) (m j)) (hmem κ _ (hgen j))) ?_
  intro a b hab
  refine hT _ ((S ⊓ Aut Λ).mul_mem ((S ⊓ Aut Λ).inv_mem a.2) b.2) ?_
  have hj : ∀ j, ∃ w' ∈ Λ, (b : V ≃ₗ[E] V) (m j) - (a : V ≃ₗ[E] V) (m j) = c • w' := by
    intro j
    have h1 := he _ (hmem a _ (hgen j))
    have h2 := he _ (hmem b _ (hgen j))
    have h3 : ρ ((a : V ≃ₗ[E] V) (m j)) (hmem a _ (hgen j)) = ρ ((b : V ≃ₗ[E] V) (m j)) (hmem b _ (hgen j)) :=
      congrFun hab j
    refine ⟨w _ (hmem b _ (hgen j)) - w _ (hmem a _ (hgen j)),
      Λ.sub_mem (hw _ (hmem b _ (hgen j))) (hw _ (hmem a _ (hgen j))), ?_⟩
    rw [smul_sub, ← h2, ← h1, h3]; abel
  have hall : ∀ x ∈ Λ, ∃ w' ∈ Λ, (b : V ≃ₗ[E] V) x - (a : V ≃ₗ[E] V) x = c • w' := by
    intro x hx
    rw [hΛ] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hj j
    | zero => exact ⟨0, Λ.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w1, h1, e1⟩ := hx
      obtain ⟨w2, h2, e2⟩ := hy
      exact ⟨w1 + w2, Λ.add_mem h1 h2, by rw [map_add, map_add, smul_add, ← e1, ← e2]; abel⟩
    | smul o x _ hx =>
      obtain ⟨w1, h1, e1⟩ := hx
      refine ⟨(o : E) • w1, ngu_smulO Λ o.2 h1, ?_⟩
      show (b : V ≃ₗ[E] V) ((o : E) • x) - (a : V ≃ₗ[E] V) ((o : E) • x) = c • ((o : E) • w1)
      rw [map_smul, map_smul, ← smul_sub, e1, smul_comm]
  intro x hx
  obtain ⟨w1, h1, e1⟩ := hall x hx
  have hinv : img (a : V ≃ₗ[E] V)⁻¹ Λ = Λ := ng_img_inv (ng_mem_Aut.1 a.2.2)
  refine ⟨(a : V ≃ₗ[E] V).symm w1, hinv.le ⟨w1, h1, rfl⟩, ?_⟩
  show (a : V ≃ₗ[E] V).symm ((b : V ≃ₗ[E] V) x) - x = c • (a : V ≃ₗ[E] V).symm w1
  have e2 : (b : V ≃ₗ[E] V) x = (a : V ≃ₗ[E] V) x + c • w1 := by rw [← e1]; abel
  rw [e2, map_add, LinearEquiv.symm_apply_apply, map_smul]; abel

theorem ngu_stab {Λ Λ' : Submodule M.L.O V} {d d' : E} (hdd : d' * d = 1) (h2 : ∀ x ∈ Λ', d • x ∈ Λ)
    (h1 : ∀ x ∈ Λ, d • x ∈ Λ') {κ : V ≃ₗ[E] V} (hκ : img κ Λ = Λ)
    (hc : ∀ x ∈ Λ, ∃ w ∈ Λ, κ x - x = (d * d) • w) : img κ Λ' = Λ' := by
  have key : ∀ g : V ≃ₗ[E] V, (∀ x ∈ Λ, ∃ w ∈ Λ, g x - x = (d * d) • w) → ∀ x ∈ Λ', g x ∈ Λ' := by
    intro g hg x hx
    obtain ⟨w, hw, e⟩ := hg (d • x) (h2 x hx)
    have e1 : g x - x = d • w := by
      have e2 : d • (g x - x) = d • (d • w) := by rw [smul_sub, ← map_smul, e, mul_smul]
      have e3 := congrArg (fun y => d' • y) e2
      simpa only [smul_smul, hdd, one_smul, ← mul_assoc, one_mul] using e3
    have e4 : g x = d • w + x := by rw [← e1]; abel
    rw [e4]
    exact Λ'.add_mem (h1 w hw) hx
  have hinv : img κ⁻¹ Λ = Λ := ng_img_inv hκ
  have hc' : ∀ x ∈ Λ, ∃ w ∈ Λ, κ.symm x - x = (d * d) • w := by
    intro x hx
    have hy : κ.symm x ∈ Λ := by rw [← hinv]; exact ⟨x, hx, rfl⟩
    obtain ⟨w, hw, e⟩ := hc _ hy
    rw [LinearEquiv.apply_symm_apply] at e
    exact ⟨-w, Λ.neg_mem hw, by rw [smul_neg, ← e]; abel⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact key κ hc x hx
  · intro x hx
    exact ⟨κ.symm x, key κ.symm hc' x hx, LinearEquiv.apply_symm_apply κ x⟩

theorem ngu_span_smul {ι : Type} (m : ι → V) (d : E) (Λ' : Submodule M.L.O V) (h : ∀ j, d • m j ∈ Λ') :
    ∀ x ∈ Submodule.span M.L.O (Set.range m), d • x ∈ Λ' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
  | zero => rw [smul_zero]; exact Λ'.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact Λ'.add_mem hx hy
  | smul o x _ hx =>
    have e : d • (o • x) = (o : E) • (d • x) := by
      show d • ((o : E) • x) = _
      rw [smul_comm]
    rw [e]; exact ngu_smulO Λ' o.2 hx

theorem ngu_img_le {ι : Type} (m : ι → V) (g : V ≃ₗ[E] V) (Λ' : Submodule M.L.O V) (h : ∀ j, g (m j) ∈ Λ') :
    img g (Submodule.span M.L.O (Set.range m)) ≤ Λ' := by
  rintro _ ⟨x, hx, rfl⟩
  show g x ∈ Λ'
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
  | zero => rw [map_zero]; exact Λ'.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact Λ'.add_mem hx hy
  | smul o x _ hx =>
    have e : g (o • x) = (o : E) • g x := by
      show g ((o : E) • x) = _
      rw [map_smul]
    rw [e]; exact ngu_smulO Λ' o.2 hx

theorem ngu_frame {r : ℕ} (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) (row : Fin (r + 1) → Fin (r + 1) → E)
    (h1 : ∀ b i, b < i → row b i = 0) (h2 : ∀ b, row b b = 1) (h3 : ∀ b, g (f b) = ∑ i, row b i • f i)
    (c : E) (hcO : c ∈ M.L.O) (hc : ∀ b i, c * row b i ∈ M.L.O) (Λ : Submodule M.L.O V)
    (hΛ : ∀ i : Fin (r + 1), c ^ (i : ℕ) • f i ∈ Λ) (b : Fin (r + 1)) : g (c ^ (b : ℕ) • f b) ∈ Λ := by
  rw [map_smul, h3, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rcases lt_trichotomy i b with hlt | rfl | hgt
  · have hlt' : (i : ℕ) < (b : ℕ) := hlt
    have e : c ^ (b : ℕ) • row b i • f i = (c ^ ((b : ℕ) - i - 1) * (c * row b i)) • (c ^ (i : ℕ) • f i) := by
      rw [smul_smul, smul_smul]
      congr 1
      have hb : (b : ℕ) = ((b : ℕ) - i - 1) + 1 + i := by omega
      conv_lhs => rw [hb, pow_add, pow_add, pow_one]
      ring
    rw [e]
    exact ngu_smulO Λ (M.L.O.mul_mem (M.L.O.pow_mem hcO _) (hc b i)) (hΛ i)
  · rw [h2, one_smul]; exact hΛ i
  · rw [h1 b i hgt, zero_smul, smul_zero]; exact Λ.zero_mem

variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

theorem NGUnimod_of (hOK : M.OK) (hX : H.Xp P.A.f ⊓ H.Xp P.B.f = ⊥) : NGUnimod P := by
  classical
  intro s hs
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  obtain ⟨-, -, hden⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top M.L
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hs' : s⁻¹ ∈ P.St := P.St.inv_mem hs
  choose rA a1 a2 a3 using N_row P.A (mem_NSet_of_mem_N P.A hs.1)
  choose rB b1 b2 b3 using N_row P.B (mem_NSet_of_mem_N P.B hs.2)
  choose rA' a1' a2' a3' using N_row P.A (mem_NSet_of_mem_N P.A hs'.1)
  choose rB' b1' b2' b3' using N_row P.B (mem_NSet_of_mem_N P.B hs'.2)
  choose mk hmk using fun p : Fin 4 × Fin (r + 1) × Fin (r + 1) => hden π hπ ((![rA, rB, rA', rB'] p.1) p.2.1 p.2.2)
  obtain ⟨k, hk⟩ : ∃ k, k = Finset.univ.sup mk := ⟨_, rfl⟩
  have hkk : ∀ p : Fin 4 × Fin (r + 1) × Fin (r + 1),
      algebraMap F E (π : F) ^ k * ((![rA, rB, rA', rB'] p.1) p.2.1 p.2.2) ∈ M.L.O := fun p =>
    hmk p k (hk ▸ Finset.le_sup (Finset.mem_univ p))
  obtain ⟨c, hc⟩ : ∃ c, c = algebraMap F E (π : F) ^ k := ⟨_, rfl⟩
  rw [← hc] at hkk
  have hcO : c ∈ M.L.O := hc ▸ M.L.O.pow_mem (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L π) k
  obtain ⟨m1, hm1⟩ : ∃ m1 : Fin (r + 1) ⊕ Fin (r + 1) → V,
      m1 = Sum.elim (fun b : Fin (r + 1) => c ^ (b : ℕ) • P.A.f b) (fun b : Fin (r + 1) => c ^ (b : ℕ) • P.B.f b) :=
    ⟨_, rfl⟩
  obtain ⟨M1, hM1⟩ : ∃ M1, M1 = Submodule.span M.L.O (Set.range m1) := ⟨_, rfl⟩
  obtain ⟨M0, hM0⟩ : ∃ M0, M0 = Submodule.span M.L.O (Set.range (Sum.elim P.A.f P.B.f)) := ⟨_, rfl⟩
  have hgA : ∀ i : Fin (r + 1), c ^ (i : ℕ) • P.A.f i ∈ M1 := fun i => by
    rw [hM1]; exact Submodule.subset_span ⟨Sum.inl i, by rw [hm1]; rfl⟩
  have hgB : ∀ i : Fin (r + 1), c ^ (i : ℕ) • P.B.f i ∈ M1 := fun i => by
    rw [hM1]; exact Submodule.subset_span ⟨Sum.inr i, by rw [hm1]; rfl⟩
  have hle : ∀ g : V ≃ₗ[E] V, (∀ b : Fin (r + 1), g (c ^ (b : ℕ) • P.A.f b) ∈ M1) →
      (∀ b : Fin (r + 1), g (c ^ (b : ℕ) • P.B.f b) ∈ M1) →
      img g M1 ≤ M1 := by
    intro g hA hB
    rw [hM1]
    refine ngu_img_le m1 g _ (fun j => ?_)
    rw [← hM1, hm1]
    rcases j with b | b
    · exact hA b
    · exact hB b
  have hs1 : img s M1 ≤ M1 := hle s
    (ngu_frame P.A.f s rA a1 a2 a3 c hcO (fun b i => hkk (0, b, i)) M1 hgA)
    (ngu_frame P.B.f s rB b1 b2 b3 c hcO (fun b i => hkk (1, b, i)) M1 hgB)
  have hs2 : img s⁻¹ M1 ≤ M1 := hle s⁻¹
    (ngu_frame P.A.f s⁻¹ rA' a1' a2' a3' c hcO (fun b i => hkk (2, b, i)) M1 hgA)
    (ngu_frame P.B.f s⁻¹ rB' b1' b2' b3' c hcO (fun b i => hkk (3, b, i)) M1 hgB)
  have hsM1 : img s M1 = M1 := by
    refine le_antisymm hs1 ?_
    have h := ng_img_mono s hs2
    rwa [← ng_img_mul, mul_inv_cancel, ng_img_one] at h
  obtain ⟨d, hd⟩ : ∃ d, d = c ^ r := ⟨_, rfl⟩
  have hdO : d ∈ M.L.O := hd ▸ M.L.O.pow_mem hcO r
  have hdd : (algebraMap F E (π : F)⁻¹ ^ k) ^ r * d = 1 := by
    rw [hd, hc, ← mul_pow, ← mul_pow, ← map_mul, inv_mul_cancel₀ hπ0, map_one, one_pow, one_pow]
  have h01 : ∀ x ∈ M0, d • x ∈ M1 := by
    rw [hM0]
    refine ngu_span_smul _ d M1 (fun j => ?_)
    have hpow : ∀ b : Fin (r + 1), d = c ^ (r - (b : ℕ)) * c ^ (b : ℕ) := fun b => by
      rw [hd, ← pow_add]; congr 1; have := b.2; omega
    rcases j with b | b
    · show d • P.A.f b ∈ M1
      rw [hpow b, mul_smul]; exact ngu_smulO M1 (M.L.O.pow_mem hcO _) (hgA b)
    · show d • P.B.f b ∈ M1
      rw [hpow b, mul_smul]; exact ngu_smulO M1 (M.L.O.pow_mem hcO _) (hgB b)
  have h10 : ∀ x ∈ M1, d • x ∈ M0 := by
    rw [hM1]
    refine ngu_span_smul _ d M0 (fun j => ?_)
    rw [hm1]
    rcases j with b | b
    · show d • (c ^ (b : ℕ) • P.A.f b) ∈ M0
      exact ngu_smulO M0 hdO (ngu_smulO M0 (M.L.O.pow_mem hcO _) (hM0 ▸ Submodule.subset_span ⟨Sum.inl b, rfl⟩))
    · show d • (c ^ (b : ℕ) • P.B.f b) ∈ M0
      exact ngu_smulO M0 hdO (ngu_smulO M0 (M.L.O.pow_mem hcO _) (hM0 ▸ Submodule.subset_span ⟨Sum.inr b, rfl⟩))
  have hfin : NguFinRep M (d * d) := by
    have e : d * d = algebraMap F E ((((π ^ k) ^ r * (π ^ k) ^ r : 𝒪[F])) : F) := by
      rw [hd, hc, Subring.coe_mul, Subring.coe_pow, Subring.coe_pow, map_mul, map_pow, map_pow]
    rw [e]
    refine ngu_finRep hOK _ ?_
    rw [Subring.coe_mul, Subring.coe_pow, Subring.coe_pow]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hπ0)) (pow_ne_zero _ (pow_ne_zero _ hπ0))
  have hK0 : P.K0 = P.St ⊓ Aut M0 := by
    ext κ
    rw [mem_normaliser_iff_stabiliser hX, Subgroup.mem_inf, ng_mem_Aut, hM0]
    rfl
  refine ngu_group P.K0 (P.St ⊓ Aut M1) s ⟨hs, ng_mem_Aut.2 hsM1⟩ ?_ ?_
  · rw [hK0, hM0]
    refine ngu_congr_index _ (d * d) hfin P.St _ (fun κ hκ hcg => ?_)
    rw [← hM0] at hκ hcg
    exact ⟨hκ.1, ng_mem_Aut.2 (ngu_stab hdd h10 h01 (ng_mem_Aut.1 hκ.2) hcg)⟩
  · rw [hK0]
    conv => enter [1, 2]; rw [hM1]
    refine ngu_congr_index _ (d * d) hfin P.St _ (fun κ hκ hcg => ?_)
    rw [← hM1] at hκ hcg
    exact ⟨hκ.1, ng_mem_Aut.2 (ngu_stab hdd h01 h10 (ng_mem_Aut.1 hκ.2) hcg)⟩

theorem NGMassOne_of_class (hOK : M.OK) (hP : P.PrimeTo) (hR : P.RelG (theta M)) (hC : NGOneClass P) : NGMassOne P :=
  NGMassOne_of hP hR.1 hC (NGBaseInt_of hP hR.2.2.2.2.2.1) (NGUnimod_of hOK hR.1)

theorem NGEqStep'_of_orbit0 (hOK : M.OK) (hP : P.PrimeTo) (hR : P.RelG (theta M)) (hO : NGOrbit0 P) (R : Reps P) :
    NGEqStep' P R := NGEqStep'_of_orbit hP hR hO (NGUnimod_of hOK hR.1) R

end Lat

section Left

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc ValuativeRel

def NGLeft1 (k r c : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) →
        (P.PrimeTo → NGOrbit0 P) ∧
        (¬ P.PrimeTo → ∀ (R : Reps P) (d0 : Datum P), Nonempty (NGCore1 k R d0 c C₀) ∧
            Nonempty (NGCore2 k R d0 c (fun t => ¬ BBne (H := H) t)) ∧ Nonempty (NGCore2 k R d0 c (fun _ => True)))

theorem NGLeft_of_left1 {k r c : ℕ} {C₀ : ℝ} (h : NGLeft1 k r c C₀) : NGLeft k r c C₀ := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H hrk P hP hex
  obtain ⟨h1, h2⟩ := h F E M hOK V H hrk P hP hex
  exact ⟨fun hp => ⟨h1 hp, NGUnimod_of hOK hP.1⟩, h2⟩

theorem nongeneric_local_of_remainder_one (k r c : ℕ) (C₀ C : ℝ) (hk : 4 * r + 7 ≤ k) (hC1 : (gainBoundConstant c C₀ : ℝ) ≤ C)
    (hC2 : (nongenericConstantNoGain c : ℝ) ≤ C) (h : NGLeft1 k r c C₀) : NonGenericAndKTwoTheorems.NonGenericLocalBound k r C :=
  nongeneric_local_of_remainder k r c C₀ C hk hC1 hC2 (NGLeft_of_left1 h)

theorem nongeneric_family_of_remainder_one {eps : ℝ} (Fm : FamP eps) (c : ℕ) (C₀ C : ℝ) (hC1 : (gainBoundConstant c C₀ : ℝ) ≤ C)
    (hC2 : (nongenericConstantNoGain c : ℝ) ≤ C)
    (h : ∀ x (i : Fm.Ix x), 4 * (Fm.D x i).R.rS + 7 ≤ (Fm.D x i).R.k → NGLeft1 (Fm.D x i).R.k (Fm.D x i).R.rS c C₀) :
    NonGenericAndKTwoTheorems.FamilyNonGenericLocalBound Fm C := fun x i hk => nongeneric_local_of_remainder_one _ _ c C₀ C hk hC1 hC2 (h x i hk)

end Left

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section NGe

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

theorem NGOrbit0_of (hP : P.PrimeTo) (hR : P.RelG (theta M)) : NGOrbit0 P := NGOrbit0_of_mat hR (NGMat_of hP hR)

theorem NGOneClass_of_primeTo (hP : P.PrimeTo) (hR : P.RelG (theta M)) : NGOneClass P := NGOneClass_of (NGOrbit0_of hP hR)

theorem NG_unique_of_primeTo (hP : P.PrimeTo) (hR : P.RelG (theta M)) {d : Datum P} {t₁ t₂ : Term V M r}
    (h₁ : IsTermOver P d t₁) (h₂ : IsTermOver P d t₂) : TRel P t₁ t₂ :=
  ng_unique hP hR.1 (NGOneClass_of_primeTo hP hR) h₁ h₂

theorem NGEqStep'_of_unimod (hP : P.PrimeTo) (hR : P.RelG (theta M)) (hU : NGUnimod P) (R : Reps P) : NGEqStep' P R :=
  NGEqStep'_of_orbit hP hR (NGOrbit0_of hP hR) hU R

end NGe

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section NGf

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

theorem NGEqStep'_holds (hOK : M.OK) (hP : P.PrimeTo) (hR : P.RelG (theta M)) (R : Reps P) : NGEqStep' P R :=
  NGEqStep'_of_orbit0 hOK hP hR (NGOrbit0_of hP hR) R

theorem NGAt_of_good (hOK : M.OK) (k : ℕ) (C : ℝ) (hP : P.PrimeTo) (hR : P.RelG (theta M)) : NGAt k P C :=
  NGAt_of_primeTo' hOK k C hP (fun R => NGEqStep'_holds hOK hP hR R)

end NGf

section Left2

def NGLeft2 (k r c : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) →
        ¬ P.PrimeTo → ∀ (R : Reps P) (d0 : Datum P), Nonempty (NGCore1 k R d0 c C₀) ∧
            Nonempty (NGCore2 k R d0 c (fun t => ¬ BBne (H := H) t)) ∧ Nonempty (NGCore2 k R d0 c (fun _ => True))

theorem NGLeft1_of_left2 {k r c : ℕ} {C₀ : ℝ} (h : NGLeft2 k r c C₀) : NGLeft1 k r c C₀ := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H hrk P hP hex
  exact ⟨fun hp => NGOrbit0_of hp hP, h F E M hOK V H hrk P hP hex⟩

theorem nongeneric_local_of_remainder_two (k r c : ℕ) (C₀ C : ℝ) (hk : 4 * r + 7 ≤ k) (hC1 : (gainBoundConstant c C₀ : ℝ) ≤ C)
    (hC2 : (nongenericConstantNoGain c : ℝ) ≤ C) (h : NGLeft2 k r c C₀) : NonGenericAndKTwoTheorems.NonGenericLocalBound k r C :=
  nongeneric_local_of_remainder_one k r c C₀ C hk hC1 hC2 (NGLeft1_of_left2 h)

theorem nongeneric_family_of_remainder_two {eps : ℝ} (Fm : FamP eps) (c : ℕ) (C₀ C : ℝ) (hC1 : (gainBoundConstant c C₀ : ℝ) ≤ C)
    (hC2 : (nongenericConstantNoGain c : ℝ) ≤ C)
    (h : ∀ x (i : Fm.Ix x), 4 * (Fm.D x i).R.rS + 7 ≤ (Fm.D x i).R.k → NGLeft2 (Fm.D x i).R.k (Fm.D x i).R.rS c C₀) :
    NonGenericAndKTwoTheorems.FamilyNonGenericLocalBound Fm C := fun x i hk => nongeneric_local_of_remainder_two _ _ c C₀ C hk hC1 hC2 (h x i hk)

end Left2

end Formalism.MainNotions.KappaEndpoints

end
