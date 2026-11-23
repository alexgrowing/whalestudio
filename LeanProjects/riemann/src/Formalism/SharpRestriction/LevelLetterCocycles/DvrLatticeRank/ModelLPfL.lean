import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfJ
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfG
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfHyp
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct Formalism.MainNotions.N.Ln34.ModelFPf

theorem rec_WD (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    MLF.WD ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' c := by
  intro τ ζ hpt m m' a y hy b z hz h
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hprim : IsPrimitiveRoot ζ l := framepf_pt_prim D HW hG c ζ τ hpt
  have hprim' : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by rw [hp]; exact hprim
  haveI : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  obtain ⟨-, -, -, h4W, -⟩ := hA.1 l K 1 LL hG
  have hone : ∃ j : ℕ, IsPrimitiveRoot (1 : ↥LL.1) (((D.loc l).PD K).p ^ j) := ⟨0, by simp⟩
  have hπ1 : PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev (c - 1) 1 letπ) = 0 := by
    rw [CrystallineExponents.cc_lev_pi ((HW l).W K 1 LL hG) (c - 1) 1 hone, sub_self]
  have hX : ((HW l).W K 1 LL hG).X = letπ := by simp [LocWach.X, hs]
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hπ : PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev (c - 1) 1 π') = 0 := by
    obtain ⟨w, hw⟩ := hr.2.2.1
    rw [hw, map_mul, map_pow, map_mul, map_pow, hπ1, zero_pow (by omega), mul_zero]
  have hQ := framepf_Q_at ((HW l).W K 1 LL hG) hs c ζ hprim'
  have hP : MLA.PtHyp (W := (HW l).W K 1 LL hG) T c ζ := by
    refine ⟨hT, ⟨1, by rw [pow_one]; exact hprim'⟩, hprim'.pow_eq_one, hQ.1, hQ.2, ?_, ?_⟩
    · intro x k hk
      have h4 := ((h4W T hT).1 (c - 1) 1 ⟨0, by simp⟩ (by rw [hX]; exact hπ1)).1 x k
      exact h4.2 hk
    · intro x hx
      exact ((HW l).W K 1 LL hG).N_φ T x hx
  exact MLA.expS_wd ((Cm l).C K 1 LL hG).tie T hinj hP π' hπ a y hy b z hz h

set_option maxHeartbeats 1000000 in
theorem exists_mul_gamma_Eat_pow_eq_Eat_pow (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) :
    ∃ u₀ ∈ ((HW l).W K 1 LL hG).AΔ, u₀ * ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gamK
      (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h' := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hr
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply]
    exact congrArg (fun t => Polynomial.aeval t (E i)) (congrFun (hπΔ δ hδ) i)
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  refine ⟨((hu.unit⁻¹ : (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))ˣ) : LetA _ _) ^ h', Subalgebra.pow_mem _ hu'Δ h', ?_⟩
  rw [hgam, map_pow, hγ, mul_pow, ← mul_assoc, ← mul_pow, hu.val_inv_mul, one_pow, one_mul]

set_option maxHeartbeats 1000000 in
theorem rec_lev (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) (a : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) :
    ((HW l).W K 1 LL hG).lev c ζ (((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gamK a) =
      PowerSeries.rescale (algebraMap ↥(OL LL) ↥LL.1
        ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL)))
        (((HW l).W K 1 LL hG).lev c ζ a) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hprim : IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ 1) := by
    rw [pow_one, hp]; exact framepf_pt_prim D HW hG c ζ τ hpt
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL)) - ((1 : ℕ) : ↥LL.1)) := by
    rw [hgam, Nat.cast_one (R := ↥LL.1), ((HW l).W K 1 LL hG).gam_gen, hs]
  have := ((Cm l).C K 1 LL hG).tie.lev_Γ ((HW l).W K 1 LL hG).gamK c ζ ζ 1 1 hprim hv (by rw [pow_one]) a
  exact this

set_option maxHeartbeats 1000000 in
theorem rec_u (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) :
    algebraMap ↥(OL LL) ↥LL.1 ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) :
      ↥(OL LL)) ≠ 0 ∧
    ∀ i : ℤ, i ≠ 0 → (algebraMap ↥(OL LL) ↥LL.1 ((((HW l).W K 1 LL hG).χΓ
      ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL))) ^ i ≠ 1 := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have har := (framepf_hyp_arith D HW l hl K LL hG 1 hsK).1
  rw [hgam]
  set χ := ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) with hχ
  have hnat : ∀ k : ℕ, 1 ≤ k → (algebraMap ↥(OL LL) ↥LL.1 χ) ^ k ≠ 1 := by
    intro k hk h1
    have h2 : χ ^ k = 1 := by
      apply Subtype.val_injective
      have := h1
      rw [← map_pow] at this
      simpa using this
    apply har k hk
    rw [← pow_mul, mul_comm, pow_mul, h2, one_pow]
  refine ⟨((Units.isUnit _).map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero, fun i hi h1 => ?_⟩
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · apply hnat (-i).toNat (by omega)
    have : (algebraMap ↥(OL LL) ↥LL.1 χ) ^ (-i) = 1 := by rw [zpow_neg, h1, inv_one]
    rwa [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  · apply hnat i.toNat (by omega)
    rwa [← zpow_natCast, Int.toNat_of_nonneg (by omega)]

end Formalism.MainNotions.N.Ln34.MLL

end
