import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfDict
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem framepf_hyp_cc_subst {O : Type} [CommRing O] (p F : PowerSeries O)
    (hp : PowerSeries.constantCoeff p = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst p F) = PowerSeries.constantCoeff F := by
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hp
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const F]
  rw [PowerSeries.subst_add hS, PowerSeries.subst_mul hS, PowerSeries.subst_X hS, PowerSeries.subst_C,
    map_add, map_mul, hp, zero_mul, zero_add]
  exact PowerSeries.constantCoeff_C _

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem framepf_hyp_bas (π'₀ : LetA O n) (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π'₀) : Nonempty (FramepfBas W T) := by
  obtain ⟨⟨r, b, hb, huniq, hdel⟩, -⟩ := hm
  exact ⟨⟨r, b, hb, huniq, fun x hx => hdel x hx⟩⟩

theorem framepf_hyp_local (e s' : ℕ) (hs : 1 ≤ s') (π' : LetA O n) (E : ZMod n → Polynomial O)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (π'₀ : LetA O n) (w₀ : (LetA O n)ˣ)
    (hw₀ : π'₀ = (w₀ : LetA O n) * letπ ^ s') (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π'₀) (c : ZMod n) :
    (∀ j, PowerSeries.constantCoeff (π' j) = 0) ∧ (∀ δ ∈ W.DelF, W.γA δ π' = π') ∧
    (∀ a ∈ W.AΔ, ∃! f : ZMod n → PowerSeries O, ∀ j, a j = PowerSeries.subst (π' j) (f j)) ∧
    (∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0) ∧
    IsUnit (algebraMap (LetA O n) W.EE π') ∧
    (∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) ∧
    ∃ Fs : PowerSeries O, W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs) ∧
      PowerSeries.constantCoeff Fs = ((W.χΓ W.gam : Oˣ) : O) ^ s' := by
  obtain ⟨f, t, hf, -, hEE, hπΔ, hγN⟩ := exists_gam_pi_factor W T e s' hs π' E hR π'₀ w₀ hw₀ hm.2
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hfΔ := gradNPf_fΔ W s' w π' f hw hπΔ hf
  obtain ⟨Fs, hFs, -⟩ := hR.2.1 f hfΔ
  have hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0 := by
    intro j
    have : π' j = (w : LetA O n) j * PowerSeries.X ^ s' := by rw [hw]; rfl
    rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 (c - 1))
  have hγc : W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs (c - 1)) := by
    have h : (W.γA W.gam π') (c - 1) = (π' * f) (c - 1) := congrFun hf (c - 1)
    rw [PowerSeries.subst_mul hS, PowerSeries.subst_X hS, ← hFs (c - 1)]
    exact h
  have hcc : PowerSeries.constantCoeff (Fs (c - 1)) = ((W.χΓ W.gam : Oˣ) : O) ^ s' := by
    rw [← framepf_hyp_cc_subst (π' (c - 1)) (Fs (c - 1)) (hπ0 (c - 1)), ← hFs (c - 1)]
    exact gradNPf_cc_f W s' w π' f hw hf (c - 1)
  exact ⟨hπ0, hπΔ, fun a ha => hR.2.1 a ha, fun δ _ => (W.γ₀_X δ).1, hEE, hγN, Fs (c - 1), hγc, hcc⟩

end Local

set_option maxHeartbeats 1000000 in

theorem frame_uniformiser_unit_multiple (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys ((D.loc l).PD K) T.ρ) :
    ∃ (π'₀ : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (w₀ : (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))ˣ),
      π'₀ = (w₀ : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) * letπ ^ sK l K ∧
        Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters ((HW l).W K 1 LL hG) T π'₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := h1 l K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, hr₀, hm₀⟩, -⟩ := h9W T hT hs1 hp
  rw [hpl] at hr₀
  obtain ⟨w₀, hw₀⟩ := hr₀.2.2.1
  exact ⟨π'₀, w₀, hw₀, hm₀⟩

theorem ramification_quotient_pos (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL) :
    1 ≤ sK l K := by
  have hd : eK K ∣ l - 1 := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl1 : 0 < l - 1 := by have := hpf.out.two_le; omega
  have he0 : 0 < eK K := Nat.pos_of_dvd_of_pos hd hl1
  exact (Nat.one_le_div_iff he0).mpr (Nat.le_of_dvd hl1 hd)

set_option maxHeartbeats 1000000 in

theorem framepf_hyp_arith (D : D7) (HW : HWOf D.loc) (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (h' : ℕ) (hs : 1 ≤ sK l K) :
    (∀ y : ℕ, 1 ≤ y → (((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) ^ sK l K) ^ y ≠ 1) ∧
      ∃ aσ : ↥(OL LL), (l : ↥(OL LL)) ^ sigA l (sK l K) h' =
        aσ * ∏ y ∈ Finset.Ico 1 (MK l K h'), ((((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) ^ sK l K) ^ y - 1) := by
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hlv : (D.loc l).v LL (l : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hlO : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL))) = 1 := by
    rw [map_natCast]
    exact hlv
  have hxv : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL hG).gam_gen
    rw [hs1, Nat.cast_one] at this
    exact this
  obtain ⟨u, hu, hxu⟩ := gradNPf_sub_one ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv
    (l : ↥(OL LL)) _ hlO hxv
  have hsl : ¬ l ∣ sK l K := by
    apply Nat.not_dvd_of_pos_of_lt hs
    have h2 := hpf.out.two_le
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hprod := fun N => gradNPf_prod ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hl hlv _
    u hu hxu (sK l K) (by omega) hsl N
  refine ⟨?_, ?_⟩
  · intro y hy h
    obtain ⟨a, ha⟩ := hprod y
    rw [Finset.prod_eq_zero (i := y) (Finset.mem_Ico.2 ⟨hy, by omega⟩) (by rw [h, sub_self]),
      mul_zero] at ha
    have h2 := congrArg (algebraMap ↥(OL LL) ↥LL.1) ha
    rw [map_pow, map_natCast, map_zero] at h2
    have h3 : (l : ↥LL.1) = 0 := (pow_eq_zero_iff (by omega)).mp h2
    rw [h3, AddValuation.map_zero] at hlv
    exact absurd hlv (by simp)
  · obtain ⟨a, ha⟩ := hprod (MK l K h' - 1)
    refine ⟨a, ?_⟩
    have hσ : sigA l (sK l K) h' = MK l K h' - 1 + padicValNat l (MK l K h' - 1).factorial := rfl
    have hI : Finset.Ico 1 (MK l K h' - 1 + 1) = Finset.Ico 1 (MK l K h') := by
      rcases Nat.eq_zero_or_pos (MK l K h') with h0 | h0
      · rw [h0]; simp
      · congr 1; omega
    rw [hσ, ← hI]
    exact ha

set_option maxHeartbeats 1000000 in

theorem framepf_hyps (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (h' : ℕ) :
    Nonempty (FramepfBas ((HW l).W K 1 LL hG) T) ∧
    (∀ j, PowerSeries.constantCoeff (π' j) = 0) ∧
    (∀ δ ∈ ((HW l).W K 1 LL hG).DelF, ((HW l).W K 1 LL hG).γA δ π' = π') ∧
    (∀ a ∈ ((HW l).W K 1 LL hG).AΔ, ∃! f : ZMod (finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL),
      ∀ j, a j = PowerSeries.subst (π' j) (f j)) ∧
    (∀ δ ∈ ((HW l).W K 1 LL hG).DelF,
      PowerSeries.constantCoeff (((HW l).W K 1 LL hG).γ₀ δ PowerSeries.X) = 0) ∧
    IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE π') ∧
    (∀ y ∈ ((HW l).W K 1 LL hG).NΔ T, ∃ d ∈ ((HW l).W K 1 LL hG).N T,
      ((HW l).W K 1 LL hG).γD T ((HW l).W K 1 LL hG).gam y - y = π' • d) ∧
    ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam ∧
    ∃ Fs : PowerSeries ↥(OL LL),
      ((HW l).W K 1 LL hG).γ₀ ((HW l).W K 1 LL hG).gam (π' (c - 1)) =
        PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs) ∧
      PowerSeries.constantCoeff Fs =
        ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) ^ sK l K ∧
      (∀ y : ℕ, 1 ≤ y →
        (((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) ^ sK l K) ^ y ≠ 1) ∧
      ∃ aσ : ↥(OL LL), (l : ↥(OL LL)) ^ sigA l (sK l K) h' =
        aσ * ∏ y ∈ Finset.Ico 1 (MK l K h'),
          ((((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) ^ sK l K) ^ y - 1) := by
  obtain ⟨π'₀, w₀, hw₀, hm₀⟩ := frame_uniformiser_unit_multiple D HW F Cm h1 l hl K LL hG T hT
  have hs := ramification_quotient_pos l hl K LL hG
  obtain ⟨hπ0, hπΔ, hsub, hX0, hEE, hγN, Fs, hγc, hcc⟩ :=
    framepf_hyp_local _ T (eK K) (sK l K) hs π' E hR π'₀ w₀ hw₀ hm₀ c
  obtain ⟨hne, hpr⟩ := framepf_hyp_arith D HW l hl K LL hG h' hs
  exact ⟨framepf_hyp_bas _ T π'₀ hm₀, hπ0, hπΔ, hsub, hX0, hEE, hγN,
    ((HW l).W K 1 LL hG).gamK_eq_one ((HW l).W_s K 1 LL hG) (by rw [(D.loc l).PD_p K]; exact hl),
    Fs, hγc, hcc, hne, hpr⟩

end Formalism.MainNotions.N.Ln34

end
