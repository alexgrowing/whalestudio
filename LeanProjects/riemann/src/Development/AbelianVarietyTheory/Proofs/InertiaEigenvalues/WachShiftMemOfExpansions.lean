import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.RToolModDStab
import Formalism.SharpRestriction.LevelLetterCocycles.SemisimpleLetterIffForallMem
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPrimOfGood
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusIterateUniformizerUnitProducts
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltLaurentProdPreserves

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

section Core

open TensorProduct Formalism.MainNotions.RamifiedCoefficientChains.Sh Formalism.MainNotions.N.Pv.LocalLengthBound.Ser Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt
open Formalism.MainNotions.CrystallineLiftingInputs (DL)
open Formalism.MainNotions.LiftingTheory (qp)
open Formalism.MainNotions.WachCoordinates (FilLev)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem wachExp_diag_shift_iff {M : Type} [AddCommGroup M] [Module LL M] {Fl : ℤ → Submodule LL M}
    (hF : Antitone Fl) {m : ℤ} {d : ℤ → M} (hd : ∀ k < m, d k = 0) (u : PowerSeries LL)
    (hu : IsUnit u) (y : ℕ) :
    (∀ k, conv ((u * PowerSeries.X) ^ y) d k ∈ Fl (-k)) ↔ ∀ k, d k ∈ Fl (-k - y) := by
  have hd' : LB m d := hd
  have hu0 : PowerSeries.constantCoeff (u ^ y) ≠ 0 :=
    ((hu.pow y).map PowerSeries.constantCoeff).ne_zero
  have e : conv ((u * PowerSeries.X) ^ y) d = fun k => smulS (u ^ y) d (k - y) := by
    show smulS ((u * PowerSeries.X) ^ y) d = _
    rw [mul_comm, mul_pow, smulS_mul hd', smulS_X_pow (LB_smulS hd' _)]
  rw [e]
  constructor
  · intro h k
    have h1 : Dg Fl (-(y : ℤ)) (smulS (u ^ y) d) := fun j => by
      have := h (j + y)
      simp only [add_sub_cancel_right] at this
      rwa [show -(y : ℤ) - j = -(j + y) by ring]
    have h2 := Dg_smulS hF (LB_smulS hd' _) h1 (u ^ y)⁻¹ k
    rw [smulS_inv hd' _ hu0] at h2
    rwa [show -k - (y : ℤ) = -(y : ℤ) - k by ring]
  · intro h k
    have h1 : Dg Fl (-(y : ℤ)) d := fun j => by
      rw [show -(y : ℤ) - j = -j - y by ring]; exact h j
    have h2 := Dg_smulS hF hd' h1 (u ^ y) (k - y)
    rwa [show -(y : ℤ) - (k - y) = -k by ring] at h2

theorem wachExp_mem_iff (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hRg : ExpRing W)
    (hRu : ExpRules W) (hCr : ExpCrit W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR) (hx : DL W T i x) (hd : IsExp W T i ζ x d)
    (Y : ℕ) (hY : qp W ^ Y • x ∈ W.N T) (y : ℕ) :
    qp W ^ y • x ∈ W.N T ↔ ∀ k, d k ∈ FilLev W T i 0 (-k - y) := by
  have hK : Module.finrank K₀ K = 1 := Formalism.MainNotions.UnusedSlot80.SatW.finrank_one_of_bij' hA.1
  obtain ⟨h9r, -⟩ := (h9 T hT hA.2.1 hA.2.2).2.2 hK
  have hR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W h9r
  have hqΔ := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hR.πΔ
  have hDL : DL W T i (qp W ^ y • x) := by
    refine ⟨by rw [smul_comm, hx.1], fun δ hδ => ?_⟩
    rw [γD_smul', map_pow, hqΔ δ hδ, hx.2 δ hδ]
  obtain ⟨⟨u, hu, hq⟩, -, -⟩ := hRg hA i ζ hζ
  have hE := (hRu hA T hT i ζ hζ).2.2.2.2.1 (qp W ^ y) x d hd
  have hN : qp W ^ Y • (qp W ^ y • x) ∈ W.N T := by
    rw [smul_comm]; exact (W.N T).smul_mem _ hY
  rw [(hCr hA T hT i ζ hζ _ _ hDL hE).1 ⟨Y, hN⟩, map_pow, hq]
  obtain ⟨m, hm⟩ := hd.1
  exact wachExp_diag_shift_iff (Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0) hm u hu y

theorem wachShift_mem_of_exp [NeZero n] (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRg : ExpRing W) (hRu : ExpRules W) (hCr : ExpCrit W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hp : (PD.p : LL) ≠ 0) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (y' Y : ℕ) (cO : ℤ → O)
    (hc : ∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O))
    (xs : List ℤ)
    (hxs : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i → IsJumpV PD T.ρ τ a →
      y' < j → j ≤ Y → a + (j : ℤ) ∈ xs)
    (seq : ℕ → W.DD T) (h0 : DL W T i (seq 0)) (h0N : qp W ^ Y • seq 0 ∈ W.N T)
    (hrec : ∀ k < xs.length, W.π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) =
      W.γD T W.gam (seq k) - seq k) :
    DL W T i (seq xs.length) ∧ qp W ^ y' • seq xs.length ∈ W.N T := by
  classical
  have hU := Formalism.MainNotions.UnusedSlot35.DssRec.π₀_unit W h9 hA T hT
  have hDS := rToolMod_dStab W h9
  have hQ : ∀ k ≤ xs.length, QLattice W T i Y (seq k) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨h0, h0N⟩
    | succ k ih =>
      intro hk
      have hk' : k < xs.length := hk
      have e : seq (k + 1) = derivationOnWachModule W T (seq k) + (-cO (xs.getD k 0)) • seq k := by
        have h1 : seq (k + 1) + cO (xs.getD k 0) • seq k = derivationOnWachModule W T (seq k) :=
          Formalism.MainNotions.UnusedSlot35.DssRec.smul_inj W.π₀ hU (by rw [hrec k hk', uniformizer_smul_derivation W T hU]; rfl)
        rw [← h1, neg_smul, add_neg_cancel_right]
      rw [e]
      exact qLattice_add W T (qLattice_derivation W T hDS hA hT i Y (ih hk'.le))
        (qLattice_smul W T _ (ih hk'.le))
  refine ⟨(hQ _ le_rfl).1, ?_⟩
  obtain ⟨⟨u, hu, hq⟩, hπ0, -⟩ := hRg hA i ζ hζ
  obtain ⟨hex, -, hadd, hsO, hsA, hγ, -⟩ := hRu hA T hT i ζ hζ
  have hqne : W.lev i ζ (qp W ^ Y) ≠ 0 := by
    rw [map_pow, hq]
    exact pow_ne_zero _ (mul_ne_zero hu.ne_zero PowerSeries.X_ne_zero)
  have hf : ∀ k : ℕ, ∃ d : ℤ → T.V ⊗[Qp] BdR, (∃ m : ℤ, ∀ j < m, d j = 0) ∧
      (k ≤ xs.length → IsExp W T i ζ (seq k) d) := by
    intro k
    by_cases hk : k ≤ xs.length
    · obtain ⟨d, hd, -⟩ := hex (seq k) _ (hQ k hk).2 hqne
      exact ⟨d, hd.1, fun _ => hd⟩
    · exact ⟨0, ⟨0, fun _ _ => rfl⟩, fun h => absurd h hk⟩
  choose f hfb hfe using hf
  rw [wachExp_mem_iff W h9 hRg hRu hCr hA T hT i ζ hζ _ _ (hQ _ le_rfl).1 (hfe _ le_rfl) Y
    (hQ _ le_rfl).2 y']
  have hf0 := (wachExp_mem_iff W h9 hRg hRu hCr hA T hT i ζ hζ _ _ h0 (hfe 0 (Nat.zero_le _)) Y
    h0N Y).1 h0N
  let uL : LLˣ := Units.map (algebraMap O LL : O →* LL) (W.χΓ W.gam)
  refine filtLaurent_shift_line LL _ (fun a => FilLev W T i 0 a)
    (Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0) uL (W.lev i ζ W.π₀) (fun x => algebraMap O LL (cO x))
    (by rw [hπ0]; exact neg_ne_zero.2 hp) (fun x => ?_) y' Y xs (fun a j ha hj hj' => ?_) f hfb
    (fun m hm k => ?_) hf0
  · have h1 := congrArg (algebraMap O LL) (hc x)
    rw [map_mul, map_natCast, map_sub, map_one] at h1
    have h2 : ((uL ^ (-x) : LLˣ) : LL) = algebraMap O LL (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) := by
      rw [← map_zpow]; rfl
    rw [hπ0, h2]
    linear_combination -h1
  · let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hA.1
    let τ : K →ₐ[Qp] LL := (W.emb i).comp e.symm.toAlgHom
    have hτ : Formalism.MainNotions.LiftingTheory.Over W τ i := by
      apply AlgHom.ext
      intro z
      show W.emb i (e.symm (e z)) = W.emb i z
      rw [e.symm_apply_apply]
    have hF : ∀ b : ℤ, FildR PD T.ρ τ b = FilLev W T i 0 b := by
      intro b
      rw [((hD hA.1 T.V T.ρ hT).2 τ).2.2 b, show τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i from hτ]
      unfold FilLev
      simp only [Nat.cast_zero, sub_zero, pow_zero, Module.End.one_eq_id, Submodule.map_id]
    refine hxs τ a j hτ ?_ hj hj'
    unfold IsJumpV
    rw [hF, hF]
    exact ha
  · have e1 := hfe m hm.le
    have e2 := hfe (m + 1) hm
    have hL := hsA W.π₀ _ _ (hadd _ _ _ _ e2 (hsO (cO (xs.getD m 0)) _ _ e1))
    have hR := hadd _ _ _ _ (hγ _ _ e1) (hsO (-1) _ _ e1)
    have ex : W.γ T (seq m) + (-1 : O) • seq m =
        W.π₀ • (seq (m + 1) + cO (xs.getD m 0) • seq m) := by
      rw [hrec m hm, neg_one_smul, ← sub_eq_add_neg]; rfl
    rw [ex] at hR
    have hN : qp W ^ Y • (W.π₀ • (seq (m + 1) + cO (xs.getD m 0) • seq m)) ∈ W.N T := by
      rw [smul_comm]
      exact (W.N T).smul_mem _
        (qLattice_add W T (hQ (m + 1) hm) (qLattice_smul W T _ (hQ m hm.le))).2
    have h3 := congrFun ((hex _ _ hN hqne).unique hL hR) k
    have h2 : ((uL ^ k : LLˣ) : LL) = (algebraMap O LL (W.χΓ W.gam : O)) ^ k := by
      rw [Units.val_zpow_eq_zpow_val]; rfl
    rw [h2, sub_smul, one_smul]
    refine Eq.trans ?_ (h3.trans ?_)
    · rfl
    · simp [sub_eq_add_neg]

end Core

theorem wachShift_mem_of_expansions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc), ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (y' Y : ℕ) (cO : ℤ → ↥(OL LL)), (∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - (((((HW l).W K 1 LL hA.2.2).χΓ ((HW l).W K 1 LL hA.2.2).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) → ∀ xs : List ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hA.2.2) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ((HW l).W K 1 LL hA.2.2).DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ Y • seq 0 ∈ ((HW l).W K 1 LL hA.2.2).N T → (∀ k < xs.length, ((HW l).W K 1 LL hA.2.2).π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) = ((HW l).W K 1 LL hA.2.2).γD T ((HW l).W K 1 LL hA.2.2).gam (seq k) - seq k) → Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ y' • seq xs.length ∈ ((HW l).W K 1 LL hA.2.2).N T := by
  intro D HW l _ K LL hA h9 hRg hRu hCr hD T hT i y' Y cO hc xs hxs seq h0 h0N hrec
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := Formalism.MainNotions.UnusedSlot80.exists_prim_of_good D hA.2.2
  refine wachShift_mem_of_exp _ h9 hRg hRu hCr hD
    (Formalism.MainNotions.UnusedSlot80.caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1) ?_ ζ (by rw [hp]; exact hζ) T hT i y' Y
    cO (fun x => by rw [hp]; exact hc x) xs hxs seq h0 h0N hrec
  rw [hp]
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

end GlobalTheory
