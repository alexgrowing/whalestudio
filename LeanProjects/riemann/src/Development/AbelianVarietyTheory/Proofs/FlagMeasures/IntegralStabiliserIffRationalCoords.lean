import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFrameStabilizerActsUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesPairingStabilizerBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInvPowDifferentIffLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemStabilizerSpanIffUnitriangularIntegralStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StabIntCoord

theorem mem_maxUnramifiedSubfield_conj_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : Frames L r k)
    (x : S.GLV) (hx : x ∈ S.St) (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : IsUni s) (hs' : IsUni s')
    (h1 : ∀ j, x (S.f j) = ∑ i, s i j • S.f i) (h2 : ∀ j, x (S.f' j) = ∑ i, s' i j • S.f' i) :
    x ∈ S.K0 ↔ IsIntM L s' := by
  have heq := ((GlobalTheory.HL.FrameStab.stab_eq L r k S).2 s s' hs hs').2 ⟨x, hx, h1, h2⟩
  have hint := ((GlobalTheory.HL.BlockStab.stabiliser_blockDiag L r k S).1 s s' hs hs' heq).2
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  have hl1 : LinearIndependent E S.f := hli.comp Sum.inl Sum.inl_injective
  have hl2 : LinearIndependent E S.f' := hli.comp Sum.inr Sum.inr_injective
  have e1 := GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral L S.f hl1 x s hs h1
  have e2 := GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral L S.f' hl2 x s' hs' h2
  unfold Frames.K0
  simp only [Subgroup.mem_inf]
  rw [e1, e2, hint]
  tauto

end GlobalTheory.HL.StabIntCoord

namespace GlobalTheory.HL.StabIntCoord

open IsDedekindDomain

theorem loc_act {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : Places F E sig) {n r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (c : ((A.loc p).Fp)ˣ)
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E)) (g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))
    (hE : A.Ext p x g') (v : Fin (r + 1) → Fin n → E) (vl : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (hv : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ))) • vl a = A.bc p (v a))
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hM : ∀ b : Fin (r + 1), x (v b) = ∑ a, M a b • v a) (b : Fin (r + 1)) :
    g' (vl b) = ∑ a : Fin (r + 1), (algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ)) /
      (c : (A.loc p).Fp) ^ (r - (b : ℕ))) * (A.loc p).ιE (M a b)) • vl a := by
  have hc : ∀ m : ℕ, ((c : (A.loc p).Fp) ^ m) ≠ 0 := fun m => pow_ne_zero _ c.ne_zero
  have hvl : ∀ a : Fin (r + 1), vl a = algebraMap (A.loc p).Fp (A.loc p).Ep (((c : (A.loc p).Fp) ^ (r - (a : ℕ)))⁻¹) • A.bc p (v a) := by
    intro a
    rw [← hv a, smul_smul, ← map_mul, inv_mul_cancel₀ (hc _), map_one, one_smul]
  have hbc : ∀ (l : Fin (r + 1) → E) (w : Fin (r + 1) → Fin n → E),
      A.bc p (∑ a, l a • w a) = ∑ a, (A.loc p).ιE (l a) • A.bc p (w a) := by
    intro l w
    funext i
    simp [Places.bc, Finset.sum_apply, map_sum, smul_eq_mul, map_mul]
  rw [hvl b, map_smul, hE, hM b, hbc, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hv a, smul_smul, smul_smul]
  congr 1
  rw [div_eq_mul_inv, map_mul]
  ring

end GlobalTheory.HL.StabIntCoord

namespace GlobalTheory.HL.StabIntCoord

set_option maxHeartbeats 1000000 in

theorem integralStabiliser_iff_rational_coords_alt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ x ∈ G.St, ∀ B : Formalism.L2.SG.PairVal.MatR D, (∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) → (x ∈ G.K0 ↔ ∀ a b : Fin (D.R.rS + 1), a < b → B a b ∈ ((ddS D ^ (-((b : ℤ) - (a : ℤ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))) := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ _ G c x hx B hB
  obtain ⟨s, s', hs, hs', hsf, hsf'⟩ := GlobalTheory.T.globalFrameStabilizer_acts_unitriangular _ _ _ G x hx
  have key : ∀ p : PlF D, (∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g') ↔
      ∀ a b : Fin (D.R.rS + 1), a < b → (D.s.atP p).ιE (B a b) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O := by
    intro p
    haveI := (D.s.atP p).lf
    haveI := (D.s.atP p).char0
    haveI : IsNonarchimedeanLocalField ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp := (D.s.atP p).lf
    haveI : CharZero ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp := (D.s.atP p).char0
    obtain ⟨xp, hxp, hExt⟩ := hx p
    have huniq := ((GlobalTheory.HL.RatExt.rational_extend (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ p).2.2.1 x)
    have hK : (∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g') ↔ xp ∈ (G.S p).K0 := by
      constructor
      · rintro ⟨g', hg', hgE⟩
        rwa [huniq.unique hExt hgE]
      · intro h; exact ⟨xp, h, hExt⟩
    rw [hK]
    have h1 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f (G.S p).f (G.f_eq p) s hsf
    have h2 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f' (G.S p).f' (G.f'_eq p) s' hsf'
    have h3 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f' (G.S p).f' (G.f'_eq p) B hB
    have hceq : algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (G.c p).val = algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E) := c.c_eq p
    show _ ↔ ∀ a b : Fin (D.R.rS + 1), a < b → ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) * (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O
    have hcne : ∀ m : ℕ, ((G.c p).val ^ m) ≠ 0 := fun m => pow_ne_zero _ (G.c p).ne_zero
    have huni : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUni M →
        IsUni (fun a b : Fin (D.R.rS + 1) => algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
          ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ))) *
            ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (M a b)) := by
      intro M hM
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · simp [hM.1 i j hij]
      · simp [hM.2 i, div_self (hcne _)]
    rw [mem_maxUnramifiedSubfield_conj_iff _ _ _ (G.S p) xp hxp _ _ (huni s hs) (huni s' hs') h1 h2]
    have hli : LinearIndependent ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (G.S p).f' :=
      (GlobalTheory.FrameBasic.main _ _ _ (G.S p)).1.comp Sum.inr Sum.inr_injective
    have hsB : ∀ a b, ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (s' a b) = ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) := by
      intro a b
      have e := (h2 b).symm.trans (h3 b)
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
      simp_rw [← sub_smul] at e
      have h0 := Fintype.linearIndependent_iff.1 hli _ e a
      have hu : IsUnit (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
          ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ)))) :=
        (isUnit_iff_ne_zero.2 (div_ne_zero (hcne _) (hcne _))).map _
      rw [← mul_sub, hu.mul_right_eq_zero, sub_eq_zero] at h0
      exact h0
    have hent : ∀ a b : Fin (D.R.rS + 1), a < b → algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
        ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ))) *
          ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (s' a b) = ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) * (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
            ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) := by
      intro a b hab
      have hab' : (a : ℕ) < b := hab
      have hb := b.isLt
      rw [show D.R.rS - (a : ℕ) = (D.R.rS - b) + ((b : ℕ) - a) by omega, pow_add,
        mul_div_cancel_left₀ _ (hcne _), map_pow, hceq, hsB, mul_comm]
    constructor
    · intro h a b hab
      rw [← hent a b hab]
      exact h a b
    · intro h a b
      rcases lt_trichotomy a b with hab | rfl | hab
      · beta_reduce
        rw [hent a b hab]
        exact h a b hab
      · show _ ∈ _
        simp [hs'.2 a, div_self (hcne _)]
      · show _ ∈ _
        simp [hs'.1 a b hab]
  have hK0 : x ∈ G.K0 ↔ ∀ p, ∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g' := Iff.rfl
  rw [hK0, forall_congr' key]
  have hI : ∀ a b : Fin (D.R.rS + 1), a < b → (B a b ∈ ((ddS D ^ (-((b : ℤ) - (a : ℤ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔
      ∀ p : PlF D, (D.s.atP p).ιE (B a b) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O) := by
    intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hb := b.isLt
    have hn : (b : ℕ) - (a : ℕ) ≤ D.R.rS := by omega
    have e : (-((b : ℤ) - (a : ℤ))) = -((((b : ℕ) - (a : ℕ) : ℕ)) : ℤ) := by
      rw [Nat.cast_sub hab'.le]
    rw [e]
    exact GlobalTheory.T.mem_inv_pow_different_iff_local D ⟨Y.δ, Y.M, Y.agree⟩ _ hn (B a b)
  constructor
  · intro h a b hab
    exact (hI a b hab).2 fun p => h p a b hab
  · intro h p a b hab
    exact (hI a b hab).1 (h a b hab) p

end GlobalTheory.HL.StabIntCoord
