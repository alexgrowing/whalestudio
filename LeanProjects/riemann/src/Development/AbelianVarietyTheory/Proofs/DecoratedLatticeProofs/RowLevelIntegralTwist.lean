import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesOverNormAndCoverWithConjugates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteMatrixIotaEqFinitePart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.CongFlag

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence
open scoped Matrix

theorem core (I : AutInst) (g : ℕ) {r : ℕ} (e0 : Fin r → VA I) (z0 : VA I) (hz0 : z0 ∈ I.Lf)
    (hzz : ZMod' I g (hA I z0 z0 + 1)) (hze : ∀ a, ZMod' I g (hA I (e0 a) z0))
    (x : I.Gf) (hxK : x ∈ I.Kset) (hxz : InMod I g (Set.range e0) ((I.fmat x - 1) *ᵥ z0))
    (v v' : VA I) (hv : InAt I g g (v - z0)) (hv' : InAt I g g (v' - z0))
    (ε c c₂ : I.E ⊗[I.F] Af I.F) (hε : ε ∈ IntAf I.F I.E) (hc : c ∈ IntAf I.F I.E) (hc₂ : c₂ ∈ IntAf I.F I.E)
    (hyp : ε • (c • (I.fmat x *ᵥ v')) = ε • (c₂ • v)) :
    ∃ N : ℕ, N.Coprime g ∧ ZMod' I g (ε * (c - c₂) * (N : I.E ⊗[I.F] Af I.F)) := by
  obtain ⟨n, hn, hnv⟩ := hv
  obtain ⟨n', hn', hnv'⟩ := hv'
  refine ⟨n * n', Nat.Coprime.mul hn hn', ?_⟩

  have hQ : Mo I g (Set.range e0) ≤ Qs I g z0 := by
    refine sup_le (Submodule.span_le.2 ?_) (mL_Qs I g hz0)
    rintro _ ⟨a, rfl⟩
    show ZMod' I g (hA I z0 (e0 a))
    rw [hA_symm]; exact Z_sig I g (hze a)
  have hmL : mL I g ≤ Qs I g z0 := mL_Qs I g hz0
  have hxmL : ∀ w ∈ mL I g, I.fmat x *ᵥ w ∈ mL I g := fun w hw =>
    pres I hxK g ∅ (mL I g) (by simp) (by simp) le_rfl w (mL_Mo I hw)
  have hNint : ∀ m : ℕ, ((m : I.E ⊗[I.F] Af I.F)) ∈ IntAf I.F I.E := fun m => natCast_mem _ m

  have hA1 : ZMod' I g (((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ v') + ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) := by
    have e : I.fmat x *ᵥ v' = z0 + (I.fmat x - 1) *ᵥ z0 + I.fmat x *ᵥ (v' - z0) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
      abel
    have e2 : ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ (v' - z0)) =
        (n : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ ((n' : I.E ⊗[I.F] Af I.F) • (v' - z0))) := by
      rw [Matrix.mulVec_smul, hA_smul_right, Nat.cast_mul]; ring
    have h2 : ZMod' I g (hA I z0 ((I.fmat x - 1) *ᵥ z0)) := hQ hxz
    have h3 : ZMod' I g (hA I z0 (I.fmat x *ᵥ ((n' : I.E ⊗[I.F] Af I.F) • (v' - z0)))) := hmL (hxmL _ hnv')
    have h1 := Z_smul I g (hNint (n * n')) hzz
    have := Z_add I g (Z_add I g h1 (Z_smul I g (hNint (n * n')) h2)) (Z_smul I g (hNint n) h3)
    rw [e, hA_add_right, hA_add_right]
    convert this using 1
    rw [← e2]; ring
  have hA2 : ZMod' I g (((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 v + ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) := by
    have e : v = z0 + (v - z0) := by abel
    have e2 : ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (v - z0) =
        (n' : I.E ⊗[I.F] Af I.F) * hA I z0 ((n : I.E ⊗[I.F] Af I.F) • (v - z0)) := by
      rw [hA_smul_right, Nat.cast_mul]; ring
    have h3 : ZMod' I g (hA I z0 ((n : I.E ⊗[I.F] Af I.F) • (v - z0))) := hmL hnv
    have h1 := Z_smul I g (hNint (n * n')) hzz
    have := Z_add I g h1 (Z_smul I g (hNint n') h3)
    rw [e, hA_add_right]
    convert this using 1
    rw [← e2]; ring

  have key : ε * (c * hA I z0 (I.fmat x *ᵥ v')) = ε * (c₂ * hA I z0 v) := by
    have := congrArg (fun w => hA I z0 w) hyp
    simp only [hA_smul_right] at this
    exact this
  have := Z_sub I g (Z_smul I g (mul_mem hε hc) hA1) (Z_smul I g (mul_mem hε hc₂) hA2)
  convert this using 1
  linear_combination (-((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) * key

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

theorem res_eq {D : D7} (PP : Formalism.L2.DIV.Pl D.host.E) (g : ℕ) (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε c c₂ : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (N : ℕ) (hN : N.Coprime g)
    (hZ : ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (ε * (c - c₂) * (N : Formalism.IndefR.Lev.EAf D))) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  obtain ⟨t, ht, he⟩ := hZ
  have hs : (⟨ε, hε⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * (⟨c, hc⟩ - ⟨c₂, hc₂⟩) * (N : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (g : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨t, ht⟩ := Subtype.ext (by
    push_cast
    exact he)
  have hr := congrArg (Formalism.L2.DIV.resS D.host.F PP) hs
  simp only [map_mul, map_sub, map_natCast, hε1, one_mul] at hr
  have hg0 : ((g : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
    show ((g : 𝓞 D.host.E) : 𝓞 D.host.E ⧸ PP.asIdeal) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 hg
  have hN0 : ((N : ℕ) : Formalism.L2.DIV.kP PP) ≠ 0 := by
    intro h0
    have hNm : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact h0
    have hco : IsCoprime ((N : ℤ) : 𝓞 D.host.E) ((g : ℤ) : 𝓞 D.host.E) :=
      (Nat.isCoprime_iff_coprime.2 hN).map (Int.castRingHom (𝓞 D.host.E))
    obtain ⟨a, b, hab⟩ := hco
    push_cast at hab
    apply PP.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hNm) (Ideal.mul_mem_left _ _ hg)
  rw [hg0, zero_mul] at hr
  exact sub_eq_zero.1 ((mul_eq_zero.1 hr).resolve_right hN0)

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped Matrix

theorem finE_inv_val {D : D7} (y : GA D (D.sp.Y 0)) :
    ((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val =
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (((Formalism.IndefR.RationalEmbedding.iota D) y).2)⁻¹ :=
  (congrArg Units.val (map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) (show GA D (Yc D 0) from y)).symm).trans
    ((GlobalTheory.SeeConjGroup.fmat_iota_eq_finE (D := D) (y⁻¹ : GA D (D.sp.Y 0))).symm.trans
      (congrArg (fun p : (Formalism.IndefR.RationalEmbedding.inst D).GA => (Formalism.L2.SG.InstExistsPf.instOf D).fmat p.2) (map_inv (Formalism.IndefR.RationalEmbedding.iota D) y)))

theorem core_res {D : D7} {r : ℕ} (e0 : Fin r → VA (Formalism.L2.SG.InstExistsPf.instOf D)) (z0 : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (g : ℕ) (hz0 : z0 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf)
    (hzz : ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (hA (Formalism.L2.SG.InstExistsPf.instOf D) z0 z0 + 1)) (hze : ∀ a, ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (hA (Formalism.L2.SG.InstExistsPf.instOf D) (e0 a) z0))
    (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (hxK : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) (hxz : InMod (Formalism.L2.SG.InstExistsPf.instOf D) g (Set.range e0) (((Formalism.L2.SG.InstExistsPf.instOf D).fmat x - 1) *ᵥ z0))
    (v v' : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (hv : InAt (Formalism.L2.SG.InstExistsPf.instOf D) g g (v - z0)) (hv' : InAt (Formalism.L2.SG.InstExistsPf.instOf D) g g (v' - z0))
    (PP : Formalism.L2.DIV.Pl D.host.E) (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε c c₂ : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (M : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (w w' : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D)
    (hM : M = (Formalism.L2.SG.InstExistsPf.instOf D).fmat x) (hw : w = v) (hw' : w' = v')
    (hyp : ε • (c • (M *ᵥ w')) = ε • (c₂ • w)) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  subst hM hw hw'
  obtain ⟨N, hN, hZ⟩ := core (Formalism.L2.SG.InstExistsPf.instOf D) g e0 z0 hz0 hzz hze x hxK hxz w w' hv hv' ε c c₂ hε hc hc₂ hyp
  exact res_eq PP g hg ε c c₂ hε hε1 hc hc₂ N hN hZ

set_option maxHeartbeats 400000 in

theorem frame_facts {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = (Formalism.L2.SG.InstExistsPf.instOf D)) (hId : IdE X) :
    ∃ (e0 : Fin D.R.rS → VA (Formalism.L2.SG.InstExistsPf.instOf D)) (z0 : VA (Formalism.L2.SG.InstExistsPf.instOf D)), z0 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ∧ ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (hA (Formalism.L2.SG.InstExistsPf.instOf D) z0 z0 + 1) ∧
      (∀ a, ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (hA (Formalism.L2.SG.InstExistsPf.instOf D) (e0 a) z0)) ∧
      (∀ κ ∈ rowJ X h, ∃ x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf, ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = x ∧ x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ∧
        InMod (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (Set.range e0) (((Formalism.L2.SG.InstExistsPf.instOf D).fmat x - 1) *ᵥ z0)) ∧
      ∀ u : D.what₂.Word, ∃ (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (z : VA (Formalism.L2.SG.InstExistsPf.instOf D)),
        ((Formalism.IndefR.RationalEmbedding.iota D) ((iotaX X h).symm (1, X.xu u))).2 = x ∧
        (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u (Fin.cast (rank_eq X h) r)))) = z ∧
        InAt (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (D.host.g 0 * D.host.g 1) ((Formalism.L2.SG.InstExistsPf.instOf D).fmat x⁻¹ *ᵥ z - z0) := by
  have hi : ∀ u, (iotaX X h) ((iotaX X h).symm (1, X.xu u)) = (1, X.xu u) := fun u => (iotaX X h).apply_symm_apply _
  obtain ⟨⟨I⟩, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq, lam_eq, ds, low, g_eq, g0_eq, Rph,
    Rph_spec, eX, fY, ee, ff, ef, Lb, Lb_perp, Lam_split, zu, zu_norm, zu_orth, zu_Lb, Fu, Fu_e, flagZVector, Fu_fixed,
    psiEf, psiEf_add, psiEf_int, psiEf_rat, e0, f0, z0, bw, bwd, ew, vectorsInLattice, basisApprox, gramIntegral, formsAtZero, weightVectorsIntegral, ew_idem,
    ew_orth, ew_int, ew_full, bw_w, bwd_w, bw_dual, latticeSpan, e_eq, xu, xu_fix, xu_z, xu_one, xu_K⟩ := X
  dsimp only at h
  subst h
  dsimp only at g_eq
  subst g_eq
  have hs : ∀ y : D.host.E, ιE.symm y = y := fun y => by
    have := eq_of_heq (hId (ιE.symm y))
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨e0, z0, vectorsInLattice.2.1, formsAtZero.1, fun a => (formsAtZero.2 a).1, fun κ hκ => ?_, fun u => ?_⟩
  · have hk : ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 ∈ K2set (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) e0 z0 bw := hκ.2
    exact ⟨_, rfl, hk.1, hk.2.2.1⟩
  · refine ⟨xu u, incl (Formalism.L2.SG.InstExistsPf.instOf D) (crdOf (Formalism.L2.SG.InstExistsPf.instOf D) ιE bas (zu u)), congrArg Prod.snd (hi u), ?_, xu_z u⟩
    funext r
    show algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (ιE (ιE.symm (bas.repr (zu u) r))) =
      algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (ιE.symm (bas.repr (zu u) r))
    rw [RingEquiv.apply_symm_apply, hs]

theorem inv_mulVec_eq {D : D7} (y : GA D (D.sp.Y 0)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (hx : ((Formalism.IndefR.RationalEmbedding.iota D) y).2 = x)
    (w : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D) (z : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (hz : w = z) :
    Matrix.mulVec ((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val w =
      ((Formalism.L2.SG.InstExistsPf.instOf D).fmat x⁻¹ *ᵥ z : VA (Formalism.L2.SG.InstExistsPf.instOf D)) := by
  subst hx hz
  exact congrArg (fun M : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D) => Matrix.mulVec M w) (finE_inv_val y)

set_option maxHeartbeats 400000 in

theorem finiteRing_sq_sub_mul_sq_eq_of_card {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : IdE X)
    (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ rowJ X h)
    (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hE : ε • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX X h).symm (1, X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u' (Fin.cast (rank_eq X h) r)))))) = ε • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX X h).symm (1, X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u (Fin.cast (rank_eq X h) r))))))) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  obtain ⟨e0, z0, hz0, hzz, hze, hK, hu⟩ := frame_facts X h hId
  obtain ⟨x, hx, hxK, hxz⟩ := hK κ hκ
  obtain ⟨y, z, hy, hz, hv⟩ := hu u
  obtain ⟨y', z', hy', hz', hv'⟩ := hu u'
  have e1 : (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val = (Formalism.L2.SG.InstExistsPf.instOf D).fmat x :=
    (GlobalTheory.SeeConjGroup.fmat_iota_eq_finE (D := D) κ).symm.trans (congrArg (Formalism.L2.SG.InstExistsPf.instOf D).fmat hx)
  have e2 := inv_mulVec_eq _ y hy _ z hz
  have e3 := inv_mulVec_eq _ y' hy' _ z' hz'
  exact core_res e0 z0 _ hz0 hzz hze x hxK hxz _ _ hv hv' PP hg ε c c₂ hε hε1 hc hc₂ _ _ _ e1 e2 e3 hE

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag

theorem resS_eq_of_flag : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)), κ ∈ rowJ W.S.X W.Q.instEq → ∀ (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, (∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u' (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))))) = toEAf D ei • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))))) → Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  intro D L hT Gi Gl Kc Yd cX ex W hP _ u u' κ hκ c c₂ hc hc₂ PP hPP hEq
  have lev : (pk W).toLevCh.Is W.P.A3.A.μ0 := hP.bot.hyp.2.2.2.1.lev
  have hPP' : PP ∈ (pk W).Pg := hPP
  have hg := (GlobalTheory.SeeConjRead.places_over_g (pk W) lev).1 PP hPP'
  obtain ⟨ei, hei⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (GlobalTheory.TypePlaces.not_isConjPl _ _ lev.Pg PP hPP' PP hPP')
  obtain ⟨hε, hε1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D ei PP hei
  exact finiteRing_sq_sub_mul_sq_eq_of_card W.S.X W.Q.instEq hP.bot.idE u u' κ hκ c c₂ hc hc₂ PP hg (toEAf D ei) hε hε1 (hEq ei hei)

end GlobalTheory.CongFlag
