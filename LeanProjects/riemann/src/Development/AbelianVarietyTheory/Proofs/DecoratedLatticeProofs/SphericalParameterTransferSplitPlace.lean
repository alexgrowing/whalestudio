import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumHeckeIdentitySplitPlaceChartsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinearStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeEsymmScaledMultisetAddSegmentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralGLCommensuratedDoubleCosetCardInvSymmStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.SplitTransfer

theorem seg_map_inv {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : ℂˣ) (t : ℕ) :
    (GlobalTheory.LFun.seg w x t).map (·⁻¹) = GlobalTheory.LFun.seg w x⁻¹ t := by
  have hr : (Finset.range t).image (fun i => t - 1 - i) = Finset.range t := by
    ext i
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro hi; exact ⟨t - 1 - i, by omega, by omega⟩
  have hinj : Set.InjOn (fun i => t - 1 - i) (Finset.range t : Set ℕ) := fun a ha b hb e => by
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at e
    omega
  unfold GlobalTheory.LFun.seg
  conv_rhs => rw [← hr, Finset.image_val_of_injOn hinj, Multiset.map_map]
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  have hi' : i < t := Finset.mem_range.1 hi
  simp only [Function.comp_apply, mul_inv]
  congr 1
  apply Units.ext
  simp only [Units.val_inv_eq_inv_val, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow]
  rw [← Complex.cpow_neg]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

set_option maxHeartbeats 1600000 in

theorem transferOn_isSplit : ∀ D : D7, TransferOn D fun v => IsSplit (E := D.host.E) v := by
  intro D ψ S T χS χT om hW t ht v hv hunr w h U hU f hf X _ _ ρ x B hx X' _ _ ρ' b hb hne
  obtain ⟨eS, heS⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D S v w h).1 hv
  obtain ⟨eT, heT⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D T v w h).1 hv
  have hxS := hx.isSatVecGL hv heS
  obtain ⟨hfix, hH⟩ := GlobalTheory.T.latticeVacuum_heckeIdentity_splitPlace_charts D ψ S T χS χT om hW t ht v w h hv hunr eS eT heS heT (f : WO S T → ℂ) hf
  obtain ⟨hcS, hsS⟩ := GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm D.host.E w S.rank
  obtain ⟨hcT, hsT⟩ := GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm D.host.E w T.rank
  let σF : Representation ℂ (GL (Fin S.rank) (w.adicCompletion D.host.E)) (WO S T → ℂ) :=
    ((om.comp (MonoidHom.inl _ _)).comp (embV S v)).comp eS.symm.toMonoidHom
  let πF : Representation ℂ (GL (Fin T.rank) (w.adicCompletion D.host.E)) (WO S T → ℂ) :=
    ((om.comp (MonoidHom.inr _ _)).comp (embV T v)).comp eT.symm.toMonoidHom
  have eσ : ∀ g, σF g = om (embV S v (eS.symm g), embV T v 1) := fun g => by simp [σF]
  have eπ : ∀ g, πF g = om (embV S v 1, embV T v (eT.symm g)) := fun g => by simp [πF]
  let σU := σF.subrepresentation U fun g u hu => by rw [Submodule.mem_comap, eσ]; exact hU _ _ u hu
  let πU := πF.subrepresentation U fun g u hu => by rw [Submodule.mem_comap, eπ]; exact hU _ _ u hu
  let ρS := ρ.comp eS.symm.toMonoidHom
  let ρT := ρ'.comp eT.symm.toMonoidHom

  have hKS : ∀ k ∈ KGL w S.rank, eS.symm k ∈ Kv S v := fun k hk => (heS.2 (eS.symm k)).2 (by simpa using hk)
  have hKT : ∀ k ∈ KGL w T.rank, eT.symm k ∈ Kv T v := fun k hk => (heT.2 (eT.symm k)).2 (by simpa using hk)
  have hfS : f ∈ fixed σU (KGL w S.rank) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
    change σF k (f : WO S T → ℂ) = f
    rw [eσ]; exact hfix _ (hKS k hk) _ (one_mem _))
  have hfT : f ∈ fixed πU (KGL w T.rank) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
    change πF k (f : WO S T → ℂ) = f
    rw [eπ]; exact hfix _ (one_mem _) _ (hKT k hk))
  have hequiv : ∀ g (u : U), (b.flip x) (πU g u) = ρT g ((b.flip x) u) := fun g u => by
    have e := hb 1 (eT.symm g) u x
    rw [show ρ 1 x = x by simp] at e
    rw [LinearMap.flip_apply, LinearMap.flip_apply]
    change b (πU g u) x = ρ' (eT.symm g) (b u x)
    rw [← e]
    congr 2
    exact Subtype.ext (by change πF g (u : WO S T → ℂ) = _; rw [eπ])
  have hinv : ∀ g (u : U) y, b (σU g u) (ρS g y) = b u y := fun g u y => by
    have e := hb (eS.symm g) 1 u y
    rw [show ρ' 1 (b u y) = b u y by simp] at e
    rw [← e]
    congr 2
    exact Subtype.ext (by change σF g (u : WO S T → ℂ) = _; rw [eσ])
  have hbfix : b f x ∈ fixed ρT (KGL w T.rank) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    have e := hequiv k f
    rw [GlobalTheory.LGrp.mem_fixed.1 hfT k hk] at e
    exact e.symm
  have hcard : (stepPar χS χT t (fun _ => B) w).card = T.rank := by
    simp [stepPar, GlobalTheory.LFun.seg, hxS.2.2.1, ht]
  have hB'inv : (stepPar χS χT t (fun _ => B) w).map (·⁻¹) =
      (B.map (·⁻¹)).map ((val (F := D.host.F) χS w)⁻¹ * ((val (F := D.host.F) χT w)⁻¹)⁻¹ * ·) +
        GlobalTheory.LFun.seg w (val (F := D.host.F) χS w)⁻¹ t := by
    rw [stepPar, Multiset.map_add, seg_map_inv, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun c _ => ?_
    simp only [Function.comp_apply, mul_inv]
  refine Or.inl ⟨hv, eT, heT, (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets D.host.E w T.rank X' ρT (b f x) _ hne hbfix hcard).2 fun ϖ hϖ k hk => ?_⟩
  have hsubT : ∀ g (y : U), U.subtype (πU g y) = πF g (U.subtype y) := fun g y => rfl
  have hsubS : ∀ g (y : U), U.subtype (σU g y) = σF g (U.subtype y) := fun g y => rfl
  have hInvT : (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) ∈ Hecke ℂ (KGL w T.rank) :=
    (GlobalTheory.T.hecke_operator_move_across_invariant_bilinear _ (KGL w T.rank) hcT hsT ℂ ℂ ℂ 1 1 0 (fun _ _ _ => by simp) 0 (zero_mem _) 0 (zero_mem _) _
      (Tj_mem_hecke hϖ k)).1
  let cf : ℕ → ℂ := fun j => if j ≤ k then (qV D.host.E w : ℂ) ^ ((S.rank - j) * (k - j)) *
    (Formalism.L2.Col.gaussBin (qV D.host.E w) t (k - j) : ℂ) *
    (((val (F := D.host.F) χS w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ S.rank)⁻¹ ^ k *
    (((val (F := D.host.F) χT w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ T.rank) ^ j else 0
  have hH' : heckeVec πF (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (U.subtype f) =
      ∑ j ∈ Finset.range (S.rank + 1), cf j • heckeVec σF (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) (U.subtype f) :=
    hH ϖ hϖ k hk
  have e1 : U.subtype (heckeVec πU (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f) =
      heckeVec πF (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (U.subtype f) :=
    map_heckeVec hcT hInvT U.subtype hsubT f
  have e2 : ∀ j, U.subtype (heckeVec σU (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f) =
      heckeVec σF (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) (U.subtype f) := fun j =>
    map_heckeVec hcS (Tj_mem_hecke hϖ j) U.subtype hsubS f
  have hT : heckeVec πU (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f =
      ∑ j ∈ Finset.range (S.rank + 1), cf j • heckeVec σU (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f := by
    apply U.injective_subtype
    rw [e1, hH', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, e2 j]
  have hmove : ∀ j ∈ Finset.range (S.rank + 1), b (heckeVec σU (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f) x =
      satEig (qV D.host.E w) S.rank (B.map (·⁻¹)) j • b f x := by
    intro j hj
    rw [(GlobalTheory.T.hecke_operator_move_across_invariant_bilinear _ _ hcS hsS U X X' σU ρS b hinv f hfS x hxS.2.1 _ (Tj_mem_hecke hϖ j)).2,
      (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets D.host.E w S.rank X ρS x B hxS.1 hxS.2.1 hxS.2.2.1).1 hxS ϖ hϖ j
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), map_smul]
  have hsym := GlobalTheory.T.satake_esymm_scaled_multiset_add_segment D.host.E w S.rank t k (B.map (·⁻¹)) (val (F := D.host.F) χS w)⁻¹
    (val (F := D.host.F) χT w)⁻¹ (by rw [Multiset.card_map, hxS.2.2.1]) (ht ▸ hk)
  calc heckeVec ρT (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (b f x)
      = b (heckeVec πU (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f) x :=
        (map_heckeVec hcT hInvT (b.flip x) hequiv f).symm
    _ = ∑ j ∈ Finset.range (S.rank + 1), cf j • satEig (qV D.host.E w) S.rank (B.map (·⁻¹)) j • b f x := by
        rw [hT, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [map_smul, LinearMap.smul_apply, hmove j hj]
    _ = satEig (qV D.host.E w) T.rank ((stepPar χS χT t (fun _ => B) w).map (·⁻¹)) k • b f x := by
        simp_rw [smul_smul]
        rw [← Finset.sum_smul]
        congr 1
        rw [hB'inv, ht, hsym]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        simp only [cf]
        split_ifs
        · rw [ht]
          simp only [Units.val_inv_eq_inv_val, inv_inv, mul_inv]
        · rfl

end GlobalTheory.ChainOnto.SplitTransfer
