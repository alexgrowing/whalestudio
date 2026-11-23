import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcPerm

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
open Polynomial
namespace GlobalTheory.CutAtGood
section AtPlace
attribute [local instance] Formalism.BasicNotions.Examples₂.NZ.neZero_g Formalism.BasicNotions.Examples₂.NZ.fact_g Classical.propDecidable
variable (D : D7)
end AtPlace
section OnMt
variable (D : D7) (μ : D.what₂.Tup) (j : ℕ)
local notation "CZ" => Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
end OnMt
section Record
variable {D : D7}
theorem isBCV_of_isBCV_of_same_ptV (hT0 : SumRepresentations.tie0 D) (hG : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D) (hBC : SumRepresentations.adm1 D) {i : D.nd.Loc}
    {x : D.nd.X i} {P0 PI : D.naut.AV i} (h0 : D.naut.ptV i P0 = some x) (hx : D.naut.ptV i PI = some x)
    {Pa0 : List (Part D.naut.CG)} (hB0 : IsBCV D.nd D.naut i P0 Pa0) : IsBCV D.nd D.naut i PI Pa0 := by
  obtain ⟨Pa, hPa⟩ := hBC i PI
  have hp := _root_.UpperTheory.GalS.bcPerm_alt D hT0 hG h5 i x P0 PI Pa0 Pa h0 hx hB0 hPa
  exact isBCV_perm hPa hp.symm
end Record
section Series
variable {D : D7}
local notation "CZ" => Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
end Series
section Main
end Main
theorem main_alt_alt : ∀ (D : D7) (P : Pend D), GlobalTheory.TypeLeaf.SerLoc D → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → EigSpan P → CentralElt D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i, ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i), CutAt i k π Xs β b ∧ TypeLocus P i k Xs := by
  intro D P hSer hBC hLGC hT0 h5 hEig hCE i k hl π hπ
  classical
  obtain ⟨hπZN, Sig, hSig, hgood⟩ := (D.Zgood_tie i π).1 hπ
  obtain ⟨σ', hσ'⟩ := P.Par_surj i π Sig hSig
  obtain ⟨P0, hP0, hB0⟩ := hSig
  let s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X] := fun kv => D.ntypes.labPar kv.1 σ' kv.2
  obtain ⟨z, L, hLnd, hLall, hz⟩ := hCE i s
  have hz' : ∀ F, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F := by
    intro F
    rw [hz, list_prod_eq s L hLnd hLall]
    rw [show (D.what₂.restRowsFiniteGroupCard : ℂ) • ((∏ kv, ef s kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        MonoidAlgebra ℂ (G0g D.nd)) = (((D.what₂.restRowsFiniteGroupCard : ℂ) • ∏ kv, ef s kv :
          ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) from rfl,
      onMt_coe, map_smul]
    rfl
  have hfixπ : ∀ PI : D.naut.AV i, D.naut.ptV i PI = some π → ∀ F ∈ D.naut.typeV i PI,
      D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F = F := by
    intro PI hPI F hF
    have hB := _root_.GlobalTheory.CutAtGood.isBCV_of_isBCV_of_same_ptV hT0 hLGC h5 hBC hP0 hPI hB0
    have hF' := typeV_le_mtPar hσ' hB hF
    refine cen_prod_fix _ _ _ F fun kv _ => ?_
    rw [← onMt_coe]
    exact series_fix hSer i σ' F hF' kv.1 kv.2
  have hιb : iotaO D.nd D.naut i (D.what₂.restRowsFiniteGroupCard : D.nd.O i) = (D.what₂.restRowsFiniteGroupCard : ℂ) := map_natCast _ _
  have hscal : ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π,
      (P.zO i z).baseChange (FractionRing (D.nd.O i)) u = (D.what₂.restRowsFiniteGroupCard : D.nd.O i) • u :=
    hEig i z π _ fun PI hPI F hF => by rw [hz', hfixπ PI hPI F hF, hιb]
  let Xs : Set (D.nd.X i) :=
    {x | ∃ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, (P.zO i z).baseChange (FractionRing (D.nd.O i)) u ≠ 0}
  have hwit : ∀ x ∈ Xs, ∃ PI : D.naut.AV i, D.naut.ptV i PI = some x ∧ ∃ F ∈ D.naut.typeV i PI,
      ∀ kv, D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (ef s kv) F ≠ 0 := by
    rintro x ⟨u, hu, hne⟩
    by_contra hcon
    push Not at hcon
    apply hne
    have h0 := hEig i z x 0 (fun PI hPI F hF => ?_) u hu
    · rw [h0, zero_smul]
    · obtain ⟨kv, hkv⟩ := hcon PI hPI F hF
      rw [hz', map_zero, zero_smul]
      by_contra hc
      have hc' : D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F ≠ 0 := fun h => hc (by rw [h, smul_zero])
      exact cen_prod_ne _ _ _ F hc' kv (Finset.mem_univ kv) hkv
  have hcard : D.what₂.restRowsFiniteGroupCard ≠ 0 := by
    rw [D.nd.restN_card_levelGroup_eq]
    refine Finset.prod_ne_zero_iff.2 fun k' _ => ?_
    have : NeZero (D.host.g k') := ⟨(D.host.g_prime k').ne_zero⟩
    exact pow_ne_zero _ Nat.card_pos.ne'
  have hb0 : (D.what₂.restRowsFiniteGroupCard : D.nd.O i) ≠ 0 := by
    intro h
    have := congrArg (iotaO D.nd D.naut i) h
    rw [hιb, map_zero] at this
    exact (Nat.cast_ne_zero.2 hcard) this
  have hπX : π ∈ Xs := by
    have hpos : 0 < Module.finrank ℂ ↥(⨆ P ∈ {P | D.naut.ptV i P = some π}, D.naut.typeV i P) := by
      obtain ⟨P2, hP2⟩ := D.naut.pt_surj i π
      refine Nat.pos_of_ne_zero fun h0 => D.naut.typeV_ne i P2 ?_
      have hbot := Submodule.finrank_eq_zero.1 h0
      exact le_bot_iff.1 (hbot ▸ le_iSup₂_of_le (f := fun P _ => D.naut.typeV i P) P2 hP2 le_rfl)
    rw [← D.naut.eig_dim i π] at hpos
    have hne : heckeEig (D.nd.T i) (D.nd.act i) π ≠ ⊥ := by
      intro h
      have e : D.nd.mult i π = Module.finrank (FractionRing (D.nd.O i))
          ↥(heckeEig (D.nd.T i) (D.nd.act i) π) := rfl
      rw [e, h, finrank_bot] at hpos
      exact lt_irrefl 0 hpos
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨u, hu, ?_⟩
    rw [hscal u hu, ← algebraMap_smul (FractionRing (D.nd.O i))]
    refine smul_ne_zero ?_ hu0
    rw [Ne, ← map_zero (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))]
    exact (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))).ne hb0
  refine ⟨Xs, P.zO i z, (D.what₂.restRowsFiniteGroupCard : D.nd.O i), ⟨hπX, (D.Z_tie i π).2 hπZN, ?_, fun f => P.zO_comm i z f,
    hb0, hscal, fun x hx u hu => ?_, ?_⟩, ?_⟩
  · intro x hx hxZ
    obtain ⟨PI, hPI, F, hF, hne⟩ := hwit x hx
    obtain ⟨Sig1, hS1⟩ := hasParamX_of_Z hT0 h5 hxZ
    obtain ⟨σ1, hσ1⟩ := P.Par_surj i x Sig1 hS1
    obtain ⟨P1, hP1, hB1⟩ := hS1
    have hF1 := typeV_le_mtPar hσ1 (_root_.GlobalTheory.CutAtGood.isBCV_of_isBCV_of_same_ptV hT0 hLGC h5 hBC hP1 hPI hB1) hF
    have hlab : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), s kv = D.ntypes.labPar kv.1 σ1 kv.2 := fun kv =>
      hSer i σ1 kv.1 kv.2 (s kv) F hF1
        (by rw [show Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv)) = ((ef s kv : ↥(Subalgebra.center ℂ
          (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) from rfl, onMt_coe]; exact hne kv)
    have hg1 : goodSig D.nd D.naut Sig1 := goodSig_of_labels (fun k' v => by
      rw [← labPar_eq hσ' k' v, ← labPar_eq hσ1 k' v]; exact hlab ⟨k', v⟩) hgood
    exact (D.Zgood_tie i x).2 ⟨(D.Z_tie i x).1 hxZ, Sig1, ⟨P1, hP1, hB1⟩, hg1⟩
  · by_contra h
    exact hx ⟨u, hu, h⟩
  · rw [← hl]
    exact lenUnit_natCast_le i _ hcard
  · refine ⟨fun v => s ⟨k, v⟩, fun v => ?_, fun x hx => ?_⟩
    · show Squarefree (D.ntypes.labPar k σ' v) ∧ ∀ u : (ZMod (D.host.g k))ˣ,
          u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ → ¬ (D.ntypes.labPar k σ' v).IsRoot (u : ZMod (D.host.g k))
      rw [labPar_eq hσ' k v]
      exact good_labels hgood i k v
    · obtain ⟨PI, hPI, F, hF, hne⟩ := hwit x hx
      refine ⟨PI, hPI, fun v => ?_⟩
      have h1 := hne ⟨k, v⟩
      rw [← onMt_coe] at h1
      change D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k (s ⟨k, v⟩))) F ≠ 0 at h1
      have hc : ∀ τ ∈ (Finset.univ : Finset ((P.lz k).Irr D.R.r)),
          Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = s ⟨k, v⟩ then (P.lz k).idem τ else 0) ∈
            Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
        intro τ _
        split_ifs
        · exact atPlace_mem_center D k v _ fun b => (P.lz k).idem_central τ b
        · rw [atPlace_zero]
          exact Subalgebra.zero_mem _
      rw [P.eSer_eq k, atPlace_sum, onMt_sum D _ _ _ _ hc, LinearMap.sum_apply] at h1
      obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      by_cases hlab : (P.lz k).lab τ = s ⟨k, v⟩
      · rw [if_pos hlab] at hτ
        exact ⟨τ, (P.kty_spec i PI k v τ).2 ⟨F, hF, hτ⟩, hlab⟩
      · exfalso
        apply hτ
        rw [if_neg hlab, atPlace_zero]
        unfold NTypes.onMt
        rw [dif_pos (Subalgebra.zero_mem _)]
        have e0 : (⟨0, Subalgebra.zero_mem _⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) = 0 := rfl
        rw [e0, map_zero]
        rfl
end GlobalTheory.CutAtGood
end
end
