import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.ThKUTrCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_of_entries {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} [IsTopologicalRing (AE F E)]
    (g : G →* UA σ J) (h : ∀ i j, ContinuousAt (fun x => mat (g x) i j) 1) : Continuous g := by
  apply continuous_of_continuousAt_one
  rw [Topology.IsInducing.subtypeVal.continuousAt_iff,
    Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]
  refine ContinuousAt.prodMk ?_ ?_
  · refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
    exact h i j
  · refine MulOpposite.continuous_op.continuousAt.comp ?_
    refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
    have := (h i j).comp_of_eq continuous_inv.continuousAt inv_one
    convert this using 1
    funext x
    simp [mat, map_inv]

open Formalism.MainNotions.S in

theorem exists_nat_mul_mem (x : E ⊗[F] Formalism.MainNotions.S.Af F) : ∃ N : ℕ, 1 ≤ N ∧ (N : E ⊗[F] Formalism.MainNotions.S.Af F) * x ∈ IntAf F E := by
  obtain ⟨d, hd0, hd⟩ := Formalism.UG.P.levelaf_denom (F := F) (E := E) x
  obtain ⟨N, hN, d', e⟩ := GlobalTheory.AutInhab.exists_nat_multiple d hd0
  refine ⟨N, hN, ?_⟩
  rw [← GlobalTheory.AutInhab.levelafC_natCast, ← e, Formalism.UG.P.levelafC_mul, mul_assoc]
  exact mul_mem (Formalism.UG.P.levelafC_mem _) hd

open Formalism.MainNotions.S in
theorem natCast_mul_mem {N : ℕ} (K : ℕ) {x : E ⊗[F] Formalism.MainNotions.S.Af F} (h : (N : E ⊗[F] Formalism.MainNotions.S.Af F) * x ∈ IntAf F E) :
    ((K * N : ℕ) : E ⊗[F] Formalism.MainNotions.S.Af F) * x ∈ IntAf F E := by
  rw [Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ K) h

open Formalism.MainNotions.S in

theorem exists_denom_coord {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ z ∈ lamAf (F := F) L, ∀ i, (D : E ⊗[F] Formalism.MainNotions.S.Af F) * z i ∈ IntAf F E := by
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.AutInhab.lamAf_fg (F := F) L hfg
  choose N hN1 hN using fun x : E ⊗[F] Formalism.MainNotions.S.Af F => exists_nat_mul_mem (F := F) x
  let den : (Fin n → E ⊗[F] Formalism.MainNotions.S.Af F) → ℕ := fun v => ∏ i, N (v i)
  refine ⟨∏ v ∈ s, den v, Finset.one_le_prod' fun v _ => Finset.one_le_prod' fun i _ => hN1 _, ?_⟩
  intro z hz
  rw [← hs] at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    intro i
    rw [← Finset.prod_erase_mul _ _ hy]
    show (((∏ v ∈ s.erase y, den v) * ∏ i, N (y i) : ℕ) : E ⊗[F] Formalism.MainNotions.S.Af F) * y i ∈ IntAf F E
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), ← mul_assoc]
    exact natCast_mul_mem _ (hN (y i))
  | zero => intro i; simp
  | add a b _ _ ha hb => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (ha i) (hb i)
  | smul r a _ ha =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem r.2 (ha i)

open Formalism.MainNotions.S in

theorem exists_level_entries {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) (N : ℕ) (hN : 1 ≤ N) :
    ∃ g : ℕ, 1 ≤ g ∧ ∀ y ∈ GlobalTheory.AutInhab.congSub (lamAf (F := F) L) g, ∀ i j, ∃ t ∈ IntAf F E,
      ((y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) - 1) i j = (N : E ⊗[F] Formalism.MainNotions.S.Af F) * t := by
  classical
  choose M hM1 hM using fun j : Fin n =>
    GlobalTheory.AutInhab.lamAf_absorbs (F := F) L hs (Pi.single j (1 : E ⊗[F] Formalism.MainNotions.S.Af F))
  obtain ⟨D, hD1, hD⟩ := exists_denom_coord (F := F) L hfg
  let M' : ℕ := ∏ j, M j
  have hM'1 : 1 ≤ M' := Finset.one_le_prod' fun j _ => hM1 j
  have hMe : ∀ j, (M' : E ⊗[F] Formalism.MainNotions.S.Af F) • Pi.single j (1 : E ⊗[F] Formalism.MainNotions.S.Af F) ∈ lamAf (F := F) L := by
    intro j
    show (((∏ j, M j : ℕ)) : E ⊗[F] Formalism.MainNotions.S.Af F) • _ ∈ _
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Nat.cast_mul, mul_smul]
    exact GlobalTheory.AutInhab.natCast_smul_mem _ _ (hM j)
  refine ⟨N * D * M', Nat.mul_pos (Nat.mul_pos hN hD1) hM'1, ?_⟩
  rintro y ⟨-, hy⟩ i j
  obtain ⟨z, hz, e⟩ := hy _ (hMe j)
  refine ⟨(D : E ⊗[F] Formalism.MainNotions.S.Af F) * z i, hD z hz i, ?_⟩
  have hu := GlobalTheory.AutInhab.isUnit_natCast (F := F) (E := E) M' hM'1
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one, Nat.cast_mul, mul_comm ((N * D : ℕ) : E ⊗[F] Formalism.MainNotions.S.Af F),
    mul_smul, hu.smul_left_cancel] at e
  have := congrFun e i
  simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_mul] at this
  rw [this, mul_assoc]

theorem trHom_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J J' : Matrix (Fin n) (Fin n) E) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] Formalism.MainNotions.S.Af F)) (ε : InfinitePlace F → Fin n → Bool) (P : InfinitePlace F → (Matrix (Fin n) (Fin n) ℂ)ˣ) (L : Submodule (𝓞 E) (Fin n → E)) (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) (hU : ∀ x, GlobalTheory.ThKUTr.rawT Φ ε P (Formalism.UG.UPts σ J' (Formalism.MainNotions.S.Af F)) x ∈ UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J)), Continuous (fun c : InfinitePlace F → ℂ => Φ.symm (c, 0)) → (∀ U ∈ nhds (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), ∃ N : ℕ, 1 ≤ N ∧ ∀ y ∈ Formalism.MainNotions.S.IntAf F E, Φ.symm (0, (N : E ⊗[F] Formalism.MainNotions.S.Af F) * y) ∈ U) → @Continuous _ _ (@instTopologicalSpaceProd _ _ _ (GlobalTheory.AutInhab.adelicBasis L hs hfg (Formalism.UG.UPts σ J' (Formalism.MainNotions.S.Af F))).topology) _ (GlobalTheory.ThKUTr.trHom σ J Φ ε P (Formalism.UG.UPts σ J' (Formalism.MainNotions.S.Af F)) hU) := by
  intro F E _ _ _ _ _ σ n J J' Φ ε P L hs hfg hU h1 h2
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  letI tH : TopologicalSpace (Formalism.UG.UPts σ J' (Formalism.MainNotions.S.Af F)) :=
    (GlobalTheory.AutInhab.adelicBasis L hs hfg (Formalism.UG.UPts σ J' (Formalism.MainNotions.S.Af F))).topology
  haveI : IsTopologicalGroup (Formalism.UG.UPts σ J' (Formalism.MainNotions.S.Af F)) :=
    (GlobalTheory.AutInhab.adelicBasis L hs hfg (Formalism.UG.UPts σ J' (Formalism.MainNotions.S.Af F))).isTopologicalGroup
  apply continuous_of_entries
  intro i j

  have hq : ContinuousAt (fun y : Formalism.UG.UPts σ J' (Formalism.MainNotions.S.Af F) =>
      Φ.symm (0, (((y : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) - 1) i j)) 1 := by
    show Filter.Tendsto _ _ _
    simp only [OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_apply]
    rw [show ((0 : InfinitePlace F → ℂ), (0 : E ⊗[F] Formalism.MainNotions.S.Af F)) = 0 from rfl, map_zero]
    rw [(GlobalTheory.AutInhab.adelicBasis L hs hfg (Formalism.UG.UPts σ J' (Formalism.MainNotions.S.Af F))).nhds_one_hasBasis.tendsto_left_iff]
    intro U hU0
    obtain ⟨N, hN, hNU⟩ := h2 U hU0
    obtain ⟨g, hg, hgy⟩ := exists_level_entries (F := F) L hs hfg N hN
    refine ⟨_, ⟨g, hg, rfl⟩, fun y hy => ?_⟩
    obtain ⟨t, ht, e⟩ := hgy _ hy i j
    have e' : ((((y : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) - 1) i j) =
        (N : E ⊗[F] Formalism.MainNotions.S.Af F) * t := e
    show Φ.symm (0, _) ∈ U
    rw [e']
    exact hNU t ht
  have hc : Continuous (fun x : ∀ v : InfinitePlace F, Formalism.REAL.UJ (ε v) =>
      Φ.symm ((fun w => ((P w : Matrix (Fin n) (Fin n) ℂ) * Formalism.MainNotions.S.uMat (x w) *
        (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) i j), 0)) := by
    refine h1.comp (continuous_pi fun w => ?_)
    have hw : Continuous fun x : ∀ v : InfinitePlace F, Formalism.REAL.UJ (ε v) => Formalism.MainNotions.S.uMat (x w) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply w))
    exact ((continuous_const.matrix_mul hw).matrix_mul continuous_const).matrix_elem i j
  have key : (fun x => mat (GlobalTheory.ThKUTr.trHom σ J Φ ε P (Formalism.UG.UPts σ J' (Formalism.MainNotions.S.Af F)) hU x) i j) =
      fun x => Φ.symm ((fun w => ((P w : Matrix (Fin n) (Fin n) ℂ) * Formalism.MainNotions.S.uMat (x.1 w) *
        (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) i j), 0) +
        Φ.symm (0, (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) i j) +
        Φ.symm (0, ((((x.2 : Formalism.UG.UPts σ J' (Formalism.MainNotions.S.Af F)) : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) :
          Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) - 1) i j) := by
    funext x
    rw [GlobalTheory.ThKUTr.mat_trHom, GlobalTheory.ThKUTr.rawT_val, GlobalTheory.ThKUTr.glueM_apply, ← map_add, ← map_add]
    congr 1
    ext <;> simp
  rw [key]
  exact ((hc.comp continuous_fst).continuousAt.add continuousAt_const).add
    (hq.comp_of_eq continuousAt_snd rfl)

end GlobalTheory.ThKUTrCont
