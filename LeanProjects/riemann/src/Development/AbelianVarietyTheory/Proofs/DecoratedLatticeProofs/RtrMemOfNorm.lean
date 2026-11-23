import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdFormsOfEquivariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColsSharpDictionary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRationalPointsStabiliserFrame
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MiTop.CenIsom

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

theorem rtr_mem_of_norm (hK : X.LevelSubgroupCharacter) {δ : Hfin X u}
    (hn : ∀ κ : Ku X u hK, ∃ κ' : Ku X u hK, (κ : Hfin X u) * δ = δ * κ' ∧
      ((psiK X u hK κ' : ℂˣ) : ℂ) = ((psiK X u hK κ : ℂˣ) : ℂ))
    {T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)} (hT : T ∈ Cu X u hK) : rtr X δ T ∈ Cu X u hK := by
  obtain ⟨h1, h2⟩ := hT
  refine ⟨fun ξ => ⟨fun γ y => ?_, fun y κ => ?_⟩, fun g ξ y => ?_⟩
  · show T ξ ((_, _) * y * (1, δ)) = T ξ (y * (1, δ))
    rw [mul_assoc]
    exact (h1 ξ).1 γ _
  · obtain ⟨κ', hκ', hψ⟩ := hn κ
    have hc : ((1 : Hinf X u), (κ : Hfin X u)) * (1, δ) = (1, δ) * (1, (κ' : Hfin X u)) :=
      Prod.ext rfl hκ'
    have e : y * (1, (κ : Hfin X u)) * (1, δ) = y * (1, δ) * (1, (κ' : Hfin X u)) := by
      rw [mul_assoc, mul_assoc, hc]
    refine (congrArg (T ξ) e).trans (((h1 ξ).2 _ κ').trans ?_)
    rw [hψ]
    rfl
  · have hc : ((g : Hinf X u), (1 : Hfin X u)) * (1, δ) = (1, δ) * (g, 1) :=
      Prod.ext ((mul_one g).trans (one_mul g).symm) ((one_mul δ).trans (mul_one δ).symm)
    have e : y * (g, 1) * (1, δ) = y * (1, δ) * (g, 1) := by
      rw [mul_assoc, mul_assoc, hc]
    exact (h2 g ξ (y * (1, δ))).trans (congrArg (T ξ) e.symm)

theorem rtr_comm {δ δ' : Hfin X u} (h : δ * δ' = δ' * δ) (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) :
    rtr X δ' (rtr X δ T) = rtr X δ (rtr X δ' T) := by
  ext ξ y
  have hc : ((1 : Hinf X u), δ') * (1, δ) = (1, δ) * (1, δ') := Prod.ext rfl h.symm
  have e : y * (1, δ') * (1, δ) = y * (1, δ) * (1, δ') := by rw [mul_assoc, mul_assoc, hc]
  exact congrArg (T ξ) e

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem exists_rtr_dia {F : Formalism.L2.Forms.Forms0 D u} (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter) (hL : LevelMatch X Tr hK)
    (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    ∃ δ : Hfin X u, ∀ T ∈ Cu X u hK, rtr X δ T ∈ Cu X u hK ∧
      dictA X Tr (rtr X δ T) = (D.mem u).A.rhoT v a (dictA X Tr T) := by
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  have hσ := GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X Tr.ιA hA
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.frame_action_mulEquiv D X u Tr.wt Tr.ιA hW hA hσ
  obtain ⟨-, hΓ, hsT⟩ := GlobalTheory.transport_rational_points D X u Tr.wt Tr.ιA hW hA Φ hΦ
  obtain ⟨hψ, -, hφ, -, -⟩ := cols_sharp_dictionary D X u hK
  obtain ⟨k, hk, hkT⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσe⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.splitAtT_of_tied F.atT v
  obtain ⟨y, hy⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.is_diamond_of_local_diamond F.cls0.lev (F.atT.eV v).1 (F.atT.eV v).2 k
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_diamond_of_split_idempotent F.cls0.lev _ _ (D.mem u).A.T_prime k hkT e he hee hσe)
  have hlev := fun h => hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)
  obtain ⟨δ, hδ⟩ : ∃ δ : Hfin X u, Φ δ = Tr.h0 * y * Tr.h0⁻¹ := Φ.surjective _
  refine ⟨δ, fun T hT => ⟨rtr_mem_of_norm hK (fun κ => ?_) hT, ?_⟩⟩
  · have hκ := (hlev κ).1.1 κ.2
    have hm := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.diamond_conj_mem_level F.cls0.lev _ _ hy ⟨_, hκ⟩
    have hχ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.level_character_conj_diamond F.cls0.lev _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.level_places_not_bad F.atT v) hy ⟨_, hκ⟩
    have e1 : Tr.h0⁻¹ * Φ (δ⁻¹ * κ * δ) * Tr.h0 = y⁻¹ * (Tr.h0⁻¹ * Φ κ * Tr.h0) * y := by
      rw [map_mul, map_mul, map_inv, hδ]
      group
    have e2 := congrArg Subtype.val e1
    have hm' : (Tr.h0⁻¹ * Φ (δ⁻¹ * κ * δ) * Tr.h0).1 ∈ F.cls0.lev.U := by
      rw [e2]
      exact hm
    have hin := (hlev (δ⁻¹ * κ * δ)).1.2 hm'
    refine ⟨⟨δ⁻¹ * κ * δ, hin⟩, by simp only [← mul_assoc, mul_inv_cancel, one_mul], ?_⟩
    rw [(hlev _).2 hin hm', (hlev κ).2 κ.2 hκ, ← hχ]
    exact congrArg (fun x => ((F.cls0.lev.chi x : ℂˣ) : ℂ)) (Subtype.ext e2)
  · have key := GlobalTheory.adForms_of_equivariant D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hinf X u) (Hfin X u)
      (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 D.what₂.Tau (Formalism.L2.Forms.embT D)
      ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ
      (fun h => (hlev h).1) (fun h hk hy => (hlev h).2 hk hy) hΓ
      (fun γ g hγ ξ y y' hy => Tr.J_eqv _ (iotaI X u γ).2 ξ y y' (by rw [hsT γ g hγ]; exact hy))
      (fun ξ => by rw [← Formalism.L2.Forms.lamT_zero]; exact Tr.J_val ξ)
      (shP X u T) (hφ ⟨T, hT⟩)
    have hc : ∀ c, Φ (Tr.hc c) = F.cls0.y c * Tr.h0⁻¹ := fun c => (hΦ (Tr.hc c) _).1 (Tr.hc_rep c)
    have e1 : dictA X Tr T = fun c s =>
        (fun x => Tr.J (shP X u T (Φ.symm (x * Tr.h0⁻¹)))) (F.cls0.y c) (F.val0.eY s) := by
      funext c s
      show Tr.J (shP X u T (Tr.hc c)) (F.val0.eY s) = Tr.J (shP X u T (Φ.symm (F.cls0.y c * Tr.h0⁻¹))) (F.val0.eY s)
      rw [← hc, MulEquiv.symm_apply_apply]
    rw [e1, Formalism.L2.Forms.rhoT_eq F.val0 v a k hk y hy _ key.1]
    funext c s
    have e2 : Tr.hc c * δ = Φ.symm (F.cls0.y c * y * Tr.h0⁻¹) := by
      apply Φ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hc, hδ]
      group
    show Tr.J (shP X u (rtr X δ T) (Tr.hc c)) (F.val0.eY s) =
      Tr.J (shP X u T (Φ.symm (F.cls0.y c * y * Tr.h0⁻¹))) (F.val0.eY s)
    rw [Formalism.L2.SG.Pf.ColDictPf.rieszVector_rightTranslate, e2]

theorem ram_rtr {F : Formalism.L2.Forms.Forms0 D u} (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter) (hL : LevelMatch X Tr hK)
    (hI : ColDictInto X Tr hK) (hB : ColDictBij X Tr hK) (δ : Hfin X u) (hδ : ∀ k : Hfin X u, δ * k = k * δ)
    (T S : Cu X u hK) (hS : S.1 = rtr X δ T.1) (hT : colDictL X Tr hK T ∈ (D.mem u).A.Mram) :
    colDictL X Tr hK S ∈ (D.mem u).A.Mram := by
  refine ⟨hI S, (Submodule.mem_iInf _).2 fun v => ?_⟩
  have h0 : (D.mem u).A.Nm v (dictA X Tr T.1) = 0 := (Submodule.mem_iInf _).1 hT.2 v
  choose d hd using exists_rtr_dia Tr hK hL v
  have hsum : ∀ P ∈ Cu X u hK, (D.mem u).A.Nm v (dictA X Tr P) = dictA X Tr (∑ a, rtr X (d a) P) := by
    intro P hP
    rw [map_sum, Formalism.BasicNotions.ColumnsAtT.Nm, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (hd a P hP).2.symm
  have hmem : ∑ a, rtr X (d a) T.1 ∈ Cu X u hK := Submodule.sum_mem _ fun a _ => (hd a T.1 T.2).1
  have hz : (⟨_, hmem⟩ : Cu X u hK) = 0 :=
    hB.1 (((hsum T.1 T.2).symm.trans h0).trans (map_zero (colDictL X Tr hK)).symm)
  have hz' : ∑ a, rtr X (d a) T.1 = 0 := congrArg Subtype.val hz
  have e : ∑ a, rtr X (d a) S.1 = rtr X δ (∑ a, rtr X (d a) T.1) := by
    rw [map_sum, hS]
    exact Finset.sum_congr rfl fun a _ => rtr_comm (hδ (d a)) T.1
  show (D.mem u).A.Nm v (dictA X Tr S.1) = 0
  rw [hsum S.1 S.2, e, hz', map_zero, map_zero]

theorem sum_inner_rieszVector_rightTranslate (hK : X.LevelSubgroupCharacter) {ι : Type} [Fintype ι] (s : ι → Hfin X u)
    (hs : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : Ku X u hK), h = iotaF X u γ * s i * (κ : Hfin X u))
    (δ : Hfin X u) (hδ : ∀ k : Hfin X u, δ * k = k * δ) (T T' : Cu X u hK) :
    ∑ i, ⟪shP X u (rtr X δ T'.1) (s i), shP X u (rtr X δ T.1) (s i)⟫_ℂ =
      ∑ i, ⟪shP X u T'.1 (s i), shP X u T.1 (s i)⟫_ℂ := by
  simp only [Formalism.L2.SG.Pf.ColDictPf.rieszVector_rightTranslate]
  refine Formalism.L2.SG.Pf.ColDictPf.sum_reps X u (fun i => s i * δ) s (Ku X u hK) (fun h => ?_) hs
    (fun h => ⟪shP X u T'.1 h, shP X u T.1 h⟫_ℂ)
    (fun γ h κ => Formalism.L2.SG.Pf.ColDictPf.inner_shP_rat X u hK T T' γ h κ)
  have e : ∀ (i : ι) (γ : Gam X u) (κ : Ku X u hK), h * δ⁻¹ = iotaF X u γ * s i * (κ : Hfin X u) ↔
      h = iotaF X u γ * (s i * δ) * (κ : Hfin X u) := by
    intro i γ κ
    rw [mul_inv_eq_iff_eq_mul, mul_assoc _ (κ : Hfin X u) δ, ← hδ κ]
    simp only [mul_assoc]
  simpa only [e] using hs (h * δ⁻¹)

open Formalism.MainNotions Formalism.L2 Formalism.L2.DIV

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : Formalism.L2.RecT ex}

set_option maxHeartbeats 1000000 in

theorem ipC_eq_sum (S : Formalism.L2.SG.SpectralTiesReal.STiesR R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (T T' : Cu S.X u S.Y.hK) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ := by
  have h1 : ∀ P : Cu S.X u S.Y.hK, colDictL S.X (S.tr u) S.Y.hK P = (D.s_Cu u (((S.hI hF).eCu u).symm P)).1 := by
    intro P
    have h := S.colPin hF u (((S.hI hF).eCu u).symm P)
    have h' : @Eq (Cu S.X u S.Y.hK) ((S.hI hF).eCu u (((S.hI hF).eCu u).symm P)) P :=
      ((S.hI hF).eCu u).apply_symm_apply P
    exact congrArg Subtype.val ((congrArg (colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u)) h').symm.trans h)
  have h2 := ((S.hI hF).eCu u).symm.inner_map_map T T'
  have h3 : @inner ℂ (Formalism.L2.SG.PackageTie2.ColT (hF.shInj u)) _ T T' =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ :=
    (Formalism.L2.SG.PackageTie2.inner_colT (hF.shInj u) T T').trans (PiLp.inner_apply _ _)
  have h4 := (congrArg₂ ((D.fm u).ipC 0) (h1 T) (h1 T')).trans (D.s_Cu_isom u _ _).symm
  exact h4.trans (h2.trans h3)

theorem isom_rtr (S : Formalism.L2.SG.SpectralTiesReal.STiesR R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (δ : Hfin S.X u) (hδ : ∀ k : Hfin S.X u, δ * k = k * δ) (T T' P P' : Cu S.X u S.Y.hK)
    (hP : P.1 = rtr S.X δ T.1) (hP' : P'.1 = rtr S.X δ T'.1) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK P) (colDictL S.X (S.tr u) S.Y.hK P') =
      (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') := by
  refine (ipC_eq_sum S hF u P P').trans (Eq.trans ?_ (ipC_eq_sum S hF u T T').symm)
  rw [hP, hP']
  exact sum_inner_rieszVector_rightTranslate S.Y.hK _ (S.Y.colReps u) δ hδ T T'

end GlobalTheory.MiTop.CenIsom

end
