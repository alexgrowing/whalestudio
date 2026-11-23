import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.PassOp

open Formalism.MainNotions.N.PlaceLabelTeichmuller

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

theorem prod_plc (a : ∀ i, MonoidAlgebra ℂ (G i)) (L : List ι) (hL : L.Nodup) :
    (L.map fun i => plc i (a i)).prod = tens (fun j => if j ∈ L then a j else 1) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.not_mem_nil, if_false]
    exact tens_one.symm
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ih hL.2, plc, tens_mul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [hL.1]
    · simp [Function.update_of_ne hj, hj]

end Tensor

local instance factGk (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroGk (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

theorem tw_eta (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv = π := by
  have hsing : ∀ (π' : D.naut.CG a) w, isoLoc D.nd D.naut [⟨a, π', 1⟩] w = D.naut.locG π' w := by
    intro π' w
    show D.naut.lpSum (spehLoc D.nd D.naut ⟨a, π', 1⟩ w) (D.naut.lpZero w) = _
    rw [D.naut.lpSum_zero]
    unfold spehLoc
    simp [D.naut.lpSum_zero, D.naut.lpTw_zero]
  have h := hAN [⟨a, D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      rw [hsing, hsing, D.naut.locG_tw, D.naut.locG_tw]
      exact (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hT _).1)
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem twistIso_eta (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    (L : List (Part D.naut.CG)) (hL : ∀ p ∈ L, 1 ≤ p.a) :
    twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) D.naut.etaTinv = L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    show (⟨p.a, D.naut.tw (D.naut.tw p.π D.naut.etaT) D.naut.etaTinv, p.d⟩ : Part D.naut.CG) ::
      twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) D.naut.etaTinv = p :: L
    rw [ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)), tw_eta D hT hAN (hL p List.mem_cons_self)]

theorem goodPar_iff_goodSig (D : D7) (Sig : List (Part D.naut.CG)) (σ' : D.ntypes.Par)
    (h1 : ∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) :
    D.ntypes.goodPar σ' ↔ goodSig D.nd D.naut Sig := by
  unfold NTypes.goodPar NTypes.goodTuple goodSig
  simp only [D.ntypes.labPar_def, h1]

theorem param_of_Z (D : D7) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h5 : SumRepresentations.adm5 D) (h41 : SumRepresentations.Conclusion41 D)
    (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ D.nd.Z i) (PI : D.naut.AV i) (hPI : D.naut.ptV i PI = some x) :
    ∃ Sig, IsBCV D.nd D.naut i PI
      (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  obtain ⟨P0, hP0, Pa0, hB0, hm⟩ := (D.Z_tie i x).1 hx
  obtain ⟨Pa, hB⟩ := h1 i PI
  have hperm : Pa0.Perm Pa := ((h41 i).2.1 P0 PI (by rw [hP0]; exact Option.some_ne_none x)
    (hP0.trans hPI.symm)).1 Pa0 Pa hB0 hB
  have hm' := hperm.subset hm
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm'
  set m : Part D.naut.CG := ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ with hmdef
  have hperm2 : (l₁ ++ m :: l₂).Perm ((l₁ ++ l₂) ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hB' := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm2 hB
  have hL : ∀ p ∈ l₁ ++ l₂, 1 ≤ p.a := fun p hp => (hB.1 p (by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))).1
  refine ⟨twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT, ?_⟩
  have e : twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT ++ [muPart D.nd D.naut i])
      D.naut.etaTinv = (l₁ ++ l₂) ++ [m] := by
    rw [show twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT ++ [muPart D.nd D.naut i])
        D.naut.etaTinv = twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT) D.naut.etaTinv ++
          twistIso D.nd D.naut [muPart D.nd D.naut i] D.naut.etaTinv from List.map_append ..,
      twistIso_eta D h0.1 h5.1 _ hL]
    rfl
  rw [e]
  exact hB'

theorem eigen_action_at_good_point (D : D7) (Q : PairedCharacterCondition.Pend D) (hSer : GlobalTheory.TypeLeaf.SerLoc D) (h41 : SumRepresentations.Conclusion41 D)
    (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ D.nd.Z i)
    (PI : D.naut.AV i) (hPI : D.naut.ptV i PI = some x) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ D.naut.typeV i PI) :
    (x ∈ D.nd.Zgood i → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F) ∧
    (x ∉ D.nd.Zgood i → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0) := by
  have hon : ∀ σ' : D.ntypes.Par, F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' →
      (D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F) ∧
      (¬ D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0) := fun σ' hF' =>
    idempotent_action_on_forms D (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i)) σ' F fun k v f hf => hSer i σ' k v f F hF' hf
  have hmem : ∀ Sig (σ' : D.ntypes.Par), (∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w) →
      IsBCV D.nd D.naut i PI (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) →
      F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
    intro Sig σ' hσ hB
    have hle : D.naut.typeV i PI ≤ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
      rw [D.mtpar_tie i σ']
      exact le_iSup₂_of_le PI ⟨Sig, fun w => (hσ w).symm, hB⟩ le_rfl
    exact hle hF
  constructor
  · intro hg
    obtain ⟨-, Sig, ⟨P2, hP2, hB2⟩, hgs⟩ := (D.Zgood_tie i x).1 hg
    obtain ⟨Pa, hB⟩ := h1 i PI
    have hperm := ((h41 i).2.1 P2 PI (by rw [hP2]; exact Option.some_ne_none x)
      (hP2.trans hPI.symm)).1 _ Pa hB2 hB
    have hBPI := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hB
    obtain ⟨σ', hσ⟩ := Q.Par_surj i x Sig ⟨P2, hP2, hB2⟩
    exact (hon σ' (hmem Sig σ' hσ hBPI)).1 ((goodPar_iff_goodSig D Sig σ' fun w => (hσ w).symm).2 hgs)
  · intro hg
    obtain ⟨Sig, hB⟩ := param_of_Z D h0 h1 h5 h41 i x hx PI hPI
    obtain ⟨σ', hσ⟩ := Q.Par_surj i x Sig ⟨PI, hPI, hB⟩
    refine (hon σ' (hmem Sig σ' hσ hB)).2 fun hgp => hg ?_
    rw [D.Zgood_tie i x]
    exact ⟨(D.Z_tie i x).1 hx, Sig, ⟨PI, hPI, hB⟩, (goodPar_iff_goodSig D Sig σ' fun w => (hσ w).symm).1 hgp⟩

theorem main : ∀ (D : D7) (Q : PairedCharacterCondition.Pend D), GlobalTheory.Pass.EigSpan Q → GlobalTheory.Pass.CentralElt D → GlobalTheory.TypeLeaf.SerLoc D →
    SumRepresentations.Conclusion41 D → SumRepresentations.tieLab D → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm5 D → KillingConditions.CommutingEndomorphismCondition D := by
  intro D Q hEig hCen hSer h41 _ h0 h1 h5 i _ _
  classical
  let zc : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) →
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    fun p => (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose
  let z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    ∑ p, if goodVec D p then zc p else 0
  have hp : ∀ p, PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (zc p : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • tens (fun kv => ESer D kv (p kv)) := by
    intro p
    obtain ⟨L, hnd, hall, he⟩ := (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose_spec
    rw [he]
    congr 1
    have e1 : (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        L.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, prod_plc _ L hnd]
    congr 1
    funext j
    rw [if_pos (hall j)]
  have hz : PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0 := by
    rw [e0_eq, eGood, Finset.smul_sum, AddSubmonoidClass.coe_finsetSum]
    show MonoidAlgebra.mapRingHom _ (iotaO D.nd D.naut i) _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact hp p
    · simp
  have hcen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
    Subalgebra.mem_center_iff.2 fun b => (goodElement_mem_center_groupAlgebra D b).symm
  have hact : ∀ F, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F := by
    intro F
    rw [hz]
    unfold NTypes.onMt
    rw [dif_pos (Subalgebra.smul_mem _ hcen _), dif_pos hcen, ← LinearMap.smul_apply, ← map_smul]
    rfl
  refine ⟨Q.zO i z, Q.zO_comm i z, ?_, ?_⟩
  · intro x hx u hu
    have hZ : x ∈ D.nd.Z i := (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1
    have := hEig i z x (D.what₂.restRowsFiniteGroupCard : D.nd.O i) (fun PI hPI F hF => by
      rw [hact, (eigen_action_at_good_point D Q hSer h41 h0 h1 h5 i x hZ PI hPI F hF).1 hx, map_natCast]) u hu
    rw [this, ← algebraMap_smul (KK D.nd i) (D.what₂.restRowsFiniteGroupCard : D.nd.O i) u, map_natCast, Int.cast_natCast]
  · intro x hx hxg u hu
    have := hEig i z x 0 (fun PI hPI F hF => by
      rw [hact, (eigen_action_at_good_point D Q hSer h41 h0 h1 h5 i x hx PI hPI F hF).2 hxg, smul_zero, map_zero, zero_smul]) u hu
    rw [this, zero_smul]

end GlobalTheory.PassOp

end
