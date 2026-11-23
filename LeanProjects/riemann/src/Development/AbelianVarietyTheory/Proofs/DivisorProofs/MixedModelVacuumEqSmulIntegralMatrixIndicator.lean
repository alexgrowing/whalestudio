import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarFiniteTensorEqDatumSmallModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.MixVacSmall

open GlobalTheory.SmallDat GlobalTheory.SmallPlaces
open GlobalTheory.BigDat (atW)

theorem mem_latO_iff_at {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (fS : IsFrame βS ΛS) (fT : IsFrame βT ΛT)
    {w : Pl D.host.E} (he : IsIdemSum (atPl w 1) {w})
    (hw : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (x : WO S T) (hx : IsHalf (atPl w 1) x) :
    x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      ∀ a b, (((loc w βT)⁻¹).val * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (atW w) * (loc w βS).val :
        Matrix (Fin T.rank) (Fin S.rank) (Kw w)) a b ∈ (ValuativeRel.valuation (Kw w)).integer := by
  classical
  rw [GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int D S T ΛS ΛT βS βT hS hT fS fT {w} _ he (by simpa using hw) _ hx]
  have hmap : ∀ Q, (frMapO S T βS βT x).map (cpt (D := D) Q) =
      ((loc Q βT)⁻¹).val * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (atW Q) * (loc Q βS).val := by
    intro Q
    rw [← map_inv]
    unfold frMapO
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  unfold IsIntM
  refine ⟨fun h a b => ?_, fun h a b => ?_⟩
  · have := (mem_OA_iff _).1 (h a b) w
    rw [← hmap, Valuation.mem_integer_iff, (Good.isEquiv_Kw w).le_one_iff_le_one]
    exact this
  · refine (mem_OA_iff _).2 fun Q => ?_
    by_cases hQ : Q = w
    · subst hQ
      have := h a b
      rw [← hmap, Valuation.mem_integer_iff, (Good.isEquiv_Kw Q).le_one_iff_le_one] at this
      exact this
    · have h0 : (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (atW Q) = 0 := by
        refine Matrix.ext fun a b => ?_
        calc atW Q (x a b) = atW Q (atPl w 1 * x a b) := congrArg _ (hx a b).symm
          _ = 0 := by rw [map_mul, GlobalTheory.BigDat.atW_atPl_ne hQ, zero_mul]
      have h1 := congrFun (congrFun (hmap Q) a) b
      rw [h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.map_apply, Matrix.zero_apply] at h1
      rw [h1]
      exact zero_mem _

theorem forall_cast_transpose {K : Type} {m m' n n' : ℕ} (hm : m' = m) (hn : n' = n) (A : Matrix (Fin m) (Fin n) K)
    (p : K → Prop) : (∀ r s, p ((A.submatrix (Fin.cast hm) (Fin.cast hn))ᵀ r s)) ↔ ∀ a b, p (A a b) := by
  subst hm hn
  exact forall_comm

theorem mem_latPtS_iff {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (B : Frames G) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) (e : Num G i j) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    {x : PtS G i j} (hx : x ∈ mixHalfS e (atPl w 1)) (hat : At (evFin D.host.F (w.under (𝓞 D.host.F))) x) :
    x ∈ latPtS t e (w.under (𝓞 D.host.F)) ↔ ∀ r s, mixCoS B t e w x r s ∈ (ValuativeRel.valuation (Kw w)).integer := by
  classical
  obtain ⟨_, ⟨es, hes, -⟩, -⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G t
  have h1 : Formalism.L2.NTheta.IsIdemAt (atPl w 1) w := GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (hes w hw) ▸ hes w hw
  have he : IsIdemSum (atPl w 1) {w} :=
    ⟨⟨fun _ => atPl w 1, fun PP h => by rw [Finset.mem_singleton] at h; subst h; exact h1, by simp⟩, h1.1.2.1⟩
  have hb : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h => hst.2 w hw (by
    have := Ideal.mul_mem_left _ ((D.host.d : ℕ) : 𝓞 D.host.E) h
    convert this using 1
    push_cast
    ring)
  have sW : IsSelfDualC (spW₁ G i j) (G.Λ (.grid (i : ℕ) (j : ℕ))) :=
    (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have sV : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have sV₁ : IsSelfDualC (negSp (spV₁ G i j)) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    isSelfDualC_neg (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have kA := mem_latO_iff_at sW sV (B.isFrame_β hL i.2.le j.2.le) (B.isFrame_β hL i.2.le j.2) he hb (mapA t e x) hx.1
  have kB := mem_latO_iff_at sV₁ sW (B.isFrame_β hL i.2 j.2.le) (B.isFrame_β hL i.2.le j.2.le) he hb (mapB e x) hx.2
  have cA := forall_cast_transpose (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩)
    (rank_vertex G t w (X := (i, j)) ⟨i.2.le, j.2.le⟩)
    (((loc w (B.β i (j + 1)))⁻¹).val * (mapA t e x).map (atW w) * (loc w (B.β i j)).val)
    (· ∈ (ValuativeRel.valuation (Kw w)).integer)
  have cB := forall_cast_transpose (rank_vertex G t w (X := (i, j)) ⟨i.2.le, j.2.le⟩)
    (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩)
    (((loc w (B.β i j))⁻¹).val * (mapB e x).map (atW w) * (loc w (B.β (i + 1) j)).val)
    (· ∈ (ValuativeRel.valuation (Kw w)).integer)
  rw [mixCoS_eq]
  refine ⟨fun h r s => ?_, fun h => ⟨hat, kA.2 (cA.1 fun r s => h r (.inl s)), kB.2 (cB.1 fun r s => h s (.inr r))⟩⟩
  rcases s with s | s
  · exact cA.2 (kA.1 h.2.1) r s
  · exact cB.2 (kB.1 h.2.2) s r

theorem mixVac_eq_indicator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToB G t i j w, IsMixModelB W B t e Γ w ι →
      ι (Γ.M'.vac _) = ι (Γ.M'.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h hT hti w hw I hI
  classical
  have hG : Γ.M'.IsGood W.ψ := h.ψ ▸ hT.geo.hM'
  obtain ⟨hid, -⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have hh := halves_split hL W t i j e Γ h.JW₁ h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := mixCoS_spec B t i j e w
  have hv := lagr_vac hI (hG.vac _).1 (hG.vac _).2.1 (latPtS t e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _ (latPtS_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) hco.2.1 hh.2.2.2.1
  funext Z
  obtain ⟨x, hx, rfl⟩ := hco.2.1 Z
  have k := mem_latPtS_iff hL B t i j hst e hw hx (hh.1 x hx)
  refine (hv.2 x hx).trans ?_
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hl : x ∈ latPtS t e (w.under (𝓞 D.host.F))
  · rw [Set.indicator_of_mem hl, Set.indicator_of_mem (s := {Z : MatB G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer})
      (a := mixCoS B t e w x) (k.1 hl), Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem (s := {Z : MatB G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer})
      (a := mixCoS B t e w x) (fun h' => hl (k.2 h')), mul_zero]

end GlobalTheory.TopFlip.MixVacSmall

end
