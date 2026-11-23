import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMoveArgumentsLastRowVertexStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConjLevelMovesVacuumByCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionMovesStandardVacuumTopNodeEqCharSmulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingColumnArgsMovedPointConjAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopLevelInv

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {Γ : Grid k}

theorem isAdmissible_flips {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e) :
    ∀ (l : List (ℕ × ℕ)) (St : Γ.PiLocalization₂), (∀ x ∈ l, CondLE ϖ e (Γ.nu x.1 x.2)) → CanFlip St.path l →
      (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) → St.IsAdmissible .one ϖ e →
      (St.flips .one ψ ϖ e l).IsAdmissible .one ϖ e := by
  intro l
  induction l with
  | nil => intro St _ _ _ hT; exact hT
  | cons x l ih =>
    intro St hν hc hJ hT
    obtain _ | ⟨hp, hc'⟩ := hc
    refine ih (St.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (GlobalTheory.T.splitThetaGrid_isAdmissible_flipTensor ψ ϖ e hϖ hψ he St x (hν x List.mem_cons_self) hp hJ hT)
    change IsOpen (Γ.flipLevel x.1 x.2 St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ Γ.flipLevel x.1 x.2 St.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

omit [MeasurableSpace k] [BorelSpace k] in

theorem prod_edgeFactor_col {j : ℕ} (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k)
    (hg : valuation k (gdet g : k) = 1) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (Γ.m, j + 1) g))).prod =
      (Γ.mu (j + 1) (gdet g) : ℂ) * (((Γ.mu (j + 1 + 1) (gdet g))⁻¹ : ℂˣ) : ℂ) := by
  have hd : ∀ Y, gdet ((Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) Y) = if Y = (Γ.m, j + 1) then gdet g else 1 := fun Y => by
    split_ifs with h
    · subst h; simp
    · simp [h]
  have hv : ∀ Y, valuation k (((if Y = (Γ.m, j + 1) then gdet g else 1 : kˣ)⁻¹ : kˣ) : k) = 1 := fun Y => by
    split_ifs
    · rw [Units.val_inv_eq_inv_val, map_inv₀, hg, inv_one]
    · simp
  have hf : ∀ b, Γ.edgeFactor .one (Pi.mulSingle (Γ.m, j + 1) g) b =
      (Γ.kappa b b.src (if b.src = (Γ.m, j + 1) then gdet g else 1) : ℂ) *
        (((Γ.kappa b b.tgt (if b.tgt = (Γ.m, j + 1) then gdet g else 1))⁻¹ : ℂˣ) : ℂ) := fun b => by
    simp only [Grid.edgeFactor, Assignment.read, gdet_invT, hd, apow_of_valuation_eq_one (hv _), mul_one]
  rw [oppositePath, List.map_append, List.prod_append, List.map_map, List.map_map, List.map_reverse, List.prod_reverse,
    List.prod_eq_one, one_mul, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
  · simp only [Function.comp, hf, Finset.prod_mul_distrib]
    rw [Finset.prod_eq_single j, Finset.prod_eq_single (j + 1)]
    · simp only [if_true, Grid.kappa, Grid.blockChar, MonoidHom.div_apply]
      simp only [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
      field_simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h; omega
    · intro b _ hb; simp [hb]
    · intro h; simp at h; omega
  · intro c hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
    simp [hf, show Γ.m ≠ j + 1 by omega]

theorem datum_colMove (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] {J : Γ.Level} (keep : Bool)
    (ρ : Reps hs J) {F : Γ.Args → ℂ} (hF : Γ.IsAdmissible .one (oppositePath Γ.m) J F) (β : Cosets hs J) {j : ℕ}
    (hj : j + 1 < Γ.m) (hJ : J (Γ.m, j + 1) ≤ KO k _) {κ : GL (Fin (topRank Γ (j + 1))) k}
    (hκ : κ ∈ (unfTerm ψ ν keep ρ F β).pr (j + 1) j.succ_pos hj) (x : ColArgs Γ) (y : RowArgs Γ) :
    (Γ.mu (j + 1) (gdet κ) : ℂ) * (((Γ.mu (j + 1 + 1) (gdet κ))⁻¹ : ℂˣ) : ℂ) *
      (unfTerm ψ ν keep ρ F β).datum (colMove j κ x) y = (unfTerm ψ ν keep ρ F β).datum x y := by
  obtain ⟨u, hu, v, hv, h, hdet⟩ := exists_of_mem_symPr hs hj hκ
  have hu1 : valuation k (gdet u : k) = 1 := valuation_gdet_of_mem_KO (hJ hu)
  set h' := ρ.elt β
  set g := h' (Γ.m, j + 1) * u * (h' (Γ.m, j + 1))⁻¹ with hg
  have hgd : gdet g = gdet κ := by
    rw [← gdet_toFrame hs hj, h, gdet_mul, gdet_of_mem_symN hv, one_mul, gdet_embX]
  have hin : (Γ.m, j + 1) ∈ innerVertices (oppositePath Γ.m) := by
    obtain ⟨m, hm⟩ : ∃ m, Γ.m = m + 1 := ⟨Γ.m - 1, by omega⟩
    refine List.mem_map.2 ⟨.theta Γ.m j, ?_, rfl⟩
    rw [oppositePath, List.tail_append_of_ne_nil (by simp; omega)]
    exact List.mem_append_right _ (by simp; omega)
  have hcomm : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) * h' = h' * Pi.mulSingle (Γ.m, j + 1) u := by
    funext Y
    by_cases hY : Y = (Γ.m, j + 1)
    · subst hY; simp [hg]
    · simp [hY]
  have hinv : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (Γ.m, j + 1) g) (Γ.pathAct .one (oppositePath Γ.m) h' F) =
      Γ.pathAct .one (oppositePath Γ.m) h' F := by
    rw [← Grid.pathAct_mul, hcomm, Grid.pathAct_mul, hF _ hin u hu]
  have hmv : moved Γ keep h' F = fun z => ((Γ.mu (j + 1) (gdet κ) : ℂ) * (((Γ.mu (j + 1 + 1) (gdet κ))⁻¹ : ℂˣ) : ℂ)) *
      moved Γ keep h' F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) z) := by
    funext z
    have := congrFun hinv z
    rw [Grid.pathAct, prod_edgeFactor_col hj g (by rw [hgd, hdet, hu1]), hgd] at this
    rw [moved, moved, ← this]
    ring
  change _ * flatTensor hs ψ ν (moved Γ keep h' F) _ _ = flatTensor hs ψ ν (moved Γ keep h' F) _ _
  rw [← GlobalTheory.T.flatTensor_moveArguments_lastRow_vertex hs ψ ν (moved Γ keep h' F) j hj g κ (by rw [hdet, hu1]) v hv h x y]
  conv_rhs => rw [hmv]
  simp only [flatTensor, flatIntegrand, mul_assoc, integral_const_mul]

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem isAdmissible_Tflip {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    (locGrid G t w).IsAdmissible .one (oppositePath D.R.m) (givenLevel G t w) (Tflip W B t Φ w) := by
  have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    rw [← Grid.alpha_div_beta]
    exact (hg.square i hi j hj).condν
  rw [← (flipStage_path_level t w B W Φ).1, ← (flipStage_path_level t w B W Φ).2]
  exact (isAdmissible_flips h00.unif h00.cond h00.one_le (flipOrder D.R.m) (givenStage t w B Φ) hν (canFlip_flipOrder _).1
    (fun X => GivenAdm.givenLevel_open hL hw X) (GivenAdm.givenStage_isAdmissible hL B t Φ hw)).invariant

theorem vac_ne_zero (S : GridChoice W U) {p : Pair T} (hp : DefPair D.R.m p) : S.Z.vac p ≠ 0 := fun h0 => by
  obtain ⟨⟨q, hq⟩, hall⟩ := (S.Z.vac_is p hp).2.norm
  have := hall q hq
  rw [h0] at this
  simp [nrm2] at this

theorem smul_unique {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (om : H →* Module.End ℂ M) {f f' : M} (hf : f ≠ 0)
    {g : H} {c c' : ℂ} (h : om g f = c • f') (h' : om g f = c' • f') : c = c' := by
  have hf' : f' ≠ 0 := fun h0 => hf (by
    have := congrArg (om g⁻¹) h
    rwa [h0, smul_zero, map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this)
  exact smul_left_injective ℂ hf' (h.symm.trans h')

theorem local_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ}, β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    (∀ d ∈ τ.support, ∀ j', (d.1 j').e = e) →
    ∀ (T₁ : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)) (T₂ : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ)),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) T₁ →
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) T₂ →
    ∀ c₁ c₂ : ℂ, W.om (.top t j) (1, ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        c₁ • T₁ (fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x)) →
      W.om (.top t (j + 1)) (((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        c₂ • T₂ (fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x)) →
    ∀ (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (c₁ * c₂) * (∏ j', movedFn S d j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) j' (x j')) * ∏ i, (d.2 i).fn (y i)) =
        τ.sum fun d a => a * (∏ j', (d.1 j').fn (x j')) * ∏ i, (d.2 i).fn (y i) := by
  intro D T L sc G W U S t μ₀ hL hde hc ht Φ β τ _ hexp j hj k hk e he hte T₁ T₂ hT₁ hT₂ c₁ c₂ hc₁ hc₂ x y
  classical
  have e₁ := smul_unique _ (vac_ne_zero S (p := .top t j) (show j + 1 ≤ D.R.m by omega)) hc₁
    (GlobalTheory.T.weil_conj_level_moves_vacuum_by_character S hL ht j hj k hk e he T₁ hT₁)
  have e₂ := smul_unique _ (vac_ne_zero S (p := .top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)) hc₂
    (GlobalTheory.T.weilAction_moves_standardVacuum_topNode_eq_char_smul S hL ht j hj k hk e he T₂ hT₂)
  obtain ⟨e', -, hsupp, hF⟩ := hexp
  set g : FinPt G (.top (j + 1)) := (S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) with hg
  have hhalf : ∀ j', IsHalf e' (movedPt t j hj g x j') ↔ IsHalf e' (x j') := fun j' => by
    rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1
    · simp only [movedPt, Function.update_self]; exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | h2
    · simp only [movedPt, Function.update_of_ne h1, Function.update_self]; exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    · simp only [movedPt, Function.update_of_ne h1, Function.update_of_ne h2]
  have hL' : (τ.sum fun d a => a * (c₁ * c₂) * (∏ j', movedFn S d j hj g j' (x j')) * ∏ i, (d.2 i).fn (y i)) =
      c₁ * c₂ * τ.sum fun d a => a * (∏ j', (d.1 j').fn (movedPt t j hj g x j')) * ∏ i, (d.2 i).fn (y i) := by
    simp only [Finsupp.sum, Finset.mul_sum, movedFn_apply]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hL']
  have hzero : ∀ x' : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)),
      ¬ ((∀ j', IsHalf e' (x' j')) ∧ ∀ i, IsHalf e' (y i)) →
      (τ.sum fun d a => a * (∏ j', (d.1 j').fn (x' j')) * ∏ i, (d.2 i).fn (y i)) = 0 := fun x' hx' => by
    refine Finset.sum_eq_zero fun d hd => ?_
    by_contra h0
    refine hx' ⟨fun j' => ?_, fun i => ?_⟩
    · rw [← ((hsupp d hd).1 j').2.1]
      exact (d.1 j').sb.1 _ fun h => h0 (by beta_reduce; rw [Finset.prod_eq_zero (f := fun j' => (d.1 j').fn (x' j')) (Finset.mem_univ j') h]; simp)
    · rw [← ((hsupp d hd).2 i).2.1]
      exact (d.2 i).sb.1 _ fun h => h0 (by beta_reduce; rw [Finset.prod_eq_zero (f := fun i => (d.2 i).fn (y i)) (Finset.mem_univ i) h]; simp)
  by_cases hx : (∀ j', IsHalf e' (x j')) ∧ ∀ i, IsHalf e' (y i)
  · rw [hF _ y (fun j' => (hhalf j').2 (hx.1 j')) hx.2, hF x y hx.1 hx.2, e₁, e₂, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [GlobalTheory.T.unfoldingColumnArgs_movedPoint_conj_atPlace S ht j hj k w.1 w.2 x]
    haveI := (isUnitVol_unitVol w.1).1
    exact datum_colMove (Γ := locGrid G t w.1) one_le_sLen _ _ _ _ (isAdmissible_Tflip hL W S.B t Φ hde hc w.2) (β w) hj
      (givenLevel_col t w.1 j).le (kapAt_mem S hj hk w) _ _
  · rw [hzero x hx, hzero _ fun h => hx ⟨fun j' => (hhalf j').1 (h.1 j'), h.2⟩, mul_zero]

end GlobalTheory.TopLevelInv

end
