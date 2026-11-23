import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TPeriodInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite

noncomputable section

namespace GlobalTheory.NRows.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

theorem used_loc (D : D7) (i : D.nd.Loc) : D.nd.mu i = D.what₂.mu0 ∨ ∃ w, D.nd.mu i = D.what₂.muAt w :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

theorem lamPos_of_used {D : D7} (h : LamUsed D) {μ} (hμ : μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : LamPos D μ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h μ hμ ⟨k, by omega⟩

theorem lamLoc {D : D7} (h : LamUsed D) (i : D.nd.Loc) : LamPos D (D.nd.mu i) (D.nd.j i) :=
  lamPos_of_used h (used_loc D i) (D.nd.j_range i).1 (D.nd.j_range i).2

theorem up_injective {D : D7} {μ} {j : ℕ} (h : LamPos D μ j) (hI : DirectSum.IsInternal (D.what₂.isot j)) :
    Function.Injective (D.what₂.thetaT μ j) := by
  have hs : Function.Surjective (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hI.submodule_iSup_eq_top, iSup_le_iff]
    intro σ f hf
    by_cases h0 : D.what₂.isot j σ = ⊥
    · rw [h0] at hf
      rw [(Submodule.mem_bot ℂ).1 hf]
      exact zero_mem _
    · have hl : ((D.what₂.lamP μ j σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ((h σ).2 h0).ne'
      refine ⟨((D.what₂.lamP μ j σ : ℝ) : ℂ)⁻¹ • f, ?_⟩
      rw [map_smul, LinearMap.comp_apply, (h σ).1 f hf, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hi := LinearMap.injective_iff_surjective.2 hs
  rw [LinearMap.coe_comp] at hi
  exact hi.of_comp

theorem rank_of {D : D7} (hI : SumRepresentations.adm8 D) (h : LamUsed D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := by
  intro j hj w hw
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have e : D.what₂.muTw w = D.what₂.muAt w := ((D.what₂.muAt_or w).resolve_left hw).symm
  have a := up_injective (lamPos_of_used h (Or.inr ⟨w, e⟩) h1 h2) (hI j h1 h2)
  have b := up_injective (lamPos_of_used h (Or.inl rfl) h1 h2) (hI j h1 h2)
  unfold SizeData₂.zeroSpaceRankAtPlace SizeData₂.dZ0 Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj a, LinearMap.finrank_range_of_inj b]

theorem not_lamUsed {D : D7} (j : Fin D.R.m) (σ : D.what₂.FT) (hσ : D.what₂.isot (j.1 + 1) σ ≠ ⊥)
    (h0 : D.what₂.thetaP D.what₂.mu0 (j.1 + 1) = 0) : ¬ LamUsed D := by
  intro h
  obtain ⟨f, hf, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have h1 := (h _ (Or.inl rfl) j σ).1 f hf
  have hl : ((D.what₂.lamP D.what₂.mu0 (j.1 + 1) σ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ((h _ (Or.inl rfl) j σ).2 hσ).ne'
  rw [h0, LinearMap.zero_apply] at h1
  exact hne ((smul_eq_zero.1 h1.symm).resolve_left hl)

theorem mtPar_holds (D : D7) : MtParTie D.nd D.naut D.ntypes := D.mtpar_tie

theorem goodIdempotent_iff_rowProjector (D : D7) : GoodIdempotentFixesLocalisationForms D ↔ ∀ (i : D.nd.Loc) (σ' : D.ntypes.Par),
    ∀ F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ', D.ntypes.goodPar σ' → D.what₂.eMt (D.nd.mu i) (D.nd.j i) F = F := by
  simp only [GoodIdempotentFixesLocalisationForms, D.nStage_trivialCharacter_compat.2]

theorem goodIdempotent_of_goodProjector {D : D7} (h : ArithmeticCylinders.Conclusion4 D) : GoodIdempotentFixesLocalisationForms D :=
  fun i σ' F hF hg => (h.2.2.2.2.1 _ _ (D.nd.j_range i).1 (D.nd.j_range i).2 σ' F hF).1 hg

theorem partsGive_of_stmt {D : D7} (h : SumRepresentations.IntegralityFromMetric D) : PartsGive D := fun a _ _ _ _ _ _ => h a

theorem baseChange_preserves_unitary_of {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (h : PartsGive D) (I : Inputs hL D) (a : RowsA D) (b : RowsB D) :
    SumRepresentations.Conclusion1 D :=
  h ⟨⟨a.tie0, I.hypO, base_change_automorphic_of D I.bc I.c1, a.a2, b.a3, b.a4, a.a5⟩, a.temp⟩ a.tieLab b.rowSize a.hecke
    (lamLoc I.lam) b.thetaOne a.g4p

theorem an_of {D : D7} (h : SumRepresentations.adm5 D) : IsobaricCuspidalStrongMultiplicityOne D.nd D.naut ∧ IsobaricDiscreteSelfDualStrongMultiplicityOne D.nd D.naut := ⟨h.1, h.2.1⟩

section Read
variable {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
  (X : GlobalTheory.NJoin.RealAt D cf nch tp)

theorem exists_vec {μ} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1)) :
    ∃ y, X.R.extV j (X.tupT μ) y = X.fn hμ j f := (X.IL.jMt μ hμ j f).2.1

theorem goodVt_zero (j : Fin D.R.m) (t : X.T) : GlobalTheory.DownLift.GoodVt X.R j t 0 := by
  intro l
  have : (fun h => l (X.R.extV j t 0 h)) = 0 := by
    funext h
    simp
  rw [this, map_zero]

theorem good_of_fixed (h : GoodIdempotentReadsAsGoodTypeProjector X) {μ} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1))
    (y) (hy : X.R.extV j (X.tupT μ) y = X.fn hμ j f) (hf : D.what₂.eMt μ (j.1 + 1) f = f) :
    GlobalTheory.DownLift.GoodVt X.R j (X.tupT μ) y := by
  have h2 : D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f = f := by rw [← D.nStage_trivialCharacter_compat.2]; exact hf
  have h3 := h μ hμ j f y hy
  exact h3.1 h2

end Read

def PartNe (D : D7) : Prop := 0 < D.R.m ∧ ∃ σ : D.what₂.FT, ∀ j : Fin D.R.m, ∃ f ∈ D.what₂.isot (j.1 + 1) σ, f ≠ 0

theorem lamUsed_of_id (D : D7) (h : ∀ μ j f, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = f)
    (h1 : ∀ μ j σ, D.what₂.lamP μ j σ = 1) : LamUsed D := fun μ _ j σ =>
  ⟨fun f _ => by rw [h, h1, Complex.ofReal_one, one_smul], fun _ => by rw [h1]; exact one_pos⟩

theorem lamUsed_model : ∃ D : D7, LamUsed D ∧ PartNe D :=
  ⟨GlobalTheory.Core.Int.Inhab.recOne, lamUsed_of_id _
    (fun _ _ f => congrArg (fun g => g f) (LinearMap.adjoint_id (𝕜 := ℂ) (E := Formalism.BasicNotions.Examples₂.NZ.En 1))) (fun _ _ _ => rfl),
    by decide, (), fun _ => ⟨Formalism.BasicNotions.Examples₂.NZ.eb 1 0,
      (show Formalism.BasicNotions.Examples₂.NZ.eb 1 0 ∈ Submodule.span ℂ (Formalism.BasicNotions.Examples₂.NZ.eb 1 '' {_σ | () = ()}) from
        Submodule.subset_span ⟨0, rfl, rfl⟩),
      (Formalism.BasicNotions.Examples₂.NZ.eb 1).toBasis.ne_zero 0⟩⟩

theorem rowsC_of_isEmpty (D : D7) [h : IsEmpty D.nd.Loc] : RowsC D :=
  ⟨fun _ _ _ _ _ i => h.elim i, fun i => h.elim i, fun i => h.elim i, fun i => h.elim i, fun i => h.elim i,
    fun i => h.elim i⟩

theorem serLoc_of_isEmpty (D : D7) [h : IsEmpty D.nd.Loc] : GlobalTheory.TypeLeaf.SerLoc D := fun i => h.elim i

theorem definite_of_tied {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (letI := D.host.cmStar; (D.sp.V j).IsDefinite) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have h := T.X.given.core.models.vpos ⟨k, by omega⟩
  intro τ
  exact Or.inl (h τ)

theorem loc_of_tied {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (w : D.what₂.places.Pl) (hw : D.what₂.muAt w ≠ D.what₂.mu0) [Nontrivial (T.P.H.cover.B.V j w)] :
    ∃ i : D.nd.Loc, D.nd.j i = j ∧ D.nd.w i = w := by
  haveI : Nontrivial (Formalism.L2.heckeAlg T.P.H.cover.B j w) := inferInstance
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (Formalism.L2.heckeAlg T.P.H.cover.B j w)
  obtain ⟨i, hi, -⟩ := T.P.H.cover.mx_all j w h1 h2 hw I hI
  exact ⟨i, (D.nd.locs_mem _ _ _).1 hi⟩

theorem eq_zero_of_good {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) (h : GoodIdempotentReadsAsGoodTypeProjector X) {μ} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m)
    (h0 : D.what₂.eMt μ (j.1 + 1) = 0) (f : D.what₂.Mt μ (j.1 + 1)) (y) (hy : X.R.extV j (X.tupT μ) y = X.fn hμ j f)
    (hg : GlobalTheory.DownLift.GoodVt X.R j (X.tupT μ) y) : f = 0 := by
  have h2 := (h μ hμ j f y hy).2 hg
  rw [← D.nStage_trivialCharacter_compat.2, h0] at h2
  exact h2.symm

theorem loc_of_inputs {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (I : Inputs hL D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (σ : D.what₂.FT) (hσ : D.what₂.isot j σ ≠ ⊥) (w : D.what₂.places.Pl) (hw : D.what₂.muAt w ≠ D.what₂.mu0) :
    ∃ i : D.nd.Loc, D.nd.j i = j ∧ D.nd.w i = w := by
  have e : D.what₂.muTw w = D.what₂.muAt w := ((D.what₂.muAt_or w).resolve_left hw).symm
  have a := up_injective (lamPos_of_used I.lam (Or.inr ⟨w, e⟩) h1 h2) (I.isot j h1 h2)
  obtain ⟨f, -, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have hne : D.what₂.thetaT (D.what₂.muTw w) j f ≠ 0 := fun h => hf (a (h.trans (map_zero _).symm))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hidx : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h3 := (D.what₂.jMt_basis (D.what₂.muTw w) j b).2
    rw [Set.range_eq_empty, Submodule.span_empty] at h3
    exact hne ((Submodule.mem_bot ℂ).1 (h3 ▸ Submodule.mem_top))
  obtain ⟨k⟩ := hidx
  haveI : Nontrivial (I.P.H.cover.B.V j w) := ⟨⟨_, 0, (I.P.H.cover.B.iV_basis j w b).1.ne_zero k⟩⟩
  exact loc_of_tied I.toRowSideFamily j h1 h2 w hw

theorem rows_model : ∃ D : D7, LamUsed D ∧ PartNe D ∧ SumRepresentations.adm8 D ∧ ∀ L : SizeData₂ D, TwistedPlaces.adm3 L := by
  have h : LamUsed GlobalTheory.Core.Int.Inhab.recOne := lamUsed_of_id _
    (fun _ _ f => congrArg (fun g => g f) (LinearMap.adjoint_id (𝕜 := ℂ) (E := Formalism.BasicNotions.Examples₂.NZ.En 1))) (fun _ _ _ => rfl)
  have hp : PartNe GlobalTheory.Core.Int.Inhab.recOne := ⟨by decide, (), fun _ => ⟨Formalism.BasicNotions.Examples₂.NZ.eb 1 0,
      (show Formalism.BasicNotions.Examples₂.NZ.eb 1 0 ∈ Submodule.span ℂ (Formalism.BasicNotions.Examples₂.NZ.eb 1 '' {_σ | () = ()}) from
        Submodule.subset_span ⟨0, rfl, rfl⟩),
      (Formalism.BasicNotions.Examples₂.NZ.eb 1).toBasis.ne_zero 0⟩⟩
  have h8 : SumRepresentations.adm8 GlobalTheory.Core.Int.Inhab.recOne := by
    intro j _ _
    haveI : Unique GlobalTheory.Core.Int.Inhab.recOne.what₂.FT := inferInstanceAs (Unique Unit)
    have ht : ∀ σ, GlobalTheory.Core.Int.Inhab.recOne.what₂.isot j σ = ⊤ := fun _ => by
      show Submodule.span ℂ (Formalism.BasicNotions.Examples₂.NZ.eb 1 '' {_σ | () = ()}) = ⊤
      have : ({_σ | () = ()} : Set (Fin 1)) = Set.univ := by ext; simp
      rw [this, Set.image_univ]
      exact (Formalism.BasicNotions.Examples₂.NZ.eb 1).toBasis.span_eq
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨iSupIndep_subsingleton _, ?_⟩
    rw [eq_top_iff, ← ht default]
    exact le_iSup _ default
  exact ⟨_, h, hp, h8, rank_of h8 h⟩

theorem baseChangeConditions_of_tied {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) : GlobalDatumCompatibility D :=
  GlobalTheory.DesignBC.jointCond_of_definite D (definite_of_tied T)

theorem bc_iff_of_tied {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) :
    SphericalInertData.Conclusion1 D ↔ ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ π : D.nbc.AU j, SphericalInertData.SphInert D.nd D.naut D.nbc j π →
      ∃ Pa, SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa :=
  ⟨fun h j h1 h2 => h (baseChangeConditions_of_tied T).1 (hypCM_of D (baseChangeConditions_of_tied T)) j h1 h2 (nV_pos D) (definite_of_tied T j h1 h2),
    fun h _ _ j h1 h2 _ _ => h j h1 h2⟩

theorem eC_eq {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) : ∃ eR : X.G ≃* G0g D.nd, ∀ g,
      Formalism.IndefR.Links.RealDat.eC (A := X.A) D.what₂.embLL g = D.ntypes.e0.coeff (eR g) := by
  obtain ⟨eR, -, -, h, -⟩ := X.given.core.grp.record
  exact ⟨eR, h⟩

theorem unitaryRealisationReading_of_idempotent_acts_via_levelGroup {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (h : ∀ μ (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1))
      (l : (X.R.cV j).W →ₗ[ℂ] ℂ),
      Formalism.IndefR.Links.gaL (Formalism.IndefR.Links.Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ)) X.R.eG
        (Formalism.IndefR.Links.RealDat.eC (A := X.A) (Formalism.IndefR.Links.sg0 D X.A)) (fun g => l (X.fn hμ j f g)) =
        fun g => l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g)) : GoodIdempotentReadsAsGoodTypeProjector X := by
  intro μ hμ j f y hy
  unfold GlobalTheory.DownLift.GoodVt
  rw [hy]
  constructor
  · intro hf l
    rw [h μ hμ j f l, hf]
  · intro hg
    apply (X.IL.jMt μ hμ j).injective
    apply Subtype.ext
    funext g
    have key : ∀ l : (X.R.cV j).W →ₗ[ℂ] ℂ,
        l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g - X.fn hμ j f g) = 0 := fun l => by
      rw [map_sub, sub_eq_zero]
      exact congrFun ((h μ hμ j f l).symm.trans (hg l)) g
    exact sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (V := (X.R.cV j).W) _).1 key)

theorem not_rows_of_dup (D : D7) (ν ν' : D.naut.CG 1) (hne : ν ≠ ν') (h : ∀ w, D.naut.locG ν w = D.naut.locG ν' w) :
    ¬ Rows D := fun r => hne (r.a.hecke ν ν' (Filter.Eventually.of_forall fun w _ => h w))

theorem lift_ne {D : D7} (h : LamUsed D) (i : D.nd.Loc) (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j i) σ ≠ ⊥) :
    (D.what₂.isot (D.nd.j i) σ).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) ≠ ⊥ := by
  intro h0
  obtain ⟨f, hf, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have h1 := (h.loc i σ).1 f hf
  have h2 : D.what₂.thetaT (D.nd.mu i) (D.nd.j i) f = 0 :=
    (Submodule.mem_bot ℂ).1 (h0 ▸ Submodule.mem_map_of_mem hf)
  have hl : ((D.what₂.lamP (D.nd.mu i) (D.nd.j i) σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ((h.loc i σ).2 hσ).ne'
  rw [h2, map_zero] at h1
  exact hne ((smul_eq_zero.1 h1.symm).resolve_left hl)

end GlobalTheory.NRows.Model

end
