import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.TermTieOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Witt

variable {D : D7} (X : HidaSetting D)

structure WittDat where
  δ : D.what₂.Word → ((VS D).V ≃ₗ[D.host.E] (VS D).V)
  isom : ∀ u, δ u ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT
  e_eq : ∀ u a, δ u (X.eX a) = D.sp.hypE a
  z_eq : ∀ u, δ u (X.zu u) = D.zmOf u

def WittExists : Prop := Nonempty (WittDat X)

variable {X}

variable (W : WittDat X)

def FlagOfWord (u : D.what₂.Word) : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E) :=
  Formalism.L2.SG.Saturated.mapFlag (W.δ u) (W.isom u) (X.Fu u)

theorem F0rec_e (u : D.what₂.Word) : (FlagOfWord W u).e = D.sp.hypE := by
  funext a
  show W.δ u ((X.Fu u).e a) = D.sp.hypE a
  rw [X.Fu_e u]
  exact W.e_eq u a

theorem F0rec_z_eq_zmOf (u : D.what₂.Word) : (FlagOfWord W u).z = D.zmOf u := by
  show W.δ u (X.Fu u).z = D.zmOf u
  rw [X.flagZVector u]
  exact W.z_eq u

theorem mapL_lf (u : D.what₂.Word) : mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) = lf D (FlagOfWord W u) := rfl

def rowsRec (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word) : Finset (Submodule (𝓞 D.host.E) (VS D).V) :=
  (Y.what₂ u).image (Formalism.HermitianLatticesTheory.gmap (W.δ u))

end Witt

section Iso

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT)

include hβ in
theorem zhat_mapFlag (F : FlagG S r T) (F' : FlagG S r T') :
    Formalism.MainNotions.S.Zhat (Formalism.L2.SG.Saturated.mapFlag β hβ F) (Formalism.L2.SG.Saturated.mapFlag β hβ F') = Formalism.MainNotions.S.Zhat F F' := by
  funext a b
  simp only [Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, Formalism.L2.SG.Saturated.fvec_mapFlag, Formalism.L2.SG.Saturated.isom_apply hβ]

include hβ in
theorem gflag_mapFlag (F : FlagG S r T) (F' : FlagG S r T') :
    Formalism.MainNotions.S.Gflag (Formalism.L2.SG.Saturated.mapFlag β hβ F) (Formalism.L2.SG.Saturated.mapFlag β hβ F') = Formalism.MainNotions.S.Gflag F F' := by
  simp only [Formalism.MainNotions.S.Gflag, Formalism.MainNotions.S.Dl, zhat_mapFlag β hβ]

include hβ in
theorem zhatL_mapL (F : LFlag S r T) (F' : LFlag S r T') :
    ZhatL (mapL β hβ F) (mapL β hβ F') = ZhatL F F' := zhat_mapFlag β hβ F.fl F'.fl

include hβ in
theorem gval_mapL (F : LFlag S r T) (F' : LFlag S r T') : Gval (mapL β hβ F) (mapL β hβ F') = Gval F F' := gflag_mapFlag β hβ F.fl F'.fl

include hβ in
theorem inSF_mapL (F : LFlag S r T) (F' : LFlag S r T') :
    Formalism.L2.SG.FourParts.InSF (mapL β hβ F) (mapL β hβ F') ↔ Formalism.L2.SG.FourParts.InSF F F' := by
  unfold Formalism.L2.SG.FourParts.InSF
  rw [Formalism.L2.SG.Pf.Xsp_mapL (β := β) (hβ := hβ)]
  simp only [Formalism.L2.SG.Pf.Xflag_mapL (β := β) (hβ := hβ)]
  simp only [Submodule.mem_map_equiv, Formalism.L2.SG.Saturated.mapL, Formalism.L2.SG.Saturated.mapFlag, map_sub,
    LinearEquiv.symm_apply_apply]

include hβ in
theorem isIdF_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Formalism.L2.SG.FourParts.IsIdF (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') ↔
      Formalism.L2.SG.FourParts.IsIdF Λ F F' := by
  unfold Formalism.L2.SG.FourParts.IsIdF
  rw [Formalism.L2.SG.Pf.Xsp_mapL (β := β) (hβ := hβ)]
  constructor
  · rintro ⟨n, hn, h1, h2⟩
    refine ⟨β⁻¹ * n * β, (Formalism.L2.SG.Pf.mem_NLam_map (β := β) (hβ := hβ) Λ F n).1 hn, fun a => ?_, ?_⟩
    · have h := h1 a
      change n (β (F.fl.e a)) = β (F'.fl.e a) at h
      change β.symm (n (β (F.fl.e a))) = F'.fl.e a
      rw [h, LinearEquiv.symm_apply_apply]
    · rw [Submodule.mem_map_equiv] at h2
      change β.symm (n (β F.fl.z) - β F'.fl.z) ∈ Xsp F at h2
      change β.symm (n (β F.fl.z)) - F'.fl.z ∈ Xsp F
      rwa [map_sub, LinearEquiv.symm_apply_apply] at h2
  · rintro ⟨n, hn, h1, h2⟩
    refine ⟨β * n * β⁻¹, (Formalism.L2.SG.Pf.conj_mem_NLam (β := β) (hβ := hβ) Λ F n).2 hn, fun a => ?_, ?_⟩
    · change β (n (β.symm (β (F.fl.e a)))) = β (F'.fl.e a)
      rw [LinearEquiv.symm_apply_apply, h1 a]
    · rw [Submodule.mem_map_equiv]
      change β.symm (β (n (β.symm (β F.fl.z))) - β F'.fl.z) ∈ Xsp F
      rwa [LinearEquiv.symm_apply_apply, ← map_sub, LinearEquiv.symm_apply_apply]

end Iso

section Terms

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {hF : FinX Y}

theorem ex_rep_iff {u u' : D.what₂.Word} (t : RT Y u u')
    (Q : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → Prop)
    (hQ : ∀ x y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u'),
      TermDef.Rel t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x y → (Q x.1 ↔ Q y.1)) :
    (∃ F', TermDef.Rep t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') t.cls F' ∧ Q F') ↔
      Q (Quot.out t.cls).1 := by
  constructor
  · rintro ⟨F', ⟨h, hm⟩, hF'⟩
    have key : Q F' = Q (Quot.out t.cls).1 :=
      congrArg (Quot.lift (fun x : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') => Q x.1)
        (fun x y hxy => propext (hQ x y hxy))) (hm.trans (Quot.out_eq t.cls).symm)
    exact key.mp hF'
  · intro hq
    exact ⟨(Quot.out t.cls).1, Exists.intro (Quot.out t.cls).2 (Quot.out_eq t.cls), hq⟩

variable (W : WittDat X) (hI : SIso D.s (sOf hF))

def tc {u u' : D.what₂.Word} (t : D.s.Term u u') : RT Y u u' := hI.eT u u' t

def repF {u u' : D.what₂.Word} (t : RT Y u u') : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) :=
  (Quot.out t.cls).1

def lamOf {u u' : D.what₂.Word} (t : D.s.Term u u') : Submodule (𝓞 D.host.E) (VS D).V :=
  Formalism.HermitianLatticesTheory.gmap (W.δ u) (tc hI t).lam

def fl'Of {u u' : D.what₂.Word} (t : D.s.Term u u') : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) :=
  mapL (W.δ u) (W.isom u) (repF (tc hI t))

variable (D) in

def LatIso : Prop :=
  ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V), β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
    ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V,
      (Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 → Formalism.HermitianLatticesTheory.gmap β Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0) ∧
      (Submodule.IsLattice D.host.E Λ → Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap β Λ)) ∧
      (Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap β Λ))

theorem rowLat_map (hL : LatIso D) {T : D.host.E} (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (h : IsRowLat D F0 Λ) : IsRowLat D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) := by
  obtain ⟨hg, ⟨hlat, hun, hlift, hfix⟩, hX⟩ := h
  obtain ⟨h1, h2, h3⟩ := hL β hβ Λ
  refine ⟨h1 hg, ⟨h2 hlat, h3 hun, ?_, ?_⟩, ?_⟩
  · exact (Formalism.L2.SG.Pf.IsLift_mapL (β := β) (hβ := hβ) Λ (lf D F0)).mpr hlift
  · exact (Formalism.L2.SG.Pf.IsFixedConv_mapL (β := β) (hβ := hβ) (gS D) Λ (lf D F0)).mpr hfix
  · show XLam (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ (lf D F0)) = _
    rw [Formalism.L2.SG.Pf.XLam_mapL (β := β) (hβ := hβ) Λ (lf D F0), hX]
    unfold Formalism.MainNotions.S.XS Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y0, ⟨a, x, hx, rfl⟩, rfl⟩
      exact ⟨a, x, hx, by simp [Formalism.L2.SG.Saturated.mapFlag]⟩
    · rintro ⟨a, x, hx, rfl⟩
      exact ⟨x • F0.e a, ⟨a, x, hx, rfl⟩, by simp [Formalism.L2.SG.Saturated.mapFlag]⟩

theorem rowLat_tc {u u' : D.what₂.Word} (t : D.s.Term u u') : IsRowLat D (X.Fu u) (tc hI t).lam := (Y.rowsOK u).1 _ (tc hI t).mem

theorem fixedC (hL : LatIso D) {u u' : D.what₂.Word} (t : D.s.Term u u') :
    FixedHyp D (lamOf W hI t) (lf D (FlagOfWord W u)) := (rowLat_map hL (W.δ u) (W.isom u) (X.Fu u) _ (rowLat_tc hI t)).2.1

theorem pdC {u u' : D.what₂.Word} (t : D.s.Term u u') :
    TermDef.PD D (lamOf W hI t) (lf D (FlagOfWord W u)) u' (fl'Of W hI t) := (Formalism.L2.SG.Pf.positive_definite_isomorphism D u' (W.δ u) (W.isom u) (tc hI t).lam (lf D (X.Fu u)) (repF (tc hI t))).2
    (Quot.out (tc hI t).cls).2

theorem inS_iffC {u u' : D.what₂.Word} (t : D.s.Term u u') :
    D.s.inS t ↔ Formalism.L2.SG.FourParts.InSF (lf D (FlagOfWord W u)) (fl'Of W hI t) := by
  rw [hI.inS t]
  show Formalism.L2.SG.FourParts.termInS (tc hI t) ↔ _
  unfold Formalism.L2.SG.FourParts.termInS
  conv_lhs => rw [← Quot.out_eq (tc hI t).cls]
  refine (Formalism.L2.SG.FourParts.isInS_mk (PI.InSClassConstW.inSFun_all _ _ _) _).trans ?_
  exact (inSF_mapL (W.δ u) (W.isom u) _ _).symm

theorem isId_iffC {u u' : D.what₂.Word} (t : D.s.Term u u') :
    D.s.isId t ↔ Formalism.L2.SG.FourParts.IsIdF (lamOf W hI t) (lf D (FlagOfWord W u)) (fl'Of W hI t) := by
  rw [hI.isId t]
  change Formalism.L2.SG.FourParts.IsIdT _ _ _ (tc hI t).cls ↔ _
  refine Iff.trans ?_ (isIdF_mapL (W.δ u) (W.isom u) (tc hI t).lam (lf D (X.Fu u)) (repF (tc hI t))).symm
  have hrow := rowLat_tc hI t
  unfold Formalism.L2.SG.FourParts.IsIdT
  constructor
  · rintro ⟨F', ⟨h, hm⟩, hid⟩
    have h2 := (ex_rep_iff (tc hI t) _ (Formalism.L2.SG.Closed.TermInSFun_holds D u u' (X.Fu u) _ hrow)).1
      ⟨F', ⟨h, hm⟩, Formalism.L2.SG.FourParts.inSF_of_isIdF _ hid⟩
    exact Formalism.L2.SG.Closed.TermIdIffInS_holds D u u' (X.Fu u) _ hrow (Quot.out (tc hI t).cls)
      (Formalism.L2.SG.Closed.TermInSRel_holds D u u' (X.Fu u) _ hrow (Quot.out (tc hI t).cls) h2) h2
  · intro h
    exact ⟨_, ⟨(Quot.out (tc hI t).cls).2, Quot.out_eq _⟩, h⟩

theorem gterm_val {u u' : D.what₂.Word} (t : D.s.Term u u') :
    algebraMap D.host.F D.host.E (D.s.Gterm t) = (tc hI t).G := by
  rw [hI.Gterm t]
  rfl

theorem G_eqC {u u' : D.what₂.Word} (t : D.s.Term u u') :
    algebraMap D.host.F D.host.E (D.s.Gterm t) = Gval (lf D (FlagOfWord W u)) (fl'Of W hI t) := by
  rw [gterm_val hI t]
  exact (gval_mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) (repF (tc hI t))).symm

theorem rel_iffC {u u' : D.what₂.Word} (t : D.s.Term u u') :
    D.s.relevant t ↔ Relevant D.host.F (lf D (FlagOfWord W u)).fl (fl'Of W hI t).fl := by
  rw [hI.relevant t]
  show (tc hI t).relevant ↔ _
  unfold TermDef.Term.relevant
  conv_lhs => rw [← Quot.out_eq (tc hI t).cls]
  refine (TermDef.isRel_mk _ (PI.TermAttrConst.UnitaryGroupMassFormula.relFun_all _ _ _ _) _).trans ?_
  exact (Formalism.L2.SG.Pf.relevant_mapFlag (β := W.δ u) (hβ := W.isom u) _ _ _).symm

theorem gen_iffC {u u' : D.what₂.Word} (t : D.s.Term u u') :
    D.s.generic t ↔ IsGeneric (lamOf W hI t) (gS D) (lf D (FlagOfWord W u)) (fl'Of W hI t) := by
  rw [hI.generic t]
  show (tc hI t).generic ↔ _
  unfold TermDef.Term.generic
  conv_lhs => rw [← Quot.out_eq (tc hI t).cls]
  refine (TermDef.isGen_mk (gS D) ((term_function_const D u u' (X.Fu u) (tc hI t).lam
    ((Y.rowsOK u).1 _ (tc hI t).mem)).2.2.2.1) _).trans ?_
  exact (Formalism.L2.SG.Pf.generic_isomorphism_holds (gS D) _ _ (W.δ u) (W.isom u) (tc hI t).lam (lf D (X.Fu u))
    (repF (tc hI t))).symm

theorem FeqF_iffC {u u' : D.what₂.Word} (t : D.s.Term u u') :
    D.s.FeqF t ↔ ∃ n ∈ NLam (lamOf W hI t) (lf D (FlagOfWord W u)),
      ∀ a, n (frame (lf D (FlagOfWord W u)) a) = frame (fl'Of W hI t) a := by
  rw [hI.FeqF t]
  show (tc hI t).FeqF ↔ _
  unfold TermDef.Term.FeqF
  conv_lhs => rw [← Quot.out_eq (tc hI t).cls]
  refine (TermDef.isFeqF_mk (PI.TermAttrConst.UnitaryGroupMassFormula.feqFFun_all _ _ _) _).trans ?_
  exact (Formalism.L2.SG.Pf.flag_equivalence_isomorphism _ _ (W.δ u) (W.isom u) (tc hI t).lam (lf D (X.Fu u)) (repF (tc hI t))).symm

variable (Y) in

def IdentityCellVanishes (u u' : D.what₂.Word) : Prop := ∀ t : RT Y u u', Formalism.L2.SG.FourParts.termIsId t → t.G = 0

include hI in

theorem id_GC (hId : ∀ u u', IdentityCellVanishes Y u u') {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.isId t) :
    D.s.Gterm t = 0 := by
  apply (algebraMap D.host.F D.host.E).injective
  rw [map_zero, gterm_val hI t]
  exact hId u u' _ ((hI.isId t).1 h)

variable (Y) in

def AtSome (u u' : D.what₂.Word) : Prop := ∀ t : RT Y u u', t.G ≠ 0 → t.relevant → ∃ w, t.atPt w

theorem cellQ {u u' : D.what₂.Word} (t : RT Y u u') (w : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1)) :
    ∀ x y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u'),
      TermDef.Rel t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x y →
      ((Gval (lf D (X.Fu u)) x.1 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) x.1)) w) ↔
        (Gval (lf D (X.Fu u)) y.1 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) y.1)) w)) := by
  intro x y hxy
  rw [PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x y hxy,
    PI.TermAttrConst.UnitaryGroupMassFormula.cellFun_all t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x y hxy w]

theorem pt_cellC (hAt : ∀ u u', AtSome Y u u') {u u' : D.what₂.Word} (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hr : D.s.relevant t) : IsInCell (ZhatOM (ZhatL (lf D (FlagOfWord W u)) (fl'Of W hI t))) (D.s.ptOf t) := by
  have hG' : (tc hI t).G ≠ 0 := by
    intro h0
    apply hG
    rw [hI.Gterm t]
    exact Subtype.ext h0
  have hr' : (tc hI t).relevant := (hI.relevant t).mp hr
  obtain ⟨w, hw⟩ := hAt u u' (tc hI t) hG' hr'
  have hex : ∃ w, (tc hI t).atPt w ∧ (tc hI t).relevant := ⟨w, hw, hr'⟩
  rw [hI.ptOf t]
  show IsInCell _ (Formalism.L2.SG.PairVal.ptOf (tc hI t))
  unfold Formalism.L2.SG.PairVal.ptOf
  rw [dif_pos hex]
  obtain ⟨h2, -⟩ := hex.choose_spec
  generalize hex.choose = w0 at h2 ⊢
  unfold TermDef.Term.atPt at h2
  rw [← Quot.out_eq (tc hI t).cls] at h2
  have h3 := ((TermDef.atPt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) (PI.TermAttrConst.UnitaryGroupMassFormula.cellFun_all _ _ _) _
    w0).mp h2).2
  have e : ZhatL (lf D (FlagOfWord W u)) (fl'Of W hI t) = ZhatL (lf D (X.Fu u)) (repF (tc hI t)) :=
    Formalism.L2.SG.Saturated.zhat_mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) (repF (tc hI t))
  rw [e]
  exact h3

theorem rp_lam {u u' : D.what₂.Word} (q : RP Y u u') : q.1.1.lam = q.1.2.lam := by
  obtain ⟨⟨s₁, h₁⟩, ⟨s₂, h₂⟩, hrow⟩ := q.2
  rw [← h₁, ← h₂]
  exact congrArg (fun x => (x.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow

theorem pLamC {u u' : D.what₂.Word} (p : D.s.Pair u u') : lamOf W hI (D.s.pfst p) = lamOf W hI (D.s.psnd p) := by
  unfold lamOf tc
  rw [hI.pfst p, hI.psnd p]
  exact congrArg (Formalism.HermitianLatticesTheory.gmap (W.δ u)) (rp_lam (hI.eP u u' p))

end Terms

section Pairs

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {hF : FinX Y} (W : WittDat X)
  (hI : SIso D.s (sOf hF))

def mvOf {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (VS D) D.R.rS T)
    (F₁ F₂ : LFlag (VS D) D.R.rS T') : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  if h : TermDef.DCRel Λ F F₁ F₂ then h.choose * h.choose_spec.2.choose else 1

def betaOf {u u' : D.what₂.Word} (p : D.s.Pair u u') : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  W.δ u * (mvOf (hI.eP u u' p).1.2.lam (lf D (X.Fu u)) (hI.eP u u' p).l2.frame (repF (hI.eP u u' p).1.2) *
      ((hI.eP u u' p).l2.lin * (hI.eP u u' p).l1.lin⁻¹) *
      (mvOf (hI.eP u u' p).1.1.lam (lf D (X.Fu u)) (hI.eP u u' p).l1.frame (repF (hI.eP u u' p).1.1))⁻¹) *
    (W.δ u)⁻¹

structure PairTies : Prop where
  isPair : ∀ {u u' : D.what₂.Word} (p : D.s.Pair u u'),
    IsPair (lamOf W hI (D.s.pfst p)) (lf D (FlagOfWord W u)) (fl'Of W hI (D.s.pfst p)) (fl'Of W hI (D.s.psnd p))
      (betaOf W hI p) (gS D)
  s0_eq : ∀ {u u' : D.what₂.Word} (p : D.s.Pair u u'), D.s.s0 p =
    Lat.s0 (lamOf W hI (D.s.pfst p)) (lf D (FlagOfWord W u)) (fl'Of W hI (D.s.pfst p)) (fl'Of W hI (D.s.psnd p))
      (betaOf W hI p) D.R.k
  scal_iff : ∀ {u u' : D.what₂.Word} (p : D.s.Pair u u'), D.s.s0 p = 1 → (D.s.scalarPair p ↔
    IsScalar (lamOf W hI (D.s.pfst p)) (lf D (FlagOfWord W u)) (fl'Of W hI (D.s.pfst p)) (fl'Of W hI (D.s.psnd p))
      (betaOf W hI p))

def JtOf {u u' : D.what₂.Word} (t : D.s.Term u u') : X.Vpi u' →L[ℂ] X.Vpi u :=
  if h : ∃ s : TT Y u u', s.toTerm = tc hI t then ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') h.choose else 0

def wRowOf {u u' : D.what₂.Word} (p : D.s.Pair u u') : ℝ := Formalism.MainNotions.S.wRow D (FlagOfWord W u) (lamOf W hI (D.s.pfst p))

theorem lamOf_mem {u u' : D.what₂.Word} (t : D.s.Term u u') : lamOf W hI t ∈ rowsRec W Y u := Finset.mem_image_of_mem _ (tc hI t).mem

theorem wRowOf_pos (hA : ∀ u, Formalism.L2.SG.PairVal.AutFin D (FlagOfWord W u) (rowsRec W Y u)) {u u' : D.what₂.Word}
    (p : D.s.Pair u u') : 0 < wRowOf W hI p := Formalism.L2.SG.PairVal.wRow_pos (h := hA u _ (lamOf_mem W hI (D.s.pfst p)))

variable (X) in

structure AmpDat where
  chi : ∀ {u u' : D.what₂.Word}, D.s.Pair u u' → ℂ
  chi_norm : ∀ {u u' : D.what₂.Word} (p : D.s.Pair u u'), ‖chi p‖ = 1
  piB : ∀ {u u' : D.what₂.Word}, D.s.Pair u u' → (X.Vpi u' →L[ℂ] X.Vpi u')
  piB_unit : ∀ {u u' : D.what₂.Word} (p : D.s.Pair u u') (x : X.Vpi u'), ‖piB p x‖ = ‖x‖

def PvalForm (A : AmpDat X) : Prop :=
  ∀ {u u' : D.what₂.Word} (p : D.s.Pair u u'), D.s.pval p =
    (wRowOf W hI p : ℂ) * A.chi p * hsInner ((JtOf hI (D.s.pfst p)).comp (A.piB p)) (JtOf hI (D.s.psnd p))

structure TieHyp : Prop where
  lat : LatIso D
  idG : ∀ u u', IdentityCellVanishes Y u u'
  atSome : ∀ u u', AtSome Y u u'
  autFin : ∀ u, Formalism.L2.SG.PairVal.AutFin D (FlagOfWord W u) (rowsRec W Y u)
  dim : ∀ u, DimTie (X := X) u
  pairs : PairTies W hI

def termTieOf (H : TieHyp W hI) (A : AmpDat X) (hV : PvalForm W hI A) : TermTie D where
  abelian₂ := fun t => lamOf W hI t
  fl := fun {u _} _ => lf D (FlagOfWord W u)
  fl' := fun t => fl'Of W hI t
  fixed := fun t => fixedC W hI H.lat t
  lift' := fun t => (pdC W hI t).1
  adm := fun t => (pdC W hI t).2.1
  conv' := fun t => (pdC W hI t).2.2.1
  inS_iff := fun t => inS_iffC W hI t
  isId_iff := fun t => isId_iffC W hI t
  G_eq := fun t => G_eqC W hI t
  rel_iff := fun t => rel_iffC W hI t
  FeqF_iff := fun t => FeqF_iffC W hI t
  id_G := fun t h => id_GC hI H.idG t h
  gen_iff := fun t => gen_iffC W hI t
  pt_cell := fun t h hr => pt_cellC W hI H.atSome t h hr
  pLam := fun p => pLamC W hI p
  pfl := fun _ => rfl
  beta := fun p => betaOf W hI p
  isPair := fun p => H.pairs.isPair p
  s0_eq := fun p => H.pairs.s0_eq p
  scal_iff := fun p => H.pairs.scal_iff p
  wRow := fun p => wRowOf W hI p
  wRow_pos := fun p => wRowOf_pos W hI H.autFin p
  chi := fun p => A.chi p
  chi_norm := fun p => A.chi_norm p
  Hpi := X.Vpi
  Hpi_dim := fun u => H.dim u
  Jt := fun t => JtOf hI t
  piB := fun p => A.piB p
  piB_unit := fun p x => A.piB_unit p x
  pval_eq := fun p => hV p

end Pairs

section Loc

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {hF : FinX Y} (W : WittDat X)
  (hI : SIso D.s (sOf hF))

variable (D) in

def WRowIso : Prop :=
  ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    Formalism.MainNotions.S.wRow D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) = Formalism.MainNotions.S.wRow D F0 Λ

variable (D) in

def RowRepsIso : Prop :=
  ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    IsRowReps D F0 what₂ → IsRowReps D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (what₂.image (Formalism.HermitianLatticesTheory.gmap β))

variable (Y) in

def massTotOf (u : D.what₂.Word) : ℝ := Formalism.MainNotions.S.Cnt.massRows D (FlagOfWord W u) (rowsRec W Y u)

theorem massTot_eq (hW : WRowIso D) (u : D.what₂.Word) :
    massTotOf Y W u = Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := by
  unfold massTotOf Formalism.MainNotions.S.Cnt.massRows rowsRec
  rw [Finset.sum_image (by
    intro A _ B _ h
    exact PI.TermAttrConst.UnitaryGroupMassFormula.gmap_injective (W.δ u) h)]
  refine Finset.sum_congr rfl (fun Λ _ => ?_)
  exact hW (W.δ u) (W.isom u) (X.Fu u) Λ

theorem massPair_val (hW : WRowIso D) {u u' : D.what₂.Word} (P : D.s.Pair u u') :
    D.s.massPair P = Formalism.MainNotions.S.wRow D (FlagOfWord W u) (lamOf W hI (D.s.pfst P)) / massTotOf Y W u := by
  rw [hI.massPair P, massTot_eq W hW u]
  have h1 : Formalism.MainNotions.S.wRow D (FlagOfWord W u) (lamOf W hI (D.s.pfst P)) =
      Formalism.MainNotions.S.wRow D (X.Fu u) (hI.eP u u' P).1.1.lam := by
    unfold lamOf tc
    rw [hI.pfst P]
    exact hW (W.δ u) (W.isom u) (X.Fu u) _
  rw [h1]
  rfl

theorem term_injC {u u' : D.what₂.Word} (γ γ' : D.s.Term u u') (hL : lamOf W hI γ = lamOf W hI γ')
    (h : ∃ n ∈ NLam (lamOf W hI γ) (lf D (FlagOfWord W u)), ∃ m ∈ NLam (lamOf W hI γ) (fl'Of W hI γ),
      ∀ b, frame (fl'Of W hI γ') b = n (m (frame (fl'Of W hI γ) b))) : γ = γ' := by
  obtain ⟨n, hn, m, hm, hfr⟩ := h
  have hlam : (tc hI γ).lam = (tc hI γ').lam := (Formalism.L2.SG.Pf.gmap_inj (W.δ u)).1 hL
  have hz : ∀ t : D.s.Term u u', (fl'Of W hI t).zt = frame (fl'Of W hI t) (Fin.last _) := by
    intro t
    rw [(pdC W hI t).1.2]
    simp [frame, FlagG.fvec]
  have hdc : TermDef.DCRel (lamOf W hI γ) (mapL (W.δ u) (W.isom u) (lf D (X.Fu u))) (fl'Of W hI γ) (fl'Of W hI γ') :=
    ⟨n, hn, m, hm, hfr, by rw [hz γ', hz γ]; exact hfr _⟩
  have hdc' := (Formalism.L2.SG.Pf.double_coset_isomorphism _ _ (W.δ u) (W.isom u) _ _ _ _).1 hdc
  apply (hI.eT u u').injective
  have key : ∀ (a b : RT Y u u'), a.lam = b.lam →
      TermDef.DCRel a.lam (lf D (X.Fu u)) (Quot.out a.cls).1 (Quot.out b.cls).1 → a = b := by
    rintro ⟨Λ, hm1, c⟩ ⟨Λ', hm2, c'⟩ h hd
    simp only at h
    subst h
    have : c = c' := by
      rw [← Quot.out_eq c, ← Quot.out_eq c']
      exact Quot.sound hd
    subst this
    rfl
  exact key (tc hI γ) (tc hI γ') hlam hdc'

include hI in

theorem ptOfConvC (u u' : D.what₂.Word) : Formalism.L2.SG.Pf.AtPt.PtOfConv D u u' := by
  intro γ hγ
  rw [hI.ptOf γ]
  show Formalism.MainNotions.S.LocalSplitGroups.Gpt _ _ (Formalism.L2.SG.PairVal.ptOf (tc hI γ)) = 0
  unfold Formalism.L2.SG.PairVal.ptOf
  rw [dif_neg]
  · exact Formalism.L2.SG.PairVal.Gpt_junkPoint_eq_zero D u u'
  · rintro ⟨w, hw, hrel⟩
    apply hγ
    refine ⟨?_, (hI.relevant γ).mpr hrel⟩
    have hG : (tc hI γ).G ≠ 0 := by
      unfold TermDef.Term.atPt at hw
      rw [← Quot.out_eq (tc hI γ).cls] at hw
      exact ((TermDef.atPt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) (PI.TermAttrConst.UnitaryGroupMassFormula.cellFun_all _ _ _) _
        w).mp hw).1
    intro h0
    rw [hI.Gterm γ] at h0
    have h1 : (((sOf hF).Gterm (hI.eT u u' γ) : D.host.F) : D.host.E) = (tc hI γ).G := rfl
    rw [h0] at h1
    exact hG (by simpa using h1.symm)

def locDatOf (Y : Formalism.L2.SG.Full.Full X) : Formalism.L2.SG.TermLoc.LocDat D := ⟨Y.δ, Y.M, Y.agree⟩

def massDatOf (H : TieHyp W hI) (A : AmpDat X) (hV : PvalForm W hI A) (hW : WRowIso D) (hR : RowRepsIso D)
    (hne : ∀ u, (Y.what₂ u).Nonempty) (u u' : D.what₂.Word) :
    Formalism.L2.SG.TermLoc.MassDat D (termTieOf W hI H A hV) u u' where
  massT γ := Formalism.MainNotions.S.wRow D (FlagOfWord W u) (lamOf W hI γ) / massTotOf Y W u
  massT_nonneg γ := div_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Formalism.L2.SG.PairVal.massRows_pos D (FlagOfWord W u) (rowsRec W Y u) (H.autFin u) ((hne u).image _)).le
  massTot := massTotOf Y W u
  massTot_pos := Formalism.L2.SG.PairVal.massRows_pos D (FlagOfWord W u) (rowsRec W Y u) (H.autFin u) ((hne u).image _)
  massPair_eq P := ⟨massPair_val W hI hW P, (massPair_val W hI hW P).trans (by rw [pLamC W hI P]),
    massPair_val W hI hW P⟩
  mass_def := ⟨FlagOfWord W u, rowsRec W Y u, F0rec_e W u, F0rec_z_eq_zmOf W u,
    hR (W.δ u) (W.isom u) (X.Fu u) (Y.what₂ u) (Y.rowsOK u), rfl, fun _ => rfl⟩
  term_inj γ γ' hL h := term_injC W hI γ γ' hL h

def termLocOf (H : TieHyp W hI) (A : AmpDat X) (hV : PvalForm W hI A) (hW : WRowIso D) (hR : RowRepsIso D)
    (hne : ∀ u, (Y.what₂ u).Nonempty) (u u' : D.what₂.Word)
    (hgen : Formalism.L2.SG.TermLoc.GenLocC D (locDatOf Y) (termTieOf W hI H A hV) u u')
    (hsc : Formalism.L2.SG.TermLoc.ScalarC D (locDatOf Y) (termTieOf W hI H A hV) u u') :
    Formalism.MainNotions.S.LocalSplitGroups.TermLoc D (termTieOf W hI H A hV) Y.δ Y.M u u' :=
  Formalism.L2.SG.TermLoc.mkTermLoc (locDatOf Y) (termTieOf W hI H A hV) u u'
    (Formalism.L2.SG.Pf.termLoc_gPtC_of (termTieOf W hI H A hV) u u' (ptOfConvC hI u u')) hgen
    (Formalism.L2.SG.Pf.termLoc_atPtC (locDatOf Y) (termTieOf W hI H A hV) u u') hsc (massDatOf W hI H A hV hW hR hne u u')

end Loc

section WittEquiv

variable {D : D7} {X : HidaSetting D} (W : WittDat X) (Y : Formalism.L2.SG.Full.Full X)

abbrev RTrec (u u' : D.what₂.Word) : Type := TermDef.Term D u u' (FlagOfWord W u) (rowsRec W Y u)

def mvCar {u u' : D.what₂.Word} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (x : TermDef.Carrier (TermDef.PD D Λ (lf D (X.Fu u)) u')) :
    TermDef.Carrier (TermDef.PD D (Formalism.HermitianLatticesTheory.gmap (W.δ u) Λ) (lf D (FlagOfWord W u)) u') :=
  ⟨mapL (W.δ u) (W.isom u) x.1, (Formalism.L2.SG.Pf.positive_definite_isomorphism D u' (W.δ u) (W.isom u) Λ (lf D (X.Fu u)) x.1).2 x.2⟩

def mvCls {u u' : D.what₂.Word} (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    TermDef.TermsOf D u' (X.Fu u) Λ → TermDef.TermsOf D u' (FlagOfWord W u) (Formalism.HermitianLatticesTheory.gmap (W.δ u) Λ) :=
  Quot.lift (fun x => TermDef.mk _ _ _ (mvCar W Λ x)) (fun x y h =>
    Quot.sound ((Formalism.L2.SG.Pf.double_coset_isomorphism _ _ (W.δ u) (W.isom u) Λ (lf D (X.Fu u)) x.1 y.1).2 h))

def toRec {u u' : D.what₂.Word} (t : RT Y u u') : RTrec W Y u u' :=
  ⟨Formalism.HermitianLatticesTheory.gmap (W.δ u) t.lam, Finset.mem_image_of_mem _ t.mem, mvCls W t.lam t.cls⟩

theorem toRec_mk {u u' : D.what₂.Word} (t : RT Y u u') :
    TermDef.mk _ _ _ (mvCar W t.lam (Quot.out t.cls)) = (toRec W Y t).cls := congrArg (mvCls W t.lam) (Quot.out_eq t.cls)

theorem ex_rep_iff_of {u' : D.what₂.Word} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hrow : TermDef.EqIff Λ (lf D F0) (TermDef.PD D Λ (lf D F0) u'))
    (c : TermDef.TermQ Λ (lf D F0) (TermDef.PD D Λ (lf D F0) u')) (x : TermDef.Carrier (TermDef.PD D Λ (lf D F0) u'))
    (hx : TermDef.mk _ _ _ x = c) (Q : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → Prop)
    (hQ : ∀ x y : TermDef.Carrier (TermDef.PD D Λ (lf D F0) u'),
      TermDef.Rel Λ (lf D F0) (TermDef.PD D Λ (lf D F0) u') x y → (Q x.1 ↔ Q y.1)) :
    (∃ F', TermDef.Rep Λ (lf D F0) (TermDef.PD D Λ (lf D F0) u') c F' ∧ Q F') ↔ Q x.1 := by
  constructor
  · rintro ⟨F', ⟨h, hm⟩, hF'⟩
    have hr := (hrow ⟨F', h⟩ x).1 (hm.trans hx.symm)
    exact (hQ ⟨F', h⟩ x hr).1 hF'
  · intro hq
    exact ⟨x.1, Exists.intro x.2 hx, hq⟩

variable {W Y}

theorem rowLat_rec (hL : LatIso D) {u : D.what₂.Word} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hm : Λ ∈ Y.what₂ u) :
    IsRowLat D (FlagOfWord W u) (Formalism.HermitianLatticesTheory.gmap (W.δ u) Λ) := rowLat_map hL (W.δ u) (W.isom u) (X.Fu u) Λ ((Y.rowsOK u).1 Λ hm)

theorem eqIff_rec (hL : LatIso D) {u u' : D.what₂.Word} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hm : Λ ∈ Y.what₂ u) :
    TermDef.EqIff (Formalism.HermitianLatticesTheory.gmap (W.δ u) Λ) (lf D (FlagOfWord W u))
      (TermDef.PD D (Formalism.HermitianLatticesTheory.gmap (W.δ u) Λ) (lf D (FlagOfWord W u)) u') := PI.DCRelEquiv.UnitaryGroupMassFormula.eqIffAll_holds _ _ _ _ _ _ _ _

theorem eqIff_base {u u' : D.what₂.Word} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hm : Λ ∈ Y.what₂ u) :
    TermDef.EqIff Λ (lf D (X.Fu u)) (TermDef.PD D Λ (lf D (X.Fu u)) u') := PI.DCRelEquiv.UnitaryGroupMassFormula.eqIffAll_holds _ _ _ _ _ _ _ _

theorem mapL_mapL_inv {u : D.what₂.Word} {T : D.host.E} (F : LFlag (VS D) D.R.rS T) :
    mapL (W.δ u) (W.isom u) (mapL (W.δ u)⁻¹ (Subgroup.inv_mem _ (W.isom u)) F) = F := by
  obtain ⟨fl, zt⟩ := F
  have h : ∀ x, W.δ u ((W.δ u)⁻¹ x) = x := fun x => (W.δ u).apply_symm_apply x
  simp only [Formalism.L2.SG.Saturated.mapL, Formalism.L2.SG.Saturated.mapFlag, h]

variable (W Y)

theorem toRec_inj (hL : LatIso D) {u u' : D.what₂.Word} : Function.Injective (toRec W Y (u := u) (u' := u')) := by
  intro t₁ t₂ h
  obtain ⟨l₁, m₁, c₁⟩ := t₁
  obtain ⟨l₂, m₂, c₂⟩ := t₂
  have hl : l₁ = l₂ := PI.TermAttrConst.UnitaryGroupMassFormula.gmap_injective (W.δ u) (congrArg TermDef.Term.lam h)
  subst hl
  obtain ⟨x₁, rfl⟩ := Quot.exists_rep c₁
  obtain ⟨x₂, rfl⟩ := Quot.exists_rep c₂
  have hc : TermDef.mk (Formalism.HermitianLatticesTheory.gmap (W.δ u) l₁) (lf D (FlagOfWord W u)) _ (mvCar W l₁ x₁) =
      TermDef.mk (Formalism.HermitianLatticesTheory.gmap (W.δ u) l₁) (lf D (FlagOfWord W u)) _ (mvCar W l₁ x₂) := by
    injection h with h1 h2
  have hr := (eqIff_rec (W := W) (u' := u') hL _ m₁ _ _).1 hc
  have hd := (Formalism.L2.SG.Pf.double_coset_isomorphism _ _ (W.δ u) (W.isom u) _ (lf D (X.Fu u)) x₁.1 x₂.1).1 hr
  exact congrArg (TermDef.Term.mk _ m₁) (Quot.sound hd)

theorem toRec_surj {u u' : D.what₂.Word} : Function.Surjective (toRec W Y (u := u) (u' := u')) := by
  intro s
  obtain ⟨lam, mem, cls⟩ := s
  obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 mem
  obtain ⟨x, rfl⟩ := Quot.exists_rep cls
  have hx : TermDef.PD D Λ (lf D (X.Fu u)) u' (mapL (W.δ u)⁻¹ (Subgroup.inv_mem _ (W.isom u)) x.1) := by
    apply (Formalism.L2.SG.Pf.positive_definite_isomorphism D u' (W.δ u) (W.isom u) Λ (lf D (X.Fu u)) _).1
    rw [mapL_mapL_inv]
    exact x.2
  refine ⟨⟨Λ, hΛ, TermDef.mk _ _ _ ⟨_, hx⟩⟩, ?_⟩
  have hc : mvCar W Λ ⟨_, hx⟩ = x := Subtype.ext (mapL_mapL_inv _)
  have hc' : mvCls W Λ (TermDef.mk _ _ _ ⟨_, hx⟩) = TermDef.mk _ _ _ x := congrArg (TermDef.mk _ _ _) hc
  show TermDef.Term.mk (Formalism.HermitianLatticesTheory.gmap (W.δ u) Λ) _ (mvCls W Λ (TermDef.mk _ _ _ ⟨_, hx⟩)) = _
  rw [hc']
  rfl

def termWitt (hL : LatIso D) (u u' : D.what₂.Word) : RT Y u u' ≃ RTrec W Y u u' :=
  Equiv.ofBijective (toRec W Y) ⟨toRec_inj W Y hL, toRec_surj W Y⟩

theorem termWitt_apply (hL : LatIso D) {u u' : D.what₂.Word} (t : RT Y u u') : termWitt W Y hL u u' t = toRec W Y t := rfl

variable {W Y}

theorem toRec_rel (hL : LatIso D) {u u' : D.what₂.Word} (t : RT Y u u') :
    TermDef.Rel (Formalism.HermitianLatticesTheory.gmap (W.δ u) t.lam) (lf D (FlagOfWord W u))
      (TermDef.PD D (Formalism.HermitianLatticesTheory.gmap (W.δ u) t.lam) (lf D (FlagOfWord W u)) u')
      (mvCar W t.lam (Quot.out t.cls)) (Quot.out (toRec W Y t).cls) := (eqIff_rec (W := W) (u' := u') hL t.lam t.mem _ _).1 ((toRec_mk W Y t).trans (Quot.out_eq _).symm)

theorem toRec_G (hL : LatIso D) {u u' : D.what₂.Word} (t : RT Y u u') : (toRec W Y t).G = t.G := by
  have h : TermDef.DCRel _ _ _ _ := toRec_rel (W := W) (Y := Y) hL t
  have e : ∀ l, Formalism.MainNotions.S.Dl (FlagOfWord W u) (Quot.out (toRec W Y t).cls).1.fl l =
      Formalism.MainNotions.S.Dl (FlagOfWord W u) (mvCar W t.lam (Quot.out t.cls)).1.fl l := PI.TermAttrConst.UnitaryGroupMassFormula.dl_eq _ h
  have hx : (toRec W Y t).G = Gval (lf D (FlagOfWord W u)) (mvCar W t.lam (Quot.out t.cls)).1 := by
    show Formalism.MainNotions.S.Gflag _ _ = Formalism.MainNotions.S.Gflag _ _
    simp only [Formalism.MainNotions.S.Gflag, e]
  rw [hx]
  exact gval_mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) (Quot.out t.cls).1

theorem toRec_relevant (hL : LatIso D) {u u' : D.what₂.Word} (t : RT Y u u') :
    (toRec W Y t).relevant ↔ t.relevant := by
  unfold TermDef.Term.relevant
  show TermDef.IsRel (Formalism.HermitianLatticesTheory.gmap (W.δ u) t.lam) (lf D (FlagOfWord W u))
      (TermDef.PD D (Formalism.HermitianLatticesTheory.gmap (W.δ u) t.lam) (lf D (FlagOfWord W u)) u') _ (toRec W Y t).cls ↔ _
  have hx : t.cls = TermDef.mk _ _ _ (Quot.out t.cls) := (Quot.out_eq t.cls).symm
  rw [← toRec_mk W Y t]
  conv_rhs => rw [hx]
  refine (TermDef.isRel_mk _ (PI.TermAttrConst.UnitaryGroupMassFormula.relFun_all _ _ _ _) _).trans
    (Iff.trans ?_ (TermDef.isRel_mk _ (PI.TermAttrConst.UnitaryGroupMassFormula.relFun_all _ _ _ _) _).symm)
  exact Formalism.L2.SG.Pf.relevant_mapFlag (β := W.δ u) (hβ := W.isom u) _ _ _

theorem toRec_generic (hL : LatIso D) {u u' : D.what₂.Word} (t : RT Y u u') :
    (toRec W Y t).generic ↔ t.generic := by
  show TermDef.IsGen (Formalism.HermitianLatticesTheory.gmap (W.δ u) t.lam) (lf D (FlagOfWord W u))
      (TermDef.PD D (Formalism.HermitianLatticesTheory.gmap (W.δ u) t.lam) (lf D (FlagOfWord W u)) u') (gS D) (toRec W Y t).cls ↔
    TermDef.IsGen t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') (gS D) t.cls
  have hx : t.cls = TermDef.mk _ _ _ (Quot.out t.cls) := (Quot.out_eq t.cls).symm
  rw [← toRec_mk W Y t]
  conv_rhs => rw [hx]
  refine (TermDef.isGen_mk (gS D)
      ((term_function_const D u u' (FlagOfWord W u) _ (rowLat_rec hL t.lam t.mem)).2.2.2.1) _).trans
    (Iff.trans ?_ (TermDef.isGen_mk (gS D)
      ((term_function_const D u u' (X.Fu u) t.lam ((Y.rowsOK u).1 t.lam t.mem)).2.2.2.1) _).symm)
  show IsGeneric (Formalism.HermitianLatticesTheory.gmap (W.δ u) t.lam) (gS D) (mapL (W.δ u) (W.isom u) (lf D (X.Fu u)))
      (mapL (W.δ u) (W.isom u) (Quot.out t.cls).1) ↔ IsGeneric t.lam (gS D) (lf D (X.Fu u)) (Quot.out t.cls).1
  exact Formalism.L2.SG.Pf.generic_isomorphism_holds (gS D) _ _ (W.δ u) (W.isom u) t.lam (lf D (X.Fu u)) (Quot.out t.cls).1

theorem toRec_atPt (hL : LatIso D) {u u' : D.what₂.Word} (t : RT Y u u') (w : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1)) :
    (toRec W Y t).atPt w ↔ t.atPt w := by
  show TermDef.AtPt (Formalism.HermitianLatticesTheory.gmap (W.δ u) t.lam) (lf D (FlagOfWord W u))
      (TermDef.PD D (Formalism.HermitianLatticesTheory.gmap (W.δ u) t.lam) (lf D (FlagOfWord W u)) u') (toRec W Y t).cls w ↔
    TermDef.AtPt t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') t.cls w
  have hx : t.cls = TermDef.mk _ _ _ (Quot.out t.cls) := (Quot.out_eq t.cls).symm
  rw [← toRec_mk W Y t]
  conv_rhs => rw [hx]
  refine (TermDef.atPt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) (PI.TermAttrConst.UnitaryGroupMassFormula.cellFun_all _ _ _) _ _).trans
    (Iff.trans ?_ (TermDef.atPt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _)
      (PI.TermAttrConst.UnitaryGroupMassFormula.cellFun_all _ _ _) _ _).symm)
  show Gval (mapL (W.δ u) (W.isom u) (lf D (X.Fu u))) (mapL (W.δ u) (W.isom u) (Quot.out t.cls).1) ≠ 0 ∧
      IsInCell (ZhatOM (ZhatL (mapL (W.δ u) (W.isom u) (lf D (X.Fu u)))
        (mapL (W.δ u) (W.isom u) (Quot.out t.cls).1))) w ↔ _
  rw [Formalism.L2.SG.Saturated.gval_mapL, Formalism.L2.SG.Saturated.zhat_mapL]

theorem toRec_ptOf (hL : LatIso D) {u u' : D.what₂.Word} (t : RT Y u u') :
    Formalism.L2.SG.PairVal.ptOf (toRec W Y t) = Formalism.L2.SG.PairVal.ptOf t := by
  unfold Formalism.L2.SG.PairVal.ptOf
  have e : (fun w => (toRec W Y t).atPt w ∧ (toRec W Y t).relevant) = (fun w => t.atPt w ∧ t.relevant) := by
    funext w
    rw [toRec_atPt hL, toRec_relevant hL]
  rw [e]

theorem toRec_massTerm (hW : WRowIso D) {u u' : D.what₂.Word} (t : RT Y u u') :
    Formalism.L2.SG.PairVal.massTerm (toRec W Y t) = Formalism.L2.SG.PairVal.massTerm t := by
  show Formalism.MainNotions.S.wRow D (FlagOfWord W u) (Formalism.HermitianLatticesTheory.gmap (W.δ u) t.lam) / Formalism.MainNotions.S.Cnt.massRows D (FlagOfWord W u) (rowsRec W Y u) =
    Formalism.MainNotions.S.wRow D (X.Fu u) t.lam / Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u)
  rw [← massTot_eq W hW u]
  exact congrArg (· / massTotOf Y W u) (hW (W.δ u) (W.isom u) (X.Fu u) t.lam)

variable (W Y)

def WittPhase (u u' : D.what₂.Word) : Prop :=
  ∀ (t : RT Y u u') w, Formalism.L2.SG.PairVal.phaseAt (toRec W Y t) w = Formalism.L2.SG.PairVal.phaseAt t w

def WittVR (u u' : D.what₂.Word) : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (t : RT Y u u'),
    Formalism.L2.SG.PairVal.vRdef D u u' (FlagOfWord W u) (rowsRec W Y u) δ M (toRec W Y t) =
      Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) δ M t

def WittScal (u u' : D.what₂.Word) : Prop :=
  ∀ t₁ t₂ : RT Y u u', Formalism.L2.SG.Corank.TermScal D (toRec W Y t₁) (toRec W Y t₂) ↔ Formalism.L2.SG.Corank.TermScal D t₁ t₂

def WittNu (u : D.what₂.Word) : Prop :=
  ∀ (T' : D.host.E) (Z : Formalism.L2.SG.CntLocal.MatZ D),
    Formalism.L2.SG.CntLocal.nu T' (FlagOfWord W u) (rowsRec W Y u) Z = Formalism.L2.SG.CntLocal.nu T' (X.Fu u) (Y.what₂ u) Z

end WittEquiv

section IdCell

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem hT_X_zero (F : LFlag S r T) (a : Fin (r + 1)) {x : S.V} (hx : x ∈ Xsp F) : S.hT (F.fl.fvec a) x = 0 := by
  have hs : ∀ x y, starRingEnd E (S.hT x y) = S.hT y x := fun x y => by
    first
      | exact S.herm.eq x y
      | exact S.herm x y
  have he : ∀ i, S.hT (F.fl.fvec a) (F.fl.e i) = 0 := by
    intro i
    induction a using Fin.lastCases with
    | last =>
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      rw [← hs, F.fl.z_orth i, map_zero]
    | cast j =>
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact F.fl.e_iso j i
  have hx' : x ∈ Submodule.span E (Set.range F.fl.e) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact he i
  | zero => exact map_zero _
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

theorem zhat_col_zero (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    (h : Formalism.L2.SG.FourParts.IsIdF Λ F F') (a : Fin (r + 1)) (b : Fin r) :
    Formalism.MainNotions.S.Zhat F.fl F'.fl a b.castSucc = 0 := by
  obtain ⟨n, hn, he, -⟩ := h
  have hmem : F'.fl.e b ∈ Xsp F := by
    rw [← he b]
    have h1 : F.fl.e b ∈ Xflag F (b.1 + 1) := Submodule.subset_span ⟨b, by simp, rfl⟩
    have h2 := hn.2.1 b.1 _ h1
    have h3 : Xflag F b.1 ≤ Xsp F := Submodule.span_mono (Set.image_subset_range _ _)
    have h4 : F.fl.e b ∈ Xsp F := Submodule.subset_span ⟨b, rfl⟩
    have h5 := (Xsp F).add_mem (h3 h2) h4
    simpa using h5
  have hb : F'.fl.fvec b.castSucc = F'.fl.e b := by simp [Formalism.MainNotions.S.FlagG.fvec]
  show Formalism.MainNotions.S.brS S (F'.fl.fvec b.castSucc) (F.fl.fvec a) = 0
  rw [hb]
  exact hT_X_zero F a hmem

theorem gval_of_isIdF (hTs : star T = T) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    (h : Formalism.L2.SG.FourParts.IsIdF Λ F F') : Gval F F' = 0 := by
  have hz := zhat_col_zero Λ F F' h
  show Formalism.MainNotions.S.Gflag F.fl F'.fl = 0
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    obtain ⟨n, hn, -, hz'⟩ := h
    have hX : Xsp F = ⊥ := by
      show Submodule.span E (Set.range F.fl.e) = ⊥
      simp [Set.range_eq_empty]
    have hnz : n F.fl.z = F.fl.z := by
      have h3 := hn.2.2 F.fl.z (by simp [Formalism.MainNotions.S.Lat.orth, hX])
      rw [hX, Submodule.mem_bot, sub_eq_zero] at h3
      exact h3
    rw [hX, Submodule.mem_bot, sub_eq_zero, hnz] at hz'
    have hT' : T' = T := by
      have h1 := F'.fl.z_norm
      have h2 := F.fl.z_norm
      rw [← hz', h2] at h1
      exact (neg_inj.mp h1).symm
    have hf : ∀ {T₀ : E} (G : Formalism.MainNotions.S.FlagG S 0 T₀), G.fvec 0 = G.z := fun G => by
      simp [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc]
    have hZ : Formalism.MainNotions.S.Zhat F.fl F'.fl 0 0 = -T := by
      show Formalism.MainNotions.S.brS S (F'.fl.fvec 0) (F.fl.fvec 0) = -T
      rw [hf, hf, ← hz']
      exact F.fl.z_norm
    have hD1 : Formalism.MainNotions.S.Dl F.fl F'.fl (0 + 1) = -T := by
      unfold Formalism.MainNotions.S.Dl Formalism.MainNotions.S.leadMinorE
      rw [dif_pos le_rfl]
      exact (Matrix.det_fin_one _).trans hZ
    have hD0 : Formalism.MainNotions.S.Dl F.fl F'.fl 0 = 1 := by
      unfold Formalism.MainNotions.S.Dl Formalism.MainNotions.S.leadMinorE
      rw [dif_pos (Nat.zero_le _), Matrix.det_isEmpty]
    unfold Formalism.MainNotions.S.Gflag
    rw [hD1, hD0, hT', star_neg, hTs, star_one]
    ring
  · have hD : ∀ l, (hl : l ≤ r + 1) → r ≤ l → Formalism.MainNotions.S.Dl F.fl F'.fl l = 0 := by
      intro l hl hrl
      unfold Formalism.MainNotions.S.Dl Formalism.MainNotions.S.leadMinorE
      rw [dif_pos hl]
      apply Matrix.det_eq_zero_of_column_eq_zero (⟨0, by omega⟩ : Fin l)
      intro i
      simp only [Matrix.submatrix_apply]
      have h0 := hz (Fin.castLE hl i) ⟨0, hr⟩
      convert h0 using 2
      exact Fin.ext rfl
    unfold Formalism.MainNotions.S.Gflag
    rw [hD (r + 1) le_rfl (by omega), hD r (by omega) le_rfl]
    simp

end IdCell

section IdCellD

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem identityCell_vanishes (u u' : D.what₂.Word) : IdentityCellVanishes Y u u' := by
  unfold IdentityCellVanishes
  intro t ht
  obtain ⟨F', ⟨h, hm⟩, hid⟩ := ht
  have hr : TermDef.Rel t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') ⟨F', h⟩ (Quot.out t.cls) :=
    (eqIff_base (u' := u') t.lam t.mem _ _).1 (hm.trans (Quot.out_eq t.cls).symm)
  have h0 := gval_of_isIdF (star_natCast _) t.lam (lf D (X.Fu u)) F' hid
  have e : ∀ l, Formalism.MainNotions.S.Dl (X.Fu u) (Quot.out t.cls).1.fl l = Formalism.MainNotions.S.Dl (X.Fu u) F'.fl l :=
    PI.TermAttrConst.UnitaryGroupMassFormula.dl_eq _ hr
  refine Eq.trans ?_ h0
  show Formalism.MainNotions.S.Gflag (X.Fu u) (Quot.out t.cls).1.fl = Formalism.MainNotions.S.Gflag (X.Fu u) F'.fl
  unfold Formalism.MainNotions.S.Gflag
  rw [e, e]

end IdCellD

def AtSomeAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word), AtSome Y u u'

def PairTiesAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (hF : FinX Y) (W : WittDat X) (hI : SIso D.s (sOf hF)),
    PairTies W hI

def FibFinAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) (t : RT Y u u'), Finite (fib Y t)

def PairIndepAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) (s₁ s₂ s₁' s₂' : TT Y u u'),
    s₁.toTerm = s₁'.toTerm → s₂.toTerm = s₂'.toTerm →
    rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ →
    rowOf Y.TR (Y.cs u) (Y.cs u') s₁' = rowOf Y.TR (Y.cs u) (Y.cs u') s₂' →
    s0T s₁ s₂ = s0T s₁' s₂' ∧ (liftScalar s₁ s₂ ↔ liftScalar s₁' s₂')

end Formalism.L2.SG.TermTieOf
