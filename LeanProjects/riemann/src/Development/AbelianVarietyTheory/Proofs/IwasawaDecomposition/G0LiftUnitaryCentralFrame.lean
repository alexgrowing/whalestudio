import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivOutsideListProd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHeckeSplitPlaceSetIffDoubleCoset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlaceLevelPlacesDistinctUnderlying
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.BlockLiftFrame

open ReciprocityTheory.Aut GlobalTheory.CenFrame

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_isCompOf (s : SplitPlace L) {κ : Formalism.AUTREP.GAf L n} (hκ : κ ∈ Umax L n) :
    ∃ y : GL (Fin n) (Os s), IsCompOf s κ y := by
  obtain ⟨y, hy⟩ := GlobalTheory.TSetDoubleCoset.loc_mem_GLint s hκ
  refine ⟨y, fun a c => ?_⟩
  rw [← hy]
  rfl

theorem isCompOf_one_of_not_mem (s : SplitPlace L) {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    (h : s.v ∉ T) {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside T x) : IsCompOf s x 1 := by
  have e : s.loc n x = 1 := by
    apply Units.ext
    refine Matrix.ext fun a b => ?_
    have hc : compAt L s.v (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b - (1 : Matrix (Fin n) (Fin n) (AL L)) a b) = 0 := by
      have := congrFun (congrFun (hx s.v h) a) b
      rw [Matrix.map_apply] at this
      rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h0 := GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero L s _ hc
    rw [map_sub, sub_eq_zero] at h0
    show s.proj (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b) =
      (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b
    rw [h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  intro a c
  rw [e]
  by_cases hac : a = c <;> simp [Matrix.one_apply, hac]

theorem isBlockDiagonal_reduction_of_blockLift_splitPlace (s : SplitPlace L) {r p : ℕ} [NeZero p] (γ : GL (Fin r) (ZMod p)) {κ : Formalism.AUTREP.GAf L n}
    {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) (hl : GlobalTheory.PendOf.IsLiftAt s r p γ (s.loc n κ)) {k : Type} [CommRing k]
    (φ : Os s →+* k) (hφ : IsResidue s φ) (i : ZMod p →+* k) :
    GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (Formalism.UG.bc i γ) (Matrix.GeneralLinearGroup.map φ y) := by
  intro a b
  have hl' := hl a b
  have hyab := hy a b
  show φ (y.val a b) = _
  by_cases hab : a.val < r ∧ b.val < r
  · rw [dif_pos hab] at hl' ⊢
    show φ (y.val a b) = i ((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩)
    set m : ℕ := ((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val with hm
    have h0 : φ (y.val a b - (m : Os s)) = 0 := by
      rw [hφ.ker]
      push_cast
      rw [hyab]
      exact hl'
    rw [map_sub, sub_eq_zero, map_natCast] at h0
    rw [h0, ← map_natCast i m, hm, ZMod.natCast_zmod_val]
  · rw [dif_neg hab] at hl' ⊢
    have h1 : ((y.val a b : Os s) : s.v.adicCompletion (maximalRealSubfield L)) = if a = b then 1 else 0 := by
      rw [hyab]; exact hl'
    split_ifs at h1 ⊢ with hab'
    · have h2 : y.val a b = 1 := Subtype.ext (by simpa using h1)
      rw [h2, map_one]
    · have h2 : y.val a b = 0 := Subtype.ext (by simpa using h1)
      rw [h2, map_zero]

end Local

theorem not_mem_gPl_of_twist (D : D7) {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) (s : SplitPlace D.host.E)
    (hs : s.w ∈ Q) : s.v ∉ GlobalTheory.PendOf.gPl D := by
  rintro ⟨kv, hov⟩
  obtain ⟨q, hq, hcard, -, hqg⟩ := (hQ s.w hs).1
  have hg : (D.host.g kv.1 : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    have h0 : (D.host.g kv.1 : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := D.naut.plGw_over kv.1 kv.2
    have h1 : ((D.host.g kv.1 : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hov, Ideal.mem_comap, map_natCast]; exact h0
    rw [← s.w_under, Ideal.mem_comap, map_natCast] at h1
    exact h1
  exact GlobalTheory.LevelTypePlace.not_two_primes s.w.asIdeal (D.host.g_prime kv.1) hq (hqg kv.1).symm hg
    (GlobalTheory.LevelTypePlace.natCast_mem_of_card s.w hcard hq.ne_zero)

theorem exists_blockLift (D : D7) {Q Pg : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {G : Type} [Group G]
    (eG : G ≃* G0 Pg D.R.r) (cG : G0 Pg D.R.r ≃* G0g D.nd)
    (hgrp : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
      (∀ kv, ((plg kv : Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
      ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)) :
    ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV,
      GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) ∧
      ∀ g (s' : SplitPlace D.host.E) (φ : Os s' →+* kP s'.w), IsResidue s' φ →
        (s'.w ∈ Q → ∃ y, IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
        ∀ hP : s'.w ∈ Pg, ∃ y, IsCompOf s' (L g) y ∧
          GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (eG ((eG.trans cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  obtain ⟨plg, iso, hpl, hg⟩ := hgrp
  obtain ⟨L, hL, hU⟩ := GlobalTheory.LiftStandardGroup.main D D.R.nV (by unfold Ranks.nV; omega)
  refine ⟨L, hL, hU, fun g s' φ hφ => ⟨fun hs => ?_, fun hP => ?_⟩⟩
  · exact ⟨1, isCompOf_one_of_not_mem s' (not_mem_gPl_of_twist D hQ s' hs) (hL g).1, map_one _⟩
  · obtain ⟨y, hy⟩ := exists_isCompOf s' (hU g)
    refine ⟨y, hy, ?_⟩
    have hkv : plg (plg.symm ⟨s'.w, hP⟩) = ⟨s'.w, hP⟩ := plg.apply_symm_apply _
    have key : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (PP : Pg), plg kv = PP →
        ∃ i : ZMod (D.host.g kv.1) →+* kP PP.1, eG ((eG.trans cG).symm g) PP = Formalism.UG.bc i (g kv) := by
      intro kv PP hPP
      subst hPP
      exact ⟨iso kv, by rw [hg, MulEquiv.apply_symm_apply]⟩
    obtain ⟨i, hi⟩ := key _ _ hkv
    rw [hi]
    have hw : s'.w = D.naut.plGw (plg.symm ⟨s'.w, hP⟩).1 (plg.symm ⟨s'.w, hP⟩).2 := by
      rw [← hpl, hkv]
    haveI : NeZero (D.host.g (plg.symm ⟨s'.w, hP⟩).1) := ⟨(D.host.g_prime _).ne_zero⟩
    exact isBlockDiagonal_reduction_of_blockLift_splitPlace s' (g _) hy ((hL g).2 _ s' hw) φ hφ i

end GlobalTheory.BlockLiftFrame

end

theorem GlobalTheory.BlockLiftFrame.atMem : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ _ =>
  ∀ s, ∃ L : G0g (w.st Z).toD7.nd → Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift (w.st Z).toD7 (w.st Z).toD7.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV) ∧
    ∀ g (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ t.r.z.R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ t.r.z.R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (t.r.z.R.eG ((t.r.z.R.eG.trans t.r.z.cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE hR hP => ?_
  intro s
  obtain ⟨plg, iso, h1, -, -, h4⟩ := t.r.z.pins.keep.grp
  exact GlobalTheory.BlockLiftFrame.exists_blockLift (w.st Z).toD7 (t.r.z.lev.is.Q_pl s) t.r.z.R.eG t.r.z.cG ⟨plg, iso, h1, h4⟩
