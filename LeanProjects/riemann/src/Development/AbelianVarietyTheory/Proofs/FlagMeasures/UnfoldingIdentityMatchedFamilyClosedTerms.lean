import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusLocalDataProductLocalWeightsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowWeightsLocalOrbitsSumEqGenusMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPairStatement

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.FourierDecayAlt GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.Tied

theorem infinite_finPl (K : Type) [Field K] [NumberField K] : Infinite (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), la.asIdeal.comap (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)

section Scale

open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_scale₂ (H : HermSp M V) (c d : E) (x y : V) :
    H.h (c • x) (d • y) = M.L.cj d * c * H.h x y := by
  rw [H.h_smul_left, H.h_herm (d • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]
  ring

theorem dl_scale₂ (H : HermSp M V) {r : ℕ} (s s' : Fin (r + 1) → E) (f f' : Fin (r + 1) → V) (l : ℕ)
    (hl : l ≤ r + 1) :
    H.Dl (fun a => s a • f a) (fun b => s' b • f' b) l =
      (∏ i : Fin l, M.L.cj (s (Fin.castLE hl i)) * s' (Fin.castLE hl i)) * H.Dl f f' l := by
  unfold HermSp.Dl
  rw [dif_pos hl, dif_pos hl]
  have hsub : (H.Zhat (fun a => s a • f a) (fun b => s' b • f' b)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i => M.L.cj (s (Fin.castLE hl i))) *
        (H.Zhat f f').submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun i => s' (Fin.castLE hl i)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.submatrix_apply, HermSp.Zhat, Matrix.of_apply, h_scale₂]
    ring
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_mul_distrib]
  ring

end Scale

theorem dl_bcP (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (l : ℕ) :
    (locH Z p).Dl (fun a => baseChange₂ D p (frame F a)) (fun b => baseChange₂ D p (frame F' b)) l =
      (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl l) := by
  unfold Loc.HermSp.Dl Formalism.MainNotions.S.Dl leadMinorE
  split_ifs with hl
  · rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Loc.HermSp.Zhat,
      Formalism.MainNotions.S.Zhat, Matrix.of_apply]
    exact baseChangeAt_form Z.M p (Z.hcj p) _ _
  · simp

theorem gval_ne_of_locGv (D : D7) (Z : LocDat D) (p : PlF D) (u u' : D.what₂.Word)
    (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (P : LocNG.FPair (locH Z p) D.R.rS) (hP : GlobalTheory.LocOver.AtBase Z p F F' (Tu D u) (Tu D u') P)
    (hG : P.Gv ≠ 0) : Gval F F' ≠ 0 := by
  intro h0
  apply hG
  obtain ⟨hA, hB, hT, hT'⟩ := hP
  have hs : ∀ (f : Fin (D.R.rS + 1) → (VS D).V),
      GlobalTheory.LocOver.scaled Z p f = fun a => frFac Z.δ p a • baseChange₂ D p (f a) := fun _ => rfl
  have hD : ∀ l (hl : l ≤ D.R.rS + 1),
      (locH Z p).Dl (GlobalTheory.LocOver.scaled Z p (frame F)) (GlobalTheory.LocOver.scaled Z p (frame F')) l =
        (∏ i : Fin l, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * frFac Z.δ p (Fin.castLE hl i)) *
          (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl l) := by
    intro l hl
    rw [hs (frame F), hs (frame F'), dl_scale₂ _ _ _ _ _ l hl, dl_bcP]
  have hlast : frFac Z.δ p (Fin.last D.R.rS) = 1 := by
    simp [frFac]
  have hc : (∏ i : Fin (D.R.rS + 1), (Z.M p).L.cj (frFac Z.δ p (Fin.castLE le_rfl i)) *
      frFac Z.δ p (Fin.castLE le_rfl i)) =
      ∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE (Nat.le_succ _) i)) *
        frFac Z.δ p (Fin.castLE (Nat.le_succ _) i) := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.castLE_rfl, id]
    rw [hlast, map_one, mul_one, mul_one]
    rfl
  unfold LocNG.FPair.Gv Loc.HermSp.Gdet Loc.HermSp.normE
  rw [hA, hB, hT, hT', hD _ le_rfl, hD _ (Nat.le_succ _), hc]
  have hG0 : Gflag F.fl F'.fl = 0 := h0
  unfold Gflag at hG0
  have hι := congrArg (D.s.atP p).ιE hG0
  rw [map_zero] at hι
  simp only [map_sub, map_mul, map_natCast] at hι
  have hcj : ∀ z, (Z.M p).L.cj ((D.s.atP p).ιE z) = (D.s.atP p).ιE (star z) := cj_iota (Z.hcj p)
  simp only [map_mul, hcj, map_natCast]
  set c := ∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE (Nat.le_succ _) i)) *
        frFac Z.δ p (Fin.castLE (Nat.le_succ _) i)
  linear_combination (c * (Z.M p).L.cj c) * hι

theorem wt_self {D : D7} {Z : LocDat D} {p : PlF D} {P : LocNG.FPair (locH Z p) D.R.rS} (d : LocNG.Datum P) :
    LocNG.Datum.wt d d = 1 := by
  simp [LocNG.Datum.wt, LocNG.volRel, Subgroup.relIndex_self]

theorem unfold_tied : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl), ClsRow TS cls → (∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ FP : ∀ p : PlF D, LocNG.FPair (locH (zOf Y) p) D.R.rS, Based (zOf Y) FP (Tu D u) (Tu D u') F F' → LocClosed F F' (zOf Y) FP TS) → ∀ (γ : PN.Pts D.host.E D.R.rS) (Fm : LocFam (zOf Y) Cl (NuC D)), FamTie TS cls (nmlOf Y u u') γ Fm → ∃ V0, OrbitFamilyIdentityAt Fm V0 := by
  intro D X Y u u' Cl TS cls hCls hLC γ Fm hT
  obtain ⟨w, F00, F'0, F'1, hγ, hD, hV0, hn, hZ, hFP, hOm, hPr, hStd, ht0, hPtm, hΛ, hdat, hgen⟩ := hT
  subst hγ
  haveI := infinite_finPl D.host.F
  obtain ⟨p0, hp0⟩ : ∃ p, p ∉ Fm.P := by
    by_contra h
    push_neg at h
    exact Set.infinite_univ (α := PlF D) (Fm.P.finite_toSet.subset fun p _ => h p)
  have hBased : Based (zOf Y) Fm.FP (Tu D u) (Tu D u') F00 F'0 := fun p => hFP p
  have hG : Gval F00 F'0 ≠ 0 := by
    refine gval_ne_of_locGv D (zOf Y) p0 u u' F00 F'0 (Fm.FP p0) (hBased p0) ?_
    obtain ⟨-, ⟨-, y, -, hy⟩, -⟩ := hPr p0 hp0
    intro h0
    rw [h0, zero_mul] at hy
    exact zero_ne_one hy
  have hLC' := hLC F00 F'0 w hZ hG Fm.FP hBased
  have hRel : ∀ p, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p)) := fun p =>
    (GlobalTheory.T.localisedBaseFrames_relevantPair D (zOf Y) u u' w F00 F'0 hZ hG p).2 _ (hBased p)
  obtain ⟨Λ₀, hΛl, hΛ₀⟩ := hΛ
  have hterm0 : ∀ p, ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ := by
    intro p
    by_cases hp : p ∈ Fm.P
    · exact hPtm p hp
    · exact ⟨_, hΛ₀ p hp⟩
  have hΛfin : ∃ Λ : LV D, Submodule.IsLattice D.host.E Λ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧
      τ.abelian₂ = lattice₂ D (zOf Y).M p Λ}.Finite := by
    refine ⟨Λ₀, hΛl, Fm.P.finite_toSet.subset fun p hp => ?_⟩
    by_contra hp'
    exact hp ⟨_, hΛ₀ p hp', rfl⟩
  obtain ⟨V1, hV1, hmass⟩ := GlobalTheory.T.mass_genus_local_data_product_local_weights D X Y u u' F00 F'0 w hZ hG (zOf Y) Fm.FP hBased hRel Fm.d0 hterm0 hΛfin
  have hΛ' : ∃ Λ : LV D, Submodule.IsLattice D.host.E Λ ∧ ∀ p, p ∉ Fm.P →
      ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ :=
    ⟨Λ₀, hΛl, fun p hp => ⟨_, hΛ₀ p hp, rfl⟩⟩
  have hdat' : ∀ c ν, (Fm.dat c ν = none → ¬ ∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧
      ∀ d, Fm.dat c ν = some d → (∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧
        ∀ t ∈ TS, cls t = c → ptPN t = toPts w → nmlOf Y u u' t = ν →
          (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) ∧ Fm.rw c = (wt t) ^ 2 := by
    intro c ν
    have h := hdat c ν
    refine ⟨fun h0 => ?_, fun d h1 => ?_⟩
    · rw [h0] at h; exact h
    · rw [h1] at h; exact h
  refine ⟨V1, hV1, ?_⟩
  intro d hd
  let dd : Dat (zOf Y) Fm.FP := fun p => if hp : p ∈ Fm.P then (d ⟨p, hp⟩).1 else Fm.d0 p
  have hdd1 : ∀ p (hp : p ∈ Fm.P), dd p = (d ⟨p, hp⟩).1 := fun p hp => by simp [dd, hp]
  have hdd2 : ∀ p, p ∉ Fm.P → dd p = Fm.d0 p := fun p hp => by simp [dd, hp]
  obtain ⟨hddT, hsum⟩ := GlobalTheory.T.rowWeights_localOrbits_sum_eq_genusMass D X Y u u' F00 F'0 w hZ hG TS cls Fm hBased hCls hLC' hD hStd hΛ' hdat' d hd
    dd hdd1 hdd2
  have hfin : {p | dd p ≠ Fm.d0 p}.Finite :=
    Fm.P.finite_toSet.subset fun p hp => by
      by_contra hp'
      exact hp (hdd2 p hp')
  rw [hsum, hmass dd hddT hfin]
  congr 2
  rw [finprod_eq_prod_of_mulSupport_subset (s := Fm.P)]
  · rw [← Finset.prod_attach]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [hdd1 p.1 p.2]
    rfl
  · intro p hp
    by_contra hp'
    exact hp (by simp only [hdd2 p hp', wt_self])

end GlobalTheory.Unfold.Tied
