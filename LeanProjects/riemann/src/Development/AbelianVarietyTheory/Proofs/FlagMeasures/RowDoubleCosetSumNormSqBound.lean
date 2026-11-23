import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesTermsOrbitsLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianAmplitudeMassProductStructureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhaseStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericIffZeroDefectGroupCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowEqIffMovedLatticeInnerDataEqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetTermEqIffStabiliserOrbitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermOfGlobalTermStrongApproxStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetEqIffIsometryUnipotentTranslateStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTermAmplitudeEqMassMulPhaseStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.RowCoset

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem isLattice_of_lrel {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) {Γ Γ' : G.Lt}
    (hΓ : Submodule.IsLattice E Γ) (h : G.LRel Γ Γ') : Submodule.IsLattice E Γ' := by
  obtain ⟨g, -, rfl⟩ := h
  refine ⟨hΓ.fg.map _, ?_⟩
  rw [Submodule.map_coe]
  have : (((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E)) : G.V → G.V) = ((g : G.V →ₗ[E] G.V) : G.V → G.V) := rfl
  rw [this, Submodule.span_image, hΓ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem term_of_lrel {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (hk : 4 * r + 7 ≤ k) {d : G.Dat}
    (hex : ∃ Λ₀, G.IsTerm d Λ₀) {Γ Γ' : G.Lt} (hΓ : G.IsTerm d Γ) (h : G.LRel Γ Γ') : G.IsTerm d Γ' := by
  have hl := isLattice_of_lrel G hΓ.1 h
  have e := ((GlobalTheory.T.globalHermitianFrames_terms_orbits_local A r k G hk d hex).2.1 Γ Γ' hΓ hl).1 h
  refine ⟨hl, fun p => ?_⟩
  obtain ⟨s, hs, hsp⟩ := e p
  rw [hsp]
  have := (A.loc p).lf
  have := (A.loc p).char0
  exact (GlobalTheory.FrameAct.stabiliser_acts_on_terms (A.L p) r k (G.S p) (d p) _ (hΓ.2 p) s hs).1

end GlobalTheory.HL.RowCoset

namespace GlobalTheory.HL.RowCoset

theorem row_coset_sum_norm_sq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → Formalism.L2.SG.PairVal.ptOf t₀.toTerm = w → ∀ Q : Prop → Prop, ‖∑' t : TauC Y u u', {t : TauC Y u u' | (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ∧ nmlOf Y u u' t = nmlOf Y u u' t₀ ∧ Q (¬ t.generic)}.indicator (Y.tO u u').vec t‖ ^ 2 = Formalism.L2.SG.TermOp.wt t₀ ^ 2 * ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ ^ 2 * ((((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) ^ 2 * ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w)‖ ^ 2) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c ν hν t₀ ρ U U' hMv hrelv hpt Q
  set d₀ := G.datOf (c.lat ρ t₀.lam) with hd₀
  have hrow : ∀ t : TauC Y u u', (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → t.lam = t₀.lam ∧ t.lam' = t₀.lam' :=
    fun t h => ⟨congrArg (fun x => x.1.1) h, congrArg (fun x => x.2.1.1) h⟩
  have hmv : ∀ (t : TauC Y u u') n m, (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧
      t.lin = n⁻¹ * t₀.lin * m) → ∃ A A' : Formalism.L2.SG.PairVal.MatR D,
      MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
    intro t n m h
    obtain ⟨A, A', -, -, -, -, hM⟩ :=
      (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv).2.2.2.2.2 t n m h
    exact ⟨A, A', hM⟩
  have hdat : ∀ (t : TauC Y u u') n m, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ →
      (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m) →
      G.datOf (c.lat (ρ * n) t.lam) = d₀ := by
    intro t n m hr h
    obtain ⟨h1, h2⟩ := hrow t hr
    exact (GlobalTheory.T.termRow_eq_iff_movedLatticeInnerData_eq D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv t n m h1 h2 h).1 hr
  have hterm : ∀ (t : TauC Y u u') n m, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ →
      (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m) →
      G.IsTerm d₀ (c.lat (ρ * n) t.lam) := by
    intro t n m hr h
    obtain ⟨A, A', hM⟩ := hmv t n m h
    have := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t (ρ * n) (U * A) (U' * A') hM).1
    rwa [hdat t n m hr h] at this
  have hgen : ∀ (t : TauC Y u u') n m, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ →
      (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m) →
      (t.generic ↔ G.Gen d₀ (c.lat (ρ * n) t.lam)) := by
    intro t n m hr h
    obtain ⟨A, A', hM⟩ := hmv t n m h
    have := GlobalTheory.T.generic_iff_zero_defectGroup_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t (ρ * n) (U * A) (U' * A') hM
    rwa [hdat t n m hr h] at this
  have hinj : ∀ (t t' : TauC Y u u') n m n' m', (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ →
      (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t₀ →
      (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m) →
      (n' ∈ NRat (lf D (X.Fu u)) ∧ m' ∈ NRat (lf D (X.Fu u')) ∧ t'.lin = n'⁻¹ * t₀.lin * m') →
      (t = t' ↔ G.LRel (c.lat (ρ * n) t.lam) (c.lat (ρ * n') t'.lam)) := by
    intro t t' n m n' m' hr hr' h h'
    obtain ⟨a1, a2⟩ := hrow t hr
    obtain ⟨b1, b2⟩ := hrow t' hr'
    exact GlobalTheory.T.doubleCoset_term_eq_iff_stabiliserOrbit D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv t t' n m n' m' a1 a2 b1 b2 h h'
  have hex : ∃ Λ₀, G.IsTerm d₀ Λ₀ :=
    ⟨_, (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv).1⟩
  have hfin : {o : Quot G.LRel | G.IsTerm d₀ o.out}.Finite :=
    (GlobalTheory.T.hermitian_amplitude_mass_product_structure _ _ _ G hk d₀ hex (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
      (Set.finite_empty.subset fun _ ⟨_, _, h⟩ => absurd trivial h)).2.2.2
  have heqv : Equivalence G.LRel := (GlobalTheory.T.globalHermitianFrames_terms_orbits_local _ _ _ G hk d₀ hex).2.2.1
  have hsurj := fun Γ hΓ => GlobalTheory.T.exists_term_of_globalTerm_strongApprox D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv Γ hΓ
  let τ : Quot G.LRel → TauC Y u u' := fun o =>
    if h : G.IsTerm d₀ o.out then (hsurj o.out h).choose else t₀
  have hτ : ∀ o, G.IsTerm d₀ o.out → ∃ n m, (Y.tO u u').rowOf (τ o) = (Y.tO u u').rowOf t₀ ∧
      (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ (τ o).lin = n⁻¹ * t₀.lin * m) ∧
      o.out = c.lat (ρ * n) (τ o).lam := by
    intro o h
    have e : τ o = (hsurj o.out h).choose := dif_pos h
    rw [e]
    exact (hsurj o.out h).choose_spec
  let Cf : Finset (Quot G.LRel) := hfin.toFinset.filter (fun o => Q (¬ G.Gen d₀ o.out))
  have hmemC : ∀ o, o ∈ Cf ↔ G.IsTerm d₀ o.out ∧ Q (¬ G.Gen d₀ o.out) := by
    intro o
    simp [Cf]
  set S : Set (TauC Y u u') := {t : TauC Y u u' | (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ∧
    nmlOf Y u u' t = nmlOf Y u u' t₀ ∧ Q (¬ t.generic)} with hS
  have hτS : ∀ o ∈ Cf, τ o ∈ S := by
    intro o ho
    obtain ⟨hT, hPo⟩ := (hmemC o).1 ho
    obtain ⟨n, m, hr, h, he⟩ := hτ o hT
    refine ⟨hr, (GlobalTheory.T.doubleCoset_eq_iff_isometry_unipotent_translate D X Y u u' hSt t₀ (τ o)).2 ⟨n, m, h⟩, ?_⟩
    have hg := hgen (τ o) n m hr h
    rw [← he] at hg
    have : (¬ (τ o).generic) = (¬ G.Gen d₀ o.out) := propext (not_congr hg)
    rw [this]
    exact hPo
  have hτinj : Set.InjOn τ Cf := by
    intro o ho o' ho' e
    obtain ⟨hT, -⟩ := (hmemC o).1 ho
    obtain ⟨hT', -⟩ := (hmemC o').1 ho'
    obtain ⟨n, m, hr, h, he⟩ := hτ o hT
    obtain ⟨n', m', hr', h', he'⟩ := hτ o' hT'
    have hl := (hinj (τ o) (τ o') n m n' m' hr hr' h h').1 e
    rw [← he, ← he'] at hl
    calc o = Quot.mk G.LRel o.out := (Quot.out_eq o).symm
      _ = Quot.mk G.LRel o'.out := Quot.sound hl
      _ = o' := Quot.out_eq o'
  have hτsurj : ∀ t ∈ S, ∃ o ∈ Cf, τ o = t := by
    rintro t ⟨hr, hn, hq⟩
    obtain ⟨n, m, h⟩ := (GlobalTheory.T.doubleCoset_eq_iff_isometry_unipotent_translate D X Y u u' hSt t₀ t).1 hn
    have hΓ := hterm t n m hr h
    obtain ⟨o, ho⟩ : ∃ o : Quot G.LRel, o = Quot.mk G.LRel (c.lat (ρ * n) t.lam) := ⟨_, rfl⟩
    have hrel1 : G.LRel (c.lat (ρ * n) t.lam) o.out := by
      have e : Quot.mk G.LRel o.out = Quot.mk G.LRel (c.lat (ρ * n) t.lam) := by rw [Quot.out_eq o, ho]
      exact heqv.symm ((Equivalence.eqvGen_iff heqv).1 (Quot.eqvGen_exact e))
    have hT : G.IsTerm d₀ o.out := term_of_lrel G hk hex hΓ hrel1
    obtain ⟨n', m', hr', h', he'⟩ := hτ o hT
    have heq : τ o = t := (hinj (τ o) t n' m' n m hr' hr h' h).2 (by rw [← he']; exact heqv.symm hrel1)
    refine ⟨o, (hmemC o).2 ⟨hT, ?_⟩, heq⟩
    have hg := hgen (τ o) n' m' hr' h'
    rw [← he', heq] at hg
    have : (¬ G.Gen d₀ o.out) = (¬ t.generic) := propext (not_congr hg.symm)
    rw [this]
    exact hq
  obtain ⟨T, hTn, hamp⟩ :=
    GlobalTheory.T.rowTerm_amplitude_eq_mass_mul_phase D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c ν hν t₀ ρ U U' hMv hrelv hpt
  set K : ℝ := ((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹ with hK
  let q₀ : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u'} := (⟨t₀.lam, t₀.mem⟩, ⟨t₀.lam', t₀.mem'⟩)
  let V : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) → H1 X u u' (Y.what₂ u) (Y.what₂ u') :=
    fun x => WithLp.toLp 2 (fun q => if q = q₀ then x else 0)
  have hVadd : ∀ x y, V x + V y = V (x + y) := by
    intro x y
    show WithLp.toLp 2 _ + WithLp.toLp 2 _ = WithLp.toLp 2 _
    rw [← WithLp.toLp_add]
    congr 1
    funext q
    by_cases h : q = q₀ <;> simp [h]
  have hV0 : V 0 = 0 := by
    show WithLp.toLp 2 _ = 0
    have : (fun q => if q = q₀ then (0 : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u)) else 0) = 0 := by
      funext q; simp
    rw [this]
    rfl
  have hVsum : ∀ (s : Finset (Quot G.LRel)) (x : Quot G.LRel → Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u)),
      ∑ o ∈ s, V (x o) = V (∑ o ∈ s, x o) := by
    intro s x
    induction s using Finset.induction_on with
    | empty => simp [hV0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, hVadd]
  have hVn : ∀ x, ‖V x‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    show ‖(WithLp.toLp 2 (fun q => if q = q₀ then x else 0) : H1 X u u' (Y.what₂ u) (Y.what₂ u'))‖ ^ 2 = _
    rw [PiLp.norm_sq_eq_of_L2]
    have : ∀ q, ‖(if q = q₀ then x else 0 : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u))‖ ^ 2 =
        if q = q₀ then ‖x‖ ^ 2 else 0 := fun q => by by_cases h : q = q₀ <;> simp [h]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hvec : ∀ o ∈ Cf, (Y.tO u u').vec (τ o) = V (((Formalism.L2.SG.TermOp.wt t₀ : ℝ) : ℂ) •
      Formalism.L2.SG.PackageTie.hsEmb ((((K * G.mu o.out : ℝ) : ℂ) * G.om d₀ o.out) • T)) := by
    intro o ho
    obtain ⟨hT, -⟩ := (hmemC o).1 ho
    obtain ⟨n, m, hr, h, he⟩ := hτ o hT
    obtain ⟨h1, h2⟩ := hrow (τ o) hr
    have ha := hamp (τ o) n m hr h
    rw [← he] at ha
    show WithLp.toLp 2 _ = WithLp.toLp 2 _
    congr 1
    funext q
    have hq : ((⟨(τ o).lam, (τ o).mem⟩, ⟨(τ o).lam', (τ o).mem'⟩) :
        {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u'}) = q₀ := Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    have hw : Formalism.L2.SG.TermOp.wt (τ o) = Formalism.L2.SG.TermOp.wt t₀ := by
      unfold Formalism.L2.SG.TermOp.wt
      rw [h1, h2]
    rw [hq, hw, ha]
  have hzero : ∀ t ∉ Cf.image τ, S.indicator (Y.tO u u').vec t = 0 := by
    intro t ht
    apply Set.indicator_of_notMem
    intro hSt'
    obtain ⟨o, ho, e⟩ := hτsurj t hSt'
    exact ht (Finset.mem_image.2 ⟨o, ho, e⟩)
  have hampeq : G.amp d₀ (fun Γ => Q (¬ G.Gen d₀ Γ)) = ∑ o ∈ Cf, (G.mu o.out : ℂ) * G.om d₀ o.out := by
    unfold GFrames.amp
    rw [tsum_eq_sum (s := Cf)]
    · exact Finset.sum_congr rfl fun o ho => if_pos ((hmemC o).1 ho)
    · intro o ho
      exact if_neg fun h => ho ((hmemC o).2 h)
  rw [tsum_eq_sum hzero, Finset.sum_image hτinj]
  rw [Finset.sum_congr rfl fun o ho => by rw [Set.indicator_of_mem (hτS o ho), hvec o ho], hVsum, hVn]
  have hsum : ∑ o ∈ Cf, ((Formalism.L2.SG.TermOp.wt t₀ : ℝ) : ℂ) •
      Formalism.L2.SG.PackageTie.hsEmb ((((K * G.mu o.out : ℝ) : ℂ) * G.om d₀ o.out) • T) =
      ((Formalism.L2.SG.TermOp.wt t₀ : ℝ) : ℂ) • (((K : ℂ) * G.amp d₀ (fun Γ => Q (¬ G.Gen d₀ Γ))) •
        Formalism.L2.SG.PackageTie.hsEmb T) := by
    rw [hampeq, Finset.mul_sum, Finset.sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [map_smul]
    congr 2
    push_cast
    ring
  rw [hsum, norm_smul, norm_smul, norm_mul, hTn, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  simp only [mul_pow, sq_abs]
  ring

end GlobalTheory.HL.RowCoset
