import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatake
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfSupportedAtSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitSatLoc

section Local
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def rtHom (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] : GAf L n →* Module.End ℂ (GAf L n → W) where
  toFun x := NG.rt L n x
  map_one' := LinearMap.ext fun f => funext fun g => by simp [NG.rt]
  map_mul' x y := LinearMap.ext fun f => funext fun g => by simp [NG.rt, mul_assoc]

theorem rtHom_apply (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (x : GAf L n) :
    rtHom (L := L) n W x = NG.rt L n x := rfl

theorem map_symm_map (s : SplitPlace L) (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) {n : ℕ} (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    Matrix.GeneralLinearGroup.map c.symm.toRingHom
      (Matrix.GeneralLinearGroup.map c.toRingHom g : GL (Fin n) (s.w.adicCompletion L)) = g :=
  Units.ext (Matrix.ext fun a b => by simp)

theorem map_map_symm (s : SplitPlace L) (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) {n : ℕ} (g : GL (Fin n) (s.w.adicCompletion L)) :
    Matrix.GeneralLinearGroup.map c.toRingHom
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom g : GL (Fin n) (s.v.adicCompletion L⁺)) = g :=
  Units.ext (Matrix.ext fun a b => by simp)

theorem mem_Ov_iff {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    (a : s.v.adicCompletion L⁺) :
    c a ∈ Formalism.UG.Ov L s.w ↔ a ∈ (s.v.adicCompletionIntegers L⁺).toSubring := by
  show c a ∈ s.w.adicCompletionIntegers L ↔ a ∈ s.v.adicCompletionIntegers L⁺
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    GlobalTheory.SplitConjVal.valuation_eq s c hc hcL]

theorem map_mem_KGL_iff {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) {n : ℕ}
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    Matrix.GeneralLinearGroup.map c.toRingHom g ∈ GlobalTheory.LFun.KGL s.w n ↔
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring := by
  rw [GlobalTheory.LFun.KGL, GlobalTheory.HeckeScalarSph.mem_GLint_iff, GlobalTheory.HeckeScalarSph.mem_GLint_iff, ← map_inv]
  simp only [Matrix.GeneralLinearGroup.map_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, mem_Ov_iff hc hcL]

theorem isUnifV_map {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ) : Formalism.UG.IsUnifV L s.w (c ϖ) := by
  show Valued.v (c ϖ) = _
  rw [GlobalTheory.SplitConjVal.valuation_eq s c hc hcL]
  exact hϖ

theorem coe_glMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ} (g : GL (Fin n) A) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) = (g : Matrix (Fin n) (Fin n) A).map f :=
  rfl

theorem diagJ_map {A B : Type} [Field A] [Field B] (f : A →+* B) (n : ℕ) (ϖ : A) (k : ℕ) :
    (Formalism.UG.diagJ n ϖ k).map f = Formalism.UG.diagJ n (f ϖ) k := by
  simp only [Formalism.UG.diagJ, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  split_ifs <;> simp

end Local

section Key
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def locAct (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n) :
    Representation ℂ (GL (Fin n) (s.w.adicCompletion L)) (GAf L n → W) :=
  (rtHom n W).comp (e.comp (Matrix.GeneralLinearGroup.map c.symm.toRingHom))

theorem locAct_apply (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n)
    (g : GL (Fin n) (s.w.adicCompletion L)) (f : GAf L n → W) :
    locAct n W s c e g f = NG.rt L n (e (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)) f := rfl

theorem heckeD_eq_heckeVec {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n) (he1 : ∀ g, TrivOutside {s.v} (e g))
    (he2 : ∀ g, s.loc n (e g) = g) (J : Subgroup (GAf L n))
    (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ)
    (k : ℕ) {F : GAf L n → W} (hF : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ F = F) :
    NG.heckeD J (tSet L n s ϖ k) F =
      GlobalTheory.LFun.heckeVec (locAct n W s c e) (GlobalTheory.LFun.KGL s.w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov L s.w) (c ϖ) k) F := by
  classical
  have hψφ : ∀ g : GL (Fin n) (s.v.adicCompletion L⁺),
      Matrix.GeneralLinearGroup.map c.symm.toRingHom
        (Matrix.GeneralLinearGroup.map c.toRingHom g : GL (Fin n) (s.w.adicCompletion L)) = g := map_symm_map s c
  have hφψ : ∀ g : GL (Fin n) (s.w.adicCompletion L),
      Matrix.GeneralLinearGroup.map c.toRingHom
        (Matrix.GeneralLinearGroup.map c.symm.toRingHom g : GL (Fin n) (s.v.adicCompletion L⁺)) = g := map_map_symm s c
  obtain ⟨α0, -, hT0⟩ := GlobalTheory.HeckeScalarSph.exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_repsU (n := n) s.v α0
  have hR1' : ∀ γ ∈ R, γ ∈ tSet L n s ϖ k := fun γ hγ => (hT0 γ).2 (hR1 γ hγ)
  have hR2' : ∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n := fun x hx => hR2 x ((hT0 x).1 hx)
  have hD : ∀ x ∈ tSet L n s ϖ k, TrivOutside {s.v} x := fun x hx => hx.1
  rw [GlobalTheory.HeckeEigConj.heckeD_eq_sum_of_agree J hJ hD hR1' hR2' hF]
  have hU := isUnifV_map hc hcL hϖ
  rw [GlobalTheory.SatHecke.Tj_eq_dosetInd hU k]
  have hK : ∀ x, TrivOutside {s.v} x →
      (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ GlobalTheory.LFun.KGL s.w n ↔ x ∈ Umax L n) := fun x hx =>
    (map_mem_KGL_iff hc hcL _).trans (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx)
  have hFK : F ∈ GlobalTheory.PRep.fixed (locAct n W s c e) (GlobalTheory.LFun.KGL s.w n) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    rw [locAct_apply]
    refine hF _ ((hK _ (he1 _)).1 ?_) (he1 _)
    rw [he2, hφψ]; exact hA
  have hdiag : ∀ a b x : GL (Fin n) (s.v.adicCompletion L⁺),
      (x : Matrix (Fin n) (Fin n) _) = (a : Matrix (Fin n) (Fin n) _) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) _) →
      (Matrix.GeneralLinearGroup.map c.toRingHom x : GL (Fin n) (s.w.adicCompletion L)) =
        Matrix.GeneralLinearGroup.map c.toRingHom a *
          Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) *
            Matrix.GeneralLinearGroup.map c.toRingHom b := by
    intro a b x h
    refine Units.ext ?_
    simp only [Units.val_mul, coe_glMap, h, Matrix.map_mul, diagJ_map,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    rfl
  have hinj : Set.InjOn (fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
      GL (Fin n) (s.w.adicCompletion L))) R := by
    intro γ hγ δ hδ h
    have h' : s.loc n γ = s.loc n δ := by
      have := congrArg (Matrix.GeneralLinearGroup.map c.symm.toRingHom) h
      simpa only [hψφ] using this
    exact GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n s γ δ (hD γ (hR1' γ hγ)) (hD δ (hR1' δ hδ)) h'
  have hmem : ∀ γ ∈ R, (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) : GL (Fin n) (s.w.adicCompletion L)) ∈
      DoubleCoset.doubleCoset (Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
        (GlobalTheory.SatHecke.diagJ_det_ne hU k)) (GlobalTheory.LFun.KGL s.w n : Set (GL (Fin n) (s.w.adicCompletion L)))
        (GlobalTheory.LFun.KGL s.w n) := by
    intro γ hγ
    obtain ⟨-, a, ha, b, hb, h⟩ := hR1' γ hγ
    exact DoubleCoset.mem_doubleCoset.2 ⟨_, (map_mem_KGL_iff hc hcL a).2 ha, _, (map_mem_KGL_iff hc hcL b).2 hb,
      hdiag a b _ h⟩
  have huniq : ∀ g ∈ DoubleCoset.doubleCoset (Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
        (GlobalTheory.SatHecke.diagJ_det_ne hU k)) (GlobalTheory.LFun.KGL s.w n : Set (GL (Fin n) (s.w.adicCompletion L)))
        (GlobalTheory.LFun.KGL s.w n),
      ∃! r, r ∈ R.image (fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
        GL (Fin n) (s.w.adicCompletion L))) ∧ r⁻¹ * g ∈ GlobalTheory.LFun.KGL s.w n := by
    intro g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    obtain ⟨x, hx⟩ : ∃ x, x = e (Matrix.GeneralLinearGroup.map c.symm.toRingHom (y *
        Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z)) :=
      ⟨_, rfl⟩
    have hxt : TrivOutside {s.v} x := hx ▸ he1 _
    have hxT : x ∈ tSet L n s ϖ k := by
      refine ⟨hxt, Matrix.GeneralLinearGroup.map c.symm.toRingHom y, ?_,
        Matrix.GeneralLinearGroup.map c.symm.toRingHom z, ?_, ?_⟩
      · exact (map_mem_KGL_iff hc hcL _).1 (by rw [hφψ]; exact hy)
      · exact (map_mem_KGL_iff hc hcL _).1 (by rw [hφψ]; exact hz)
      · rw [hx, he2, map_mul, map_mul, Units.val_mul, Units.val_mul]
        congr 2
        rw [coe_glMap, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagJ_map]
        simp
    obtain ⟨γ, ⟨hγR, hγx⟩, hγu⟩ := hR2' x hxT
    have hkey : ∀ δ ∈ R, ((Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n δ) :
        GL (Fin n) (s.w.adicCompletion L))⁻¹ * (y * Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
          (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z) ∈ GlobalTheory.LFun.KGL s.w n ↔ δ⁻¹ * x ∈ Umax L n) := by
      intro δ hδ
      have e1 : (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n δ) : GL (Fin n) (s.w.adicCompletion L))⁻¹ *
          (y * Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z) =
          Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (δ⁻¹ * x)) := by
        rw [map_mul, map_mul, map_inv, map_inv, hx, he2, hφψ]
      rw [e1]
      exact hK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD δ (hR1' δ hδ))) hxt)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hγR, (hkey γ hγR).2 hγx⟩, ?_⟩
    rintro r ⟨hr, hr'⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hr
    rw [hγu δ ⟨hδ, (hkey δ hδ).1 hr'⟩]
  rw [GlobalTheory.LFun.heckeVec_dosetInd hFK (R := R.image fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
    GL (Fin n) (s.w.adicCompletion L))) (fun r hr => ?_) huniq, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [locAct_apply, hψφ, GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n s (e (s.loc n γ)) γ (he1 _)
      (hD γ (hR1' γ hγ)) (he2 _)]
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hr
    exact hmem γ hγ

end Key
section Main

set_option maxHeartbeats 800000 in

theorem exists_locComp_hasSatake : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ B : Multiset ℂˣ, B.card = D.R.nV → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV B k • F) → ∃ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ ∧ GlobalTheory.SmGL.HasSatake σ.ρ α ∧ Finset.univ.val.map α = B := by
  intro _ hL D P i Q sp hJ B hB F hFiso hFty hF0 hFeig
  have hirr := P.H.av.irr i Q
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV
    ({ (P.M.loc i).wt with S := P.H.av.S i Q, irrS := hirr } : NG.AutRep D.host.E D.R.nV) sp
  have hσ' : IsLocS (P.H.av.S i Q) sp σ := hσ
  obtain ⟨c, T0, hc, hcL, -, -, -⟩ := hσ'
  have hFfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → NG.rt D.host.E D.R.nV κ F = F := by
    intro κ hκ ht
    have hJκ := ((hJ κ ht).1).2 hκ
    have h1 := hFty.2 ⟨κ, hJκ⟩
    rw [(hJ κ ht).2 hJκ] at h1
    simpa using h1
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) hirr sp σ hσ c hc hcL
    (Formalism.UG.GLint (Fin D.R.nV) (sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) 1
    (fun g hg => hg) (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) F hFiso hF0
    (fun κ ht h => by
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      exact hFfix κ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff sp ht).1 h) ht)
  have hufix : u ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL sp.w D.R.nV) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    have hA' := (map_mem_KGL_iff hc hcL (Matrix.GeneralLinearGroup.map c.symm.toRingHom A)).1
      (by rw [map_map_symm]; exact hA)
    have := hu _ hA'
    rwa [map_map_symm, MonoidHom.one_apply, Units.val_one, one_smul] at this
  have hsph : GlobalTheory.SmGL.IsSpherical σ.ρ := by
    have : u ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO (sp.w.adicCompletion D.host.E) (Fin D.R.nV)) := by
      rw [GlobalTheory.HeckeEigConj.KO_eq_KGL D.host.E sp.w D.R.nV]; exact hufix
    exact (Submodule.ne_bot_iff _).2 ⟨u, this, hu0⟩
  have hR := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 sp.w)
  obtain ⟨α, hα⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake_of_unr hR ((GlobalTheory.CuspRep.ParLaws.unr_iff hR σ).2 hsph)
  have hSat := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake D.host.E sp.w D.R.nV σ.V σ.ρ α hα
  obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E D.R.nV sp
  have hspan := GlobalTheory.SpanLoc.main D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) hirr sp σ hσ c hc hcL hFiso
  rw [iSup_subtype'] at hspan
  have hFK : F ∈ GlobalTheory.PRep.fixed (locAct D.R.nV (P.M.loc i).wt.W sp c e) (GlobalTheory.LFun.KGL sp.w D.R.nV) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    rw [locAct_apply]
    refine hFfix _ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff sp (he1 _)).1 ?_) (he1 _)
    rw [he2]
    exact (map_mem_KGL_iff hc hcL _).1 (by rw [map_map_symm]; exact hA)
  have hspan' : F ∈ ⨆ T : {T : σ.V →ₗ[ℂ] (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) // (∀ v, T v ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {sp.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (sp.loc D.R.nV x)) v) = NG.rt D.host.E D.R.nV x (T v)}, LinearMap.range T.1 := hspan
  have hequiv : ∀ (T : {T : σ.V →ₗ[ℂ] (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) // (∀ v, T v ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {sp.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (sp.loc D.R.nV x)) v) = NG.rt D.host.E D.R.nV x (T v)}) g v, T.1 (σ.ρ g v) = locAct D.R.nV (P.M.loc i).wt.W sp c e g (T.1 v) := by
    intro T g v
    rw [locAct_apply, ← T.2.2 _ (he1 _) v, he2, map_map_symm]
  have hIs : GlobalTheory.LFun.IsSatVecGL sp.w (locAct D.R.nV (P.M.loc i).wt.W sp c e) F (Finset.univ.val.map α) :=
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (ρ := locAct D.R.nV (P.M.loc i).wt.W sp c e) σ.irr hSat
      Subtype.val hequiv hspan' hFK hF0
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := maximalRealSubfield D.host.E) sp.v
  have hϖ' : IsUnif D.host.E sp.v ϖ := hϖ
  have heq : ∀ k ≤ D.R.nV, GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV (Finset.univ.val.map α) k =
      GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV B k := by
    intro k hk
    have h1 := hIs.2.2.2 (c ϖ) (isUnifV_map hc hcL hϖ') k hk
    rw [← heckeD_eq_heckeVec sp c hc hcL e he1 he2 _ (fun κ ht => (hJ κ ht).1) hϖ' k hFfix, hFeig ϖ hϖ' k hk] at h1
    exact (smul_left_injective ℂ hF0 h1).symm
  exact ⟨σ, α, hσ, hα, GlobalTheory.LFun.eq_of_satEig_eq (GlobalTheory.LFun.qV_ne_zero sp.w) (by simp) hB heq⟩

end Main

end GlobalTheory.SplitSatLoc

end
