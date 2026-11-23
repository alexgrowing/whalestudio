import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstLiftXPowFrob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedPDivGroupChartOfIsConnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawOfIsLawOfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedExtensionOfSeriesPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationOfSeriesPairsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFormalGroupLawCoboundaryOneEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogReducesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPullbackTeichmullerLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleFreeFiniteOfReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModNoPTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesSemilinearPDivGroupHomChaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomChartConstantCoeffSubstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartSemilinearHomIsFormalGrouStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationNaturalSemilinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFormalGroupLawQuasiLogarithmsStatement

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

section Pull

variable {p : ℕ} [Fact p.Prime]

theorem semiPull_exists {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] (σ : k →+* k') {d e : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'} (hμ : IsLaw μ) (hν : IsLaw ν)
    (φ : Fin d → MvPowerSeries (Fin e) k') (hφ : IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ) :
    ∃ m : Mod p hμ →ₛₗ[WittVector.map (p := p) σ] Mod p hν, ∀ f : quasiLog p hμ, ∃ g : quasiLog p hν,
      g.1 = subst (fun j => Katz.lift p (φ j)) (MvPowerSeries.map (frMap p σ) f.1) ∧
      m (Submodule.Quotient.mk f) = Submodule.Quotient.mk g := by
  have hσμ := GlobalTheory.T.isCommFormalGroupLaw_map k k' σ d μ hμ
  have hB := GlobalTheory.T.map_formalGroupLawQuasiLogarithms p k k' σ d μ hμ hσμ
  obtain ⟨m1, hm1⟩ := GlobalTheory.Katz.ModHom.map_exists p k' e d ν _ hν hσμ φ hφ
  let L0 : quasiLog p hμ →ₛₗ[WittVector.map (p := p) σ] quasiLog p hσμ :=
    { toFun := fun f => ⟨MvPowerSeries.map (frMap p σ) f.1, (hB f.1 f.2).1⟩
      map_add' := fun f g => Subtype.ext (map_add _ _ _)
      map_smul' := fun r f => Subtype.ext (by
        ext α
        change coeff α (MvPowerSeries.map (frMap p σ) (r • f.1)) =
          coeff α ((WittVector.map (p := p) σ r) • MvPowerSeries.map (frMap p σ) f.1)
        rw [← algebraMap_smul (Fr p k) r f.1, ← algebraMap_smul (Fr p k') (WittVector.map (p := p) σ r),
          coeff_map, coeff_smul, coeff_smul, coeff_map]
        simp only [smul_eq_mul, map_mul, frMap_algebraMap]) }
  let m0 : Mod p hμ →ₛₗ[WittVector.map (p := p) σ] Mod p hσμ :=
    Submodule.mapQ _ _ L0 (fun f hf => (hB f.1 f.2).2.1 hf)
  refine ⟨m1.comp m0, fun f => ?_⟩
  obtain ⟨g, hg, hmg⟩ := hm1 (L0 f)
  exact ⟨g, hg, hmg⟩

end Pull

section Chart

variable {p : ℕ} [Fact p.Prime]

def IsChartPull {k k' : Type} [Field k] [CharP k p] [Field k'] [CharP k' p] {σ : k →+* k'}
    {G : PDivGroup p k} {G' : PDivGroup p k'} {d e : ℕ} (c : Chart G d) (c' : Chart G' e)
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'}
    (hμ : IsLaw μ) (hν : IsLaw ν) (s : SemiHom σ G' G) (m : Mod p hμ → Mod p hν) : Prop :=
  ∀ φ : Fin d → MvPowerSeries (Fin e) k', (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) →
    ∀ f : quasiLog p hμ, ∃ g : quasiLog p hν,
      g.1 = subst (fun j => Katz.lift p (φ j)) (MvPowerSeries.map (frMap p σ) f.1) ∧
      m (Submodule.Quotient.mk f) = Submodule.Quotient.mk g

theorem chartPull_exists {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G : PDivGroup p k} {G' : PDivGroup p k'} {d e : ℕ}
    (c : Chart G d) (c' : Chart G' e) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'} (hμ : IsLaw μ) (hν : IsLaw ν) (hc : c.IsLawOf μ)
    (hc' : c'.IsLawOf ν) (s : SemiHom σ G' G) :
    ∃ m : Mod p hμ →ₛₗ[WittVector.map (p := p) σ] Mod p hν, IsChartPull c c' hμ hν s m := by
  obtain ⟨φ, hφ, huniq⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k k' σ d e G G' c c' s
  obtain ⟨m, hm⟩ := semiPull_exists σ hμ hν φ (GlobalTheory.T.connectedPDivGroupChart_semilinearHom_isFormalGroupHom p k k' σ d e G G' c c' s μ ν φ hc hc' hφ)
  refine ⟨m, fun ψ hψ f => ?_⟩
  rw [huniq ψ hψ]
  exact hm f

theorem mk_eq_mk_of_sub {k : Type} [Field k] [CharP k p] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} {hμ : IsLaw μ} (f g : quasiLog p hμ)
    (h : f.1 - g.1 ∈ intBy p k (Fin d) 1) :
    (Submodule.Quotient.mk f : Mod p hμ) = Submodule.Quotient.mk g :=
  by
  refine (Submodule.Quotient.eq _).2 ?_
  change ((f - g : quasiLog p hμ) : MvPowerSeries (Fin d) (Fr p k)) ∈ intBy p k (Fin d) 1
  rw [Submodule.coe_sub]
  exact h

theorem chartPull_comp {k k' k'' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Field k''] [CharP k'' p] [PerfectRing k'' p] {σ : k →+* k'} {τ : k' →+* k''}
    {υ : k →+* k''} {G : PDivGroup p k} {G' : PDivGroup p k'} {G'' : PDivGroup p k''} {d e e' : ℕ}
    (c : Chart G d) (c' : Chart G' e) (c'' : Chart G'' e')
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'}
    {κ : Fin e' → MvPowerSeries (Fin e' ⊕ Fin e') k''} (hμ : IsLaw μ) (hν : IsLaw ν) (hκ : IsLaw κ)
    (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G)
    (hu : ∀ n a, u.app n a = t.app n (s.app n a))
    (ms : Mod p hμ → Mod p hν) (mt : Mod p hν → Mod p hκ) (mu : Mod p hμ → Mod p hκ)
    (hs : IsChartPull c c' hμ hν s ms) (ht : IsChartPull c' c'' hν hκ t mt)
    (hmu : IsChartPull c c'' hμ hκ u mu) (x : Mod p hμ) : mu x = mt (ms x) := by
  obtain rfl := ringHom_eq_of_app s t u hu
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  obtain ⟨φs, hφs, -⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k k' σ d e G G' c c' s
  obtain ⟨φt, hφt, -⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k' k'' τ e e' G' G'' c' c'' t
  have h3s := GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst p k k' σ d e G G' c c' s φs hφs
  have h3t := GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst p k' k'' τ e e' G' G'' c' c'' t φt hφt
  let ψ : Fin d → MvPowerSeries (Fin e) k'' := fun j => MvPowerSeries.map τ (φs j)
  have hψ0 : ∀ j, constantCoeff (ψ j) = 0 := fun j => by
    simp only [ψ, constantCoeff_map, h3s.1 j, map_zero]
  have hφu : ∀ n j, c''.ev n (subst φt (ψ j)) = u.app n (c.x n j) := fun n j => by
    rw [h3t.2 n, hφs, hu]
  obtain ⟨gs, hgs, hms⟩ := hs φs hφs f
  obtain ⟨gt, hgt, hmt⟩ := ht φt hφt gs
  obtain ⟨gu, hgu, hmu'⟩ := hmu (fun j => subst φt (ψ j)) hφu f
  rw [hmu', hms, hmt]
  refine mk_eq_mk_of_sub gu gt ?_
  have hσμ := GlobalTheory.T.isCommFormalGroupLaw_map k k'' (τ.comp σ) d μ hμ
  have hF := (GlobalTheory.T.map_formalGroupLawQuasiLogarithms p k k'' (τ.comp σ) d μ hμ hσμ f.1 f.2).1
  have key := (GlobalTheory.Katz.PullQuasiLog.main p k'' e d (fun i => MvPowerSeries.map (τ.comp σ) (μ i)) hσμ _ hF).2.1
    e' φt ψ (h3t.1) hψ0
  rw [hgu, hgt, hgs, map_subst_lift p τ φs h3s.1, MvPowerSeries.map_map, ← frMap_comp]
  exact key

end Chart

section ChartRules

variable {p : ℕ} [Fact p.Prime]

theorem chartPull_id {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G : PDivGroup p k} {d : ℕ}
    (c : Chart G d) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (hμ : IsLaw μ)
    (m : Mod p hμ → Mod p hμ) (hm : IsChartPull c c hμ hμ (SemiHom.ofHom (𝟙 G)) m) (x : Mod p hμ) :
    m x = x := by
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  obtain ⟨g, hg, hmg⟩ := hm (fun j => X j) (fun n j => by
    rw [SemiHom.ofHom_app, id_app]
    exact GlobalTheory.Katz.evA_X k (Fin d) (G.A n) (c.x n) (c.nil n) j) f
  rw [hmg]
  refine mk_eq_mk_of_sub g f ?_
  rw [hg, frMap_id, MvPowerSeries.map_id, RingHom.id_apply,
    (GlobalTheory.Katz.PullQuasiLog.main p k d d μ hμ f.1 f.2).1, sub_self]
  exact zero_mem _

theorem chartPull_add {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H : PDivGroup p k} {d e : ℕ}
    (cG : Chart G d) (cH : Chart H e) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k} (hμ : IsLaw μ) (hν : IsLaw ν) (hcH : cH.IsLawOf ν)
    (f g : G ⟶ H) (mf mg mfg : Mod p hν → Mod p hμ)
    (hf : IsChartPull cH cG hν hμ (SemiHom.ofHom f) mf) (hg : IsChartPull cH cG hν hμ (SemiHom.ofHom g) mg)
    (hfg : IsChartPull cH cG hν hμ (SemiHom.ofHom (f + g)) mfg) (x : Mod p hν) :
    mfg x = mf x + mg x := by
  induction x using Submodule.Quotient.induction_on with | _ y => ?_
  obtain ⟨φf, hφf, -⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k k (RingHom.id k) e d H G cH cG (SemiHom.ofHom f)
  obtain ⟨φg, hφg, -⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k k (RingHom.id k) e d H G cH cG (SemiHom.ofHom g)
  have c1 := (GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst p k k (RingHom.id k) e d H G cH cG _ φf hφf).1
  have c2 := (GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst p k k (RingHom.id k) e d H G cH cG _ φg hφg).1
  have hsum : cG.IsMapOf cH (f + g) (op ν φf φg) :=
    GlobalTheory.T.isMapOf_add_formalGroupLawEvalPoints p k d e G H cG cH ν f g φf φg hcH (fun n j => hφf n j) (fun n j => hφg n j)
  obtain ⟨a, ha, hma⟩ := hf φf hφf y
  obtain ⟨b, hb, hmb⟩ := hg φg hφg y
  obtain ⟨s, hs, hms⟩ := hfg (op ν φf φg) (fun n j => hsum n j) y
  rw [hma, hmb, hms, ← Submodule.Quotient.mk_add]
  refine mk_eq_mk_of_sub s (a + b) ?_
  rw [Submodule.coe_add, hs, ha, hb, frMap_id, MvPowerSeries.map_id, RingHom.id_apply, ← sub_sub]
  exact (GlobalTheory.Katz.PullQuasiLog.main p k d e ν hν y.1 y.2).2.2 φf φg c1 c2

theorem chartPull_red {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G : PDivGroup p k} {G' : PDivGroup p k'} {d e : ℕ}
    (c : Chart G d) (c' : Chart G' e) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'} (hμ : IsLaw μ) (hν : IsLaw ν) (hc : c.IsLawOf μ)
    (hc' : c'.IsLawOf ν) (s : SemiHom σ G' G) (m : Mod p hμ → Mod p hν) (hm : IsChartPull c c' hμ hν s m)
    (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt)
    (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] G'.RigExt)
    (hρ : ∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) →
      (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (t, w) = G.rigMk (z, u))
    (hρ' : ∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) →
      (∀ n, u.1 n = ∑ i, w i • dUnit k' (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u))
    (r : Mod p hμ →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt)
    (r' : Mod p hν →ₛₗ[(WittVector.constantCoeff : WittVector p k' →+* k')] G'.RigExt)
    (hr : ∀ (f : quasiLog p hμ) t w, Red p (cob1 (fun i => Katz.lift p (μ i)) f.1) t → RedV p (lin f.1) w →
      r (Submodule.Quotient.mk f) = ρ (t, w))
    (hr' : ∀ (f : quasiLog p hν) t w, Red p (cob1 (fun i => Katz.lift p (ν i)) f.1) t → RedV p (lin f.1) w →
      r' (Submodule.Quotient.mk f) = ρ' (t, w)) (x : Mod p hμ) :
    r' (m x) = s.rig (r x) := by
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k k' σ d e G G' c c' s
  have hhom := GlobalTheory.T.connectedPDivGroupChart_semilinearHom_isFormalGroupHom p k k' σ d e G G' c c' s μ ν φ hc hc' hφ
  obtain ⟨g, hg, hmg⟩ := hm φ hφ f
  have hD := GlobalTheory.T.quasiLog_reduces_to_cocycle p k d μ hμ
  obtain ⟨t, w, ht, hw⟩ := hD.1 f.1 f.2
  have hcoc := hD.2 f.1 f.2 t ht
  have hσμ := GlobalTheory.T.isCommFormalGroupLaw_map k k' σ d μ hμ
  have hB := GlobalTheory.T.map_formalGroupLawQuasiLogarithms p k k' σ d μ hμ hσμ f.1 f.2
  have hP := GlobalTheory.KatzPull.quasiLog_pull p k' e d ν _ hν hσμ φ hhom _ hB.1
  rw [hmg, hr f t w ht hw, hr' g (pull2 φ (MvPowerSeries.map σ t)) (pullLin φ (fun i => σ (w i)))
    (by rw [hg]; exact hP.2.1 _ (hB.2.2.1 t ht)) (by rw [hg]; exact hP.2.2 _ (hB.2.2.2 w hw))]
  exact GlobalTheory.T.rigidifiedExtension_presentation_natural_semilinear p k k' σ d e G G' c c' s μ φ ρ ρ' hc hφ hρ hρ' t w hcoc

theorem chartPull_frob {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G : PDivGroup p k} {d : ℕ}
    (c : Chart G d) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (hμ : IsLaw μ)
    (m : Mod p hμ → Mod p hμ) (hm : IsChartPull c c hμ hμ (absFrob (Dieu.p_eq_zero p k) G) m) :
    KatzF.IsF p hμ m := by
  intro f
  obtain ⟨g, hg, hmg⟩ := hm (fun j => X j ^ p) (fun n j => by
    rw [absFrob_app, map_pow]
    congr 1
    exact GlobalTheory.Katz.evA_X k (Fin d) (G.A n) (c.x n) (c.nil n) j) f
  exact ⟨g, hg.trans (subst_lift_X_pow_frob p _ f.1), hmg⟩

theorem chartPull_isPull {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H : PDivGroup p k} {d e : ℕ}
    (c : Chart G d) (c' : Chart H e) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k} (hμ : IsLaw μ) (hν : IsLaw ν) (f : G ⟶ H)
    (φ : Fin e → MvPowerSeries (Fin d) k) (hφ : c.IsMapOf c' f φ) (m : Mod p hν → Mod p hμ)
    (hm : IsChartPull c' c hν hμ (SemiHom.ofHom f) m) : KatzF.IsPull p hμ hν φ m := by
  intro x
  obtain ⟨g, hg, hmg⟩ := hm φ (fun n j => hφ n j) x
  refine ⟨g, ?_, hmg⟩
  rw [hg, frMap_id, MvPowerSeries.map_id, RingHom.id_apply]

end ChartRules

section Main

variable {p : ℕ} [Fact p.Prime]

theorem isChartPull_comp {k k' k'' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Field k''] [CharP k'' p] [PerfectRing k'' p] {σ : k →+* k'} {τ : k' →+* k''}
    {υ : k →+* k''} {G : PDivGroup p k} {G' : PDivGroup p k'} {G'' : PDivGroup p k''} {d e e' : ℕ}
    (c : Chart G d) (c' : Chart G' e) (c'' : Chart G'' e')
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'}
    {κ : Fin e' → MvPowerSeries (Fin e' ⊕ Fin e') k''} (hμ : IsLaw μ) (hν : IsLaw ν) (hκ : IsLaw κ)
    (hc : c.IsLawOf μ) (hc'' : c''.IsLawOf κ)
    (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G)
    (hu : ∀ n a, u.app n a = t.app n (s.app n a))
    (ms : Mod p hμ → Mod p hν) (mt : Mod p hν → Mod p hκ)
    (hs : IsChartPull c c' hμ hν s ms) (ht : IsChartPull c' c'' hν hκ t mt) :
    IsChartPull c c'' hμ hκ u (fun x => mt (ms x)) := by
  obtain ⟨mu, hmu⟩ := chartPull_exists c c'' hμ hκ hc hc'' u
  have e : (mu : Mod p hμ → Mod p hκ) = fun x => mt (ms x) :=
    funext (chartPull_comp c c' c'' hμ hν hκ s t u hu ms mt mu hs ht hmu)
  rw [← e]
  exact hmu

theorem exists_base_isConn_katz : ∀ (p : ℕ) [Fact p.Prime],
    ∃ B : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn), B.Katz := by
  intro p _
  have hch : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsConn →
      ∃ (d : ℕ) (c : Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ := by
    intro k _ _ _ G hG
    obtain ⟨d, ⟨c⟩⟩ := GlobalTheory.T.exists_connectedPDivGroupChart_of_isConn p k (CharP.cast_eq_zero k p) G hG
    obtain ⟨μ, hμ⟩ := (GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).1
    exact ⟨d, c, μ, hμ⟩
  choose d c μ hc using hch
  have hlaw : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (hG : G.IsConn),
      IsLaw (μ k G hG) := fun k _ _ _ G hG => GlobalTheory.T.isCommFormalGroupLaw_of_isLawOf p k _ G _ _ (hc k G hG)
  choose ρ hρ using fun (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k)
    (hG : G.IsConn) => GlobalTheory.T.exists_rigidifiedExtension_of_series_pair p k (d k G hG) G (c k G hG)
  choose r hr hsurj hker using fun (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k)
    (hG : G.IsConn) => GlobalTheory.Katz.reductionMap p k (d k G hG) (μ k G hG) (hlaw k G hG) G.RigExt (ρ k G hG)
      (GlobalTheory.T.rigidifiedExtension_presentation_of_series_pairs p k _ G _ _ _ (hc k G hG) (hρ k G hG))
  choose P hP using fun (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] (σ : k →+* k') (G : PDivGroup p k) (G' : PDivGroup p k') (d e : ℕ) (cc : Chart G d)
    (cc' : Chart G' e) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (ν' : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (hμ' : IsLaw μ') (hν' : IsLaw ν')
    (hc1 : cc.IsLawOf μ') (hc2 : cc'.IsLawOf ν') (s : SemiHom σ G' G) =>
    chartPull_exists cc cc' hμ' hν' hc1 hc2 s
  have hff : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (hG : G.IsConn),
      Module.Free (WittVector p k) (Mod p (hlaw k G hG)) ∧ Module.Finite (WittVector p k) (Mod p (hlaw k G hG)) := by
    intro k _ _ _ G hG
    haveI : Module.Finite k G.RigExt :=
      (GlobalTheory.PDivGroup.finrank_rigExt_omega p k (CharP.cast_eq_zero k p) G).2.1
    exact GlobalTheory.wittModule_free_finite_of_reduction p k _ G.RigExt (r k G hG)
      (GlobalTheory.Katz.WittHaus.haus p k _ _ (hlaw k G hG))
      (GlobalTheory.Katz.mod_noPTorsion p k _ _ (hlaw k G hG)
        (GlobalTheory.T.eq_zero_of_formalGroupLawCoboundaryOne_eq_zero p k (CharP.cast_eq_zero k p) _ G _ _ (hc k G hG)))
      (hsurj k G hG) (fun x => (hker k G hG x).1)
  let B : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn) :=
    { M := @fun k _ _ _ G hG => ModuleCat.of (WittVector p k) (Mod p (hlaw k G hG))
      smap := @fun k k' _ _ _ _ _ _ σ G' G h' h s =>
        (P k k' σ G G' _ _ (c k G h) (c k' G' h') _ _ (hlaw k G h) (hlaw k' G' h') (hc k G h) (hc k' G' h')
          s).toAddMonoidHom
      red := @fun k _ _ _ G hG => r k G hG
      free := @fun k _ _ _ G hG => (hff k G hG).1
      finite := @fun k _ _ _ G hG => (hff k G hG).2
      red_surjective := @fun k _ _ _ G hG => hsurj k G hG
      red_eq_zero := @fun k _ _ _ G hG => hker k G hG
      smap_smul := @fun k k' _ _ _ _ _ _ σ G' G h' h s a m =>
        (P k k' σ G G' _ _ (c k G h) (c k' G' h') _ _ (hlaw k G h) (hlaw k' G' h') (hc k G h) (hc k' G' h')
          s).map_smulₛₗ a m
      smap_id := @fun k _ _ _ G h m =>
        chartPull_id (c k G h) (hlaw k G h) _ (hP k k (RingHom.id k) G G _ _ (c k G h) (c k G h) _ _ (hlaw k G h)
          (hlaw k G h) (hc k G h) (hc k G h) (SemiHom.ofHom (𝟙 G))) m
      smap_add := @fun k _ _ _ G H hG hH f g m =>
        chartPull_add (c k G hG) (c k H hH) (hlaw k G hG) (hlaw k H hH) (hc k H hH) f g _ _ _
          (hP k k (RingHom.id k) H G _ _ (c k H hH) (c k G hG) _ _ (hlaw k H hH) (hlaw k G hG) (hc k H hH)
            (hc k G hG) (SemiHom.ofHom f))
          (hP k k (RingHom.id k) H G _ _ (c k H hH) (c k G hG) _ _ (hlaw k H hH) (hlaw k G hG) (hc k H hH)
            (hc k G hG) (SemiHom.ofHom g))
          (hP k k (RingHom.id k) H G _ _ (c k H hH) (c k G hG) _ _ (hlaw k H hH) (hlaw k G hG) (hc k H hH)
            (hc k G hG) (SemiHom.ofHom (f + g))) m
      smap_comp := @fun k k' k'' _ _ _ _ _ _ _ _ _ σ τ υ G'' G' G h'' h' h s t u hu m =>
        chartPull_comp (c k G h) (c k' G' h') (c k'' G'' h'') (hlaw k G h) (hlaw k' G' h') (hlaw k'' G'' h'')
          s t u hu _ _ _
          (hP k k' σ G G' _ _ (c k G h) (c k' G' h') _ _ (hlaw k G h) (hlaw k' G' h') (hc k G h) (hc k' G' h') s)
          (hP k' k'' τ G' G'' _ _ (c k' G' h') (c k'' G'' h'') _ _ (hlaw k' G' h') (hlaw k'' G'' h'')
            (hc k' G' h') (hc k'' G'' h'') t)
          (hP k k'' υ G G'' _ _ (c k G h) (c k'' G'' h'') _ _ (hlaw k G h) (hlaw k'' G'' h'') (hc k G h)
            (hc k'' G'' h'') u) m
      red_smap := @fun k k' _ _ _ _ _ _ σ G' G h' h s m =>
        chartPull_red (c k G h) (c k' G' h') (hlaw k G h) (hlaw k' G' h') (hc k G h) (hc k' G' h') s _
          (hP k k' σ G G' _ _ (c k G h) (c k' G' h') _ _ (hlaw k G h) (hlaw k' G' h') (hc k G h) (hc k' G' h') s)
          (ρ k G h) (ρ k' G' h') (hρ k G h) (hρ k' G' h') (r k G h) (r k' G' h') (hr k G h) (hr k' G' h') m }
  have hid : ∀ {k : Type} [Field k] (G : PDivGroup p k) (n : ℕ) (a : G.A n),
      (SemiHom.ofHom (𝟙 G)).app n a = a := fun G n a => rfl
  refine ⟨B, @fun k _ _ _ G h d' cc μ' hμ' hcc =>
    { toFun := P k k (RingHom.id k) G G _ _ (c k G h) cc _ _ (hlaw k G h) hμ' (hc k G h) hcc
        (SemiHom.ofHom (𝟙 G))
      invFun := P k k (RingHom.id k) G G _ _ cc (c k G h) _ _ hμ' (hlaw k G h) hcc (hc k G h)
        (SemiHom.ofHom (𝟙 G))
      map_add' := map_add _
      map_smul' := fun a x => by
        refine (LinearMap.map_smulₛₗ _ a x).trans ?_
        congr 1
      left_inv := fun x =>
        (chartPull_comp (c k G h) cc (c k G h) (hlaw k G h) hμ' (hlaw k G h) (SemiHom.ofHom (𝟙 G))
          (SemiHom.ofHom (𝟙 G)) (SemiHom.ofHom (𝟙 G)) (fun n a => rfl) _ _ _
          (hP k k (RingHom.id k) G G _ _ (c k G h) cc _ _ (hlaw k G h) hμ' (hc k G h) hcc _)
          (hP k k (RingHom.id k) G G _ _ cc (c k G h) _ _ hμ' (hlaw k G h) hcc (hc k G h) _)
          (hP k k (RingHom.id k) G G _ _ (c k G h) (c k G h) _ _ (hlaw k G h) (hlaw k G h) (hc k G h)
            (hc k G h) _) x).symm.trans
          (chartPull_id (c k G h) (hlaw k G h) _
            (hP k k (RingHom.id k) G G _ _ (c k G h) (c k G h) _ _ (hlaw k G h) (hlaw k G h) (hc k G h)
              (hc k G h) _) x)
      right_inv := fun x =>
        (chartPull_comp cc (c k G h) cc hμ' (hlaw k G h) hμ' (SemiHom.ofHom (𝟙 G))
          (SemiHom.ofHom (𝟙 G)) (SemiHom.ofHom (𝟙 G)) (fun n a => rfl) _ _ _
          (hP k k (RingHom.id k) G G _ _ cc (c k G h) _ _ hμ' (hlaw k G h) hcc (hc k G h) _)
          (hP k k (RingHom.id k) G G _ _ (c k G h) cc _ _ (hlaw k G h) hμ' (hc k G h) hcc _)
          (hP k k (RingHom.id k) G G _ _ cc cc _ _ hμ' hμ' hcc hcc _) x).symm.trans
          (chartPull_id cc hμ' _ (hP k k (RingHom.id k) G G _ _ cc cc _ _ hμ' hμ' hcc hcc _) x) }, ?_⟩
  intro k _ _ _ G h d' cc μ' hμ' hcc
  refine ⟨chartPull_frob cc hμ' _ ?_, ?_⟩
  · have hin := isChartPull_comp cc (c k G h) (c k G h) hμ' (hlaw k G h) (hlaw k G h) hcc (hc k G h)
      (SemiHom.ofHom (𝟙 G)) (absFrob (Dieu.p_eq_zero p k) G) (absFrob (Dieu.p_eq_zero p k) G)
      (fun n a => rfl) _ _
      (hP k k (RingHom.id k) G G _ _ cc (c k G h) _ _ hμ' (hlaw k G h) hcc (hc k G h) _)
      (hP k k _ G G _ _ (c k G h) (c k G h) _ _ (hlaw k G h) (hlaw k G h) (hc k G h) (hc k G h) _)
    exact isChartPull_comp cc (c k G h) cc hμ' (hlaw k G h) hμ' hcc hcc
      (absFrob (Dieu.p_eq_zero p k) G) (SemiHom.ofHom (𝟙 G)) (absFrob (Dieu.p_eq_zero p k) G)
      (fun n a => rfl) _ _ hin
      (hP k k (RingHom.id k) G G _ _ (c k G h) cc _ _ (hlaw k G h) hμ' (hc k G h) hcc _)
  · intro H h' d'' c' ν hν hc' f φ _ hφ
    refine chartPull_isPull cc c' hμ' hν f φ hφ _ ?_
    have hin := isChartPull_comp c' (c k H h') (c k G h) hν (hlaw k H h') (hlaw k G h) hc' (hc k G h)
      (SemiHom.ofHom (𝟙 H)) (SemiHom.ofHom f) (SemiHom.ofHom f)
      (fun n a => rfl) _ _
      (hP k k (RingHom.id k) H H _ _ c' (c k H h') _ _ hν (hlaw k H h') hc' (hc k H h') _)
      (hP k k _ H G _ _ (c k H h') (c k G h) _ _ (hlaw k H h') (hlaw k G h) (hc k H h') (hc k G h) _)
    exact isChartPull_comp c' (c k G h) cc hν (hlaw k G h) hμ' hc' hcc
      (SemiHom.ofHom f) (SemiHom.ofHom (𝟙 G)) (SemiHom.ofHom f)
      (fun n a => rfl) _ _ hin
      (hP k k (RingHom.id k) G G _ _ (c k G h) cc _ _ (hlaw k G h) hμ' (hc k G h) hcc _)

end Main

end GlobalTheory
