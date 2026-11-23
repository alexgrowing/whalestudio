import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniqueIntertwiner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAllMaps
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AutMult.MultAssembly

open GlobalTheory.CuspMult

variable {D : D7} {θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem continuous_of_mem_allMaps {T : MMap M} (hT : T ∈ allMaps θ M) (v : M.Vec) : Continuous (T v) := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact (hT.aut v).cont
  | zero => exact continuous_const
  | add T T' _ _ ih ih' => exact ih.add ih'
  | smul a T _ ih => exact ih.const_smul a

variable (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

def Represents (Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)) (T : MMap M) : Prop :=
  ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v

variable {μ}

theorem eq_of_represents_cont {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T T' : MMap M}
    (hT : ∀ v, Continuous (T v)) (hT' : ∀ v, Continuous (T' v)) (h : Represents μ Φ T) (h' : Represents μ Φ T') :
    T = T' :=
  MultilinearMap.ext fun v => (hT v).ae_eq_iff_eq μ (hT' v) |>.1 ((h v).symm.trans (h' v))

theorem represents_zero : Represents μ (0 : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)) 0 := fun _ => by
  simp only [ContinuousMultilinearMap.zero_apply, MultilinearMap.zero_apply]
  exact ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)

theorem Represents.add {Φ Φ' : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T T' : MMap M} (h : Represents μ Φ T)
    (h' : Represents μ Φ' T') : Represents μ (Φ + Φ') (T + T') := fun v => by
  simp only [ContinuousMultilinearMap.add_apply, MultilinearMap.add_apply]
  exact lift_add_ae (h v) (h' v)

theorem Represents.smul (c : ℂ) {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T : MMap M} (h : Represents μ Φ T) :
    Represents μ (c • Φ) (c • T) := fun v => by
  simp only [ContinuousMultilinearMap.smul_apply, MultilinearMap.smul_apply]
  exact lift_smul_ae c (h v)

theorem Represents.translate (g : GfC V) {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T : MMap M}
    (h : Represents μ Φ T) :
    Represents μ (postRepPi M.H ((RG V μ).comp (GfC V).subtype) g Φ) (finRep M g T) := fun v =>
  (lift_R (g : GA D V) _).trans ((measurePreserving_mul_right μ (g : GA D V)).quasiMeasurePreserving.ae (h v))

theorem Represents.translate' (g : GfC V) {Φ Φ' : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T : MMap M}
    (h : Represents μ Φ T) (h' : ∀ y, Φ' y = RG V μ (g : GA D V) (Φ y)) : Represents μ Φ' (finRep M g T) := fun v => by
  rw [h']
  exact (lift_R (g : GA D V) _).trans ((measurePreserving_mul_right μ (g : GA D V)).quasiMeasurePreserving.ae (h v))

variable (μ) in

def phiOf (T : MMap M) : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ) :=
  open Classical in
  if h : ∃ Φ, Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ Represents μ Φ T then h.choose else 0

theorem phiOf_spec (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {T : MMap M} (hT : T ∈ allMaps θ M) :
    phiOf μ T ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ Represents μ (phiOf μ T) T := by
  have h : ∃ Φ, Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ Represents μ Φ T :=
    (GlobalTheory.CuspIntertwiner.existsUnique_intertwiner hP D θ hθ V S M μ T hT).exists
  rw [phiOf, dif_pos h]
  exact h.choose_spec

theorem phiOf_eq (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {T : MMap M} (hT : T ∈ allMaps θ M)
    {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} (h : Represents μ Φ T) : phiOf μ T = Φ :=
  GlobalTheory.CuspIntertwiner.eq_of_represents (phiOf_spec hP hθ hT).2 h

variable {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W}

variable (μ) in

def homOf (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (f : W →ₗ[ℂ] MMap M) (hf : ∀ w, f w ∈ allMaps θ M) :
    W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ) where
  toFun w := phiOf μ (f w)
  map_add' w w' := by
    rw [map_add]
    exact phiOf_eq hP hθ (add_mem (hf w) (hf w')) ((phiOf_spec hP hθ (hf w)).2.add (phiOf_spec hP hθ (hf w')).2)
  map_smul' c w := by
    rw [map_smul]
    exact phiOf_eq hP hθ (Submodule.smul_mem _ c (hf w)) ((phiOf_spec hP hθ (hf w)).2.smul c)

theorem homOf_apply (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (f : W →ₗ[ℂ] MMap M)
    (hf : ∀ w, f w ∈ allMaps θ M) (w : W) : homOf μ hP hθ f hf w = phiOf μ (f w) := rfl

open Classical in
theorem homOf_mem (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {f : W →ₗ[ℂ] MMap M}
    (hf : f ∈ homInto σ (finRep M) (allMaps θ M)) :
    homOf μ hP hθ f hf.1 ∈ homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) := by
  unfold homFinDS
  rw [mem_homTensorPi]
  have hs := fun w => mem_homPi.1 (phiOf_spec (μ := μ) hP hθ (hf.1 w)).1
  refine ⟨fun w y => (hs w).1 y, fun g w y => ?_, fun i g w y => (hs w).2 i g y⟩
  rw [homOf_apply, homOf_apply, hf.2 g w]
  have hm : finRep M g (f w) ∈ allMaps θ M := by
    rw [← hf.2 g w]
    exact hf.1 _
  rw [phiOf_eq hP hθ hm ((phiOf_spec hP hθ (hf.1 w)).2.translate g)]
  rfl

variable (μ) in

def toHom (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) :
    homInto σ (finRep M) (allMaps θ M) →ₗ[ℂ] homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) where
  toFun f := ⟨homOf μ hP hθ f.1 f.2.1, homOf_mem hP hθ f.2⟩
  map_add' f f' := by
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    exact phiOf_eq hP hθ (add_mem (f.2.1 w) (f'.2.1 w))
      ((phiOf_spec hP hθ (f.2.1 w)).2.add (phiOf_spec hP hθ (f'.2.1 w)).2)
  map_smul' c f := by
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    exact phiOf_eq hP hθ (Submodule.smul_mem _ c (f.2.1 w)) ((phiOf_spec hP hθ (f.2.1 w)).2.smul c)

theorem toHom_injective (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) :
    Function.Injective (toHom (σ := σ) (M := M) μ hP hθ) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => Subtype.ext (LinearMap.ext fun w => ?_)
  have h0 : phiOf μ (f.1 w) = 0 := congrArg (fun Ψ : homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) => Ψ.1 w) hf
  have hr := (phiOf_spec (μ := μ) hP hθ (f.2.1 w)).2
  rw [h0] at hr
  exact eq_of_represents_cont (continuous_of_mem_allMaps (f.2.1 w)) (fun _ => continuous_const) hr represents_zero

variable (σ) in

def stab (w : W) : Subgroup (GfC V) where
  carrier := {g | σ g w = w}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
    rw [hb, ha]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

open Classical in
theorem toHom_surjective (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (hσ : GlobalTheory.PRep.IsSmooth σ) :
    Function.Surjective (toHom (σ := σ) (M := M) μ hP hθ) := by
  intro Ψ
  have hΨ := Ψ.2
  unfold homFinDS at hΨ
  rw [mem_homTensorPi] at hΨ
  obtain ⟨h1, h2, h3⟩ := hΨ
  have hΨ : ∀ w, Ψ.1 w ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) := fun w => mem_homPi.2 ⟨h1 w, fun i g => h3 i g w⟩
  have hex : ∀ w, ∃ T ∈ allMaps θ M, Represents μ (Ψ.1 w) T := fun w =>
    GlobalTheory.CuspRepr.exists_allMaps D θ hθ V S M μ (Ψ.1 w) (hΨ w) (stab σ w) (hσ w) fun k hk y => by
      have hk' : σ k w = w := hk
      exact (h2 k w y).symm.trans (congrArg (fun u => Ψ.1 u y) hk')
  choose T hT hr using hex
  have hc : ∀ w v, Continuous (T w v) := fun w => continuous_of_mem_allMaps (hT w)
  let f : W →ₗ[ℂ] MMap M :=
    { toFun := T
      map_add' := fun w w' => eq_of_represents_cont (hc _) (fun v => (hc w v).add (hc w' v)) (hr (w + w'))
        (by rw [map_add]; exact (hr w).add (hr w'))
      map_smul' := fun c w => eq_of_represents_cont (hc _) (fun v => (hc w v).const_smul c) (hr (c • w))
        (by rw [map_smul]; exact (hr w).smul c) }
  have hf : f ∈ homInto σ (finRep M) (allMaps θ M) :=
    ⟨hT, fun g w => eq_of_represents_cont (hc _) (fun v => (hc w v).comp (continuous_mul_right _)) (hr (σ g w))
      ((hr w).translate' g (h2 g w))⟩
  exact ⟨⟨f, hf⟩, Subtype.ext (LinearMap.ext fun w => phiOf_eq hP hθ (hT w) (hr w))⟩

end GlobalTheory.AutMult.MultAssembly

namespace GlobalTheory.AutMult

open GlobalTheory.AutMult.MultAssembly in

theorem cuspMult_eq_mCuspDS : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → ∀ (D : D7) (θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → GlobalTheory.CuspMult.cuspMult θ M σ = mCuspDS μ σ M := by
  intro hP _ _ D θ hθ V S M μ _ _ W _ _ σ hσ
  exact (LinearEquiv.ofBijective (toHom μ hP hθ) ⟨toHom_injective hP hθ, toHom_surjective hP hθ hσ⟩).rank_eq

end GlobalTheory.AutMult
