import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W)) (𝓕W : Set (Formalism.L2.Theta.GA D W))
variable (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) {G : Type} [Monoid G] (ω : G →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W))
  (𝓕W : Set (Formalism.L2.Theta.GA D W)) (c : ℂ)
variable (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) {G : Type} [Monoid G]
  (ω : G →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc
open scoped TensorProduct
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
def eWloc_alt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) : (X.R.cV j).W ≃ₗ[ℂ] (P.M.loc i).wt.W := by
  have key : ∀ (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m),
      (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W := by
    rintro k rfl p1 p2
    exact A.eW _ hμ j
  exact key _ hj _ _
def formToVectorMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →ₗ[ℂ] (Formalism.L2.Theta.GA D (Vc D j) → (X.R.cV j).W) :=
  (X.R.cV j).ext ∘ₗ
    { toFun := fun F k => (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm
        ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))
      map_add' := fun F F' => by funext k; simp
      map_smul' := fun c F => by funext k; simp }
def canonicalEmbedding' {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) :
    Y.A →ₗ[ℂ] Formalism.IndefR.Mult.MMap (X.R.MW j (sg0 D X.A)) :=
  Classical.choose hc
def canonicalConstant {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) : ℝ :=
  Classical.choose (Classical.choose_spec hc)
def thetaEvaluationMap {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) :
    ↥Y.C →ₗ[ℂ] (Formalism.L2.Theta.GA D (Wc D j) → ℂ) :=
  LinearMap.applyₗ (PiTensorProduct.map (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype)
      (kUnit (X.R.MW j (sg0 D X.A)))) ∘ₗ
    (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (X.R.MW j (sg0 D X.A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc ∘ₗ Y.C.subtype
def standardWeilRepresentation (A : GlobalTheory.NJoin.Agree X P.M P.rep) (j : Fin D.R.m) (t : X.T) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ (WO (Vc D j) (Wc D j) → ℂ) :=
  (X.R.ωP j t).comp ((A.PV j).ψ.prodMap (X.PW j).ψ)
def OmegaSubmoduleAtLocal (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    Submodule ℂ ((X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ)) :=
  OmSub (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) X.R.ψ
    (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
def canonicalPairingValue (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i))
    (φ : (X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ))
    (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y : ↥Y.C) : ℂ :=
  lamV (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) φ F y
def standardSchwartzFunctionMap (j : Fin D.R.m) (t : X.T) : (X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ) :=
  pureTensorO X.R.ψ X.R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (X.R.MW j (sg0 D X.A))) (X.R.BV j)
    (onb (X.R.MW j (sg0 D X.A))) (X.R.vP j t) ∘ₗ X.R.ioP j (kUnit (X.R.MW j (sg0 D X.A)))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ}
theorem map_mem_iSup_range_isLinAt {Θ Ω : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup Ω] [Module ℂ Ω]
    (ω₁ : GAf E n × GAf E r →* Module.End ℂ Θ) (ω₂ : GAf E n × GAf E r →* Module.End ℂ Ω)
    (P : Θ → Prop) (Q : Ω → Prop) (T : Θ →ₗ[ℂ] Ω) (hT : ∀ p f, P f → T (ω₁ p f) = ω₂ p (T f))
    (hTQ : ∀ f, P f → Q (T f)) (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ) {f : Θ}
    (hf : f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω₁ s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι) :
    T f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω₂ s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
  have hle : (⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω₁ s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι).map T ≤
      ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω₂ s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
    rw [Submodule.map_iSup]
    refine iSup_le fun ι => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hι => ?_
    rw [← LinearMap.range_comp]
    exact le_iSup₂_of_le (T ∘ₗ ι) ⟨isLinAt_comp ω₁ ω₂ P T hT s μ η ι hι.2 hι.1, fun Φ => hTQ _ (hι.2 Φ)⟩ le_rfl
  exact hle (Submodule.mem_map_of_mem hf)
theorem mem_iSup_range_isLinAt_valAct1 {Θ B : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup B] [Module ℂ B]
    [FiniteDimensional ℂ B] (ω : GAf E n × GAf E r →* Module.End ℂ Θ) (P : Θ → Prop) (Q : (B →ₗ[ℂ] Θ) → Prop)
    (hQ : ∀ β f, P f → Q (single1 β f))
    (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ) (φ : B →ₗ[ℂ] Θ)
    (hφ : ∀ b, φ b ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι) :
    φ ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] (B →ₗ[ℂ] Θ))
      (_ : IsLinAt (valAct1 ω) s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
  let bB := Module.finBasis ℂ B
  rw [eq_sum_single1 bB φ]
  refine Submodule.sum_mem _ fun l _ => ?_
  exact _root_.GlobalTheory.ThetaTri.map_mem_iSup_range_isLinAt ω (valAct1 ω) P Q (single1 (bB.coord l))
    (fun p f _ => single1_valAct1 ω _ p f) (fun f hf => hQ _ f hf) s μ η (hφ _)
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W))
  (𝓕W : Set (Formalism.L2.Theta.GA D W)) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ)
  (ω : GAf E n × GAf E r →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
def omegaMapAtLocal (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ ↥(_root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ) :=
  omSub (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) X.R.ψ (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
def canonicalPairingMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    ↥(_root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ) →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →ₗ[ℂ] ↥Y.C →ₗ⋆[ℂ] ℂ :=
  lam (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) X.R.ψ (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
end GlobalTheory.ThetaTri
end
end
