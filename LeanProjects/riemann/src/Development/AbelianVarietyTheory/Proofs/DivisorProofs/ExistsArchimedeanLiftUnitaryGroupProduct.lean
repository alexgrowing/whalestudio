import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLift

open GlobalTheory.PointAtPlaceHom

variable {D : D7}

def prodAt (θ : InfFam D) (V : HSp D) (l : List D.what₂.Tau) (u : D.what₂.Tau → Mt V.rank) : GA D V :=
  (l.map fun τ => atTau θ V τ (u τ)).prod

theorem prodAt_mem (θ : InfFam D) (V : HSp D) (l : List D.what₂.Tau) (u : D.what₂.Tau → Mt V.rank) :
    prodAt θ V l u ∈ GinfC V := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
  exact atTau_mem V τ _

theorem infMat_prodAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {u : D.what₂.Tau → Mt V.rank}
    (hu : u ∈ UG (gramAt D V)) (ρ : D.what₂.Tau) (l : List D.what₂.Tau) (hl : l.Nodup) :
    infMat D.sp.cm.sig V.gram (θ ρ) (prodAt θ V l u) = if ρ ∈ l then u ρ else 1 := by
  induction l with
  | nil => rw [if_neg List.not_mem_nil]; exact infMat_one V _
  | cons τ l ih =>
    have e : prodAt θ V (τ :: l) u = atTau θ V τ (u τ) * prodAt θ V l u := List.prod_cons
    have hs := atTau_spec hθ V τ (hu τ)
    rw [List.nodup_cons] at hl
    rw [e, infMat_mul, ih hl.2]
    by_cases c : ρ = τ
    · subst c
      rw [hs.2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [hs.2.2 ρ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

theorem continuousOn_prodAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (l : List D.what₂.Tau) :
    ContinuousOn (prodAt θ V l) (UG (gramAt D V)) := by
  induction l with
  | nil => exact continuousOn_const
  | cons τ l ih =>
    have e : prodAt θ V (τ :: l) = fun u => atTau θ V τ (u τ) * prodAt θ V l u := funext fun _ => List.prod_cons
    have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
    have c : ContinuousOn (fun u : D.what₂.Tau → Mt V.rank => atTau θ V τ (u τ)) (UG (gramAt D V)) :=
      (continuousOn_atTau hθ V τ).comp (continuous_apply τ).continuousOn fun u hu => hu τ
    rw [e]
    exact c.mul ih

theorem archM_mem {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    archM V (θ τ) g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  obtain ⟨θ₀, h₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ = fun ρ => θ₀ (tauE D ρ) := (GlobalTheory.SmoothForms.RealPts.realPoints D).1 _ _ hθ fun ρ => h₀ _
  subst e
  exact (GlobalTheory.Member.Arch.unit_iff _ _ _).1 (((GlobalTheory.Member.Arch.archM_spec D V θ₀ h₀).1 _).2.2.2.2 g)

theorem exists_real_lift : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∃ L : (D.what₂.Tau → Mt V.rank) → GA D V, (∀ u ∈ UG (gramAt D V), L u ∈ GinfC V ∧ ∀ τ, archM V (θ τ) (L u) = u τ) ∧ (∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), L (u * u') = L u * L u') ∧ ContinuousOn L (UG (gramAt D V)) ∧ (∀ g, (fun τ => archM V (θ τ) g) ∈ UG (gramAt D V)) ∧ (∀ u ∈ GinfC V, L (fun τ => archM V (θ τ) u) = u) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ g = L (Pi.mulSingle τ g)) ∧ (∀ g, ∃ a ∈ GfC V, ∃ u ∈ GinfC V, g = a * u) ∧ (∀ a ∈ GfC V, ∀ u ∈ GinfC V, a * u = u * a) ∧ ∀ τ, (gramAt D V τ).IsHermitian ∧ (gramAt D V τ).det ≠ 0 := by
  intro D θ V hθ
  obtain ⟨r1, -, r3, r4, -, r6, r7, -⟩ := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  let L : (D.what₂.Tau → Mt V.rank) → GA D V := prodAt θ V Finset.univ.toList
  have hm : ∀ u, L u ∈ GinfC V := prodAt_mem θ V _
  have hL : ∀ u ∈ UG (gramAt D V), ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (L u) = u τ := fun u hu τ => by
    rw [infMat_prodAt hθ V hu τ _ (Finset.nodup_toList _), if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  refine ⟨L, fun u hu => ⟨hm u, hL u hu⟩, fun u hu u' hu' => ?_, continuousOn_prodAt hθ V _,
    fun g τ => archM_mem hθ V g τ, fun u hu => ?_, fun τ g hg => ?_, r7, fun a ha u hu => (r6 u hu a ha).symm,
    fun τ => ⟨(r1 τ).1, (r1 τ).2.ne_zero⟩⟩
  · refine r3 _ (hm _) _ (mul_mem (hm _) (hm _)) fun τ => ?_
    rw [r4, hL u hu, hL u' hu', hL (u * u') fun ρ => mul_mem_UH (hu ρ) (hu' ρ)]
    rfl
  · exact r3 _ (hm _) _ hu fun τ => hL _ (fun ρ => archM_mem hθ V u ρ) τ
  · have hs := atTau_spec hθ V τ hg
    have hu : (Pi.mulSingle τ g : D.what₂.Tau → Mt V.rank) ∈ UG (gramAt D V) := fun ρ => by
      by_cases c : ρ = τ
      · subst c
        rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne c]
        exact one_mem_UH _
    refine r3 _ hs.1 _ (hm _) fun ρ => ?_
    rw [hL _ hu]
    by_cases c : ρ = τ
    · subst c
      rw [Pi.mulSingle_eq_same, hs.2.1]
    · rw [Pi.mulSingle_eq_of_ne c, hs.2.2 ρ c]

end GlobalTheory.RealLift

end
