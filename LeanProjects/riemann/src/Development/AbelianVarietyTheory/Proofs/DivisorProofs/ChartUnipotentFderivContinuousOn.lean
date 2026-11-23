import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

open NumberField GlobalTheory.CuspRep Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CuspRep.JointCont

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

theorem map_unip {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : BlockIx a r → R) :
    Matrix.GeneralLinearGroup.map f (unip x) = unip (fun p => f (x p)) := by
  apply Units.ext
  ext i j
  change f ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) = (1 + nilM fun p => f (x p) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp

theorem continuous_nilM {R : Type} [CommRing R] [TopologicalSpace R] :
    Continuous (fun x : BlockIx a r → R => (nilM x : Matrix (Fin a) (Fin a) R)) := by
  refine continuous_matrix fun i j => ?_
  simp only [nilM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_unip {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (fun x : BlockIx a r → R => unip x) :=
  Units.continuous_iff.2 ⟨continuous_const.add continuous_nilM, continuous_const.sub continuous_nilM⟩

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem chart_mul_finGL_of_fix (φ : Sm E a) (h : GA E a) (k : GL (Fin a) (Af E)) (hk : finRep E a k φ = φ) :
    chart φ.1 (h * finGL E a k) = chart φ.1 h := by
  rw [← chart_rt_fin]
  congr 1
  funext z
  exact congrArg (fun ψ : Sm E a => ψ.1 z) hk

def infPart (g : GA E a) (x : BlockIx a r → Ad E) : GL (Fin a) (Cinf E) :=
  unip (fun p => pInf E (x p)) * Matrix.GeneralLinearGroup.map (pInf E) g

def finPart (g : GA E a) (x : BlockIx a r → Ad E) : GL (Fin a) (Af E) :=
  unip (fun p => pFin E (x p)) * Matrix.GeneralLinearGroup.map (pFin E) g

theorem unip_mul_eq (g : GA E a) (x : BlockIx a r → Ad E) :
    unip x * g = finGL E a (finPart g x) * infGL E a (infPart g x) := by
  refine ga_ext ?_ ?_ <;>
    simp only [finPart, infPart, map_mul, map_unip, pInf_finGL, pInf_infGL, pFin_finGL, pFin_infGL, one_mul, mul_one]

theorem continuous_infPart (g : GA E a) : Continuous (fun x : BlockIx a r → Ad E => toL (infPart g x).val) := by
  have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pInf E (x p)) :=
    continuous_pi fun p => continuous_pInf.comp (continuous_apply p)
  have h2 : Continuous (fun x : BlockIx a r → Ad E =>
      ((infPart g x : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) :=
    Units.continuous_val.comp ((continuous_unip.comp h1).mul continuous_const)
  exact h2

theorem continuous_finPart (g : GA E a) : Continuous (fun x : BlockIx a r → Ad E => finPart g x) := by
  have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pFin E (x p)) :=
    continuous_pi fun p => continuous_pFin.comp (continuous_apply p)
  exact (continuous_unip.comp h1).mul continuous_const

theorem eventually_chart_eq (φ : Sm E a) (hφ : IsAutForm φ) (g : GA E a) (x₀ : BlockIx a r → Ad E) :
    ∀ᶠ x in 𝓝 x₀, chart φ.1 (unip x * g) =
      chart φ.1 (finGL E a (finPart g x₀)) ∘ lmul (toL (infPart g x).val) := by
  have hc : Continuous (fun x : BlockIx a r → Ad E => (finPart g x₀)⁻¹ * finPart g x) := continuous_const.mul (continuous_finPart g)
  have h1 : finRep E a ((finPart g x₀)⁻¹ * finPart g x₀) φ = φ := by rw [inv_mul_cancel]; simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hφ.level.mem_nhds h1)] with x hx
  have hx' : finRep E a ((finPart g x₀)⁻¹ * finPart g x) φ = φ := hx
  rw [unip_mul_eq, ← mul_inv_cancel_left (finPart g x₀) (finPart g x), map_mul, mul_assoc, ← infGL_comm,
    ← mul_assoc, chart_mul_finGL_of_fix φ _ _ hx', chart_mul]

theorem chart_unipotent_translate_continuousOn (φ : Sm E a) (hφ : IsAutForm φ) (g : GA E a) (X : Lie E a) :
    ContinuousOn (fun p : (BlockIx a r → Ad E) × Lie E a => chart φ.1 (unip p.1 * g) p.2)
        (Set.univ ×ˢ invSet E a) ∧
      ContinuousOn (fun p : (BlockIx a r → Ad E) × Lie E a => fderiv ℝ (chart φ.1 (unip p.1 * g)) p.2 X)
        (Set.univ ×ˢ invSet E a) := by
  have hP : Continuous (fun p : (BlockIx a r → Ad E) × Lie E a => lmul (toL (infPart g p.1).val) p.2) := by
    have := ((continuous_infPart g).comp continuous_fst).matrix_mul
      (continuous_snd : Continuous fun p : (BlockIx a r → Ad E) × Matrix (Fin a) (Fin a) (Cinf E) => p.2)
    exact this
  have hQ : Continuous (fun p : (BlockIx a r → Ad E) × Lie E a => lmul (toL (infPart g p.1).val) X) := by
    have := ((continuous_infPart g).comp continuous_fst).matrix_mul
      (continuous_const : Continuous fun _ : (BlockIx a r → Ad E) × Lie E a => (Matrix.of X))
    exact this
  have hinv : ∀ p : (BlockIx a r → Ad E) × Lie E a, p.2 ∈ invSet E a →
      lmul (toL (infPart g p.1).val) p.2 ∈ invSet E a := fun p hp => (infPart g p.1).isUnit.mul hp
  constructor
  · rintro ⟨x₀, y₀⟩ ⟨-, hy₀⟩
    set f₀ := chart φ.1 (finGL E a (finPart g x₀))
    have hf₀ : ContDiffOn ℝ ∞ f₀ (invSet E a) := φ.2 _
    have hA : ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E a => f₀ (lmul (toL (infPart g p.1).val) p.2))
        (x₀, y₀) :=
      ContinuousAt.comp (g := f₀) (hf₀.continuousOn.continuousAt (isOpen_invSet.mem_nhds (hinv (x₀, y₀) hy₀)))
        hP.continuousAt
    refine (hA.congr ?_).continuousWithinAt
    filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually (eventually_chart_eq φ hφ g x₀)] with p hp
    rw [hp]; rfl
  · rintro ⟨x₀, y₀⟩ ⟨-, hy₀⟩
    set f₀ := chart φ.1 (finGL E a (finPart g x₀))
    have hf₀ : ContDiffOn ℝ ∞ f₀ (invSet E a) := φ.2 _
    have hD : ContinuousOn (fun z => fderiv ℝ f₀ z) (invSet E a) :=
      hf₀.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)
    have hA : ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E a =>
        fderiv ℝ f₀ (lmul (toL (infPart g p.1).val) p.2) (lmul (toL (infPart g p.1).val) X)) (x₀, y₀) :=
      ContinuousAt.clm_apply
        (ContinuousAt.comp (g := fun z => fderiv ℝ f₀ z)
          (hD.continuousAt (isOpen_invSet.mem_nhds (hinv (x₀, y₀) hy₀))) hP.continuousAt)
        hQ.continuousAt
    refine (hA.congr ?_).continuousWithinAt
    have hy : ∀ᶠ p : (BlockIx a r → Ad E) × Lie E a in 𝓝 (x₀, y₀), p.2 ∈ invSet E a :=
      (continuous_snd.tendsto (x₀, y₀)).eventually (isOpen_invSet.mem_nhds hy₀)
    filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually (eventually_chart_eq φ hφ g x₀), hy]
      with p hp hp2
    have hd : DifferentiableAt ℝ f₀ (lmul (toL (infPart g p.1).val) p.2) :=
      (hf₀.contDiffAt (isOpen_invSet.mem_nhds (hinv p hp2))).differentiableAt (by simp)
    change _ = fderiv ℝ (chart φ.1 (unip p.1 * g)) p.2 X
    rw [hp, fderiv_comp _ hd (lmul _).differentiableAt, ContinuousLinearMap.fderiv]
    rfl

theorem chart_jointCont : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ → ∀ (g : GlobalTheory.CuspRep.GA E a) (X : GlobalTheory.CuspRep.Lie E a), ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g) p.2) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) ∧ ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => fderiv ℝ (GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g)) p.2 X) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) :=
  fun _ _ _ _ _ _ φ hφ g X => chart_unipotent_translate_continuousOn φ hφ g X

end GlobalTheory.CuspRep.JointCont
