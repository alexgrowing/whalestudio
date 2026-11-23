import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov.Transp

private theorem measurePreserving_curry_symm_pi (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A]
    (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A).symm (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ)
      (Measure.pi fun _ : ι × κ => μ) := by
  refine ⟨(MeasurableEquiv.curry ι κ A).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ => ?_).symm
  have hpre : (MeasurableEquiv.curry ι κ A).symm ⁻¹' Set.univ.pi s
      = Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext f
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem curry_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A) (Measure.pi fun _ => μ)
      (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h := MeasurePreserving.symm _ (measurePreserving_curry_symm_pi ι κ A μ)
  rwa [MeasurableEquiv.symm_symm] at h

theorem swap_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v)
      (Measure.pi fun _ => Measure.pi fun _ => μ) (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h1 := measurePreserving_curry_symm_pi ι κ A μ
  have h2 := measurePreserving_piCongrLeft (fun _ : κ × ι => μ) (Equiv.prodComm ι κ)
  have h3 := curry_mp κ ι A μ
  have key : (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v) =
      (MeasurableEquiv.curry κ ι A) ∘ (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => A) (Equiv.prodComm ι κ)) ∘
        (MeasurableEquiv.curry ι κ A).symm := by
    funext f v i
    simp [MeasurableEquiv.coe_curry, MeasurableEquiv.coe_curry_symm, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_eq_cast]
  rw [key]
  exact h3.comp (h2.comp h1)

theorem glue_mp {ι A B A' B' : Type} [Fintype ι] [MeasureSpace A] [MeasureSpace B] [MeasureSpace A'] [MeasureSpace B']
    [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)]
    [SigmaFinite (volume : Measure A')] [SigmaFinite (volume : Measure B')]
    {f : A' → ι → A} {g : B' → ι → B}
    (hf : MeasurePreserving f volume (Measure.pi fun _ : ι => (volume : Measure A)))
    (hg : MeasurePreserving g volume (Measure.pi fun _ : ι => (volume : Measure B))) :
    MeasurePreserving (fun (p : A' × B') (v : ι) => (f p.1 v, g p.2 v)) volume
      (Measure.pi fun _ : ι => (volume : Measure (A × B))) := by
  have h1 := hf.prod hg
  have h2 := MeasurePreserving.symm _
    (measurePreserving_arrowProdEquivProdArrow A B ι (fun _ => (volume : Measure A)) (fun _ => (volume : Measure B)))
  exact h2.comp h1

theorem sigmaFinite_volume_pi_family (I A : Type) [Fintype I] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → A)) := by
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure A))
  infer_instance

theorem sigmaFinite_volume_pi_double_family (I J A : Type) [Fintype I] [Fintype J] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → J → A)) := by
  have := sigmaFinite_volume_pi_family J A
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure (J → A)))
  infer_instance

theorem swap_vol (I ι A : Type) [Fintype I] [Fintype ι] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    MeasurePreserving (fun (f : I → ι → A) (v : ι) (i : I) => f i v) volume
      (Measure.pi fun _ : ι => (volume : Measure (I → A))) := by
  have := sigmaFinite_volume_pi_family I A
  exact swap_mp I ι A volume

end GlobalTheory.DegVol.RefCov.Transp

namespace GlobalTheory.DegVol.RefCov

theorem atP_measurePreserving : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ),
    MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume
      (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) := by
  intro ι _ k r j β
  have s0 := Transp.sigmaFinite_volume_pi_family (Fin (k + 1)) ℂ
  have s1 := Transp.sigmaFinite_volume_pi_family (UTin β) ℂ
  have s2 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} (Fin (k + 1) → ℂ)
  have s3 := Transp.sigmaFinite_volume_pi_family {p : UT r // j ≤ p.1.1.val} ℂ
  have s4 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} ℝ
  have t1 := Transp.sigmaFinite_volume_pi_double_family (UTin β) ι ℂ
  have t2 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have t3 := Transp.sigmaFinite_volume_pi_double_family {p : UT r // j ≤ p.1.1.val} ι ℂ
  have t4 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι ℝ
  have p1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ)))
    infer_instance
  have p2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))))
    infer_instance
  have q1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ι → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ι → ℝ)))
    infer_instance
  have q2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))))
    infer_instance
  have e1 := Transp.swap_vol (UTin β) ι ℂ
  have e2 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have e3 := Transp.swap_vol {p : UT r // j ≤ p.1.1.val} ι ℂ
  have e4 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι ℝ
  have g := Transp.glue_mp e1 (Transp.glue_mp e2 (Transp.glue_mp e3 e4))
  exact g

end GlobalTheory.DegVol.RefCov
