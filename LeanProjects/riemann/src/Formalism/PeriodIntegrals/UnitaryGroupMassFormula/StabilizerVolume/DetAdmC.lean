import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DetAdmB

noncomputable section

namespace PI.VolStabS.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabS.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabS
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported

section Crd

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) {a M : ℕ}

def crdH (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    (Fin a → Fin M → R ⊗[F] E) ≃ₜ (Fin a × Fin M × Fin d → R) where
  toFun X c := crd b R (X c.1 c.2.1) c.2.2
  invFun Y x i := (Algebra.TensorProduct.basis R b).equivFun.symm (fun k => Y (x, i, k))
  left_inv X := by
    funext x i
    show (Algebra.TensorProduct.basis R b).equivFun.symm (fun k => crd b R (X x i) k) = X x i
    have e : (fun k => crd b R (X x i) k) = (Algebra.TensorProduct.basis R b).equivFun (X x i) := by
      funext k
      simp [crd, Module.Basis.equivFun_apply]
    rw [e, LinearEquiv.symm_apply_apply]
  right_inv Y := by
    funext c
    show crd b R ((Algebra.TensorProduct.basis R b).equivFun.symm (fun k => Y (c.1, c.2.1, k))) c.2.2
      = Y c
    have e : ∀ y, crd b R y c.2.2 = (Algebra.TensorProduct.basis R b).equivFun y c.2.2 := fun y => by
      simp [crd, Module.Basis.equivFun_apply]
    rw [e, LinearEquiv.apply_symm_apply]
  continuous_toFun := continuous_pi fun c =>
    (continuous_crd b R c.2.2).comp ((continuous_apply c.2.1).comp (continuous_apply c.1))
  continuous_invFun := continuous_pi fun x => continuous_pi fun i =>
    (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap).comp
      (continuous_pi fun k => continuous_apply _)

end Crd

section Split

variable (F : Type) [Field F] [NumberField F]

def splitH (ι : Type) : (ι → AF F) ≃ₜ (ι → Ainf F) × (ι → Af F) where
  toFun Y := (fun c => fstA F (Y c), fun c => sndA F (Y c))
  invFun p c := pairA F (p.1 c) (p.2 c)
  left_inv Y := rfl
  right_inv p := rfl
  continuous_toFun := by
    refine (continuous_pi fun c => ?_).prodMk (continuous_pi fun c => ?_)
    · exact continuous_fst.comp (continuous_apply c)
    · exact continuous_snd.comp (continuous_apply c)
  continuous_invFun := continuous_pi fun c =>
    ((continuous_apply c).comp continuous_fst).prodMk ((continuous_apply c).comp continuous_snd)

end Split

section admitted

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {a M : ℕ}

def locBox (D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
  (crdH b (Fv F v)) ⁻¹' (Set.pi univ fun c => D c v)

variable {b}

theorem isClopen_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) : IsClopen (locBox b D v) :=
  (show IsClopen (Set.pi univ fun c => D c v) from ⟨isClosed_set_pi (fun c _ => (hD.1 c v).1.isClosed),
    isOpen_set_pi finite_univ (fun c _ => (hD.1 c v).1.isOpen)⟩).preimage (crdH b (Fv F v)).continuous

theorem isCompact_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) : IsCompact (locBox b D v) :=
  (crdH b (Fv F v)).isCompact_preimage.2 (isCompact_univ_pi fun c => (hD.1 c v).2)

theorem isSB_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) :
    IsSB ((locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)) :=
  ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (isClopen_locBox hD v)).isLocallyConstant,
    HasCompactSupport.intro' (isCompact_locBox hD v) (isClopen_locBox hD v).isClosed
      fun Y hY => Set.indicator_of_notMem hY _⟩

theorem locBox_eq_latV {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (v : HeightOneSpectrum (𝓞 F)) (hv : ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    locBox b D v = latV b v := by
  ext Y
  simp only [locBox, latV, mem_preimage, Set.mem_univ_pi, Set.mem_ofPred_eq]
  constructor
  · intro h x i k
    have h1 := h (x, i, k)
    rw [hv] at h1
    exact h1
  · intro h c
    rw [hv]
    exact h c.1 c.2.1 c.2.2

theorem finprod_ite {α : Type} (P : α → Prop) [DecidablePred P] [Decidable (∀ v, P v)] (h : ∀ᶠ v in cofinite, P v) :
    ∏ᶠ v, (if P v then (1 : ℂ) else 0) = if ∀ v, P v then 1 else 0 := by
  by_cases hall : ∀ v, P v
  · rw [if_pos hall]
    exact finprod_eq_one_of_forall_eq_one fun v => if_pos (hall v)
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨v0, hv0⟩ := hall
    refine finprod_eq_zero _ v0 (if_neg hv0) ?_
    refine (eventually_cofinite.1 h).subset fun v hv => ?_
    intro hP
    exact hv (if_pos hP)

theorem finprod_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (W : Fin a → Fin M → Af F ⊗[F] E) :
    ∏ᶠ v, (locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v W) =
      (boxS D).indicator 1 (crdH b (Af F) W) := by
  classical
  set q := crdH b (Af F) W
  have hv : ∀ v, (locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v W) =
      if (∀ c, q c v ∈ D c v) then 1 else 0 := by
    intro v
    have e : ∀ c, crdH b (Fv F v) (projV v W) c = q c v := fun c =>
      crd_map b (evalV F v) (W c.1 c.2.1) c.2.2
    rw [Set.indicator_apply]
    simp only [locBox, mem_preimage, Set.mem_univ_pi, e, Pi.one_apply]
  rw [finprod_congr hv, finprod_ite _ ?_]
  · rw [Set.indicator_apply]
    by_cases hq : q ∈ boxS D
    · rw [if_pos hq, if_pos (fun v c => hq c v)]
      rfl
    · rw [if_neg hq, if_neg (fun h' => hq (fun c v => h' v c))]
  · filter_upwards [hD.2, eventually_all.2 fun c => (q c).eventually] with v h1 h2 c
    rw [h1 c]
    exact h2 c

end admitted

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {a M : ℕ}

variable (F E a M) in

def psiH : (Fin a → Fin M → AF F ⊗[F] E) ≃ₜ
    (Fin a × Fin M × Fin (Module.finrank F E) → Ainf F) ×
      (Fin a × Fin M × Fin (Module.finrank F E) → Af F) :=
  (crdH (Module.finBasis F E) (AF F)).trans (splitH F _)

theorem psiH_fst (X : Fin a → Fin M → AF F ⊗[F] E) :
    (psiH F E a M X).1 = crdH (Module.finBasis F E) (Ainf F) (projInf X) := by
  funext c
  exact (crd_map (Module.finBasis F E) (fstA F) (X c.1 c.2.1) c.2.2).symm

theorem psiH_snd (X : Fin a → Fin M → AF F ⊗[F] E) :
    (psiH F E a M X).2 = crdH (Module.finBasis F E) (Af F) (projFin X) := by
  funext c
  exact (crd_map (Module.finBasis F E) (sndA F) (X c.1 c.2.1) c.2.2).symm

theorem key_int (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2)
    {D : Fin a × Fin M × Fin (Module.finrank F E) → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (f : C_c(Fin a × Fin M × Fin (Module.finrank F E) → Ainf F, ℝ)) :
    ∫ X, f (psiH F E a M X).1 * (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 ∂ν1 =
      ∫ X, f (psiH F E a M X).1 * (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 ∂ν2 := by
  classical
  let b := Module.finBasis F E
  let Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ := fun Y => ((f (crdH b (Ainf F) Y) : ℝ) : ℂ)
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (locBox b D v).indicator 1
  let Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ := fun W => ∏ᶠ v, Φv v (projV v W)
  let Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φinf (projInf X) * Φf (projFin X)
  have hadm : IsAdm F E Φ := by
    refine ⟨_, b, Φinf, Φf, Φv, ?_, ?_, ⟨fun v => isSB_locBox hD v, ?_, fun _ => rfl⟩, fun _ => rfl⟩
    · exact Complex.continuous_ofReal.comp (f.continuous.comp (crdH b (Ainf F)).continuous)
    · exact (f.hasCompactSupport.comp_homeomorph (crdH b (Ainf F))).comp_left Complex.ofReal_zero
    · filter_upwards [hD.2] with v hv
      exact congrArg (fun s => s.indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)) (locBox_eq_latV v hv)
  have hΦ : ∀ X, Φ X = ((f (psiH F E a M X).1 *
      (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 : ℝ) : ℂ) := by
    intro X
    have e2 : Φf (projFin X) = (boxS D).indicator 1 ((psiH F E a M X).2) := by
      rw [psiH_snd]
      exact finprod_locBox hD (projFin X)
    simp only [Φ, e2, psiH_fst, Φinf, b]
    rw [Complex.ofReal_mul]
    congr 1
    by_cases hq : (psiH F E a M X).2 ∈ boxS D
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      simp
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
      simp
  have := h Φ hadm
  simp only [hΦ] at this
  rw [integral_complex_ofReal, integral_complex_ofReal] at this
  exact_mod_cast this

end Main

end PI.VolStabS.DeterminantAdmissible
