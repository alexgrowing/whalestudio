import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.IsUnitDetOfCartan

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexOrder

namespace Formalism.IndefR.Tow.SobPf.Avg

section Pds

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pds_eq_iteratedFDeriv (L : List (Fin N)) {f : (Fin N → ℝ) → E} (hf : ContDiff ℝ ∞ f) (r : Fin N → ℝ) :
    OrbStPf.pds L f r = iteratedFDeriv ℝ L.length f r (fun i => Pi.single (L.get i) 1) := by
  induction L generalizing r with
  | nil => simp [OrbStPf.pds]
  | cons i L ih =>
    have h2 : OrbStPf.pds L f = fun r => iteratedFDeriv ℝ L.length f r (fun j => Pi.single (L.get j) 1) :=
      funext ih
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ L.length f) r :=
      (hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) r
    show fderiv ℝ (OrbStPf.pds L f) r (Pi.single i 1) =
      iteratedFDeriv ℝ (L.length + 1) f r (fun k => Pi.single ((i :: L).get k) 1)
    rw [iteratedFDeriv_succ_apply_left, h2, fderiv_continuousMultilinear_apply_const_apply hd]
    rfl

end Pds

section Avg

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def Kset (G s : Matrix (Fin n) (Fin n) ℂ) : Set (Fin n → Fin n → ℂ) := {k | Matrix.of k ∈ KAt G s}

theorem isCompact_Kset {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCompact (Kset G s) := isCompact_KAt hs

theorem isClosed_Kset (G s : Matrix (Fin n) (Fin n) ℂ) : IsClosed (Kset G s) := isClosed_KAt G s

def avgTerm (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : (Fin n → Fin n → ℂ) → ℂ) (w : H) {d : ℕ}
    (Xs : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ) (k : Fin n → Fin n → ℂ) : H :=
  p k • π (oneProd Xs t * Matrix.of k) w

theorem append_mem_lieG {G : Matrix (Fin n) (Fin n) ℂ} {d d' : ℕ} {X : Fin d → Matrix (Fin n) (Fin n) ℂ}
    {Y : Fin d' → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, X i ∈ lieG G) (hY : ∀ i, Y i ∈ lieG G) :
    ∀ i, Fin.append X Y i ∈ lieG G := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa using hX i
  · simpa using hY i

variable {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {w : H}
  (p : (Fin n → Fin n → ℂ) → ℂ)

theorem avgTerm_eq (hG : IsUnit G.det) (hπ : IsGRep G π) (hw : SmoothVec (lieG G) π w) {d d' : ℕ}
    {Xs : Fin d → Matrix (Fin n) (Fin n) ℂ} (hXs : ∀ i, Xs i ∈ lieG G) {Yc : Fin d' → Matrix (Fin n) (Fin n) ℂ}
    (hYc : ∀ i, Yc i ∈ lieG G) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.UH G) (s' : Fin d' → ℝ)
    {k : Fin n → Fin n → ℂ} (hk : Matrix.of k = u * oneProd Yc s') (t : Fin d → ℝ) :
    avgTerm π p w Xs t k = (p k • (π u).restrictScalars ℝ)
      (π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (appL d d' t + Fin.append 0 s')) w) := by
  have hdu : IsUnit u.det := by
    have h : uᴴ * G * u = G := hu
    have h' := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul] at h'
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h'
    exact hG.ne_zero h'.symm
  have hT : appL d d' t + Fin.append 0 s' = Fin.append t s' := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [appL]
  have hA : ∀ i, u⁻¹ * Xs i * u ∈ lieG G := fun i => conj_mem_lieG hG hu (hXs i)
  have hX : oneProd (fun i => u⁻¹ * Xs i * u) t * oneProd Yc s' ∈ Formalism.QuantumDeterminants.UH G := by
    rw [← oneProd_append]
    exact (smooth_oneProd hπ hw _ (append_mem_lieG hA hYc) _).2
  simp only [avgTerm]
  rw [hk, hT, oneProd_append, ← mul_assoc, oneProd_mul hdu, mul_assoc, hπ.2.1 u hu _ hX]
  rfl

variable {p}

theorem contDiff_orbit (hw : SmoothVec (lieG G) π w) {N : ℕ} {Z : Fin N → Matrix (Fin n) (Fin n) ℂ}
    (hZ : ∀ i, Z i ∈ lieG G) : ContDiff ℝ ∞ fun r => π (oneProd Z r) w :=
  Formalism.IndefR.Tow.OrbStPf.contDiff_orb (ρ := π) (Lie := lieG G) Z hZ hw 0

theorem pIter_avgTerm (hG : IsUnit G.det) (hπ : IsGRep G π) (hw : SmoothVec (lieG G) π w) {d d' : ℕ}
    {Xs : Fin d → Matrix (Fin n) (Fin n) ℂ} (hXs : ∀ i, Xs i ∈ lieG G) {Yc : Fin d' → Matrix (Fin n) (Fin n) ℂ}
    (hYc : ∀ i, Yc i ∈ lieG G) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.UH G) (s' : Fin d' → ℝ)
    {k : Fin n → Fin n → ℂ} (hk : Matrix.of k = u * oneProd Yc s') (j : ℕ) (t : Fin d → ℝ) :
    pIter (avgTerm π p w Xs) j t k = (p k • (π u).restrictScalars ℝ).compContinuousMultilinearMap
      ((iteratedFDeriv ℝ j (fun r => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) r) w)
        (Fin.append t s')).compContinuousLinearMap (fun _ => appL d d')) := by
  have hA : ∀ i, u⁻¹ * Xs i * u ∈ lieG G := fun i => conj_mem_lieG hG hu (hXs i)
  have hF := contDiff_orbit hw (append_mem_lieG hA hYc)
  have hT : appL d d' t + Fin.append 0 s' = Fin.append t s' := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [appL]
  have hfun : (fun t => avgTerm π p w Xs t k) = (p k • (π u).restrictScalars ℝ) ∘
      ((fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) ∘ appL d d') := by
    funext t
    exact avgTerm_eq p hG hπ hw hXs hYc hu s' hk t
  have hG1 : ContDiff ℝ ∞
      (fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) :=
    hF.comp (contDiff_id.add contDiff_const)
  have e1 : iteratedFDeriv ℝ j ((p k • (π u).restrictScalars ℝ) ∘
      ((fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) ∘ appL d d')) t =
      (p k • (π u).restrictScalars ℝ).compContinuousMultilinearMap (iteratedFDeriv ℝ j
        ((fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) ∘ appL d d') t) :=
    (p k • (π u).restrictScalars ℝ).iteratedFDeriv_comp_left (hG1.comp (appL d d').contDiff).contDiffAt
      (by exact_mod_cast le_top)
  have e2 : iteratedFDeriv ℝ j
      ((fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) ∘ appL d d') t =
      (iteratedFDeriv ℝ j
        (fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) (appL d d' t)).compContinuousLinearMap
        (fun _ => appL d d') :=
    (appL d d').iteratedFDeriv_comp_right hG1 t (by exact_mod_cast le_top)
  have e3 : iteratedFDeriv ℝ j
      (fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) (appL d d' t) =
      iteratedFDeriv ℝ j (fun r => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) r) w)
        (appL d d' t + Fin.append 0 s') :=
    iteratedFDeriv_comp_add_right (f := fun r => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) r) w)
      j (Fin.append 0 s') (appL d d' t)
  unfold pIter
  rw [hfun, e1, e2, e3, hT]

theorem contDiff_avgTerm (hG : IsUnit G.det) (hπ : IsGRep G π) (hw : SmoothVec (lieG G) π w) {d : ℕ}
    {Xs : Fin d → Matrix (Fin n) (Fin n) ℂ} (hXs : ∀ i, Xs i ∈ lieG G) {k : Fin n → Fin n → ℂ}
    (hk : Matrix.of k ∈ Formalism.QuantumDeterminants.UH G) : ContDiff ℝ ∞ fun t => avgTerm π p w Xs t k := by
  have hk' : Matrix.of k = Matrix.of k * oneProd (fun i : Fin 0 => (i.elim0 : Matrix (Fin n) (Fin n) ℂ)) 0 := by
    rw [oneProd_zero, mul_one]
  have hY0 : ∀ i : Fin 0, (fun i : Fin 0 => (i.elim0 : Matrix (Fin n) (Fin n) ℂ)) i ∈ lieG G :=
    fun i => i.elim0
  have hF := contDiff_orbit hw (append_mem_lieG (fun i => conj_mem_lieG hG hk (hXs i)) hY0)
  have hfun : (fun t => avgTerm π p w Xs t k) = fun t =>
      (p k • (π (Matrix.of k)).restrictScalars ℝ)
        (π (oneProd (Fin.append (fun i => (Matrix.of k)⁻¹ * Xs i * Matrix.of k)
          (fun i : Fin 0 => (i.elim0 : Matrix (Fin n) (Fin n) ℂ))) (appL d 0 t + Fin.append 0 0)) w) := by
    funext t
    exact avgTerm_eq p hG hπ hw hXs hY0 hk 0 hk' t
  rw [hfun]
  exact (ContinuousLinearMap.contDiff _).comp (hF.comp ((appL d 0).contDiff.add contDiff_const))

end Avg

end Formalism.IndefR.Tow.SobPf.Avg

end
