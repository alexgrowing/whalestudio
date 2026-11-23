import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DiscreteSeriesHolds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
import Formalism.LocalToGlobal.IndefiniteReal.LowestKType
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.WeylBridge

noncomputable section

open Matrix
open scoped InnerProductSpace ComplexConjugate

namespace Formalism.IndefR.ModelConjugation

open PI.ZuckTensorWork

variable {n : ℕ}

def toCj (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : H ≃ₗᵢ⋆[ℂ] Cj H where
  toFun := Cj.mk
  invFun := Cj.un
  map_add' _ _ := rfl
  map_smul' c x := Cj.mk_smul c x
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' _ := rfl

theorem conjDS_unique (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lam) (h : ℝ)
    (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hbig : 2 * (n : ℝ) < h)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsDS ε lam σ)
    (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (hσ' : Formalism.MainNotions.S.IsDS (revE ε) (revP lam) σ') :
    ∃ U : H ≃ₗᵢ⋆[ℂ] H', ∀ m ∈ Formalism.MainNotions.S.UJset ε, ∀ x, U (σ m x) = σ' (revM m) (U x) := by
  have hC : Formalism.MainNotions.S.IsDS (revE ε) (revP lam) (sigC σ) := discrete_series_holds n ε H σ lam hσ
  have hlam' : Formalism.QuantumDeterminants.IsHCParam (revP lam) := harish_chandra_holds n lam hlam
  have hgap' : Formalism.QuantumDeterminants.GapAtLeast (revE ε) (revP lam) h := spectral_gap_holds n ε lam h hgap
  obtain ⟨-, -, -, -, hU⟩ := ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap n (revE ε) (revP lam) hlam' h hgap' hbig
    (Cj H) (sigC σ) hC
  obtain ⟨U', hU'⟩ := hU H' σ' hσ'
  refine ⟨(toCj H).trans U', fun m hm x => ?_⟩
  have hm' : revM m ∈ Formalism.MainNotions.S.UJset (revE ε) := revM_mem_UJset' hm
  have e1 : Cj.mk (σ m x) = sigC σ (revM m) (Cj.mk x) := by
    show Cj.mk (σ m x) = cjOp (σ (revM (revM m))) (Cj.mk x)
    rw [revM_revM]
    rfl
  show U' (Cj.mk (σ m x)) = σ' (revM m) (U' (Cj.mk x))
  rw [e1, hU' _ hm']

def Rm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if j = Fin.rev i then 1 else 0

theorem revM_eq_Rm (m : Matrix (Fin n) (Fin n) ℂ) : revM m = Rm n * m * Rm n := by
  ext i j
  simp only [revM, Rm, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (Fin.rev j)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (by rw [h, Fin.rev_rev])
  · simp

theorem Rm_mul_self : Rm n * Rm n = 1 := by
  have h := revM_eq_Rm (1 : Matrix (Fin n) (Fin n) ℂ)
  rw [revM_one, Matrix.mul_one] at h
  exact h.symm

theorem Rm_conjTranspose : (Rm n)ᴴ = Rm n := by
  ext i j
  simp only [Rm, conjTranspose_apply, Matrix.of_apply]
  by_cases h : i = Fin.rev j
  · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev]), star_one]
  · rw [if_neg h, if_neg (fun h' => h (by rw [h', Fin.rev_rev])), star_zero]

theorem lowKSub_kStable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsKStableOn ε σ (Formalism.MainNotions.S.lowKSub ε lam σ) := by
  intro g hg x hx
  have hle : Formalism.MainNotions.S.lowKSub ε lam σ ≤ (Formalism.MainNotions.S.lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) := by
    apply sSup_le
    intro S hS y hy
    exact le_sSup hS (hS.2.1 g hg y hy)
  exact hle hx

theorem conjDS_frame {N : ℕ} (hN : N = n) (εX : Fin n → Bool) (lamX : Fin n → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lamX)
    (h : ℝ) (hgap : Formalism.QuantumDeterminants.GapAtLeast εX lamX h) (hbig : 2 * (n : ℝ) < h)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsDS εX lamX σ)
    (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')) (εM : Fin N → Bool) (lamM : Fin N → ℝ)
    (hσ' : Formalism.MainNotions.S.IsDS εM lamM σ')
    (hε : ∀ a, εM a = εX (Fin.rev (finCongr hN a))) (hl : ∀ a, lamM a = -lamX (Fin.rev (finCongr hN a)))
    (A : Matrix (Fin N) (Fin n) ℂ) (A' : Matrix (Fin n) (Fin N) ℂ) (h1 : A * A' = 1) (h2 : A' * A = 1)
    (hJ : Aᴴ * PI.UpqRep.Jm εM * A = PI.UpqRep.Jm εX) :
    ∃ U : H ≃ₗᵢ⋆[ℂ] H', (∀ m ∈ Formalism.MainNotions.S.UJset εX, ∀ x, U (σ m x) = σ' (A * m * A') (U x)) ∧
      ∃ k ∈ Formalism.MainNotions.S.UJset εM, ∃ W : Submodule ℂ H', FiniteDimensional ℂ W ∧ Formalism.MainNotions.S.IsKStableOn εM σ' W ∧
        ∀ w ∈ Formalism.MainNotions.S.lowKSub εX lamX σ, ∃ w' ∈ W, U w = σ' k w' := by
  subst hN
  have eε : εM = revE εX := funext fun a => by rw [hε a]; rfl
  have el : lamM = revP lamX := funext fun a => by rw [hl a]; rfl
  subst eε el
  obtain ⟨U0, hU0⟩ := conjDS_unique εX lamX hlam h hgap hbig H σ hσ H' σ' hσ'

  set k : Matrix (Fin N) (Fin N) ℂ := A * Rm N with hk
  set k' : Matrix (Fin N) (Fin N) ℂ := Rm N * A' with hk'
  have hkk' : k * k' = 1 := by
    rw [hk, hk', Matrix.mul_assoc, ← Matrix.mul_assoc (Rm N), Rm_mul_self, Matrix.one_mul, h1]
  have hk'k : k' * k = 1 := by
    rw [hk, hk', Matrix.mul_assoc, ← Matrix.mul_assoc A', h2, Matrix.one_mul, Rm_mul_self]
  have hkU : k ∈ Formalism.MainNotions.S.UJset (revE εX) := by
    show kᴴ * PI.UpqRep.Jm (revE εX) * k = PI.UpqRep.Jm (revE εX)
    rw [hk, conjTranspose_mul, Rm_conjTranspose]
    calc Rm N * Aᴴ * PI.UpqRep.Jm (revE εX) * (A * Rm N) = Rm N * (Aᴴ * PI.UpqRep.Jm (revE εX) * A) * Rm N := by
          simp only [Matrix.mul_assoc]
      _ = PI.UpqRep.Jm (revE εX) := by rw [hJ, ← revM_eq_Rm, revM_Jm]
  have ujMul : ∀ a b : Matrix (Fin N) (Fin N) ℂ, a ∈ Formalism.MainNotions.S.UJset (revE εX) → b ∈ Formalism.MainNotions.S.UJset (revE εX) →
      a * b ∈ Formalism.MainNotions.S.UJset (revE εX) := by
    intro a b ha hb
    have ha' : aᴴ * PI.UpqRep.Jm (revE εX) * a = PI.UpqRep.Jm (revE εX) := ha
    have hb' : bᴴ * PI.UpqRep.Jm (revE εX) * b = PI.UpqRep.Jm (revE εX) := hb
    show (a * b)ᴴ * PI.UpqRep.Jm (revE εX) * (a * b) = PI.UpqRep.Jm (revE εX)
    calc (a * b)ᴴ * PI.UpqRep.Jm (revE εX) * (a * b) = bᴴ * (aᴴ * PI.UpqRep.Jm (revE εX) * a) * b := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = PI.UpqRep.Jm (revE εX) := by rw [ha', hb']
  have hk'U : k' ∈ Formalism.MainNotions.S.UJset (revE εX) := by
    have hk0 : kᴴ * PI.UpqRep.Jm (revE εX) * k = PI.UpqRep.Jm (revE εX) := hkU
    show k'ᴴ * PI.UpqRep.Jm (revE εX) * k' = PI.UpqRep.Jm (revE εX)
    calc k'ᴴ * PI.UpqRep.Jm (revE εX) * k' = k'ᴴ * (kᴴ * PI.UpqRep.Jm (revE εX) * k) * k' := by rw [hk0]
      _ = (k * k')ᴴ * PI.UpqRep.Jm (revE εX) * (k * k') := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = PI.UpqRep.Jm (revE εX) := by rw [hkk', conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hrep := hσ'.2.2.1
  have hmul : ∀ a b, a ∈ Formalism.MainNotions.S.UJset (revE εX) → b ∈ Formalism.MainNotions.S.UJset (revE εX) → ∀ y,
      σ' (a * b) y = σ' a (σ' b y) := by
    intro a b ha hb y
    rw [hrep.1.2 a ha b hb]
    rfl
  have hone : ∀ y, σ' 1 y = y := by intro y; rw [hrep.1.1]; rfl

  let Lk : H' →ₗᵢ[ℂ] H' := ⟨(σ' k : H' →ₗ[ℂ] H'), hrep.2.1 k hkU⟩
  have hLk : Function.Surjective Lk := fun y => ⟨σ' k' y, by
    show σ' k (σ' k' y) = y
    rw [← hmul k k' hkU hk'U, hkk', hone]⟩
  refine ⟨U0.trans (LinearIsometryEquiv.ofSurjective Lk hLk), ?_, ?_⟩
  · intro m hm x
    have hmr : revM m ∈ Formalism.MainNotions.S.UJset (revE εX) := revM_mem_UJset' hm
    have hAm : A * m * A' = k * revM m * k' := by
      rw [revM_eq_Rm, hk, hk']
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Rm N) (Rm N), Rm_mul_self, Matrix.one_mul, ← Matrix.mul_assoc (Rm N) (Rm N),
        Rm_mul_self, Matrix.one_mul]
    show σ' k (U0 (σ m x)) = σ' (A * m * A') (σ' k (U0 x))
    rw [hU0 m hm x, hAm, ← hmul _ _ (ujMul _ _ (ujMul _ _ hkU hmr) hk'U) hkU, Matrix.mul_assoc (k * revM m),
      hk'k, Matrix.mul_one, hmul _ _ hkU hmr]
  · refine ⟨k, hkU, (Formalism.MainNotions.S.lowKSub εX lamX σ).map (U0 : H →ₛₗ[starRingEnd ℂ] H'), ?_, ?_, ?_⟩
    · have hfin := (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap _ εX lamX hlam h hgap hbig H σ hσ).2.2.1
        (Formalism.QuantumDeterminants.lowK εX lamX)
      have hfg : (Formalism.MainNotions.S.lowKSub εX lamX σ).FG := (Submodule.fg_iff_finiteDimensional _).2 hfin
      exact (Submodule.fg_iff_finiteDimensional _).1 (hfg.map _)
    · rintro g hg _ ⟨x, hx, rfl⟩
      have hm : revM g ∈ Formalism.REAL.Kset εX := revM_mem_Kset hg
      have hmU : revM g ∈ Formalism.MainNotions.S.UJset εX := ReciprocityTheory.ChartRestriction.DS.HW.hw_kset_subset εX hm
      refine ⟨σ (revM g) x, lowKSub_kStable εX lamX σ (revM g) hm x hx, ?_⟩
      show U0 (σ (revM g) x) = σ' g (U0 x)
      rw [hU0 _ hmU x, revM_revM]
    · intro w hw
      exact ⟨U0 w, Submodule.mem_map_of_mem hw, rfl⟩

section Rec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def ModelConjAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : Formalism.IndefR.Mult.DSModel V S) (v : NumberField.InfinitePlace X.B.I.F)
    (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin X.B.I.n) ℂ) (A' : Matrix (Fin X.B.I.n) (Fin V.rank) ℂ) : Prop :=
  ∃ U : X.B.H v ≃ₗᵢ⋆[ℂ] M.H τ,
    (∀ m ∈ Formalism.MainNotions.S.UJset (X.B.I.ε v), ∀ x, U (X.B.σ v m x) = M.σ τ (A * m * A') (U x)) ∧
    U (X.B.w v) ∈ M.sm τ ∧ ‖U (X.B.w v)‖ = 1

theorem modelConjAt_of (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : Formalism.IndefR.Mult.DSModel V S)
    (v : NumberField.InfinitePlace X.B.I.F) (τ : D.what₂.Tau) (hN : V.rank = X.B.I.n)
    (hlamX : Formalism.QuantumDeterminants.IsHCParam (X.B.lam v)) (hX : ℝ) (hgapX : Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε v) (X.B.lam v) hX)
    (hbigX : 2 * (X.B.I.n : ℝ) < hX)
    (hlamM : Formalism.QuantumDeterminants.IsHCParam (M.lam τ)) (hM : ℝ) (hgapM : Formalism.QuantumDeterminants.GapAtLeast (M.ε τ) (M.lam τ) hM)
    (hbigM : 2 * (V.rank : ℝ) < hM)
    (hε : ∀ a, M.ε τ a = X.B.I.ε v (Fin.rev (finCongr hN a)))
    (hl : ∀ a, M.lam τ a = -X.B.lam v (Fin.rev (finCongr hN a)))
    (A : Matrix (Fin V.rank) (Fin X.B.I.n) ℂ) (A' : Matrix (Fin X.B.I.n) (Fin V.rank) ℂ) (h1 : A * A' = 1)
    (h2 : A' * A = 1) (hJ : Aᴴ * PI.UpqRep.Jm (M.ε τ) * A = PI.UpqRep.Jm (X.B.I.ε v)) :
    ModelConjAt X M v τ A A' := by
  have hdsM := M.ds τ
  haveI : CompleteSpace (M.H τ) := hdsM.1
  obtain ⟨U, hU, k, hk, W, hWf, hWK, hlow⟩ := conjDS_frame hN (X.B.I.ε v) (X.B.lam v) hlamX hX hgapX hbigX
    (X.B.H v) (X.B.σ v) (X.ds v) (M.H τ) (M.σ τ) (M.ε τ) (M.lam τ) hdsM hε hl A A' h1 h2 hJ
  obtain ⟨w', hw', hUw⟩ := hlow (X.B.w v) (X.low v).2
  refine ⟨U, hU, ?_, by rw [LinearIsometryEquiv.norm_map]; exact (X.low v).1⟩

  have hsm := (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap V.rank (M.ε τ) (M.lam τ) hlamM hM hgapM hbigM (M.H τ) (M.σ τ)
    hdsM).2.2.2.1 W hWf hWK w' hw'
  have hw'sm : w' ∈ M.sm τ := Submodule.subset_span
    (Formalism.IndefR.PeterssonHilbertSpace.sm_transfer (M.ε τ) (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (lieAt V τ)
      (fun X hX => hX) w' (Formalism.IndefR.LowestKTypeSmoothness.smoothOnH_of_isSmoothVecU (M.ε τ) (M.σ τ) w' hsm))

  have hfr : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := hk
  have hkdet : IsUnit k.det := by
    have hJd : (Formalism.REAL.Jm (M.ε τ)).det ≠ 0 := by
      have := congrArg Matrix.det (Formalism.REAL.Jm_mul_self (M.ε τ))
      intro h0; rw [det_mul, h0, mul_zero, det_one] at this; exact zero_ne_one this
    have := congrArg Matrix.det hk'
    rw [det_mul, det_mul] at this
    refine isUnit_iff_ne_zero.2 fun h0 => hJd ?_
    rw [h0, mul_zero] at this
    exact this.symm
  set g0 : Matrix (Fin V.rank) (Fin V.rank) ℂ := (M.fr τ)⁻¹ * k * M.fr τ with hg0
  have hg0u : IsUnit g0 := by
    rw [Matrix.isUnit_iff_isUnit_det, hg0, det_mul, det_mul]
    exact ((isUnit_nonsing_inv_det _ hfr).mul hkdet).mul hfr
  have hg0mem : g0 ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    show g0ᴴ * gramAt D V τ * g0 = gramAt D V τ
    rw [← M.fr_gram τ, hg0]
    have hfrh : IsUnit (M.fr τ)ᴴ.det := by rw [det_conjTranspose]; exact hfr.star
    calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * k * M.fr τ)
        = (M.fr τ)ᴴ * kᴴ * (((M.fr τ)ᴴ)⁻¹ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k *
            M.fr τ := by
          rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv]; simp only [Matrix.mul_assoc]
      _ = (M.fr τ)ᴴ * (kᴴ * Formalism.REAL.Jm (M.ε τ) * k) * M.fr τ := by
          rw [Matrix.nonsing_inv_mul _ hfrh, Matrix.mul_nonsing_inv _ hfr]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hk']
  let g : Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ := ⟨hg0u.unit, hg0mem⟩
  have hrep : M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm g) = M.σ τ k := by
    show M.σ τ (M.fr τ * g0 * (M.fr τ)⁻¹) = M.σ τ k
    congr 1
    rw [hg0]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hfr, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hfr, Matrix.one_mul]
  rw [hUw, ← hrep]
  exact Formalism.IndefR.SchurOrthogonalityAlt.sm_stable M τ g hw'sm

end Rec

end Formalism.IndefR.ModelConjugation
