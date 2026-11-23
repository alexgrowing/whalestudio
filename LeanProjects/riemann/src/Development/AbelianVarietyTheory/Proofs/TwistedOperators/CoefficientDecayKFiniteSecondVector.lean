import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspace
import Formalism.RealPlaceAnalysis.SmoothOnGVIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory

namespace GlobalTheory.KFinDecay

section Core

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem avg_comm (π : K →* (H →L[ℂ] H)) (hiso : ∀ k x, ‖π k x‖ = ‖x‖)
    (hc : ∀ x, Continuous fun k => π k x) (u : H) (g : K) (x : H) :
    (∫ k, InnerProductSpace.rankOne ℂ (π k u) (π k u) ∂μ) (π g x) =
      π g ((∫ k, InnerProductSpace.rankOne ℂ (π k u) (π k u) ∂μ) x) := by
  have hin : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    LinearIsometry.inner_map_map (𝕜 := ℂ) ⟨(π g : H →ₗ[ℂ] H), hiso g⟩ x y
  have hF : Continuous fun k => InnerProductSpace.rankOne ℂ (π k u) (π k u) :=
    GlobalTheory.CompactRep.continuous_rankOne_self.comp (hc u)
  have hFi : Integrable (fun k => InnerProductSpace.rankOne ℂ (π k u) (π k u)) μ :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [ContinuousLinearMap.integral_apply hFi, ContinuousLinearMap.integral_apply hFi,
    ← (π g).integral_comp_comm (hFi.apply_continuousLinearMap x),
    ← integral_mul_left_eq_self (fun k => InnerProductSpace.rankOne ℂ (π k u) (π k u) (π g x)) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [InnerProductSpace.rankOne_apply, map_mul, ContinuousLinearMap.mul_apply, hin, map_smul]

theorem le_of_dense (π : K →* (H →L[ℂ] H)) (hiso : ∀ k x, ‖π k x‖ = ‖x‖)
    (hc : ∀ x, Continuous fun k => π k x) (Ds : Submodule ℂ H) (hD : Dense (Ds : Set H))
    (hT : ∀ u ∈ Ds, ∀ w, (∫ k, InnerProductSpace.rankOne ℂ (π k u) (π k u) ∂μ) w ∈ Ds)
    (Y : Submodule ℂ H) (hYf : FiniteDimensional ℂ Y)
    (hY : ∀ B : H →L[ℂ] H, (∀ k x, B (π k x) = π k (B x)) → ∀ y ∈ Y, B y ∈ Y) : Y ≤ Ds := by
  intro a ha
  let Z : Submodule ℂ H := Ds ⊓ Y
  haveI : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le (inf_le_right : Z ≤ Y)
  have hwZ : a - Z.starProjection a ∈ Zᗮ := Z.sub_starProjection_mem_orthogonal a
  have hwY : a - Z.starProjection a ∈ Y :=
    Y.sub_mem ha (inf_le_right (a := Ds) (Z.starProjection_apply_mem a))
  have hperp : Dsᗮ = ⊥ := Submodule.topologicalClosure_eq_top_iff.1
    (Submodule.dense_iff_topologicalClosure_eq_top.1 hD)
  have hw0 : a - Z.starProjection a = 0 := by
    set w := a - Z.starProjection a with hw
    have hmem : w ∈ Dsᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      have hF : Continuous fun k => InnerProductSpace.rankOne ℂ (π k u) (π k u) :=
        GlobalTheory.CompactRep.continuous_rankOne_self.comp (hc u)
      have hFi : Integrable (fun k => InnerProductSpace.rankOne ℂ (π k u) (π k u)) μ :=
        hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hTw : (∫ k, InnerProductSpace.rankOne ℂ (π k u) (π k u) ∂μ) w ∈ Z :=
        ⟨hT u hu w, hY _ (fun k x => avg_comm μ π hiso hc u k x) w hwY⟩
      have h0 := Submodule.inner_right_of_mem_orthogonal hTw hwZ
      have h1 := GlobalTheory.CompactRep.inner_integral_rankOne hFi w w
      have h2 : ⟪w, (∫ k, InnerProductSpace.rankOne ℂ (π k u) (π k u) ∂μ) w⟫_ℂ = 0 := by
        rw [← inner_conj_symm, h0, map_zero]
      have h3 : ∀ k, ⟪π k u, w⟫_ℂ * ⟪w, π k u⟫_ℂ = ((‖⟪w, π k u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
        intro k
        rw [← inner_conj_symm w (π k u), RCLike.norm_conj, Complex.mul_conj']
        norm_cast
      simp only [h3] at h1
      rw [integral_complex_ofReal, h2] at h1
      have hcont : Continuous fun k => ‖⟪w, π k u⟫_ℂ‖ ^ 2 :=
        ((continuous_const.inner (hc u)).norm).pow 2
      by_contra hne
      have hwu : ⟪w, u⟫_ℂ ≠ 0 := fun h => hne (by rw [← inner_conj_symm, h, map_zero])
      have hpos : 0 < ∫ k, ‖⟪w, π k u⟫_ℂ‖ ^ 2 ∂μ :=
        hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
          (HasCompactSupport.of_compactSpace _) (fun k => by positivity)
          (by rw [map_one, ContinuousLinearMap.one_apply]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 hwu))
      exact hpos.ne' (by exact_mod_cast h1.symm)
    rw [hperp] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  have hmem := Z.starProjection_apply_mem a
  rw [← sub_eq_zero.1 hw0] at hmem
  exact hmem.1

end Core

section Norms

variable {n : ℕ}

theorem hsn_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsn X := Real.sqrt_nonneg _

theorem hsn_mul_le (A B : Matrix (Fin n) (Fin n) ℂ) : hsn (A * B) ≤ hsn A * hsn B := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  have e : ∀ X : Matrix (Fin n) (Fin n) ℂ, hsn X = ‖X‖ := fun X => by
    rw [Matrix.frobenius_norm_def, hsn, Real.sqrt_eq_rpow]
    norm_cast
  rw [e, e, e]
  exact Matrix.frobenius_norm_mul A B

theorem decay_shift {N : ℕ} {C B : ℝ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {g h h' : Matrix (Fin n) (Fin n) ℂ}
    (hC : ‖f (g * h)‖ * (1 + hsn (g * h)) ^ N ≤ C) (hh : h * h' = 1) (hB : hsn h' ≤ B) :
    ‖f (g * h)‖ * (1 + hsn g) ^ N ≤ C * (1 + B) ^ N := by
  have e : g = g * h * h' := by rw [Matrix.mul_assoc, hh, Matrix.mul_one]
  have hB0 : 0 ≤ B := (hsn_nonneg _).trans hB
  have h1 : hsn g ≤ hsn (g * h) * B := by
    calc hsn g = hsn (g * h * h') := by rw [← e]
      _ ≤ hsn (g * h) * hsn h' := hsn_mul_le _ _
      _ ≤ hsn (g * h) * B := mul_le_mul_of_nonneg_left hB (hsn_nonneg _)
  have h2 : 1 + hsn g ≤ (1 + hsn (g * h)) * (1 + B) := by
    nlinarith [hsn_nonneg (g * h), hsn_nonneg g]
  calc ‖f (g * h)‖ * (1 + hsn g) ^ N ≤ ‖f (g * h)‖ * ((1 + hsn (g * h)) ^ N * (1 + B) ^ N) := by
        rw [← mul_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hsn_nonneg g]) h2 N) (norm_nonneg _)
    _ = (‖f (g * h)‖ * (1 + hsn (g * h)) ^ N) * (1 + B) ^ N := by ring
    _ ≤ C * (1 + B) ^ N := mul_le_mul_of_nonneg_right hC (pow_nonneg (by linarith) _)

theorem mul_mem_of_form {G g g' : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * G * g = G) (hg' : g'ᴴ * G * g' = G) :
    (g * g')ᴴ * G * (g * g') = G := by
  calc (g * g')ᴴ * G * (g * g') = g'ᴴ * (gᴴ * G * g) * g' := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [hg, hg']

end Norms

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)

theorem conj_mem_UH {y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hy : y ∈ Formalism.MainNotions.S.UJset (M.ε τ)) :
    (M.fr τ)⁻¹ * y * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hy' : yᴴ * Formalism.REAL.Jm (M.ε τ) * y = Formalism.REAL.Jm (M.ε τ) := hy
  have e1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  show ((M.fr τ)⁻¹ * y * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * y * M.fr τ) = gramAt D V τ
  rw [← M.fr_gram τ]
  calc ((M.fr τ)⁻¹ * y * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * y * M.fr τ)
      = (M.fr τ)ᴴ * (yᴴ * ((((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹)) * y) *
          M.fr τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [e1, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one, hy']

theorem rep_conj (y : Matrix (Fin V.rank) (Fin V.rank) ℂ) : M.rep τ ((M.fr τ)⁻¹ * y * M.fr τ) = M.σ τ y := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  simp only [DSModel.rep, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd,
    Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

theorem rep_mul' {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (x : M.H τ) :
    M.rep τ (g * g') x = M.rep τ g (M.rep τ g' x) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have := (M.ds τ).2.2.1.1.2 _ (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hg) _
    (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hg')
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd] at this
  simp only [DSModel.rep, Matrix.mul_assoc, this, ContinuousLinearMap.comp_apply]

def decSet (v : M.H τ) (N : ℕ) : Submodule ℂ (M.H τ) where
  carrier := {a | DecayAt M τ v a N}
  add_mem' := by
    rintro a b ⟨C, hC⟩ ⟨C', hC'⟩
    refine ⟨C + C', fun g hg => ?_⟩
    rw [map_add, inner_add_right]
    calc ‖⟪v, M.rep τ g a⟫_ℂ + ⟪v, M.rep τ g b⟫_ℂ‖ * (1 + hsn g) ^ N
        ≤ (‖⟪v, M.rep τ g a⟫_ℂ‖ + ‖⟪v, M.rep τ g b⟫_ℂ‖) * (1 + hsn g) ^ N :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg (by linarith [hsn_nonneg g]) _)
      _ ≤ C + C' := by rw [add_mul]; exact add_le_add (hC g hg) (hC' g hg)
  zero_mem' := ⟨0, fun g _ => by simp⟩
  smul_mem' := by
    rintro c a ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [map_smul, inner_smul_right, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg _)

theorem coef_sigma_le {v u : M.H τ} {N : ℕ} {C : ℝ}
    (hC : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ‖⟪v, M.rep τ g u⟫_ℂ‖ * (1 + hsn g) ^ N ≤ C)
    {y y' : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hy : y ∈ Formalism.MainNotions.S.UJset (M.ε τ)) (hyy : y * y' = 1) {B : ℝ}
    (hB : hsn ((M.fr τ)⁻¹ * y' * M.fr τ) ≤ B) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ‖⟪v, M.rep τ g (M.σ τ y u)⟫_ℂ‖ * (1 + hsn g) ^ N ≤ C * (1 + B) ^ N := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hh := conj_mem_UH M τ hy
  have e : M.rep τ g (M.σ τ y u) = M.rep τ (g * ((M.fr τ)⁻¹ * y * M.fr τ)) u := by
    rw [rep_mul' M τ hg hh, rep_conj]
  have hhh : ((M.fr τ)⁻¹ * y * M.fr τ) * ((M.fr τ)⁻¹ * y' * M.fr τ) = 1 := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
    rw [← Matrix.mul_assoc y y', hyy, Matrix.one_mul, Matrix.nonsing_inv_mul _ hd]
  rw [e]
  exact decay_shift (f := fun x => ⟪v, M.rep τ x u⟫_ℂ)
    (hC _ (GlobalTheory.KFinDecay.mul_mem_of_form hg hh)) hhh hB

end Model

end GlobalTheory.KFinDecay

namespace GlobalTheory.KFinDecay

theorem decayAt_of_kFin : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (v : M.H τ) (N : ℕ), v ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → DecayAt M τ v v N → ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, DecayAt M τ v a N := by
  intro _ D V S M τ v N _ hvv a ha
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨_, _, hU, hI, -⟩ := M.ds τ
  by_cases hv0 : v = 0
  · subst hv0
    exact ⟨0, fun g _ => by simp⟩
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hU
  have hJJ : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := Formalism.REAL.Jm_mul_self _
  have hinvUJ : ∀ y ∈ Formalism.MainNotions.S.UJset (M.ε τ),
      y * (Formalism.REAL.Jm (M.ε τ) * yᴴ * Formalism.REAL.Jm (M.ε τ)) = 1 := by
    intro y hy
    have hy' : yᴴ * Formalism.REAL.Jm (M.ε τ) * y = Formalism.REAL.Jm (M.ε τ) := hy
    rw [mul_eq_one_comm]
    calc Formalism.REAL.Jm (M.ε τ) * yᴴ * Formalism.REAL.Jm (M.ε τ) * y
        = Formalism.REAL.Jm (M.ε τ) * (yᴴ * Formalism.REAL.Jm (M.ε τ) * y) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy', hJJ]

  have hdense : Dense (decSet M τ v N : Set (M.H τ)) := by
    let S0 : Submodule ℂ (M.H τ) := Submodule.span ℂ {x | ∃ y ∈ Formalism.MainNotions.S.UJset (M.ε τ), x = M.σ τ y v}
    have hS0 : S0 ≤ decSet M τ v N := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨C, hC⟩ := hvv
      exact ⟨C * (1 + hsn ((M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * yᴴ * Formalism.REAL.Jm (M.ε τ)) * M.fr τ)) ^ N,
        fun g hg => coef_sigma_le M τ hC hy (hinvUJ y hy) le_rfl hg⟩
    have hst : ∀ y ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ x ∈ S0, M.σ τ y x ∈ S0 := by
      intro y hy x hx
      refine Submodule.span_induction (p := fun x _ => M.σ τ y x ∈ S0) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨y', hy', rfl⟩
        refine Submodule.subset_span ⟨y * y', mul_mem_of_form hy hy', ?_⟩
        rw [hmul y hy y' hy']
        rfl
      · simp
      · intro x x' _ _ h h'
        rw [map_add]
        exact S0.add_mem h h'
      · intro c x _ h
        rw [map_smul]
        exact S0.smul_mem c h
    have hcl : ∀ y ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ x ∈ S0.topologicalClosure,
        M.σ τ y x ∈ S0.topologicalClosure := by
      intro y hy
      have : S0.topologicalClosure ≤ S0.topologicalClosure.comap (M.σ τ y : M.H τ →ₗ[ℂ] M.H τ) :=
        Submodule.topologicalClosure_minimal S0 (fun x hx => S0.le_topologicalClosure (hst y hy x hx))
          (S0.isClosed_topologicalClosure.preimage (M.σ τ y).continuous)
      exact fun x hx => this hx
    have h1mem : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * Formalism.REAL.Jm (M.ε τ) * 1 = Formalism.REAL.Jm (M.ε τ)
      simp
    rcases hI S0.topologicalClosure S0.isClosed_topologicalClosure hcl with h | h
    · exfalso
      have hvS : v ∈ S0.topologicalClosure :=
        S0.le_topologicalClosure (Submodule.subset_span ⟨1, h1mem, by rw [h1]; rfl⟩)
      rw [h] at hvS
      exact hv0 ((Submodule.mem_bot ℂ).1 hvS)
    · exact Dense.mono (fun x hx => hS0 hx) (Submodule.dense_iff_topologicalClosure_eq_top.2 h)

  let π : Formalism.REAL.KG (M.ε τ) →* (M.H τ →L[ℂ] M.H τ) :=
    { toFun := fun k => M.σ τ (Formalism.REAL.toMK k)
      map_one' := h1
      map_mul' := fun k l => hmul _ k.1.2 _ l.1.2 }
  have hemb : Continuous fun k : Formalism.REAL.KG (M.ε τ) => Formalism.REAL.toMK k :=
    ((Formalism.REAL.isClosedEmbeddingMatrix _ (M.ε τ)).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).continuous
  have hUk : ∀ k : Formalism.REAL.KG (M.ε τ), Formalism.REAL.toMK k ∈ Formalism.MainNotions.S.UJset (M.ε τ) := fun k => k.1.2
  have hπc : ∀ x, Continuous fun k => π k x := fun x => (hcont x).comp_continuous hemb hUk
  have hπiso : ∀ k x, ‖π k x‖ = ‖x‖ := fun k x => hiso _ (hUk k) x
  have hBc : Continuous fun k : Formalism.REAL.KG (M.ε τ) => hsn ((M.fr τ)⁻¹ * (Formalism.REAL.toMK k)ᴴ * M.fr τ) := by
    have hm : Continuous fun k : Formalism.REAL.KG (M.ε τ) => (M.fr τ)⁻¹ * (Formalism.REAL.toMK k)ᴴ * M.fr τ :=
      (continuous_const.mul hemb.matrix_conjTranspose).mul continuous_const
    unfold hsn
    exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (hm.matrix_elem i j).norm.pow 2)
  obtain ⟨B, hB⟩ := (isCompact_range hBc).bddAbove

  have hT : ∀ u ∈ decSet M τ v N, ∀ w,
      (∫ k, InnerProductSpace.rankOne ℂ (π k u) (π k u) ∂(Formalism.REAL.muK (M.ε τ))) w ∈ decSet M τ v N := by
    intro u hu w
    obtain ⟨C, hC⟩ := hu
    have hF : Continuous fun k => InnerProductSpace.rankOne ℂ (π k u) (π k u) :=
      GlobalTheory.CompactRep.continuous_rankOne_self.comp (hπc u)
    have hFi : Integrable (fun k => InnerProductSpace.rankOne ℂ (π k u) (π k u)) (Formalism.REAL.muK (M.ε τ)) :=
      hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hGi := hFi.apply_continuousLinearMap w
    refine ⟨‖u‖ * ‖w‖ * (C * (1 + B) ^ N) * (Formalism.REAL.muK (M.ε τ)).real Set.univ, fun g hg => ?_⟩
    have hpos : 0 < (1 + hsn g) ^ N := pow_pos (by linarith [hsn_nonneg g]) N
    rw [ContinuousLinearMap.integral_apply hFi w]
    have hL : ⟪v, M.rep τ g (∫ k, InnerProductSpace.rankOne ℂ (π k u) (π k u) w ∂(Formalism.REAL.muK (M.ε τ)))⟫_ℂ =
        ∫ k, ⟪v, M.rep τ g (InnerProductSpace.rankOne ℂ (π k u) (π k u) w)⟫_ℂ ∂(Formalism.REAL.muK (M.ε τ)) := by
      have := ((innerSL ℂ v).comp (M.rep τ g)).integral_comp_comm hGi
      simpa using this.symm
    rw [hL, ← le_div_iff₀ hpos]
    refine (norm_integral_le_of_norm_le_const
      (C := ‖u‖ * ‖w‖ * (C * (1 + B) ^ N) / (1 + hsn g) ^ N)
      (Filter.Eventually.of_forall fun k => ?_)).trans_eq (by ring)
    rw [le_div_iff₀ hpos, InnerProductSpace.rankOne_apply, map_smul, inner_smul_right, norm_mul, mul_assoc]
    have hkK : Formalism.REAL.toMK k ∈ Formalism.REAL.Kset (M.ε τ) := k.2
    have hkk : Formalism.REAL.toMK k * (Formalism.REAL.toMK k)ᴴ = 1 := by
      have := Unitary.mul_star_self_of_mem hkK.1
      simpa [Matrix.star_eq_conjTranspose] using this
    have h1' : ‖⟪v, M.rep τ g (π k u)⟫_ℂ‖ * (1 + hsn g) ^ N ≤ C * (1 + B) ^ N :=
      coef_sigma_le M τ hC (hUk k) hkk (hB ⟨k, rfl⟩) hg
    have h2' : ‖⟪π k u, w⟫_ℂ‖ ≤ ‖u‖ * ‖w‖ := (norm_inner_le_norm _ _).trans (by rw [hπiso])
    calc ‖⟪π k u, w⟫_ℂ‖ * (‖⟪v, M.rep τ g (π k u)⟫_ℂ‖ * (1 + hsn g) ^ N)
        ≤ (‖u‖ * ‖w‖) * (C * (1 + B) ^ N) :=
          mul_le_mul h2' h1' (mul_nonneg (norm_nonneg _) hpos.le) (by positivity)
      _ = _ := by ring

  obtain ⟨Sf, hSf, haS, hSst⟩ := ha
  obtain ⟨Y, hYf, haY, hYB⟩ := (GlobalTheory.AdmUnitary.admissible_and_kFin_smooth _ (M.ε τ) (M.H τ) (M.σ τ)
    ⟨⟨h1, hmul⟩, hiso, hcont⟩ hI).1 Sf hSf hSst a haS
  have hYst : ∀ Bo : M.H τ →L[ℂ] M.H τ, (∀ k x, Bo (π k x) = π k (Bo x)) → ∀ y ∈ Y, Bo y ∈ Y := by
    intro Bo hBo
    refine hYB Bo fun k hk x => ?_
    rw [← Formalism.REAL.range_toMK] at hk
    obtain ⟨k', rfl⟩ := hk
    exact hBo k' x
  exact le_of_dense (Formalism.REAL.muK (M.ε τ)) π hπiso hπc (decSet M τ v N) hdense hT Y hYf hYst haY

end GlobalTheory.KFinDecay
