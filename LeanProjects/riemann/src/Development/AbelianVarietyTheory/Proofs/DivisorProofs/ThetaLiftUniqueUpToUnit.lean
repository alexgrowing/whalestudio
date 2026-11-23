import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormEqMulInner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFormsRescale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConjSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryRealPointsActFockSubstitution
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumUniqueAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjLiftUnique

section Gen

open Matrix Formalism.MainNotions.S

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {S : D.what₂.Tau → SPar} {M : DSModel W S}

variable (ψ V W) in

def thetaSub : Submodule ℂ (WO V W → ℂ) where
  carrier := {g | IsThetaFunO ψ V W g}
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' c _ := GlobalTheory.OrientedHeis.theta_smul c

variable (ω) in

structure IsInvForm (b : thetaSub ψ V W →ₗ⋆[ℂ] thetaSub ψ V W →ₗ[ℂ] ℂ) : Prop where
  symm : ∀ x y, b y x = conj (b x y)
  pos : ∀ x, 0 ≤ (b x x).re
  defin : ∀ x, b x x = 0 → x = 0
  inv : ∀ p (x y x' y' : thetaSub ψ V W), x'.1 = ω p x.1 → y'.1 = ω p y.1 → b x' y' = b x y

theorem exists_invForm (hω : IsWeilDatumO ψ V W χV χW ω) :
    ∃ b : thetaSub ψ V W →ₗ⋆[ℂ] thetaSub ψ V W →ₗ[ℂ] ℂ, IsInvForm ω b := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  have hN := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO V W) (ratL W V) K hK hKc
  obtain ⟨μ, 𝓕, hμ⟩ := (hN (fun _ => 1) continuous_const (fun h => one_ne_zero (congrFun h 0)) (fun _ _ _ => rfl)).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  have hI : ∀ x y : thetaSub ψ V W, Integrable (fun w => x.1 w * conj (y.1 w)) (μ.restrict 𝓕) := fun x y =>
    GlobalTheory.WeilInner.integrable_mul_conj _ x.2.cont.measurable y.2.cont.measurable
      (GlobalTheory.OrientedHeis.theta_bounded hω.std x.2) (GlobalTheory.OrientedHeis.theta_bounded hω.std y.2)
  have hn : ∀ x : thetaSub ψ V W, ∫ w in 𝓕, x.1 w * conj (x.1 w) ∂μ = ((∫ w in 𝓕, ‖x.1 w‖ ^ 2 ∂μ : ℝ) : ℂ) := fun x => by
    simp only [Complex.mul_conj', ← Complex.ofReal_pow]
    exact integral_complex_ofReal
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ w in 𝓕, y.1 w * conj (x.1 w) ∂μ)
    (fun x x' y => ?_) (fun a x y => ?_) (fun x y y' => ?_) (fun a x y => ?_),
    fun x y => ?_, fun x => ?_, fun x h0 => ?_, fun p x y x' y' hx hy => ?_⟩
  · simp only [Submodule.coe_add, Pi.add_apply, map_add, mul_add]
    exact integral_add (hI y x) (hI y x')
  · simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (conj a)]
    exact integral_const_mul _ _
  · simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (hI y x) (hI y' x)
  · simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
    exact integral_const_mul _ _
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [← integral_conj]
    simp only [map_mul, Complex.conj_conj, mul_comm]
  · rw [LinearMap.mk₂'ₛₗ_apply, hn, Complex.ofReal_re]
    exact integral_nonneg fun w => by positivity
  · rw [LinearMap.mk₂'ₛₗ_apply, hn, Complex.ofReal_eq_zero] at h0
    by_contra hne
    obtain ⟨c, hc⟩ := (hN x.1 x.2.cont (fun h => hne (Subtype.ext h)) (by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (x.2.quasi γ w)).trans (by rw [norm_mul, hω.std.1.2.1, one_mul]))).2
    have h2 := hc μ 𝓕 hμ.1 hμ.2.1 hμ.2.2
    simp only [norm_mul, mul_pow] at h2
    rw [integral_const_mul, h0, mul_zero] at h2
    exact zero_ne_one h2
  · simp only [LinearMap.mk₂'ₛₗ_apply, hx, hy]
    exact GlobalTheory.WeilInner.om_inner D ψ V W χV χW ω hω μ 𝓕 hμ p _ _ y.2 x.2

theorem exists_unit_eigen (hω : IsWeilDatumO ψ V W χV χW ω) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    {p : GA D V × GA D W} (h : ∃ c : ℂ, ω p f = c • f) : ∃ c : ℂ, ‖c‖ = 1 ∧ ω p f = c • f := by
  obtain ⟨c, hc⟩ := h
  by_cases f0 : f = 0
  · exact ⟨1, norm_one, by rw [f0, map_zero, smul_zero]⟩
  obtain ⟨b, hb⟩ := exists_invForm hω
  refine ⟨c, ?_, hc⟩
  have e := hb.inv p ⟨f, hf⟩ ⟨f, hf⟩ (c • ⟨f, hf⟩) (c • ⟨f, hf⟩) hc.symm hc.symm
  rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at e
  have e2 := (mul_eq_right₀ fun h => f0 (congrArg Subtype.val (hb.defin _ h))).1 e
  rw [Complex.conj_mul'] at e2
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [one_pow]; exact_mod_cast e2)

theorem exists_kop (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (τ : D.what₂.Tau) : FiniteDimensional ℂ (lowT M τ) ∧
    ∃ g : Formalism.REAL.Kset (M.ε τ) → lowT M τ →ₗ[ℂ] lowT M τ,
      (∀ k x, ((g k x : M.sm τ) : M.H τ) = M.σ τ k ((x : M.sm τ) : M.H τ)) ∧ (∀ k x, ‖g k x‖ = ‖x‖) ∧
      ∀ U : Submodule ℂ (lowT M τ), (∀ k, ∀ x ∈ U, g k x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  haveI := (h2 τ).1
  refine ⟨Module.Finite.of_injective (((M.sm τ).subtype ∘ₗ (lowT M τ).subtype).codRestrict
    (lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) fun x => x.2) fun x y h =>
      Subtype.ext (Subtype.ext (by exact congrArg (fun z : lowKSub (M.ε τ) (M.lam τ) (M.σ τ) => (z : M.H τ)) h)), ?_⟩
  let g : Formalism.REAL.Kset (M.ε τ) → lowT M τ →ₗ[ℂ] lowT M τ := fun k =>
    (((M.σ τ k : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ (M.sm τ).subtype ∘ₗ (lowT M τ).subtype).codRestrict (M.sm τ)
      fun x => h1 τ ((h2 τ).2.1 k k.2 _ x.2)).codRestrict (lowT M τ) fun x => (h2 τ).2.1 k k.2 _ x.2
  refine ⟨g, fun _ _ => rfl, fun k x => (M.ds τ).2.2.1.2.1 k (kset_uj k.2) _, fun U hU => ?_⟩
  by_cases h0 : U = ⊥
  · exact Or.inl h0
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  refine Or.inr (GlobalTheory.DefLift.eq_top_of_translates h1 h2 τ U v hv0 fun k hk u hu => ?_)
  have : u = g ⟨k, hk⟩ v := Subtype.ext (Subtype.ext hu)
  exact this ▸ hU _ v hv

open Classical in
variable (θ ω) in

def Eqv {c : CoefA V} (F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W) : Prop :=
  (∀ u ∈ GinfC V, ∀ x w, (F x (c.ρ u w)).1 = ω (u, 1) (F x w).1) ∧
  ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
    ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → ∀ w,
      (F (PiTensorProduct.tprod ℂ (Function.update v τ u)) w).1 =
        ω (1, atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)) (F (PiTensorProduct.tprod ℂ v) w).1

theorem exists_const_of_eqv (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {c : CoefA V} (hc : c.Is)
    {b : thetaSub ψ V W →ₗ⋆[ℂ] thetaSub ψ V W →ₗ[ℂ] ℂ} (hb : IsInvForm ω b)
    {F F' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W} (hF : Eqv θ ω F) (hF' : Eqv θ ω F') (w₀ : c.W) (h₀ : ‖w₀‖ = 1) :
    ∃ a : ℂ, ∀ (v : ∀ ρ, lowT M ρ) w (v' : ∀ ρ, lowT M ρ) w',
      b (F (PiTensorProduct.tprod ℂ v) w) (F' (PiTensorProduct.tprod ℂ v') w') =
        a * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ) := by
  classical
  refine exists_const (fun (v : ∀ ρ, lowT M ρ) w (v' : ∀ ρ, lowT M ρ) w' =>
    b (F (PiTensorProduct.tprod ℂ v) w) (F' (PiTensorProduct.tprod ℂ v') w')) w₀ h₀ (fun w w' τ v v' => ?_) fun v v' => ?_
  · obtain ⟨_, g, g1, g2, g3⟩ := exists_kop h1 h2 τ
    refine form_eq_mul_inner g (fun k x y => (LinearIsometry.mk (g k) (g2 k)).inner_map_map x y) g3
      ((b ∘ₛₗ (F.flip w ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ)).compl₂
        (F'.flip w' ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v' τ)) fun k x y => ?_
    have e1 := hF.2 τ k k.2 (Function.update v τ x) (g k x) (by rw [Function.update_self]; exact g1 k x) w
    have e2 := hF'.2 τ k k.2 (Function.update v' τ y) (g k y) (by rw [Function.update_self]; exact g1 k y) w'
    rw [Function.update_idem] at e1 e2
    exact hb.inv _ _ _ _ _ e1 e2
  · refine form_eq_mul_inner (fun u : GinfC V => c.ρ u) (fun u => hc.2.1 u) (fun U hU => hc.2.2.2.2 U fun h => ?_)
      ((b ∘ₛₗ F (PiTensorProduct.tprod ℂ v)).compl₂ (F' (PiTensorProduct.tprod ℂ v'))) fun u x y =>
        hb.inv _ _ _ _ _ (hF.1 u u.2 _ x) (hF'.1 u u.2 _ y)
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
    rw [map_mul, hc.1 k hk, mul_one]
    rintro _ ⟨x, hx, rfl⟩
    exact hU ⟨a, ha⟩ x hx

theorem exists_kset {n p : ℕ} {ε : Fin n → Bool} {G P B B' : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (h : IsONBasis G (P⁻¹ * Formalism.REAL.Jm ε * P) B p)
    (h' : IsONBasis G (P⁻¹ * Formalism.REAL.Jm ε * P) B' p) :
    ∃ k ∈ Formalism.REAL.Kset ε, P⁻¹ * k * P ∈ Formalism.QuantumDeterminants.UH G ∧ B' = P⁻¹ * k * P * B ∧
      P⁻¹ * Formalism.REAL.Jm ε * P * (P⁻¹ * k * P) = P⁻¹ * k * P * (P⁻¹ * Formalism.REAL.Jm ε * P) := by
  obtain ⟨e, he, h1, h2⟩ := h
  obtain ⟨e', he', h1', h2'⟩ := h'
  obtain rfl : e = e' := funext fun a => by
    rcases he a with h | h <;> rcases he' a with h' | h' <;> first | exact h.1.trans h'.1.symm | omega
  have hd : (Matrix.diagonal fun a => (e a : ℂ)) * (Matrix.diagonal fun a => (e a : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases he a with h | h <;> simp [h.1]
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  generalize (Matrix.diagonal fun a => (e a : ℂ)) = d at *
  have p1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have p2 : P⁻¹ * P = 1 := mul_eq_one_comm.1 p1
  have p3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, p1, Matrix.conjTranspose_one]
  obtain ⟨C, c2⟩ : ∃ C, C * B = 1 := ⟨d * (Bᴴ * G), by rw [Matrix.mul_assoc, h1, hd]⟩
  have c1 : B * C = 1 := mul_eq_one_comm.1 c2
  have c3 : Cᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, c1, Matrix.conjTranspose_one]
  have e0 : P⁻¹ * (P * (B' * C) * P⁻¹) * P = B' * C := by
    calc _ = (P⁻¹ * P) * (B' * C) * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [p2, Matrix.one_mul, Matrix.mul_one]
  have u : (B' * C)ᴴ * G * (B' * C) = G := by
    calc _ = Cᴴ * (B'ᴴ * G * B') * C := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Cᴴ * Bᴴ) * G * (B * C) := by rw [h1', ← h1]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [c3, c1, Matrix.one_mul, Matrix.mul_one]
  have cm : P⁻¹ * Formalism.REAL.Jm ε * P * (B' * C) = B' * C * (P⁻¹ * Formalism.REAL.Jm ε * P) := by
    generalize P⁻¹ * Formalism.REAL.Jm ε * P = s at *
    calc _ = B' * (C * B) * d * C := by rw [← Matrix.mul_assoc, h2', c2, Matrix.mul_one]
      _ = B' * C * (s * B) * C := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc, c1, Matrix.mul_one]
  have kJ : P * (B' * C) * P⁻¹ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (P * (B' * C) * P⁻¹) := by
    calc _ = P * (B' * C * (P⁻¹ * Formalism.REAL.Jm ε * P)) * P⁻¹ := by simp only [Matrix.mul_assoc, p1, Matrix.mul_one]
      _ = (P * P⁻¹) * Formalism.REAL.Jm ε * (P * (B' * C) * P⁻¹) := by rw [← cm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [p1, Matrix.one_mul]
  refine ⟨P * (B' * C) * P⁻¹, ⟨?_, kJ⟩, e0.symm ▸ u, by rw [e0, Matrix.mul_assoc, c2, Matrix.mul_one], e0.symm ▸ cm⟩
  have k2 : (P * (B' * C) * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * (B' * C) * P⁻¹) = Formalism.REAL.Jm ε := by
    calc _ = (P⁻¹)ᴴ * ((B' * C)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (B' * C)) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by rw [hG, u, ← hG]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [p3, p1, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  generalize P * (B' * C) * P⁻¹ = k at *
  calc kᴴ * k = kᴴ * (k * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = 1 := by rw [kJ, ← Matrix.mul_assoc, k2, hJ]

theorem exists_move (hω : IsWeilDatumO ψ V W χV χW ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK)
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) 1) (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {c : CoefA V}
    {F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W} (hF : Eqv θ ω F) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (cart M τ)) f)
    {BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {B B' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    {p : D.what₂.Tau → ℕ} (hB : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (B τ) (p τ))
    (hB' : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (B' τ) (p τ)) (Δ : PolF D W.rank V.rank) {v : ∀ ρ, lowT M ρ}
    (hn : ∀ ρ, ‖v ρ‖ = 1) {w : c.W}
    (he : (F (PiTensorProduct.tprod ℂ v) w).1 = pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f Δ) :
    ∃ (v' : ∀ ρ, lowT M ρ) (l : ℂ), (∀ ρ, ‖v' ρ‖ = 1) ∧ ‖l‖ = 1 ∧
      (F (PiTensorProduct.tprod ℂ v') w).1 = l • pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B' f Δ := by
  classical
  have key : ∀ s : Finset D.what₂.Tau, ∃ (v' : ∀ ρ, lowT M ρ) (l : ℂ), (∀ ρ, ‖v' ρ‖ = 1) ∧ ‖l‖ = 1 ∧
      (F (PiTensorProduct.tprod ℂ v') w).1 =
        l • pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (s.piecewise B' B) f Δ := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨v, 1, hn, norm_one, by rw [Finset.piecewise_empty, one_smul, he]⟩
    | insert τ s hτ ih =>
      obtain ⟨v', l, n1, n2, e⟩ := ih
      obtain ⟨-, g, g1, g2, -⟩ := exists_kop h1 h2 τ
      obtain ⟨k, hk, k1, k2, k3⟩ := exists_kset (M.fr_unit τ) (M.fr_gram τ) (hB τ) (hB' τ)
      have sp := GlobalTheory.PointAtPlaceHom.atTau_spec hθ W τ k1
      have e1 := hF.2 τ k hk v' (g ⟨k, hk⟩ (v' τ)) (g1 _ _) w
      generalize atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ) = h at sp e1
      have s1 : compAt θ τ (Formalism.L2.Theta.mt W h) = (M.fr τ)⁻¹ * k * M.fr τ := sp.2.1
      have s2 : ∀ ρ, ρ ≠ τ → compAt θ ρ (Formalism.L2.Theta.mt W h) = 1 := sp.2.2
      have s0 : ∀ ρ, compAt θ ρ (Formalism.L2.Theta.mt V 1) = 1 := fun ρ => GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)
      have cT : ∀ ρ, cart M ρ * compAt θ ρ (Formalism.L2.Theta.mt W h) = compAt θ ρ (Formalism.L2.Theta.mt W h) * cart M ρ :=
        fun ρ => by
          by_cases hρ : ρ = τ
          · subst hρ; rw [s1]; exact k3
          · rw [s2 ρ hρ, Matrix.one_mul, Matrix.mul_one]
      obtain ⟨a, a1, a2⟩ := exists_unit_eigen hω hf (GlobalTheory.DefLift.FockAct.om_vac hω hθ kV kW (sS := fun _ => 1) hV
        (GlobalTheory.Chain.VacVec.cart_isCartanInv M) hf hv (one_mem _) sp.1 (fun ρ => by rw [Matrix.one_mul, Matrix.mul_one]) cT)
      refine ⟨Function.update v' τ (g ⟨k, hk⟩ (v' τ)), l * a, fun ρ => ?_, by rw [norm_mul, n2, a1, one_mul], ?_⟩
      · by_cases hρ : ρ = τ
        · subst hρ; rw [Function.update_self, g2, n1]
        · rw [Function.update_of_ne hρ, n1]
      · rw [e1, e, map_smul, (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χV χW ω hω hθ (fun _ => 1) (fun _ => 1) BV BV
          (cart M) (cart M) (s.piecewise B' B) ((insert τ s).piecewise B' B) 1 h
          (fun ρ => by rw [Matrix.one_mul, Matrix.mul_one]) cT (fun ρ => by rw [s0, Matrix.one_mul]) (fun ρ => ?_) f hf Δ).2,
          a2, GlobalTheory.FiniteFock.pureTensorO_smul, mul_smul]
        by_cases hρ : ρ = τ
        · subst hρ
          rw [s1, Finset.piecewise_insert_self, Finset.piecewise_eq_of_notMem _ _ _ hτ, k2]
        · rw [s2 ρ hρ, Matrix.one_mul, Finset.piecewise_insert_of_ne _ _ _ hρ]
  simpa only [Finset.piecewise_univ] using key Finset.univ

theorem vec_unique (kV : V.SigOK) (kW : W.SigOK) {sS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hS : ∀ τ, IsCartanInv (gramAt D V τ) (sS τ))
    (hT : ∀ τ, IsCartanInv (gramAt D W τ) (sT τ)) {ΛS : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} (dS : IsSelfDualC V ΛS) (dT : IsSelfDualC W ΛT)
    {βS βT Pg Q ξ} {f₀ f f₀' f' : WO V W → ℂ} (h : IsThPVecOf ψ θ V W sS sT ΛS ΛT βS βT Pg Q ξ f₀ f)
    (h' : IsThPVecOf ψ θ V W sS sT ΛS ΛT βS βT Pg Q ξ f₀' f') : ∃ a : ℂ, ‖a‖ = 1 ∧ f' = a • f := by
  obtain ⟨h₀, e, he, ⟨T, hT₀⟩, hall⟩ := h
  obtain ⟨h₀', e', he', -, hall'⟩ := h'
  obtain rfl : e' = e := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
    obtain ⟨⟨es', hes', rfl⟩, -⟩ := he'
    exact Finset.sum_congr rfl fun PP hPP =>
      (((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 PP _ _ (Or.inl ⟨hes PP hPP, rfl⟩)).2.2.2.1 _ _
        (Or.inl ⟨hes' PP hPP, rfl⟩)).1
  obtain ⟨a, ha, rfl⟩ := GlobalTheory.vacuum_unique_all D ψ θ h₀.1 h₀.2.inf V W sS sT kV kW hS hT ΛS ΛT dS dT f₀ f₀' h₀ h₀'
  refine ⟨a, ha, ?_⟩
  rw [hall T hT₀]
  exact hall' (a • T)
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT₀.trans Φ hΦ x hx, GlobalTheory.SplitScalar.heisO_smul]
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT₀.modul Φ hΦ y hy, GlobalTheory.SplitScalar.heisO_smul]
      vac := by rw [LinearMap.smul_apply, hT₀.vac] }

theorem exists_isometry {K X ι : Type} [Field K] [AddCommGroup X] [Module K X] [Finite ι] (bX : Module.Basis ι K X)
    {σ : K →+* ℂ} {c c' : CoefA V} (hc : c.Is) (hc' : c'.Is) (c₁ : X →ₛₗ[σ] c.W) (c₁' : X →ₛₗ[σ] c'.W)
    (i1 : LinearIndependent ℂ fun a => c₁ (bX a)) (s1 : Submodule.span ℂ (Set.range fun a => c₁ (bX a)) = ⊤)
    (i2 : LinearIndependent ℂ fun a => c₁' (bX a)) (s2 : Submodule.span ℂ (Set.range fun a => c₁' (bX a)) = ⊤)
    (hp : ∀ a b, ⟪c₁' (bX a), c₁' (bX b)⟫_ℂ = ⟪c₁ (bX a), c₁ (bX b)⟫_ℂ)
    (hr : ∀ γ ∈ GQ V, ∃ r : X → X, (∀ v, c₁ (r v) = c.ρ γ (c₁ v)) ∧ ∀ v, c₁' (r v) = c'.ρ γ (c₁' v)) :
    ∃ Φ : c.W ≃ₗ[ℂ] c'.W, (∀ v, Φ (c₁ v) = c₁' v) ∧ (∀ x, ‖Φ x‖ = ‖x‖) ∧ ∀ h x, Φ (c.ρ h x) = c'.ρ h (Φ x) := by
  haveI := Fintype.ofFinite ι
  let b1 := Module.Basis.mk i1 s1.ge
  let b2 := Module.Basis.mk i2 s2.ge
  let Φ := b1.equiv b2 (Equiv.refl _)
  have hb : ∀ a, Φ (c₁ (bX a)) = c₁' (bX a) := fun a => by
    simpa [b1, b2] using b1.equiv_apply a b2 (Equiv.refl _)
  have h1 : ∀ v, Φ (c₁ v) = c₁' v := fun v =>
    LinearMap.congr_fun (bX.ext (f₁ := Φ.toLinearMap.comp c₁) (f₂ := c₁') hb) v
  refine ⟨Φ, h1, fun x => ?_, fun h x => ?_⟩
  · have : ⟪Φ x, Φ x⟫_ℂ = ⟪x, x⟫_ℂ := by
      rw [← b1.sum_repr x]
      simp only [b1, Module.Basis.mk_apply, map_sum, map_smul, hb, sum_inner, inner_sum, inner_smul_left,
        inner_smul_right, hp]
    rw [@norm_eq_sqrt_re_inner ℂ, this, ← @norm_eq_sqrt_re_inner ℂ]
  · have hrat : ∀ γ ∈ GQ V, Φ (c.ρ γ x) = c'.ρ γ (Φ x) := fun γ hγ => by
      obtain ⟨r, r1, r2⟩ := hr γ hγ
      refine LinearMap.congr_fun (LinearMap.ext_on_range (f := Φ.toLinearMap ∘ₗ c.ρ γ) (g := c'.ρ γ ∘ₗ Φ.toLinearMap)
        s1 fun a => ?_) x
      change Φ (c.ρ γ _) = c'.ρ γ (Φ _)
      rw [← r1, h1, r2, h1]
    obtain ⟨u, hu, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
    rw [map_mul, map_mul, hc.1 k hk, hc'.1 k hk, mul_one, mul_one]
    by_contra hne
    obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu _
      (isOpen_ne_fun (Φ.toLinearMap.continuous_of_finiteDimensional.comp (hc.2.2.1 x)) (hc'.2.2.1 (Φ x))) hne
    refine hU ?_
    change Φ (c.ρ (γ * k) x) = c'.ρ (γ * k) (Φ x)
    rw [map_mul, map_mul, hc.1 k hk, hc'.1 k hk, mul_one, mul_one, hrat γ hγ]

theorem io_unique {ω' : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χV χW ω)
    (hω' : IsWeilDatumO ψ V W χV χW ω') (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK)
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) 1) (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {c c' : CoefA V} (hc : c.Is)
    (Φ : c.W ≃ₗ[ℂ] c'.W) (hΦ : ∀ x, ‖Φ x‖ = ‖x‖) (hΦ' : ∀ h x, Φ (c.ρ h x) = c'.ρ h (Φ x))
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (cart M τ)) f)
    {a : ℂ} (ha : ‖a‖ = 1)
    {BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {B B' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    {p : D.what₂.Tau → ℕ} (hB : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (B τ) (p τ))
    (hB' : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (B' τ) (p τ)) {Δ : PolF D W.rank V.rank}
    {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank} {io' : LowT M →ₗ[ℂ] c'.W →ₗ[ℂ] PolF D W.rank V.rank}
    (hio : IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f) Δ io)
    (hio' : IsIoW θ M c' ω' (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B' (a • f)) Δ io') :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ x w, pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B' (a • f) (io' x (Φ w)) =
      κ • pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) := by
  classical
  have t1 := GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (fun _ => 1) BV (cart M) B hf
  have t2 := GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (fun _ => 1) BV (cart M) B' (GlobalTheory.OrientedHeis.theta_smul a hf)
  have hu := GlobalTheory.WeilUniq.weilDatum_unique D ψ hω.std V W χV χW ω ω' hω hω'
  let F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W :=
    io.compr₂ ((pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f).codRestrict _ t1)
  let F' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W :=
    (io'.compl₂ Φ.toLinearMap).compr₂ ((pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B' (a • f)).codRestrict _ t2)
  have f1 : ∀ x w, (F x w).1 = pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) := fun _ _ => rfl
  have f2 : ∀ x w, (F' x w).1 = pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B' (a • f) (io' x (Φ w)) := fun _ _ => rfl
  clear_value F F'
  have hF : Eqv θ ω F := ⟨fun u hu x w => by rw [f1, f1, hio.1 u hu],
    fun τ k hk v u hu w => by rw [f1, f1, hio.2.1 τ k hk v u hu]⟩
  have hF' : Eqv θ ω F' := ⟨fun u hu' x w => by rw [f2, f2, hu _ _ (t2 _), hio'.1 u hu', hΦ'],
    fun τ k hk v u hu' w => by rw [f2, f2, hu _ _ (t2 _), hio'.2.1 τ k hk v u hu']⟩
  obtain ⟨v₀, w₀, n1, n2, e⟩ := hio.2.2
  obtain ⟨v₀', w₀', n1', n2', e'⟩ := hio'.2.2
  obtain ⟨w₁, rfl⟩ := Φ.surjective w₀'
  obtain ⟨v₁, l, n3, hl, e1⟩ := exists_move hω hθ kV kW hV h1 h2 hF hf hv hB hB' Δ n1 ((f1 _ w₀).trans (congrArg _ e))
  obtain ⟨b, hb⟩ := exists_invForm hω
  obtain ⟨c₁, k1⟩ := exists_const_of_eqv h1 h2 hc hb hF hF w₀ n2
  obtain ⟨c₂, k2⟩ := exists_const_of_eqv h1 h2 hc hb hF' hF' w₀ n2
  obtain ⟨c₃, k3⟩ := exists_const_of_eqv h1 h2 hc hb hF hF' w₀ n2
  have a0 : a ≠ 0 := fun h => by simp [h] at ha
  obtain ⟨κ, hκ, hk⟩ := exists_phase b hb.symm hb.pos hb.defin (fun v w => F (PiTensorProduct.tprod ℂ v) w)
    (fun v w => F' (PiTensorProduct.tprod ℂ v) w) k1 k2 k3 n3 n1' n2 ((hΦ w₁).symm.trans n2') (l := l * a⁻¹)
    (by rw [norm_mul, norm_inv, hl, ha, inv_one, one_mul]) (Subtype.ext (by
      rw [e1, Submodule.coe_smul, f2, e', GlobalTheory.FiniteFock.pureTensorO_smul, smul_smul, inv_mul_cancel_right₀ a0]))
  have hFF : F' = κ • F := PiTensorProduct.ext (MultilinearMap.ext fun v => LinearMap.ext (hk v))
  exact ⟨κ, hκ, fun x w => by rw [← f1, ← f2, hFF]; rfl⟩

theorem thetaP_eq {ω' : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {c c' : CoefA V} {P T : Type} [AddCommGroup P]
    [Module ℂ P] [AddCommGroup T] [Module ℂ T] {pt pt' : P → WO V W → ℂ} {io : T →ₗ[ℂ] c.W →ₗ[ℂ] P}
    {io' : T →ₗ[ℂ] c'.W →ₗ[ℂ] P} (hu : ∀ p x, ω' p (pt' x) = ω p (pt' x)) (Φ : c.W → c'.W) {κ : ℂ}
    (hk : ∀ x w, pt' (io' x (Φ w)) = κ • pt (io x w)) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)}
    {B : Submodule ℂ (GA D V → c.W)} {B' : Submodule ℂ (GA D V → c'.W)} {th : B →ₗ[ℂ] (T →ₗ[ℂ] (GA D W → ℂ))}
    {th' : B' →ₗ[ℂ] (T →ₗ[ℂ] (GA D W → ℂ))} (h : Lift.IsThetaP ν 𝓕 (fun g h φ => thetaKO ω h g φ) pt io B th)
    (h' : Lift.IsThetaP ν 𝓕 (fun g h φ => thetaKO ω' h g φ) pt' io' B' th') (y : B) (y' : B')
    (hy : ∀ h, y'.1 h = Φ (y.1 h)) (v : T) : th' y' v = κ • th y v := by
  funext g
  simp only [h'.eq, Lift.thetaPInt, thetaKO, hu]
  simp only [h.eq, Lift.thetaPInt, thetaKO, hy, hk, map_smul, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul κ _

end Gen

end GlobalTheory.ConjLiftUnique

end
