import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift GlobalTheory.RawLift

namespace GlobalTheory.FockKillAdapted

open GlobalTheory.FockKill GlobalTheory.FockIndep GlobalTheory.OrientedHeis
open scoped Real Classical

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {τ : D.what₂.Tau}
  {Sp : D.what₂.Tau → SPar} {M : DSModel T Sp}

theorem exists_coef {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) {p : ℕ} {B' : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hBT : IsONBasis (gramAt D T τ) (cart M τ) B' p)
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (lX : X ∈ lieAt T τ) (lY : Complex.I • (cart M τ * X) ∈ lieAt T τ) (ha : cart M τ * X = -(X * cart M τ)) :
    ∃ ν : Fin T.rank → Fin T.rank → ℂ, (∀ a b : Fin T.rank, ¬ (p ≤ (a : ℕ) ∧ (b : ℕ) < p) → ν a b = 0) ∧
      ∀ a c b d, ∀ u, u = unitMap (BS τ) B' a c → ∀ u', u' = unitMap (BS τ) B' b d →
        ((omDir S T τ (X * u) τ u' : ℝ) + Complex.I * (omDir S T τ (cplxO 1 (cart M τ) (X * u)) τ u' : ℝ)) +
          (-Complex.I) * ((omDir S T τ (X * cplxO 1 (cart M τ) u) τ u' : ℝ) +
            Complex.I * (omDir S T τ (cplxO 1 (cart M τ) (X * cplxO 1 (cart M τ) u)) τ u' : ℝ)) =
        (if c = d then ν a b else 0) + (if d = c then ν b a else 0) := by
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  obtain ⟨ε, hε, -, ht⟩ := hBT
  let o : Matrix (Fin T.rank) (Fin T.rank) ℂ → Fin T.rank → Fin T.rank → ℝ := fun W a b =>
    2 * (tauE D τ D.host.xi0 * (B'ᴴ * gramAt D T τ * W * B') a b).re
  have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have osym : ∀ W ∈ lieAt T τ, ∀ a b, o W a b = o W b a := fun W hW a b =>
    congrArg (2 * ·) (skew_entry (GlobalTheory.SmoothAutCheck.gramAt_herm T τ) hW hre a b)
  have ozero : ∀ W, cart M τ * W = -(W * cart M τ) → ∀ a b : Fin T.rank, ((a : ℕ) < p ↔ (b : ℕ) < p) →
      o W a b = 0 := fun W hW a b hab => by
    simp only [o]
    rw [zero_entry (hT τ) ht hW, mul_zero, Complex.zero_re, mul_zero]
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hε b with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · simp only [h1, h3, Complex.ofReal_one, star_one]; norm_num
    · exact absurd (hab.1 h2) (by omega)
    · exact absurd (hab.2 h4) (by omega)
    · simp only [h1, h3, Complex.ofReal_neg, Complex.ofReal_one, star_neg, star_one]; norm_num
  have hom1 : ∀ W a c b d, omDir S T τ (W * unitMap (BS τ) B' a c) τ (unitMap (BS τ) B' b d) =
      if c = d then o W b a else 0 := fun W a c b d => by
    rw [omDir, if_pos rfl, trace_unitMap (hB τ)]
    split_ifs <;> simp [o]
  have hJ : ∀ (W : Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      cplxO 1 (cart M τ) (W * u) = Complex.I • (cart M τ * W) * u := fun W u => by
    rw [cplxO, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]
  have hJ' : ∀ u : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      X * cplxO 1 (cart M τ) u = (-(Complex.I • (cart M τ * X))) * u := fun u => by
    rw [cplxO, Matrix.mul_one, ha, smul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hJ'' : Complex.I • (cart M τ * -(Complex.I • (cart M τ * X))) = X := by
    rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, (hT τ).1, Matrix.one_mul, smul_neg, smul_smul,
      Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  have oneg : ∀ W a b, o (-W) a b = -o W a b := fun W a b => by
    simp only [o, Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_apply, mul_neg, Complex.neg_re]
  clear_value o
  refine ⟨fun a b => if p ≤ (a : ℕ) ∧ (b : ℕ) < p then
    2 * (o X a b + Complex.I * o (Complex.I • (cart M τ * X)) a b) else 0, fun a b h => if_neg h, ?_⟩
  rintro a c b d _ rfl _ rfl
  rw [hJ', hJ, hJ, hJ'', hom1, hom1, hom1, oneg]
  by_cases e3 : c = d
  swap
  · simp [e3, Ne.symm e3]
  subst e3
  simp only [if_true]
  have z1 := ozero _ ha
  have z2 := ozero _ (anti_I ha)
  have s1 := osym _ lX a b
  have s2 := osym _ lY a b
  generalize Complex.I • (cart M τ * X) = Y at z2 s2
  rw [s1, s2]
  have e : (o X b a : ℂ) + Complex.I * o Y b a + -Complex.I * ((-o Y b a : ℝ) + Complex.I * o X b a) =
      2 * (o X b a + Complex.I * o Y b a) := by
    push_cast
    linear_combination (-o X b a : ℂ) * Complex.I_mul_I
  rw [e]
  by_cases ha' : (a : ℕ) < p <;> by_cases hb' : (b : ℕ) < p
  · simp [z1 b a (by simp [ha', hb']), z2 b a (by simp [ha', hb'])]
  · rw [if_neg (by omega), if_pos (by omega), zero_add]
  · rw [if_pos (by omega), if_neg (by omega), add_zero]
  · simp [z1 b a (by simp [ha', hb']), z2 b a (by simp [ha', hb'])]

end GlobalTheory.FockKillAdapted

namespace GlobalTheory.FockKillAdapted

open GlobalTheory.FockKill GlobalTheory.FockIndep GlobalTheory.OrientedHeis
open scoped Real Classical

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {τ : D.what₂.Tau}
  {Sp : D.what₂.Tau → SPar} {M : DSModel T Sp}

theorem gen_kill (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) {p : ℕ} {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hBT : IsONBasis (gramAt D T τ) (cart M τ) (BT τ) p)
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} {GX GY : Module.End ℂ (WO S T → ℂ)}
    (hX : IsGen ψ om θ τ X GX) (hY : IsGen ψ om θ τ (Complex.I • (cart M τ * X)) GY)
    (lX : X ∈ lieAt T τ) (lY : Complex.I • (cart M τ * X) ∈ lieAt T τ) (ha : cart M τ * X = -(X * cart M τ))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f)
    (h0 : (GX + Complex.I • GY) f = 0) {P : MvPolynomial (FVar D T.rank S.rank) ℂ}
    (hP : ∀ a b : Fin T.rank, p ≤ (a : ℕ) → (b : ℕ) < p →
      ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) :
    (GX + Complex.I • GY) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P) = 0 := by
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hS := fun τ => isCartanInv_one (hB τ)
  obtain ⟨ν, n0, hν⟩ := exists_coef hB hBT lX lY ha
  unfold pureTensorO aPlusAll
  refine (quad_pure (P := IsThetaFunO ψ S T) (G := GX + Complex.I • GY)
    (B := fun k g => ((fockScale D k.1 : ℂ)⁻¹ * (if k.1 = τ then (1 : ℂ) else 0)) •
      (annih (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) (X * unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g +
        (-Complex.I) • annih (heisO ψ S T) θ τ (cplxO 1 (cart M τ))
          (X * cplxO 1 (cart M k.1) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2)) g))
    (μ := fun i j => if i.1 = τ then if j.1 = τ then if i.2.2 = j.2.2 then
      ((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * ν i.2.1 j.2.1 else 0 else 0 else 0)
    (fun _ _ => theta_add) (fun a _ => theta_smul a) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf ?_ h0 P).trans ?_
  · exact fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  · exact fun i j _ h => aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
  · exact fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  · intro i g g' hg hg'
    rw [annih_add hψ hθ _ _ _ hg hg', annih_add hψ hθ _ _ _ hg hg']
    simp only [smul_add]
    abel
  · intro i a g hg
    rw [annih_smul hψ hθ _ _ _ _ hg, annih_smul hψ hθ _ _ _ _ hg, smul_comm _ a, ← smul_add, smul_comm _ a]
  · rintro ⟨τ₁, a, c⟩ ⟨τ₂, b, d⟩ g hg
    have ta := fun z => annih_theta hψ hθ τ (cplxO 1 (cart M τ)) z hg
    have aa := fun z => annih_aPlus (sS := fun _ => 1) hψ hθ τ z hS hT τ₂ (unitMap (BS τ₂) (BT τ₂) b d) hg
    dsimp only at aa ⊢
    rw [aa, aa, aPlus_smul hψ hθ _ _ _ _ (theta_add (ta _) (theta_smul _ (ta _))),
      aPlus_add hψ hθ _ _ _ (ta _) (theta_smul _ (ta _)), aPlus_smul hψ hθ _ _ _ _ (ta _), smul_add (-Complex.I),
      add_add_add_comm, smul_add, smul_smul, ← add_smul, smul_smul]
    refine congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)
    by_cases e1 : τ₁ = τ
    swap
    · simp only [if_neg e1, ite_self, mul_zero, zero_mul, add_zero]
    by_cases e2 : τ₂ = τ
    swap
    · simp [e2, omDir, Ne.symm e2]
    subst e1
    subst e2
    have := hν a c b d _ rfl _ rfl
    simp only [if_true]
    by_cases e3 : c = d
    · simp only [if_pos e3, if_pos e3.symm] at this ⊢
      linear_combination ((fockScale D τ₂ : ℂ)⁻¹ * (fockScale D τ₂ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * this
    · simp only [if_neg e3, if_neg (Ne.symm e3)] at this ⊢
      linear_combination ((fockScale D τ₂ : ℂ)⁻¹ * (fockScale D τ₂ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * this
  · exact fun i _ h => gen_aPlus hψ hθ hX hY _ _ _ h
  · intro i
    rw [hv, hv, smul_zero, add_zero, smul_zero]
  · refine (congrArg _ ?_).trans (map_zero _)
    simp only [Fintype.sum_prod_type, ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.smul_sum]
    by_cases hab : p ≤ (a : ℕ) ∧ (b : ℕ) < p
    · rw [hP a b hab.1 hab.2, smul_zero]
    · rw [n0 a b hab, mul_zero, zero_smul]

end GlobalTheory.FockKillAdapted

open Formalism.DivisionValues GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.FockKillAdapted

open GlobalTheory.FockKill GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.RawLift.FockCoef in

theorem killed_of_harmonic_adapted : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), S.SigOK → T.SigOK → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → ∀ p : D.what₂.Tau → ℕ, (∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ)) → ∀ (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsONBasis (gramAt D T τ) (cart M τ) (BT τ) (p τ)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ P : PolF D T.rank S.rank, (∀ τ, ∀ a b : Fin T.rank, p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) → GlobalTheory.RawLift.FockCoef.Killed om θ M (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P) := by
  intro D ψ θ S T χS χT om hθ hom Sp M kS kT BS hBS p hp BT hBT f hf hv P hP
  intro τ Z hZ h w
  have hψ := hom.std
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 := fun τ => by
    obtain ⟨ε, h1, h2, -⟩ := hBS τ
    rw [h2, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · rw [h.1, Complex.ofReal_one]
    · exact absurd a.2 (not_lt.2 h.2)
  have hS := fun τ => isCartanInv_one (hB τ)
  obtain ⟨h1, h2⟩ := pMinus_laws hZ
  obtain ⟨ha, eY⟩ := parts (GlobalTheory.SmoothAutCheck.gramAt_unit T τ) (hT τ) h1 h2
  obtain ⟨lX, lY⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  unfold RderC
  unfold conjAt at lX lY ⊢
  rw [eY] at lY ⊢
  generalize (1 / 2 : ℂ) • (Z + -((gramAt D T τ)⁻¹ * Zᴴ * gramAt D T τ)) = X at ha lX lY
  obtain ⟨GX, hX⟩ : ∃ G, IsGen ψ om θ τ X G := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ _ lX
  obtain ⟨GY, hY⟩ : ∃ G, IsGen ψ om θ τ (Complex.I • (cart M τ * X)) G :=
    GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ _ lY
  have hφ : IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P) :=
    pure_mem (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
      (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) hf _
  have key := gen_kill hψ hθ hB (hBT τ) hX hY lX lY ha hf (hv τ)
    (gen_kill_vac hom hθ kS kT hS hT hX hY lX lY ha hf hv) (hP τ)
  generalize pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P = φ at key hφ
  funext g
  have a1 := ((hX φ hφ).2.2.2 (h, g) w).deriv
  have a2 := ((hY φ hφ).2.2.2 (h, g) w).deriv
  simp only [Prod.mk_mul_mk, mul_one] at a1 a2
  have a3 := congrFun (congrArg (om (h, g)) key) w
  rw [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, map_zero] at a3
  simp only [Pi.add_apply, Pi.smul_apply, Rder]
  rw [a1, a2]
  exact a3

end GlobalTheory.FockKillAdapted

end
