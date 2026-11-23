import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

noncomputable section

open WittVector Ideal Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

open GlobalTheory.PDivGroup GlobalTheory.Sandwich

structure IsIntegers (O C : Type) [CommRing O] [NormedField C] [Algebra O C] : Prop where

  inj : Function.Injective (algebraMap O C)

  mem_iff : ∀ x : C, (∃ a : O, algebraMap O C a = x) ↔ ‖x‖ ≤ 1

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

def zeta (ε : PreTilt O p) (n : ℕ) : O := PreTilt.untilt (root^[n] ε)

theorem zeta_succ_pow (ε : PreTilt O p) (n : ℕ) : zeta ε (n + 1) ^ p = zeta ε n := by
  unfold zeta
  rw [← map_pow, Function.iterate_succ_apply']
  congr 1
  exact (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply _

def IsPrimitiveSystem (ε : PreTilt O p) : Prop := ∀ n, IsPrimitiveRoot (zeta ε n) (p ^ n)

theorem IsPrimitiveSystem.zeta_zero {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    zeta ε 0 = 1 := by simpa using (hε 0).pow_eq_one

def epsTate {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : (PDivGroup.mu p O).Tate :=
  muTate O (zeta ε) hε.zeta_zero (zeta_succ_pow ε)

def epsEquiv [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    ℤ_[p] ≃ₗ[ℤ_[p]] (PDivGroup.mu p O).Tate :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ (epsTate hε))
    (smul_muTate_bijective (zeta ε) hε.zeta_zero (zeta_succ_pow ε) hε)

def epsPairing [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (t : G.Tate) (χ : G.dual.Tate) : ℤ_[p] :=
  (epsEquiv hε).symm (pairing G O t χ)

theorem epsPairing_smul [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε)
    (G : PDivGroup p O) (t : G.Tate) (χ : G.dual.Tate) :
    epsPairing hε G t χ • epsTate hε = pairing G O t χ :=
  (epsEquiv hε).apply_symm_apply _

def toO {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (t : G.Tate) :
    Fin h → O := fun i => padicToO p O (e t i)

def pairingO [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) {G : PDivGroup p O}
    {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (y : Fin h → O) (χ : G.dual.Tate) : O :=
  ∑ i, y i * padicToO p O (epsPairing hε G (e.symm (Pi.single i 1)) χ)

theorem pairingO_toO [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε)
    {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (t : G.Tate)
    (χ : G.dual.Tate) : pairingO hε e (toO e t) χ = padicToO p O (epsPairing hε G t χ) := by
  have ht : t = ∑ i, e t i • e.symm (Pi.single i 1) := by
    apply e.injective
    rw [map_sum]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [ht]
  simp only [pairingO, toO, epsPairing, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, map_mul]

section Datum

variable {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def actH (D : Datum ε h Λ) (a : Λ) : (Fin h → O) →ₗ[O] (Fin h → O) :=
  Matrix.toLin' ((D.ρM a).map (fontaineTheta O p))

def bQuot (D : Datum ε h Λ) : ((Fin h → O) ⧸ D.Fil) →ₗ[O] (Fin h → O) :=
  D.Fil.liftQ D.bb le_rfl

structure Realizes [IsDomain O] (hε : IsPrimitiveSystem ε) (u₁ u₂ : Oˣ) (G : PDivGroup p O)
    (ρ : Action Λ G) (D : Datum ε h Λ) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (fil : G.dual.omega ≃ₗ[O] D.Fil) (lie : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] G.Lie) : Prop where

  tate_act : ∀ (a : Λ) (t : G.Tate), e (ρ.onTate O a t) = D.ρT a *ᵥ e t

  fil_act : ∀ (a : Λ) (w : G.dual.omega),
    (fil (ρ.onOmegaDual a w) : Fin h → O) = actH D a (fil w)

  lie_act : ∀ (a : Λ) (m : Fin h → O),
    lie (D.Fil.mkQ (actH D a m)) = ρ.onLie a (lie (D.Fil.mkQ m))

  al_eq : ∀ t : G.Tate, D.al (toO e t) =
    (u₁ : O) • (fil (omegaMap G.dual (PDivGroup.mu p O) (dualChar G t) (dlogT p O)) : Fin h → O)

  b_eq : ∀ (x : G.Lie) (χ : G.dual.Tate), pairingO hε e (bQuot D (lie.symm x)) χ =
    (u₂ : O) * x (omegaMap G (PDivGroup.mu p O) (charHom G χ) (dlogT p O))

end Datum

def HodgeTateSandwichAt [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : Prop :=
  ∃ u₁ u₂ : Oˣ, ∀ (G : PDivGroup p O) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ρ : Action Λ G),
    ∃ (D : Datum ε G.height Λ) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]))
      (fil : G.dual.omega ≃ₗ[O] D.Fil) (lie : ((Fin G.height → O) ⧸ D.Fil) ≃ₗ[O] G.Lie),
      Realizes hε u₁ u₂ G ρ D e fil lie

def HodgeTateSandwich : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C] [NormedAlgebra ℚ_[p] C]
    [CompleteSpace C] [IsAlgClosed C] (O : Type) [CommRing O] [IsDomain O] [Algebra O C],
    IsIntegers O C →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
      (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), HodgeTateSandwichAt hε

section Inhabitant

variable [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε)

omit [IsDomain O] in
theorem mult_bb (y : Fin 1 → O) : (mult ε).bb y = y := by
  simp [Datum.bb, mult]

omit [IsDomain O] in
theorem mult_Fil : (mult ε).Fil = ⊥ :=
  LinearMap.ker_eq_bot'.2 fun y hy => (mult_bb y).symm.trans hy

def muBasis : (PDivGroup.mu p O).Tate ≃ₗ[ℤ_[p]] (Fin 1 → ℤ_[p]) :=
  (epsEquiv hε).symm ≪≫ₗ (LinearEquiv.funUnique (Fin 1) ℤ_[p] ℤ_[p]).symm

variable (ε) in

def muLie : ((Fin 1 → O) ⧸ (mult ε).Fil) ≃ₗ[O] (PDivGroup.mu p O).Lie :=
  (mult ε).Fil.quotEquivOfEqBot mult_Fil ≪≫ₗ LinearEquiv.funUnique (Fin 1) O O ≪≫ₗ
    (LinearMap.ringLmapEquivSelf O O O).symm ≪≫ₗ (muOmegaEquiv p O).symm.dualMap

omit [IsDomain O] in
theorem muLie_mk (m : Fin 1 → O) : muLie ε ((mult ε).Fil.mkQ m) (dlogT p O) = m 0 := by
  have h : (muOmegaEquiv p O).symm (dlogT p O) = 1 := muLieGen_dlogT p O
  simp [muLie, h]

omit [IsDomain O] in
instance : Subsingleton (mult ε).Fil := by rw [mult_Fil]; infer_instance

theorem realizes_mu (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
    [CharZero C] : Realizes hε 1 1 (PDivGroup.mu p O) (padicAction _) (mult ε) (muBasis hε)
      (LinearEquiv.ofSubsingleton _ _) (muLie ε) where
  tate_act a t := by
    have h : (padicAction (PDivGroup.mu p O)).onTate O a t = a • t := by
      change tateMap _ _ O (algebraMap ℤ_[p] (CategoryTheory.End (PDivGroup.mu p O)) a) t = _
      rw [Algebra.algebraMap_eq_smul_one]
      exact (LinearMap.congr_fun (map_smul (tateMap _ _ O) a (CategoryTheory.CategoryStruct.id _)) t)
    rw [h, map_smul]
    simp [mult, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
  fil_act a w := by
    rw [Subsingleton.elim (LinearEquiv.ofSubsingleton _ _ _ : (mult ε).Fil) 0,
      Subsingleton.elim (LinearEquiv.ofSubsingleton _ _ _ : (mult ε).Fil) 0]
    simp
  lie_act a m := by
    have h : ∀ x, (padicAction (PDivGroup.mu p O)).onLie a x = padicToO p O a • x := fun x => by
      change lieMap _ _ (algebraMap ℤ_[p] (CategoryTheory.End (PDivGroup.mu p O)) a) x = _
      rw [Algebra.algebraMap_eq_smul_one]
      exact (LinearMap.congr_fun (lieMap_smul (padicToO p O) a
        (CategoryTheory.CategoryStruct.id _)) x).trans (by simp)
    rw [h, ← map_smul, ← map_smul]
    congr 2
    ext i
    simp [actH, mult, Matrix.mulVec, dotProduct, Subsingleton.elim i 0, padicToO,
      Matrix.algebraMap_matrix_apply]
  al_eq t := by
    have h : fontaineTheta O p (Sandwich.mu ε) = 0 := by
      rw [Sandwich.mu, map_sub, fontaineTheta_teichmuller, map_one, sub_eq_zero]
      exact hε.zeta_zero
    rw [Subsingleton.elim (LinearEquiv.ofSubsingleton _ _ _ : (mult ε).Fil) 0]
    ext i
    simp [Datum.al, mult, Matrix.mulVec, dotProduct, h]
  b_eq x χ := by
    obtain ⟨q, rfl⟩ := (muLie ε).surjective x
    obtain ⟨m, rfl⟩ := (mult ε).Fil.mkQ_surjective q
    have he : (muBasis hε).symm (Pi.single 0 1) = epsTate hε := by
      simp only [muBasis, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
      exact one_smul ℤ_[p] (epsTate hε)
    set a := epsPairing hε (PDivGroup.mu p O) (epsTate hε) χ with ha
    have hχ : χ = a • constGen p O := by
      refine ((PDivGroup.mu p O).pairing_flip_bijective C).1 (LinearMap.ext fun t => ?_)
      obtain ⟨c, rfl⟩ := (epsEquiv hε).surjective t
      change pairing _ O (c • epsTate hε) χ = pairing _ O (c • epsTate hε) (a • constGen p O)
      rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, ← epsPairing_smul hε,
        pairing_apply _ (constGen p O), charHom_constGen, tateMap_id]
    rw [LinearEquiv.symm_apply_apply, ← dlog_eq_omegaMap]
    conv_rhs => rw [hχ, dlog_smul (padicToO p O), dlog_constGen, map_smul, muLie_mk]
    have hb : bQuot (mult ε) ((mult ε).Fil.mkQ m) = m := mult_bb m
    rw [hb, pairingO, Fin.sum_univ_one, he, ← ha]
    simp [mul_comm]

end Inhabitant

section Guards

variable {p : ℕ} [Fact p.Prime] {C : Type} [NormedField C] [NormedAlgebra ℚ_[p] C]
  {O : Type} [CommRing O] [Algebra O C]

theorem norm_p : ‖(p : C)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] C), norm_algebraMap', Padic.norm_p]

theorem IsIntegers.pow_dvd_iff (H : IsIntegers O C) (n : ℕ) (a : O) :
    (p : O) ^ n ∣ a ↔ ‖algebraMap O C a‖ ≤ (p : ℝ)⁻¹ ^ n := by
  have hp : (0 : ℝ) < (p : ℝ)⁻¹ ^ n := by have := (Fact.out : p.Prime).pos; positivity
  have hn : ‖(p : C) ^ n‖ = (p : ℝ)⁻¹ ^ n := by rw [norm_pow, norm_p]
  have h0 : (p : C) ^ n ≠ 0 := by rw [← norm_pos_iff, hn]; exact hp
  constructor
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_pow, map_natCast, norm_mul, hn]
    exact mul_le_of_le_one_right hp.le ((H.mem_iff _).1 ⟨b, rfl⟩)
  · intro h
    obtain ⟨b, hb⟩ := (H.mem_iff (algebraMap O C a / (p : C) ^ n)).2
      (by rw [norm_div, hn, div_le_one hp]; exact h)
    refine ⟨b, H.inj ?_⟩
    rw [map_mul, map_pow, map_natCast, hb, mul_div_cancel₀ _ h0]

theorem IsIntegers.not_isUnit (H : IsIntegers O C) : ¬IsUnit (p : O) := fun h => by
  have h1 := (H.pow_dvd_iff (p := p) 1 1).1 (by rw [pow_one]; exact h.dvd)
  rw [map_one, norm_one, pow_one] at h1
  have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact absurd (inv_lt_one_of_one_lt₀ this) (not_lt.2 h1)

theorem IsIntegers.isAdicComplete [CompleteSpace C] (H : IsIntegers O C) :
    IsAdicComplete (span {(p : O)}) O := by
  have hm : ∀ (n : ℕ) (a b : O), a ≡ b [SMOD (span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔
      ‖algebraMap O C a - algebraMap O C b‖ ≤ (p : ℝ)⁻¹ ^ n := fun n a b => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, H.pow_dvd_iff, map_sub]
  have h1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have ht : Filter.Tendsto (fun n : ℕ => (p : ℝ)⁻¹ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ h1)
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · have h2 : ‖algebraMap O C x - algebraMap O C 0‖ ≤ 0 :=
      ge_of_tendsto' ht fun n => (hm n x 0).1 (hx n)
    exact H.inj (sub_eq_zero.1 (norm_le_zero_iff.1 h2))
  · have hc : CauchySeq fun n => algebraMap O C (f n) :=
      cauchySeq_of_le_tendsto_0' _ (fun n m hnm => by
        rw [dist_eq_norm]; exact (hm n _ _).1 (hf hnm)) ht
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    obtain ⟨l, rfl⟩ := (H.mem_iff L).2
      (le_of_tendsto' hL.norm fun n => (H.mem_iff _).1 ⟨f n, rfl⟩)
    refine ⟨l, fun n => (hm n _ _).2 ?_⟩
    refine le_of_tendsto (hL.const_sub (algebraMap O C (f n))).norm ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm' using (hm n _ _).1 (hf hm')

end Guards

example (p : ℕ) [Fact p.Prime] : IsIntegers 𝓞_ℂ_[p] ℂ_[p] :=
  have key : ∀ x : ℂ_[p], x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := fun x => by
    rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff).symm
  ⟨Subtype.val_injective, fun x => ⟨fun ⟨a, ha⟩ => ha ▸ (key _).1 a.2,
    fun h => ⟨⟨x, (key x).2 h⟩, rfl⟩⟩⟩

example (p : ℕ) [Fact p.Prime] : CompleteSpace ℂ_[p] ∧ IsAlgClosed ℂ_[p] ∧
    Nonempty (NormedAlgebra ℚ_[p] ℂ_[p]) := ⟨inferInstance, inferInstance, ⟨inferInstance⟩⟩

end GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta
