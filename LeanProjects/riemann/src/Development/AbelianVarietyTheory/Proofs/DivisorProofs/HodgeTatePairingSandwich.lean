import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichKernelRangeExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.DetInv.HTKer

theorem sat_of_ker_eq_range {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C] [IsFractionRing O C]
    {h : ℕ} (a b : Matrix (Fin h) (Fin h) O)
    (H : LinearMap.ker (toLin' (a.map (algebraMap O C))) = LinearMap.range (toLin' (b.map (algebraMap O C))))
    (y : Fin h → O) : toLin' a y = 0 ↔ ∃ c : O, c ≠ 0 ∧ ∃ m, c • y = toLin' b m := by
  have inj : Function.Injective (algebraMap O C) := IsFractionRing.injective O C
  have key : ∀ (X : Matrix (Fin h) (Fin h) O) (z : Fin h → O),
      toLin' (X.map (algebraMap O C)) (fun i => algebraMap O C (z i)) = fun i => algebraMap O C (toLin' X z i) := by
    intro X z
    funext i
    simp [toLin'_apply, mulVec, dotProduct]
  constructor
  · intro hy
    have h1 : (fun i => algebraMap O C (y i)) ∈ LinearMap.ker (toLin' (a.map (algebraMap O C))) := by
      rw [LinearMap.mem_ker, key, hy]; funext i; simp
    rw [H] at h1
    obtain ⟨z, hz⟩ := h1
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) z
    choose m hm using hc
    refine ⟨c, nonZeroDivisors.ne_zero c.2, m, ?_⟩
    funext i
    apply inj
    have h2 : (fun i => algebraMap O C (m i)) = algebraMap O C c • z := by
      funext j; rw [hm j]; simp [Algebra.smul_def]
    have h3 := congrFun (key b m) i
    rw [h2, map_smul, hz] at h3
    rw [← h3]; simp
  · rintro ⟨c, hc, m, hm⟩
    have h1 : (fun i => algebraMap O C (toLin' b m i)) ∈ LinearMap.ker (toLin' (a.map (algebraMap O C))) := by
      rw [H]; exact ⟨_, key b m⟩
    rw [LinearMap.mem_ker, key, ← hm, map_smul] at h1
    funext i
    have h2 := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, map_eq_zero_iff _ inj, mul_eq_zero] at h2
    exact h2.resolve_left hc

theorem finrank_ker_of_sat {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.IsTorsionFree O M] (a b : M →ₗ[O] M)
    (H : ∀ y, a y = 0 ↔ ∃ c : O, c ≠ 0 ∧ ∃ m, c • y = b m) :
    Module.finrank O (LinearMap.ker a) = Module.finrank O (M ⧸ LinearMap.ker b) := by
  have hle : LinearMap.range b ≤ LinearMap.ker a := by
    rintro _ ⟨m, rfl⟩
    exact (H _).2 ⟨1, one_ne_zero, m, one_smul _ _⟩
  have h1 := Submodule.rank_quotient_add_rank (R := O) ((LinearMap.range b).comap (LinearMap.ker a).subtype)
  have h2 : Module.rank O (LinearMap.ker a ⧸ (LinearMap.range b).comap (LinearMap.ker a).subtype) = 0 := by
    rw [rank_eq_zero_iff_isTorsion]
    intro x
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨c, hc, m, hm⟩ := (H y).1 hy
    refine ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, ?_⟩
    change c • Submodule.mkQ ((LinearMap.range b).comap (LinearMap.ker a).subtype) ⟨y, hy⟩ = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, hm.symm⟩
  rw [h2, zero_add, (Submodule.comapSubtypeEquivOfLe hle).rank_eq, ← (LinearMap.quotKerEquivRange b).rank_eq] at h1
  unfold Module.finrank
  rw [h1]

theorem finrank_dual_ker {O : Type} [CommRing O] [IsDomain O] [ValuationRing O] {h : ℕ}
    (b : (Fin h → O) →ₗ[O] (Fin h → O)) :
    Module.finrank O (Module.Dual O (LinearMap.ker b)) = Module.finrank O (LinearMap.ker b) := by
  have free : ∀ (N : Submodule O (Fin h → O)) [Module.Finite O N], Module.Free O N := by
    intro N _
    have : Module.Flat O N := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
      exact Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance
    exact Module.free_of_flat_of_isLocalRing
  haveI := free (LinearMap.range b)
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective b.rangeRestrict
    (LinearMap.range_rangeRestrict b)
  have hb : ∀ m, b (s (b.rangeRestrict m)) = b m := fun m =>
    congrArg Subtype.val (LinearMap.congr_fun hs (b.rangeRestrict m))
  haveI : Module.Finite O (LinearMap.ker b) := by
    refine Module.Finite.of_surjective
      (LinearMap.codRestrict (LinearMap.ker b) (LinearMap.id - s ∘ₗ b.rangeRestrict) (fun m => by
        simp [hb])) ?_
    rintro ⟨m, hm⟩
    refine ⟨m, Subtype.ext ?_⟩
    have : b.rangeRestrict m = 0 := Subtype.ext hm
    simp [this]
  haveI := free (LinearMap.ker b)
  rw [Module.finrank_linearMap, Module.finrank_self, mul_one]

section
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]

noncomputable def coordO {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) :
    O ⊗[ℤ_[p]] G.Tate ≃ₗ[O] (Fin h → O) :=
  (LinearEquiv.baseChange ℤ_[p] O _ _ e).trans (TensorProduct.piScalarRight ℤ_[p] O O (Fin h))

theorem coordO_tmul {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (c : O) (t : G.Tate) :
    coordO e (c ⊗ₜ t) = c • IndefiniteRowSideFullHecke.EpsilonPairingZeta.toO e t := by
  funext i
  simp [coordO, IndefiniteRowSideFullHecke.EpsilonPairingZeta.toO, Algebra.smul_def, ← padicToO_unique p O (algebraMap ℤ_[p] O), mul_comm]

variable [IsDomain O] {ε : PreTilt O p} {hε : IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε}

omit [Algebra ℤ_[p] O] in
theorem pairingO_add {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (y z : Fin h → O)
    (χ : G.dual.Tate) : IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e (y + z) χ =
      IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e y χ + IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e z χ := by
  simp [IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO, add_mul, Finset.sum_add_distrib]

omit [Algebra ℤ_[p] O] in
theorem pairingO_smul {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (c : O) (y : Fin h → O)
    (χ : G.dual.Tate) : IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e (c • y) χ = c * IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e y χ := by
  simp [IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO, Finset.mul_sum, mul_assoc]

omit [Algebra ℤ_[p] O] in

theorem pairingO_inj {G : PDivGroup p O} (hG : Function.Surjective (G.pairing O).flip) {h : ℕ}
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (y z : Fin h → O)
    (H : ∀ χ, IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e y χ = IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e z χ) : y = z := by
  funext i
  obtain ⟨χ, hχ⟩ := hG ((IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsEquiv hε).toLinearMap ∘ₗ LinearMap.proj i ∘ₗ e.toLinearMap)
  have h1 : ∀ t, IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing hε G t χ = e t i := by
    intro t
    have := LinearMap.congr_fun hχ t
    simp only [LinearMap.flip_apply] at this
    rw [IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing, this]
    simp
  have h2 : ∀ w : Fin h → O, IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e w χ = w i := by
    intro w
    simp only [IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO, h1, LinearEquiv.apply_symm_apply]
    rw [Finset.sum_eq_single i] <;> simp +contextual [Pi.single_apply, eq_comm]
  rw [← h2 y, ← h2 z, H]

variable {u₁ u₂ : Oˣ} {G : PDivGroup p O} {h : ℕ} {D : Datum ε h ℤ_[p]} {e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])}
  {fil : G.dual.omega ≃ₗ[O] D.Fil} {lie : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] G.Lie}

theorem al_coordO (R : IndefiniteRowSideFullHecke.EpsilonPairingZeta.Realizes hε u₁ u₂ G G.padicAction D e fil lie) (x : O ⊗[ℤ_[p]] G.Tate) :
    D.al (coordO e x) = (u₁ : O) • (fil (G.hodgeTateLinear x) : Fin h → O) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c t =>
    rw [coordO_tmul, map_smul, R.al_eq, hodgeTateLinear_tmul, hodgeTate_eq_omegaMap, map_smul,
      Submodule.coe_smul, smul_comm]
  | add x y hx hy => simp only [map_add, hx, hy, Submodule.coe_add, smul_add]

theorem ht_eq_zero_iff (R : IndefiniteRowSideFullHecke.EpsilonPairingZeta.Realizes hε u₁ u₂ G G.padicAction D e fil lie) (x : O ⊗[ℤ_[p]] G.Tate) :
    G.hodgeTateLinear x = 0 ↔ D.al (coordO e x) = 0 := by
  rw [al_coordO R, ← Units.smul_def, smul_eq_zero_iff_eq, Submodule.coe_eq_zero, fil.map_eq_zero_iff]

theorem finrank_ker_ht (R : IndefiniteRowSideFullHecke.EpsilonPairingZeta.Realizes hε u₁ u₂ G G.padicAction D e fil lie)
    (H : ∀ y, D.al y = 0 ↔ ∃ c : O, c ≠ 0 ∧ ∃ m, c • y = D.bb m) :
    Module.finrank O (LinearMap.ker G.hodgeTateLinear) = Module.finrank O G.Lie := by
  rw [← lie.finrank_eq]
  refine Eq.trans ?_ (finrank_ker_of_sat D.al D.bb H)
  refine LinearEquiv.finrank_eq (LinearEquiv.ofSubmodules (coordO e) _ _ ?_)
  ext y
  obtain ⟨x, rfl⟩ := (coordO e).surjective y
  simp [ht_eq_zero_iff R]

omit [Algebra ℤ_[p] O] in
theorem finrank_lie_add [ValuationRing O] (fil : G.dual.omega ≃ₗ[O] D.Fil)
    (lie : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] G.Lie) :
    Module.finrank O G.Lie + Module.finrank O G.dual.Lie = h := by
  have h1 : Module.finrank O G.dual.Lie = Module.finrank O D.Fil :=
    fil.dualMap.finrank_eq.symm.trans (finrank_dual_ker D.bb)
  rw [h1, ← lie.finrank_eq, Submodule.finrank_quotient_add_finrank]
  simp

end

theorem ker_hodgeTateLinear : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ (G : PDivGroup p O) (ζ : (PDivGroup.mu p O).Tate) (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]), v.Integers O → Function.Bijective (fun a : ℤ_[p] => a • ζ) → (∀ s χ, pairing G O s χ = B s χ • ζ) → (∀ x : O ⊗[ℤ_[p]] G.Tate, G.hodgeTateLinear x = 0 ↔ ∃ (c : O) (y : G.Lie), c ≠ 0 ∧ ∀ χ, c * (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog (G := G) χ)) ∧ Module.finrank O (LinearMap.ker G.hodgeTateLinear) + Module.finrank O (LinearMap.ker G.dual.hodgeTateLinear) = G.height := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε hS G ζ B hv hζ hB
  obtain ⟨u₁, u₂, hS⟩ := hS
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : ValuationRing O := by
    refine @ValuationRing.mk O _ _ ⟨fun a b => ?_⟩
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inr hc.symm⟩
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inl hc.symm⟩
  have hroot : IsPrimitiveRoot (PreTilt.untilt (root ε)) p := by
    simpa [IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta] using hε 1
  have sat : ∀ {h : ℕ} (D : Datum ε h ℤ_[p]) (y), D.al y = 0 ↔ ∃ c : O, c ≠ 0 ∧ ∃ m, c • y = D.bb m := by
    intro h D y
    refine sat_of_ker_eq_range (C := C) _ _ ?_ y
    have := (ker_bC_eq_range_alC_and_ker_alC_eq_range_bC p C v O hv ε hroot ℤ_[p] h D).2
    simpa only [alC, bC, redC, Matrix.map_map, RingHom.coe_comp] using this
  obtain ⟨D, e, fil, lie, R⟩ := hS G ℤ_[p] G.padicAction
  obtain ⟨D', e', fil', lie', R'⟩ := hS G.dual ℤ_[p] G.dual.padicAction
  refine ⟨fun x => ?_, ?_⟩
  swap
  · rw [finrank_ker_ht R (sat D), finrank_ker_ht R' (sat D')]
    exact finrank_lie_add fil lie
  have hperf : Function.Surjective (G.pairing O).flip :=
    (tate_free_perfect p O C G).2.2.2.2.2.2.2.2

  obtain ⟨w, hw⟩ := hζ.2 (IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsTate hε)
  obtain ⟨w', hw'⟩ := (IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsEquiv hε).surjective ζ
  have hw'' : w' • IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsTate hε = ζ := hw'
  have hww : w' * w = 1 := by
    apply hζ.1
    simp only at hw ⊢
    rw [mul_smul, hw, hw'', one_smul]
  have hBe : ∀ t χ, B t χ = IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing hε G t χ * w := by
    intro t χ
    apply hζ.1
    simp only at hw ⊢
    rw [mul_smul, hw, IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing_smul, hB]
  set W : O := algebraMap ℤ_[p] O w
  set W' : O := algebraMap ℤ_[p] O w'
  have hWW : W' * W = 1 := by rw [← map_mul, hww, map_one]
  have hBO : ∀ (x : O ⊗[ℤ_[p]] G.Tate) χ, (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) =
      W * IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e (coordO e x) χ := by
    intro x χ
    induction x using TensorProduct.induction_on with
    | zero =>
      have := pairingO_smul (hε := hε) e 0 0 χ
      simp only [zero_smul, zero_mul] at this
      simp [this]
    | tmul c t =>
      rw [coordO_tmul, pairingO_smul, IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO_toO, ← padicToO_unique p O (algebraMap ℤ_[p] O)]
      simp only [LinearMap.baseChange_tmul, LinearMap.flip_apply, rid_tmul, hBe, Algebra.smul_def, map_mul, W]
      ring
    | add x y hx hy => simp only [map_add, hx, hy, pairingO_add, mul_add]
  have hb : ∀ (m : Fin G.height → O) χ, IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e (D.bb m) χ =
      u₂ * lie (D.Fil.mkQ m) (dlog (G := G) χ) := by
    intro m χ
    rw [dlog_eq_omegaMap, ← R.b_eq, LinearEquiv.symm_apply_apply]
    rfl
  rw [ht_eq_zero_iff R, sat]
  constructor
  · rintro ⟨c, hc, m, hm⟩
    refine ⟨c, (W * u₂) • lie (D.Fil.mkQ m), hc, fun χ => ?_⟩
    rw [hBO, LinearMap.smul_apply, smul_eq_mul, mul_assoc, ← hb, ← hm, pairingO_smul]
    ring
  · rintro ⟨c, y, hc, hy⟩
    obtain ⟨m, hm⟩ := D.Fil.mkQ_surjective (lie.symm y)
    refine ⟨c * W * u₂, ?_, m, pairingO_inj (hε := hε) hperf e _ _ fun χ => ?_⟩
    · exact mul_ne_zero (mul_ne_zero hc (right_ne_zero_of_mul_eq_one hWW)) u₂.ne_zero
    · rw [hb, hm, LinearEquiv.apply_symm_apply, ← hy, hBO, pairingO_smul]
      ring

end GlobalTheory.DetInv.HTKer
