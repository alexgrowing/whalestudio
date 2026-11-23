import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.HatDescent

variable {l : ℕ} [Fact l.Prime]

theorem aDp_ev_eis_mul_eq_zero {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (y : Per.BdRp l)
    (hy : GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) * y = 0) : y = 0 := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)} := by
    rw [ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hxi
  refine (GlobalTheory.MemLoc.filtration_eq_xi_pow l ε hE).2.1 y ?_
  rw [← hc, map_mul, mul_assoc, hy, mul_zero]

theorem eis_pow_dvd_of_aDp_mem {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (n : ℕ)
    (x : (Wq l a)⟦X⟧)
    (h : GlobalTheory.MemLoc.aDp l (ϖ.ev a x) ∈ Ideal.span {GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) ^ n}) :
    eis l a e ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    have h1 : Per.θ l (ϖ.ev a x) = 0 := by
      have h2 := congrArg (Per.θD l) hc
      rw [map_mul, map_pow, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1,
        (ϖ.theta_ev_eq_zero_iff a _).2 dvd_rfl] at h2
      exact Subtype.ext (h2.symm.trans (by simp))
    obtain ⟨x', rfl⟩ := (ϖ.theta_ev_eq_zero_iff a x).1 h1
    have h2 : GlobalTheory.MemLoc.aDp l (ϖ.ev a x') ∈
        Ideal.span {GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) ^ n} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨c, ?_⟩
      rw [← sub_eq_zero]
      apply aDp_ev_eis_mul_eq_zero (a := a) ϖ
      rw [map_mul, map_mul] at hc
      rw [mul_sub, ← hc]
      ring
    obtain ⟨z, hz⟩ := ih x' h2
    exact ⟨z, by rw [hz, pow_succ']; ring⟩

end GlobalTheory.BKReal.HatDescent

namespace GlobalTheory.BKReal.HatDescent

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

def crdB {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) : OD l O →ₗ[ℤ_[l]] Per.BdRp l :=
  TensorProduct.lid ℤ_[l] (Per.BdRp l) ∘ₗ (b.coord j).rTensor (Per.BdRp l)

theorem crdB_tmul {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) (o : O) (β : Per.BdRp l) :
    crdB b j (o ⊗ₜ β) = b.coord j o • β := rfl

theorem crdB_mul {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) (c : Per.BdRp l) (z : OD l O) :
    crdB b j (z * (1 ⊗ₜ c)) = crdB b j z * c := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o β =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, crdB_tmul, crdB_tmul, smul_mul_assoc]
  | add x y hx hy => rw [add_mul, map_add, map_add, hx, hy, add_mul]

theorem crdB_sum {J : Type} [Fintype J] [DecidableEq J] (b : Module.Basis J ℤ_[l] O) (j : J)
    (β : J → Per.BdRp l) : crdB b j (∑ k, b k ⊗ₜ β k) = β j := by
  rw [map_sum, Finset.sum_eq_single j (fun k _ hk => by
    rw [crdB_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp [Finsupp.single_apply, hk])
    (by simp), crdB_tmul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]

variable {a e : ℕ} [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem toAc_eis (t : Wq l a →ₐ[ℤ_[l]] O) : toAc t K (eis l a e) = fun _ => EIn l e (A O K) := by
  have hX : toAc t K X = fun _ => uIn (A O K) :=
    funext fun τ => Subtype.ext ((congrArg (PowerSeries.map _) (PowerSeries.map_X _)).trans
      (PowerSeries.map_X _))
  have hE : EIn l e (A O K) = uIn _ ^ e + (l : A O K) := Subtype.ext (by simp [E])
  rw [eis, map_add, map_pow, hX, map_natCast, hE]
  rfl

theorem exists_of_toOD_iTot_mem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (f : ZMod a → A O K)
    (h : toOD l O (ϖ.iTot t K f) ∈
      Ideal.span {((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) : OD l O) ^ n}) :
    ∃ g : ZMod a → A O K, f = (fun _ => EIn l e (A O K)) ^ n * g := by
  classical
  set b := Module.Free.chooseBasis ℤ_[l] O
  obtain ⟨x, rfl⟩ := exists_eq_sum_toAc t K b f
  have hT : toOD l O (ϖ.iTot t K (∑ j, b j • toAc t K (x j))) =
      ∑ j, b j ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (x j)) := by
    simp only [map_sum, map_smul, PiSys.iTot_toAc]
    refine Finset.sum_congr rfl fun j _ => ?_
    show b j • ((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (x j))) = _
    rw [smul_tmul', smul_eq_mul, mul_one]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have hx : ∀ j, eis l a e ^ n ∣ x j := fun j => by
    apply eis_pow_dvd_of_aDp_mem ϖ n
    rw [Ideal.mem_span_singleton']
    refine ⟨crdB b j z, ?_⟩
    have := congrArg (crdB b j) (hz.trans hT)
    rw [crdB_sum, Algebra.TensorProduct.tmul_pow, one_pow, crdB_mul] at this
    exact this
  choose y hy using hx
  refine ⟨∑ j, b j • toAc t K (y j), ?_⟩
  simp only [hy, map_mul, map_pow, toAc_eis, Finset.mul_sum, mul_smul_comm]

end GlobalTheory.BKReal.HatDescent

namespace GlobalTheory.BKReal.PiSys

open GlobalTheory.BKReal.HatDescent

theorem eq_Ehat_pow_mul_of_iD_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (x : ZMod a → Ahat O K l e),
    ϖ.iD t K x ∈ Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} →
      ∃ y : ZMod a → Ahat O K l e, x = (fun _ => Ehat O K l e) ^ n * y := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ n x hx
  have hd : ϖ.iD t K (fun _ => Ehat O K l e) =
      (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
    rw [iD, glue_const, Ehat, iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  choose g x' hg using fun τ => exists_eq_algebraMap_add_pow_mul (EIn l e (invL l (A O K))) n (x τ)
  have hsplit : x = (fun τ => ofAl O K l e (g τ)) + (fun _ => Ehat O K l e) ^ n * x' :=
    funext fun τ => hg τ
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (l : A O K)) (S := invL l (A O K)) g
  choose r hr using hm

  have h1 : ϖ.iD t K (fun τ => ofAl O K l e (g τ)) ∈
      Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} := by
    rw [hsplit, map_add, map_mul, map_pow] at hx
    exact (Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))).1 hx
  have h2 : (fun τ => ofA O K l e (r τ)) =
      (fun _ => ofA O K l e ((l : A O K) ^ m)) * fun τ => ofAl O K l e (g τ) := by
    funext τ
    rw [Pi.mul_apply, ofA, RingHom.comp_apply, RingHom.comp_apply, hr τ, Algebra.smul_def, map_mul]
  have h3 : toOD l O (ϖ.iTot t K r) ∈
      Ideal.span {((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) : OD l O) ^ n} := by
    rw [← iD_ofA, h2, map_mul, ← hd]
    exact Ideal.mul_mem_left _ _ h1
  obtain ⟨h, hh⟩ := exists_of_toOD_iTot_mem t ϖ n r h3
  have hu : IsUnit (algebraMap (A O K) (invL l (A O K)) (l : A O K)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hEA : algebraMap (A O K) (invL l (A O K)) (EIn l e (A O K)) = EIn l e (invL l (A O K)) := rfl
  have hgτ : ∀ τ, g τ = EIn l e (invL l (A O K)) ^ n *
      (algebraMap (A O K) (invL l (A O K)) (h τ) * ↑(hu.unit⁻¹ ^ m)) := fun τ => by
    have h4 : algebraMap (A O K) (invL l (A O K)) (l : A O K) ^ m * g τ =
        EIn l e (invL l (A O K)) ^ n * algebraMap (A O K) (invL l (A O K)) (h τ) := by
      have h5 := (hr τ).symm
      rw [Algebra.smul_def, hh, Pi.mul_apply, Pi.pow_apply] at h5
      simp only [map_mul, map_pow, hEA] at h5
      exact h5
    have hone : (↑(hu.unit⁻¹ ^ m) : invL l (A O K)) * algebraMap (A O K) (invL l (A O K)) (l : A O K) ^ m = 1 := by
      rw [Units.val_pow_eq_pow_val, ← mul_pow, hu.val_inv_mul, one_pow]
    linear_combination (-(g τ)) * hone + (↑(hu.unit⁻¹ ^ m) : invL l (A O K)) * h4
  refine ⟨fun τ => ofAl O K l e (algebraMap (A O K) (invL l (A O K)) (h τ) * ↑(hu.unit⁻¹ ^ m)) + x' τ, ?_⟩
  funext τ
  rw [hg τ, Pi.mul_apply, Pi.pow_apply, hgτ τ, map_mul, map_pow, mul_add]
  rfl

end GlobalTheory.BKReal.PiSys
