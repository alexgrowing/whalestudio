import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsSquareRootCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.DirGPowOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Ws

namespace UpperTheory.V.Cu.RankFourTwistExistence

section SlopeTestRemainingChoices

variable {Γ O : Type} [Group Γ] [TopologicalSpace Γ] [CommRing O] {I : Ideal O} {γ δ : Γ →* Oˣ}

theorem ac_mul (h : AdicCont I fun g => (γ g : O)) (h' : AdicCont I fun g => (δ g : O)) :
    AdicCont I fun g => ((γ * δ) g : O) := fun N => by
  simp only [MonoidHom.mul_apply, Units.val_mul, map_mul]
  exact (h N).mul (h' N)

theorem ac_zpow (h : AdicCont I fun g => (γ g : O)) (n : ℤ) : AdicCont I fun g => ((γ ^ n) g : O) := fun N => by
  have h1 : IsLocallyConstant fun g => Units.map (Ideal.Quotient.mk (I ^ N)).toMonoidHom (γ g) :=
    IsLocallyConstant.desc _ Units.val (h N) Units.val_injective
  have h2 := h1.comp fun u => ((u ^ n : (O ⧸ I ^ N)ˣ) : O ⧸ I ^ N)
  refine (congrArg IsLocallyConstant (funext fun g => ?_)).mp h2
  simp only [Function.comp_apply, MonoidHom.zpow_apply]
  rw [← map_zpow]
  rfl

theorem ac_ker [IsTopologicalGroup Γ] (h : IsOpen (γ.ker : Set Γ)) : AdicCont I fun g => (γ g : O) := fun N => by
  rw [IsLocallyConstant.iff_exists_open]
  refine fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' γ.ker, h.preimage (continuous_const_mul _), by simp, fun y hy => ?_⟩
  have h1 : γ (x⁻¹ * y) = 1 := hy
  beta_reduce
  rw [← mul_inv_cancel_left x y, map_mul γ, h1, mul_one]

end SlopeTestRemainingChoices

noncomputable def rd {l : ℕ} [Fact l.Prime] (c : Coef l) : c.Oˣ →* (ResidueField c.O)ˣ :=
  Units.map (residue c.O).toMonoidHom

theorem eq_of_rd {l : ℕ} [Fact l.Prime] {c : Coef l} {x y : c.Oˣ} {m : ℕ} (hm : l.Coprime m) (hx : x ^ m = 1)
    (hy : y ^ m = 1) (h : rd c x = rd c y) : x = y :=
  (congrFacts (AlgebraicClosure ℚ) l c).2.2.2.1 x y m ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hm) hx hy
    (Ideal.Quotient.eq.1 (congrArg Units.val h))

theorem grpF {M : Type} [CommGroup M] (η ω ξ ψ : M) (e k : ℤ) :
    (η ^ (e + 2 - k)) ^ 2 * ((η ^ 2 * ω) ^ (k - 1) * (ξ * ψ)) =
      η ^ 2 * ω * ω⁻¹ * ξ * ((η ^ 2 * ω) ^ e * ψ) * (ω ^ (k - 1) * (ω ^ e)⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow, ofMul_zpow, ofMul_inv]
  module

theorem grpT {M : Type} [CommGroup M] (η ω ξ ψ : M) (e k : ℤ) :
    (ω ^ e * ψ * η ^ (e + 2 - k)) ^ 2 * ((η ^ 2 * ω) ^ (k - 1) * (ξ * ψ⁻¹)) =
      η ^ 2 * ω * ω⁻¹ * ξ * ((η ^ 2 * ω) ^ e * ψ) * (ω ^ (k - 1) * (ω ^ e)⁻¹) * (ω ^ e) ^ 2 := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow, ofMul_zpow, ofMul_inv]
  module

theorem cancel3 {M : Type} [CommGroup M] {a b d p : M} (h : a * b = d ^ 2 * p) (hb : b = d) : a = d * p := by
  subst hb
  apply mul_right_cancel (b := b)
  rw [h, sq, mul_right_comm]

end UpperTheory.V.Cu.RankFourTwistExistence

open UpperTheory.V.Cu.RankFourTwistExistence in
theorem UpperTheory.V.Cu.twEx4 : UpperTheory.V.Cu.TwEx4 := by
  intro Ω _ _ _ l hl c D T h3 k hk1 hk
  have h : D.Good := h3.1
  obtain ⟨-, he2, -, ⟨mψ, -, hmψ, hψ⟩, -⟩ := UpperTheory.V.Ws.large₂.host3 D h3
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcont, -, homo, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D h
  obtain ⟨mξ, hmξ, hξ⟩ := h.xi_ord
  have hl1 : l.Coprime (l - 1) := (Nat.coprime_self_sub_right hl.out.one_le).2 (Nat.coprime_one_right l)
  set ε := chiO ℚ Ω l c.O with hε
  set μ : G ℚ Ω →* c.Oˣ := D.al * D.ξ ^ (-1 : ℤ) with hμ
  set P : G ℚ Ω →* c.Oˣ := D.om ^ (D.e : ℤ) * D.ψ with hP
  have al_eq : ∀ g, D.al g = ε g * (D.om g)⁻¹ * D.ξ g := fun _ => rfl
  have mu_eq : ∀ g, μ g = ε g * (D.om g)⁻¹ := fun g => by
    rw [hμ, MonoidHom.mul_apply, MonoidHom.zpow_apply, al_eq, zpow_neg_one, mul_inv_cancel_right]
  have charpoly_eq_of_isIso : ∀ g, P g = D.om g ^ D.e * D.ψ g := fun g => by
    rw [hP, MonoidHom.mul_apply, MonoidHom.zpow_apply, zpow_natCast]
  have P_eqz : ∀ g, P g = D.om g ^ (D.e : ℤ) * D.ψ g := fun g => by
    rw [hP, MonoidHom.mul_apply, MonoidHom.zpow_apply]
  have Psi_z : ∀ g, D.Psi g = ε g ^ (D.e : ℤ) * D.ψ g := fun _ => rfl
  have Psi_eq : ∀ g, D.Psi g = μ g ^ D.e * P g := fun g => by
    have : D.Psi g = ε g ^ D.e * D.ψ g := by rw [← zpow_natCast]; rfl
    rw [this, mu_eq, charpoly_eq_of_isIso, mul_pow, inv_pow, mul_assoc, inv_mul_cancel_left]
  have al_eq' : ∀ g, D.al g = μ g * D.ξ g := fun g => by rw [al_eq, mu_eq]
  have th_eq : ∀ g, D.th g = D.al g * D.Psi g := fun _ => rfl
  have rmu : ∀ g, rd c (μ g) = 1 := fun g => by
    have : rd c (D.om g) = rd c (ε g) := Units.ext (h.om_bar g)
    rw [mu_eq, map_mul, map_inv, this, mul_inv_cancel]
  have ral : ∀ g, rd c (D.al g) = rd c (D.ξ g) := fun g => by rw [al_eq', map_mul, rmu, one_mul]
  have rPsi : ∀ g, rd c (D.Psi g) = rd c (P g) := fun g => by rw [Psi_eq, map_mul, map_pow, rmu, one_pow, one_mul]
  have omp : ∀ g, D.om g ^ (l - 1) = 1 := fun g => DFunLike.congr_fun h.om_pow g
  have hM : l.Coprime ((l - 1) * mψ * mξ) := (hl1.mul_right hmψ).mul_right hmξ
  have PM : ∀ g, P g ^ ((l - 1) * mψ * mξ) = 1 := fun g => by
    have h1 : D.ψ g ^ mψ = 1 := DFunLike.congr_fun hψ g
    rw [charpoly_eq_of_isIso, mul_pow, ← pow_mul, mul_comm D.e, mul_assoc, mul_assoc, pow_mul, omp, one_pow, one_mul, mul_assoc, mul_left_comm,
      pow_mul, h1, one_pow]
  have xM : ∀ g, D.ξ g ^ ((l - 1) * mψ * mξ) = 1 := fun g => by
    have h1 : D.ξ g ^ mξ = 1 := DFunLike.congr_fun hξ g
    rw [mul_comm, pow_mul, h1, one_pow]
  have h2 : IsUnit (2 : c.O) := by
    have : IsUnit ((2 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes hl.out Nat.prime_two).2 h.l_odd
    simpa [map_ofNat] using this.map (algebraMap ℤ_[l] c.O)
  obtain ⟨η, η2, ηr, ηc, η1⟩ := UpperTheory.exists_square_root_character c.O h2 (G ℚ Ω) μ (fun g => congrArg Units.val (rmu g))
    (ac_mul (hcont 2) (ac_zpow (ac_ker h.xi_open) _))
  have rη : ∀ g, rd c (η g) = 1 := fun g => Units.ext (ηr g)
  have eps_eq : ∀ g, ε g = η g ^ 2 * D.om g := fun g => by rw [η2, mu_eq, inv_mul_cancel_right]
  have epz : ∀ g, ε g ^ (k - 1) = ε g ^ ((k : ℤ) - 1) := fun g => by
    rw [← zpow_natCast, Nat.cast_sub hk1, Nat.cast_one]
  have hkz : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  have omz : ∀ g, D.om g ^ ((k : ℤ) - 1) = D.om g ^ (D.e : ℤ) := fun g => by
    rw [hkz, zpow_natCast, zpow_natCast]
    exact pow_eq_pow_iff_modEq.2 (hk.of_dvd (orderOf_dvd_of_pow_eq_one (omp g)))
  have om2 : ∀ g, (D.om g ^ (D.e : ℤ)) ^ 2 = 1 := fun g => by
    obtain ⟨n, hn⟩ := he2
    rw [zpow_natCast, ← pow_mul, mul_comm, hn, pow_mul, omp, one_pow]
  set j : ℤ := (D.e : ℤ) + 2 - k with hj
  have hc03 : ∀ g, chi D T.pr 0 g * chi D T.pr 3 g = D.th g := fun g => by
    cases T.pr
    · change D.th g * 1 = D.th g
      rw [mul_one]
    · rfl
  obtain ⟨t, tc, tmul, tred, t1⟩ : ∃ t : G ℚ Ω →* c.Oˣ, AdicCont (maximalIdeal c.O) (fun g => (t g : c.O)) ∧
      (∀ g, (t g * η g ^ j) ^ 2 * UpperTheory.V.Cu.Phi D T.pr k g = D.th g) ∧
      (∀ g, rd c (chi D T.pr 3 g) = rd c (t g)) ∧ ∀ g, P g = 1 → t g = 1 := by
    cases hpr : T.pr
    · refine ⟨1, ac_ker (by rw [MonoidHom.ker_one]; exact isOpen_univ), fun g => ?_, fun g => ?_, fun _ _ => rfl⟩
      · change (1 * η g ^ j) ^ 2 * (ε g ^ (k - 1) * (D.ξ g * D.ψ g)) = ε g * (D.om g)⁻¹ * D.ξ g * (ε g ^ (D.e : ℤ) * D.ψ g)
        rw [one_mul, epz, eps_eq, hj, grpF, omz, mul_inv_cancel, mul_one]
      · rfl
    · refine ⟨P, ac_mul (ac_zpow (ac_ker homo) _) (ac_ker h.psi_open), fun g => ?_, fun g => rPsi g, fun _ h => h⟩
      · change (P g * η g ^ j) ^ 2 * (ε g ^ (k - 1) * (D.ξ g * (D.ψ g)⁻¹)) =
          ε g * (D.om g)⁻¹ * D.ξ g * (ε g ^ (D.e : ℤ) * D.ψ g)
        rw [P_eqz, epz, eps_eq, hj, grpT, omz, mul_inv_cancel, mul_one, om2, mul_one]
  have δ_eq : ∀ g, (t * η ^ j) g = t g * η g ^ j := fun _ => rfl
  have rδ : ∀ g, rd c ((t * η ^ j) g) = rd c (t g) := fun g => by rw [δ_eq, map_mul, map_zpow, rη, one_zpow, mul_one]
  refine ⟨t * η ^ j, ⟨ac_mul tc (ac_zpow ηc j), fun g => ?_, fun g => ?_, fun g => ?_, fun g hg hr => ?_,
    D.om.ker ⊓ D.ψ.ker, j, homo.inter h.psi_open, fun g hg => ?_⟩⟩
  · rw [δ_eq]
    exact tmul g
  · have e0 : chi D T.pr 0 g * chi D T.pr 3 g = (t * η ^ j) g ^ 2 * UpperTheory.V.Cu.Phi D T.pr k g := (hc03 g).trans (tmul g).symm
    have e1 := congrArg (rd c) e0
    rw [map_mul, map_mul, map_pow] at e1
    exact congrArg Units.val (cancel3 e1 ((tred g).trans (rδ g).symm))
  · exact congrArg Units.val ((tred g).trans (rδ g).symm)
  · have hr' : ∀ i, rd c (D.ps i g) = 1 := fun i => Units.ext (by
      have := congrFun (congrFun hr i) i
      change residue c.O (D.ps i g : c.O) = 1
      simpa [Raw.rbar, Raw.r0, diagRep] using this)
    have e1 : ε g = 1 := by rw [hε, chiO, MonoidHom.comp_apply, hg, map_one]
    have o1 : D.om g = 1 := eq_of_rd hl1 (omp g) (one_pow _) (e1 ▸ Units.ext (h.om_bar g))
    have p1 : P g = 1 := eq_of_rd hM (PM g) (one_pow _) (by rw [← rPsi, map_one]; exact hr' 1)
    have x1 : D.ξ g = 1 := eq_of_rd hM (xM g) (one_pow _) (by rw [← ral, map_one]; exact hr' 2)
    have s1 : D.ψ g = 1 := by rw [charpoly_eq_of_isIso, o1, one_pow, one_mul] at p1; exact p1
    refine ⟨?_, ?_⟩
    · rw [δ_eq, t1 g p1, η1 g (by rw [mu_eq, e1, o1, inv_one, mul_one]), one_zpow, mul_one]
    · cases T.pr
      · change D.ξ g * D.ψ g = 1
        rw [x1, s1, mul_one]
      · change D.ξ g * (D.ψ g)⁻¹ = 1
        rw [x1, s1, inv_one, mul_one]
  · have o1 : D.om g = 1 := hg.1
    have o2 : D.ψ g = 1 := hg.2
    rw [← hε, δ_eq, t1 g (by rw [charpoly_eq_of_isIso, o1, o2, one_pow, mul_one]), one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, η2, mu_eq, o1, inv_one, mul_one]
