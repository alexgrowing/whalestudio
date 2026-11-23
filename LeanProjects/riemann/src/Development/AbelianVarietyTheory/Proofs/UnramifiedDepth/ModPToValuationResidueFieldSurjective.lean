import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WdAinf

open WittVector Ideal

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

abbrev WRing (ϖ : PreTilt O p) := Ainf.A p O ⧸ span {(p : Ainf.A p O) ^ 2, teichmuller p ϖ}

lemma mk_teich (ϖ : PreTilt O p) :
    Ideal.Quotient.mk (span {(p : Ainf.A p O) ^ 2, teichmuller p ϖ}) (teichmuller p ϖ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))

lemma p_sq (ϖ : PreTilt O p) : (p : WRing p O ϖ) ^ 2 = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : Ainf.A p O) ^ 2, teichmuller p ϖ})), ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))

lemma modP_valuationIntegers_prime_eq_zero : (p : Ainf.Rn p O 0) = 0 := by
  have h := Ainf.hpRn p O 0
  exact (pow_one _).symm.trans h

def piW (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) : WRing p O ϖ →+* Ainf.Rn p O 0 :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (span {(p : O) ^ (0 + 1)})).comp (fontaineTheta O p))
    (fun a ha => by
      obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.1 ha
      simp only [RingHom.comp_apply, map_add, map_mul, map_pow, map_natCast,
        fontaineTheta_teichmuller, hϖ, modP_valuationIntegers_prime_eq_zero]
      simp)

lemma piW_mk (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) (a : Ainf.A p O) :
    piW p O ϖ hϖ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (fontaineTheta O p a) := rfl

lemma piW_surj (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) :
    Function.Surjective (piW p O ϖ hϖ) := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, rfl⟩ := Ainf.theta_surj p O hv b
  exact ⟨_, piW_mk p O ϖ hϖ a⟩

lemma ker_piW (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) :
    RingHom.ker (piW p O ϖ hϖ) = span {(p : WRing p O ϖ)} := by
  obtain ⟨-, -, hK, -, -, -⟩ := a0 p C v O hv
  have h3 := (hK ϖ hϖ).2.2
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hx
    rw [RingHom.mem_ker, piW_mk, Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at hx
    have ha : a ∈ RingHom.ker ((Ideal.Quotient.mk (span {(p : O)})).comp (fontaineTheta O p)) := by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]; exact hx
    rw [h3] at ha
    obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.1 ha
    refine Ideal.mem_span_singleton'.2 ⟨Ideal.Quotient.mk _ b, ?_⟩
    simp only [map_add, map_mul, map_natCast, mk_teich, mul_zero, add_zero]
  · intro hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
    rw [RingHom.mem_ker, ← hy, map_mul, map_natCast, modP_valuationIntegers_prime_eq_zero, mul_zero]

lemma W_local (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) :
    IsLocalRing (WRing p O ϖ) := by
  haveI := Ainf.Rn_local p O hv 0
  refine Ainf.local_of_surj_sq (piW p O ϖ hϖ) (piW_surj p O hv ϖ hϖ) ?_
  intro k hk
  rw [ker_piW p O hv ϖ hϖ] at hk
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hk
  rw [show y * (p : WRing p O ϖ) * (y * p) = y * y * (p : WRing p O ϖ) ^ 2 by ring, p_sq, mul_zero]

lemma ann_p (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) (a : WRing p O ϖ) :
    (p : WRing p O ϖ) * a = 0 ↔ piW p O ϖ hϖ a = 0 := by
  obtain ⟨-, -, -, -, -, hF⟩ := a0 p C v O hv
  rw [← RingHom.mem_ker (f := piW p O ϖ hϖ), ker_piW p O hv ϖ hϖ]
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := (hF ϖ hϖ).2.2.1 a h
    exact Ideal.mem_span_singleton'.2 ⟨y, mul_comm _ _⟩
  · intro h
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 h
    rw [show (p : WRing p O ϖ) * (y * p) = y * (p : WRing p O ϖ) ^ 2 by ring, p_sq, mul_zero]

lemma pow_mem_of_nonunit (hv : v.Integers O) (x : O) (hx : ¬IsUnit x) :
    ∃ n : ℕ, (p : O) ∣ x ^ n := by
  have h1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) (fun e => hx (hv.isUnit_of_one' e))
  have h2 : 0 < v (p : C) :=
    pos_iff_ne_zero.2 fun h => Nat.cast_ne_zero.2 hp.out.ne_zero ((Valuation.zero_iff v).1 h)
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one h2 h1
  refine ⟨n, hv.dvd_of_le ?_⟩
  rw [map_pow, map_pow, map_natCast]
  exact hn.le

abbrev ResK (hv : v.Integers O) : Type :=
  haveI := Ainf.O_local O hv
  ResidueField O

def resO (hv : v.Integers O) : O →+* ResK O hv :=
  haveI := Ainf.O_local O hv
  residue O

lemma resO_surj (hv : v.Integers O) : Function.Surjective (resO O hv) :=
  haveI := Ainf.O_local O hv
  residue_surjective

lemma resO_eq_zero (hv : v.Integers O) (x : O) : resO O hv x = 0 ↔ ¬IsUnit x :=
  haveI := Ainf.O_local O hv
  (residue_eq_zero_iff x).trans ((mem_maximalIdeal x).trans mem_nonunits_iff)

def rho1 (hv : v.Integers O) : Ainf.Rn p O 0 →+* ResK O hv :=
  Ideal.Quotient.lift _ (resO O hv) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [zero_add, pow_one, map_mul, (resO_eq_zero O hv (p : O)).2 Fact.out, mul_zero])

lemma modPToValuationResidueField_surjective (hv : v.Integers O) : Function.Surjective (rho1 p O hv) := by
  intro y
  obtain ⟨a, rfl⟩ := resO_surj O hv y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

lemma nil_ker (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) (w : WRing p O ϖ)
    (hw : rho1 p O hv (piW p O ϖ hϖ w) = 0) : IsNilpotent w := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective w
  have h1 : resO O hv (fontaineTheta O p a) = 0 := hw
  obtain ⟨n, c, hc⟩ := pow_mem_of_nonunit p O hv _ ((resO_eq_zero O hv _).1 h1)
  have h2 : (Ideal.Quotient.mk _ a : WRing p O ϖ) ^ n ∈ RingHom.ker (piW p O ϖ hϖ) := by
    rw [RingHom.mem_ker, map_pow, piW_mk, ← map_pow, hc, map_mul, map_natCast, modP_valuationIntegers_prime_eq_zero, zero_mul]
  rw [ker_piW p O hv ϖ hϖ] at h2
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
  refine ⟨n * 2, ?_⟩
  rw [pow_mul, ← hy, mul_pow, p_sq, mul_zero]

variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
  (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O))
include hv hε hϖ

lemma xi_img : ∃ u : (Ainf.A p O)ˣ,
    (Ideal.Quotient.mk _ (Ainf.xi p O ε) : WRing p O ϖ) =
      (p : WRing p O ϖ) * (Ideal.Quotient.mk _ (u : Ainf.A p O) : WRing p O ϖ) := by
  obtain ⟨-, -, -, hX, -, -⟩ := a0 p C v O hv
  obtain ⟨u, hu⟩ := ((hX ε hv hε).2.2.2 ϖ hϖ).2
  refine ⟨u, ?_⟩
  have hu' : Ainf.xi p O ε = u * ((p : Ainf.A p O) - teichmuller p ϖ) := hu
  rw [hu', map_mul, map_sub, map_natCast, mk_teich, sub_zero, mul_comm]

def toW : Ainf.R0 p O ε →+* WRing p O ϖ :=
  Ideal.Quotient.lift _ (Ideal.Quotient.mk _) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨u, hu⟩ := xi_img p O hv ε hε ϖ hϖ
    rw [map_mul, map_pow, hu, mul_pow, p_sq, zero_mul, mul_zero])

def psiW : Ainf.R'n p O ε 1 →+* WRing p O ϖ :=
  Ideal.Quotient.lift _ (toW p O hv ε hε ϖ hϖ) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast, show (1 + 1 : ℕ) = 2 from rfl, p_sq, mul_zero])

lemma psiW_surj : Function.Surjective (psiW p O hv ε hε ϖ hϖ) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a), rfl⟩

def LW : LAlg (Ainf.R0 p O ε) :=
  { carrier := WRing p O ϖ, alg := (toW p O hv ε hε ϖ hϖ).toAlgebra, loc := W_local p O hv ϖ hϖ }

omit hϖ in

def LK : LAlg (Ainf.R0 p O ε) :=
  { carrier := ResK O hv, alg := ((resO O hv).comp (Ainf.thetaBar p O hv ε hε)).toAlgebra }

def piWL : LHom (LW p O hv ε hε ϖ hϖ) ((Ainf.ainfTowerL p O hv ε hε).R 0) :=
  ⟨{ toRingHom := piW p O ϖ hϖ
     commutes' := fun r => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      rfl },
    TowerExample.isLocalHom_of_surj _ (piW_surj p O hv ϖ hϖ)⟩

omit hϖ in

def rho1L : LHom ((Ainf.ainfTowerL p O hv ε hε).R 0) (LK p O hv ε hε) :=
  ⟨{ toRingHom := rho1 p O hv
     commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (modPToValuationResidueField_surjective p O hv)⟩

def psiL : LHom ((Ainf.ainfTowerL p O hv ε hε).R' 1) (LW p O hv ε hε ϖ hϖ) :=
  ⟨{ toRingHom := psiW p O hv ε hε ϖ hϖ
     commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (psiW_surj p O hv ε hε ϖ hϖ)⟩

omit hϖ in
lemma thetaBar_surj : Function.Surjective (Ainf.thetaBar p O hv ε hε) := by
  intro y
  obtain ⟨a, rfl⟩ := Ainf.theta_surj p O hv y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

omit hϖ in
lemma ainf_thetaQuotRing_isLocalRing : IsLocalRing (Ainf.R0 p O ε) := by
  haveI := Ainf.O_local O hv
  refine Ainf.local_of_surj_sq (Ainf.thetaBar p O hv ε hε) (thetaBar_surj p O hv ε hε) ?_
  intro k hk
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective k
  have ha : a ∈ RingHom.ker (fontaineTheta O p) := hk
  rw [Ainf.ker_theta p O hv ε hε] at ha
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton'.2 ⟨y * y, by ring⟩

omit hϖ in
lemma LK_localHom : IsLocalHom (algebraMap (Ainf.R0 p O ε) (LK p O hv ε hε : Type)) := by
  haveI := ainf_thetaQuotRing_isLocalRing p O hv ε hε
  exact IsLocalHom.of_surjective _ ((resO_surj O hv).comp (thetaBar_surj p O hv ε hε))

omit hϖ in
lemma LK_max : maximalIdeal (LK p O hv ε hε : Type) = ⊥ :=
  maximalIdeal_eq_bot (R := ResK O hv)

end GlobalTheory.WdAinf

namespace GlobalTheory

theorem wData_ainfTower_exists :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (ϖ : PreTilt O p), ϖ.untilt = (p : O) →
    ∀ (W : Type) [CommRing W] (pr : Ainf.A p O →+* W), Function.Surjective pr →
    RingHom.ker pr = Ideal.span {(p : Ainf.A p O) ^ 2, WittVector.teichmuller p ϖ} →
    (∀ w : W, ∃ c : PreTilt O p, ∃ c' : W, w = pr (WittVector.teichmuller p c) + p * c') ∧
    (∀ (n : ℕ) (a : Fin n → PreTilt O p), ∑ j, pr (WittVector.teichmuller p (a j)) = pr (WittVector.teichmuller p (∑ j, a j)) +
      p * pr (WittVector.teichmuller p (MvPolynomial.eval₂ (Int.castRingHom (PreTilt O p)) (fun j => (frobeniusEquiv (PreTilt O p) p).symm (a j)) (wS p n)))) ∧
    (∀ c : PreTilt O p, WittVector.fontaineTheta O p (WittVector.teichmuller p c) ∈ Ideal.span {(p : O)} → pr (WittVector.teichmuller p c) = 0)) →
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p),
    ∃ (K : LAlg (Ainf.R0 p O ε)) (wd : WData (Ainf.ainfTowerL p O hv ε hε) K), IsNilOver wd.ρW ∧ maximalIdeal (K : Type) = ⊥ ∧
      IsLocalHom (algebraMap (Ainf.R0 p O ε) (K : Type))) := by
  intro H p _ C _ _ _ v O _ _ _ _ hv ε hε
  obtain ⟨⟨ϖ, hϖ⟩, -⟩ := a0 p C v O hv
  obtain ⟨h1, h2, h3⟩ := H p O hv ε hε ϖ hϖ (WdAinf.WRing p O ϖ) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective Ideal.mk_ker
  obtain ⟨u, hu⟩ := WdAinf.xi_img p O hv ε hε ϖ hϖ
  refine ⟨WdAinf.LK p O hv ε hε,
    { W := WdAinf.LW p O hv ε hε ϖ hϖ
      ρW := (WdAinf.rho1L p O hv ε hε).comp (WdAinf.piWL p O hv ε hε ϖ hϖ)
      ρ1 := WdAinf.rho1L p O hv ε hε
      ψ := WdAinf.psiL p O hv ε hε ϖ hϖ
      πW := WdAinf.piWL p O hv ε hε ϖ hϖ
      πW_surj := WdAinf.piW_surj p O hv ϖ hϖ
      ρW_eq := rfl
      p_sq := WdAinf.p_sq p O ϖ
      ker_πW := WdAinf.ker_piW p O hv ϖ hϖ
      ann_p := WdAinf.ann_p p O hv ϖ hϖ
      compat := fun a => by
        obtain ⟨a0, rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨a1, rfl⟩ := Ideal.Quotient.mk_surjective a0
        rfl
      b := Units.map (Ideal.Quotient.mk (Ideal.span {(p : Ainf.A p O) ^ 2,
        WittVector.teichmuller p ϖ})).toMonoidHom u
      ξ_img := hu
      Rb := PreTilt O p
      T := (Ideal.Quotient.mk (Ideal.span {(p : Ainf.A p O) ^ 2,
        WittVector.teichmuller p ϖ})).toMonoidHom.comp (WittVector.teichmuller p)
      decomp := h1
      witt_add := h2
      T_kill := fun c hc => h3 c (by
        have hc' : Ideal.Quotient.mk (Ideal.span {(p : O) ^ (0 + 1)})
          (WittVector.fontaineTheta O p (WittVector.teichmuller p c)) = 0 := hc
        rwa [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at hc') },
    ⟨(WdAinf.modPToValuationResidueField_surjective p O hv).comp (WdAinf.piW_surj p O hv ϖ hϖ),
      fun w hw => WdAinf.nil_ker p O hv ϖ hϖ w hw⟩,
    WdAinf.LK_max p O hv ε hε, WdAinf.LK_localHom p O hv ε hε⟩

end GlobalTheory
