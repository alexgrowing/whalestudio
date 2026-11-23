import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSupportBoundedDenominators
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology

namespace GlobalTheory.CoefFinPer

theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' φ) =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • GlobalTheory.WeilM.schr ψ (w + w') φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h

theorem schr_sandwich {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) (ha : GlobalTheory.WeilM.schr ψ a φ = φ) :
    GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ w φ) = GlobalTheory.WeilM.schr ψ (a + w + a) φ := by
  rw [schr_schr', ← congrArg (GlobalTheory.WeilM.schr ψ (a + w)) ha, schr_schr', smul_smul, ← AddChar.map_add_eq_mul]
  have : ⅟(2 : R) * (a.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ a.2) + ⅟(2 : R) * ((a + w).1 ⬝ᵥ a.2 - a.1 ⬝ᵥ (a + w).2) = 0 := by
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    ring
  rw [this, AddChar.map_zero_eq_one, one_smul]

theorem conj_eq_neg {G : Type} [AddCommGroup G] (ψ : AddChar G ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) (t : G) :
    starRingEnd ℂ (ψ t) = ψ (-t) := by
  have h1 : ψ t * starRingEnd ℂ (ψ t) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ t]; simp
  have h2 : ψ t * ψ (-t) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hne : ψ t ≠ 0 := by intro h; rw [h, zero_mul] at h2; exact zero_ne_one h2
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem coef_transl_fin : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ Mo : AddSubgroup (κ → Af F), IsOpen (Mo : Set (κ → Af F)) ∧
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ w l : (κ → AF F) × (κ → AF F), (∀ i, (l.1 i).1 = 0 ∧ (l.2 i).1 = 0) →
        (fun i => (l.1 i).2) ∈ Mo → (fun i => (l.2 i).2) ∈ Mo →
        @MeasureTheory.integral _ ℂ _ _ (borel _) μ (fun x => Φ x * starRingEnd ℂ (GlobalTheory.WeilM.schr ψ (w + l) Φ x)) =
          @MeasureTheory.integral _ ℂ _ _ (borel _) μ (fun x => Φ x * starRingEnd ℂ (GlobalTheory.WeilM.schr ψ w Φ x)) := by
  intro F _ _ κ _ ψ hψ Φ hΦ
  obtain ⟨N, hN, hfix⟩ := GlobalTheory.FinSuppHeis.heis_fix_finDiv F κ ψ hψ.1 Φ hΦ
  have h2N : (2 * (N : F)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast (by omega : N ≠ 0))
  set c : Af F := algebraMap F (Af F) ((2 * (N : F))⁻¹) with hc
  set T : Set (Af F) := {a | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} with hT
  let Mo : AddSubgroup (κ → Af F) :=
    { carrier := {y | ∀ i, c * y i ∈ T}
      zero_mem' := by
        intro i v
        simp only [Pi.zero_apply, mul_zero]
        exact (v.adicCompletionIntegers F).zero_mem
      add_mem' := by
        intro y z hy hz i v
        simp only [Pi.add_apply, mul_add]
        exact add_mem (hy i v) (hz i v)
      neg_mem' := by
        intro y hy i v
        simp only [Pi.neg_apply, mul_neg]
        exact neg_mem (hy i v) }
  refine ⟨Mo, ?_, ?_⟩
  · show IsOpen {y : κ → Af F | ∀ i, c * y i ∈ T}
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      GlobalTheory.SuppDen.isOpen_integral.preimage (continuous_const.mul (continuous_apply i))
  intro μ hμ w l hl hl1 hl2
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  have hdiv : ∀ z : AF F, z.1 = 0 → c * z.2 ∈ T →
      (⅟(2 : AF F) * z).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (⅟(2 : AF F) * z) := by
    intro z hz1 hz2
    refine ⟨by show (⅟(2 : AF F)).1 * z.1 = 0; rw [hz1, mul_zero], fun v => ⟨(c * z.2) v, hz2 v, ?_⟩⟩
    have hev : ∀ y : AF F, evFin F v y = evalV F v y.2 := fun y => rfl
    have e1 : z.2 = algebraMap F (Af F) (2 * (N : F)) * (c * z.2) := by
      rw [hc, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h2N, map_one, one_mul]
    have e2 : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
      rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
    have e4 : evalV F v z.2 = algebraMap F (Fv F v) (2 * (N : F)) * (c * z.2) v := by
      conv_lhs => rw [e1]
      rw [map_mul, AlgHom.commutes]
      rfl
    rw [map_mul, hev z, e4, map_mul, map_ofNat, map_natCast]
    linear_combination ((N : Fv F v) * (c * z.2) v) * e2
  have hnegd : ∀ z : AF F, z.1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N z → (-z).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (-z) := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨by show -z.1 = 0; rw [hz1, neg_zero], fun v => ?_⟩
    obtain ⟨b, hb, e⟩ := hz2 v
    exact ⟨-b, neg_mem hb, by rw [map_neg, e, mul_neg]⟩
  set a : (κ → AF F) × (κ → AF F) := (fun i => ⅟(2 : AF F) * l.1 i, fun i => ⅟(2 : AF F) * l.2 i) with ha
  have hA1 : ∀ i, (a.1 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (a.1 i) := fun i => hdiv _ (hl i).1 (hl1 i)
  have hA2 : ∀ i, (a.2 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (a.2 i) := fun i => hdiv _ (hl i).2 (hl2 i)
  have hfixa : GlobalTheory.WeilM.schr ψ a Φ = Φ :=
    hfix a fun i => ⟨(hA1 i).1, (hA1 i).2, (hA2 i).1, (hA2 i).2⟩
  have hfixna : GlobalTheory.WeilM.schr ψ (-a) Φ = Φ :=
    hfix (-a) fun i => ⟨(hnegd _ (hA1 i)).1, (hnegd _ (hA1 i)).2, (hnegd _ (hA2 i)).1, (hnegd _ (hA2 i)).2⟩
  have h2 : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self 2
  have hwl : w + l = a + w + a := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show w.1 i + l.1 i = ⅟(2 : AF F) * l.1 i + w.1 i + ⅟(2 : AF F) * l.1 i
      linear_combination (-(l.1 i)) * h2
    · show w.2 i + l.2 i = ⅟(2 : AF F) * l.2 i + w.2 i + ⅟(2 : AF F) * l.2 i
      linear_combination (-(l.2 i)) * h2
  have hlaw : GlobalTheory.WeilM.schr ψ (w + l) Φ = GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ w Φ) := by
    rw [schr_sandwich ψ a w Φ hfixa, hwl]
  have hpt : ∀ (G : (κ → AF F) → ℂ) x, Φ x * starRingEnd ℂ (GlobalTheory.WeilM.schr ψ a G x) =
      GlobalTheory.WeilM.schr ψ (-a) Φ (a.1 + x) * starRingEnd ℂ (G (a.1 + x)) := by
    intro G x
    simp only [GlobalTheory.WeilM.schr, Prod.fst_neg, Prod.snd_neg, map_mul, conj_eq_neg ψ (GlobalTheory.StdCharFromIsStd.norm_psi hψ)]
    rw [show a.1 + x + -a.1 = x by abel, add_comm x a.1]
    have : -(x ⬝ᵥ a.2 + ⅟(2 : AF F) * (a.1 ⬝ᵥ a.2)) = (a.1 + x) ⬝ᵥ -a.2 + ⅟(2 : AF F) * (-a.1 ⬝ᵥ -a.2) := by
      simp only [add_dotProduct, dotProduct_neg, neg_dotProduct]
      linear_combination (-(a.1 ⬝ᵥ a.2)) * h2
    rw [this]; ring
  rw [hlaw]
  calc ∫ x, Φ x * starRingEnd ℂ (GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ w Φ) x) ∂μ
      = ∫ x, (fun y => GlobalTheory.WeilM.schr ψ (-a) Φ y * starRingEnd ℂ (GlobalTheory.WeilM.schr ψ w Φ y)) (a.1 + x) ∂μ := by
        congr 1; funext x; exact hpt _ x
    _ = ∫ y, GlobalTheory.WeilM.schr ψ (-a) Φ y * starRingEnd ℂ (GlobalTheory.WeilM.schr ψ w Φ y) ∂μ :=
        MeasureTheory.integral_add_left_eq_self (μ := μ) (fun y => GlobalTheory.WeilM.schr ψ (-a) Φ y * starRingEnd ℂ (GlobalTheory.WeilM.schr ψ w Φ y)) a.1
    _ = _ := by rw [hfixna]

end GlobalTheory.CoefFinPer
