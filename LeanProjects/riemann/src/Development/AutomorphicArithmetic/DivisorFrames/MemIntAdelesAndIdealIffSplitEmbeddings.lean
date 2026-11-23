import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cpt_incl {D : D7} (Q : Pl D.host.E) (x : D.host.E) :
    cpt (D := D) Q (x ⊗ₜ[D.host.F] 1) = algebraMap D.host.E (Q.adicCompletion D.host.E) x := by
  show (toAd D (x ⊗ₜ[D.host.F] 1)) Q = _
  rw [GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D)]
  rfl

private theorem val_oToS {D : D7} (Q : Pl D.host.E) (a : 𝓞 D.host.E) :
    Valued.v (cpt (D := D) Q (oToS D.host.F D.host.E a : Lev.EAf D)) = Q.intValuation a := by
  have h : (oToS D.host.F D.host.E a : Lev.EAf D) = (a : D.host.E) ⊗ₜ[D.host.F] 1 := rfl
  rw [h, cpt_incl, Formalism.UG.P.levelaf_valued_algebraMap]
  exact Q.valuation_of_algebraMap a

private theorem exists_exact {R : Type} [CommRing R] [IsDedekindDomain R] (Pw : Finset (HeightOneSpectrum R))
    (c : HeightOneSpectrum R → ℕ) :
    ∃ a ∈ ∏ w ∈ Pw, w.asIdeal ^ c w, ∀ w ∈ Pw, w.intValuation a = WithZero.exp (-(c w : ℤ)) := by
  choose x hx hx' using fun w : HeightOneSpectrum R =>
    Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top (c w)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Pw) (fun w => w.asIdeal) (fun w => c w + 1)
    (fun w _ => w.prime) (fun i _ j _ h e => h (HeightOneSpectrum.ext e)) (fun w => x w.1)
  have h1 : ∀ w ∈ Pw, y ∈ w.asIdeal ^ c w := fun w hw => by
    have := add_mem (Ideal.pow_le_pow_right (Nat.le_succ _) (hy w hw)) (hx w)
    rwa [sub_add_cancel] at this
  have h2 : ∀ w ∈ Pw, y ∉ w.asIdeal ^ (c w + 1) := fun w hw h => hx' w (by
    have := sub_mem h (hy w hw)
    rwa [sub_sub_cancel] at this)
  refine ⟨y, ?_, fun w hw => le_antisymm ((w.intValuation_le_pow_iff_mem _ _).2 (h1 w hw)) ?_⟩
  · rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
    · simp only [Ideal.mem_iInf]
      exact h1
    · intro P _ Q _ hPQ
      exact (HeightOneSpectrum.isCoprime_of_ne P Q hPQ).pow
  · have h3 := h2 w hw
    rw [← w.intValuation_le_pow_iff_mem, not_le] at h3
    have h0 : w.intValuation y ≠ 0 := (lt_of_le_of_lt zero_le h3).ne'
    rw [← WithZero.exp_log h0] at h3 ⊢
    rw [WithZero.exp_lt_exp] at h3
    rw [WithZero.exp_le_exp]
    push_cast at h3
    omega

private theorem le_of_mem_map {O S K Γ : Type} [CommRing O] [CommRing S] [CommRing K] [LinearOrderedCommGroupWithZero Γ]
    (f : O →+* S) (φ : S →+* K) (v : Valuation K Γ) (I : Ideal O) (γ : Γ) (h1 : ∀ s, v (φ s) ≤ 1)
    (h2 : ∀ a ∈ I, v (φ (f a)) ≤ γ) : ∀ s ∈ I.map f, v (φ s) ≤ γ := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, ha, rfl⟩ := hs
    exact h2 a ha
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_mul' (h1 a) hx).trans_eq (one_mul _)

private theorem val_le_one {D : D7} (w : Pl D.host.E) (s : OA D) : Valued.v (cpt (D := D) w s.1) ≤ 1 := by
  obtain ⟨s, hs⟩ := s
  have := (mem_OA_iff s).1 hs w
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

private theorem val_le_of_mem {D : D7} (w : Pl D.host.E) (I : Ideal (𝓞 D.host.E)) (γ : WithZero (Multiplicative ℤ))
    (h2 : ∀ a ∈ I, w.intValuation a ≤ γ) (z : Lev.EAf D) (h : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hI : (⟨z, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ idS D.host.F I) : Valued.v (cpt (D := D) w z) ≤ γ := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* w.adicCompletion D.host.E,
      ∀ s, φ s = cpt (D := D) w s.1 := ⟨(cpt (D := D) w).comp (OA D).subtype, fun _ => rfl⟩
  have := le_of_mem_map (oToS D.host.F D.host.E) φ Valued.v I γ
    (fun s => by rw [hφ]; exact val_le_one w s) (fun a ha => by rw [hφ, val_oToS]; exact h2 a ha) ⟨z, h⟩ hI
  rwa [hφ] at this

private theorem inId_iff {D : D7} (Pw : Finset (Pl D.host.E)) (c : Pl D.host.E → ℕ) (z : Lev.EAf D)
    (hz : ∀ Q, Q ∉ Pw → cpt (D := D) Q z = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) z ↔
      ∀ w ∈ Pw, Valued.v (cpt (D := D) w z) ≤ WithZero.exp (-(c w : ℤ)) := by
  constructor
  · rintro ⟨h, hI⟩ w hw
    refine val_le_of_mem w _ _ (fun a ha => ?_) z h hI
    rw [w.intValuation_le_pow_iff_mem]
    exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ c w) hw) ha
  · intro h
    obtain ⟨a, ha, hv⟩ := exists_exact Pw c
    have hy : ((a : D.host.E)⁻¹ ⊗ₜ[D.host.F] 1 : Lev.EAf D) * z ∈ OA D := (mem_OA_iff _).2 fun Q => by
      rw [RingHom.map_mul]
      by_cases hQ : Q ∈ Pw
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, cpt_incl,
          Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀]
        have : Q.valuation D.host.E (a : D.host.E) = WithZero.exp (-(c Q : ℤ)) :=
          (Q.valuation_of_algebraMap a).trans (hv Q hQ)
        rw [this, inv_mul_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero)]
        exact h Q hQ
      · rw [hz Q hQ, mul_zero]
        exact zero_mem _
    have e : z = ((oToS D.host.F D.host.E a * ⟨_, hy⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) := by
      refine cpt_ext fun Q => ?_
      have h : (oToS D.host.F D.host.E a : Lev.EAf D) = (a : D.host.E) ⊗ₜ[D.host.F] 1 := rfl
      rw [Subring.coe_mul, h, RingHom.map_mul, RingHom.map_mul, cpt_incl, cpt_incl]
      by_cases hQ : Q ∈ Pw
      · have h0 : (a : D.host.E) ≠ 0 := by
          intro h0
          have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
          have := hv Q hQ
          rw [h1, map_zero] at this
          exact WithZero.exp_ne_zero this.symm
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]
      · rw [hz Q hQ, mul_zero, mul_zero]
    rw [e]
    exact ⟨Subtype.property _, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)⟩

private theorem val_unifAt {F : Type} [Field F] [NumberField F] (v : Pl F) :
    Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v : Fv F v) = WithZero.exp (-1 : ℤ) := by
  have e := GlobalTheory.FlipMatch.isEquiv_Fv v
  have h : valuation (Fv F v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v : Fv F v) = uniformizer (Fv F v) :=
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  refine le_antisymm ?_ ?_
  · have h1 : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v : Fv F v) < 1 := e.lt_one_iff_lt_one.1 (h ▸ uniformizer_lt_one)
    rw [← WithZero.exp_zero] at h1
    exact WithZero.lt_mul_exp_iff_le (by simp) |>.1 (by simpa [← WithZero.exp_add] using h1)
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at hπ
    rw [← hπ, ← e, h]
    exact le_uniformizer_iff.2 (e.lt_one_iff_lt_one.2 (by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega))

private theorem val_evW {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : Lev.EAf D) :
    Valued.v (GlobalTheory.BotMatch.evW τ z) = Valued.v (cpt (D := D) (splitPrime τ) z) :=
  GlobalTheory.FlipMatch.valued_complEquiv_symm τ _

theorem UpperTheory.mem_intAdeles_and_ideal_iff_splitEmbeddings :
    ∀ (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)), IsIdemSum ε Pw → ∀ (ι : Type) [Fintype ι] (pl : ι → Pl D.host.F)
        (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i)), (∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) →
        Function.Injective (fun i => splitPrime (τ i)) → ∀ (c : Pl D.host.E → ℕ) (z : Lev.EAf D), toEAf D ε * z = z →
          (z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈ 𝒪[Fv D.host.F (pl i)]) ∧
          (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) z ↔
            ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈ GlobalTheory.SplitWeil.cball (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i) ^ c (splitPrime (τ i)))) := by
  intro D ε Pw hε ι _ pl τ hP _ c z hz
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hε
  have h0 : ∀ Q, Q ∉ Pw → cpt (D := D) Q z = 0 := fun Q hQ => by
    rw [← hz, RingHom.map_mul, map_sum, map_sum, Finset.sum_eq_zero, zero_mul]
    intro P hP
    exact (cpt_of_isIdemAt (hes P hP)).2 Q fun e => hQ (e ▸ hP)
  constructor
  · have h1 : ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈ 𝒪[Fv D.host.F (pl i)] ↔
        cpt (D := D) (splitPrime (τ i)) z ∈ (splitPrime (τ i)).adicCompletionIntegers D.host.E := fun i => by
      rw [Valuation.mem_integer_iff, (GlobalTheory.FlipMatch.isEquiv_Fv _).le_one_iff_le_one, val_evW,
        HeightOneSpectrum.mem_adicCompletionIntegers]
    refine (mem_OA_iff z).trans ⟨fun h i => (h1 i).2 (h _), fun h Q => ?_⟩
    by_cases hQ : Q ∈ Pw
    · obtain ⟨i, rfl⟩ := (hP Q).1 hQ
      exact (h1 i).1 (h i)
    · rw [h0 Q hQ]
      exact zero_mem _
  · have h1 : ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈
        GlobalTheory.SplitWeil.cball (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i) ^ c (splitPrime (τ i))) ↔
        Valued.v (cpt (D := D) (splitPrime (τ i)) z) ≤ WithZero.exp (-(c (splitPrime (τ i)) : ℤ)) := fun i => by
      refine (GlobalTheory.FlipMatch.isEquiv_Fv (pl i) _ _).trans ?_
      rw [val_evW, Units.val_pow_eq_pow_val, map_pow, val_unifAt, ← WithZero.exp_nsmul]
      simp
    refine (inId_iff Pw c z h0).trans ⟨fun h i => (h1 i).2 (h _ ((hP _).2 ⟨i, rfl⟩)), fun h Q hQ => ?_⟩
    obtain ⟨i, rfl⟩ := (hP Q).1 hQ
    exact (h1 i).1 (h i)
