import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntTraceModEqSumResiduesSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverTypePrimeChosenAndConjStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemPrimeOfInclEMemPlaceIdealIntegralAdelicSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerLiftModNatIntegralAdeleTensorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpDivMulEqStdAddCharMulOfCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarFiniteAddCharDivNatEqExpTraceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SymChar.CharProd
open Classical

theorem wInt_le {D : D7} (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E))
    {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (hc : c ∈ GlobalTheory.Mem.SymChar.wInt X w) :
    c ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, _, rfl⟩ := hx
    exact Formalism.L2.SG.Pf.unitaryCongruence.inclE_mem X.B.I ⟨a, rfl⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact mul_mem c.2 hx

theorem addChar_sum {ι A M : Type} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M) (s : Finset ι)
    (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

instance neZeroG (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def cK (D : D7) (k : Fin 2) : ZMod (D.host.g k) := ((D.host.g (k + 1) : ℕ) : ZMod (D.host.g k))⁻¹

def psiK (D : D7) (k : Fin 2) : AddChar (ZMod (D.host.g k)) ℂ :=
  (ZMod.stdAddChar (N := D.host.g k)).mulShift (cK D k)

theorem cK_ne_zero (D : D7) (k : Fin 2) : cK D k ≠ 0 := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  unfold cK
  refine inv_ne_zero ?_
  rw [Ne, CharP.cast_eq_zero_iff (ZMod (D.host.g k)) (D.host.g k)]
  intro hd
  have h := (Nat.prime_dvd_prime_iff_eq (D.host.g_prime k) (D.host.g_prime (k + 1))).1 hd
  have hne := D.host.g_ne
  fin_cases k
  · exact hne h
  · exact hne h.symm

theorem psiK_ne_one (D : D7) (k : Fin 2) : psiK D k ≠ 1 :=
  ZMod.isPrimitive_stdAddChar _ (cK_ne_zero D k)

theorem psiEf_conj_eq_prod : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ ψ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ, (∀ kv, ψ' kv ≠ 1) ∧ ∀ (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (t u : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1)), (∀ kv, GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) s (t kv)) → (∀ kv, GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I s) (u kv)) → star (X.psiEf (divN X.B.I X.B.g s)) = ∏ kv, ψ' kv (t kv + u kv) := by
  intro D X _h _hι hg
  refine ⟨fun kv => psiK D kv.1, fun kv => psiK_ne_one D kv.1, ?_⟩
  intro s t u ht hu
  obtain ⟨_, _, hcard0⟩ := GlobalTheory.T.places_over_typePrime_chosen_and_conj D 0
  obtain ⟨v0⟩ : Nonempty (D.nd.PlG 0) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    have h0 : Module.finrank ℚ D.host.E = 0 := by rw [← hcard0]; simp
    exact (Module.finrank_pos (R := ℚ) (M := D.host.E)).ne' h0
  have hs : s ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
    have h1 := wInt_le X _ (ht ⟨0, v0⟩)
    have h2 : (((t ⟨0, v0⟩).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
      natCast_mem _ _
    simpa using add_mem h1 h2
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_integer_lift_mod_nat_integralAdeleTensor D X s hs
  set a := Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E)) with ha
  have hg0 : X.B.g ≠ 0 := by
    rw [X.g_eq]; exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hstep : X.psiEf (divN X.B.I X.B.g s) = X.psiEf (divN X.B.I X.B.g a) := by
    conv_lhs => rw [show s = a + (s - a) by ring]
    rw [Formalism.L2.SG.Pf.unitaryCongruence.divN_add, X.psiEf_add,
      Formalism.L2.SG.Pf.unitaryCongruence.psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg0 hα, mul_one]
  rw [hstep, GlobalTheory.T.star_finiteAddChar_div_nat_eq_exp_trace D X α]
  have hres : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      α - (((t kv).val : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal ∧
      α - (((u kv).val : ℕ) : 𝓞 D.host.E) ∈ (GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw kv.1 kv.2)).asIdeal := by
    intro kv
    have hZ : s - a ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) :=
      GlobalTheory.Mem.SymChar.wInt_of_zmod X kv.1 (hg kv) hα
    constructor
    · apply GlobalTheory.T.mem_prime_of_inclE_mem_placeIdealIntegralAdelicSpan D X
      have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)
          (X.ιE.symm (((α - (((t kv).val : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E)) : D.host.E)) =
          (s - (((t kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) - (s - a) := by
        rw [ha]; push_cast; rw [map_sub, map_natCast, map_sub, map_natCast]; ring
      rw [e]; exact sub_mem (ht kv) hZ
    · rw [GlobalTheory.IdemSupport.mem_cP, map_sub, map_natCast]
      apply GlobalTheory.T.mem_prime_of_inclE_mem_placeIdealIntegralAdelicSpan D X
      have hZ' : sigA X.B.I s - sigA X.B.I a ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
        rw [← map_sub]
        exact GlobalTheory.Mem.SymChar.wInt_of_zmod X kv.1 (hg kv) (Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g hα)
      have hsa : sigA X.B.I a = Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)
          (X.ιE.symm ((GlobalTheory.IdemSupport.cO D α : 𝓞 D.host.E) : D.host.E)) := by
        rw [ha, Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE]
        congr 1
        apply X.ιE.injective
        rw [X.ιE_conj, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, GlobalTheory.IdemSupport.cO_coe]
        exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
      have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)
          (X.ιE.symm (((GlobalTheory.IdemSupport.cO D α - (((u kv).val : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E)) : D.host.E)) =
          (sigA X.B.I s - (((u kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) -
            (sigA X.B.I s - sigA X.B.I a) := by
        rw [hsa]; push_cast; rw [map_sub, map_natCast, map_sub, map_natCast]; ring
      rw [e]; exact sub_mem (hu kv) hZ'
  have htr : ∀ k : Fin 2, ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ZMod (D.host.g k)) =
      ∑ v : D.nd.PlG k, (t ⟨k, v⟩ + u ⟨k, v⟩) := by
    intro k
    obtain ⟨hinj, hcov, hcard⟩ := GlobalTheory.T.places_over_typePrime_chosen_and_conj D k
    rw [GlobalTheory.T.intTrace_modEq_sum_residues_split_prime (D.host.g k) (D.host.g_prime k) _ hinj hcov hcard α
      (Sum.elim (fun v => (((t ⟨k, v⟩).val : ℕ) : ℤ)) (fun v => (((u ⟨k, v⟩).val : ℕ) : ℤ))) ?_]
    · rw [Fintype.sum_sum_type, Finset.sum_add_distrib]; simp
    · rintro (v | v)
      · simpa using (hres ⟨k, v⟩).1
      · simpa using (hres ⟨k, v⟩).2
  rw [Fintype.prod_sigma]
  have hk : ∀ k : Fin 2, ∏ v : D.nd.PlG k, psiK D k (t ⟨k, v⟩ + u ⟨k, v⟩) =
      psiK D k ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ZMod (D.host.g k)) := by
    intro k; rw [htr k, addChar_sum]
  simp only [hk, Fin.prod_univ_two]
  simp only [psiK, cK, AddChar.mulShift_apply]
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  rw [X.g_eq]
  exact GlobalTheory.T.exp_div_mul_eq_stdAddChar_mul_of_coprime (D.host.g 0) (D.host.g 1) hcop _

end GlobalTheory.Mem.SymChar.CharProd
