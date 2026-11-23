import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CoverOne

variable {l : ℕ} [Fact l.Prime]

theorem theta_algebraMap_inj {z z' : ℤ_[l]}
    (h : Per.θ l (algebraMap ℤ_[l] (Ainf l) z) = Per.θ l (algebraMap ℤ_[l] (Ainf l) z')) : z = z' := by
  have h1 := GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) z
  have h2 := GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) z'
  have h3 : (algebraMap ℚ_[l] ℂ_[l]) (z : ℚ_[l]) = (algebraMap ℚ_[l] ℂ_[l]) (z' : ℚ_[l]) := by
    rw [← h1, ← h2]
    exact congrArg Subtype.val h
  exact PadicInt.ext ((algebraMap ℚ_[l] ℂ_[l]).injective h3)

theorem one_tmul_injective (LL : FinExt l) {y y' : Ainf l}
    (h : (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] y = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] y') : y = y' := by
  have hA : Function.Injective (algebraMap ℤ_[l] (Ainf l)) := fun z z' hz =>
    theta_algebraMap_inj (congrArg (Per.θ l) hz)
  have : Module.IsTorsionFree ℤ_[l] (Ainf l) := Module.isTorsionFree_iff_algebraMap_injective.2 hA
  have hO : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := fun z z' hz => by
    refine theta_algebraMap_inj ?_
    rw [← intToOC_algebraMap, ← intToOC_algebraMap, hz]
  exact Algebra.TensorProduct.includeRight_injective (R := ℤ_[l]) (A := ↥(OL LL)) (B := Ainf l) hO h

end GlobalTheory.CoverOne

namespace GlobalTheory.CoverOne

variable {l : ℕ} [Fact l.Prime]

theorem ratio_pow {e : ℕ} (ϖ : PiSys l e) (g : GQ l) (n m : ℕ) : ϖ.ratio g (n + m) ^ l ^ m = ϖ.ratio g n := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, ← add_assoc, ϖ.ratio_succ, ih]

theorem seq_fixed {e : ℕ} [NeZero e] (ϖ : PiSys l e) {g : GQ l} (hg : ϖ.kummer g = 1) (n : ℕ) :
    g (ϖ.seq n) = ϖ.seq n := by
  have hd : ∀ j, ((l : ℕ) : OC l) ∣ ϖ.ratio g j - 1 := fun j => by
    have h1 := ϖ.coeff_kummer g j
    rw [hg, map_one] at h1
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_one, ← h1]
  have hr : ϖ.ratio g n = 1 := by
    rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {((l : ℕ) : OC l)})]
    intro m
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rcases m with _ | m
    · simp
    · have := dvd_sub_pow_of_dvd_sub (hd (n + m)) m
      rwa [ratio_pow, one_pow] at this
  have h2 := congrArg Subtype.val hr
  rw [PiSys.coe_ratio, OneMemClass.coe_one, ← map_one (algebraMap (Om l) ℂ_[l])] at h2
  exact (div_eq_one_iff_eq (ϖ.seq_ne_zero n)).1 ((algebraMap (Om l) ℂ_[l]).injective h2)

end GlobalTheory.CoverOne

namespace GlobalTheory.CoverOne

variable {l : ℕ} [Fact l.Prime]

theorem unr_fixed (a : ℕ) [NeZero a] {g : GQ l} (hg : ∀ w, Per.σA g (wA l a w) = wA l a w) {x : Om l}
    (hx : x ^ l ^ a = x) : g x = x := by
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have h1 := congrArg (fun y => ((Per.θ l y : OC l) : ℂ_[l])) (hg (WittVector.teichmuller l z))
  simp only [GlobalTheory.RingBasics.θ_σA, wA_teich, WittVector.fontaineTheta_teichmuller] at h1
  have h2 : Per.σC g (ω : ℂ_[l]) = (ω : ℂ_[l]) := by
    rw [← GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
    exact (GlobalTheory.RingIface.sigO_coe l g _).symm.trans h1
  rw [GlobalTheory.RingBasics.σC_coe] at h2
  have hω' : g ω = ω := UniformSpace.Completion.coe_injective _ h2
  rcases eq_or_ne x 0 with rfl | h0
  · exact map_zero g
  have h3 := one_lt_pow_l l a
  have h4 : x ^ (l ^ a - 1) = 1 := mul_right_cancel₀ h0 (by rw [← pow_succ, Nat.sub_add_cancel h3.le, hx, one_mul])
  have : NeZero (l ^ a - 1) := ⟨by omega⟩
  obtain ⟨i, -, rfl⟩ := hω.eq_pow_of_pow_eq_one h4
  rw [map_pow, hω']

end GlobalTheory.CoverOne

namespace GlobalTheory.CoverOne

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (k : GQ l), Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) → k ∈ ϖ.GfieldInf a := by
  intro l _ a e _ _ ϖ LL _ _ k hc
  have hfix : ∀ f, galOA ↥(OL LL) k (ϖ.iTot (thetaW a LL) ↥LL.1 f) = ϖ.iTot (thetaW a LL) ↥LL.1 f :=
    fun f => hc f f fun τ => by rw [map_one]; rfl
  have hev : ∀ x, Per.σA k (ϖ.ev a x) = ϖ.ev a x := fun x => by
    have h := hfix (toAc (thetaW a LL) ↥LL.1 x)
    rw [PiSys.iTot_toAc, galOA_tmul] at h
    exact one_tmul_injective LL h
  have hteich : Per.σA k ϖ.teich = ϖ.teich := by simpa using hev X
  have h0 : ϖ.teich ≠ 0 := fun h => ϖ.flat_ne_zero (by
    have := congrArg (fun w : Ainf l => w.coeff 0) h
    simpa [PiSys.teich] using this)
  have hkum : ϖ.kummer k = 1 := by
    rw [PiSys.gal_teich, PiSys.mu, add_sub_cancel] at hteich
    have h1 := mul_right_cancel₀ h0 (hteich.trans (one_mul _).symm)
    have h2 := congrArg (fun w : Ainf l => w.coeff 0) h1
    simpa using h2
  have hseq := seq_fixed ϖ hkum
  have hw : ∀ w, Per.σA k (wA l a w) = wA l a w := fun w => by simpa using hev (C w)
  have hz : ∀ x, k x = x → x ∈ IntermediateField.fixedField (Subgroup.zpowers k) := fun x hx => by
    rintro ⟨_, m, rfl⟩
    exact MulAction.mem_fixedBy_zpow (α := Om l) (g := k) (a := x) hx m
  rw [PiSys.GfieldInf, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact IntermediateField.adjoin_le_iff.2 fun x hx => hz x (unr_fixed a hw hx)
  · exact IntermediateField.adjoin_le_iff.2 fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact hz _ (hseq 0)
  · exact IntermediateField.adjoin_le_iff.2 fun x ⟨n, hn⟩ => hn ▸ hz _ (hseq n)

end GlobalTheory.CoverOne
