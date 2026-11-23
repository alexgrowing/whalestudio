import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

variable {l : ℕ} [Fact l.Prime]

def sh (x : Tl l) : ℂ_[l] := ((PreTilt.untilt x : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l])

def omC : Om l →+* ℂ_[l] := algebraMap (Om l) ℂ_[l]

theorem omC_apply (y : Om l) : omC y = (y : ℂ_[l]) := (PadicComplex.coe_eq _ y).symm

theorem norm_omC (y : Om l) : ‖omC y‖ = ‖y‖ := by
  rw [omC_apply, PadicComplex.norm_extends]

def oc (K : FinExt l) : ↥(OL K) →+* ℂ_[l] :=
  (omC (l := l)).comp ((K.1.val : ↥K.1 →+* Om l).comp (algebraMap ↥(OL K) ↥K.1))

theorem oc_apply (K : FinExt l) (c : ↥(OL K)) : oc K c = (((c : ↥K.1) : Om l) : ℂ_[l]) :=
  omC_apply _

theorem norm_oc_le_one (K : FinExt l) (c : ↥(OL K)) : ‖oc K c‖ ≤ 1 := by
  have h := (GlobalTheory.CompanionTheory.LTHodge.CharEx.mem_integer_iff K (c : ↥K.1)).1 (GlobalTheory.CompanionTheory.LTHodge.CharEx.intEquiv K c).2
  rw [oc_apply, PadicComplex.norm_extends]
  exact h

@[simp] theorem sh_zero : sh (0 : Tl l) = 0 := by
  simp [sh, GroundTheory.PAdicHodge.untilt_zero]

@[simp] theorem sh_one : sh (1 : Tl l) = 1 := by
  simp [sh]

theorem sh_mul (x y : Tl l) : sh (x * y) = sh x * sh y := by
  simp [sh, GroundTheory.PAdicHodge.untilt_mul]

theorem sh_pow (x : Tl l) (n : ℕ) : sh (x ^ n) = sh x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, sh_mul, ih]

theorem norm_eq_norm_sh (x : Tl l) : ‖x‖ = ‖sh x‖ := rfl

theorem norm_sh_le_one (x : Tl l) : ‖sh x‖ ≤ 1 := GroundTheory.PAdicHodge.norm_untilt_le_one x

theorem sh_eq_zero {x : Tl l} : sh x = 0 ↔ x = 0 := GroundTheory.PAdicHodge.untilt_eq_zero_iff

theorem norm_sh_add_sub_le (x y : Tl l) : ‖sh (x + y) - (sh x + sh y)‖ ≤ ‖(l : ℂ_[l])‖ := by
  simpa [sh] using GroundTheory.PAdicHodge.norm_untilt_add_sub_le x y

theorem exists_sh_near (y : ℂ_[l]) (hy : ‖y‖ ≤ 1) : ∃ x : Tl l, ‖sh x - y‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨x, hx⟩ := GroundTheory.PAdicHodge.exists_mk_untilt_eq (K := ℂ_[l]) (p := l)
    ⟨y, GroundTheory.PAdicHodge.mem_normInteger.2 hy⟩
  exact ⟨x, by simpa [sh] using (GroundTheory.PAdicHodge.mk_eq_mk_iff_norm_sub_le (p := l)).1 hx⟩

theorem thB_tch (x : Tl l) : thB l (tch l x) = sh x := by
  show GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField l (wB l (WittVector.teichmuller l x)) = _
  rw [wB, GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus,
    WittVector.fontaineTheta_teichmuller]
  rfl

theorem thB_rB (y : Om l) : thB l (rB l y) = (y : ℂ_[l]) :=
  GroundTheory.PAdicHodge.thetaAlgHom_algClToBdR l y

theorem tch_mul (x y : Tl l) : tch l (x * y) = tch l x * tch l y := by
  simp [tch, map_mul]

theorem tch_pow (x : Tl l) (n : ℕ) : tch l (x ^ n) = tch l x ^ n := by
  induction n with
  | zero => simp [tch]
  | succ n ih => rw [pow_succ, pow_succ, tch_mul, ih]

theorem sh_actT (g : GQ l) (x : Tl l) :
    sh (actT g x) = GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) (sh x) :=
  GroundTheory.PAdicHodge.AInf.coe_untilt_gal (Formalism.Per6.toBot g) x

theorem galCp_omC (g : GQ l) (y : Om l) :
    GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) (omC y) = omC (g y) := by
  rw [omC_apply, omC_apply]
  exact GroundTheory.PAdicHodge.galCp_coe (Formalism.Per6.toBot g) y

theorem norm_galCp (g : GQ l) (x : ℂ_[l]) : ‖GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) x‖ = ‖x‖ :=
  GroundTheory.PAdicHodge.norm_galCp _ x

theorem norm_sub_pow (x y : Tl l) (f : ℕ) : ‖x ^ l ^ f - y ^ l ^ f‖ = ‖x - y‖ ^ l ^ f := by
  rw [← sub_pow_char_pow, norm_pow]

section Near

variable {ρ : ℝ}

theorem near_add (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} {A B : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x + y) - (A + B)‖ ≤ ρ := by
  have e : sh (x + y) - (A + B) = (sh (x + y) - (sh x + sh y)) + ((sh x - A) + (sh y - B)) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((norm_sh_add_sub_le x y).trans hρ)
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)))

theorem near_mul {x y : Tl l} {A B : ℂ_[l]} (hB : ‖B‖ ≤ 1) (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x * y) - A * B‖ ≤ ρ := by
  have e : sh (x * y) - A * B = sh x * (sh y - B) + (sh x - A) * B := by rw [sh_mul]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_sh_le_one x)).trans hy
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hB).trans hx

theorem near_neg (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x : Tl l} {A : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ) :
    ‖sh (-x) - (-A)‖ ≤ ρ := by
  have h := norm_sh_add_sub_le x (-x)
  rw [add_neg_cancel, sh_zero, zero_sub, norm_neg] at h
  have e : sh (-x) - (-A) = (sh x + sh (-x)) - (sh x - A) := by ring
  rw [e, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (h.trans hρ) (by rw [norm_neg]; exact hx))

theorem near_sub (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} {A B : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x - y) - (A - B)‖ ≤ ρ := by
  rw [sub_eq_add_neg x y, sub_eq_add_neg A B]
  exact near_add hρ hx (near_neg hρ hy)

theorem near_pow (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x : Tl l} {A : ℂ_[l]} (hA : ‖A‖ ≤ 1)
    (hx : ‖sh x - A‖ ≤ ρ) (n : ℕ) : ‖sh (x ^ n) - A ^ n‖ ≤ ρ := by
  induction n with
  | zero => simpa using (norm_nonneg _).trans hρ
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact near_mul hA ih hx

theorem near_sum (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {ι : Type*} (s : Finset ι) {x : ι → Tl l}
    {A : ι → ℂ_[l]} (hx : ∀ i ∈ s, ‖sh (x i) - A i‖ ≤ ρ) :
    ‖sh (∑ i ∈ s, x i) - ∑ i ∈ s, A i‖ ≤ ρ := by
  induction s using Finset.induction_on with
  | empty => simpa using (norm_nonneg _).trans hρ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact near_add hρ (hx a (Finset.mem_insert_self _ _))
      (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

theorem near_of_norm_sub_le (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} (h : ‖x - y‖ ≤ ρ) :
    ‖sh x - sh y‖ ≤ ρ := by
  have h1 : ‖sh (x - y) - 0‖ ≤ ρ := by rw [sub_zero]; exact h
  have h2 : ‖sh y - sh y‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  simpa using near_add hρ h1 h2

theorem norm_sub_le_of_near (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} (h : ‖sh x - sh y‖ ≤ ρ) :
    ‖x - y‖ ≤ ρ := by
  have h1 : ‖sh x - sh x‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  have h2 : ‖sh y - sh y‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  have h3 := near_sub hρ h1 h2
  have e : sh (x - y) = (sh (x - y) - (sh x - sh y)) + (sh x - sh y) := by ring
  rw [norm_eq_norm_sh, e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h3 h)

end Near

theorem fixed_unique {f : ℕ} (hf : 0 < f) {x y : Tl l} (hx : x ^ l ^ f = x) (hy : y ^ l ^ f = y)
    (h : ‖x - y‖ < 1) : x = y := by
  have h1 : ‖x - y‖ = ‖x - y‖ ^ l ^ f := by rw [← norm_sub_pow, hx, hy]
  have hq : 1 < l ^ f := Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt
  by_contra hne
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have := pow_lt_self_of_lt_one₀ hpos h hq
  linarith

end GlobalTheory.CompanionTheory.LTPer.Tilt
