import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocalGeneratorAtBasePrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealGeneratedByOneAlmostEverywhereStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section
open Classical
set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.IdeleAA

open GlobalTheory.SelfDualAt (cP indP evalV_indP algebraMap_placeIdempotent_mul cA_alg)

variable {D : D7}

abbrev ex (x : Pl D) : AE D := algebraMap (AF D.host.F) (AE D) (cP (· = x))

theorem indicatorAdele_singleton_mul_singleton (x v : Pl D) : indP (D := D) (· = v) * indP (· = x) = if v = x then indP (· = x) else 0 := by
  apply GlobalTheory.FinPl.Conductor.af_ext
  intro w
  split_ifs with h
  · subst h; rw [map_mul, evalV_indP]; split_ifs <;> simp
  · rw [map_mul, evalV_indP, evalV_indP, map_zero]; split_ifs with h1 h2 <;> simp_all

theorem indicatorIdempotent_mul (x v : Pl D) : cP (D := D) (· = v) * cP (· = x) = if v = x then cP (· = x) else 0 := by
  have e : cP (D := D) (· = v) * cP (· = x) = pairA D.host.F 0 (indP (· = v) * indP (· = x)) :=
    Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [zero_mul]) rfl
  rw [e, indicatorAdele_singleton_mul_singleton]
  split_ifs
  · rfl
  · exact Prod.ext rfl rfl

theorem ex_mul (x v : Pl D) : ex v * ex x = if v = x then ex x else 0 := by
  rw [ex, ex, ← map_mul, indicatorIdempotent_mul]; split_ifs <;> simp

theorem sum_mul_ex (S : Finset (Pl D)) (f : Pl D → D.host.E) (hf : ∀ v ∉ S, f v = 0) (x : Pl D) :
    (∑ v ∈ S, ex v * incA D (f v)) * ex x = ex x * incA D (f x) := by
  rw [Finset.sum_mul]
  have h : ∀ v ∈ S, ex v * incA D (f v) * ex x = if v = x then ex x * incA D (f x) else 0 := by
    intro v _
    rw [mul_right_comm, ex_mul]
    split_ifs with h
    · subst h; rfl
    · rw [zero_mul]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs with hx
  · rfl
  · rw [hf x hx, map_zero, mul_zero]

def alpha (S : Finset (Pl D)) (a : Pl D → D.host.E) : AE D := 1 + ∑ v ∈ S, ex v * incA D (a v - 1)

theorem alpha_mul_ex (S : Finset (Pl D)) (a : Pl D → D.host.E) (ha : ∀ v ∉ S, a v = 1) (x : Pl D) :
    alpha S a * ex x = ex x * incA D (a x) := by
  rw [alpha, add_mul, one_mul, sum_mul_ex S (fun v => a v - 1) (fun v hv => by simp [ha v hv]), map_sub, map_one,
    mul_sub, mul_one]
  ring

theorem alpha_mul_inv (S : Finset (Pl D)) (a : Pl D → D.host.E) (ha : ∀ v ∉ S, a v = 1) (h0 : ∀ v, a v ≠ 0) :
    alpha S a * alpha S (fun v => (a v)⁻¹) = 1 := by
  have ha' : ∀ v ∉ S, (fun v => (a v)⁻¹) v = 1 := fun v hv => by simp [ha v hv]
  have key : ∀ v ∈ S, ex v * incA D (a v - 1) * alpha S (fun v => (a v)⁻¹) =
      ex v * incA D ((a v - 1) * (a v)⁻¹) := by
    intro v _
    rw [mul_comm (ex v), mul_assoc, mul_comm (ex v), alpha_mul_ex S _ ha' v, map_mul]; ring
  rw [alpha, add_mul, one_mul, Finset.sum_mul, Finset.sum_congr rfl key, alpha, add_assoc, ← Finset.sum_add_distrib]
  have h2 : ∀ v ∈ S, ex v * incA D ((a v)⁻¹ - 1) + ex v * incA D ((a v - 1) * (a v)⁻¹) = 0 := by
    intro v _
    rw [← mul_add, ← map_add]
    have : (a v)⁻¹ - 1 + (a v - 1) * (a v)⁻¹ = 0 := by rw [sub_mul, mul_inv_cancel₀ (h0 v)]; ring
    rw [this, map_zero, mul_zero]
  rw [Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero]

theorem cA_incA (t : D.host.E) : cA D (incA D t) = incA D (D.host.conj t) := by
  change (1 : AF D.host.F) ⊗ₜ[D.host.F] D.sp.cm.sig t = _
  rw [Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj]
  rfl

theorem tmul_eq (p : AF D.host.F) (e : D.host.E) :
    p ⊗ₜ[D.host.F] e = algebraMap (AF D.host.F) (AE D) p * incA D e := by
  change _ = (p ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end GlobalTheory.IdeleAA

namespace GlobalTheory.IdeleAA
open GlobalTheory.SelfDualAt (cP indP evalV_indP algebraMap_placeIdempotent_mul cA_alg)
variable {D : D7}

theorem evalV_inv_mem (x : Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) :
    evalV D.host.F x (algebraMap D.host.F (Af D.host.F) ((c : D.host.F))⁻¹) ∈ x.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : x.intValuation c = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 hc
  have h2 := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) x c
  rw [h1] at h2
  show Valued.v ((((c : D.host.F))⁻¹ : D.host.F) : x.adicCompletion D.host.F) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have : HeightOneSpectrum.valuation D.host.F x (c : D.host.F) = 1 := h2
  rw [this, inv_one]

def gam (x : Pl D) (c : 𝓞 D.host.F) : Af D.host.F := algebraMap D.host.F (Af D.host.F) ((c : D.host.F))⁻¹ * indP (· = x)

theorem gam_int (x : Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) : gam x c ∈ intAf D.host.F := by
  intro w
  rw [gam, map_mul, evalV_indP]
  split_ifs with h
  · subst h; rw [mul_one]; exact evalV_inv_mem w c hc
  · rw [mul_zero]; exact zero_mem _

theorem gam_supp (x : Pl D) (c : 𝓞 D.host.F) : ∀ w, ¬ (w = x) → evalV D.host.F w (gam x c) = 0 := by
  intro w hw
  rw [gam, map_mul, evalV_indP, if_neg hw, mul_zero]

theorem coe_ne_zero (x : Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) : ((c : D.host.F) : D.host.E) ≠ 0 := by
  intro h
  apply hc
  have : (c : D.host.F) = 0 := by exact_mod_cast h
  have : c = 0 := by exact_mod_cast this
  rw [this]; exact zero_mem _

theorem ex_scale (x : Pl D) (c : 𝓞 D.host.F) (e : D.host.E) :
    ex x * incA D (((c : D.host.F) : D.host.E)⁻¹ * e) = pairA D.host.F 0 (gam x c) ⊗ₜ[D.host.F] e := by
  rw [ex, ← tmul_eq]
  have h1 : ((c : D.host.F) : D.host.E)⁻¹ * e = ((c : D.host.F))⁻¹ • e := by
    rw [Algebra.smul_def, map_inv₀]; rfl
  rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  congr 1
  refine Prod.ext ?_ ?_
  · show ((c : D.host.F))⁻¹ • (0 : Ainf D.host.F) = 0
    exact smul_zero _
  · show ((c : D.host.F))⁻¹ • indP (D := D) (· = x) = gam x c
    rw [gam, Algebra.smul_def]

theorem pair_supp (x : Pl D) (γ : Af D.host.F) (hγ : ∀ w, ¬ (w = x) → evalV D.host.F w γ = 0) :
    cP (D := D) (· = x) * pairA D.host.F 0 γ = pairA D.host.F 0 γ := by
  refine Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [zero_mul]) ?_
  show indP (D := D) (· = x) * γ = γ
  apply GlobalTheory.FinPl.Conductor.af_ext
  intro w
  rw [map_mul, evalV_indP]
  split_ifs with h
  · rw [one_mul]
  · rw [hγ w h, mul_zero]

theorem scale_tmul (x : Pl D) (ρ : AE D) (t : D.host.E) (hρ : ρ * ex x = ex x * incA D t) (γ : Af D.host.F)
    (hγ : ∀ w, ¬ (w = x) → evalV D.host.F w γ = 0) (e : D.host.E) :
    ρ * (pairA D.host.F 0 γ ⊗ₜ[D.host.F] e) = pairA D.host.F 0 γ ⊗ₜ[D.host.F] (t * e) := by
  rw [tmul_eq, tmul_eq, ← pair_supp x γ hγ, map_mul, map_mul, ← ex, ← mul_assoc, ← mul_assoc, hρ]
  ring

end GlobalTheory.IdeleAA

namespace GlobalTheory.IdeleAA
open GlobalTheory.SelfDualAt (cP indP evalV_indP algebraMap_placeIdempotent_mul cA_alg)
variable {D : D7}

theorem indicatorAdele_mul_eq_self (x : Pl D) (γ : Af D.host.F) (hγ : ∀ w, ¬ (w = x) → evalV D.host.F w γ = 0) :
    indP (D := D) (· = x) * γ = γ := by
  apply GlobalTheory.FinPl.Conductor.af_ext
  intro w
  rw [map_mul, evalV_indP]
  split_ifs with h
  · rw [one_mul]
  · rw [hγ w h, mul_zero]

theorem pair_scale (x : Pl D) (c : 𝓞 D.host.F) (γ : Af D.host.F) (hγ : ∀ w, ¬ (w = x) → evalV D.host.F w γ = 0)
    (e : D.host.E) :
    pairA D.host.F 0 γ ⊗ₜ[D.host.F] (((c : D.host.F) : D.host.E)⁻¹ * e) =
      pairA D.host.F 0 (gam x c * γ) ⊗ₜ[D.host.F] e := by
  have h1 : ((c : D.host.F) : D.host.E)⁻¹ * e = ((c : D.host.F))⁻¹ • e := by
    rw [Algebra.smul_def, map_inv₀]; rfl
  rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  congr 1
  refine Prod.ext ?_ ?_
  · show ((c : D.host.F))⁻¹ • (0 : Ainf D.host.F) = 0
    exact smul_zero _
  · show ((c : D.host.F))⁻¹ • γ = gam x c * γ
    rw [gam, mul_assoc, indicatorAdele_mul_eq_self x γ hγ, Algebra.smul_def]

theorem gam_mul_int (x : Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) {γ : Af D.host.F} (hγ : γ ∈ intAf D.host.F) :
    gam x c * γ ∈ intAf D.host.F := GlobalTheory.LatVac.mul_mem_intAf (gam_int x c hc) hγ

theorem gam_mul_supp (x : Pl D) (c : 𝓞 D.host.F) (γ : Af D.host.F) :
    ∀ w, ¬ (w = x) → evalV D.host.F w (gam x c * γ) = 0 := by
  intro w hw
  rw [map_mul, gam_supp x c w hw, zero_mul]

theorem smul_latMul (S' : HSp D) (L : Lat S') (x : Pl D) (𝔞 𝔞' : Set D.host.E) (ρ : AE D) (t : D.host.E)
    (hρ : ρ * ex x = ex x * incA D t)
    (h𝔞 : ∀ a ∈ 𝔞, ∃ c : 𝓞 D.host.F, c ∉ x.asIdeal ∧ ∃ a' ∈ 𝔞', ∃ o : 𝓞 D.host.E,
      t * a = ((c : D.host.F) : D.host.E)⁻¹ * (a' * (o : D.host.E)))
    (y : Fin S'.rank → AE D) (hy : y ∈ latMul S' 𝔞 L (· = x)) : ρ • y ∈ latMul S' 𝔞' L (· = x) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨γ, hγ, hsupp, a, ha, l, hl, rfl⟩ := hy
    obtain ⟨c, hc, a', ha', o, hao⟩ := h𝔞 a ha
    apply AddSubgroup.subset_closure
    refine ⟨gam x c * γ, gam_mul_int x c hc hγ, gam_mul_supp x c γ, a', ha', o • l, L.smul_mem o hl, ?_⟩
    funext i
    show ρ * (pairA D.host.F 0 γ ⊗ₜ[D.host.F] (a * l i)) = _
    rw [scale_tmul x ρ t hρ γ hsupp, ← pair_scale x c γ hsupp]
    congr 1
    have ho : (o • l) i = (o : D.host.E) * l i := by rw [Pi.smul_apply, Algebra.smul_def]
    rw [ho, ← mul_assoc, hao]
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem lat_iff (S : Finset (Pl D)) (a : Pl D → D.host.E) (ha : ∀ v ∉ S, a v = 1) (h0 : ∀ v, a v ≠ 0)
    (hgen : ∀ v, ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ ((c : D.host.F) : D.host.E) * a v ∈ D.host.AA ∧
      ∀ b ∈ D.host.AA, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = a v * (o : D.host.E))
    (Sp : HSp D) (L : Lat Sp) (x : Pl D) (y : Fin Sp.rank → AE D) :
    y ∈ latA Sp L (· = x) ↔ alpha S (fun v => (a v)⁻¹) • y ∈ latV Sp L (· = x) := by
  have ha' : ∀ v ∉ S, (fun v => (a v)⁻¹) v = 1 := fun v hv => by simp [ha v hv]
  obtain ⟨c, hc, hca, hcb⟩ := hgen x
  have hc0 := coe_ne_zero x c hc
  constructor
  · intro hy
    refine smul_latMul Sp L x _ _ _ (a x)⁻¹ (alpha_mul_ex S _ ha' x) ?_ y hy
    intro b hb
    obtain ⟨o, ho⟩ := hcb b hb
    refine ⟨c, hc, 1, rfl, o, ?_⟩
    rw [one_mul, inv_mul_eq_iff_eq_mul₀ (h0 x), ← mul_assoc, mul_comm (a x), mul_assoc, ← ho, ← mul_assoc,
      inv_mul_cancel₀ hc0, one_mul]
  · intro hy
    have h := smul_latMul Sp L x {1} {a | a ∈ D.host.AA} _ (a x) (alpha_mul_ex S _ ha x) ?_ _ hy
    · rwa [smul_smul, alpha_mul_inv S a ha h0, one_smul] at h
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨c, hc, _, hca, 1, ?_⟩
    field_simp [hc0]
    simp

end GlobalTheory.IdeleAA

namespace GlobalTheory.IdeleAA
open GlobalTheory.SelfDualAt (cP indP evalV_indP algebraMap_placeIdempotent_mul cA_alg)
open GlobalTheory.FinPl.Conductor (chi chi_add chi_zero psiE_eq_chi approx tmul_mem mul_mem_int lift_mem chi_rat chi_int ev_same ev_ne)
variable {D : D7}

abbrev Dual (D : D7) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E := FractionalIdeal.dual ℤ ℚ 1

theorem trace_int_of_dual {d : D.host.E} (hd : d ∈ Dual D) (o : 𝓞 D.host.E) :
    ∃ n : ℤ, Algebra.trace ℚ D.host.E (d * o) = n := by
  change d ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) at hd
  rw [FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)] at hd
  obtain ⟨n, hn⟩ := hd (algebraMap _ _ o) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
  refine ⟨n, ?_⟩
  rw [Algebra.traceForm_apply] at hn
  rw [← hn]; simp

theorem mul_mem_dual {d : D.host.E} (hd : d ∈ Dual D) (o : 𝓞 D.host.E) : d * (o : D.host.E) ∈ Dual D := by
  have h := FractionalIdeal.mem_coe.1 (Submodule.smul_mem _ o (FractionalIdeal.mem_coe.2 hd))
  rwa [Algebra.smul_def, mul_comm] at h

theorem chi_tmul_dual {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {γ : Af D.host.F}
    (hγ : γ ∈ intAf D.host.F) {d : D.host.E} (hd : d ∈ Dual D) : chi ψ (γ ⊗ₜ[D.host.F] d) = 1 := by
  rw [chi, GlobalTheory.LatVac.trace_tmul]
  refine GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hγ
  rw [← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]
  have hi : IsIntegral ℤ (algebraMap D.host.F D.host.E (a : D.host.F)) :=
    a.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  obtain ⟨n, hn⟩ := trace_int_of_dual hd ⟨_, hi⟩
  refine ⟨n, ?_⟩
  rw [← hn, Algebra.smul_def, mul_comm]
  rfl

theorem chi_dual {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {γ : Af D.host.F}
    (hγ : γ ∈ intAf D.host.F) {d : D.host.E} (hd : d ∈ Dual D) {w : Af D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ intAE D) : chi ψ ((γ ⊗ₜ[D.host.F] d) * w) = 1 := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact chi_tmul_dual hψ (GlobalTheory.LatVac.mul_mem_intAf hγ hα) (mul_mem_dual hd o)
  | zero => rw [mul_zero]; exact chi_zero ψ
  | add x y _ _ hx hy => rw [mul_add, chi_add, hx, hy, one_mul]
  | neg x _ hx =>
    have h := chi_add ψ (γ ⊗ₜ[D.host.F] d * x) (γ ⊗ₜ[D.host.F] d * -x)
    rw [← mul_add, add_neg_cancel, mul_zero, chi_zero, hx, one_mul] at h
    exact h.symm

theorem conj_F (c : 𝓞 D.host.F) : D.host.conj ((c : D.host.F) : D.host.E) = ((c : D.host.F) : D.host.E) := by
  rw [← Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj]
  exact D.sp.cm.sig.commutes (c : D.host.F)

theorem conj_ne_zero {a : D.host.E} (ha : a ≠ 0) : D.host.conj a ≠ 0 := by
  intro h
  apply ha
  have := congrArg D.host.conj h
  rwa [Formalism.L2.Pj.conj_conj, map_zero] at this

theorem claimC (a : D.host.E) (ha0 : a ≠ 0) (c : 𝓞 D.host.F)
    (hcb : ∀ b ∈ D.host.AA, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = a * (o : D.host.E))
    {z : D.host.E} (hz : z ∈ Dual D) :
    ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * ((c : D.host.F) : D.host.E) *
      (D.host.xi0⁻¹ * a⁻¹ * (D.host.conj a)⁻¹) * z = (o : D.host.E) := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hxi := Formalism.L2.Pj.cmHost_imaginaryGenerator_ne_zero hP D
  have hca := conj_ne_zero ha0
  change z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) at hz
  rw [← Formalism.L2.Pj.dual_eq hP D] at hz
  refine FractionalIdeal.mul_induction_on (C := fun z => ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) *
      ((c : D.host.F) : D.host.E) * (D.host.xi0⁻¹ * a⁻¹ * (D.host.conj a)⁻¹) * z = (o : D.host.E)) hz ?_ ?_
  · intro m hm n hn
    refine FractionalIdeal.mul_induction_on (C := fun m => ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) *
      ((c : D.host.F) : D.host.E) * (D.host.xi0⁻¹ * a⁻¹ * (D.host.conj a)⁻¹) * (m * n) = (o : D.host.E)) hm ?_ ?_
    · intro s hs a1 ha1
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hs
      obtain ⟨o1, ho1⟩ := hcb a1 ha1
      obtain ⟨o2, ho2⟩ := hcb _ (Formalism.L2.Pj.conj_mem_AA D hn)
      have hn' : ((c : D.host.F) : D.host.E) * n = D.host.conj a * D.host.conj (o2 : D.host.E) := by
        have := congrArg D.host.conj ho2
        rwa [map_mul, map_mul, conj_F, Formalism.L2.Pj.conj_conj] at this
      refine ⟨r * o1 * (D.host.conj • o2), ?_⟩
      have e2 : ((D.host.conj • o2 : 𝓞 D.host.E) : D.host.E) = D.host.conj (o2 : D.host.E) :=
        Formalism.L2.Pj.algebraMap_conj_smul D o2
      have e1 : (((r * o1 * (D.host.conj • o2)) : 𝓞 D.host.E) : D.host.E) =
          (r : D.host.E) * (o1 : D.host.E) * D.host.conj (o2 : D.host.E) := by
        rw [← e2]; push_cast; ring
      rw [e1, Algebra.smul_def]
      have e3 : ((c : D.host.F) : D.host.E) * ((c : D.host.F) : D.host.E) *
          (D.host.xi0⁻¹ * a⁻¹ * (D.host.conj a)⁻¹) * (algebraMap (𝓞 D.host.E) D.host.E r * D.host.xi0 * a1 * n) =
          algebraMap (𝓞 D.host.E) D.host.E r * (((c : D.host.F) : D.host.E) * a1) *
            (((c : D.host.F) : D.host.E) * n) * (D.host.xi0⁻¹ * D.host.xi0) * (a⁻¹ * (D.host.conj a)⁻¹) := by ring
      rw [e3, ho1, hn', inv_mul_cancel₀ hxi]
      field_simp
    · rintro x y ⟨o, ho⟩ ⟨o', ho'⟩
      exact ⟨o + o', by rw [add_mul, mul_add, ho, ho']; push_cast; rfl⟩
  · rintro x y ⟨o, ho⟩ ⟨o', ho'⟩
    exact ⟨o + o', by rw [mul_add, ho, ho']; push_cast; rfl⟩

theorem claimC' (a : D.host.E) (c : 𝓞 D.host.F) (hca : ((c : D.host.F) : D.host.E) * a ∈ D.host.AA) :
    ((c : D.host.F) : D.host.E) * ((c : D.host.F) : D.host.E) * (D.host.xi0 * a * D.host.conj a) ∈ Dual D := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  change _ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
  rw [← Formalism.L2.Pj.dual_eq hP D]
  have e : ((c : D.host.F) : D.host.E) * ((c : D.host.F) : D.host.E) * (D.host.xi0 * a * D.host.conj a) =
      D.host.xi0 * (((c : D.host.F) : D.host.E) * a) * D.host.conj (((c : D.host.F) : D.host.E) * a) := by
    rw [map_mul, conj_F]; ring
  rw [e]
  exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hca)
    (Formalism.L2.Pj.conj_mem_AAbar D hca)

end GlobalTheory.IdeleAA

namespace GlobalTheory.IdeleAA
open GlobalTheory.SelfDualAt (cP indP evalV_indP algebraMap_placeIdempotent_mul cA_alg)
open GlobalTheory.FinPl.Conductor (chi chi_add chi_zero psiE_eq_chi approx tmul_mem mul_mem_int lift_mem chi_rat chi_int ev_same ev_ne)
variable {D : D7}

theorem cA_mul_ex (ρ : AE D) (x : Pl D) (t : D.host.E) (h : ρ * ex x = ex x * incA D t) :
    cA D ρ * ex x = ex x * incA D (D.host.conj t) := by
  have e : ex x = cA D (ex x) := (cA_alg _).symm
  calc cA D ρ * ex x = cA D (ρ * ex x) := by rw [map_mul, ← e]
    _ = ex x * incA D (D.host.conj t) := by rw [h, map_mul, ← e, cA_incA]

theorem B_mul_ex (S : Finset (Pl D)) (a : Pl D → D.host.E) (ha : ∀ v ∉ S, a v = 1) (x : Pl D) :
    incA D D.host.xi0⁻¹ * alpha S (fun v => (a v)⁻¹) * cA D (alpha S (fun v => (a v)⁻¹)) * ex x =
      ex x * incA D (D.host.xi0⁻¹ * (a x)⁻¹ * (D.host.conj (a x))⁻¹) := by
  have ha' : ∀ v ∉ S, (fun v => (a v)⁻¹) v = 1 := fun v hv => by simp [ha v hv]
  have h1 := alpha_mul_ex S _ ha' x
  have h2 := cA_mul_ex _ x _ h1
  rw [map_inv₀ D.host.conj (a x)] at h2
  rw [mul_assoc, h2, ← mul_assoc, mul_assoc (incA D _), h1, map_mul, map_mul]
  ring

theorem Binv_mul_ex (S : Finset (Pl D)) (a : Pl D → D.host.E) (ha : ∀ v ∉ S, a v = 1) (x : Pl D) :
    incA D D.host.xi0 * alpha S a * cA D (alpha S a) * ex x =
      ex x * incA D (D.host.xi0 * a x * D.host.conj (a x)) := by
  have h1 := alpha_mul_ex S _ ha x
  have h2 := cA_mul_ex _ x _ h1
  rw [mul_assoc, h2, ← mul_assoc, mul_assoc (incA D _), h1, map_mul, map_mul]
  ring

theorem Binv_mul_B (S : Finset (Pl D)) (a : Pl D → D.host.E) (ha : ∀ v ∉ S, a v = 1) (h0 : ∀ v, a v ≠ 0) :
    (incA D D.host.xi0 * alpha S a * cA D (alpha S a)) *
      (incA D D.host.xi0⁻¹ * alpha S (fun v => (a v)⁻¹) * cA D (alpha S (fun v => (a v)⁻¹))) = 1 := by
  have hxi := Formalism.L2.Pj.cmHost_imaginaryGenerator_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  calc _ = incA D (D.host.xi0 * D.host.xi0⁻¹) * (alpha S a * alpha S (fun v => (a v)⁻¹)) *
        cA D (alpha S a * alpha S (fun v => (a v)⁻¹)) := by rw [map_mul, map_mul]; ring
    _ = 1 := by rw [mul_inv_cancel₀ hxi, alpha_mul_inv S a ha h0, map_one, map_one, one_mul, one_mul]

theorem mul_of_ex (ρ : AE D) (x : Pl D) (t : D.host.E) (h : ρ * ex x = ex x * incA D t) {z : AE D}
    (hz : z ∈ idAt D (· = x)) : ρ * z = ex x * incA D t * z := by
  conv_lhs => rw [← algebraMap_placeIdempotent_mul (· = x) z hz]
  rw [← mul_assoc, ← ex, h]

theorem intAt_mul {x : Pl D} {z w : AE D} (hz : z ∈ intAt D (· = x)) (hw : w ∈ intAt D (· = x)) :
    z * w ∈ intAt D (· = x) :=
  ⟨Ideal.mul_mem_right _ _ hz.1, by rw [map_mul]; exact mul_mem_int hz.2 hw.2⟩

theorem coeC (c : 𝓞 D.host.F) : (((c * c : 𝓞 D.host.F) : D.host.F) : D.host.E) =
    ((c : D.host.F) : D.host.E) * ((c : D.host.F) : D.host.E) := by push_cast; ring

theorem C_not_mem {x : Pl D} {c : 𝓞 D.host.F} (hc : c ∉ x.asIdeal) : c * c ∉ x.asIdeal := fun h =>
  (x.isPrime.mem_or_mem h).elim hc hc

theorem indicatorIdempotent_eq_single (x : Pl D) : cP (D := D) (· = x) = pairA D.host.F 0 (singleV D.host.F x 1) := by
  refine congrArg (pairA D.host.F 0) (GlobalTheory.FinPl.Conductor.af_ext fun w => ?_)
  rw [evalV_indP]
  split_ifs with h
  · subst h; rw [ev_same]
  · rw [ev_ne h]

theorem finPart_incA (o : D.host.E) : finPart D (incA D o) = (1 : Af D.host.F) ⊗ₜ[D.host.F] o := by
  change finPart D ((1 : AF D.host.F) ⊗ₜ[D.host.F] o) = _
  simp [finPart]

theorem assoc4 {R : Type*} [CommRing R] (p q s o : R) (h : p * q = 1) : s * o = p * (q * s * o) := by
  rw [← mul_assoc p, ← mul_assoc p, h, one_mul]

theorem mem_of_split (x : Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) (K x0 : D.host.E)
    {u : Af D.host.F ⊗[D.host.F] D.host.E} (hu : u ∈ intAE D) (o1 o2 : 𝓞 D.host.E) (h1 : K = o1) (h2 : K * x0 = o2) :
    (gam x c ⊗ₜ[D.host.F] K) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x0 + u) ∈ intAE D := by
  rw [mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, h2]
  refine add_mem (tmul_mem (gam_int x _ hc) o2) (mul_mem_int ?_ hu)
  rw [h1]; exact tmul_mem (gam_int x _ hc) o1

theorem finPart_ex (x : Pl D) (c : 𝓞 D.host.F) (hc0 : ((c : D.host.F) : D.host.E) ≠ 0) (t : D.host.E) :
    finPart D (ex x * incA D t) = gam x c ⊗ₜ[D.host.F] (((c : D.host.F) : D.host.E) * t) := by
  have h : t = ((c : D.host.F) : D.host.E)⁻¹ * (((c : D.host.F) : D.host.E) * t) := by
    rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  conv_lhs => rw [h]
  rw [ex_scale, GlobalTheory.LatVac.finPart_pair]

theorem finitePartTraceCharacter_idempotent_inverseDifferent {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : Pl D) (c : 𝓞 D.host.F)
    (hc : c ∉ x.asIdeal) (t : D.host.E) (ht : ((c : D.host.F) : D.host.E) * t ∈ Dual D) (w : AE D)
    (hw : finPart D w ∈ intAE D) : chi ψ (finPart D (ex x * incA D t * w)) = 1 := by
  rw [(finPart D).map_mul, finPart_ex x c (coe_ne_zero x c hc)]
  exact chi_dual hψ (gam_int x _ hc) ht hw

theorem cond_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S : Finset (Pl D)) (a : Pl D → D.host.E)
    (ha : ∀ v ∉ S, a v = 1) (h0 : ∀ v, a v ≠ 0)
    (hgen : ∀ v, ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ ((c : D.host.F) : D.host.E) * a v ∈ D.host.AA ∧
      ∀ b ∈ D.host.AA, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = a v * (o : D.host.E))
    (x : Pl D) (s : AE D) (hs : s ∈ idAt D (· = x)) :
    (∀ o ∈ intAt D (· = x), psiE ψ (s * o) = 1) ↔
      incA D D.host.xi0⁻¹ * alpha S (fun v => (a v)⁻¹) * cA D (alpha S (fun v => (a v)⁻¹)) * s ∈ intAt D (· = x) := by
  obtain ⟨c, hc, hca, hcb⟩ := hgen x
  have hC := C_not_mem hc
  have hC0 := coe_ne_zero x _ hC
  have hinf : infPart D s = 0 := hs.1
  have hinf' : ∀ o, infPart D (s * o) = 0 := fun o => by rw [map_mul, hinf, zero_mul]
  constructor
  · intro h
    have hz : ex x * s = s := algebraMap_placeIdempotent_mul _ s hs
    obtain ⟨x0, u, hu, e⟩ := approx (finPart D s)
    have hx0 : x0 ∈ Dual D := by
      change x0 ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
      rw [FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
      intro y hy
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
      have h1 := h (ex x * incA D (o : D.host.E)) (by rw [ex, indicatorIdempotent_eq_single, ← tmul_eq]; exact lift_mem x o)
      rw [← mul_assoc, mul_comm s, hz, psiE_eq_chi ψ (hinf' _), map_mul, e, finPart_incA, add_mul, chi_add,
        chi_int hψ (mul_mem_int hu (tmul_mem (GlobalTheory.LatVac.one_mem_intAf _) o)), mul_one,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one] at h1
      obtain ⟨n, hn⟩ := (chi_rat hψ _).1 h1
      exact ⟨n, by rw [Algebra.traceForm_apply, hn]; simp⟩
    have one_mem : (1 : D.host.E) ∈ Dual D := FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)
    obtain ⟨o1, ho1⟩ := claimC (a x) (h0 x) c hcb one_mem
    obtain ⟨o2, ho2⟩ := claimC (a x) (h0 x) c hcb hx0
    have hB := mul_of_ex _ x _ (B_mul_ex S a ha x) hs
    rw [hB]
    refine ⟨Ideal.mul_mem_left _ _ hs, ?_⟩
    rw [(finPart D).map_mul]
    rw [finPart_ex x (c * c) hC0]
    rw [coeC]
    rw [e]
    rw [mul_one] at ho1
    exact mem_of_split x (c * c) hC _ x0 hu o1 o2 ho1 ho2
  · intro hBs o ho
    have hw := intAt_mul hBs ho
    have hso : s * o = (incA D D.host.xi0 * alpha S a * cA D (alpha S a)) *
        (incA D D.host.xi0⁻¹ * alpha S (fun v => (a v)⁻¹) * cA D (alpha S (fun v => (a v)⁻¹)) * s * o) := by
      exact assoc4 _ _ s o (Binv_mul_B S a ha h0)
    rw [psiE_eq_chi ψ (hinf' _), hso, mul_of_ex _ x _ (Binv_mul_ex S a ha x) hw.1]
    exact finitePartTraceCharacter_idempotent_inverseDifferent hψ x (c * c) hC _ (by rw [coeC]; exact claimC' (a x) c hca) _ hw.2

end GlobalTheory.IdeleAA

namespace GlobalTheory.IdeleAA
variable {D : D7}

theorem exists_idele_AA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ α : (AE D)ˣ, ∀ x : Pl D, (∀ (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x)) ∧ ∀ s ∈ idAt D (· = x), ((∀ o ∈ intAt D (· = x), psiE ψ (s * o) = 1) ↔ incA D D.host.xi0⁻¹ * ((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x)) := by
  intro D ψ hψ
  have hAA := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hloc := GlobalTheory.T.fractionalIdeal_localGenerator_at_basePrime D D.host.AA hAA
  obtain ⟨S, hS⟩ := GlobalTheory.T.fractionalIdeal_generated_by_one_almostEverywhere D D.host.AA hAA
  let a : Pl D → D.host.E := fun v => if v ∈ S then (hloc v).choose else 1
  have hpos : ∀ v ∈ S, a v = (hloc v).choose := fun v hv => if_pos hv
  have ha : ∀ v ∉ S, a v = 1 := fun v hv => if_neg hv
  have h0 : ∀ v, a v ≠ 0 := fun v => by
    by_cases hv : v ∈ S
    · rw [hpos v hv]; exact (hloc v).choose_spec.1
    · rw [ha v hv]; exact one_ne_zero
  have hgen : ∀ v, ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ ((c : D.host.F) : D.host.E) * a v ∈ D.host.AA ∧
      ∀ b ∈ D.host.AA, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = a v * (o : D.host.E) := fun v => by
    by_cases hv : v ∈ S
    · rw [hpos v hv]; exact (hloc v).choose_spec.2
    · rw [ha v hv]
      obtain ⟨c, hc, hcA, hcb⟩ := hS v hv
      refine ⟨c, hc, by rwa [mul_one], fun b hb => ?_⟩
      obtain ⟨o, ho⟩ := hcb b hb
      exact ⟨o, by rw [ho, one_mul]⟩
  refine ⟨⟨alpha S a, alpha S (fun v => (a v)⁻¹), alpha_mul_inv S a ha h0, by rw [mul_comm]; exact alpha_mul_inv S a ha h0⟩,
    fun x => ⟨fun Sp L y => lat_iff S a ha h0 hgen Sp L x y, fun s hs => cond_iff hψ S a ha h0 hgen x s hs⟩⟩

end GlobalTheory.IdeleAA

end
