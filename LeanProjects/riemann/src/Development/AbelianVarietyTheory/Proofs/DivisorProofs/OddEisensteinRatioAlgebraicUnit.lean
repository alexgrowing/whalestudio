import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMapRingOfIntegersLeOne

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.VacUnit

open Formalism.MainNotions.TaylorLogMetric (hYY LocBasis YYl)
open Formalism.MainNotions.StandardLatticesGL3 (OnB LaB pullB KLat)

theorem mem_Qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Qbar) : x ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at h ⊢
  exact h.of_pow hn

theorem norm_int_le {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (f : K →+* ℂ_[p]) (c : 𝓞 K) :
    ‖f (c : K)‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
  | exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
  | (apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one ..)

theorem norm_nat_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm

theorem norm_det_le {p : ℕ} [Fact p.Prime] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ_[p]) (h : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[p] _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _

variable {D : D7} {N N' r : ℕ}

theorem hYY_comb (c : Fin r → D.host.K) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (y : Matrix (Fin N') (Fin N) D.host.E) : hYY D (∑ k, c k • b k) y = ∑ k, c k * hYY D (b k) y := by
  simp only [hYY, ← smul_eq_mul, ← map_smul, ← map_sum]
  congr 1
  simp only [Matrix.sum_apply, Matrix.smul_apply, Finset.smul_sum, smul_eq_mul, Finset.sum_mul, smul_mul_assoc]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

theorem exists_coord {p : ℕ} [Fact p.Prime] (f : D.host.K →+* ℂ_[p])
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)}
    {b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hl : LocBasis D p Y b) (hl' : LocBasis D p Y b') (j : Fin r) :
    ∃ a : Fin r → D.host.K, (∀ i, ‖f (a i)‖ ≤ 1) ∧ b' j = ∑ i, a i • b i := by
  obtain ⟨s, hs, hY⟩ := hl'.2.1 j
  obtain ⟨t, ht, c, hc⟩ := hl.2.2 _ hY
  have hst : Nat.Coprime (t * s) p := Nat.Coprime.mul_left ht hs
  have h0 : ((t * s : ℕ) : D.host.K) ≠ 0 := by
    intro h
    have h1 := norm_nat_coprime hst
    rw [← map_natCast f, h] at h1
    simp at h1
  refine ⟨fun i => ((t * s : ℕ) : D.host.K)⁻¹ * (c i : D.host.K), fun i => ?_, ?_⟩
  · rw [map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, norm_nat_coprime hst, inv_one, one_mul]
    exact norm_int_le f _
  · have h2 : ((t * s : ℕ) : D.host.K) • b' j = ∑ i, (c i : D.host.K) • b i := by
      rw [smul_smul, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul] at hc
      rw [Nat.cast_smul_eq_nsmul, hc]
      rfl
    simp only [mul_smul]
    rw [← Finset.smul_sum, ← h2, smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem norm_det_eq_one {p : ℕ} [Fact p.Prime] (f : D.host.K →+* ℂ_[p])
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)}
    {b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b)
    (hl : LocBasis D p Y b) (hl' : LocBasis D p Y b') :
    ‖f (Matrix.of fun i j => hYY D (b' j) (b i)).det‖ = 1 := by
  choose a ha hab using exists_coord f hl hl'
  choose a' ha' hab' using exists_coord f hl' hl
  have hM : ∀ i j, hYY D (b' j) (b i) = a j i := by
    intro i j
    rw [hab j, hYY_comb]
    simp [hb.1 _ i]
  have hMM : (Matrix.of fun i j => hYY D (b' j) (b i)) * (Matrix.of fun j k => a' k j) = 1 := by
    ext i k
    have h1 := hb.1 k i
    conv_lhs at h1 => rw [hab' k, hYY_comb]
    rw [Matrix.mul_apply, Matrix.one_apply, if_congr (eq_comm (a := i)) rfl rfl, ← h1]
    simp [mul_comm]
  have hd := congrArg (fun A => ‖f (Matrix.det A)‖) hMM
  simp only [Matrix.det_mul, map_mul, norm_mul, Matrix.det_one, map_one, norm_one] at hd
  have h1 : ‖f (Matrix.of fun i j => hYY D (b' j) (b i)).det‖ ≤ 1 := by
    rw [RingHom.map_det]
    exact norm_det_le _ fun i j => by simpa [hM] using ha j i
  have h2 : ‖f (Matrix.of fun j k => a' k j).det‖ ≤ 1 := by
    rw [RingHom.map_det]
    exact norm_det_le _ fun i j => by simpa using ha' j i
  refine le_antisymm h1 ?_
  rw [← hd]
  exact mul_le_of_le_one_right (norm_nonneg _) h2

noncomputable def phiK (D : D7) : D.host.K →+* Qbar :=
  (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring fun x => by
    change _ ∈ Qbar
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom
      (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toRatAlgHom

theorem at_place (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} (hC : Crv D ⊤ δ) (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0)
    {e₁ e₂ : VC D N N' → ℂ} (h₁ : oddE0 D ⊤ δ t0 N N' e₁) (h₂ : oddE0 D ⊤ δ t0 N N' e₂) (hne : e₁ ≠ 0) {κ : ℂ}
    (hκ : e₂ = κ • e₁) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 := by
  have hSD : ∀ n, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
    exact h2 ▸ (h1 1).2
  obtain ⟨b, ε, hb, hl, hε, hεn, -, he⟩ := h₁.2.2.2.2 p lam (by simp)
  obtain ⟨b', ε', hb', hl', hε', hεn', -, he'⟩ := h₂.2.2.2.2 p lam (by simp)
  obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := GlobalTheory.UnitaryTheta.const_sq_eq_det D ⊤ δ hC t0 ht N N' _ b b' hb hb'
  obtain ⟨μ, hμ, hI3⟩ := hI.mu ⊤ δ hC N N' _ _ (La0 D (tor0 D ⊤ δ) N N') (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inl ⟨_, b', hb', rfl⟩) (Or.inr ⟨_, _, hSD N, hSD N', rfl⟩) _
    (GlobalTheory.UnitaryTheta.pullB_mem D ⊤ δ hC t0 ht N N' _ b hb).1
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  have e2 := congrFun hκ z
  rw [he', hpull, Pi.smul_apply, smul_eq_mul] at e2
  rw [he] at e2 hz
  simp only [GlobalTheory.UnitaryTheta.iop_smul, hI3] at e2
  have hz' := right_ne_zero_of_mul hz
  have key : κ * ε = ε' * c * μ := by
    apply mul_right_cancel₀ hz'
    linear_combination -e2
  have hζQ : ζ ∈ Qbar := mem_Qbar_of_pow hm (hζ ▸ one_mem _)
  have hμQ : μ ∈ Qbar := mem_Qbar_of_pow (n := 8) (by norm_num) (hμ ▸ one_mem _)
  set u := phiK D (Matrix.of fun i j => hYY D (b' j) (b i)).det with hu
  have hun : ‖lam u‖ = 1 := norm_det_eq_one (lam.comp (phiK D)) hb hl hl'
  change c ^ 2 = ζ * (u : ℂ) at hc
  have hcQ : c ∈ Qbar := mem_Qbar_of_pow (n := 2) (by norm_num) (hc ▸ mul_mem hζQ u.2)
  rw [lamC, dif_pos hε] at hεn
  rw [lamC, dif_pos hε'] at hεn'
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul hz
  have hκQ : κ ∈ Qbar := by
    rw [eq_div_of_mul_eq hε0 key]
    exact div_mem (mul_mem (mul_mem hε' hcQ) hμQ) hε
  refine ⟨hκQ, ?_⟩
  rw [lamC, dif_pos hκQ]
  have root : ∀ (x : Qbar) (n : ℕ), 0 < n → (x : ℂ) ^ n = 1 → ‖lam x‖ = 1 := by
    intro x n hn hx
    have : x ^ n = 1 := Subtype.ext (by simpa using hx)
    have h := congrArg (fun y => ‖lam y‖) this
    simp only [map_pow, norm_pow, map_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  have hcn : ‖lam ⟨c, hcQ⟩‖ = 1 := by
    have : (⟨c, hcQ⟩ : Qbar) ^ 2 = ⟨ζ, hζQ⟩ * u := Subtype.ext (by simpa using hc)
    have h := congrArg (fun y => ‖lam y‖) this
    simp only [map_pow, norm_pow, map_mul, norm_mul, hun, root ⟨ζ, hζQ⟩ m hm hζ, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  have : (⟨κ, hκQ⟩ : Qbar) * ⟨ε, hε⟩ = ⟨ε', hε'⟩ * ⟨c, hcQ⟩ * ⟨μ, hμQ⟩ := Subtype.ext key
  have h := congrArg (fun y => ‖lam y‖) this
  simpa only [map_mul, norm_mul, hεn, hεn', hcn, root ⟨μ, hμQ⟩ 8 (by norm_num) hμ, mul_one] using h

theorem vac_unit : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ {N N' : ℕ} {e₁ e₂ : VC D N N' → ℂ},
  oddE0 D ⊤ δ t0 N N' e₁ → oddE0 D ⊤ δ t0 N N' e₂ → e₁ ≠ 0 → ∀ κ : ℂ, e₂ = κ • e₁ →
  κ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam κ‖ = 1 := by
  intro D hI δ t0 hC ht N N' e₁ e₂ h₁ h₂ hne κ hκ
  refine ⟨?_, fun p _ lam => (at_place hI hC ht h₁ h₂ hne hκ p lam).2⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  exact (at_place hI hC ht h₁ h₂ hne hκ 2 (IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[2])).toRingHom).1

end GlobalTheory.VacUnit
