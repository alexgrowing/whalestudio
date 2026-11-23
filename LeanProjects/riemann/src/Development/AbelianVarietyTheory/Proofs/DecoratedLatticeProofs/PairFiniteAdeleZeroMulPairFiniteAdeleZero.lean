import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdHomOrth

variable {D : D7}

def finInt (D : D7) : AddSubgroup (AE D) :=
  AddSubgroup.closure {z | ∃ α ∈ intAf D.host.F, ∃ x : D.host.E, IsIntegral ℤ x ∧ z = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x}

theorem gen_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) {x : D.host.E} (hx : IsIntegral ℤ x) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] x : AE D) ∈ finInt D :=
  AddSubgroup.subset_closure ⟨α, hα, x, hx, rfl⟩

theorem star_int {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd D.host.E).toIntAlgHom

theorem incA_eq (e : D.host.E) : incA D e = ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := rfl

theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl

theorem trace_tmul {R : Type} [CommRing R] [Algebra D.host.F R] (a : R) (e : D.host.E) :
    Algebra.trace R (R ⊗[D.host.F] D.host.E) (a ⊗ₜ[D.host.F] e) =
      a * algebraMap D.host.F R (Algebra.trace D.host.F D.host.E e) := by
  have h1 : a ⊗ₜ[D.host.F] e = a • ((1 : R) ⊗ₜ[D.host.F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : Algebra.lmul R (R ⊗[D.host.F] D.host.E) ((1 : R) ⊗ₜ[D.host.F] e) =
      (Algebra.lmul D.host.F D.host.E e).baseChange R := by
    ext x
    simp
  rw [h1, map_smul, smul_eq_mul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem intAf_mul' {a b : Af D.host.F} (ha : a ∈ intAf D.host.F) (hb : b ∈ intAf D.host.F) : a * b ∈ intAf D.host.F :=
  fun w => by rw [map_mul]; exact mul_mem (ha w) (hb w)

theorem coe_mem_intAf (r : 𝓞 D.host.F) : algebraMap D.host.F (Af D.host.F) (r : D.host.F) ∈ intAf D.host.F := by
  intro v
  rw [AlgHom.commutes]
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 D.host.F) D.host.F v r

theorem char_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {β : Af D.host.F} (hβ : β ∈ intAf D.host.F) :
    ψ (pairA D.host.F 0 β) = 1 := by
  have := GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 1 (fun a => by
    have htr : Algebra.trace ℚ D.host.F (a : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) a : ℤ) : ℚ) :=
      (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) a).symm
    rw [mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _) β hβ
  rwa [map_one, mul_one] at this

theorem pairFiniteAdele_zero_mul_pairFiniteAdele_zero (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) :=
  Prod.ext (mul_zero (0 : Ainf D.host.F)) rfl

theorem pairFiniteAdele_zero_mul_algebraMap_base (α : Af D.host.F) (q : D.host.F) :
    pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) q =
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) q) :=
  Prod.ext (zero_mul (algebraMap D.host.F (Ainf D.host.F) q)) rfl

theorem incA_mul_mem {e : D.host.E} (he : IsIntegral ℤ e) {z : AE D} (hz : z ∈ finInt D) : incA D e * z ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    rw [incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact gen_mem hα (he.mul hx)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem cA_mem {z : AE D} (hz : z ∈ finInt D) : cA D z ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    rw [cA_tmul]
    exact gen_mem hα (star_int hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem mul_mem' {z w : AE D} (hz : z ∈ finInt D) (hw : w ∈ finInt D) : z * w ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    induction hw using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, x', hx', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairFiniteAdele_zero_mul_pairFiniteAdele_zero]
      exact gen_mem (intAf_mul' hα hβ) (hx.mul hx')
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem psi_trace {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {z : AE D} (hz : z ∈ finInt D) :
    ψ (Algebra.trace (AF D.host.F) (AE D) z) = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E x) := Algebra.isIntegral_trace hx
    rw [trace_tmul, pairFiniteAdele_zero_mul_algebraMap_base]
    exact char_int hψ (intAf_mul' hα (coe_mem_intAf ⟨_, hint⟩))
  | zero => rw [map_zero]; exact AddChar.map_zero_eq_one ψ
  | add x y _ _ hx hy => rw [map_add, AddChar.map_add_eq_mul, hx, hy, one_mul]
  | neg x _ hx => rw [map_neg, AddChar.map_neg_eq_inv, hx, inv_one]

theorem exists_den {ι : Type} [Fintype ι] (f : ι → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, IsIntegral ℤ ((d : D.host.E) * f i) := by
  haveI : Algebra.IsAlgebraic ℤ D.host.E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).2 inferInstance
  obtain ⟨y, hy, h⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image f)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i => ?_⟩
  have h1 := h (f i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  rw [zsmul_eq_mul] at h1
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h1; simpa using h1
  · rw [e] at h1
    have := h1.neg
    simpa using this

theorem exists_den_entries (S T : HSp D) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ stdHom S T, ∀ r s, (d : AE D) * v r s ∈ finInt D := by
  obtain ⟨a0, ha0, hfrac⟩ := D.host.AA.isFractional
  have ha0' : ((a0 : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero ⟨a0, ha0⟩ (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨d, hd, hx0⟩ := exists_den (D := D) fun _ : Unit => ((a0 : D.host.E))⁻¹
  obtain ⟨e, he, hG⟩ := exists_den (D := D) fun p : Fin S.rank × Fin S.rank => S.gram p.1 p.2
  refine ⟨d * e, Nat.mul_pos hd he, fun v hv => ?_⟩
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r c
    have hint' : IsIntegral ℤ (((d * e : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) := by
      have hA : IsIntegral ℤ ((a0 : D.host.E) * a) := by
        obtain ⟨y, hy⟩ := hfrac a ha
        have h2 : IsIntegral ℤ (algebraMap (𝓞 D.host.E) D.host.E y) := y.2
        rw [hy, Algebra.smul_def] at h2
        exact h2
      have hsum : IsIntegral ℤ (∑ k, star (s k) * ((e : D.host.E) * S.gram k c)) :=
        IsIntegral.sum _ fun k _ => IsIntegral.mul (star_int (hs k)) (hG (k, c))
      have e1 : ((d * e : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c) =
          ((d : D.host.E) * ((a0 : D.host.E))⁻¹) * ((a0 : D.host.E) * a) * t r *
            ∑ k, star (s k) * ((e : D.host.E) * S.gram k c) := by
        have hx : ((a0 : D.host.E))⁻¹ * (a0 : D.host.E) = 1 := inv_mul_cancel₀ ha0'
        have e2 : ∑ k, star (s k) * ((e : D.host.E) * S.gram k c) = (e : D.host.E) * ∑ k, star (s k) * S.gram k c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [e2]; push_cast
        linear_combination (-((d : D.host.E) * e * a * t r * ∑ k, star (s k) * S.gram k c)) * hx
      rw [e1]
      exact (((hx0 ()).mul hA).mul (ht r)).mul hsum
    rw [Matrix.of_apply, ← map_natCast (incA D) (d * e), incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact gen_mem hα hint'
  | zero => intro r s; rw [Matrix.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro r s; rw [Matrix.add_apply, mul_add]; exact add_mem (hx r s) (hy r s)
  | neg x _ hx => intro r s; rw [Matrix.neg_apply, mul_neg]; exact neg_mem (hx r s)

theorem exists_nsmul_orth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∃ M : ℕ, 0 < M ∧ ∀ x ∈ stdHom S T, ∀ w ∈ stdHom S T, ψ (symplO S T x (M • w)) = 1 := by
  intro D ψ hψ S T
  obtain ⟨d, hd, hden⟩ := exists_den_entries S T
  obtain ⟨p, hp, hξ⟩ := exists_den (D := D) fun _ : Unit => D.host.xi0
  obtain ⟨q, hq, hS⟩ := exists_den (D := D) fun i : Fin S.rank × Fin S.rank => S.gram⁻¹ i.1 i.2
  obtain ⟨r, hr, hT⟩ := exists_den (D := D) fun i : Fin T.rank × Fin T.rank => T.gram i.1 i.2
  refine ⟨p * q * r * d * d, by positivity, fun x hx w hw => ?_⟩
  refine psi_trace hψ ?_
  unfold hO
  simp only [Finset.mul_sum]
  refine sum_mem fun a _ => sum_mem fun b _ => sum_mem fun c _ => sum_mem fun e _ => ?_
  have key : incA D D.host.xi0 * (incA D (S.gram⁻¹ a b) * cA D (((p * q * r * d * d) • w) c b) * incA D (T.gram c e) * x e a) =
      incA D ((p : D.host.E) * D.host.xi0) * (incA D ((q : D.host.E) * S.gram⁻¹ a b) * (incA D ((r : D.host.E) * T.gram c e) *
        (cA D ((d : AE D) * w c b) * ((d : AE D) * x e a)))) := by
    rw [Matrix.smul_apply, nsmul_eq_mul]
    simp only [map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [key]
  exact incA_mul_mem (hξ ()) (incA_mul_mem (hS (a, b)) (incA_mul_mem (hT (c, e))
    (mul_mem' (cA_mem (hden w hw c b)) (hden x hx e a))))

end GlobalTheory.StdHomOrth
