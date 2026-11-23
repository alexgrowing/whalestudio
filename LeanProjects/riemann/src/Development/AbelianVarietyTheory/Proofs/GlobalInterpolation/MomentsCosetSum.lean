import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeisenbergCocycleFormIntegralSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexEqOfSelfDualAlternatingStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylHeisenbergOperatorCalculusRationalStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodLatticeHalfLatticeInclusionsSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFactsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLiftHalfLatticeRationalStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFactsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddSubgroupRepsExistenceCardSumStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaMovedCosetIndicatorVacuumShapeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsTranslateRationalPointUnitDenominatorStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.CosetSum

section Lat

variable {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module E H] [Module (𝓞 E) H]
  [IsScalarTower (𝓞 E) E H]

theorem sm (L : Submodule (𝓞 E) H) (r : 𝓞 E) {y z : H} (hy : y ∈ L) (h : z = (r : E) • y) : z ∈ L := by
  rw [h]; have := L.smul_mem r hy; rwa [← algebraMap_smul E r y] at this

theorem cop (L : Submodule (𝓞 E) H) {r s : 𝓞 E} (h : IsCoprime r s) {y : H} (h1 : (r : E) • y ∈ L) (h2 : (s : E) • y ∈ L) :
    y ∈ L := by
  obtain ⟨u, v, huv⟩ := h
  have h0 : (u : E) * r + v * s = 1 := by exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) huv
  have : y = (u : E) • ((r : E) • y) + (v : E) • ((s : E) • y) := by
    rw [smul_smul, smul_smul, ← add_smul, h0, one_smul]
  rw [this]; exact add_mem (sm L u h1 rfl) (sm L v h2 rfl)

theorem lat [StarRing E] (M M'' B : Submodule (𝓞 E) H) (ω : H → H → ℝ) (π σ : 𝓞 E) (p g c : ℕ)
    (hπσ : π * σ = p) (hcop : IsCoprime π σ) (hp0 : p ≠ 0) (hg : g.Coprime p) (hc : c.Coprime p)
    (hadd : ∀ x y z, ω x (y + z) = ω x y + ω x z) (hanti : ∀ x y, ω x y = -ω y x)
    (hstar : ∀ (r : E) x y, ω (r • x) y = ω x (star r • y)) (hσ : star (π : E) = σ)
    (hM : ∀ x, x ∈ M ↔ ∀ y ∈ M, ∃ n : ℤ, ω x y = n) (hM'' : ∀ x, x ∈ M'' ↔ ∀ y ∈ M'', ∃ n : ℤ, ω x y = n)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ∃ n : ℤ, ω x y = n)
    (h1 : ∀ y ∈ M, (π : E) • y ∈ M'') (h2 : ∀ y ∈ M'', (σ : E) • y ∈ M)
    (b1 : ∀ y ∈ M, ((g : E) * ((π : E) / σ)) • y ∈ B) (b2 : ∀ y ∈ B, ((g : E) * ((σ : E) / π)) • y ∈ M) :
    ∃ B' B₁ B₂ : AddSubgroup H,
      (∀ y, y ∈ B' ↔ y ∈ B ∧ ∀ m ∈ M ⊓ M'', ∃ n : ℤ, ω ((((c * g : ℕ) : E) * σ) • m) y = n) ∧ B₁ ≤ B' ∧ B₂ ≤ B' ∧
      (∀ y ∈ B, y ∈ M → y ∈ B') ∧ (∀ y ∈ B', ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ M.toAddSubgroup) ∧
      (∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ M.toAddSubgroup → y₁ ∈ M.toAddSubgroup) ∧
      (∀ R, IsReps M.toAddSubgroup B₁ R → IsReps M.toAddSubgroup M''.toAddSubgroup R) ∧ ∀ y ∈ B₂, (g : E) • y ∈ M := by
  have hpE : (p : E) = π * σ := by exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) hπσ.symm
  have hp' : (p : E) ≠ 0 := by exact_mod_cast hp0
  have hπ0 : (π : E) ≠ 0 := fun h => hp' (by rw [hpE, h, zero_mul])
  have hσ0 : (σ : E) ≠ 0 := fun h => hp' (by rw [hpE, h, mul_zero])
  have hπ : star (σ : E) = π := by rw [← hσ, star_star]
  have h0 : ∀ x, ω x 0 = 0 := fun x => by have := hadd x 0 0; rw [add_zero] at this; linarith
  have hneg : ∀ x y, ω x (-y) = -ω x y := fun x y => by
    have := hadd x y (-y); rw [add_neg_cancel, h0] at this; linarith
  have hgp : IsCoprime (g : 𝓞 E) (π * σ) := by rw [hπσ]; exact Nat.Coprime.cast hg
  have hcgp : IsCoprime ((c * g : ℕ) : 𝓞 E) (p : 𝓞 E) := Nat.Coprime.cast (Nat.Coprime.mul_left hc hg)
  let B' : AddSubgroup H :=
    { carrier := {y | y ∈ B ∧ ∀ m ∈ M ⊓ M'', ∃ n : ℤ, ω ((((c * g : ℕ) : E) * σ) • m) y = n}
      zero_mem' := ⟨zero_mem _, fun m _ => ⟨0, by simp [h0]⟩⟩
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun m hm => by
        obtain ⟨n, hn⟩ := hx.2 m hm
        obtain ⟨k, hk⟩ := hy.2 m hm
        exact ⟨n + k, by rw [hadd, hn, hk]; push_cast; rfl⟩⟩
      neg_mem' := fun {x} hx => ⟨neg_mem hx.1, fun m hm => by
        obtain ⟨n, hn⟩ := hx.2 m hm
        exact ⟨-n, by rw [hneg, hn]; push_cast; rfl⟩⟩ }
  let B₂ : AddSubgroup H := B.toAddSubgroup.map (DistribSMul.toAddMonoidHom H (p : E))
  have hB₂ : ∀ y, y ∈ B₂ ↔ ∃ z ∈ B, (p : E) • z = y := fun y => Iff.rfl
  have hg₂ : ∀ y ∈ B₂, (g : E) • y ∈ M := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (hB₂ y).1 hy
    refine sm M (π * π) (b2 z hz) ?_
    rw [hpE]; push_cast; match_scalars; field_simp
  refine ⟨B', M''.toAddSubgroup ⊓ B.toAddSubgroup, B₂, fun y => Iff.rfl, ?_, ?_, ?_, ?_, ?_, ?_, hg₂⟩
  · intro y hy
    exact ⟨hy.2, fun m hm => (hM'' _).1 (sm M'' ((c * g : ℕ) * σ) hm.2 (by push_cast; rfl)) y hy.1⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := (hB₂ y).1 hy
    refine ⟨sm B p hz (by push_cast; rfl), fun m hm => ?_⟩
    have : (p : E) = star (p : E) := by simp
    rw [this, ← hstar]
    refine hB _ (sm B (c * σ * σ * σ) (b1 m hm.1) ?_) z hz
    rw [hpE]; push_cast; match_scalars; field_simp
  · intro y hy hyM
    exact ⟨hy, fun m hm => (hM _).1 (sm M ((c * g : ℕ) * σ) hm.1 (by push_cast; rfl)) y hyM⟩
  · intro y hy
    have e1 : ((π * π : 𝓞 E) : E) • (((c * g : ℕ) : E) • y) ∈ M'' := by
      rw [hM'']
      intro m hm
      obtain ⟨n, hn⟩ := hy.2 ((σ : E) • m) ⟨h2 m hm, sm M'' σ hm rfl⟩
      rw [smul_smul, hstar] at hn
      refine ⟨-n, ?_⟩
      rw [hanti, Int.cast_neg, ← hn]
      congr 2
      simp only [star_mul, hπ, star_natCast]
      push_cast; module
    have e2 : (σ : E) • (((c * g : ℕ) : E) • y) ∈ M'' := by
      refine sm M'' c (h1 _ (b2 y hy.1)) ?_
      push_cast; match_scalars; field_simp
    have e3 := cop M'' (hcop.mul_left hcop) e1 e2
    obtain ⟨u, v, huv⟩ := hcgp
    have huv' : (u : E) * ((c * g : ℕ) : E) + v * p = 1 := by exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) huv
    refine ⟨(u : E) • (((c * g : ℕ) : E) • y), ⟨sm M'' u e3 rfl, sm B (u * (c * g : ℕ)) hy.1 (by push_cast; module)⟩,
      (p : E) • ((v : E) • y), (hB₂ _).2 ⟨_, sm B v hy.1 rfl, rfl⟩, ?_⟩
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (p : E), huv', one_smul, sub_self]
    exact zero_mem _
  · intro y₁ hy₁ y₂ hy₂ hs
    have e1 : ((g : 𝓞 E) : E) • y₁ ∈ M := by
      have := sub_mem (sm M g hs rfl) (hg₂ y₂ hy₂)
      convert this using 1
      push_cast; module
    exact cop M hgp.of_mul_right_right e1 (h2 _ hy₁.1)
  · rintro R ⟨r1, r2, r3⟩
    refine ⟨fun x hx => (r1 x hx).1, r2, fun m hm => ?_⟩
    obtain ⟨u, v, huv⟩ := hgp.of_mul_right_right.mul_left hcop
    have huv' : (u : E) * (g * π) + v * σ = 1 := by exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) huv
    obtain ⟨x, hx, hx'⟩ := r3 (((u : E) * (g * π)) • m) ⟨sm M'' (u * (g * π)) hm (by push_cast; rfl),
      sm B u (b1 _ (h2 m hm)) (by match_scalars; field_simp)⟩
    refine ⟨x, hx, ?_⟩
    have := add_mem hx' (sm M v (h2 m hm) rfl)
    convert this using 1
    rw [smul_smul, sub_add_eq_add_sub, ← add_smul, huv', one_smul]

end Lat

section Size

variable {p : ℕ} [Fact p.Prime]

theorem lamC_mul (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  simp only [TaylorLogMetric.lamC, dif_pos hx, dif_pos hy, dif_pos (mul_mem hx hy), ← map_mul]; rfl

theorem lamC_sum (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ i ∈ s, f i ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (∑ i ∈ s, f i) = ∑ i ∈ s, TaylorLogMetric.lamC lam (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, TaylorLogMetric.lamC, dif_pos (zero_mem _)]; exact map_zero lam
  | insert k s hk ih =>
    have h1 := h k (Finset.mem_insert_self _ _)
    have h2 : ∀ i ∈ s, f i ∈ TaylorLogMetric.Qbar := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have h3 := sum_mem h2
    rw [Finset.sum_insert hk, Finset.sum_insert hk, ← ih h2]
    simp only [TaylorLogMetric.lamC, dif_pos h1, dif_pos h3, dif_pos (add_mem h1 h3), ← map_add]; rfl

theorem lamC_nat (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (n : ℕ) : TaylorLogMetric.lamC lam (n : ℂ) = n := by
  simp only [TaylorLogMetric.lamC, dif_pos (natCast_mem TaylorLogMetric.Qbar n)]; exact map_natCast lam n

theorem norm_nat_le (n : ℕ) : ‖(n : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ n

theorem norm_le_of_dvd {m n : ℕ} (h : m ∣ n) : ‖(n : ℂ_[p])‖ ≤ ‖(m : ℂ_[p])‖ := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_nat_le k)

theorem norm_nat (n : ℕ) : ‖(n : ℂ_[p])‖ = ‖(n : ℚ_[p])‖ := by
  simpa using PadicComplex.norm_extends' p (n : ℚ_[p])

theorem norm_p : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [norm_nat, Padic.norm_p]

theorem norm_unit {u : ℕ} (h : ¬ p ∣ u) : ‖(u : ℂ_[p])‖ = 1 := by
  rw [norm_nat, Padic.norm_natCast_eq_one_iff]
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd).2 h

theorem size (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (κ ζ : ℂ) (F n j k u : ℕ) (hκ : κ ∈ TaylorLogMetric.Qbar) (hκ' : ‖TaylorLogMetric.lamC lam κ‖ ^ 2 ≤ (p : ℝ) ^ F)
    (hζ : ζ ∈ TaylorLogMetric.Qbar) (hζ' : ‖TaylorLogMetric.lamC lam ζ‖ = 1) (hn : n ≠ 0) (hk : k ∣ p ^ F) (hu : ¬ p ∣ u) (hd : n ∣ u * (j * k)) :
    (n : ℂ)⁻¹ * j * (((Real.sqrt (k : ℝ) : ℝ) : ℂ) * κ) * ζ ∈ TaylorLogMetric.Qbar ∧
    ‖TaylorLogMetric.lamC lam ((n : ℂ)⁻¹ * j * (((Real.sqrt (k : ℝ) : ℝ) : ℂ) * κ) * ζ)‖ ≤ ‖((p : ℂ_[p]) ^ F)⁻¹‖ := by
  have hs2 : ((Real.sqrt (k : ℝ) : ℝ) : ℂ) * ((Real.sqrt (k : ℝ) : ℝ) : ℂ) = k := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg k)]; simp
  have hs : ((Real.sqrt (k : ℝ) : ℝ) : ℂ) ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff]
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [sq, hs2]; exact isAlgebraic_natCast k
  have hnQ := natCast_mem TaylorLogMetric.Qbar n
  have hjQ := natCast_mem TaylorLogMetric.Qbar j
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  refine ⟨mul_mem (mul_mem (mul_mem (inv_mem hnQ) hjQ) (mul_mem hs hκ)) hζ, ?_⟩
  rw [lamC_mul lam (mul_mem (mul_mem (inv_mem hnQ) hjQ) (mul_mem hs hκ)) hζ,
    lamC_mul lam (mul_mem (inv_mem hnQ) hjQ) (mul_mem hs hκ), lamC_mul lam hs hκ, lamC_mul lam (inv_mem hnQ) hjQ, lamC_nat]
  have e1 : ‖TaylorLogMetric.lamC lam (n : ℂ)⁻¹‖ * ‖(n : ℂ_[p])‖ = 1 := by
    rw [← norm_mul, ← lamC_nat lam n, ← lamC_mul lam (inv_mem hnQ) hnQ, inv_mul_cancel₀ hn']
    have := lamC_nat lam 1
    rw [Nat.cast_one] at this
    rw [this]; simp
  have e2 : ‖TaylorLogMetric.lamC lam ((Real.sqrt (k : ℝ) : ℝ) : ℂ)‖ ^ 2 = ‖(k : ℂ_[p])‖ := by
    rw [sq, ← norm_mul, ← lamC_mul lam hs hs, hs2, lamC_nat]
  have e3 : ‖(j : ℂ_[p])‖ * ‖(k : ℂ_[p])‖ ≤ ‖(n : ℂ_[p])‖ := by
    have := norm_le_of_dvd (p := p) hd
    rwa [Nat.cast_mul, Nat.cast_mul, norm_mul, norm_mul, norm_unit hu, one_mul] at this
  have hp : (0 : ℝ) < (p : ℝ) ^ F := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) F
  have e4 : 1 ≤ (p : ℝ) ^ F * ‖(k : ℂ_[p])‖ := by
    have := norm_le_of_dvd (p := p) hk
    rw [Nat.cast_pow, norm_pow, norm_p, inv_pow] at this
    rwa [inv_le_iff_one_le_mul₀' hp] at this
  rw [norm_inv, norm_pow, norm_p, inv_pow, inv_inv, norm_mul, norm_mul, norm_mul, norm_mul, hζ', mul_one]
  set a := ‖TaylorLogMetric.lamC lam (n : ℂ)⁻¹‖
  set s := ‖TaylorLogMetric.lamC lam ((Real.sqrt (k : ℝ) : ℝ) : ℂ)‖
  set K := ‖TaylorLogMetric.lamC lam κ‖
  set J := ‖(j : ℂ_[p])‖
  set kk := ‖(k : ℂ_[p])‖
  set P := (p : ℝ) ^ F
  have ha : 0 ≤ a := norm_nonneg _
  have hJ : 0 ≤ J := norm_nonneg _
  have hkk : 0 ≤ kk := norm_nonneg _
  have e5 : a * J * kk ≤ 1 := by rw [← e1, mul_assoc]; exact mul_le_mul_of_nonneg_left e3 ha
  have e6 : a * J ≤ P := by nlinarith [mul_nonneg ha hJ]
  refine (pow_le_pow_iff_left₀ (by positivity) hp.le two_ne_zero).1 ?_
  calc (a * J * (s * K)) ^ 2 = (a * J) * ((a * J * kk) * K ^ 2) := by rw [← e2]; ring
    _ ≤ P * (1 * P) := by gcongr
    _ = P ^ 2 := by ring

end Size

section Idx

variable {X : Fields} {a b : ℕ}

theorem relIndex_smulLat (r : X.E) (Z : AddSubgroup (HomE X.E a b)) (D : Submodule (𝓞 X.E) (HomE X.E a b))
    (P : AddSubgroup (HomE X.E a b)) (h : ∀ y ∈ D, r • y ∈ Z ↔ y ∈ P) :
    Z.relIndex (smulLat r D).toAddSubgroup = P.relIndex D.toAddSubgroup := by
  have e : (smulLat r D).toAddSubgroup = D.toAddSubgroup.map (DistribSMul.toAddMonoidHom _ r) := by
    ext y; exact Iff.rfl
  rw [e, ← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right, ← AddSubgroup.inf_relIndex_right P]
  congr 1
  ext y
  exact ⟨fun hy => ⟨(h y hy.2).1 hy.1, hy.2⟩, fun hy => ⟨(h y hy.2).2 hy.1, hy.2⟩⟩

theorem relIndex_ne (r : X.E) (hr : r ≠ 0) (M B : Submodule (𝓞 X.E) (HomE X.E a b)) (h : ∀ y ∈ B, r • y ∈ M)
    (hfin : (smulLat r M).toAddSubgroup.relIndex M.toAddSubgroup ≠ 0) : M.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
  rw [← relIndex_smulLat r (smulLat r M).toAddSubgroup B M.toAddSubgroup]
  · refine fun h0 => hfin (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  · refine fun y _ => ⟨?_, fun hy => ⟨y, hy, rfl⟩⟩
    rintro ⟨m, hm, e⟩
    have : m = y := smul_right_injective _ hr e
    exact this ▸ hm

theorem idx (M M'' B Z : Submodule (𝓞 X.E) (HomE X.E a b)) (π : 𝓞 X.E) (f : X.E) (g p : ℕ) (hp : p.Prime) (hg : g.Coprime p)
    (h1 : ∀ y ∈ M, (π : X.E) • y ∈ M'') (hb : ∀ y ∈ M, ((g : X.E) * (π : X.E)) • y ∈ B)
    (hZ : ∀ y ∈ M, f • y ∈ Z ↔ y ∈ smulLat (π : X.E) M)
    (hfin : (smulLat ((g : X.E) * (π : X.E)) M).toAddSubgroup.relIndex M.toAddSubgroup ≠ 0) (J : Finset (HomE X.E a b))
    (hJ : IsReps Z.toAddSubgroup (smulLat f (M ⊓ M'')).toAddSubgroup J) :
    ∃ u : ℕ, ¬ p ∣ u ∧ B.toAddSubgroup.relIndex M.toAddSubgroup ∣ u * (J.card * M''.toAddSubgroup.relIndex M.toAddSubgroup) := by
  obtain ⟨-, r2, -, -, r5⟩ := GlobalTheory.T.addSubgroup_reps_existence_card_sum (HomE X.E a b)
  have l1 : (smulLat ((g : X.E) * (π : X.E)) M).toAddSubgroup ≤ (smulLat (π : X.E) M).toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_smulLat _ _ _).2 ⟨(g : X.E) • y, sm M g hy rfl, by
      change _ = ((g : X.E) * (π : X.E)) • y
      module⟩
  have l2 : (smulLat (π : X.E) M).toAddSubgroup ≤ (M ⊓ M'').toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨sm M π hy rfl, h1 y hy⟩
  have l3 : (M ⊓ M'').toAddSubgroup ≤ M.toAddSubgroup := fun y hy => hy.1
  have l4 : (smulLat ((g : X.E) * (π : X.E)) M).toAddSubgroup ≤ B.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact hb y hy
  refine ⟨(smulLat ((g : X.E) * (π : X.E)) M).toAddSubgroup.relIndex (smulLat (π : X.E) M).toAddSubgroup, r5 _ _ g p hp hg ?_ ?_, ?_⟩
  · exact fun h0 => hfin (AddSubgroup.relIndex_eq_zero_of_le_right (l2.trans l3) h0)
  · rintro _ ⟨y, hy, rfl⟩
    refine (mem_smulLat _ _ _).2 ⟨y, hy, ?_⟩
    change _ = g • ((π : X.E) • y)
    rw [← Nat.cast_smul_eq_nsmul X.E, smul_smul]
  · have e : M''.toAddSubgroup.relIndex M.toAddSubgroup = (M ⊓ M'').toAddSubgroup.relIndex M.toAddSubgroup :=
      (AddSubgroup.inf_relIndex_left M.toAddSubgroup M''.toAddSubgroup).symm
    rw [r2 _ _ _ hJ, relIndex_smulLat f _ (M ⊓ M'') (smulLat (π : X.E) M).toAddSubgroup fun y hy => hZ y hy.1, e,
      AddSubgroup.relIndex_mul_relIndex _ _ _ l2 l3, AddSubgroup.relIndex_mul_relIndex _ _ _ l1 (l2.trans l3)]
    exact AddSubgroup.relIndex_dvd_of_le_left _ l4

end Idx

section An

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem Wx_sum {κ : Type} (x : HomE X.E a b) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ) (z : VCx X.Tau a b) :
    Wx A x (fun z => ∑ i ∈ T, c i * F i z) z = ∑ i ∈ T, c i * Wx A x (F i) z := by
  simp only [Wx, opU, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem Wx_sum' {κ : Type} (x : HomE X.E a b) (T : Finset κ) (F : κ → VCx X.Tau a b → ℂ) (z : VCx X.Tau a b) :
    Wx A x (fun z => ∑ i ∈ T, F i z) z = ∑ i ∈ T, Wx A x (F i) z := by
  simpa using Wx_sum A x T (fun _ => 1) F z

theorem Wx_mul (x : HomE X.E a b) (c : ℂ) (F : VCx X.Tau a b → ℂ) (z : VCx X.Tau a b) :
    Wx A x (fun z => c * F z) z = c * Wx A x F z := by
  simp only [Wx, opU]; ring

theorem Wx_add {x y : HomE X.E a b} (h : ∃ n : ℤ, coc A x y = n) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = Wx A (x + y) F := by
  obtain ⟨n, hn⟩ := h
  rw [(GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).1, hn]
  have : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((n : ℝ)) : ℂ)) = 1 :=
    Complex.exp_eq_one_iff.2 ⟨-n, by push_cast; ring⟩
  rw [this]; simp

theorem charsum (e : VCx X.Tau a b → ℂ) (M B Z C B' : AddSubgroup (HomE X.E a b)) [DecidablePred (· ∈ B')]
    (hfix : ∀ y ∈ M, Wx A y e = e)
    (hCM : C ≤ M) (hCZ : ∀ j ∈ C, j ∈ Z → j ∈ B) (hB : ∀ x ∈ B, ∀ y ∈ B, ∃ n : ℤ, imH A x y = n)
    (hB' : ∀ y, y ∈ B' ↔ y ∈ B ∧ ∀ c ∈ C, ∃ n : ℤ, imH A c y = n) (J R : Finset (HomE X.E a b)) (hJ : IsReps Z C J)
    (hR : ∀ y ∈ R, y ∈ B) (z : VCx X.Tau a b) :
    ∑ j ∈ J, Wx A (-j) (fun z => ∑ y ∈ R, Wx A y e z) z = J.card * ∑ y ∈ R.filter (· ∈ B'), Wx A y e z := by
  obtain ⟨-, h2, -, h4, h5, h6, -⟩ := GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b
  have e1 : ∀ j ∈ J, Wx A (-j) (fun z => ∑ y ∈ R, Wx A y e z) z = ∑ y ∈ R, brkE A y (-j) * Wx A y e z := by
    intro j hj
    rw [Wx_sum']
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [h2, hfix _ (neg_mem (hCM (hJ.1 j hj)))]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [← Finset.sum_mul]
  obtain ⟨c1, c2⟩ := (GlobalTheory.T.addSubgroup_reps_existence_card_sum (HomE X.E a b)).2.2.2.1 ℂ Z C J (fun j => brkE A y (-j)) hJ
    (fun u _ v _ => by
      simp only [h5]
      rw [neg_add, (h4 _ _ _).2.2.1, ← Complex.exp_add]
      congr 1; push_cast; ring)
    (fun u hu hZ => (h6 _ _).2 (hB _ (neg_mem (hCZ u hu hZ)) y (hR y hy)))
  split_ifs with h
  · rw [c1 fun u hu => (h6 _ _).2 (((hB' y).1 h).2 _ (neg_mem hu))]
  · rw [c2, zero_mul, mul_zero]
    intro h'
    refine h ((hB' y).2 ⟨hR y hy, fun c hc => (h6 _ _).1 ?_⟩)
    simpa using h' (-c) (neg_mem hc)

theorem prodsum (e e'' : VCx X.Tau a b → ℂ) (c : ℂ) (M B' B₁ B₂ : AddSubgroup (HomE X.E a b)) (hfix : ∀ y ∈ M, Wx A y e = e)
    (hB : ∀ x ∈ B', ∀ y ∈ B', ∃ n : ℤ, coc A x y = n) (l1 : B₁ ≤ B') (l2 : B₂ ≤ B')
    (hs : ∀ y ∈ B', ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ M) (hu : ∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ M → y₁ ∈ M)
    (R R₁ R₂ : Finset (HomE X.E a b)) (hR : IsReps M B' R) (hR₁ : IsReps M B₁ R₁) (hR₂ : IsReps M B₂ R₂)
    (he : ∀ z, ∑ y ∈ R₁, Wx A y e z = c * e'' z) (z : VCx X.Tau a b) :
    ∑ y ∈ R, Wx A y e z = ∑ y ∈ R₂, c * Wx A y e'' z := by
  rw [(GlobalTheory.T.addSubgroup_reps_existence_card_sum (HomE X.E a b)).2.2.1 ℂ M B' B₁ B₂ R R₁ R₂ (fun y => Wx A y e z) l1 l2 hs hu hR hR₁ hR₂
    (fun y hy l hl hl' => by
      show Wx A (y + l) e z = Wx A y e z
      rw [← Wx_add A (hB y hy l hl'), hfix l hl])]
  refine Finset.sum_congr rfl fun y₂ h₂ => ?_
  rw [← Wx_mul, ← funext he, Wx_sum']
  refine Finset.sum_congr rfl fun y₁ h₁ => ?_
  rw [Wx_add A (hB _ (l2 (hR₂.1 _ h₂)) _ (l1 (hR₁.1 _ h₁))), add_comm]

theorem coc_nsmul (n : ℕ) (x y : HomE X.E a b) : coc A ((n : X.E) • x) y = n * coc A x y := by
  have h4 := (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.1
  induction n with
  | zero => have := (h4 0 0 y).1; simp only [add_zero] at this; simp only [Nat.cast_zero, zero_smul]; linarith
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, (h4 _ _ _).1, ih]; push_cast; ring

end An

theorem per_smul {X : Fields} (A : Amb X) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' N'' : Submodule (𝓞 X.E) (Sp X.E b))
    (r : X.E) (h : ∀ y ∈ N', r • y ∈ N'') : ∀ y ∈ per A N N', r • y ∈ per A N N'' := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hz
    exact Submodule.subset_span ⟨s, hs, r • x, fun v hv => h _ (hx v hv), smul_comm _ _ _⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
  | smul c u _ hu => rw [smul_comm]; exact Submodule.smul_mem _ c hu

theorem moments_coset_sum : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (N'' : Submodule (𝓞 X.E) (Sp X.E b)) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]) (κ : ℂ) (F : ℕ), Ctx A a b S SG ϖ p g cA → IsSdLat N → IsSdLat N' → IsSdLat N'' → (∀ y ∈ N', (ϖ : X.E) • y ∈ N'') → (∀ y ∈ N'', star (ϖ : X.E) • y ∈ N') → PtMom A a b lam ι un (star (ϖ : X.E) / (ϖ : X.E)) → κ ∈ TaylorLogMetric.Qbar → ‖TaylorLogMetric.lamC lam κ‖ ^ 2 ≤ (p : ℝ) ^ F → (per A N N'').toAddSubgroup.relIndex (per A N N').toAddSubgroup ∣ p ^ F → (∀ R : Finset (HomE X.E a b), IsReps (per A N N').toAddSubgroup (per A N N'').toAddSubgroup R → ∀ z, ∑ y ∈ R, Wx A y (A.e a b N N') z = ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ) * κ * A.e a b N N'' z) → ∀ J : Finset (HomE X.E a b), IsReps (mulLat (p * g) (homAt S N N')).toAddSubgroup (smulLat (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) (per A N N' ⊓ per A N N'')).toAddSubgroup J → ∀ x ∈ divLat cA (homAt S N N'), x ∈ homAt (divs ϖ) N N' → InIntClosure (per A N N'' : Set (HomE X.E a b)) (fun t m => ((p : ℂ_[p]) ^ F)⁻¹ * ptTab ι un t m) Set.univ fun m => TaylorLogMetric.lamC lam (∑ j ∈ J, jetC A.cD (A.thInd S N N' (p * g) (x + j)) m) := by
  classical
  intro X A a b S SG ϖ p g cA N N' N'' _ lam ι un κ F hctx hN hN' hN'' hn1 hn2 hpt hκ hκ' hk hmove J hJ x hx hx'
  obtain ⟨hAA, b1, b2, b3, b4, -, b6, b7⟩ := GlobalTheory.T.periodLattice_halfLattice_inclusions_splitPrime X A a b S SG ϖ p g cA N N' hctx hN hN'
  obtain ⟨hX, hLa, -, hsm, hp, hϖ, hcop, -, -, hg, hcA⟩ := hctx
  have hLa' := hLa
  obtain ⟨hδ, hne, hS, hAU, hFG, hL⟩ := hLa'
  have hLa0 : A.LaHyp a b ∅ := ⟨hδ, hne, by simp, by simp [Amb.AAUnit], hFG, hL⟩
  obtain ⟨h1, -, h3, h4, -, -, h7, h8⟩ := GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b
  obtain ⟨c1, c2, -⟩ := GlobalTheory.T.heisenbergCocycleForm_integral_selfDual X A a b N N' hX hδ (hL N N' hN hN').2
  obtain ⟨-, c2'', -⟩ := GlobalTheory.T.heisenbergCocycleForm_integral_selfDual X A a b N N'' hX hδ (hL N N'' hN hN'').2
  obtain ⟨-, -, f3, -⟩ := GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hFG hAA hN hN'
  obtain ⟨r1, r2, -⟩ := GlobalTheory.T.addSubgroup_reps_existence_card_sum (HomE X.E a b)
  have hg0 : 0 < g := Nat.pos_of_ne_zero fun h => hp.one_lt.ne' (by simpa [h] using hg)
  have hcA0 : 0 < cA := Nat.pos_of_ne_zero fun h => hp.one_lt.ne' (by simpa [h] using hcA)
  have hσ : star (ϖ : X.E) = (X.conjO ϖ : 𝓞 X.E) := rfl
  rw [hσ] at b1 b2 b4 hn2 hJ
  set σ := X.conjO ϖ with hσd
  have hpE : (p : X.E) = ϖ * σ := by exact_mod_cast congrArg (fun x : 𝓞 X.E => (x : X.E)) hϖ.symm
  have hp' : (p : X.E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hπ0 : (ϖ : X.E) ≠ 0 := fun h => hp' (by rw [hpE, h, zero_mul])
  have hσ0 : (σ : X.E) ≠ 0 := fun h => hp' (by rw [hpE, h, mul_zero])
  have hgE : (g : X.E) ≠ 0 := by exact_mod_cast hg0.ne'
  have m1 := per_smul A N N' N'' _ hn1
  have m2 := per_smul A N N'' N' _ hn2
  set M := per A N N' with hM
  set M'' := per A N N'' with hM''
  set B := halfBO S M (p * g) with hB
  have hanti : ∀ u v : HomE X.E a b, imH A u v = -imH A v u := fun u v => by rw [h3, h3]; ring
  have hBi : ∀ u ∈ B, ∀ v ∈ B, ∃ n : ℤ, imH A u v = n := fun u hu v hv => by
    obtain ⟨n, hn⟩ := b6 u hu v hv
    obtain ⟨k, hk⟩ := b6 v hv u hu
    exact ⟨n - k, by rw [h3, hn, hk]; push_cast; rfl⟩
  obtain ⟨B', B₁, B₂, hB', l1, l2, l3, hs, hu, hrep, hg₂⟩ := lat M M'' B (imH A) ϖ σ p g cA hϖ hcop hp.ne_zero hg hcA
    (fun u v w => (h4 u v w).2.2.2) hanti (fun r u v => (c1 r u v).2) hσ c2 c2'' hBi m1 m2 b1 b2
  have l0 : B' ≤ B.toAddSubgroup := fun y hy => ((hB' y).1 hy).1
  have hb : ∀ y ∈ M, ((g : X.E) * ϖ) • y ∈ B := fun y hy => sm B σ (b1 y hy) (by match_scalars; field_simp)

  have fB : M.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
    refine relIndex_ne ((g * σ : 𝓞 X.E) : X.E) (by push_cast; exact mul_ne_zero hgE hσ0) M B (fun y hy => sm M ϖ (b2 y hy) ?_)
      (f3 _ fun h => mul_ne_zero hgE hσ0 (by exact_mod_cast congrArg (fun x : 𝓞 X.E => (x : X.E)) h))
    push_cast; match_scalars; field_simp
  have fM : M.toAddSubgroup.relIndex M''.toAddSubgroup ≠ 0 := relIndex_ne (σ : X.E) hσ0 M M'' m2 (f3 _ fun h => hσ0 (by simp [h]))
  have fM' : M''.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := ne_zero_of_dvd_ne_zero (pow_ne_zero _ hp.ne_zero) hk
  obtain ⟨R, hR⟩ := r1 _ _ fB
  obtain ⟨R₁, hR₁⟩ := r1 M.toAddSubgroup B₁ fun h => fB (AddSubgroup.relIndex_eq_zero_of_le_right (l1.trans l0) h)
  obtain ⟨R₂, hR₂⟩ := r1 M.toAddSubgroup B₂ fun h => fB (AddSubgroup.relIndex_eq_zero_of_le_right (l2.trans l0) h)
  have hR' : IsReps M.toAddSubgroup B' (R.filter (· ∈ B')) := by
    refine ⟨fun y hy => (Finset.mem_filter.1 hy).2,
      fun u hu v hv => hR.2.1 u (Finset.mem_filter.1 hu).1 v (Finset.mem_filter.1 hv).1, fun y hy => ?_⟩
    obtain ⟨u, hu, hu'⟩ := hR.2.2 y (l0 hy)
    refine ⟨u, Finset.mem_filter.2 ⟨hu, ?_⟩, hu'⟩
    simpa using sub_mem hy (l3 _ (sub_mem (l0 hy) (hR.1 u hu)) hu')
  have hcard : R₁.card = M''.toAddSubgroup.relIndex M.toAddSubgroup := by
    rw [r2 _ _ _ (hrep R₁ hR₁)]
    exact GlobalTheory.T.relIndex_eq_of_selfDual_alternating _ (imH A) _ _ (fun u v w => (h4 u v w).2.2.1) hanti c2 c2'' fM fM'
  obtain ⟨u, hup, hud⟩ := idx M M'' B _ ϖ _ g p hp hg m1 hb (fun y hy => (b4 y hy).2.2.2)
    (by simpa using f3 (g * ϖ) fun h => mul_ne_zero hgE hπ0 (by exact_mod_cast congrArg (fun x : 𝓞 X.E => (x : X.E)) h)) J hJ
  rw [← hcard] at hud hk

  obtain ⟨t₀, ht₀, ht₀'⟩ := GlobalTheory.T.exists_lift_halfLattice_rational X A a b S N N' cA (p * g) hFG hAA hS hAU hN hN' hcA0 (Nat.mul_pos hp.pos hg0) x hx
  obtain ⟨n, hn0, hnd, hth⟩ := GlobalTheory.T.theta_movedCosetIndicator_vacuum_shape X A a b S N N' cA (p * g) hX hLa hAA hN hN' hcA0 (Nat.mul_pos hp.pos hg0)
  have hγt := b3 x hx hx' t₀ ht₀ ht₀'
  have hCM : (smulLat (((cA * g : ℕ) : X.E) * (σ : X.E)) (M ⊓ M'')).toAddSubgroup ≤ M.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact sm M ((cA * g : ℕ) * σ) hy.1 (by push_cast; rfl)
  have hfix : ∀ y ∈ M.toAddSubgroup, Wx A y (A.e a b N N') = A.e a b N N' := fun y hy =>
    funext fun z => (hL N N' hN hN').1 _ ⟨y, hy, rfl⟩ z
  have hsh : ∀ j ∈ J, A.thInd S N N' (p * g) (x + j) =
      fun z => (n : ℂ)⁻¹ * Wx A (-t₀) (Wx A (-j) fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) z := by
    intro j hj
    have hjA : j ∈ halfAO S M (cA * (p * g)) := by
      obtain ⟨y, hy, rfl⟩ := hJ.1 j hj
      exact (b4 y hy.1).2.1
    rw [Wx_add A (b7 _ (neg_mem ht₀) _ (neg_mem hjA)), ← neg_add]
    refine hth _ (add_mem hx ?_) _ (add_mem ht₀ hjA) (by simpa using ht₀') R hR
    exact Submodule.smul_mem _ (cA : 𝓞 X.E) (b4 j (hCM (hJ.1 j hj))).1
  have hsmooth : ∀ j ∈ J, ∀ k : ℕ, ContDiff ℂ k (A.thInd S N N' (p * g) (x + j)) := by
    intro j hj k
    rw [hsh j hj]
    exact contDiff_const.mul (h7 _ _ (h7 _ _ fun k => ContDiff.sum fun y _ => h7 _ _ (hsm N N' hN hN') k) k)
  set ζ : HomE X.E a b → ℂ := fun y => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A (-t₀) y : ℂ)) with hζ
  have hsum : (fun z => ∑ j ∈ J, 1 * A.thInd S N N' (p * g) (x + j) z) = fun z => ∑ y ∈ R₂,
      ((n : ℂ)⁻¹ * J.card * (((Real.sqrt (R₁.card : ℝ) : ℝ) : ℂ) * κ) * ζ y) * Wx A (-t₀ + y) (A.e a b N N'') z := by
    funext z
    rw [Finset.sum_congr rfl fun j hj => by rw [one_mul, hsh j hj], ← Finset.mul_sum, ← Wx_sum',
      funext (charsum A _ M.toAddSubgroup B.toAddSubgroup _ _ B' hfix hCM ?_ hBi ?_ J R hJ hR.1), Wx_mul,
      funext (prodsum A _ _ _ _ B' B₁ B₂ hfix (fun u hu v hv => b6 u (l0 hu) v (l0 hv)) l1 l2 hs hu _ R₁ R₂ hR' hR₁ hR₂
        (hmove R₁ (hrep R₁ hR₁))), Wx_sum, Finset.mul_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [h1]; ring
    · rintro _ ⟨y, hy, rfl⟩ hZ
      obtain ⟨m, hm, rfl⟩ := (b4 y hy.1).2.2.2.1 hZ
      refine sm B (cA * σ) (hb m hm) ?_
      change (((cA * g : ℕ) : X.E) * (σ : X.E)) • ((ϖ : X.E) • m) = _
      push_cast; module
    · intro y
      rw [hB']
      refine and_congr_right fun _ => ⟨?_, fun h m hm => h _ ⟨m, hm, rfl⟩⟩
      rintro h _ ⟨m, hm, rfl⟩
      exact h m hm
  have hunit : ∀ y ∈ R₂, _ := fun y hy => GlobalTheory.T.moments_translate_rationalPoint_unitDenominator X A a b ϖ p N N'' lam ι un hX hLa0 hAA hsm hϖ hcop hN hN'' hpt
    (-t₀ + y) (cA * g) (Nat.Coprime.mul_left hcA hg) (by
      have := m1 _ (add_mem (neg_mem hγt) (sm M cA (hg₂ y (hR₂.1 y hy)) rfl))
      convert this using 1
      push_cast; module)
  have hroot : ∀ y ∈ R₂, ζ y ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (ζ y)‖ = 1 := by
    intro y hy
    have e0 : ((g * p * (cA * g) : ℕ) : X.E) • (-t₀) ∈ B := by
      refine sm B σ (hb _ (neg_mem hγt)) ?_
      push_cast; rw [hpE]; module
    obtain ⟨k, hk⟩ := b6 _ e0 y (l0 (l2 (hR₂.1 y hy)))
    rw [coc_nsmul] at hk
    have hne : ((g * p * (cA * g) : ℕ) : ℝ) ≠ 0 := by
      have := hp.pos
      positivity
    have e1 : coc A (-t₀) y = (((k : ℚ) / (g * p * (cA * g) : ℕ) : ℚ) : ℝ) := by
      rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, eq_div_iff hne, ← hk, mul_comm]
    simp only [hζ]
    rw [e1]
    exact (GlobalTheory.T.algebraicNumbers_padicPlaces_facts X.K p A.σ₀ ι).2.2 lam _
  have hsz := fun y hy => size lam κ (ζ y) F n J.card R₁.card u hκ hκ' (hroot y hy).1 (hroot y hy).2 hn0 hk hup (hnd.trans hud)
  have hp0 : ((p : ℂ_[p]) ^ F)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
  refine clo_congr (clo_sum R₂ _ fun y hy => clo_smul (hunit y hy).2 _ _ hp0 (hsz y hy).2) le_rfl le_rfl fun m _ => ?_
  have e1 := h8 _ J (fun _ => 1) (fun j => A.thInd S N N' (p * g) (x + j)) hsmooth m
  rw [hsum, h8 _ R₂ _ (fun y => Wx A (-t₀ + y) (A.e a b N N'')) (fun y _ => h7 _ _ (hsm N N'' hN hN''))] at e1
  simp only [one_mul] at e1
  rw [← e1, lamC_sum lam _ _ fun y hy => mul_mem (hsz y hy).1 ((hunit y hy).1 m)]
  exact Finset.sum_congr rfl fun y hy => lamC_mul lam (hsz y hy).1 ((hunit y hy).1 m)

end GlobalTheory.MomT.CosetSum
