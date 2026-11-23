import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistAdmissible
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsNearlyPrimitive
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.TwistMove

open GlobalTheory.SW.TwistAdm

variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

def imL (b : Matrix (Fin N) (Fin N) E) : AddSubgroup (Fin N → E) :=
  (stdL E N).toAddSubgroup.map (Matrix.toLin' b).toAddMonoidHom

theorem mem_imL {b : Matrix (Fin N) (Fin N) E} {x : Fin N → E} :
    x ∈ imL b ↔ ∃ v ∈ stdL E N, b *ᵥ v = x := by
  simp [imL]

theorem std_eq_closure : (stdL E N).toAddSubgroup =
    AddSubgroup.closure (Set.range (Pi.basis fun _ : Fin N => integralBasis E)) := by
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  ext x
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, Base.mem_stdL,
    Module.Basis.mem_span_iff_repr_mem, Sigma.forall]
  refine forall_congr' fun a => ?_
  simp only [Pi.basis_repr]
  rw [← Module.Basis.mem_span_iff_repr_mem, mem_span_integralBasis]
  exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe⟩

theorem relIndex_imL {b₁ b₂ : Matrix (Fin N) (Fin N) E} (h₁ : b₁.det ≠ 0) (h₂ : b₂.det ≠ 0)
    (hle : imL b₁ ≤ imL b₂) :
    ((imL b₁).relIndex (imL b₂) : ℚ) * |Algebra.norm ℚ b₂.det| = |Algebra.norm ℚ b₁.det| := by
  let B := Pi.basis fun _ : Fin N => integralBasis E
  have key : ∀ b : Matrix (Fin N) (Fin N) E, b.det ≠ 0 → ∃ B' : Module.Basis _ ℚ (Fin N → E),
      imL b = AddSubgroup.closure (Set.range B') ∧ B.det B' = Algebra.norm ℚ b.det := by
    intro b hb
    have hd : LinearMap.det (Matrix.toLin' b) ≠ 0 := by rwa [LinearMap.det_toLin']
    refine ⟨B.map (((Matrix.toLin' b).equivOfDetNeZero hd).restrictScalars ℚ), ?_, ?_⟩
    · rw [imL, std_eq_closure, AddMonoidHom.map_closure, ← Set.range_comp]
      rfl
    · rw [← LinearMap.det_toLin', ← LinearMap.det_restrictScalars]
      have := B.det_comp ((Matrix.toLin' b).restrictScalars ℚ) B
      rw [B.det_self, mul_one] at this
      exact this
  obtain ⟨B₁, e₁, d₁⟩ := key b₁ h₁
  obtain ⟨B₂, e₂, d₂⟩ := key b₂ h₂
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hle B₁ B₂ e₁ e₂, ← d₁, ← d₂, ← abs_mul, mul_comm,
    Module.Basis.det_mul_det]

theorem gidx_mul_le {𝔛 : Lt E N} {t : ℕ} (ht : 0 < t) (h : ∀ v ∈ stdL E N, (t : E) • v ∈ 𝔛)
    {b : Matrix (Fin N) (Fin N) E} (hb : b.det ≠ 0) (hX : 𝔛.toAddSubgroup ≤ imL b) :
    gidx 𝔛 * |(Algebra.norm ℚ b.det : ℝ)| ≤ 1 := by
  have hs : ((t : E) • (1 : Matrix (Fin N) (Fin N) E)).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 ht.ne')
  set s := (t : E) • (1 : Matrix (Fin N) (Fin N) E) with hsd
  have h1 : imL (1 : Matrix (Fin N) (Fin N) E) = (stdL E N).toAddSubgroup := by
    ext x; simp [mem_imL]
  have hKX : imL s ≤ 𝔛.toAddSubgroup := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := mem_imL.1 hx
    simpa [hsd, Matrix.smul_mulVec] using h v hv
  have hKL : imL s ≤ (stdL E N).toAddSubgroup := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := mem_imL.1 hx
    simpa [hsd, Matrix.smul_mulVec] using nat_smul_mem _ t hv
  have e1 := relIndex_imL hs hb (hKX.trans hX)
  have e2 := relIndex_imL hs (b₂ := 1) (by simp) (h1 ▸ hKL)
  rw [h1, Matrix.det_one, map_one, abs_one, mul_one] at e2
  have hn : 0 < |Algebra.norm ℚ s.det| := abs_pos.2 (Algebra.norm_ne_zero_iff.2 hs)
  have n1 : (imL s).relIndex (imL b) ≠ 0 := fun h0 => by
    rw [h0] at e1; simp at e1; exact hn.ne' (by simpa using e1.symm)
  have l1 := AddSubgroup.relIndex_le_of_le_right (H := imL s) hX n1
  have m1 := AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hKL hKX)
    (inf_le_right : (stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup ≤ _)
  have m2 := AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hKL hKX)
    (inf_le_left : (stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup ≤ _)
  rw [AddSubgroup.inf_relIndex_right] at m1
  rw [AddSubgroup.inf_relIndex_left] at m2
  rw [← m1] at l1
  rw [← m2] at e2
  unfold gidx
  generalize (imL s).relIndex ((stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup) = k at *
  generalize (stdL E N).toAddSubgroup.relIndex 𝔛.toAddSubgroup = p at *
  generalize 𝔛.toAddSubgroup.relIndex (stdL E N).toAddSubgroup = q at *
  have hkq : (0 : ℚ) < (k * q : ℕ) := e2 ▸ hn
  have hk : 0 < k := Nat.pos_of_mul_pos_right (by exact_mod_cast hkq)
  have hq : 0 < q := Nat.pos_of_mul_pos_left (by exact_mod_cast hkq)
  have l2 : ((k * p : ℕ) : ℚ) * |Algebra.norm ℚ b.det| ≤ (k * q : ℕ) := by
    rw [e2, ← e1]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast l1) (abs_nonneg _)
  have l3 : (p : ℚ) * |Algebra.norm ℚ b.det| ≤ q := by
    push_cast at l2
    rw [mul_assoc] at l2
    exact le_of_mul_le_mul_left l2 (by exact_mod_cast hk)
  rw [div_mul_eq_mul_div, div_le_one (by exact_mod_cast hq)]
  exact_mod_cast l3

theorem exists_frame (E : Type) [Field E] [NumberField E] (N : ℕ) : ∃ c : ℕ, 0 < c ∧
    ∀ (𝔛 : Lt E N) (t : ℕ), 0 < t → (∀ v ∈ 𝔛, (t : E) • v ∈ stdL E N) →
      (∀ v ∈ stdL E N, (t : E) • v ∈ 𝔛) → ∃ b : Matrix (Fin N) (Fin N) E, b.det ≠ 0 ∧
        (∀ v ∈ stdL E N, b *ᵥ v ∈ 𝔛) ∧ ∀ u, b *ᵥ u ∈ 𝔛 → (c : E) • u ∈ stdL E N := by
  obtain ⟨C, hC⟩ := NearPrim.exists_reduce E
  obtain ⟨M, hM⟩ := NearPrim.exists_approx E
  refine ⟨M.factorial ^ N, pow_pos M.factorial_pos _, fun 𝔛 t ht h1 h2 => ?_⟩
  have ht0 : (t : E) ≠ 0 := Nat.cast_ne_zero.2 ht.ne'
  let L : AddSubgroup (Fin N → E) :=
    { carrier := {s | (t : E) • s ∈ 𝔛}
      add_mem' := fun {s t} hs ht => by
        rw [Set.mem_setOf_eq, smul_add]; exact add_mem hs ht
      zero_mem' := by simp
      neg_mem' := fun {s} hs => by rw [Set.mem_setOf_eq, smul_neg]; exact neg_mem hs }
  have hO : ∀ s : Fin N → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L := fun s hs =>
    h2 s ((Base.mem_stdL s).2 hs)
  have hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L := fun y hy s hs => by
    change (t : E) • y • s ∈ 𝔛
    rw [smul_comm]
    exact 𝔛.smul_mem (⟨y, hy⟩ : 𝓞 E) hs
  have hden : ∀ s ∈ L, ∀ i, IsIntegral ℤ (((t * t : ℤ) : E) * s i) := fun s hs i => by
    have := (Base.mem_stdL _).1 (h1 _ hs) i
    simpa [mul_assoc] using this
  choose a haL ha0 hai haC hmin using NearPrim.exists_rows L hO (t * t)
    (by positivity) hden C hC
  refine ⟨(t : E) • (Matrix.of a)ᵀ, ?_, fun v hv => ?_, fun u hu => ?_⟩
  · rw [Matrix.det_smul, Matrix.det_transpose,
      Matrix.det_of_lowerTriangular (Matrix.of a) (fun i j h => ha0 i j h)]
    exact mul_ne_zero (pow_ne_zero _ ht0) (Finset.prod_ne_zero_iff.2 fun i _ => hai i)
  · exact colsIn_mulVec (fun j => haL j) hv
  · rw [Matrix.smul_mulVec, Matrix.mulVec_transpose] at hu
    exact (Base.mem_stdL _).2 (NearPrim.integral_coord L hsm M hM (Matrix.of a) haL ha0 hai hmin N
      le_rfl u (fun j hj => absurd j.2 (not_lt.2 hj)) hu)

variable [IsCMField E]

theorem admissibleLatticeFamily_moved_by_rational_matrix {M R : ℕ} {φ : Fam E n N} {𝔛 : Lt E N} (hφ : admitted M R φ)
    (hA : Agree (R * M) 𝔛 (stdL E N)) (a : Matrix (Fin N) (Fin N) E) {c : ℕ} (hc0 : 0 < c)
    (h1 : ∀ v ∈ stdL E N, ∃ ξ ∈ 𝔛, a *ᵥ ξ = (c : E) • v)
    (h2 : ∀ ξ ∈ 𝔛, (c : E) • (a *ᵥ ξ) ∈ stdL E N) :
    admitted M (R * c) (fun Λ (x : Matrix (Fin n) (Fin N) E) => twist R 𝔛 φ Λ
      (HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) x a)) := by
  have hex := exists_mult hφ.pos.2 hA
  refine ⟨⟨hφ.pos.1, Nat.mul_pos hφ.pos.2 hc0⟩, ?_,
    fun Λ hΛ => (twist_level hφ hA a c h1 h2 hΛ).1,
    fun Λ hΛ => (twist_level hφ hA a c h1 h2 hΛ).2, ?_⟩
  · intro h hh Λ hΛ Λ' hΛ' hm x
    obtain ⟨R', hR'⟩ := twist_adm hφ hA
    have := hR'.equiv h hh Λ hΛ Λ' hΛ' hm (x * a)
    rwa [← Matrix.mul_assoc] at this
  · intro Λ hΛ Λ' hΛ' ⟨u, hu, hc, h3, h4⟩ x hx hx'
    have hct : u.Coprime (c * c) := by
      have : u.Coprime c := hc.coprime_dvd_right ⟨R * M, by ring⟩
      exact this.mul_right this
    have key : ∀ A B : Lt E n, (∀ v ∈ A, (u : E) • v ∈ B) → ColsIn B (((R * c : ℕ) : E) • x) →
        (∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ A) → ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ B := by
      intro A B hAB hB h ξ hξ
      refine mem_of_coprime B hct (hAB _ (h ξ hξ)) ?_
      have := colsIn_mulVec hB (h2 ξ hξ)
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec] at this
      rw [smul_smul]
      convert this using 2
      push_cast; ring
    simp only [twist_eq φ hex]
    by_cases h : ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ Λ
    · have h' := key Λ Λ' h3 hx' h
      rw [if_pos h, if_pos h']
      exact hφ.loc Λ hΛ Λ' hΛ' ⟨u, hu, hc.coprime_dvd_right ⟨c, by ring⟩, h3, h4⟩ _
        (cols_of_cond hex.choose_spec.2 h) (cols_of_cond hex.choose_spec.2 h')
    · rw [if_neg h, if_neg (fun h' => h (key Λ' Λ h4 hx h'))]

end GlobalTheory.SW.TwistMove

open GlobalTheory.SW.TwistMove in

theorem GlobalTheory.SW.twist_move_adm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (n M R : ℕ) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∃ a : Matrix (Fin N) (Fin N) E, a.det ≠ 0 ∧ gidx 𝔛 ≤ C * |(Algebra.norm ℚ a.det : ℝ)| ∧ admitted M (R * c) (fun Λ x => twist R 𝔛 φ Λ (x * a)) := by
  intro E _ _ _ N
  obtain ⟨c, hc, H⟩ := exists_frame E N
  have hc0 : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  refine ⟨c, |(Algebra.norm ℚ ((c : E) ^ N) : ℝ)|, hc, fun n M R φ 𝔛 hφ _ hA => ?_⟩
  obtain ⟨t, ht, -, h1, h2⟩ := id hA
  obtain ⟨b, hb, hb1, hb2⟩ := H 𝔛 t ht h1 h2
  have hu : IsUnit b.det := hb.isUnit
  have ha : b⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det b hu).ne_zero
  have k2 : ∀ ξ ∈ 𝔛, (c : E) • (b⁻¹ *ᵥ ξ) ∈ stdL E N := fun ξ hξ => hb2 _ (by
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec])
  refine ⟨b⁻¹, ha, ?_, admissibleLatticeFamily_moved_by_rational_matrix hφ hA b⁻¹ hc (fun v hv => ⟨b *ᵥ ((c : E) • v),
    hb1 _ (TwistAdm.nat_smul_mem _ c hv), by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]⟩) k2⟩
  have hd : ((c : E)⁻¹ • b).det * ((c : E) ^ N * b⁻¹.det) = 1 := by
    rw [Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Fintype.card_fin, inv_pow]
    field_simp
  have hle := gidx_mul_le ht h2 (left_ne_zero_of_mul_eq_one hd) (fun ξ hξ => mem_imL.2
    ⟨_, k2 ξ hξ, by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]⟩)
  have hn := congrArg (fun z : E => |((Algebra.norm ℚ z : ℚ) : ℝ)|) hd
  simp only [map_mul, Rat.cast_mul, abs_mul, map_one, Rat.cast_one, abs_one] at hn
  have := mul_le_mul_of_nonneg_right hle (mul_nonneg
    (abs_nonneg (Algebra.norm ℚ ((c : E) ^ N) : ℝ)) (abs_nonneg (Algebra.norm ℚ b⁻¹.det : ℝ)))
  rwa [mul_assoc, hn, mul_one, one_mul] at this
