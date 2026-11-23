import Development.EtaleCohomology.KummerTheory.AdicDegPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.KummerTheory

section Alg
variable (l : ℕ) [Fact l.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[l] M]

theorem adic_decomp [Module.Finite ℤ_[l] M] : ∃ (r : ℕ) (c : Fin r → M) (e : ℕ), 0 < e ∧
    LinearIndependent ℤ_[l] c ∧ ∀ x : M, ∃ (a : Fin r → ℤ_[l]) (τ : M), x = ∑ s, a s • c s + τ ∧ e • τ = 0 := by
  classical
  set T := Submodule.torsion ℤ_[l] M
  have hTfin : Module.Finite ℤ_[l] T := inferInstance
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors (Submodule.torsion_isTorsion (R := ℤ_[l]) (M := M))
  have hane : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  have hkill : ∀ τ ∈ T, (l ^ a.valuation : ℕ) • τ = 0 := by
    intro τ hτ
    have h1 : a • (⟨τ, hτ⟩ : T) = 0 := Submodule.mem_annihilator.mp ha _ Submodule.mem_top
    have h2 : a • τ = 0 := congrArg Subtype.val h1
    rw [PadicInt.unitCoeff_spec hane, mul_smul] at h2
    have h3 := congrArg (fun v => (((PadicInt.unitCoeff hane)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • v) h2
    simp only [smul_zero, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at h3
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    push_cast
    exact h3
  set Q := M ⧸ T
  let b := Module.finBasis ℤ_[l] Q
  let c : Fin (Module.finrank ℤ_[l] Q) → M := fun s => (Submodule.Quotient.mk_surjective T (b s)).choose
  have hc : ∀ s, T.mkQ (c s) = b s := fun s => (Submodule.Quotient.mk_surjective T (b s)).choose_spec
  have hcomp : T.mkQ ∘ c = b := funext hc
  refine ⟨_, c, l ^ a.valuation, pow_pos (Fact.out : l.Prime).pos _, ?_, ?_⟩
  · exact LinearIndependent.of_comp T.mkQ (hcomp ▸ b.linearIndependent)
  · intro x
    refine ⟨b.repr (T.mkQ x), x - ∑ s, b.repr (T.mkQ x) s • c s, by abel, hkill _ ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, hc]
    rw [b.sum_repr, sub_self]

theorem adic_qbasis {r : ℕ} (c : Fin r → M) (e : ℕ) (he : 0 < e) (hli : LinearIndependent ℤ_[l] c)
    (hdec : ∀ x : M, ∃ (a : Fin r → ℤ_[l]) (τ : M), x = ∑ s, a s • c s + τ ∧ e • τ = 0) :
    LinearIndependent ℚ_[l] (fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : ℚ_[l] ⊗[ℤ_[l]] M)) ∧
    Submodule.span ℚ_[l] (Set.range fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : ℚ_[l] ⊗[ℤ_[l]] M)) = ⊤ := by
  let f := TensorProduct.mk ℤ_[l] ℚ_[l] M 1
  refine ⟨hli.of_isLocalizedModule ℚ_[l] (nonZeroDivisors ℤ_[l]) f, ?_⟩
  have htop := span_eq_top_of_isLocalizedModule ℚ_[l] (nonZeroDivisors ℤ_[l]) f (v := Set.univ) Submodule.span_univ
  refine top_unique (htop ▸ Submodule.span_le.mpr ?_)
  rintro _ ⟨x, -, rfl⟩
  obtain ⟨a, τ, rfl, hτ⟩ := hdec x
  have hfτ : f τ = 0 := by
    have h1 : (e : ℚ_[l]) • f τ = 0 := by rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hτ, map_zero]
    exact (smul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr he.ne')
  rw [map_add, hfτ, add_zero, map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [map_smul]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

end Alg

def levH (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) : Hl l E n i →+ Ht (l ^ k) E n i where
  toFun x := lev l x k
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lev_comb (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} {r : ℕ} (c : Fin r → Hl l E n i) (a : Fin r → ℤ_[l]) (k : ℕ) :
    lev l (∑ s, a s • c s) k = comb (l ^ k) (fun s => lev l (c s) k) (fun s => PadicInt.toZModPow k (a s)) := by
  change levH l E n i k _ = _
  rw [map_sum]
  rfl

theorem AdicAlg_of : AdicAlg := by
  intro l _ E n i hfin hker M hM hcok
  obtain ⟨r, c, e, he, hli, hdec⟩ := adic_decomp l (M := Hl l E n i)
  refine ⟨r, c, e * M, Nat.mul_pos he hM, adic_qbasis l c e he hli hdec, fun k => ⟨?_, ?_⟩⟩
  · intro t ht
    have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    let a : Fin r → ℤ_[l] := fun s => ((t s).val : ℤ_[l])
    have hat : (fun s => PadicInt.toZModPow k (a s)) = t := funext fun s => by simp [a]
    have hx : lev l (∑ s, a s • c s) k = 0 := by rw [lev_comb, hat]; exact ht
    obtain ⟨y, hy⟩ := hker k _ hx
    obtain ⟨b, τ, rfl, hτ⟩ := hdec y
    have heq : ∑ s, ((e : ℤ_[l]) * a s - (e : ℤ_[l]) * (l : ℤ_[l]) ^ k * b s) • c s = 0 := by
      have h1 := congrArg (fun v => (e : ℤ_[l]) • v) hy
      simp only [smul_add, Finset.smul_sum, smul_smul] at h1
      have h2 : (e : ℤ_[l]) • (l : ℤ_[l]) ^ k • τ = 0 := by
        rw [smul_comm, Nat.cast_smul_eq_nsmul, hτ, smul_zero]
      rw [smul_smul] at h2
      rw [h2, add_zero] at h1
      simp only [sub_smul, Finset.sum_sub_distrib, h1, mul_assoc, sub_self]
    have hs := Fintype.linearIndependent_iff.mp hli _ heq
    have ht0 : t = 0 := by
      funext s
      have h3 : a s = (l : ℤ_[l]) ^ k * b s := by
        have h4 := hs s
        rw [sub_eq_zero, mul_assoc] at h4
        exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr he.ne') h4
      rw [← congrFun hat s]
      simp only [h3, map_mul, map_pow, map_natCast, Pi.zero_apply]
      rw [show ((l : ZMod (l ^ k)) ^ k) = ((l ^ k : ℕ) : ZMod (l ^ k)) by push_cast; rfl, ZMod.natCast_self, zero_mul]
    rw [ht0, smul_zero]
  · intro z
    obtain ⟨x, hx⟩ := hcok k z
    obtain ⟨a, τ, rfl, hτ⟩ := hdec x
    refine ⟨fun s => PadicInt.toZModPow k ((e : ℤ_[l]) * a s), ?_⟩
    rw [← lev_comb, mul_smul, ← hx]
    have key : ∀ w, lev l (e • w) k = e • lev l w k := fun w => map_nsmul (levH l E n i k) e w
    rw [← key, smul_add, hτ, add_zero, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_smul, Nat.cast_smul_eq_nsmul]

end LateralTheory.KummerTheory
