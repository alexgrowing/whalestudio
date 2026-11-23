import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.PairSpan

section Abstract

variable {Γ k : Type} [Group Γ] [Field k]

theorem alt_left_nondeg {v : Fin 2 → k} (hv : v ≠ 0) : ∃ a : Fin 2 → k, v 0 * a 1 - v 1 * a 0 ≠ 0 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; funext i; fin_cases i <;> simp [h0, h1]
    exact ⟨![1, 0], by simp [h1]⟩
  · exact ⟨![0, 1], by simp [h0]⟩

theorem stable_cases {W : Γ →* GL (Fin 2) k} {H : Subgroup Γ} (hirr : UpperTheory.V.Af.IsIrr (W.comp H.subtype))
    (U : Submodule k (Fin 2 → k)) (hU : ∀ s ∈ H, ∀ v ∈ U, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ U) :
    U = ⊥ ∨ U = ⊤ :=
  hirr.2.2 U le_top (by intro g v hv; exact hU g g.2 v hv)

theorem coc_conj {n : ℕ} (ρ : Γ →* GL (Fin n) k) (y : Γ → Fin n → k)
    (hy : ∀ g h, y (g * h) = y g + (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ y h) (s g : Γ) (hg : ρ g = 1) :
    y (s * g * s⁻¹) = (ρ s : Matrix (Fin n) (Fin n) k) *ᵥ y g := by
  have h1 : y 1 = 0 := by simpa using hy 1 1
  have h2 : y s + (ρ s : Matrix (Fin n) (Fin n) k) *ᵥ y s⁻¹ = 0 := by rw [← hy, mul_inv_cancel, h1]
  rw [hy, hy, map_mul, hg, mul_one, add_right_comm, h2, zero_add]

end Abstract
end GlobalTheory.Ord2.PairSpan

namespace GlobalTheory.Ord2.PairSpan

variable {Γ k : Type} [Group Γ] [Field k]

theorem exists_pair_ne [IsAlgClosed k] [CharZero k] {W : Γ →* GL (Fin 2) k} {H : Subgroup Γ}
    (hirr : UpperTheory.V.Af.IsIrr (W.comp H.subtype)) {N : Set Γ}
    (hN : ∀ s ∈ H, ∀ g ∈ N, s * g * s⁻¹ ∈ N) {y z : Γ → Fin 2 → k}
    (hy : ∀ s ∈ H, ∀ g ∈ N, y (s * g * s⁻¹) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ y g)
    (hz : ∀ s ∈ H, ∀ g ∈ N, z (s * g * s⁻¹) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ z g)
    (hy0 : ∃ g ∈ N, y g ≠ 0) (hz0 : ∃ g ∈ N, z g ≠ 0) :
    ∃ g ∈ N, ∃ h ∈ N, y h 0 * z g 1 - y h 1 * z g 0 ≠ y g 0 * z h 1 - y g 1 * z h 0 := by
  by_contra hcon
  push_neg at hcon
  let Sig : Submodule k ((Fin 2 → k) × (Fin 2 → k)) := Submodule.span k ((fun g => (y g, z g)) '' N)
  have hgen : ∀ g ∈ N, (y g, z g) ∈ Sig := fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have hinv : ∀ s ∈ H, ∀ σ ∈ Sig,
      ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.1, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.2) ∈ Sig := by
    intro s hs σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      rw [← hy s hs g hg, ← hz s hs g hg]
      exact hgen _ (hN s hs g hg)
    | zero =>
      simp only [Prod.fst_zero, Prod.snd_zero, Matrix.mulVec_zero, Prod.mk_zero_zero]
      exact Sig.zero_mem
    | add x x' _ _ ihx ihx' => simpa [Matrix.mulVec_add] using Sig.add_mem ihx ihx'
    | smul a x _ ihx => simpa [Matrix.mulVec_smul] using Sig.smul_mem a ihx
  have hB : ∀ g ∈ N, ∀ σ ∈ Sig, y g 0 * σ.2 1 - y g 1 * σ.2 0 = σ.1 0 * z g 1 - σ.1 1 * z g 0 := by
    intro g hg σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact (hcon g hg h hh).symm
    | zero => simp
    | add x x' _ _ ihx ihx' =>
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      linear_combination ihx + ihx'
    | smul a x _ ihx =>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      linear_combination a * ihx
  let K' : Submodule k (Fin 2 → k) := Sig.comap (LinearMap.inr k (Fin 2 → k) (Fin 2 → k))
  have hK' : K' = ⊥ := by
    rcases stable_cases hirr K' (by
      intro s hs v hv
      have := hinv s hs _ hv
      simpa [K', Matrix.mulVec_zero] using this) with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg, hyg⟩ := hy0
      obtain ⟨a, ha⟩ := alt_left_nondeg hyg
      have hmem : ((0 : Fin 2 → k), a) ∈ Sig := by
        have : a ∈ K' := h ▸ Submodule.mem_top
        simpa [K'] using this
      exact ha ((hB g hg _ hmem).trans (by simp))
  let P : Submodule k (Fin 2 → k) := Sig.map (LinearMap.fst k (Fin 2 → k) (Fin 2 → k))
  have hP : P = ⊤ := by
    rcases stable_cases hirr P (by
      rintro s hs v ⟨σ, hσ, rfl⟩
      exact ⟨_, hinv s hs σ hσ, rfl⟩) with h | h
    · exfalso
      obtain ⟨g, hg, hyg⟩ := hy0
      have : y g ∈ P := ⟨_, hgen g hg, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hyg this
    · exact h
  let f : Sig →ₗ[k] (Fin 2 → k) := (LinearMap.fst k (Fin 2 → k) (Fin 2 → k)).comp Sig.subtype
  have hfi : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun σ hσ => ?_
    have h1 : (σ : (Fin 2 → k) × (Fin 2 → k)).1 = 0 := hσ
    have h2 : (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ K' := by
      show LinearMap.inr k _ _ (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ Sig
      have : LinearMap.inr k (Fin 2 → k) (Fin 2 → k) (σ : (Fin 2 → k) × (Fin 2 → k)).2 = σ := by
        ext1 <;> simp [h1]
      rw [this]; exact σ.2
    rw [hK', Submodule.mem_bot] at h2
    exact Subtype.ext (Prod.ext h1 h2)
  have hfs : Function.Surjective f := by
    intro a
    have : a ∈ P := hP ▸ Submodule.mem_top
    obtain ⟨σ, hσ, rfl⟩ := this
    exact ⟨⟨σ, hσ⟩, rfl⟩
  let e := LinearEquiv.ofBijective f ⟨hfi, hfs⟩
  let φ : Module.End k (Fin 2 → k) :=
    (LinearMap.snd k (Fin 2 → k) (Fin 2 → k)).comp (Sig.subtype.comp e.symm.toLinearMap)
  have hφmem : ∀ a, (a, φ a) ∈ Sig := by
    intro a
    have h1 : ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k)).1 = a := e.apply_symm_apply a
    have : (a, φ a) = ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k)) := Prod.ext h1.symm rfl
    rw [this]; exact (e.symm a).2
  have hφ : ∀ σ ∈ Sig, φ σ.1 = σ.2 := by
    intro σ hσ
    have : e.symm σ.1 = ⟨σ, hσ⟩ := e.symm_apply_eq.2 rfl
    show ((e.symm σ.1 : Sig) : (Fin 2 → k) × (Fin 2 → k)).2 = σ.2
    rw [this]
  have hφW : ∀ s ∈ H, ∀ a, φ ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ a) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ φ a :=
    fun s hs a => hφ _ (hinv s hs _ (hφmem a))
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φ
  have hE : Module.End.eigenspace φ c = ⊤ := by
    rcases stable_cases hirr (Module.End.eigenspace φ c) (by
      intro s hs v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [hφW s hs, hv, Matrix.mulVec_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · exact h
  have hφc : ∀ a, φ a = c • a := fun a => Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top)
  have hzy : ∀ g ∈ N, z g = c • y g := fun g hg => by rw [← hφc]; exact (hφ _ (hgen g hg)).symm
  obtain ⟨g1, hg1, hzg1⟩ := hz0
  have hc0 : c ≠ 0 := by rintro rfl; apply hzg1; rw [hzy g1 hg1, zero_smul]
  obtain ⟨g0, hg0, hyg0⟩ := hy0
  have horth : ∀ h ∈ N, y g0 0 * y h 1 - y g0 1 * y h 0 = 0 := by
    intro h hh
    have := hcon h hh g0 hg0
    rw [hzy h hh, hzy g0 hg0] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h2 : (2 * c) * (y g0 0 * y h 1 - y g0 1 * y h 0) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exfalso; exact hc0 (by simpa using h3)
    · exact h3
  have hall : ∀ σ ∈ Sig, y g0 0 * σ.1 1 - y g0 1 * σ.1 0 = 0 := by
    intro σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact horth h hh
    | zero => simp
    | add x x' _ _ ihx ihx' =>
      simp only [Prod.fst_add, Pi.add_apply]
      linear_combination ihx + ihx'
    | smul a x _ ihx =>
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      linear_combination a * ihx
  obtain ⟨a, ha⟩ := alt_left_nondeg hyg0
  exact ha (hall _ (hφmem a))

end GlobalTheory.Ord2.PairSpan

namespace GlobalTheory.Ord2

open PairSpan in

theorem exists_om_ne_swap_on_N0g : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W),
    ∀ z ∈ Z1 (Loc.colRep (dual1 W)), (∃ g ∈ N0g W, y g ≠ 0) → (∃ g ∈ N0g W, z g ≠ 0) →
    ∃ g ∈ N0g W, ∃ h ∈ N0g W, om (y h) (z g) ≠ om (y g) (z h) := by
  intro l _ Ω _ _ _ e S A W hW y hyZ z hzZ hy0 hz0
  have hy' : ∀ g h, y (g * h) = y g + (W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ y h := fun g h => by
    rw [hyZ.2 g h]; rfl
  have hz' : ∀ g h, z (g * h) = z g + (dual1 W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z h := fun g h => by
    rw [hzZ.2 g h]; rfl
  have hnorm : (N0g W).Normal := by unfold N0g; infer_instance
  have hdual : ∀ s, cycBar ℚ Ω l s = 1 → dt W s = 1 → dual1 W s = W s := by
    intro s h1 h2
    apply Units.ext
    rw [dual1, tw_val]
    simp [h1, h2]
  have hN1 : ∀ g ∈ N0g W, W g = 1 := fun g hg => (Subgroup.mem_inf.1 hg).2
  have hNd : ∀ g ∈ N0g W, dual1 W g = 1 := by
    intro g hg
    have h1 : cycBar ℚ Ω l g = 1 := (Subgroup.mem_inf.1 hg).1
    have h2 : dt W g = 1 := by
      show Matrix.GeneralLinearGroup.det (W g) = 1
      rw [hN1 g hg, map_one]
    rw [hdual g h1 h2, hN1 g hg]
  have hH : ∀ s ∈ H0g W, dual1 W s = W s := fun s hs =>
    hdual s (Subgroup.mem_inf.1 hs).1 (Subgroup.mem_inf.1 hs).2
  obtain ⟨g, hg, h, hh, hne⟩ := exists_pair_ne (k := Qbar l) (W := W) (H := H0g W) (N := (N0g W : Set (G ℚ Ω)))
    hW.irr (fun s _ g hg => hnorm.conj_mem g hg s)
    (y := y) (z := z)
    (fun s _ g hg => coc_conj W y hy' s g (hN1 g hg))
    (fun s hs g hg => by rw [coc_conj (dual1 W) z hz' s g (hNd g hg), hH s hs])
    hy0 hz0
  exact ⟨g, hg, h, hh, hne⟩

end GlobalTheory.Ord2

end
