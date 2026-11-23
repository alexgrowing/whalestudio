import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.TemperednessTransfer

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Module
open PositivityTheory.Pf1.CLGD.DescRes LocalGlobalAboveLAlt

namespace GlobalTheory.CompanionTheory.TempRes

section Lin

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem iSup_eigenspace_eq_top {f : End ℂ V} (hf : f.IsSemisimple) : ⨆ α, f.eigenspace α = ⊤ := by
  have h := Module.End.iSup_maxGenEigenspace_eq_top f
  simp_rw [hf.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h
  exact h

theorem mem_eigenspace_pow {f : End ℂ V} {α : ℂ} {v : V} (hv : v ∈ f.eigenspace α) (M : ℕ) :
    v ∈ (f ^ M).eigenspace (α ^ M) := by
  rw [End.mem_eigenspace_iff] at hv ⊢
  induction M with
  | zero => simp
  | succ n ih => rw [pow_succ, End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem absSpace_le_pow (f : End ℂ V) (t : ℝ) (M : ℕ) : absSpace f t ≤ absSpace (f ^ M) (t ^ M) := by
  refine iSup₂_le fun α hα v hv => ?_
  exact Submodule.mem_iSup_of_mem (α ^ M) (Submodule.mem_iSup_of_mem (by rw [norm_pow, hα])
    (mem_eigenspace_pow hv M))

theorem absSpace_pow_eq {f : End ℂ V} (hf : f.IsSemisimple) {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : M ≠ 0) :
    absSpace (f ^ M) (t ^ M) = absSpace f t := by
  set S : Set ℂ := {β | ‖β‖ = t ^ M} with hS
  set b : Submodule ℂ V := ⨆ (α : ℂ) (_ : ‖α‖ ≠ t), f.eigenspace α with hb
  have hbW : b ≤ ⨆ β ∈ Sᶜ, (f ^ M).eigenspace β := by
    refine iSup₂_le fun α hα v hv => ?_
    refine Submodule.mem_iSup_of_mem (α ^ M) (Submodule.mem_iSup_of_mem ?_ (mem_eigenspace_pow hv M))
    intro h
    have h' : ‖α‖ ^ M = t ^ M := by simpa [hS, norm_pow] using h
    exact hα ((pow_left_inj₀ (norm_nonneg _) ht hM).mp h')
  have hab : absSpace f t ⊔ b = ⊤ := by
    rw [eq_top_iff, ← iSup_eigenspace_eq_top hf]
    refine iSup_le fun α => ?_
    by_cases hα : ‖α‖ = t
    · exact le_sup_of_le_left (le_iSup₂_of_le α hα le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)
  have hd : Disjoint (absSpace (f ^ M) (t ^ M)) (⨆ β ∈ Sᶜ, (f ^ M).eigenspace β) :=
    (End.eigenspaces_iSupIndep (f ^ M)).disjoint_biSup_biSup (s := S) (t := Sᶜ) disjoint_compl_right
  refine le_antisymm ?_ (absSpace_le_pow f t M)
  have e : absSpace (f ^ M) (t ^ M) = absSpace f t ⊔ (b ⊓ absSpace (f ^ M) (t ^ M)) := by
    rw [← sup_inf_assoc_of_le _ (absSpace_le_pow f t M), hab, top_inf_eq]
  have e0 : b ⊓ absSpace (f ^ M) (t ^ M) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ hbW).trans (by rw [inf_comm]; exact hd.le_bot))
  rw [e0, sup_bot_eq] at e
  exact e.le

end Lin

section Weil

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem exists_pow_eq (a : WDRep h V) {φ ψ : Weil h} {d : ℕ} (hφ : deg φ = 1) (hψ : deg ψ = d) :
    ∃ M : ℕ, 0 < M ∧ a.ρ ψ ^ M = a.ρ φ ^ (d * M) := by
  have key : ∀ n k : ℕ, 0 < k → a.ρ (ψ ^ (n + k) * (φ ^ (d * (n + k)))⁻¹) = a.ρ (ψ ^ n * (φ ^ (d * n))⁻¹) →
      ∃ M : ℕ, 0 < M ∧ a.ρ ψ ^ M = a.ρ φ ^ (d * M) := by
    intro n k hk e
    refine ⟨k, hk, ?_⟩
    have e1 : ψ ^ k = (ψ ^ n)⁻¹ * (ψ ^ (n + k) * (φ ^ (d * (n + k)))⁻¹) * φ ^ (d * (n + k)) := by
      rw [pow_add]; group
    have e2 : φ ^ (d * k) = (ψ ^ n)⁻¹ * (ψ ^ n * (φ ^ (d * n))⁻¹) * φ ^ (d * (n + k)) := by
      rw [mul_add, pow_add]; group
    rw [← map_pow, ← map_pow, e1, e2, map_mul, map_mul, e, ← map_mul, ← map_mul]
  have hdeg : ∀ n : ℕ, deg (ψ ^ n * (φ ^ (d * n))⁻¹) = 0 := fun n => by
    simp [hφ, hψ, mul_comm]
  let u : ℕ → Ine (F := E) A := fun n => ⟨((ψ ^ n * (φ ^ (d * n))⁻¹ : Weil h) : G E Ω), deg_eq_zero_iff.mp (hdeg n)⟩
  have hu : ∀ n, ineIncl h (u n) = ψ ^ n * (φ ^ (d * n))⁻¹ := fun n => Subtype.ext rfl
  have hfin : Finite (Set.range fun σ : Ine (F := E) A => a.ρ (ineIncl h σ)) := a.smooth.finite_range
  obtain ⟨m, n, hne, hmn⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨a.ρ (ineIncl h (u k)), u k, rfl⟩ :
      Set.range fun σ : Ine (F := E) A => a.ρ (ineIncl h σ)))
  have hmn' : a.ρ (ψ ^ m * (φ ^ (d * m))⁻¹) = a.ρ (ψ ^ n * (φ ^ (d * n))⁻¹) := by
    have := congrArg Subtype.val hmn
    simpa only [hu] using this
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact key m (k + 1) (by omega) (by rw [← add_assoc]; exact hmn'.symm)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact key n (k + 1) (by omega) (by rw [← add_assoc]; exact hmn')

theorem isPurePair_iff (a : WDRep h V) {φ ψ : Weil h} {f : ℕ} (hf : f ≠ 0) (hφ : deg φ = 1) (hψ : deg ψ = f) :
    IsPurePair (((normV w : ℕ) : ℝ) ^ f) (a.ρ ψ) a.N ↔ IsPurePair ((normV w : ℕ) : ℝ) (a.ρ φ) a.N := by
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  have hs : ∀ r : ℝ, 0 ≤ r → absSpace (a.ρ ψ) (r ^ f) = absSpace (a.ρ φ) r := by
    intro r hr
    obtain ⟨M, hM, e⟩ := exists_pow_eq a hφ hψ
    rw [← absSpace_pow_eq (a.semisimple ψ) (pow_nonneg hr f) hM.ne', e, ← pow_mul,
      absSpace_pow_eq (a.semisimple φ) hr (mul_ne_zero hf hM.ne')]
  have hs' : ∀ x : ℝ, absSpace (a.ρ ψ) ((((normV w : ℕ) : ℝ) ^ f) ^ x) = absSpace (a.ρ φ) (((normV w : ℕ) : ℝ) ^ x) := by
    intro x
    rw [← hs _ (Real.rpow_nonneg hq x), ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq,
      ← Real.rpow_mul hq, mul_comm]
  unfold IsPurePair
  simp only [hs']

end Weil

section Res

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem resF_ne_zero : resF h h' ≠ 0 := by
  intro h0
  have e := normV_eq_pow_resF h h'
  rw [h0, pow_zero] at e
  exact (one_lt_normV w').ne' e

theorem tempered_resRep (a : WDRep h V) : (resRep h h' a).Tempered ↔ a.Tempered := by
  have hq : ((normV w' : ℕ) : ℝ) = ((normV w : ℕ) : ℝ) ^ resF h h' := by
    rw [normV_eq_pow_resF h h']; push_cast; rfl
  have hd : deg (resW h h' (frob h')) = (resF h h' : ℕ) := by
    rw [deg_resW, deg_frob, mul_one]
  constructor
  · intro ht φ hφ
    have h1 := ht (frob h') deg_frob
    rw [hq] at h1
    exact (isPurePair_iff a (resF_ne_zero h h') hφ hd).mp h1
  · intro ht φ' hφ'
    rw [hq]
    have hd' : deg (resW h h' φ') = (resF h h' : ℕ) := by rw [deg_resW, hφ', mul_one]
    exact (isPurePair_iff a (resF_ne_zero h h') deg_frob hd').mpr (ht _ deg_frob)

theorem normV_cpow (s : ℝ) :
    ((normV w' : ℕ) : ℂ) ^ ((s : ℝ) : ℂ) = (((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) ^ resF h h' := by
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [normV_eq_pow_resF h h', Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
    ← Complex.ofReal_cpow (pow_nonneg hq _), ← Complex.ofReal_cpow hq, ← Complex.ofReal_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq, ← Real.rpow_mul hq, mul_comm]

theorem iso_res_tw (a : WDRep h V) (s : ℝ) : ((resRep h h' a).tw s).Iso (resRep h h' (a.tw s)) := by
  refine ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  simp only [LinearEquiv.refl_apply, WDRep.tw_ρ, resRep_ρ, deg_resW, LinearMap.smul_apply]
  rw [zpow_mul, zpow_natCast, normV_cpow h h']

end Res

theorem tempRes : TempRes := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ A w w' h h' x s
  induction x using WD.ind with
  | hP n a =>
    rw [WD.res_mk, WD.lpTw_mk, WD.lpTw_mk, WD.tempered_mk, WD.tempered_mk]
    exact ⟨fun ht => (tempered_resRep h h' (a.tw s)).mp ((iso_res_tw h h' a s).tempered ht),
      fun ht => (iso_res_tw h h' a s).symm.tempered ((tempered_resRep h h' (a.tw s)).mpr ht)⟩

end GlobalTheory.CompanionTheory.TempRes
