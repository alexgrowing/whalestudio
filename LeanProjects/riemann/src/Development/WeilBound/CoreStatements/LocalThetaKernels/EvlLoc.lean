import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.GoodCharIsLocallyConstant
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.IntegrablePair
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.CyclicAndLine
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsEqMulApplyZero
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsInvariantForm
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DualNumberGraphFiltrationIsotropicOfSkew

noncomputable section

open Matrix GlobalTheory.WeilM MeasureTheory

namespace PositivityTheory.ThKH.Evl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ : Type} [Fintype κ] {ψ : AddChar k ℂ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem schr_schr (w w' : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : k) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add,
    ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc, add_dotProduct, dotProduct_add]
  congr 2
  have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

theorem schr_mem (hc : Continuous ψ) (w : (κ → k) × (κ → k)) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    schr ψ w φ ∈ SB (κ → k) := by
  have := nonarch_field k
  have hlc := isLocallyConstant_addChar ψ hc
  have h1 : IsLocallyConstant fun x : κ → k => ψ (x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)) :=
    hlc.comp_continuous ((continuous_id.dotProduct continuous_const).add continuous_const)
  exact ⟨h1.mul (hφ.1.comp_continuous (continuous_id.add continuous_const)),
    (hφ.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left⟩

omit [Invertible (2 : k)] in
theorem t2Space_local_field_bis : T2Space k := by
  let := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

theorem cyc (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (h1 : ψ ≠ 1) {φ₀ : (κ → k) → ℂ} (h₀ : φ₀ ∈ SB (κ → k)) (hne : φ₀ ≠ 0)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w, l (schr ψ w φ₀) = 0) : ∀ φ ∈ SB (κ → k), l φ = 0 := by
  have := t2Space_local_field_bis (k := k)
  obtain ⟨u, hu⟩ := (GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar k).2 ψ hc hn h1
  let d : Darboux (R := k) (W := (κ → k) × (κ → k)) (fun w w' => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) κ :=
    ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩
  let : MeasurableSpace (κ → k) := borel _
  have : BorelSpace (κ → k) := ⟨rfl⟩
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.SchrSys.exists_isModel ψ _ u d Measure.addHaar hu inferInstance
  have hcyc := (GlobalTheory.CompanionTheory.VacLoc.ModelLine.cyclic_and_line ψ _ u d _ S ⊥ (fun _ => 1) ⟨φ₀, h₀⟩ ⟨φ₀, h₀⟩ hu hS).1
    (fun h => hne (congrArg Subtype.val h))
  intro φ hφ
  have hle : Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) ≤ LinearMap.ker (l ∘ₗ (SB (κ → k)).subtype) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show l _ = 0
    rw [Submodule.subtype_apply, hS.1]
    exact hl w
  have hm : (⟨φ, hφ⟩ : SB (κ → k)) ∈ Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) := by
    rw [show Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) = ⊤ from hcyc]
    trivial
  exact hle hm

theorem core (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (h1 : ψ ≠ 1) {φ₀ : (κ → k) → ℂ} (h₀ : φ₀ ∈ SB (κ → k)) (hne : φ₀ ≠ 0)
    (A : Set ((κ → k) × (κ → k))) (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hA : ∀ a ∈ A, ∀ φ ∈ SB (κ → k), l (schr ψ a φ) = l φ)
    (hs : ∀ w, ∃ a ∈ A, ∃ b, w = a + b ∧ ((∃ c : ℂ, schr ψ b φ₀ = c • φ₀) ∨
      ∃ a' ∈ A, schr ψ a' φ₀ = φ₀ ∧ ψ (a'.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a'.2) ≠ 1))
    (hl : l φ₀ = 0) : ∀ φ ∈ SB (κ → k), l φ = 0 := by
  have hne0 : ∀ x, ψ x ≠ 0 := fun x h => by simpa [h] using hn x
  refine cyc hc hn h1 h₀ hne l fun w => ?_
  obtain ⟨a, ha, b, rfl, hb⟩ := hs w
  have e := hA a ha _ (schr_mem hc b h₀)
  rw [schr_schr, map_smul, smul_eq_mul] at e
  suffices h : l (schr ψ b φ₀) = 0 from (mul_eq_zero.1 (e.trans h)).resolve_left (hne0 _)
  rcases hb with ⟨c, hc'⟩ | ⟨a', ha', hfix, hψ⟩
  · rw [hc', map_smul, hl, smul_zero]
  · have e1 := hA a' ha' _ (schr_mem hc b h₀)
    rw [schr_schr, map_smul, smul_eq_mul] at e1
    have e2 : l (schr ψ b φ₀) = l (schr ψ b (schr ψ a' φ₀)) := by rw [hfix]
    rw [schr_schr, map_smul, smul_eq_mul, add_comm b a'] at e2
    set t := a'.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a'.2 with ht
    have e3 : ψ (⅟(2 : k) * t) = ψ t * ψ (⅟(2 : k) * (b.1 ⬝ᵥ a'.2 - a'.1 ⬝ᵥ b.2)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
      rw [ht]
      linear_combination (a'.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a'.2) * h2
    rw [e3, mul_assoc, ← e2] at e1
    have : (ψ t - 1) * l (schr ψ b φ₀) = 0 := by linear_combination e1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hψ)

omit [Invertible (2 : k)] in

theorem exists_subgroup (κ : Type) [Fintype κ] : ∃ U : AddSubgroup (κ → k), IsCompact (U : Set (κ → k)) ∧
    (U : Set (κ → k)).indicator (fun _ => (1 : ℂ)) ∈ SB (κ → k) := by
  have := t2Space_local_field_bis (k := k)
  have := nonarch_pi k κ
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : κ → k)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean K hK0
  have hcl : IsClopen (V : Set (κ → k)) := V.isClopen
  have hcp : IsCompact (V : Set (κ → k)) := hK.of_isClosed_subset hcl.1 hV
  exact ⟨V, hcp, (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant,
    HasCompactSupport.intro hcp fun x hx => Set.indicator_of_notMem hx _⟩

theorem transl (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (h1 : ψ ≠ 1) (U : AddSubgroup (κ → k))
    (hU : (U : Set (κ → k)).indicator (fun _ => (1 : ℂ)) ∈ SB (κ → k)) (L : ((κ → k) → ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ t, ∀ f ∈ SB (κ → k), L (fun x => f (x + t)) = L f) (h0 : L ((U : Set (κ → k)).indicator fun _ => 1) = 0) :
    ∀ f ∈ SB (κ → k), L f = 0 := by
  have e : ∀ (t : κ → k) (f : (κ → k) → ℂ), schr ψ (t, 0) f = fun x => f (x + t) := fun t f => by
    funext x; simp [schr]
  refine core hc hn h1 hU (fun h => by simpa using congrFun h 0) (Set.range fun t => (t, 0)) L ?_ ?_ h0
  · rintro _ ⟨t, rfl⟩ f hf
    rw [e, hL t f hf]
  · intro w
    refine ⟨(w.1, 0), ⟨_, rfl⟩, (0, w.2), by simp, ?_⟩
    by_cases h : ∀ u ∈ U, ψ (u ⬝ᵥ w.2) = 1
    · refine Or.inl ⟨1, funext fun x => ?_⟩
      by_cases hx : x ∈ U
      · simp [schr, h x hx]
      · simp [schr, hx]
    · push Not at h
      obtain ⟨u, hu, h⟩ := h
      refine Or.inr ⟨(u, 0), ⟨_, rfl⟩, ?_, by simpa using h⟩
      rw [e]
      funext x
      by_cases hx : x ∈ U
      · have : x + u ∈ U := U.add_mem hx hu
        simp [hx, this]
      · have : x + u ∉ U := fun h' => hx ((U.add_mem_cancel_right hu).1 h')
        simp [hx, this]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] in

theorem mem_of_orth (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ)
    (z : (κ → k) × (κ → k)) (hz : ∀ w ∈ large₂, w.1 ⬝ᵥ z.2 = z.1 ⬝ᵥ w.2) : z ∈ large₂ := by
  classical
  let Ω : ((κ → k) × (κ → k)) →ₗ[k] Module.Dual k ((κ → k) × (κ → k)) :=
    LinearMap.mk₂ k (fun z w => w.1 ⬝ᵥ z.2 - z.1 ⬝ᵥ w.2)
      (fun a b c => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun a b c => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
      (fun a b c => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun a b c => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
  have hinj : Function.Injective Ω := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simpa [Ω] using LinearMap.congr_fun ha (0, Pi.single i 1)
    · simpa [Ω] using LinearMap.congr_fun ha (Pi.single i 1, 0)
  have hmem : ∀ z : (κ → k) × (κ → k), (∀ w ∈ large₂, w.1 ⬝ᵥ z.2 = z.1 ⬝ᵥ w.2) → Ω z ∈ large₂.dualAnnihilator := fun z hz => by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    exact sub_eq_zero.2 (hz w hw)
  have hle : large₂.map Ω ≤ large₂.dualAnnihilator := by
    rintro _ ⟨w, hw, rfl⟩
    exact hmem w fun w' hw' => hiso w' hw' w hw
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq large₂
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hdim] at h1
  have h2 : Module.finrank k (large₂.map Ω) = Module.finrank k large₂.dualAnnihilator := by
    rw [← (Submodule.equivMapOfInjective Ω hinj large₂).finrank_eq, hdim]
    omega
  have h3 := Submodule.eq_of_le_of_finrank_eq hle h2
  obtain ⟨w, hw, e⟩ : Ω z ∈ large₂.map Ω := h3 ▸ hmem z hz
  exact hinj e ▸ hw

theorem exists_test (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (h1 : ψ ≠ 1) (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ) :
    ∃ φ₀ : (κ → k) → ℂ, ∀ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ) → l φ₀ = 0 →
      ∀ φ ∈ SB (κ → k), l φ = 0 := by
  classical
  have := t2Space_local_field_bis (k := k)
  have := nonarch_field k
  have hlc := isLocallyConstant_addChar ψ hc
  have hne0 : ∀ x, ψ x ≠ 0 := fun x h => by simpa [h] using hn x
  obtain ⟨n, j, σ, p, hp, hσ, hj⟩ := GlobalTheory.CompanionTheory.LagFun.exists_param large₂
  obtain ⟨U, hUc, hU⟩ := exists_subgroup (k := k) κ
  obtain ⟨V, -, hV⟩ := exists_subgroup (k := k) (Fin n)
  have cj : Continuous j := j.continuous_on_pi
  have cσ : Continuous σ := σ.continuous_on_pi
  have cp : Continuous p := p.continuous_on_pi
  have hce : Topology.IsClosedEmbedding j := Function.LeftInverse.isClosedEmbedding hp cp cj
  set g : (Fin n → k) → ℂ := fun t => ψ (⅟(2 : k) * (j t ⬝ᵥ σ t)) with hg
  have lg : IsLocallyConstant g := hlc.comp_continuous (continuous_const.mul (cj.dotProduct cσ))
  set χ : (κ → k) → ℂ := (U : Set (κ → k)).indicator (fun _ => (1 : ℂ)) with hχ
  let ext : ((Fin n → k) → ℂ) →ₗ[ℂ] ((κ → k) → ℂ) :=
    { toFun := fun f x => (g (p x))⁻¹ * f (p x) * χ (x - j (p x))
      map_add' := fun a b => by funext x; simp only [Pi.add_apply]; ring
      map_smul' := fun a b => by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have ext_apply : ∀ f x, ext f x = (g (p x))⁻¹ * f (p x) * χ (x - j (p x)) := fun _ _ => rfl
  have ext_j : ∀ f t, g t * ext f (j t) = f t := fun f t => by
    rw [ext_apply, hp, sub_self, hχ, Set.indicator_of_mem U.zero_mem, mul_one, mul_inv_cancel_left₀ (hne0 _)]
  have ext_mem : ∀ f ∈ SB (Fin n → k), ext f ∈ SB (κ → k) := fun f hf => by
    refine ⟨(((lg.comp fun z => z⁻¹).comp_continuous cp).mul (hf.1.comp_continuous cp)).mul
      (hU.1.comp_continuous (continuous_id.sub (cj.comp cp))), ?_⟩
    refine HasCompactSupport.intro ((hf.2.prod hUc).image
      (f := fun q : (Fin n → k) × (κ → k) => j q.1 + q.2) ((cj.comp continuous_fst).add continuous_snd)) fun x hx => ?_
    by_contra h
    rw [ext_apply] at h
    have h2 := mul_ne_zero_iff.1 h
    have h3 : x - j (p x) ∈ U := by
      by_contra h4
      exact h2.2 (Set.indicator_of_notMem h4 _)
    exact hx ⟨(p x, x - j (p x)), ⟨subset_tsupport _ (mul_ne_zero_iff.1 h2.1).2, h3⟩, by simp⟩
  have res_mem : ∀ φ ∈ SB (κ → k), (fun t => g t * φ (j t)) ∈ SB (Fin n → k) := fun φ hφ =>
    ⟨lg.mul (hφ.1.comp_continuous cj), (hφ.2.comp_isClosedEmbedding hce).mul_left⟩
  refine ⟨ext ((V : Set (Fin n → k)).indicator fun _ => 1), fun l hl h0 => ?_⟩
  have van : ∀ φ ∈ SB (κ → k), (∀ t, φ (j t) = 0) → l φ = 0 := fun φ hφ hz => by
    refine eq_zero_of_mul_invariant l {f | ∃ y, (0, y) ∈ large₂ ∧ f = fun x => ψ (x ⬝ᵥ y)} ?_ ?_ hφ ?_
    · rintro _ ⟨y, -, rfl⟩
      exact hlc.comp_continuous (continuous_id.dotProduct continuous_const)
    · rintro _ ⟨y, hy, rfl⟩ φ' hφ'
      rw [← hl _ hy φ' hφ']
      congr 1
      funext x
      simp [schr]
    · intro x hx
      have hx' : x - j (p x) ≠ 0 := fun h => hx (by rw [sub_eq_zero.1 h]; exact hz _)
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hx'
      have hi' : (x - j (p x)) i ≠ 0 := hi
      obtain ⟨s, hs⟩ := DFunLike.ne_iff.1 h1
      let f : (κ → k) →ₗ[k] k := (s / (x - j (p x)) i) • (LinearMap.proj i ∘ₗ (LinearMap.id - j ∘ₗ p))
      have hf : ∀ z, z ⬝ᵥ (fun a => f (Pi.single a 1)) = f z := fun z => by
        rw [LinearMap.pi_apply_eq_sum_univ f z, dotProduct]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_eq_mul]
        congr 2
        funext b
        simp [Pi.single_apply, eq_comm]
      refine ⟨_, ⟨fun a => f (Pi.single a 1), mem_of_orth large₂ hiso hdim _ fun w hw => ?_, rfl⟩, ?_⟩
      · obtain ⟨t, ht⟩ := hj w hw
        rw [hf, ← ht]
        simp [f, hp]
      · have : f x = s := by
          show (s / (x - j (p x)) i) * (x - j (p x)) i = s
          exact div_mul_cancel₀ _ hi'
        simpa only [hf, this, AddChar.one_apply] using hs
  have key : ∀ φ ∈ SB (κ → k), l φ = l (ext fun t => g t * φ (j t)) := fun φ hφ => by
    rw [← sub_eq_zero, ← map_sub]
    refine van _ (Submodule.sub_mem _ hφ (ext_mem _ (res_mem φ hφ))) fun t => ?_
    refine mul_left_cancel₀ (hne0 (⅟(2 : k) * (j t ⬝ᵥ σ t))) ?_
    have := ext_j (fun t => g t * φ (j t)) t
    rw [Pi.sub_apply, mul_sub, mul_zero, sub_eq_zero]
    exact this.symm
  have hT := transl hc hn h1 V hV (l ∘ₗ ext) (fun t₁ f hf => by
    have e : (fun t => g t * schr ψ (j t₁, σ t₁) (ext f) (j t)) = fun t => f (t + t₁) := by
      funext t
      rw [← ext_j f (t + t₁)]
      have e3 := hiso _ (hσ t) _ (hσ t₁)
      simp only [hg, schr, map_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add] at e3 ⊢
      congr 2
      have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
      linear_combination ⅟(2 : k) * e3 - (j t ⬝ᵥ σ t₁) * h2
    show l (ext _) = l (ext f)
    rw [← e, ← key _ (schr_mem hc _ (ext_mem f hf)), hl _ (hσ t₁) _ (ext_mem f hf)]) h0
  intro φ hφ
  rw [key φ hφ]
  exact hT _ (res_mem φ hφ)

theorem line (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (h1 : ψ ≠ 1) (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ)
    (l l' : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ)
    (hl' : ∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l' (schr ψ w φ) = l' φ) (hne : ∃ φ ∈ SB (κ → k), l φ ≠ 0) :
    ∃ c : ℂ, ∀ φ ∈ SB (κ → k), l' φ = c * l φ := by
  obtain ⟨φ₀, h⟩ := exists_test hc hn h1 large₂ hiso hdim
  obtain ⟨φ₁, hφ₁, h₁⟩ := hne
  have h0 : l φ₀ ≠ 0 := fun e => h₁ (h l hl e φ₁ hφ₁)
  refine ⟨l' φ₀ / l φ₀, fun φ hφ => ?_⟩
  have := h (l' - (l' φ₀ / l φ₀) • l) (fun w hw φ hφ => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hl w hw φ hφ, hl' w hw φ hφ]) (by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0, sub_self]) φ hφ
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero] using this

end PositivityTheory.ThKH.Evl
