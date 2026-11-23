import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocF
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemClosureHeckeSplitCongruenceOfFinPartOne
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF Topology Filter
open Formalism.IndefR.Fin.U1 GlobalTheory.HeckeSplitAll GlobalTheory.HeckeSplitAll.Approx
open scoped TensorProduct

namespace GlobalTheory.HeckeSplitGen

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_mkEF (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ) (a b : AF F) :
    cAF σ (mkE (F := F) δ (AF F) a b) = mkE (F := F) δ (AF F) a (-b) :=
  conj_mkE σ δ hδ (AF F) a b

theorem finPartF_mkE (δ : E) (a b : AF F) :
    finPartF F E (mkE (F := F) δ (AF F) a b) = mkE (F := F) δ (Af F) a.2 b.2 :=
  map_mkE (sndA F) δ a b

theorem infPartF_mkE (δ : E) (a b : AF F) :
    infPartF F E (mkE (F := F) δ (AF F) a b) = mkE (F := F) δ (Ainf F) a.1 b.1 :=
  map_mkE (fstA F) δ a b

theorem incAF_eq_mkE (δ : E) (α β : F) :
    incAF F E (algebraMap F E α + algebraMap F E β * δ) =
      mkE (F := F) δ (AF F) (algebraMap F (AF F) α) (algebraMap F (AF F) β) :=
  incl_eq_mkE δ (AF F) α β

theorem cut_mkE (δ : E) (ε a b : AF F) :
    algebraMap (AF F) (AEF F E) ε * mkE (F := F) δ (AF F) a b + (1 - algebraMap (AF F) (AEF F E) ε) =
      mkE (F := F) δ (AF F) (ε * a + (1 - ε)) (ε * b) := by
  rw [← map_one (algebraMap (AF F) (AEF F E)), ← map_sub, smul_mkE,
    algebraMap_eq_mkE δ (AF F) (1 - ε), mkE_add, add_zero]

theorem isModTopF : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩

theorem continuous_mkEF (δ : E) :
    Continuous fun p : AF F × AF F => mkE (F := F) δ (AF F) p.1 p.2 := by
  have := isModTopF (F := F) (E := E)
  have hA : ContinuousAdd (AEF F E) := IsModuleTopology.toContinuousAdd (AF F) (AEF F E)
  have hS : ContinuousSMul (AF F) (AEF F E) := IsModuleTopology.toContinuousSMul (AF F) (AEF F E)
  have e : ∀ p : AF F × AF F, mkE (F := F) δ (AF F) p.1 p.2 =
      p.1 • ((1 : AF F) ⊗ₜ[F] (1 : E)) + p.2 • ((1 : AF F) ⊗ₜ[F] δ) := fun p => by
    simp only [mkE, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp only [e]
  exact ((continuous_fst (X := AF F) (Y := AF F)).smul
    (continuous_const (y := ((1 : AF F) ⊗ₜ[F] (1 : E))))).add
    ((continuous_snd (X := AF F) (Y := AF F)).smul (continuous_const (y := ((1 : AF F) ⊗ₜ[F] δ))))

theorem tendsto_mkEF (δ : E) {A B : ℕ → AF F} {a b : AF F} (hA : Tendsto A atTop (𝓝 a))
    (hB : Tendsto B atTop (𝓝 b)) :
    Tendsto (fun k => mkE (F := F) δ (AF F) (A k) (B k)) atTop (𝓝 (mkE (F := F) δ (AF F) a b)) := by
  have := ((continuous_mkEF (E := E) δ).tendsto (a, b)).comp (hA.prodMk_nhds hB)
  simpa only [Function.comp_def] using this

theorem mkE_mem_intAEF (δ : 𝓞 E) (a b : Af F) (ha : ∀ v, ‖a v‖ ≤ 1) (hb : ∀ v, ‖b v‖ ≤ 1) :
    mkE (F := F) (δ : E) (Af F) a b ∈ intAEF F E :=
  add_mem (AddSubgroup.subset_closure ⟨a, fun v => (norm_le_one_iff_int v _).1 (ha v), 1, rfl⟩)
    (AddSubgroup.subset_closure ⟨b, fun v => (norm_le_one_iff_int v _).1 (hb v), δ, rfl⟩)

theorem exists_splitIdemF (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ) (hδ0 : δ ≠ 0) (Δ : F)
    (hΔ : algebraMap F E Δ = δ * δ) (v : HeightOneSpectrum (𝓞 F)) (s : v.adicCompletion F)
    (hs : s * s = algebraMap F (v.adicCompletion F) Δ) :
    ∃ e, IsSplitIdemF σ e ∧ e + cAF σ e = algebraMap (AF F) (AEF F E) (epv v) := by
  have hcA : ∀ a b, cAF σ (mkE (F := F) δ (AF F) a b) = mkE (F := F) δ (AF F) a (-b) := conj_mkEF σ δ hδ
  have hΔ0 : Δ ≠ 0 := by
    intro h; rw [h, map_zero] at hΔ; exact hδ0 (mul_self_eq_zero.mp hΔ.symm)
  have hs0 : s ≠ 0 := by
    intro h; rw [h, mul_zero] at hs
    exact hΔ0 ((map_eq_zero_iff _ (algebraMap F (v.adicCompletion F)).injective).mp hs.symm)
  set a : AF F := pairA F 0 (single v (1 / 2)) with ha
  set b : AF F := pairA F 0 (single v (1 / (2 * s))) with hb
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have := (algebraMap F (v.adicCompletion F)).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at this
  have e1 : a * a + algebraMap F (AF F) Δ * (b * b) = a := by
    rw [ha, hb, algebraMap_AF, pairA_mul, pairA_mul, pairA_mul, pairA_add, pairA_eq_iff]
    refine ⟨by ring, fa_ext fun w => ?_⟩
    simp only [fa_mul, fa_add, af_apply]
    by_cases hw : w = v
    · subst hw
      rw [single_self, single_self, ← hs]; field_simp; ring
    · rw [single_ne _ hw, single_ne _ hw]; ring
  have e2 : a * b + b * a = b := by
    rw [ha, hb, pairA_mul, pairA_mul, pairA_add, pairA_eq_iff]
    refine ⟨by ring, fa_ext fun w => ?_⟩
    simp only [fa_mul, fa_add]
    by_cases hw : w = v
    · subst hw; rw [single_self, single_self]; field_simp; ring
    · rw [single_ne _ hw, single_ne _ hw]; ring
  have e3 : a * a + algebraMap F (AF F) Δ * (b * -b) = 0 := by
    rw [ha, hb, algebraMap_AF, pairA_neg, pairA_mul, pairA_mul, pairA_mul, pairA_add]
    show pairA F _ _ = pairA F 0 0
    rw [pairA_eq_iff]
    refine ⟨by ring, fa_ext fun w => ?_⟩
    simp only [fa_mul, fa_add, fa_neg, af_apply, fa_zero]
    by_cases hw : w = v
    · subst hw; rw [single_self, single_self, ← hs]; field_simp; ring
    · rw [single_ne _ hw, single_ne _ hw]; ring
  have e4 : a * -b + b * a = 0 := by ring
  have e5 : a + a = pairA F 0 (single v 1) := by
    rw [ha, pairA_add, pairA_eq_iff]
    refine ⟨by ring, fa_ext fun w => ?_⟩
    simp only [fa_add]
    by_cases hw : w = v
    · subst hw; rw [single_self, single_self]; field_simp; norm_num
    · rw [single_ne _ hw, single_ne _ hw, add_zero]
  have hsum : mkE (F := F) δ (AF F) a b + cAF σ (mkE (F := F) δ (AF F) a b) =
      algebraMap (AF F) (AEF F E) (epv v) := by
    rw [hcA, mkE_add, add_neg_cancel, e5, algebraMap_eq_mkE]
  refine ⟨mkE (F := F) δ (AF F) a b, ⟨?_, ?_, v, pairA F 0 (single v 1), ?_, hsum⟩, hsum⟩
  · rw [mkE_mul δ Δ hΔ, e1, e2]
  · rw [hcA, mkE_mul δ Δ hΔ, e3, e4]; exact mkE_zero δ (AF F)
  · exact ⟨single v 1, rfl, single_self v 1, fun v' hv' => single_ne 1 hv'⟩

theorem exists_int_deltaF {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ (δ : 𝓞 E) (Δ : 𝓞 F), σ (δ : E) = -δ ∧
    (δ : E) ≠ 0 ∧ algebraMap F E Δ = δ * δ := by
  obtain ⟨a, ha0, ha⟩ := GlobalTheory.AdelicU.exists_integer_conj_eq_neg h
  have hfix : σ ((a : E) * a) = (a : E) * a := by rw [map_mul, ha, neg_mul_neg]
  have hs := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : F, algebraMap F E Δ = (a : E) * a := by
    rcases hs.eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with hb | ht
    · have : (a : E) * a ∈ AlgHom.equalizer σ (AlgHom.id F E) := hfix
      rw [hb] at this
      exact Algebra.mem_bot.1 this
    · exfalso
      obtain ⟨x, hx⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne h
      exact hx (show x ∈ AlgHom.equalizer σ (AlgHom.id F E) from ht ▸ Algebra.mem_top)
  have h4 : IsIntegral ℤ Δ :=
    (isIntegral_algebraMap_iff (algebraMap F E).injective).1 (hΔ ▸ (a.isIntegral_coe.mul a.isIntegral_coe))
  exact ⟨a, ⟨Δ, h4⟩, ha, RingOfIntegers.coe_ne_zero_iff.2 ha0, hΔ⟩

end Gen

end GlobalTheory.HeckeSplitGen

namespace GlobalTheory.HeckeSplitGen

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_grpHF_of_good (σ : E →ₐ[F] E) (N : ℕ) (hN : N ≠ 0) (δ : 𝓞 E)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    (∀ v ∈ T, ∃ e, IsSplitIdemF σ e ∧ e + cAF σ e = algebraMap (AF F) (AEF F E) (epv v)) →
    ∀ (x : (AEF F E)ˣ) (a b a' b' : AF F), (x : AEF F E) = mkE (F := F) (δ : E) (AF F) a b →
      ((x⁻¹ : (AEF F E)ˣ) : AEF F E) = mkE (F := F) (δ : E) (AF F) a' b' → a.1 = 1 → b.1 = 0 →
      (∀ v ∉ T, ‖a.2 v - 1‖ ≤ ‖(N : v.adicCompletion F)‖ ∧ ‖b.2 v‖ ≤ ‖(N : v.adicCompletion F)‖ ∧
        ‖a'.2 v‖ ≤ 1 ∧ ‖b'.2 v‖ ≤ 1) → x ∈ grpHF σ N := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro _ x a b a' b' hx hx' ha hb hg
    have hg' := fun v => hg v (Finset.notMem_empty v)
    refine Subgroup.subset_closure (Or.inr ⟨?_, ?_, ?_⟩)
    · rw [hx, infPartF_mkE, ha, hb, mkE_one]
    · obtain ⟨za, hza, ea⟩ := exists_div_nat (a.2 - 1) N hN fun v => by rw [af_sub_one]; exact (hg' v).1
      obtain ⟨zb, hzb, eb⟩ := exists_div_nat b.2 N hN fun v => (hg' v).2.1
      refine ⟨_, mkE_mem_intAEF δ za zb hza hzb, ?_⟩
      rw [hx, finPartF_mkE]
      exact mkE_sub_one _ N _ _ _ _ ea eb
    · rw [hx', finPartF_mkE]
      exact mkE_mem_intAEF δ _ _ (fun v => (hg' v).2.2.1) fun v => (hg' v).2.2.2
  | insert v T hvT ih =>
    intro hT x a b a' b' hx hx' ha hb hg
    obtain ⟨e, he, hee⟩ := hT v (Finset.mem_insert_self v T)
    rw [← cut_mul (epv_sq v) x]
    refine mul_mem (Subgroup.subset_closure (Or.inl (Or.inr ⟨e, he, ?_⟩))) ?_
    · have h : algebraMap (AF F) (AEF F E) (epv v) * algebraMap (AF F) (AEF F E) (epv v) =
          algebraMap (AF F) (AEF F E) (epv v) := by rw [← map_mul, epv_sq]
      rw [hee, cut_val]
      linear_combination ((x : AEF F E) - 1) * h
    · refine ih (fun w hw => hT w (Finset.mem_insert_of_mem hw)) _ _ _ _ _
        (by rw [cut_val, hx, cut_mkE]) (by rw [cut_inv, hx', cut_mkE]) ?_ ?_ fun w hw => ?_
      · simp only [finite_adele_fst_add, finite_adele_fst_mul, finite_adele_fst_sub, ha, epv_fst, finite_adele_fst_one]; ring
      · rw [finite_adele_fst_mul, hb, mul_zero]
      · simp only [finite_adele_snd_add, finite_adele_snd_mul, finite_adele_snd_sub, finite_adele_snd_one]
        by_cases hwv : w = v
        · subst hwv
          rw [epv_self]
          simp
        · rw [epv_ne hwv]
          simpa using hg w (by rw [Finset.mem_insert, not_or]; exact ⟨hwv, hw⟩)

theorem exists_mem_grpHF (σ : E →ₐ[F] E) (N : ℕ) (hN : N ≠ 0) (δ : 𝓞 E) (Δ : 𝓞 F)
    (hΔ : algebraMap F E Δ = δ * δ) (α β : F) (hn : α * α - Δ * (β * β) ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hg : ∀ v ∉ T, GoodAt N (Δ : F) α β v)
    (hT : ∀ v ∈ T, ∃ e, IsSplitIdemF σ e ∧ e + cAF σ e = algebraMap (AF F) (AEF F E) (epv v)) :
    ∃ g ∈ grpHF σ N,
      (g : AEF F E) = mkE (F := F) (δ : E) (AF F) (pairA F (algebraMap _ _ α) 1) (pairA F (algebraMap _ _ β) 0) ∧
      ((g⁻¹ : (AEF F E)ˣ) : AEF F E) =
        mkE (F := F) (δ : E) (AF F) (pairA F (algebraMap _ _ (α / (α * α - Δ * (β * β)))) 1)
          (pairA F (algebraMap _ _ (-β / (α * α - Δ * (β * β)))) 0) := by
  set n : F := α * α - Δ * (β * β) with hndef
  have hyy : (algebraMap F E α + algebraMap F E β * δ) *
      (algebraMap F E (α / n) + algebraMap F E (-β / n) * δ) = 1 := by
    have h0 : algebraMap F E n ≠ 0 := (map_ne_zero _).2 hn
    have h1 : algebraMap F E n = algebraMap F E α * algebraMap F E α -
        δ * δ * (algebraMap F E β * algebraMap F E β) := by
      rw [hndef, map_sub, map_mul, map_mul, map_mul, hΔ]
    rw [map_div₀, map_div₀, map_neg]
    field_simp
    rw [h1]; ring
  let y : Eˣ := ⟨_, _, hyy, by rw [mul_comm]; exact hyy⟩
  let Y : (AEF F E)ˣ := Units.map (incAF F E).toMonoidHom y
  have hY : Y ∈ grpHF σ N := Subgroup.subset_closure (Or.inl (Or.inl ⟨y, rfl⟩))
  have hY1 : (Y : AEF F E) = mkE (F := F) (δ : E) (AF F) (algebraMap _ _ α) (algebraMap _ _ β) :=
    incAF_eq_mkE _ α β
  have hY2 : ((Y⁻¹ : (AEF F E)ˣ) : AEF F E) =
      mkE (F := F) (δ : E) (AF F) (algebraMap _ _ (α / n)) (algebraMap _ _ (-β / n)) :=
    incAF_eq_mkE _ _ _
  have e1 : ∀ c : F, epInf F * algebraMap _ _ c + (1 - epInf F) = pairA F (algebraMap _ _ c) 1 := fun c => by
    refine Prod.ext ?_ ?_
    · show 1 * algebraMap F (Ainf F) c + (1 - 1) = algebraMap F (Ainf F) c
      ring
    · show 0 * algebraMap F (Af F) c + (1 - 0) = 1
      ring
  have e2 : ∀ c : F, epInf F * algebraMap _ _ c = pairA F (algebraMap _ _ c) 0 := fun c => by
    refine Prod.ext ?_ ?_
    · show 1 * algebraMap F (Ainf F) c = algebraMap F (Ainf F) c
      ring
    · show 0 * algebraMap F (Af F) c = 0
      ring
  have e3 : ∀ (c : F) v, ((1 - epInf F) * algebraMap _ _ c + (1 - (1 - epInf F))).2 v =
      algebraMap F (v.adicCompletion F) c := fun c v => by
    show (1 - 0) * algebraMap F (v.adicCompletion F) c + (1 - (1 - 0)) = _
    ring
  have e4 : ∀ (c : F) v, ((1 - epInf F) * algebraMap _ _ c).2 v = algebraMap F (v.adicCompletion F) c :=
    fun c v => by
    show (1 - 0) * algebraMap F (v.adicCompletion F) c = _
    ring
  have hx : cut (idem_compl (epInf_sq F)) Y ∈ grpHF σ N := by
    refine mem_grpHF_of_good σ N hN δ T hT _ _ _ _ _ (by rw [cut_val, hY1, cut_mkE]) (by rw [cut_inv, hY2, cut_mkE])
      ?_ ?_ fun v hv => ?_
    · show (1 - 1) * algebraMap F (Ainf F) α + (1 - (1 - 1)) = 1
      ring
    · show (1 - 1) * algebraMap F (Ainf F) β = 0
      ring
    · obtain ⟨g1, g2, g3⟩ := hg v hv
      rw [e3, e4, e3, e4, map_div₀, map_div₀, norm_div, norm_div, g3, div_one, div_one, map_neg, norm_neg]
      exact ⟨g1, g2, norm_le_one_of_sub_le (g1.trans (norm_nat_le_one v N)), g2.trans (norm_nat_le_one v N)⟩
  refine ⟨cut (epInf_sq F) Y, ?_, by rw [cut_val, hY1, cut_mkE, e1, e2], by rw [cut_inv, hY2, cut_mkE, e1, e2]⟩
  rw [eq_mul_inv_of_mul_eq (cut_mul (epInf_sq F) Y)]
  exact mul_mem hY (inv_mem hx)

end Main

end GlobalTheory.HeckeSplitGen

namespace GlobalTheory.HeckeSplitGen

theorem mem_closure_grpHF_of_finPart_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ), 0 < N → ∀ z : (AF F ⊗[F] E)ˣ,
    finPartF F E (z : AF F ⊗[F] E) = 1 → z ∈ closure (grpHF σ N : Set (AF F ⊗[F] E)ˣ) := by
  intro F E _ _ _ _ _ σ h N hN z hz
  obtain ⟨δ, Δ, hδ, hδ0, hΔ⟩ := exists_int_deltaF h
  have h2 := h.2.2.1
  have hΔ0 : (Δ : F) ≠ 0 := by
    intro h'; rw [h', map_zero] at hΔ; exact hδ0 (mul_self_eq_zero.mp hΔ.symm)
  have hns : ∀ α β : F, α ≠ 0 → α * α - Δ * (β * β) ≠ 0 := by
    intro α β hα h'
    have hli := LinearIndependent.pair_iff.1 (linIndep_one_delta σ (δ : E) hδ hδ0)
    have h1 : (α • (1 : E) + β • (δ : E)) * (α • (1 : E) + (-β) • (δ : E)) = 0 := by
      have := congrArg (algebraMap F E) h'
      rw [map_sub, map_mul, map_mul, map_mul, hΔ, map_zero] at this
      simp only [Algebra.smul_def, map_neg]
      linear_combination this
    rcases mul_eq_zero.1 h1 with h3 | h3
    · exact hα (hli _ _ h3).1
    · exact hα (hli _ _ h3).1
  obtain ⟨v₀, ⟨τ⟩⟩ := GlobalTheory.AdelicU.exists_split_place h
  have hs₀ : τ (δ : E) * τ (δ : E) = algebraMap F (v₀.adicCompletion F) Δ := by
    rw [← map_mul, ← hΔ, τ.commutes]
  obtain ⟨e₀, he₀, hee₀⟩ := exists_splitIdemF σ (δ : E) hδ hδ0 (Δ : F) hΔ v₀ (τ (δ : E)) hs₀
  obtain ⟨a, b, hab⟩ : ∃ a b, (z : AEF F E) = mkE (F := F) (δ : E) (AF F) a b :=
    ⟨_, _, (mkE_cP_cQ σ (δ : E) hδ hδ0 h2 (AF F) _).symm⟩
  obtain ⟨a', b', hab'⟩ : ∃ a b, ((z⁻¹ : (AEF F E)ˣ) : AEF F E) = mkE (F := F) (δ : E) (AF F) a b :=
    ⟨_, _, (mkE_cP_cQ σ (δ : E) hδ hδ0 h2 (AF F) _).symm⟩
  have hz' : finPartF F E ((z⁻¹ : (AEF F E)ˣ) : AEF F E) = 1 := by
    have := congrArg (finPartF F E) z.mul_inv
    rwa [map_mul, hz, one_mul, map_one] at this
  rw [hab, finPartF_mkE, ← mkE_one (F := F) (δ : E) (Af F)] at hz
  rw [hab', finPartF_mkE, ← mkE_one (F := F) (δ : E) (Af F)] at hz'
  obtain ⟨f1, f2⟩ := mkE_inj σ _ hδ hδ0 h2 _ hz
  obtain ⟨f1', f2'⟩ := mkE_inj σ _ hδ hδ0 h2 _ hz'
  have hmul := z.mul_inv
  rw [hab, hab', mkE_mul (δ : E) (Δ : F) hΔ (AF F), ← mkE_one (F := F) (δ : E) (AF F)] at hmul
  obtain ⟨m1, m2⟩ := mkE_inj σ _ hδ hδ0 h2 _ hmul
  have hch := fun k : ℕ => exists_pair v₀ N hN.ne' Δ hΔ0 hns a.1 b.1 (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  choose α β hα0 hα hβ T hg hT using hch
  have hG := fun k => exists_mem_grpHF σ N hN.ne' δ Δ hΔ (α k) (β k) (hns _ _ (hα0 k)) (T k) (hg k) fun v hv => by
    rcases hT k v hv with rfl | ⟨s, hs⟩
    · exact ⟨e₀, he₀, hee₀⟩
    · exact exists_splitIdemF σ _ hδ hδ0 _ hΔ v s hs
  choose g hgm hg1 hg2 using hG
  have tα : ∀ w, Tendsto (fun k => algebraMap F w.Completion (α k)) atTop (𝓝 (a.1 w)) := fun w =>
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun k => (hα k w).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have tβ : ∀ w, Tendsto (fun k => algebraMap F w.Completion (β k)) atTop (𝓝 (b.1 w)) := fun w =>
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun k => (hβ k w).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have tinv : ∀ w, Tendsto (fun k => algebraMap F w.Completion (α k / (α k * α k - Δ * (β k * β k)))) atTop
      (𝓝 (a'.1 w)) ∧ Tendsto (fun k => algebraMap F w.Completion (-β k / (α k * α k - Δ * (β k * β k)))) atTop
      (𝓝 (b'.1 w)) := fun w => by
    have p1 : a.1 w * a'.1 w + algebraMap F w.Completion Δ * (b.1 w * b'.1 w) = 1 :=
      congrArg (fun x : AF F => x.1 w) m1
    have p2 : a.1 w * b'.1 w + b.1 w * a'.1 w = 0 := congrArg (fun x : AF F => x.1 w) m2
    have h0 : a.1 w * a.1 w - algebraMap F w.Completion Δ * (b.1 w * b.1 w) ≠ 0 :=
      left_ne_zero_of_mul_eq_one (b := a'.1 w * a'.1 w - algebraMap F w.Completion Δ * (b'.1 w * b'.1 w)) (by
        linear_combination (a.1 w * a'.1 w + algebraMap F w.Completion Δ * (b.1 w * b'.1 w) + 1) * p1 -
          algebraMap F w.Completion Δ * (a.1 w * b'.1 w + b.1 w * a'.1 w) * p2)
    have tn := ((tα w).mul (tα w)).sub (((tβ w).mul (tβ w)).const_mul (algebraMap F w.Completion Δ))
    have q1 : a'.1 w = a.1 w / (a.1 w * a.1 w - algebraMap F w.Completion Δ * (b.1 w * b.1 w)) := by
      rw [eq_div_iff h0]
      linear_combination a.1 w * p1 - algebraMap F w.Completion Δ * b.1 w * p2
    have q2 : b'.1 w = -b.1 w / (a.1 w * a.1 w - algebraMap F w.Completion Δ * (b.1 w * b.1 w)) := by
      rw [eq_div_iff h0]
      linear_combination a.1 w * p2 - b.1 w * p1
    rw [q1, q2]
    simp only [map_div₀, map_sub, map_mul, map_neg]
    exact ⟨(tα w).div tn h0, (tβ w).neg.div tn h0⟩
  have tpt : ∀ (c d : ℕ → F) (A B : AF F), A.2 = 1 → B.2 = 0 →
      (∀ w, Tendsto (fun k => algebraMap F w.Completion (c k)) atTop (𝓝 (A.1 w))) →
      (∀ w, Tendsto (fun k => algebraMap F w.Completion (d k)) atTop (𝓝 (B.1 w))) →
      Tendsto (fun k => mkE (F := F) (δ : E) (AF F) (pairA F (algebraMap _ _ (c k)) 1)
        (pairA F (algebraMap _ _ (d k)) 0)) atTop (𝓝 (mkE (F := F) (δ : E) (AF F) A B)) := by
    intro c d A B hA hB hc hd
    have t1 : Tendsto (fun k => pairA F (algebraMap _ _ (c k)) 1) atTop (𝓝 A) := by
      rw [← hA]
      exact Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hc) tendsto_const_nhds
    have t2 : Tendsto (fun k => pairA F (algebraMap _ _ (d k)) 0) atTop (𝓝 B) := by
      rw [← hB]
      exact Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hd) tendsto_const_nhds
    exact tendsto_mkEF (E := E) _ t1 t2
  refine mem_closure_of_tendsto (f := g) (b := atTop) ?_ (Eventually.of_forall hgm)
  refine Units.isInducing_embedProduct.tendsto_nhds_iff.2 (Tendsto.prodMk_nhds ?_ ?_)
  · show Tendsto (fun k => (g k : AEF F E)) atTop (𝓝 (z : AEF F E))
    simp only [hg1, hab]
    exact tpt _ _ _ _ f1 f2 tα tβ
  · refine (MulOpposite.continuous_op.tendsto _).comp ?_
    show Tendsto (fun k => (((g k)⁻¹ : (AEF F E)ˣ) : AEF F E)) atTop (𝓝 ((z⁻¹ : (AEF F E)ˣ) : AEF F E))
    simp only [hg2, hab']
    exact tpt _ _ _ _ f1' f2' (fun w => (tinv w).1) fun w => (tinv w).2

end GlobalTheory.HeckeSplitGen
