import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCovering.NCovAd
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraMore

noncomputable section

namespace GlobalTheory.CompanionTheory.PsiCondLoc

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain Filter Topology Metric
open Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ ≤ 1 / 2) : z = 1 :=
  _root_.UpperTheory.Reformulated.B.Ue24.eq_one_of_pow_near h

theorem exists_sub_mem_of_infinite {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {C s : Set G} (hC : IsCompact C) (hs : s ⊆ C) (hi : s.Infinite) {V : Set G} (hV : V ∈ 𝓝 (0 : G)) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ a - b ∈ V := by
  have ht : Tendsto (fun p : G × G => p.1 - p.2) (𝓝 ((0 : G), (0 : G))) (𝓝 ((0 : G) - 0)) :=
    (continuous_fst.sub continuous_snd : Continuous fun p : G × G => p.1 - p.2).tendsto ((0 : G), (0 : G))
  rw [sub_zero] at ht
  have h1 := ht hV
  rw [Filter.mem_map, nhds_prod_eq, Filter.mem_prod_self_iff] at h1
  obtain ⟨W, hW, hWV⟩ := h1
  have hU : ∀ c ∈ C, (fun y => y - c) ⁻¹' W ∈ 𝓝 c := fun c _ =>
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨t, -, hcov⟩ := hC.elim_nhds_subcover _ hU
  have hch : ∀ a : G, ∃ c : G, a ∈ s → c ∈ t ∧ a - c ∈ W := by
    intro a
    by_cases ha : a ∈ s
    · have := hcov (hs ha)
      simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop] at this
      obtain ⟨c, hc, hac⟩ := this
      exact ⟨c, fun _ => ⟨hc, hac⟩⟩
    · exact ⟨a, fun h => absurd h ha⟩
  choose f hf using hch
  obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
    hi.exists_ne_map_eq_of_mapsTo (f := f) (t := (t : Set G)) (fun a ha => (hf a ha).1) t.finite_toSet
  refine ⟨a, ha, b, hb, hab, ?_⟩
  have h2 : (a - f a, b - f b) ∈ W ×ˢ W := ⟨(hf a ha).2, (hf b hb).2⟩
  have h3 := hWV h2
  simpa [hfab] using h3

variable {F : Type} [Field F] [NumberField F]

theorem pairA_add_snd (u w : Af F) : pairA F 0 (u + w) = pairA F 0 u + pairA F 0 w := by
  show ((0 : Ainf F), u + w) = ((0 : Ainf F), u) + ((0 : Ainf F), w)
  rw [Prod.mk_add_mk, add_zero]

theorem pairA_add_fst (u w : Ainf F) : pairA F (u + w) 0 = pairA F u 0 + pairA F w 0 := by
  show (u + w, (0 : Af F)) = (u, (0 : Af F)) + (w, (0 : Af F))
  rw [Prod.mk_add_mk, add_zero]

theorem pairA_nsmul_snd (n : ℕ) (u : Af F) : pairA F 0 (n • u) = n • pairA F 0 u := by
  show ((0 : Ainf F), n • u) = n • ((0 : Ainf F), u)
  rw [Prod.smul_mk, smul_zero]

theorem pairA_nsmul_fst (n : ℕ) (u : Ainf F) : pairA F (n • u) 0 = n • pairA F u 0 := by
  show (n • u, (0 : Af F)) = n • (u, (0 : Af F))
  rw [Prod.smul_mk, smul_zero]

theorem exists_polydisc {U : Set (Ainf F)} (hU : U ∈ 𝓝 (0 : Ainf F)) :
    ∃ δ > 0, ∀ x : Ainf F, (∀ w, ‖x w‖ < δ) → x ∈ U := by
  have hU' : U ∈ 𝓝 (0 : ∀ w : InfinitePlace F, w.Completion) := hU
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.1 hU'
  refine ⟨δ, hδ, fun x hx => hb ?_⟩
  have hx' : ∀ w, dist ((x : ∀ w : InfinitePlace F, w.Completion) w) ((0 : ∀ w : InfinitePlace F, w.Completion) w) < δ := fun w => by
    rw [Pi.zero_apply, dist_zero_right]; exact hx w
  exact mem_ball.2 ((dist_pi_lt_iff hδ).2 hx')

theorem polydisc_mem_nhds {ε : ℝ} (hε : 0 < ε) : {x : Ainf F | ∀ w, ‖x w‖ < ε} ∈ 𝓝 (0 : Ainf F) := by
  have h : Metric.ball (0 : ∀ w : InfinitePlace F, w.Completion) ε ∈ 𝓝 (0 : ∀ w : InfinitePlace F, w.Completion) :=
    Metric.ball_mem_nhds _ hε
  refine Filter.mem_of_superset h fun x hx w => ?_
  have h1 := (dist_pi_lt_iff hε).1 (mem_ball.1 hx) w
  rwa [Pi.zero_apply, dist_zero_right] at h1

theorem af_nontrivial : Nontrivial (Af F) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  refine ⟨0, 1, fun h => ?_⟩
  have h2 : (0 : v.adicCompletion F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
  exact zero_ne_one h2

theorem single_self (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : (singleV F v y) v = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem single_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) :
    (singleV F v y) w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y h

theorem mul_single (u : Af F) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    u * singleV F v y = singleV F v (u v * y) := by
  refine Subtype.ext (funext fun w => ?_)
  show u w * (singleV F v y) w = (singleV F v (u v * y)) w
  by_cases h : w = v
  · subst h
    rw [single_self, single_self]
  · rw [single_ne v _ h, single_ne v _ h, mul_zero]

theorem int_at {a : Af F} (h : a ∈ Formalism.UG.intAd F) (w : HeightOneSpectrum (𝓞 F)) :
    a w ∈ w.adicCompletionIntegers F := by
  have h' : ∀ w : HeightOneSpectrum (𝓞 F), a w ∈ w.adicCompletionIntegers F := h
  exact h' w

theorem exists_int_kernel {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ α : 𝓞 F, α ≠ 0 ∧ ∀ y ∈ Formalism.UG.intAd F, ψ (pairA F 0 (algebraMap F (Af F) (α : F) * y)) = 1 := by
  have hc : Continuous fun y : Af F => ψ (pairA F 0 y) :=
    hψ.1.comp (Continuous.prodMk continuous_const continuous_id)
  set n : Set (Af F × Af F) := {p | ‖ψ (pairA F 0 (p.1 * p.2)) - 1‖ < 1 / 2} with hn
  have hno : IsOpen n := by
    have : Continuous fun p : Af F × Af F => ‖ψ (pairA F 0 (p.1 * p.2)) - 1‖ :=
      ((hc.comp (continuous_fst.mul continuous_snd)).sub continuous_const).norm
    exact isOpen_lt this continuous_const
  have h00 : ψ (pairA F 0 0) = 1 := by
    have : pairA F (0 : Ainf F) (0 : Af F) = 0 := rfl
    rw [this]; exact AddChar.map_zero_eq_one ψ
  have hI : IsCompact (Formalism.UG.intAd F : Set (Af F)) := (finiteAdeleIntegers_compactOpen F).2
  obtain ⟨u, w, hu, -, h0u, hIw, huw⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : Af F))) hI hno
    (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      have ha' : a = 0 := ha
      subst ha'
      simp [hn, h00])
  haveI := af_nontrivial (F := F)
  have hinj : Function.Injective fun β : 𝓞 F => algebraMap F (Af F) (β : F) :=
    (algebraMap F (Af F)).injective.comp RingOfIntegers.coe_injective
  obtain ⟨a, ⟨β₁, rfl⟩, b, ⟨β₂, rfl⟩, hab, hsub⟩ := exists_sub_mem_of_infinite hI
    (s := Set.range fun β : 𝓞 F => algebraMap F (Af F) (β : F))
    (by rintro _ ⟨β, rfl⟩; exact NCovAd_int_mem β) (Set.infinite_range_of_injective hinj)
    (hu.mem_nhds (h0u rfl))
  refine ⟨β₁ - β₂, fun h => hab ?_, fun y hy => ?_⟩
  · rw [sub_eq_zero.1 h]
  · have hal : algebraMap F (Af F) ((β₁ - β₂ : 𝓞 F) : F) =
        algebraMap F (Af F) (β₁ : F) - algebraMap F (Af F) (β₂ : F) := by
      rw [show ((β₁ - β₂ : 𝓞 F) : F) = (β₁ : F) - (β₂ : F) from map_sub (algebraMap (𝓞 F) F) _ _, map_sub]
    rw [hal]
    refine eq_one_of_pow_near fun k => ?_
    have e : ψ (pairA F 0 ((algebraMap F (Af F) (β₁ : F) - algebraMap F (Af F) (β₂ : F)) * y)) ^ (2 ^ k) =
        ψ (pairA F 0 ((algebraMap F (Af F) (β₁ : F) - algebraMap F (Af F) (β₂ : F)) * ((2 ^ k : ℕ) • y))) := by
      rw [← AddChar.map_nsmul_eq_pow, ← pairA_nsmul_snd, mul_smul_comm]
    rw [e]
    have hm : (2 ^ k : ℕ) • y ∈ Formalism.UG.intAd F := nsmul_mem hy _
    exact (huw (Set.mk_mem_prod hsub (hIw hm))).le

theorem exists_small_of_infinite (K : Submodule (𝓞 F) F) {α : 𝓞 F} (hα : α ≠ 0) (hαK : (α : F) ∈ K)
    {T : Set F} (hTK : T ⊆ K) (hT : T.Infinite)
    (hd : ∀ s ∈ T, ∀ t ∈ T, s ≠ t → ∀ β : 𝓞 F, s - t ≠ (α : F) * (β : F))
    {V : Set (Ainf F)} (hV : V ∈ 𝓝 (0 : Ainf F)) :
    ∃ k ∈ K, k ≠ 0 ∧ algebraMap F (Ainf F) k ∈ V := by
  have hα0 : (α : F) ≠ 0 := by exact_mod_cast hα
  obtain ⟨R, hR⟩ := NCovAd_inf_approx (F := F)
  choose β hβ using fun t : F => hR (algebraMap F (Ainf F) (t / α))
  set d : F → F := fun t => t - (α : F) * (β t : F) with hdd
  have hdK : ∀ t ∈ T, d t ∈ K := by
    intro t ht
    have h1 : (β t) • (α : F) ∈ K := K.smul_mem _ hαK
    have h2 : (β t) • (α : F) = (α : F) * (β t : F) := by
      rw [Algebra.smul_def, mul_comm]
    rw [h2] at h1
    exact K.sub_mem (hTK ht) h1
  have hinjF : Function.Injective (algebraMap F (Ainf F)) := (algebraMap F (Ainf F)).injective
  have hdinj : Set.InjOn d T := by
    intro s hs t ht hst
    by_contra hne
    apply hd s hs t ht hne (β s - β t)
    have : s - (α : F) * (β s : F) = t - (α : F) * (β t : F) := hst
    push_cast
    linear_combination this
  set C : Set (Ainf F) := Set.univ.pi fun w : InfinitePlace F =>
    closedBall (0 : w.Completion) (‖algebraMap F (Ainf F) (α : F) w‖ * R) with hC
  have hCc : IsCompact C := isCompact_univ_pi fun w => NCovAd_ball_compact w _
  have hsC : (algebraMap F (Ainf F) ∘ d) '' T ⊆ C := by
    rintro _ ⟨t, -, rfl⟩ w -
    rw [mem_closedBall, dist_zero_right]
    have e : algebraMap F (Ainf F) (d t) =
        algebraMap F (Ainf F) (α : F) * (algebraMap F (Ainf F) (t / α) - algebraMap F (Ainf F) (β t : F)) := by
      rw [← map_sub, ← map_mul]
      congr 1
      simp only [hdd]
      field_simp
    show ‖algebraMap F (Ainf F) (d t) w‖ ≤ _
    rw [e]
    show ‖algebraMap F (Ainf F) (α : F) w * (algebraMap F (Ainf F) (t / α) - algebraMap F (Ainf F) (β t : F)) w‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hβ t w) (norm_nonneg _)
  have hinf : ((algebraMap F (Ainf F) ∘ d) '' T).Infinite :=
    hT.image (hinjF.comp_injOn hdinj)
  obtain ⟨_, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, hab, hsub⟩ := exists_sub_mem_of_infinite hCc hsC hinf hV
  refine ⟨d s - d t, K.sub_mem (hdK s hs) (hdK t ht), fun h => hab ?_, ?_⟩
  · show algebraMap F (Ainf F) (d s) = algebraMap F (Ainf F) (d t)
    rw [sub_eq_zero.1 h]
  · rw [map_sub]; exact hsub

theorem inf_trivial_of_small {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (K : Submodule (𝓞 F) F)
    (hK : ∀ x ∈ K, ψ (pairA F (algebraMap F (Ainf F) x) 0) = 1)
    (hs : ∀ V ∈ 𝓝 (0 : Ainf F), ∃ k ∈ K, k ≠ 0 ∧ algebraMap F (Ainf F) k ∈ V) (x : Ainf F) :
    ψ (pairA F x 0) = 1 := by
  have hc : Continuous fun y : Ainf F => ψ (pairA F y 0) :=
    hψ.1.comp (Continuous.prodMk continuous_id continuous_const)
  have h00 : ψ (pairA F 0 0) = 1 := by
    have : pairA F (0 : Ainf F) (0 : Af F) = 0 := rfl
    rw [this]; exact AddChar.map_zero_eq_one ψ
  have hU : {y : Ainf F | ‖ψ (pairA F y 0) - 1‖ < 1 / 2} ∈ 𝓝 (0 : Ainf F) := by
    have hcn : Continuous fun y : Ainf F => ‖ψ (pairA F y 0) - 1‖ := (hc.sub continuous_const).norm
    exact (isOpen_lt hcn continuous_const).mem_nhds (by simp [h00])
  obtain ⟨δ, hδ, hδU⟩ := exists_polydisc hU
  obtain ⟨R, hR⟩ := NCovAd_inf_approx (F := F)
  have hR1 : 0 < |R| + 1 := by positivity
  obtain ⟨k, hkK, hk0, hkV⟩ := hs _ (polydisc_mem_nhds (div_pos hδ hR1))
  have hall : ∀ y : Ainf F, ‖ψ (pairA F y 0) - 1‖ ≤ 1 / 2 := by
    intro y
    obtain ⟨β, hβ⟩ := hR (y * algebraMap F (Ainf F) k⁻¹)
    set z := y * algebraMap F (Ainf F) k⁻¹ - algebraMap F (Ainf F) (β : F) with hz
    have hone : algebraMap F (Ainf F) k * algebraMap F (Ainf F) k⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hk0, map_one]
    have e : y = algebraMap F (Ainf F) (k * (β : F)) + algebraMap F (Ainf F) k * z := by
      rw [hz, map_mul]
      linear_combination (-y) * hone
    have hsm : k * (β : F) ∈ K := by
      have h1 : β • k ∈ K := K.smul_mem _ hkK
      have h2 : β • k = k * (β : F) := by
        rw [Algebra.smul_def, mul_comm]
      rwa [h2] at h1
    have hin : algebraMap F (Ainf F) k * z ∈ {y : Ainf F | ‖ψ (pairA F y 0) - 1‖ < 1 / 2} := by
      refine hδU _ fun w => ?_
      show ‖algebraMap F (Ainf F) k w * z w‖ < δ
      rw [norm_mul]
      have h1 := hkV w
      have h2 : ‖z w‖ ≤ |R| + 1 := ((hβ w).trans (le_abs_self R)).trans (by linarith)
      calc ‖algebraMap F (Ainf F) k w‖ * ‖z w‖ ≤ ‖algebraMap F (Ainf F) k w‖ * (|R| + 1) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ < δ / (|R| + 1) * (|R| + 1) := mul_lt_mul_of_pos_right h1 hR1
        _ = δ := div_mul_cancel₀ _ hR1.ne'
    have e2 : ψ (pairA F y 0) = ψ (pairA F (algebraMap F (Ainf F) k * z) 0) := by
      conv_lhs => rw [e, pairA_add_fst, AddChar.map_add_eq_mul, hK _ hsm, one_mul]
    rw [e2]
    exact le_of_lt hin
  refine eq_one_of_pow_near fun k => ?_
  rw [← AddChar.map_nsmul_eq_pow, ← pairA_nsmul_fst]
  exact hall _

theorem trivial_of_parts {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) {α : 𝓞 F} (hα : α ≠ 0)
    (hk : ∀ y ∈ Formalism.UG.intAd F, ψ (pairA F 0 (algebraMap F (Af F) (α : F) * y)) = 1)
    (hinf : ∀ x, ψ (pairA F x 0) = 1) (x : AF F) : ψ x = 1 := by
  have hα0 : (α : F) ≠ 0 := by exact_mod_cast hα
  obtain ⟨y, hy⟩ := NCovAd_fin_approx (F := F) (algebraMap F (Af F) (α : F)⁻¹ * x.2)
  set e := algebraMap F (Af F) (α : F)⁻¹ * x.2 - algebraMap F (Af F) y with he
  have hone : algebraMap F (Af F) (α : F) * algebraMap F (Af F) (α : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hα0, map_one]
  have e1 : x = algebraMap F (AF F) ((α : F) * y) + pairA F (x.1 - algebraMap F (Ainf F) ((α : F) * y)) 0 +
      pairA F 0 (algebraMap F (Af F) (α : F) * e) := by
    refine Prod.ext ?_ ?_
    · show x.1 = algebraMap F (Ainf F) ((α : F) * y) + (x.1 - algebraMap F (Ainf F) ((α : F) * y)) + 0
      ring
    · show x.2 = algebraMap F (Af F) ((α : F) * y) + 0 + algebraMap F (Af F) (α : F) * e
      rw [he, map_mul]
      linear_combination (-x.2) * hone
  rw [e1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.2.2.1, hinf, hk _ hy]
  simp

theorem finite_bad {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ a : Fv F v, a ∉ v.adicCompletionIntegers F ∧
      ∀ b ∈ v.adicCompletionIntegers F, psiV F ψ v (a * b) = 1}.Finite := by
  by_contra hB
  set B := {v : HeightOneSpectrum (𝓞 F) | ∃ a : Fv F v, a ∉ v.adicCompletionIntegers F ∧
      ∀ b ∈ v.adicCompletionIntegers F, psiV F ψ v (a * b) = 1} with hBdef
  have hBi : B.Infinite := hB
  obtain ⟨α, hα, hk⟩ := exists_int_kernel hψ
  have hα0 : (α : F) ≠ 0 := by exact_mod_cast hα
  have hone : algebraMap F (Af F) (α : F) * algebraMap F (Af F) (α : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hα0, map_one]
  have h0 : ψ (pairA F 0 0) = 1 := by
    have : pairA F (0 : Ainf F) (0 : Af F) = 0 := rfl
    rw [this]; exact AddChar.map_zero_eq_one ψ
  let K : Submodule (𝓞 F) F :=
    { carrier := {x | ∀ c : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((c : F) * x))) = 1}
      add_mem' := fun {x y} hx hy c => by
        rw [mul_add, map_add, pairA_add_snd, AddChar.map_add_eq_mul, hx c, hy c, one_mul]
      zero_mem' := fun c => by rw [mul_zero, map_zero]; exact h0
      smul_mem' := fun c' x hx c => by
        have e : (c : F) * (c' • x) = ((c * c' : 𝓞 F) : F) * x := by
          rw [Algebra.smul_def]
          show (c : F) * ((c' : F) * x) = ((c : F) * (c' : F)) * x
          ring
        rw [e]; exact hx _ }
  have hKmem : ∀ x : F, x ∈ K ↔ ∀ c : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((c : F) * x))) = 1 :=
    fun x => Iff.rfl
  have hKinf : ∀ x ∈ K, ψ (pairA F (algebraMap F (Ainf F) x) 0) = 1 := by
    intro x hx
    have h1 := (hKmem x).1 hx 1
    rw [show ((1 : 𝓞 F) : F) = 1 from rfl, one_mul] at h1
    have e : algebraMap F (AF F) x = pairA F (algebraMap F (Ainf F) x) 0 + pairA F 0 (algebraMap F (Af F) x) := by
      refine Prod.ext ?_ ?_
      · show algebraMap F (Ainf F) x = algebraMap F (Ainf F) x + 0
        rw [add_zero]
      · show algebraMap F (Af F) x = 0 + algebraMap F (Af F) x
        rw [zero_add]
    have h2 := hψ.2.2.1 x
    rw [e, AddChar.map_add_eq_mul, h1, mul_one] at h2
    exact h2
  have hαK : (α : F) ∈ K := by
    refine (hKmem _).2 fun c => ?_
    rw [mul_comm, map_mul]
    exact hk _ (NCovAd_int_mem c)
  have hch : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a : Fv F v, v ∈ B → a ∉ v.adicCompletionIntegers F ∧
      ∀ b ∈ v.adicCompletionIntegers F, psiV F ψ v (a * b) = 1 := by
    intro v
    by_cases hv : v ∈ B
    · obtain ⟨a, ha⟩ := hv
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose a ha using hch
  choose y hy using fun v => NCovAd_fin_approx (F := F) (algebraMap F (Af F) (α : F)⁻¹ * singleV F v (a v))
  set E : HeightOneSpectrum (𝓞 F) → Af F := fun v =>
    algebraMap F (Af F) (α : F)⁻¹ * singleV F v (a v) - algebraMap F (Af F) (y v) with hE
  set t : HeightOneSpectrum (𝓞 F) → F := fun v => (α : F) * y v with ht
  have hsplit : ∀ v, singleV F v (a v) = algebraMap F (Af F) (α : F) * E v + algebraMap F (Af F) (t v) := by
    intro v
    simp only [hE, ht, map_mul]
    linear_combination (-singleV F v (a v)) * hone
  have hkey : ∀ v ∈ B, ∀ v', v ≠ v' → ∀ β : 𝓞 F, t v - t v' ≠ (α : F) * (β : F) := by
    intro v hv v' hne β heq
    have hX : algebraMap F (Af F) (α : F) * (E v - E v') + algebraMap F (Af F) ((α : F) * (β : F)) ∈
        Formalism.UG.intAd F :=
      add_mem (mul_mem (NCovAd_int_mem α) (sub_mem (hy v) (hy v'))) (NCovAd_int_mem (α * β))
    have e : singleV F v (a v) - singleV F v' (a v') =
        algebraMap F (Af F) (α : F) * (E v - E v') + algebraMap F (Af F) ((α : F) * (β : F)) := by
      rw [← heq, map_sub, hsplit v, hsplit v']
      ring
    rw [← e] at hX
    have h1 := int_at hX v
    have h2 : (singleV F v (a v) - singleV F v' (a v')) v = a v := by
      show (singleV F v (a v)) v - (singleV F v' (a v')) v = a v
      rw [single_self, single_ne v' _ hne, sub_zero]
    rw [h2] at h1
    exact (ha v hv).1 h1
  have htinj : Set.InjOn t B := by
    intro v hv v' hv' e
    by_contra hne
    refine hkey v hv v' hne 0 ?_
    rw [e, sub_self]
    simp
  have hTK : t '' B ⊆ K := by
    rintro _ ⟨v, hv, rfl⟩
    refine (hKmem _).2 fun c => ?_
    have e : algebraMap F (Af F) ((c : F) * t v) =
        singleV F v (a v * (algebraMap F (Af F) (c : F)) v) +
          algebraMap F (Af F) (α : F) * (-(algebraMap F (Af F) (c : F) * E v)) := by
      rw [mul_comm (a v), ← mul_single, hsplit v, map_mul]
      ring
    have hcO : (algebraMap F (Af F) (c : F)) v ∈ v.adicCompletionIntegers F :=
      int_at (NCovAd_int_mem c) v
    rw [e, pairA_add_snd, AddChar.map_add_eq_mul, hk _ (neg_mem (mul_mem (NCovAd_int_mem c) (hy v))), mul_one]
    exact (ha v hv).2 _ hcO
  have hd : ∀ s ∈ t '' B, ∀ s' ∈ t '' B, s ≠ s' → ∀ β : 𝓞 F, s - s' ≠ (α : F) * (β : F) := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩ hne β
    exact hkey v hv v' (fun h => hne (by rw [h])) β
  have hsmall : ∀ V ∈ 𝓝 (0 : Ainf F), ∃ k ∈ K, k ≠ 0 ∧ algebraMap F (Ainf F) k ∈ V := fun V hV =>
    exists_small_of_infinite K hα hαK hTK (hBi.image htinj) hd hV
  have hinf := inf_trivial_of_small hψ K hKinf hsmall
  obtain ⟨x, hx⟩ := hψ.2.2.2
  exact hx (trivial_of_parts hψ hα hk hinf x)

theorem good_of_unit {ψ : AddChar (AF F) ℂ} {α : 𝓞 F}
    (hk : ∀ y ∈ Formalism.UG.intAd F, ψ (pairA F 0 (algebraMap F (Af F) (α : F) * y)) = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hα : α ≠ 0)
    (hv : algebraMap F (Fv F v) ((α : F)⁻¹) ∈ v.adicCompletionIntegers F) {a : Fv F v}
    (ha : a ∈ v.adicCompletionIntegers F) : psiV F ψ v a = 1 := by
  have hα0 : (α : F) ≠ 0 := by exact_mod_cast hα
  have hy : singleV F v (algebraMap F (Fv F v) ((α : F)⁻¹) * a) ∈ Formalism.UG.intAd F := by
    intro w
    by_cases h : w = v
    · subst h
      rw [single_self]
      exact mul_mem hv ha
    · rw [single_ne v _ h]
      exact zero_mem _
  have e : algebraMap F (Af F) (α : F) * singleV F v (algebraMap F (Fv F v) ((α : F)⁻¹) * a) = singleV F v a := by
    rw [mul_single]
    congr 1
    have e1 : (algebraMap F (Af F) (α : F)) v = algebraMap F (Fv F v) (α : F) := rfl
    rw [e1, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hα0, map_one, one_mul]
  have := hk _ hy
  rwa [e] at this

theorem psiCond : PositivityTheory.SiegelWeilFormula.Gunr.PsiCond := by
  intro F _ _ ψ hψ
  obtain ⟨α, hα, hk⟩ := exists_int_kernel hψ
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (Fv F v) ((α : F)⁻¹) ∈ v.adicCompletionIntegers F :=
    (algebraMap F (Af F) ((α : F)⁻¹)).2
  have h2 := (finite_bad hψ).eventually_cofinite_notMem
  filter_upwards [h1, h2] with v hv hb a
  constructor
  · intro h
    by_contra ha
    exact hb ⟨a, ha, h⟩
  · intro ha b hb'
    exact good_of_unit hk v hα hv (mul_mem ha hb')

end GlobalTheory.CompanionTheory.PsiCondLoc
end
