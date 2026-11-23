import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt

noncomputable section

namespace PositivityTheory.ThKH.Locrep

open scoped Matrix
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_evFin' (v : Pl F) : Continuous (evFin F v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

variable (E) in

theorem exists_small_lattices (v : Pl F) :
    ∃ Λ : ℕ → AddSubgroup (AE F E), Antitone Λ ∧ (∀ n, ∀ z ∈ Λ n, ∀ z' ∈ Λ n, z * z' ∈ Λ n) ∧
      (∀ V ∈ 𝓝 (0 : AE F E), ∃ n, (Λ n : Set (AE F E)) ⊆ V) ∧ (∀ n, ∀ z ∈ Λ n, At (evFin F v) z) ∧
      ∀ n, ∃ V ∈ 𝓝 (0 : AE F E), ∀ z ∈ V, At (evFin F v) z → z ∈ Λ n := by
  classical
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  let c : AE F E → Fin (Module.finrank F E) → Fv F v := fun z i => evFin F v (b.repr z i)
  have hc : Continuous c := continuous_pi fun i =>
    (continuous_evFin' v).comp (IsModuleTopology.continuous_of_linearMap (b.coord i))
  obtain ⟨C, hC1, hC⟩ : ∃ C : ℝ, 1 ≤ C ∧ ∀ i j k, ‖c (b i * b j) k‖ ≤ C := by
    obtain ⟨C, hC⟩ := (Set.finite_range fun p : Fin (Module.finrank F E) × Fin (Module.finrank F E) ×
      Fin (Module.finrank F E) => ‖c (b p.1 * b p.2.1) p.2.2‖).bddAbove
    exact ⟨max 1 C, le_max_left _ _, fun i j k => (hC ⟨(i, j, k), rfl⟩).trans (le_max_right _ _)⟩
  have hC0 : 0 < C := one_pos.trans_le hC1
  let r : ℕ → ℝ := fun n => (1 / 2) ^ n / C
  have hr0 : ∀ n, 0 < r n := fun n => by positivity
  have hrC : ∀ n, r n * C ≤ 1 := fun n => by
    rw [div_mul_cancel₀ _ hC0.ne']
    exact pow_le_one₀ (by norm_num) (by norm_num)
  let Λ : ℕ → AddSubgroup (AE F E) := fun n =>
    { carrier := {z | At (evFin F v) z ∧ ∀ i, ‖c z i‖ ≤ r n}
      zero_mem' := ⟨fun u _ => smul_zero u, fun i => by simpa [c] using (hr0 n).le⟩
      add_mem' := fun {x y} hx hy => ⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], fun i => by
        have : c (x + y) i = c x i + c y i := by simp [c]
        rw [this]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx.2 i) (hy.2 i))⟩
      neg_mem' := fun {x} hx => ⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], fun i => by
        have : c (-x) i = -c x i := by simp [c]
        rw [this, norm_neg]
        exact hx.2 i⟩ }
  refine ⟨Λ, fun m n hmn z hz => ⟨hz.1, fun i => (hz.2 i).trans ?_⟩, fun n z hz z' hz' => ⟨fun u hu => ?_, fun k => ?_⟩,
    fun V hV => ?_, fun n z hz => hz.1, fun n => ?_⟩
  · exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn) hC0.le
  · rw [← smul_mul_assoc, hz.1 u hu, zero_mul]
  · have e : c (z * z') k = ∑ i, ∑ j, c z i * c z' j * c (b i * b j) k := by
      have e1 : z * z' = ∑ i, ∑ j, (b.repr z i * b.repr z' j) • (b i * b j) := by
        conv_lhs => rw [← b.sum_repr z, ← b.sum_repr z', Finset.sum_mul_sum]
        simp only [smul_mul_smul_comm]
      simp only [c]
      rw [e1]
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, map_mul]
    rw [e]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hr0 n).le fun i _ =>
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hr0 n).le fun j _ => ?_
    rw [norm_mul, norm_mul]
    calc _ ≤ r n * r n * C := by
          gcongr
          exacts [hz.2 i, hz'.2 j, hC i j k]
      _ = r n * (r n * C) := mul_assoc _ _ _
      _ ≤ r n := mul_le_of_le_one_right (hr0 n).le (hrC n)
  · let j : (Fin (Module.finrank F E) → Fv F v) → AE F E := fun y => ∑ i, GlobalTheory.EmbChart.atPlace v (y i) • b i
    have hj : Continuous j := continuous_finsetSum _ fun i _ =>
      ((GlobalTheory.VacAny.continuous_atPlace v).comp (continuous_apply i)).smul continuous_const
    have hj0 : j 0 = 0 := by simp [j]
    have h1 : j ⁻¹' V ∈ 𝓝 0 := hj.continuousAt.preimage_mem_nhds (hj0 ▸ hV)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 h1
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨n, fun z hz => ?_⟩
    have e : j (c z) = z := by
      conv_rhs => rw [← b.sum_repr z]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← GlobalTheory.SchrLoc.eq_atPlace_of_at (z := b.repr z i) fun u hu => by
        have := congrArg (fun t => b.repr t i) (hz.1 u hu)
        simpa using this]
    rw [← e]
    refine hball (mem_ball_zero_iff.2 ?_)
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (hr0 n).le).2 hz.2) (lt_of_le_of_lt ?_ hn)
    exact div_le_self (by positivity) hC1
  · have hc0 : c 0 = 0 := by funext i; simp [c]
    refine ⟨c ⁻¹' Metric.closedBall 0 (r n), hc.continuousAt.preimage_mem_nhds
      (hc0 ▸ Metric.closedBall_mem_nhds _ (hr0 n)), fun z hz ha => ⟨ha, fun i => ?_⟩⟩
    exact (norm_le_pi_norm _ i).trans (mem_closedBall_zero_iff.1 hz)

theorem exists_small_subgroups (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) :
    ∃ K : ℕ → Subgroup (UA σ W.J), Antitone K ∧ (∀ U ∈ 𝓝 (1 : UA σ W.J), ∃ n, (K n : Set (UA σ W.J)) ⊆ U) ∧
      (∀ n, (K n : Set (UA σ W.J)) ⊆ UAt σ W (evFin F v)) ∧
      ∀ n, ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ h ∈ U, h ∈ UAt σ W (evFin F v) → h ∈ K n := by
  classical
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  obtain ⟨Λ, hanti, hmul, hbas, hat, hop⟩ := exists_small_lattices E v
  have mm : ∀ g h : UA σ W.J, mat (g * h) = mat g * mat h := fun _ _ => rfl
  have m1 : mat (1 : UA σ W.J) = 1 := rfl
  have key : ∀ n, ∀ g h : UA σ W.J, (∀ i j, (mat g - 1) i j ∈ Λ n) → (∀ i j, (mat h - 1) i j ∈ Λ n) →
      ∀ i j, (mat (g * h) - 1) i j ∈ Λ n := fun n g h hg hh i j => by
    have e : mat (g * h) - 1 = (mat g - 1) * (mat h - 1) + (mat g - 1) + (mat h - 1) := by
      rw [mm]; noncomm_ring
    rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
    exact add_mem (add_mem (sum_mem fun k _ => hmul n _ (hg i k) _ (hh k j)) (hg i j)) (hh i j)
  let K : ℕ → Subgroup (UA σ W.J) := fun n =>
    { carrier := {h | (∀ i j, (mat h - 1) i j ∈ Λ n) ∧ ∀ i j, (mat h⁻¹ - 1) i j ∈ Λ n}
      one_mem' := ⟨fun i j => by rw [m1, sub_self]; exact zero_mem _,
        fun i j => by rw [inv_one, m1, sub_self]; exact zero_mem _⟩
      mul_mem' := fun {g h} hg hh => ⟨key n g h hg.1 hh.1, by rw [mul_inv_rev]; exact key n _ _ hh.2 hg.2⟩
      inv_mem' := fun {g} hg => ⟨hg.2, by rw [inv_inv]; exact hg.1⟩ }
  have hK : Antitone K := fun m n hmn h hh => ⟨fun i j => hanti hmn (hh.1 i j), fun i j => hanti hmn (hh.2 i j)⟩
  refine ⟨K, hK, fun U hU => ?_, fun n h hh u hu => ?_, fun n => ?_⟩
  · let L : Filter (UA σ W.J) := ⨅ n, 𝓟 (K n : Set (UA σ W.J))
    have ent : ∀ f : UA σ W.J → Matrix (Fin d) (Fin d) (AE F E), (∀ n, ∀ h ∈ K n, ∀ i j, (f h - 1) i j ∈ Λ n) →
        Tendsto f L (𝓝 1) := fun f hf => by
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => fun V hV => ?_
      have hc : Continuous fun z : AE F E => z + (1 : Matrix (Fin d) (Fin d) (AE F E)) i j :=
        continuous_id.add continuous_const
      obtain ⟨n, hn⟩ := hbas _ (hc.continuousAt.preimage_mem_nhds (by rwa [zero_add]))
      refine mem_iInf_of_mem n fun h hh => ?_
      simpa using hn (hf n h hh i j)
    have hL : L ≤ 𝓝 1 := by
      have : Tendsto (fun h : UA σ W.J => h) L (𝓝 1) := by
        refine tendsto_subtype_rng.2 (Units.isInducing_embedProduct.tendsto_nhds_iff.2 ?_)
        exact (ent mat fun n h hh => hh.1).prodMk_nhds
          ((MulOpposite.continuous_op.tendsto _).comp (ent (fun h => mat h⁻¹) fun n h hh => hh.2))
      exact this
    have hdir : Directed (· ≥ ·) fun n => 𝓟 (K n : Set (UA σ W.J)) :=
      Antitone.directed_ge fun m n hmn => principal_mono.2 (hK hmn)
    exact (mem_iInf_of_directed hdir U).1 (hL hU)
  · exact Matrix.ext fun i j => hat n _ (hh.1 i j) u hu
  · obtain ⟨V, hV, hVn⟩ := hop n
    have ent : ∀ f : UA σ W.J → Matrix (Fin d) (Fin d) (AE F E), Continuous f → f 1 = 1 →
        ∀ᶠ h in 𝓝 (1 : UA σ W.J), ∀ i j, (f h - 1) i j ∈ V := fun f hf h1 => by
      refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
      have hc : Continuous fun h => (f h - 1) i j := by
        simp only [Matrix.sub_apply, sub_eq_add_neg]
        exact (hf.matrix_elem i j).add continuous_const
      exact hc.continuousAt.preimage_mem_nhds (by simpa [h1] using hV)
    have h1 := ent mat (Units.continuous_val.comp continuous_subtype_val) m1
    have h2 := ent (fun h => mat h⁻¹) (Units.continuous_coe_inv.comp continuous_subtype_val) (by rw [inv_one, m1])
    refine ⟨_, h1.and h2, fun h hh ha => ⟨fun i j => hVn _ (hh.1 i j) fun u hu => congrFun (congrFun (ha u hu) i) j,
      fun i j => hVn _ (hh.2 i j) fun u hu => ?_⟩⟩
    have e : mat h⁻¹ - 1 = -(mat h⁻¹ * (mat h - 1)) := by
      rw [mul_sub, ← mm, inv_mul_cancel, m1, mul_one, neg_sub]
    have e2 : u • (mat h⁻¹ - 1) = 0 := by rw [e, smul_neg, ← Matrix.mul_smul, ha u hu, Matrix.mul_zero, neg_zero]
    exact congrFun (congrFun e2 i) j

end PositivityTheory.ThKH.Locrep
