import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ExistsKhwGenSubOfKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Helpers

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem kfin_mapsTo_orth (U : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) (S : Submodule ℂ H)
    [FiniteDimensional ℂ S] (hS : ∀ x ∈ S, U x ∈ S) {v : H} (hv : v ∈ Sᗮ) : U v ∈ Sᗮ := by
  let L : H →ₗᵢ[ℂ] H := ⟨U.toLinearMap, hU⟩
  let f : S →ₗ[ℂ] S :=
    { toFun := fun x => ⟨U x, hS x x.2⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro c x; ext; simp }
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply L.injective
    exact congrArg Subtype.val hab
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  obtain ⟨s, hs⟩ := hsurj ⟨u, hu⟩
  have hsu : U (s : H) = u := congrArg Subtype.val hs
  rw [← hsu]
  have key : inner ℂ (U (s : H)) (U v) = inner ℂ (s : H) v := L.inner_map_map (s : H) v
  rw [key]
  exact hv _ s.2

theorem kfin_starProj_comm (U : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) (S : Submodule ℂ H)
    [FiniteDimensional ℂ S] [S.HasOrthogonalProjection] (hS : ∀ x ∈ S, U x ∈ S) (w : H) :
    S.starProjection (U w) = U (S.starProjection w) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hS _ (Submodule.starProjection_apply_mem S w)
  · intro x hx
    have hmem : w - S.starProjection w ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal w
    have h2 := kfin_mapsTo_orth U hU S hS hmem
    rw [map_sub] at h2
    exact Submodule.inner_left_of_mem_orthogonal hx h2

end Helpers

theorem kfin_diag_mem_Kset (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  unfold Kset
  rw [Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  · unfold Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm _ _

section Wt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kfin_wt_orth (hσ : IsURepOn (UJset ε) σ) {μ ν : Fin n → ℝ} {v w : H}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ v) (hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ ν w)
    (hne : μ ≠ ν) : inner ℂ v w = 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hd : ν a - μ a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  set c : ℝ := Real.pi / (ν a - μ a) with hc
  have hπ : (ν a - μ a) * c = Real.pi := by rw [hc]; field_simp
  let θ : Fin n → ℝ := fun b => if b = a then c else 0
  have hs : ∀ f : Fin n → ℝ, ∑ b, f b * θ b = f a * c := by
    intro f
    simp only [θ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  obtain ⟨h1, h2⟩ := kfin_diag_mem_Kset (n := n) ε θ
  have hK : Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε :=
    kfin_diag_mem_Kset ε θ
  have hU : Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) ∈ UJset ε := by
    show _ * Jm ε * _ = Jm ε
    rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').mp h1, Matrix.one_mul]
  obtain ⟨-, hiso, -⟩ := hσ
  let L : H →ₗᵢ[ℂ] H :=
    ⟨(σ (Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)))).toLinearMap, hiso _ hU⟩
  have hinner : inner ℂ (σ (Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I))) v)
      (σ (Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I))) w) = inner ℂ v w :=
    L.inner_map_map v w
  rw [hv θ hK, hw θ hK, inner_smul_left, inner_smul_right, hs μ, hs ν, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, ← mul_assoc, ← Complex.exp_add] at hinner
  have hexp : ((μ a * c : ℝ) : ℂ) * -Complex.I + ((ν a * c : ℝ) : ℂ) * Complex.I =
      (Real.pi : ℂ) * Complex.I := by
    rw [← hπ]; push_cast; ring
  rw [hexp, Complex.exp_pi_mul_I] at hinner
  linear_combination (-1 / 2 : ℂ) * hinner

theorem kfin_wts_finite (hσ : IsURepOn (UJset ε) σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    {μ : Fin n → ℝ | ∃ s ∈ S, s ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s}.Finite := by
  classical
  have hc : ∀ μ : {μ : Fin n → ℝ | ∃ s ∈ S, s ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s},
      ∃ s ∈ S, s ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ (μ : Fin n → ℝ) s := fun μ => μ.2
  choose f hfS hf0 hfw using hc
  let g : {μ : Fin n → ℝ | ∃ s ∈ S, s ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s} → S :=
    fun μ => ⟨f μ, hfS μ⟩
  have hli : LinearIndependent ℂ (S.subtype ∘ g) := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro i
      exact hf0 i
    · intro i j hij
      exact kfin_wt_orth hσ (hfw i) (hfw j) (fun h => hij (Subtype.ext h))
  have hfin := (LinearIndependent.of_comp S.subtype hli).finite
  exact Set.finite_coe_iff.mp hfin

end Wt

section Key

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem kfin_key (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V)
    (S : Submodule ℂ H) (hS : S ≤ closGen E V) [FiniteDimensional ℂ S]
    (hSK : ∀ k ∈ Kset ε, ∀ x ∈ S, σ k x ∈ S) (m : ℕ)
    (hm : ∀ (μ : Fin n → ℝ) (w : D), w ∈ genSub E V → IsKHWVec ε E μ w →
      (∃ s ∈ S, s ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s) → w ∈ layer ε E V m) :
    S ≤ (layer ε E V m).map D.subtype := by
  classical
  have hE := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hUK : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  set Lm : Submodule ℂ D := layer ε E V m with hLm
  have hLmf : FiniteDimensional ℂ Lm := finiteDimensional_layer hVf m
  haveI : CompleteSpace Lm := FiniteDimensional.complete ℂ Lm
  set Fm : Submodule ℂ H := Lm.map D.subtype with hFm
  have hFmf : FiniteDimensional ℂ Fm := Module.Finite.map Lm D.subtype
  haveI : CompleteSpace Fm := FiniteDimensional.complete ℂ Fm
  intro x hx
  by_contra hxF
  obtain ⟨y, hy⟩ : ∃ y, y = x - Fm.starProjection x := ⟨_, rfl⟩
  have hy0 : y ≠ 0 := by
    intro h
    apply hxF
    rw [← Submodule.starProjection_eq_self_iff]
    rw [hy] at h
    exact (sub_eq_zero.1 h).symm
  have hyF : y ∈ Fmᗮ := hy ▸ Fm.sub_starProjection_mem_orthogonal x
  have hFcl : Fm ≤ closGen E V :=
    (Submodule.map_mono (layer_le_genSub m)).trans (Submodule.le_topologicalClosure _)
  have hycl : y ∈ ((genSub E V).map D.subtype).topologicalClosure := by
    rw [hy]
    exact Submodule.sub_mem _ (hS hx) (hFcl (Fm.starProjection_apply_mem x))
  obtain ⟨z0, hz0M, hz0⟩ : ∃ z0 : D, z0 ∈ genSub E V ∧ inner ℂ (z0 : H) y ≠ 0 := by
    by_contra hno
    push_neg at hno
    have hyo : y ∈ ((genSub E V).map D.subtype)ᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro u ⟨z1, hz1, rfl⟩
      exact hno z1 hz1
    rw [← Submodule.orthogonal_closure] at hyo
    have := (Submodule.inf_orthogonal_eq_bot _).le ⟨hycl, hyo⟩
    exact hy0 ((Submodule.mem_bot ℂ).1 this)
  obtain ⟨l0, hl0⟩ := exists_layer_of_mem_genSub hE hVk hz0M
  have hLlf : FiniteDimensional ℂ (layer ε E V (max l0 m)) := finiteDimensional_layer hVf _
  obtain ⟨GD, hGD⟩ : ∃ GD : Submodule ℂ D, GD = layer ε E V (max l0 m) ⊓ Lmᗮ := ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z' : D, z' = z0 - Lm.starProjection z0 := ⟨_, rfl⟩
  have hz'GD : z' ∈ GD := by
    rw [hGD, hz']
    exact ⟨Submodule.sub_mem _ (layer_mono (le_max_left l0 m) hl0)
      (layer_mono (le_max_right l0 m) (Lm.starProjection_apply_mem z0)),
      Lm.sub_starProjection_mem_orthogonal z0⟩
  have hz'Lm : z' ∈ Lmᗮ := by
    rw [hGD] at hz'GD
    exact hz'GD.2
  have hz'x : inner ℂ (z' : H) x ≠ 0 := by
    have e1 : inner ℂ (z' : H) (Fm.starProjection x) = 0 := by
      obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.1 (Fm.starProjection_apply_mem x)
      rw [← hfx]
      have := (Submodule.mem_orthogonal' _ _).1 hz'Lm f hf
      rw [Submodule.coe_inner] at this
      exact this
    have e2 : inner ℂ ((Lm.starProjection z0 : D) : H) y = 0 :=
      (Submodule.mem_orthogonal _ _).1 hyF _ (Submodule.mem_map_of_mem (Lm.starProjection_apply_mem z0))
    have e3 : inner ℂ (z' : H) x = inner ℂ (z' : H) y + inner ℂ (z' : H) (Fm.starProjection x) := by
      rw [← inner_add_right, hy, sub_add_cancel]
    have e4 : inner ℂ (z' : H) y = inner ℂ (z0 : H) y := by
      rw [hz', Submodule.coe_sub, inner_sub_left, e2, sub_zero]
    rw [e3, e1, add_zero, e4]
    exact hz0
  have hLmk := layer_kStable hE hVk m
  have hGDk : IsKStableSub ε E GD := by
    rw [hGD]
    intro a b hab v hv
    refine ⟨layer_kStable hE hVk _ a b hab v hv.1, ?_⟩
    refine (Submodule.mem_orthogonal' _ _).2 fun u hu => ?_
    rw [hUK a b hab v u]
    exact (Submodule.mem_orthogonal' _ _).1 hv.2 _ (hLmk b a hab.symm u hu)
  have hGDf : FiniteDimensional ℂ GD := by
    rw [hGD]
    exact Submodule.finiteDimensional_of_le inf_le_left
  have hGDL : GD ≤ layer ε E V (max l0 m) := by rw [hGD]; exact inf_le_left
  have hGDo : GD ≤ Lmᗮ := by rw [hGD]; exact inf_le_right
  have hGDK := kStable_of_isKStableSub hσ hD GD hGDf hGDk
  obtain ⟨G0, hG0⟩ : ∃ G0 : Submodule ℂ D, G0 = GD ⊓ (Sᗮ).comap D.subtype := ⟨_, rfl⟩
  have hG0GD : G0 ≤ GD := by rw [hG0]; exact inf_le_left
  have hG0S : ∀ v ∈ G0, (v : H) ∈ Sᗮ := by
    intro v hv
    rw [hG0] at hv
    exact hv.2
  have hG0mem : ∀ v ∈ GD, (v : H) ∈ Sᗮ → v ∈ G0 := by
    intro v hv hvS
    rw [hG0]
    exact ⟨hv, hvS⟩
  have hG0f : FiniteDimensional ℂ G0 := Submodule.finiteDimensional_of_le hG0GD
  haveI : CompleteSpace G0 := FiniteDimensional.complete ℂ G0
  have hG0K : ∀ k ∈ Kset ε, ∀ v ∈ G0, ∃ w ∈ G0, (w : H) = σ k v := by
    intro k hk v hv
    obtain ⟨w, hw, hwv⟩ := hGDK k hk v (hG0GD hv)
    refine ⟨w, hG0mem w hw ?_, hwv⟩
    rw [hwv]
    exact kfin_mapsTo_orth (σ k) (hσ.2.1 k (closure_inUJ_of_mem_Kset hk)) S (hSK k hk) (hG0S v hv)
  have hG0k : IsKStableSub ε E G0 := isKStableSub_of_kStable hσ hD G0 hG0f hG0K
  obtain ⟨G1, hG1⟩ : ∃ G1 : Submodule ℂ D, G1 = GD ⊓ G0ᗮ := ⟨_, rfl⟩
  have hG1f : FiniteDimensional ℂ G1 := by
    rw [hG1]
    exact Submodule.finiteDimensional_of_le inf_le_left
  have hG1k : IsKStableSub ε E G1 := by
    rw [hG1]
    intro a b hab v hv
    refine ⟨hGDk a b hab v hv.1, ?_⟩
    refine (Submodule.mem_orthogonal' _ _).2 fun u hu => ?_
    rw [hUK a b hab v u]
    exact (Submodule.mem_orthogonal' _ _).1 hv.2 _ (hG0k b a hab.symm u hu)
  have hG1ne : G1 ≠ ⊥ := by
    intro hbot
    have hbb1 : z' - G0.starProjection z' ∈ G1 := by
      rw [hG1]
      exact ⟨Submodule.sub_mem _ hz'GD (hG0GD (G0.starProjection_apply_mem z')),
        G0.sub_starProjection_mem_orthogonal z'⟩
    rw [hbot] at hbb1
    have hbb0 : z' - G0.starProjection z' = 0 := (Submodule.mem_bot ℂ).1 hbb1
    have hz'G0 : z' ∈ G0 := by
      rw [sub_eq_zero.1 hbb0]
      exact G0.starProjection_apply_mem z'
    exact hz'x ((Submodule.mem_orthogonal' _ _).1 (hG0S z' hz'G0) x hx)
  obtain ⟨w, hwG1, hw0, μ, hμ⟩ := exists_khw hE hUK hG1f hG1k hG1ne
  have hwGD : w ∈ GD := by
    rw [hG1] at hwG1
    exact hwG1.1
  have hwG0o : w ∈ G0ᗮ := by
    rw [hG1] at hwG1
    exact hwG1.2
  have hwM : w ∈ genSub E V := layer_le_genSub _ (hGDL hwGD)
  have hwS : ∃ s ∈ S, s ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s := by
    refine ⟨S.starProjection (w : H), S.starProjection_apply_mem _, ?_, ?_⟩
    · intro h0
      have hwSo : (w : H) ∈ Sᗮ := by
        have := S.sub_starProjection_mem_orthogonal (w : H)
        rwa [h0, sub_zero] at this
      have := (Submodule.mem_orthogonal' _ _).1 hwG0o w (hG0mem w hwGD hwSo)
      exact hw0 ((inner_self_eq_zero (𝕜 := ℂ)).1 this)
    · intro θ hθ
      have hθK : Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
        rw [← mir_Kset_eq]; exact hθ
      have hwt := (isWtOn_iff hσ hD w μ).2 hμ.1
      rw [← kfin_starProj_comm _ (hσ.2.1 _ (closure_inUJ_of_mem_Kset hθK)) S (hSK _ hθK), hwt θ hθ,
        map_smul]
  have hwm := hm μ w hwM hμ hwS
  have := (Submodule.mem_orthogonal' _ _).1 (hGDo hwGD) w hwm
  exact hw0 ((inner_self_eq_zero (𝕜 := ℂ)).1 this)

end Key

section Data

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_kfin_le (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (S : Submodule ℂ H) (hS : S ≤ closGen E V) (hSf : FiniteDimensional ℂ S)
    (hSK : ∀ k ∈ Kset ε, ∀ x ∈ S, σ k x ∈ S) : S ≤ (genSub E V).map D.subtype := by
  classical
  have hE := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  haveI := hSf
  have hWf := kfin_wts_finite (ε := ε) hσ S
  choose kf hkf using fun μ => khw_mem_layer hE hU hV hc hgap μ
  refine (kfin_key hσ hD hV.1 hV.2.1 S hS hSK (hWf.toFinset.sup kf) ?_).trans
    (Submodule.map_mono (layer_le_genSub _))
  intro μ w hw hμ hμS
  exact layer_mono (Finset.le_sup (hWf.mem_toFinset.2 hμS)) (hkf μ w hw hμ)

end Data

end ReciprocityTheory.ChartRestriction.DS
