import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

open Filter Topology

namespace UpperTheory.Gal.Lim

theorem exists_trace_limit : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (a : ℕ) (J I : Type) (x : J → Γ) (θ : J → PadicAlgCl l) (L : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] L → (∀ j, θ j ∈ L) → ∀ (ρ : I → (Γ →* GL (Fin a) (PadicAlgCl l))) (η : I → J → PadicAlgCl l) (D : I → Set J), (∀ i, Continuous (ρ i)) → (∀ i, ∀ j ∈ D i, η i j = trc (ρ i) (x j)) → (∀ s : Finset I, Dense (x '' ⋂ i ∈ s, D i)) → PolyApprox θ (Set.range η) → ∃ t : Γ → PadicAlgCl l, (∀ g, t g ∈ L) ∧ (∀ (F : Finset I) (c : I → PadicAlgCl l) (ε : ℝ), (∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε) → ∀ g, ‖t g - ∑ i ∈ F, c i * trc (ρ i) g‖ ≤ ε) ∧ ∀ A : Set I, PolyApprox θ (η '' A) → PolyApprox t ((fun i => trc (ρ i)) '' A) ∧ ∀ j, (∀ i ∈ A, j ∈ D i) → t (x j) = θ j := by
  classical
  intro l _ Γ _ _ _ a J I x θ L hL hθL ρ η D hρ hη hD hθ
  have hcont : ∀ i, Continuous (trc (ρ i)) := fun i =>
    (Units.continuous_val.comp (hρ i)).matrix_trace
  have hLc : IsComplete (L : Set (PadicAlgCl l)) := by
    haveI : FiniteDimensional ℚ_[l] L.toSubalgebra.toSubmodule := hL
    exact Submodule.complete_of_finiteDimensional L.toSubalgebra.toSubmodule
  have conv : ∀ A : Set I, PolyApprox θ (η '' A) → ∀ ε > 0, ∃ F : Finset I, (↑F ⊆ A) ∧
      ∃ c : I → PadicAlgCl l, ∀ P : MvPolynomial J ℤ,
        ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε := by
    intro A hA ε hε
    obtain ⟨s, c, hs, hc⟩ := hA ε hε
    rcases s.eq_empty_or_nonempty with rfl | ⟨f0, hf0⟩
    · exact ⟨∅, by simp, fun _ => 0, fun P => le_of_eq_of_le (by simp only [Finset.sum_empty]; rfl) (hc P)⟩
    haveI : Nonempty I := ⟨(hs hf0).choose⟩
    have hex : ∀ f ∈ s, ∃ i, i ∈ A ∧ η i = f := fun f hf => hs hf
    choose! k hkA hk using hex
    refine ⟨s.image k, ?_, fun i => c (η i), fun P => ?_⟩
    · intro i hi
      rw [Finset.coe_image] at hi
      obtain ⟨f, hf, rfl⟩ := hi
      exact hkA f hf
    · rw [Finset.sum_image (fun f hf f' hf' e => by rw [← hk f hf, ← hk f' hf', e])]
      have e2 : ∑ f ∈ s, c (η (k f)) * MvPolynomial.aeval (η (k f)) P
          = ∑ f ∈ s, c f * MvPolynomial.aeval f P :=
        Finset.sum_congr rfl fun f hf => by rw [hk f hf]
      rw [e2]
      exact hc P
  set B : Filter J := ⨅ i, Filter.principal (D i) with hBdef
  have hDF : ∀ F : Finset I, (⋂ i ∈ F, D i) ∈ B := fun F =>
    (Filter.biInter_finset_mem F).2 fun i _ => Filter.mem_iInf_of_mem i (Filter.mem_principal_self _)
  have hne : ∀ g : Γ, (Filter.comap x (𝓝 g) ⊓ B).NeBot := by
    intro g
    refine (((nhds_basis_opens g).comap x).inf (Filter.hasBasis_iInf_principal_finite D)).neBot_iff.2 ?_
    rintro ⟨U, T⟩ ⟨⟨hgU, hU⟩, hT⟩
    obtain ⟨y, hyU, j, hj, rfl⟩ := (hD hT.toFinset).inter_open_nonempty U hU ⟨g, hgU⟩
    exact ⟨j, hyU, by simpa using hj⟩
  have hbd : ∀ g (F : Finset I) (c : I → PadicAlgCl l) (ε : ℝ),
      (∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε) →
      ∀ r > 0, ∀ᶠ j in Filter.comap x (𝓝 g) ⊓ B, ‖θ j - ∑ i ∈ F, c i * trc (ρ i) g‖ ≤ ε + r := by
    intro g F c ε hc r hr
    have hTc : Continuous fun y => ∑ i ∈ F, c i * trc (ρ i) y :=
      continuous_finset_sum _ fun i _ => continuous_const.mul (hcont i)
    have hU : {y | ‖(∑ i ∈ F, c i * trc (ρ i) y) - ∑ i ∈ F, c i * trc (ρ i) g‖ < r} ∈ 𝓝 g :=
      (isOpen_lt (continuous_norm.comp (hTc.sub continuous_const)) continuous_const).mem_nhds (by simpa using hr)
    filter_upwards [Filter.mem_inf_of_left (Filter.preimage_mem_comap hU), Filter.mem_inf_of_right (hDF F)] with j hj1 hj2
    have hj2' : ∀ i ∈ F, j ∈ D i := by simpa using hj2
    have e1 : ∑ i ∈ F, c i * trc (ρ i) (x j)
        = ∑ i ∈ F, c i * MvPolynomial.aeval (η i) (MvPolynomial.X j : MvPolynomial J ℤ) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [MvPolynomial.aeval_X, hη i j (hj2' i hi)]
    have h1 := hc (MvPolynomial.X j)
    rw [MvPolynomial.aeval_X, ← e1] at h1
    have h2 : ‖(∑ i ∈ F, c i * trc (ρ i) (x j)) - ∑ i ∈ F, c i * trc (ρ i) g‖ < r := hj1
    calc ‖θ j - ∑ i ∈ F, c i * trc (ρ i) g‖
        = ‖(θ j - ∑ i ∈ F, c i * trc (ρ i) (x j)) + ((∑ i ∈ F, c i * trc (ρ i) (x j)) - ∑ i ∈ F, c i * trc (ρ i) g)‖ := by
          congr 1; abel
      _ ≤ ε + r := (norm_add_le _ _).trans (add_le_add h1 h2.le)
  have hlim : ∀ g : Γ, ∃ v ∈ L, Filter.Tendsto θ (Filter.comap x (𝓝 g) ⊓ B) (𝓝 v) := by
    intro g
    haveI := hne g
    have hcau : Cauchy (Filter.map θ (Filter.comap x (𝓝 g) ⊓ B)) := by
      refine Metric.cauchy_iff.2 ⟨inferInstance, fun e he => ?_⟩
      obtain ⟨F, -, c, hc⟩ := conv Set.univ (by rw [Set.image_univ]; exact hθ) (e / 5) (by positivity)
      refine ⟨θ '' {j | ‖θ j - ∑ i ∈ F, c i * trc (ρ i) g‖ ≤ e / 5 + e / 5},
        Filter.image_mem_map (hbd g F c _ hc _ (by positivity)), ?_⟩
      rintro _ ⟨j, hj, rfl⟩ _ ⟨j', hj', rfl⟩
      simp only [Set.mem_setOf_eq] at hj hj'
      rw [dist_eq_norm]
      calc ‖θ j - θ j'‖ = ‖(θ j - ∑ i ∈ F, c i * trc (ρ i) g) - (θ j' - ∑ i ∈ F, c i * trc (ρ i) g)‖ := by
            congr 1; abel
        _ ≤ ‖θ j - ∑ i ∈ F, c i * trc (ρ i) g‖ + ‖θ j' - ∑ i ∈ F, c i * trc (ρ i) g‖ := norm_sub_le _ _
        _ < e := by linarith
    obtain ⟨v, hv, hlimv⟩ := hLc _ hcau
      (Filter.le_principal_iff.2 (Filter.mem_map.2 (Filter.univ_mem' fun j => hθL j)))
    exact ⟨v, hv, hlimv⟩
  choose t htL htlim using hlim
  have hev : ∀ Q : MvPolynomial Γ ℤ, Continuous fun u : Γ → PadicAlgCl l => MvPolynomial.aeval u Q := by
    intro Q
    simp_rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
    exact MvPolynomial.continuous_eval _
  have core : ∀ (F : Finset I) (c : I → PadicAlgCl l) (ε : ℝ),
      (∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε) →
      ∀ Q : MvPolynomial Γ ℤ, ‖MvPolynomial.aeval t Q - ∑ i ∈ F, c i * MvPolynomial.aeval (trc (ρ i)) Q‖ ≤ ε := by
    intro F c ε hc Q
    let Ψ : (Γ → Γ × PadicAlgCl l) → PadicAlgCl l := fun w =>
      MvPolynomial.aeval (fun g => (w g).2) Q - ∑ i ∈ F, c i * MvPolynomial.aeval (fun g => trc (ρ i) (w g).1) Q
    have hΨc : Continuous Ψ :=
      ((hev Q).comp (continuous_pi fun g => continuous_snd.comp (continuous_apply g))).sub
        (continuous_finset_sum _ fun i _ => continuous_const.mul
          ((hev Q).comp (continuous_pi fun g => (hcont i).comp (continuous_fst.comp (continuous_apply g)))))
    let Z : Set (Γ × PadicAlgCl l) := (fun j => (x j, θ j)) '' ⋂ i ∈ F, D i
    have hmem : (fun g => (g, t g)) ∈ closure (Set.univ.pi fun _ : Γ => Z) := by
      rw [closure_pi_set]
      intro g _
      haveI := hne g
      refine mem_closure_of_tendsto ((Filter.tendsto_comap.mono_left inf_le_left).prodMk_nhds (htlim g)) ?_
      filter_upwards [Filter.mem_inf_of_right (hDF F)] with j hj
      exact ⟨j, hj, rfl⟩
    have hsub : closure (Set.univ.pi fun _ : Γ => Z) ⊆ {w | ‖Ψ w‖ ≤ ε} := by
      refine closure_minimal ?_ (isClosed_le (continuous_norm.comp hΨc) continuous_const)
      intro w hw
      have hw' : ∀ g, ∃ j, j ∈ ⋂ i ∈ F, D i ∧ (x j, θ j) = w g := fun g => hw g (Set.mem_univ g)
      choose σ hσD hσ using hw'
      have hwσ : w = fun g => (x (σ g), θ (σ g)) := funext fun g => (hσ g).symm
      subst hwσ
      have hσD' : ∀ g, ∀ i ∈ F, σ g ∈ D i := fun g => by simpa using hσD g
      show ‖MvPolynomial.aeval (fun g => θ (σ g)) Q
        - ∑ i ∈ F, c i * MvPolynomial.aeval (fun g => trc (ρ i) (x (σ g))) Q‖ ≤ ε
      have e0 : MvPolynomial.aeval (fun g => θ (σ g)) Q = MvPolynomial.aeval θ (MvPolynomial.rename σ Q) := by
        rw [MvPolynomial.aeval_rename]; rfl
      have e2 : ∑ i ∈ F, c i * MvPolynomial.aeval (fun g => trc (ρ i) (x (σ g))) Q
          = ∑ i ∈ F, c i * MvPolynomial.aeval (η i) (MvPolynomial.rename σ Q) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [MvPolynomial.aeval_rename,
          show (fun g => trc (ρ i) (x (σ g))) = η i ∘ σ from
            funext fun g => (hη i (σ g) (hσD' g i hi)).symm]
      rw [e0, e2]
      exact hc _
    have h := hsub hmem
    simp only [Set.mem_setOf_eq, Ψ] at h
    exact h
  refine ⟨t, htL, fun F c ε hc g => ?_, fun A hA => ⟨?_, ?_⟩⟩
  · have := core F c ε hc (MvPolynomial.X g)
    simpa [MvPolynomial.aeval_X] using this
  · intro ε hε
    obtain ⟨F, hFA, c, hc⟩ := conv A hA ε hε
    refine ⟨F.image (fun i => trc (ρ i)), fun f => ∑ i ∈ F.filter (fun i => trc (ρ i) = f), c i, ?_, fun Q => ?_⟩
    · rw [Finset.coe_image]; exact Set.image_mono hFA
    · have e : ∑ f ∈ F.image (fun i => trc (ρ i)),
          (∑ i ∈ F.filter (fun i => trc (ρ i) = f), c i) * MvPolynomial.aeval f Q
          = ∑ i ∈ F, c i * MvPolynomial.aeval (trc (ρ i)) Q := by
        calc _ = ∑ f ∈ F.image (fun i => trc (ρ i)), ∑ i ∈ F.filter (fun i => trc (ρ i) = f),
                c i * MvPolynomial.aeval (trc (ρ i)) Q := by
              refine Finset.sum_congr rfl fun f _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [(Finset.mem_filter.1 hi).2]
          _ = _ := Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) _
      exact le_of_eq_of_le (congrArg (fun z => ‖MvPolynomial.aeval t Q - z‖) e) (core F c ε hc Q)
  · intro j hj
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨F, hFA, c, hc⟩ := conv A hA (ε / 2) (by positivity)
    have h1 := core F c _ hc (MvPolynomial.X (x j))
    have h2 := hc (MvPolynomial.X j)
    simp only [MvPolynomial.aeval_X] at h1 h2
    have e : ∑ i ∈ F, c i * trc (ρ i) (x j) = ∑ i ∈ F, c i * η i j :=
      Finset.sum_congr rfl fun i hi => by rw [hη i j (hj i (hFA (Finset.mem_coe.2 hi)))]
    rw [e] at h1
    rw [dist_eq_norm]
    calc ‖t (x j) - θ j‖ = ‖(t (x j) - ∑ i ∈ F, c i * η i j) - (θ j - ∑ i ∈ F, c i * η i j)‖ := by
          congr 1; abel
      _ ≤ _ := norm_sub_le _ _
      _ ≤ ε := by linarith

end UpperTheory.Gal.Lim
