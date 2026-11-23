import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace GeneralLinearEntryConvergence

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem tendsto_af {ι : Type} {l : Filter ι} (x : Af E) (z : ι → Af E)
    (h1 : ∀ w : Pl E, ∀ᶠ t in l, z t w = x w)
    (h2 : ∀ᶠ t in l, ∀ w : Pl E, z t w - x w ∈ w.adicCompletionIntegers E) :
    Tendsto z l (𝓝 x) := by
  classical
  let A : ∀ w : Pl E, Set (w.adicCompletion E) := fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))
  let sm : (∀ w : Pl E, A w) → Af E := fun y =>
    RestrictedProduct.structureMap (fun w : Pl E => w.adicCompletion E) A cofinite y
  have hsm : Continuous sm :=
    (RestrictedProduct.isEmbedding_structureMap (R := fun w : Pl E => w.adicCompletion E) (A := A)
      (𝓕 := cofinite)).continuous
  let u0 : ∀ w : Pl E, A w := fun w => ⟨0, zero_mem (w.adicCompletionIntegers E)⟩
  let u : ι → ∀ w : Pl E, A w := fun t w =>
    if h : z t w - x w ∈ w.adicCompletionIntegers E then ⟨_, h⟩ else u0 w
  have hu : Tendsto u l (𝓝 u0) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h1 w] with t ht
    have h0 : z t w - x w ∈ w.adicCompletionIntegers E := by
      rw [ht, sub_self]; exact zero_mem _
    simp only [u, dif_pos h0]
    apply Subtype.ext
    change (0 : w.adicCompletion E) = z t w - x w
    rw [ht, sub_self]
  have hv : Tendsto (fun t => sm (u t)) l (𝓝 (sm u0)) := (hsm.tendsto u0).comp hu
  have e0 : sm u0 = 0 := by
    ext w
    rfl
  rw [e0] at hv
  have hv' : Tendsto (fun t => z t - x) l (𝓝 0) := by
    refine hv.congr' ?_
    filter_upwards [h2] with t ht
    apply Subtype.ext
    funext w
    change (u t w : w.adicCompletion E) = z t w - x w
    simp only [u, dif_pos (ht w)]
  have := (tendsto_const_nhds (x := x)).add hv'
  simpa using this

theorem tendsto_ad {ι : Type} {l : Filter ι} (y : Ad E) (z : ι → Ad E) (h1 : ∀ t, (z t).1 = y.1)
    (h2 : Tendsto (fun t => (z t).2) l (𝓝 y.2)) : Tendsto z l (𝓝 y) := by
  refine (Prod.tendsto_iff _ _).2 ⟨?_, h2⟩
  simp only [h1]
  exact tendsto_const_nhds

theorem tendsto_gl {ι : Type} {l : Filter ι} (x : GA E a) (z : ι → GA E a)
    (h1 : ∀ i j, Tendsto (fun t => (z t).val i j) l (𝓝 (x.val i j)))
    (h2 : ∀ i j, Tendsto (fun t => (z t)⁻¹.val i j) l (𝓝 (x⁻¹.val i j))) : Tendsto z l (𝓝 x) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine Tendsto.prodMk_nhds ?_ ?_
  · exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h1 i j
  · exact (MulOpposite.continuous_op.tendsto _).comp
      (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h2 i j)

variable [IsTotallyComplex E]

theorem tendsto_entry (S : Finset (Pl E)) (x : GA E a) (z : Finset (Pl E) → GA E a)
    (hinf : ∀ T, cInf (z T) = cInf x) (hloc : ∀ T w, (w ∈ S ∨ w ∈ T) → cLoc w (z T) = cLoc w x)
    (hone : ∀ T w, w ∉ S → w ∉ T → cLoc w (z T) = 1) (i j : Fin a) :
    Tendsto (fun T => (z T).val i j) atTop (𝓝 (x.val i j)) := by
  classical
  refine tendsto_ad _ _ (fun T => ?_) (tendsto_af _ _ (fun w => ?_) ?_)
  · have h := congrArg (fun m : GL (Fin a) (Cinf E) => m.val i j) (hinf T)
    exact (infEq E).symm.injective h
  · filter_upwards [eventually_ge_atTop {w}] with T hT
    exact congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j)
      (hloc T w (Or.inr (hT (Finset.mem_singleton_self w))))
  · have hx : ∀ᶠ w in cofinite, (x.val i j).2 w ∈ w.adicCompletionIntegers E := (x.val i j).2.2
    set F := (Filter.eventually_cofinite.1 hx).toFinset
    filter_upwards [eventually_ge_atTop F] with T hT w
    by_cases hw : w ∈ S ∨ w ∈ T
    · have h := congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j) (hloc T w hw)
      change ((z T).val i j).2 w = (x.val i j).2 w at h
      rw [h, sub_self]
      exact zero_mem _
    · rw [not_or] at hw
      have h := congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j) (hone T w hw.1 hw.2)
      change ((z T).val i j).2 w = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j at h
      have hwF : w ∉ F := fun h' => hw.2 (hT h')
      have hxw : (x.val i j).2 w ∈ w.adicCompletionIntegers E := by
        by_contra hc
        exact hwF ((Filter.eventually_cofinite.1 hx).mem_toFinset.2 hc)
      refine sub_mem ?_ hxw
      rw [h, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _

theorem step1 (hG : G0) (S : Finset (Pl E)) (f : GA E a → ℂ)
    (hf : ∀ w, w ∉ S → ∀ h, cLoc w h = 1 → f h = 0 → ∀ u, f (h * fl a w u) = 0)
    (g g₀ : GA E a) (hinf : cInf g₀ = cInf g) (hS : ∀ w ∈ S, cLoc w g₀ = cLoc w g) (hIn : InS S g₀)
    (h0 : f g₀ = 0) (T : Finset (Pl E)) :
    ∃ h : GA E a, f h = 0 ∧ cInf h = cInf g ∧ (∀ w, (w ∈ S ∨ w ∈ T) → cLoc w h = cLoc w g) ∧
      (∀ w, w ∉ S → w ∉ T → cLoc w h = 1) := by
  classical
  obtain ⟨-, -, h3, h4, h5, -⟩ := hG E a
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨g₀, h0, hinf, fun w hw => ?_, fun w hw _ => hIn w hw⟩
    rcases hw with hw | hw
    · exact hS w hw
    · simp at hw
  | insert w T hwT ih =>
    obtain ⟨h, hf0, hi, hl, ho⟩ := ih
    by_cases hwS : w ∈ S
    · refine ⟨h, hf0, hi, fun v hv => ?_, fun v hv hv' => ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')⟩
      rcases hv with hv | hv
      · exact hl v (Or.inl hv)
      · rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hl v (Or.inl hwS)
        · exact hl v (Or.inr hv)
    · refine ⟨h * fl a w (cLoc w g), hf w hwS h (ho w hwS hwT) hf0 _, ?_, fun v hv => ?_, fun v hv hv' => ?_⟩
      · rw [map_mul, h3, mul_one, hi]
      · rw [map_mul]
        by_cases hvw : v = w
        · subst hvw
          rw [h4, ho v hwS hwT, one_mul]
        · rw [h5 _ _ _ hvw, mul_one]
          rcases hv with hv | hv
          · exact hl v (Or.inl hv)
          · exact hl v (Or.inr ((Finset.mem_insert.1 hv).resolve_left hvw))
      · have hvw : v ≠ w := fun e => hv' (e ▸ Finset.mem_insert_self w T)
        rw [map_mul, h5 _ _ _ hvw, mul_one]
        exact ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')

end GeneralLinearEntryConvergence

open GeneralLinearEntryConvergence in
theorem convergence_entries_general_linear : G0 → PlacewiseToOutsideS := by
  intro hG E _ _ _ a S f hfc hf g g₀ hinf hS hIn h0
  choose H hH using step1 hG S f hf g g₀ hinf hS hIn h0
  have hT : Tendsto H atTop (𝓝 g) := by
    refine tendsto_gl g H (tendsto_entry S g H (fun T => (hH T).2.1) (fun T => (hH T).2.2.1)
      (fun T => (hH T).2.2.2)) (tendsto_entry S g⁻¹ (fun T => (H T)⁻¹) (fun T => ?_) (fun T w hw => ?_)
      (fun T w hw hw' => ?_))
    · rw [map_inv, map_inv, (hH T).2.1]
    · rw [map_inv, map_inv, (hH T).2.2.1 w hw]
    · rw [map_inv, (hH T).2.2.2 w hw hw', inv_one]
  have h1 := (hfc.tendsto g).comp hT
  have h2 : Tendsto (f ∘ H) atTop (𝓝 0) := by
    have e : f ∘ H = fun _ => 0 := funext fun T => (hH T).1
    rw [e]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end PositivityTheory.jumpWindows

end
