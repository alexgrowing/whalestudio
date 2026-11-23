import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.H2GaloisQuotientEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.H2RightExactModL
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LocEuler

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem finrank_iInf_ker_add_sum_le_of_surjective {k V : Type} [Field k] [AddCommGroup V] [Module k V] {ι : Type} [Fintype ι]
    (W U : ι → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, AddCommGroup (U i)]
    [∀ i, Module k (U i)] (hV : Module.Finite k V) (hW : ∀ i, Module.Finite k (W i))
    (r : ∀ i, V →ₗ[k] W i) (f : ∀ i, W i →ₗ[k] U i) (hf : ∀ i, Function.Surjective (f i))
    (p : ∀ i, V →ₗ[k] U i) (hp : ∀ i, p i = (f i).comp (r i)) :
    finrank k (⨅ i, LinearMap.ker (p i) : Submodule k V) + ∑ i, finrank k (U i) ≤
      finrank k (⨅ i, LinearMap.ker (r i) : Submodule k V) + ∑ i, finrank k (W i) := by
  classical
  haveI := hV
  haveI := hW
  obtain rfl : p = fun i => (f i).comp (r i) := funext hp
  set X : Submodule k V := ⨅ i, LinearMap.ker ((f i).comp (r i)) with hX
  set Y : Submodule k V := ⨅ i, LinearMap.ker (r i) with hY
  have hmem : ∀ x : X, ∀ i, r i x ∈ LinearMap.ker (f i) := fun x i => by
    have := (Submodule.mem_iInf _).mp x.2 i
    simpa using this
  let g : X →ₗ[k] (∀ i, LinearMap.ker (f i)) :=
    LinearMap.pi fun i => ((r i).comp X.subtype).codRestrict (LinearMap.ker (f i)) (fun x => hmem x i)
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : finrank k (LinearMap.range g) ≤ ∑ i, finrank k (LinearMap.ker (f i)) := by
    calc _ ≤ finrank k (∀ i, LinearMap.ker (f i)) := Submodule.finrank_le _
      _ = _ := Module.finrank_pi_fintype k
  have h3 : finrank k (LinearMap.ker g) ≤ finrank k Y := by
    let e : LinearMap.ker g →ₗ[k] Y := (X.subtype.comp (LinearMap.ker g).subtype).codRestrict Y (fun x => by
      have hx := LinearMap.mem_ker.mp x.2
      refine (Submodule.mem_iInf _).mpr fun i => ?_
      have := congrArg Subtype.val (congrFun hx i)
      exact this)
    refine LinearMap.finrank_le_finrank_of_injective (f := e) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have h4 : ∀ i, finrank k (LinearMap.ker (f i)) + finrank k (U i) = finrank k (W i) := by
    intro i
    have := LinearMap.finrank_range_add_finrank_ker (f i)
    rw [LinearMap.range_eq_top.mpr (hf i), finrank_top] at this
    omega
  have h5 : ∑ i, finrank k (LinearMap.ker (f i)) + ∑ i, finrank k (U i) = ∑ i, finrank k (W i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => h4 i
  omega

theorem UpperTheory.V.GC.H2_galois_quotient_surjective :
    Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], IsTotallyReal F → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ) (h : GLink l S K π) (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M), ContAction ρ →
    ∀ c : InfinitePlace F → G F Ω, (∀ w, IsCCAt w (c w)) → ∀ (A : S → ValuationSubring Ω), (∀ v, IsPlaceOver (A v) v.1) → Loc.H0dual (cycF F Ω l k) (ρ.comp π) = ⊥ →
    ∀ (Q : S → Type) [∀ v, AddCommGroup (Q v)] [∀ v, Module k (Q v)] [∀ v, TopologicalSpace (Q v)] [∀ v, DiscreteTopology (Q v)] (σ : ∀ v, Representation k (Dec (F := F) (A v)) (Q v)) (q : ∀ v, M →ₗ[k] Q v)
    (hq : ∀ v s m, q v (ρ ((π.comp (Dec (F := F) (A v)).subtype) s) m) = σ v s (q v m)), (∀ v, Function.Surjective (q v)) →
    finrank k (⨅ v, LinearMap.ker (compatiblePairH2 ρ (σ v) (π.comp (Dec (F := F) (A v)).subtype) (h.cont.comp continuous_subtype_val) (q v) continuous_of_discreteTopology (hq v)) : Submodule k (H2 ρ)) +
      ∑ v, finrank k (H2 (σ v)) + finrank k (H0 ρ) + finrank ℚ F * finrank k M ≤ finrank k (H1 ρ) + ∑ w, finrank k (LinearMap.ker (ρ (π (c w)) - 1)) := by
  intro P F Ω _ _ _ _ _ l _ hF S K Γ _ _ _ _ _ _ π h k _ _ _ M _ _ _ _ _ ρ hρ c hc A hA hdual Q _ _ _ _ σ q hq hsurj
  obtain ⟨_, hfin2, hG⟩ := H2_galois_quotient_eq P F Ω l hF S K Γ π h k M ρ hρ c hc A hA
  rw [hdual, finrank_bot, add_zero] at hG
  have hcv : ∀ v : S, Continuous (π.comp (Dec (F := F) (A v)).subtype) :=
    fun v => h.cont.comp continuous_subtype_val
  have hρv : ∀ v : S, ReciprocityTheory.Gal.ContAction (ρ.comp (π.comp (Dec (F := F) (A v)).subtype)) :=
    fun v => hρ.comp (((hcv v).comp continuous_fst).prodMk continuous_snd)
  have hfinv : ∀ v : S, Module.Finite k (H2 (ρ.comp (π.comp (Dec (F := F) (A v)).subtype))) :=
    fun v => (locEuler P.lf P.lt P.le F Ω l v.1 (A v) (hA v) k M _ (hρv v)).2.1
  have hontov : ∀ v : S, Function.Surjective (mapH2 (ρ.comp (π.comp (Dec (F := F) (A v)).subtype)) (σ v) (q v)
      continuous_of_discreteTopology (hq v)) :=
    fun v => local_second_cohomology_surjective_at_place P.lf F Ω l v.1 (A v) (hA v) k M (Q v) _ (σ v) (hρv v) (q v) (hq v) (hsurj v)
  have key := finrank_iInf_ker_add_sum_le_of_surjective (k := k) (V := H2 ρ)
    (fun v : S => H2 (ρ.comp (π.comp (Dec (F := F) (A v)).subtype))) (fun v => H2 (σ v)) hfin2 hfinv
    (fun v => resH2 ρ _ (hcv v))
    (fun v => mapH2 _ (σ v) (q v) continuous_of_discreteTopology (hq v)) hontov
    (fun v => compatiblePairH2 ρ (σ v) (π.comp (Dec (F := F) (A v)).subtype) (h.cont.comp continuous_subtype_val)
      (q v) continuous_of_discreteTopology (hq v))
    (fun v => Submodule.linearMap_qext _ (LinearMap.ext fun f => rfl))
  unfold Sha2 at hG
  beta_reduce at hG key
  omega
