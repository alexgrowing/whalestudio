import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLeSpanInvariantsOfSemilinearFamily
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem exists_invariant_basis {F₀ F R M D : Type} [Field F₀] [Field F] [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype D] (κ : F →+* R) (ι : F₀ →+* F) (σ : D → (F →+* F)) (t : D → (M →+ M)) (V : AddSubgroup M)
    (hV : ∀ c, ∀ y ∈ V, κ c • y ∈ V) {m : ℕ} (u : Fin m → M)
    (hu : ∀ y ∈ V, ∃ c : Fin m → F, y = ∑ j, κ (c j) • u j) (hσ : Function.Injective σ)
    (hsl : ∀ d c y, t d (κ c • y) = κ (σ d c) • t d y) (hst : ∀ d, ∀ y ∈ V, t d y ∈ V)
    (hav : ∀ d, ∀ y ∈ V, t d (∑ d', t d' y) = ∑ d', t d' y) (hid : ∃ d, ∀ y ∈ V, t d y = y)
    (hfix : ∀ c, (∀ d, σ d c = c) → ∃ c₀, ι c₀ = c) :
    ∃ s, s ≤ m ∧ ∃ w : Fin s → M, (∀ j, w j ∈ V) ∧ (∀ j d, t d (w j) = w j) ∧
      (∀ c : Fin s → F, ∑ j, κ (c j) • w j = 0 → c = 0) ∧
      (∀ y ∈ V, ∃ c : Fin s → F, y = ∑ j, κ (c j) • w j) ∧
      (∀ y ∈ V, (∀ d, t d y = y) → ∃ c : Fin s → F₀, y = ∑ j, κ (ι (c j)) • w j) := by
  classical
  let : Module F M := Module.compHom M κ
  have hs : ∀ (c : F) (y : M), c • y = κ c • y := fun _ _ => rfl
  let V' : Submodule F M := { V with smul_mem' := fun c y hy => hV c y hy }
  have h1 := GlobalTheory.stable_le_span_invariants_of_semilinear_family F M D σ t V' hσ (fun d c y _ => hsl d c y)
    hst hav hid
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent F {y | y ∈ V' ∧ ∀ d, t d y = y}
  have hle : V' ≤ Submodule.span F (Set.range u) := by
    intro y hy
    obtain ⟨c, rfl⟩ := hu y hy
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (c j) (Submodule.subset_span ⟨j, rfl⟩)
  have hbu : Set.range ((↑) : b → M) ≤ Submodule.span F (Set.range u) := by
    rintro _ ⟨x, rfl⟩
    exact hle (hb x.2).1
  have : Finite b := by
    have : Module.Finite F (Submodule.span F (Set.range u)) := Module.Finite.span_of_finite F (Set.finite_range u)
    have h0 : LinearIndependent F fun x : b => (⟨x.1, hbu ⟨x, rfl⟩⟩ : Submodule.span F (Set.range u)) :=
      LinearIndependent.of_comp (Submodule.subtype _) hli
    exact h0.finite
  have : Fintype b := Fintype.ofFinite b
  have hc := (linearIndependent_le_span_aux' _ hli (Set.range u) hbu).trans (Fintype.card_range_le u)
  rw [Fintype.card_fin] at hc
  let e := (Fintype.equivFin b).symm
  have hli' : LinearIndependent F (fun j => (e j : M)) := hli.comp e e.injective
  have hind : ∀ c : Fin (Fintype.card b) → F, ∑ j, κ (c j) • (e j : M) = 0 → c = 0 := fun c hc =>
    funext (Fintype.linearIndependent_iff.1 hli' c hc)
  have hgen : ∀ y ∈ V, ∃ c : Fin (Fintype.card b) → F, y = ∑ j, κ (c j) • (e j : M) := by
    intro y hy
    have h2 : y ∈ Submodule.span F (Set.range fun j => (e j : M)) := by
      have h3 : (Set.range fun j => (e j : M)) = b := by
        ext x
        constructor
        · rintro ⟨j, rfl⟩; exact (e j).2
        · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩
      rw [h3, hsp]
      exact h1 hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 h2
    exact ⟨c, hc.symm⟩
  refine ⟨_, hc, fun j => e j, fun j => (hb (e j).2).1, fun j => (hb (e j).2).2, hind, hgen, ?_⟩
  intro y hy hinv
  obtain ⟨c, rfl⟩ := hgen y hy
  have h4 : ∀ j d, σ d (c j) = c j := by
    intro j d
    have h5 := hinv d
    rw [map_sum] at h5
    simp only [hsl, fun j => (hb (e j).2).2 d] at h5
    have h6 := hind (fun j => σ d (c j) - c j) (by
      simp only [map_sub, sub_smul, Finset.sum_sub_distrib, h5, sub_self])
    exact sub_eq_zero.1 (congrFun h6 j)
  choose c₀ hc₀ using fun j => hfix (c j) (h4 j)
  exact ⟨c₀, by simp only [hc₀]⟩

theorem exists_frame_of_invariants : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk) (a : G → (Rk →ₐ[k] Rk)) (ι : k⸨X⸩ →+* k⸨X⸩) (σ : {δ // δ ∈ W.DelF} → (k⸨X⸩ →+* k⸨X⸩)), IsRed E ρ (k := k) lam κ → IsDel E ρ κ a ι σ → ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∀ i, (∃ u : Fin A.m → W.DD T, ∀ x, ∃ c : Fin A.m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) → ∃ β : Vc k A.m →+ Rk ⊗[k] (Fin A.m → k), IsFrame (κ.comp ι) (eps E ρ i) β ∧ ∀ y, (∃ x, β x = y) ↔ ∃ x : ↥(DΔ W T), y = eps E ρ i • J E ρ T q x := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W RA RW _ _ _ _ inclR φR gR πA
    E k _ _ Rk _ _ _ _ ρ lam κ a ι σ hR hD T A q hq i hu
  classical
  obtain ⟨u, hu⟩ := hu
  set ε := eps E ρ i with hε
  have hεε : ε * ε = ε := eps_idem E ρ i
  choose g hg using fun δ : {δ // δ ∈ W.DelF} => W.resΓ_onto δ.1
  let f : W.DD T →+ Rk ⊗[k] (Fin A.m → k) := (DistribSMul.toAddMonoidHom _ ε).comp (J E ρ T q)
  have hf : ∀ x, f x = ε • J E ρ T q x := fun _ => rfl
  let t : {δ // δ ∈ W.DelF} → (Rk ⊗[k] (Fin A.m → k) →+ Rk ⊗[k] (Fin A.m → k)) :=
    fun δ => (Act a A (g δ)).toAddMonoidHom
  have ht : ∀ δ x, t δ (f x) = f (W.γD T δ.1 x) := by
    intro δ x
    change Act a A (g δ) (ε • J E ρ T q x) = _
    rw [Act_smul, hD.a_eps, ← J_act E ρ hD.a_ρ T A q hq, hg, hf]
  have hsum : ∀ x, ∑ δ, t δ (f x) = f (∑ δ ∈ W.DelF, W.γD T δ x) := by
    intro x
    simp only [ht]
    rw [map_sum, Finset.sum_coe_sort W.DelF (fun δ => f (W.γD T δ x))]
  have hinv : ∀ x ∈ DΔ W T, ∀ δ, t δ (f x) = f x := by
    intro x hx δ
    rw [ht, hx δ.1 δ.2]
  have hV : ∀ c, ∀ y ∈ f.range, κ c • y ∈ f.range := by
    rintro c _ ⟨x, rfl⟩
    obtain ⟨e, he⟩ := hR.κ_of i c
    refine ⟨e • x, ?_⟩
    rw [hf, hf, J_smul, smul_smul, smul_smul, ← he, mul_comm]
  have hsl : ∀ d c y, t d (κ c • y) = κ (σ d c) • t d y := by
    intro d c y
    change Act a A (g d) (κ c • y) = κ (σ d c) • Act a A (g d) y
    rw [Act_smul, hD.a_κ _ d (hg d)]
  obtain ⟨s, hs, w, hwV, hwi, hind, hgen, hgen₀⟩ := exists_invariant_basis κ ι σ t f.range hV
    (fun j => f (u j)) (by rintro _ ⟨x, rfl⟩; exact hu x) hD.σ_inj hsl
    (by rintro d _ ⟨x, rfl⟩; exact ⟨_, (ht d x).symm⟩)
    (by rintro d _ ⟨x, rfl⟩; rw [hsum]; exact hinv _ (sum_mem_DΔ T x) d)
    ⟨⟨1, (W.DelF_def 1).2 ⟨1, one_pos, one_pow 1⟩⟩, by rintro _ ⟨x, rfl⟩; rw [ht, W.γD_one]⟩
    (fun c => (hD.σ_fix c).1)
  have hspan : ∀ y : Fin A.m → k, ε ⊗ₜ[k] y ∈ Submodule.span Rk (Set.range w) := by
    intro y
    obtain ⟨x, rfl⟩ := hq.1 y
    have key : ∀ z ∈ Submodule.span Rk (Set.range (J E ρ T q)), ε • z ∈ Submodule.span Rk (Set.range w) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, rfl⟩ := hz
        obtain ⟨c, hc⟩ := hgen _ ⟨x, rfl⟩
        rw [← hf, hc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy
    have := key _ (J_span E ρ T q x)
    rwa [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this
  have hm : A.m ≤ s := card_le_of_span (eps_idem E ρ i) (hR.eps_ne i) w (Pi.basisFun k (Fin A.m))
    (Pi.basisFun k (Fin A.m)).linearIndependent (fun j => hspan _)
  obtain rfl : s = A.m := le_antisymm hs hm
  let β : Vc k A.m →+ Rk ⊗[k] (Fin A.m → k) :=
    { toFun := fun c => ∑ j, κ (ι (c j)) • w j
      map_zero' := by simp
      map_add' := fun c c' => by simp [add_smul, Finset.sum_add_distrib] }
  have hβ : ∀ c, β c = ∑ j, κ (ι (c j)) • w j := fun _ => rfl
  have hβV : ∀ c, β c ∈ f.range := fun c => by
    rw [hβ]; exact AddSubgroup.sum_mem _ fun j _ => hV _ _ (hwV j)
  refine ⟨β, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have := hind (fun j => ι (c j)) hc
    funext j
    exact (map_eq_zero ι).1 (congrFun this j)
  · intro c x
    simp [hβ, Finset.smul_sum, smul_smul]
  · intro c
    obtain ⟨x, hx⟩ := hβV c
    rw [← hx, hf, smul_smul, hεε]
  · intro y
    refine Submodule.span_mono ?_ (hspan y)
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    rw [hβ, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [hj]
    · simp
  · intro y
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨x, hx⟩ := hβV c
      have hi : ∀ δ, t δ (β c) = β c := by
        intro δ
        rw [hβ, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsl, hwi, (hD.σ_fix _).2 ⟨_, rfl⟩]
      obtain ⟨r, hr⟩ := hR.res_surj ((W.DelF.card : k)⁻¹)
      refine ⟨⟨r • ∑ δ ∈ W.DelF, W.γD T δ x, ?_⟩, ?_⟩
      · intro δ hδ
        rw [map_smul, sum_mem_DΔ T x δ hδ]
      · change _ = ε • J E ρ T q (r • _)
        rw [J_smulO, smul_comm, ← hf, ← hsum, hx, hr, algebraMap_smul]
        simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_coe]
        rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hD.card_ne, one_smul]
    · rintro ⟨x, rfl⟩
      obtain ⟨c, hc⟩ := hgen₀ _ ⟨x.1, rfl⟩ (hinv x.1 x.2)
      exact ⟨c, hc.symm⟩

end GlobalTheory.RedFun
