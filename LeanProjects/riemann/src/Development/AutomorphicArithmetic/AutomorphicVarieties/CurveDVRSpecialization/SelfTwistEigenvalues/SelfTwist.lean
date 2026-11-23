import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.CliffordSS
open Polynomial Matrix

private theorem selfTwist_commonEig {K M ι : Type} [Field K] [IsAlgClosed K] [AddCommGroup M]
    [Module K M] [FiniteDimensional K M] (T : ι → M →ₗ[K] M) (U : Submodule K M) (hU : U ≠ ⊥)
    (hst : ∀ i, ∀ x ∈ U, T i x ∈ U) (hc : ∀ i j, ∀ x ∈ U, T i (T j x) = T j (T i x)) :
    ∃ (χ : ι → K) (y : M), y ∈ U ∧ y ≠ 0 ∧ ∀ i, T i y = χ i • y := by
  obtain ⟨U', ⟨h1, h2, h3⟩, hmin⟩ := (wellFounded_lt (α := Submodule K M)).has_min
    {U' : Submodule K M | U' ≤ U ∧ U' ≠ ⊥ ∧ ∀ i, ∀ x ∈ U', T i x ∈ U'} ⟨U, le_rfl, hU, hst⟩
  have key : ∀ i, ∃ c : K, ∀ x ∈ U', T i x = c • x := by
    intro i
    haveI : Nontrivial U' := Submodule.nontrivial_iff_ne_bot.mpr h2
    obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (K := K) (V := U') ((T i).restrict (h3 i))
    obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
    have hv1 : T i v = c • (v : M) := congrArg Subtype.val hv.apply_eq_smul
    have hv2 : (v : M) ≠ 0 := fun h => hv.2 (Subtype.ext h)
    refine ⟨c, ?_⟩
    let U'' : Submodule K M := U' ⊓ Module.End.eigenspace (T i) c
    have hle : U'' ≤ U' := inf_le_left
    have hmem : U'' ≤ U ∧ U'' ≠ ⊥ ∧ ∀ j, ∀ x ∈ U'', T j x ∈ U'' := by
      refine ⟨hle.trans h1, ?_, ?_⟩
      · rw [Submodule.ne_bot_iff]
        exact ⟨v, ⟨v.2, Module.End.mem_eigenspace_iff.mpr hv1⟩, hv2⟩
      · intro j x hx
        refine ⟨h3 j x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        rw [hc i j x (h1 hx.1), Module.End.mem_eigenspace_iff.mp hx.2, map_smul]
    have heq : U'' = U' := by
      by_contra hne
      exact hmin U'' hmem (lt_of_le_of_ne hle hne)
    intro x hx
    rw [← heq] at hx
    exact Module.End.mem_eigenspace_iff.mp hx.2
  choose χ hχ using key
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp h2
  exact ⟨χ, y, h1 hy, hy0, fun i => hχ i y hy⟩

private theorem selfTwist_abstract {K G M : Type} [Field K] [IsAlgClosed K] [Group G]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] (c : Representation K G M)
    (N : Subgroup G) [hN : N.Normal] (hidx : (N.index : K) ≠ 0)
    (hab : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ N) (p : M) (hp : ∀ n ∈ N, c n p = p)
    (g₀ : G) (hg₀ : c g₀ p ≠ p) :
    ∃ (φ : G →* Kˣ) (y : M), φ ≠ 1 ∧ N ≤ φ.ker ∧ y ≠ 0 ∧ ∀ g, c g y = (φ g : K) • y := by
  have hmul : ∀ a b x, c a (c b x) = c (a * b) x := by
    intro a b x; rw [map_mul]; rfl
  let E : Submodule K M :=
    { carrier := {x | ∀ n ∈ N, c n x = x}
      add_mem' := fun {a b} ha hb n hn => by rw [map_add, ha n hn, hb n hn]
      zero_mem' := fun n hn => map_zero _
      smul_mem' := fun r x hx n hn => by rw [map_smul, hx n hn] }
  have hE : ∀ x, x ∈ E ↔ ∀ n ∈ N, c n x = x := fun x => Iff.rfl
  have hEst : ∀ g, ∀ x ∈ E, c g x ∈ E := by
    intro g x hx n hn
    have h := hx (g⁻¹ * n * g) (by simpa using hN.conj_mem n hn g⁻¹)
    calc c n (c g x) = c g (c (g⁻¹ * n * g) x) := by rw [hmul, hmul]; congr 2; group
      _ = c g x := by rw [h]
  have hEc : ∀ a b, ∀ x ∈ E, c a (c b x) = c b (c a x) := by
    intro a b x hx
    have h := hx _ (hab a⁻¹ b⁻¹)
    calc c a (c b x) = c (b * a) (c (a⁻¹ * b⁻¹ * a⁻¹⁻¹ * b⁻¹⁻¹) x) := by
          rw [hmul, hmul]; congr 2; group
      _ = c b (c a x) := by rw [h, hmul]
  let D : M →ₗ[K] M := c g₀ - LinearMap.id
  have hD : ∀ x, D x = c g₀ x - x := fun x => rfl
  let U : Submodule K M := E.map D
  have hUE : U ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact E.sub_mem (hEst _ _ hx) hx
  obtain ⟨χ, y, hyU, hy0, hy⟩ := selfTwist_commonEig (fun g => c g) U
    ((Submodule.ne_bot_iff _).mpr ⟨D p, ⟨p, hp, rfl⟩, sub_ne_zero.mpr hg₀⟩)
    (by
      rintro g _ ⟨x, hx, rfl⟩
      refine ⟨c g x, hEst g x hx, ?_⟩
      rw [hD, hD, map_sub, hEc _ _ _ hx])
    (fun a b x hx => hEc a b x (hUE hx))
  have hinj : ∀ a b : K, a • y = b • y → a = b := fun a b h => smul_left_injective K hy0 h
  let χ' : G →* K :=
    { toFun := χ
      map_one' := hinj _ _ (by rw [← hy 1]; simp)
      map_mul' := fun a b => hinj _ _ (by
        rw [← hy (a * b), ← hmul, hy b, map_smul, hy a, smul_smul, mul_comm]) }
  refine ⟨χ'.toHomUnits, y, ?_, ?_, hy0, fun g => hy g⟩
  · intro h1
    have h2 : χ g₀ = 1 := by
      have := congrArg (fun f : G →* Kˣ => (f g₀ : K)) h1
      exact this
    have h3 : c g₀ y = y := by rw [hy g₀, h2, one_smul]
    obtain ⟨x, hx, hxy⟩ := hyU
    have h4 : c g₀ x = x + y := by rw [← hxy, hD]; abel
    have h5 : ∀ k : ℕ, c (g₀ ^ k) x = x + (k : K) • y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← hmul, ih, map_add, map_smul, h3, h4, Nat.cast_succ, add_smul, one_smul]
        abel
    have h6 := h5 N.index
    rw [hx _ (N.pow_index_mem g₀)] at h6
    have h7 : (N.index : K) • y = 0 := by simpa using h6
    exact hy0 ((smul_eq_zero.mp h7).resolve_left hidx)
  · intro n hn
    rw [MonoidHom.mem_ker]
    apply Units.ext
    exact hinj _ _ (by
      change χ n • y = (1 : K) • y
      rw [← hy n, one_smul]; exact hUE hyU n hn)

theorem UpperTheory.V.Pr.T.selfTwist :
    ∀ {K G V : Type} [Field K] [IsAlgClosed K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (ρ : Representation K G V) (N : Subgroup G) [N.Normal], N.FiniteIndex → (N.index : K) ≠ 0 →
      (∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ N) →
      (∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) →
      (∃ W : Submodule K V, (∀ g ∈ N, ∀ v ∈ W, ρ g v ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤) →
      ∃ (φ : G →* Kˣ) (e : V ≃ₗ[K] V), φ ≠ 1 ∧ N ≤ φ.ker ∧ ∀ g v, ρ g (e v) = (φ g : K) • e (ρ g v) := by
  intro K G V _ _ _ _ _ _ ρ N _ _ hidx hab hirr ⟨W, hW, hWb, hWt⟩
  obtain ⟨W', hW', hc⟩ := UpperTheory.V.Pr.T.cliffordSS ρ N hirr W hW
  have hinv : ∀ g v, ρ g⁻¹ (ρ g v) = v := by
    intro g v
    change (ρ g⁻¹ * ρ g) v = v
    rw [← map_mul]; simp
  have hinv' : ∀ g v, ρ g (ρ g⁻¹ v) = v := by
    intro g v; simpa using hinv g⁻¹ v
  have hc' : ∀ g (f : V →ₗ[K] V) v, (Representation.linHom ρ ρ) g f v = ρ g (f (ρ g⁻¹ v)) :=
    fun g f v => rfl
  obtain ⟨p, hpW, hpW', hpmem⟩ : ∃ p : V →ₗ[K] V, (∀ w ∈ W, p w = w) ∧ (∀ w ∈ W', p w = 0) ∧
      ∀ v, p v ∈ W := by
    refine ⟨W.subtype ∘ₗ W.linearProjOfIsCompl W' hc, ?_, ?_, ?_⟩
    · intro w hw
      exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨w, hw⟩)
    · intro w hw
      exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩)
    · intro v; exact (W.linearProjOfIsCompl W' hc v).2
  have hp : ∀ n ∈ N, (Representation.linHom ρ ρ) n p = p := by
    intro n hn
    ext v
    have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [hc', map_add, map_add, map_add p, hpW _ (hW _ (N.inv_mem hn) a ha),
      hpW' _ (hW' _ (N.inv_mem hn) b hb), hpW a ha, hpW' b hb, add_zero, add_zero, hinv']
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, (Representation.linHom ρ ρ) g₀ p ≠ p := by
    by_contra hall
    push Not at hall
    refine (hirr W ?_).elim hWb hWt
    intro g w hw
    have h := LinearMap.congr_fun (hall g) (ρ g w)
    rw [hc', hinv, hpW w hw] at h
    rw [h]; exact hpmem _
  obtain ⟨φ, y, h1, h2, hy0, hy⟩ :=
    selfTwist_abstract (Representation.linHom ρ ρ) N hidx hab p hp g₀ hg₀
  have hy' : ∀ g v, ρ g (y v) = (φ g : K) • y (ρ g v) := by
    intro g v
    have h := LinearMap.congr_fun (hy g) (ρ g v)
    rw [hc', hinv] at h
    exact h
  have hker : LinearMap.ker y = ⊥ := by
    refine (hirr (LinearMap.ker y) ?_).resolve_right (fun h => hy0 (LinearMap.ker_eq_top.mp h))
    intro g v hv
    have h := hy' g v
    rw [LinearMap.mem_ker.mp hv, map_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_left (φ g).ne_zero
  have hinj : Function.Injective y := LinearMap.ker_eq_bot.mp hker
  exact ⟨φ, LinearEquiv.ofBijective y ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩,
    h1, h2, hy'⟩
