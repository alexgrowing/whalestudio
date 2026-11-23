import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageRegSet

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.GaussComp

theorem exists_indep {T M I : Type} [CommRing T] [IsDomain T] [IsPrincipalIdealRing T] [AddCommGroup M] [Module T M]
    [Module.IsTorsionFree T M] [Finite I] (z : I → M) :
    ∃ (p : ℕ) (x : Fin p → M) (A : I → Fin p → T), LinearIndependent T x ∧ ∀ i, z i = ∑ l, A i l • x l := by
  classical
  let N := Submodule.span T (Set.range z)
  have : Module.Finite T N := Module.Finite.span_of_finite T (Set.finite_range z)
  have : Module.Free T N := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis T N
  have hz : ∀ i, z i ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Module.finrank T N, fun l => (b l : M), fun i l => b.repr ⟨z i, hz i⟩ l, ?_, fun i => ?_⟩
  · exact b.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  · have h := congrArg Subtype.val (b.sum_repr ⟨z i, hz i⟩)
    rw [Submodule.coe_sum] at h
    simpa using h.symm

theorem mem_spanBy_iff {R F : Type} [CommRing R] [CommRing F] [Algebra R F] (S : Set F) (v : F) :
    v ∈ spanBy (algebraMap R F) S ↔ v ∈ Submodule.span R S := by
  simp only [spanBy]
  rw [Submodule.mem_span_set']
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact ⟨n, r, fun i => ⟨t i, ht i⟩, by simp [Algebra.smul_def]⟩
  · rintro ⟨n, f, g, hg⟩
    exact ⟨n, f, fun i => g i, fun i => (g i).2, by rw [← hg]; simp [Algebra.smul_def]⟩

section

variable {T E F' FE : Type} [CommRing T] [IsDomain T] [IsPrincipalIdealRing T] [CommRing E] [CommRing F']
  [CommRing FE] [Algebra T E] [Algebra T F'] [Algebra E FE] (θb : F' →+* FE)

omit [IsDomain T] [IsPrincipalIdealRing T] in
theorem map_smul' (hc : θb.comp (algebraMap T F') = (algebraMap E FE).comp (algebraMap T E)) (t : T) (e : E)
    (x : F') : e • θb (t • x) = (t • e) • θb x := by
  have h : θb (algebraMap T F' t) = algebraMap E FE (algebraMap T E t) := congrArg (fun g => g t) hc
  simp only [Algebra.smul_def, map_mul, h]
  ring

theorem symm_indep [Module.IsTorsionFree T F']
    (hc : θb.comp (algebraMap T F') = (algebraMap E FE).comp (algebraMap T E))
    (hL : LinDisj (algebraMap T F') (algebraMap E FE) θb) {I : Type} [Fintype I] {ε : I → E}
    (hε : LinearIndependent T ε) (y : I → F') (h : ∑ a, ε a • θb (y a) = 0) (a : I) : y a = 0 := by
  classical
  obtain ⟨p, x, A, hx, hy⟩ := exists_indep (T := T) y
  have h2 : ∑ l, algebraMap E FE (∑ b, A b l • ε b) * θb (x l) = 0 := by
    rw [← h]
    simp only [hy, map_sum, Finset.smul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
      rw [← Algebra.smul_def]; exact (map_smul' θb hc _ _ _).symm
  have h3 : (fun l => ∑ b, A b l • ε b) = 0 := by
    refine hL p x (fun r hr => ?_) _ h2
    exact funext (Fintype.linearIndependent_iff.mp hx r (by simpa [Algebra.smul_def] using hr))
  have h4 : ∀ b l, A b l = 0 := fun b l =>
    Fintype.linearIndependent_iff.mp hε (fun b => A b l) (congrFun h3 l) b
  rw [hy a]
  simp [h4]

private theorem sum_smul_theta_eq_sum_basis_smul_theta (hc : θb.comp (algebraMap T F') = (algebraMap E FE).comp (algebraMap T E))
    {K : Type} [Fintype K] {p : ℕ} (c : K → E) (z : K → F') (A : K → Fin p → T) (e : Fin p → E)
    (hcA : ∀ k, c k = ∑ l, A k l • e l) :
    ∑ k, c k • θb (z k) = ∑ l, e l • θb (∑ k, A k l • z k) := by
  simp only [hcA, Finset.sum_smul, map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    (map_smul' θb hc _ _ _).symm

private theorem exists_dual_coeffs_of_linearIndependent {R₀ : Type} [CommRing R₀] [IsDomain R₀] {Jx : Type} [Fintype Jx] [DecidableEq Jx]
    {p : ℕ} (B : Jx → Fin p → R₀) (hB : LinearIndependent R₀ B) (j : Jx) :
    ∃ (D : Fin p → R₀) (t : R₀), t ≠ 0 ∧ ∀ a, ∑ l, D l * B a l = if a = j then t else 0 := by
  let ψ : (Fin p → R₀) →ₗ[R₀] (Fin p → FractionRing R₀) :=
    LinearMap.pi fun l => (Algebra.linearMap R₀ (FractionRing R₀)).comp (LinearMap.proj l)
  have hψ : ∀ x l, ψ x l = algebraMap R₀ (FractionRing R₀) (x l) := fun _ _ => rfl
  have hker : LinearMap.ker ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    funext l
    have h0 := congrFun hx l
    rw [hψ] at h0
    apply IsFractionRing.injective R₀ (FractionRing R₀)
    rw [h0]
    simp
  have h2 : LinearIndependent (FractionRing R₀) (ψ ∘ B) :=
    (LinearIndependent.iff_fractionRing R₀ (FractionRing R₀)).mp (hB.map' ψ hker)
  have h3 : (ψ ∘ B) j ∉ Submodule.span (FractionRing R₀) ((ψ ∘ B) '' {a | a ≠ j}) :=
    h2.notMem_span_image (by simp)
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h3 inferInstance
  have hfa : ∀ a, a ≠ j → f ((ψ ∘ B) a) = 0 := by
    intro a ha
    have hm : f ((ψ ∘ B) a) ∈ (Submodule.span (FractionRing R₀) ((ψ ∘ B) '' {a | a ≠ j})).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨a, ha, rfl⟩)
    rw [hf0] at hm
    exact (Submodule.mem_bot (FractionRing R₀)).mp hm
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R₀) Finset.univ
    (fun l => f (fun m => if l = m then 1 else 0))
  have hb' : ∀ l, ∃ d : R₀, algebraMap R₀ (FractionRing R₀) d =
      (b : R₀) • f (fun m => if l = m then 1 else 0) :=
    fun l => RingHom.mem_rangeS.mp (hb l (Finset.mem_univ l))
  choose D hD using hb'
  have key : ∀ a, algebraMap R₀ (FractionRing R₀) (∑ l, D l * B a l) = (b : R₀) • f ((ψ ∘ B) a) := by
    intro a
    rw [LinearMap.pi_apply_eq_sum_univ f ((ψ ∘ B) a), map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, hD l, Function.comp_apply, hψ, smul_eq_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  refine ⟨D, ∑ l, D l * B j l, fun h0 => hf ?_, fun a => ?_⟩
  · have hj := key j
    rw [h0, map_zero, Algebra.smul_def] at hj
    exact (mul_eq_zero.mp hj.symm).resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
  · split_ifs with h
    · rw [h]
    · apply IsFractionRing.injective R₀ (FractionRing R₀)
      rw [key a, hfa a h, smul_zero, map_zero]

theorem exists_mul_mem [Module.IsTorsionFree T F'] [Module.IsTorsionFree T E]
    (hc : θb.comp (algebraMap T F') = (algebraMap E FE).comp (algebraMap T E))
    (hL : LinDisj (algebraMap T F') (algebraMap E FE) θb) (N : Submodule T F') {I J : Type} [Fintype I] [Fintype J]
    {ε : I → E} (hε : LinearIndependent T ε) (w : I → F') (r : J → E) (y : J → F') (hy : ∀ k, y k ∈ N)
    (h : ∑ j, ε j • θb (w j) = ∑ k, r k • θb (y k)) (j : I) : ∃ t : T, t ≠ 0 ∧ t • w j ∈ N := by
  classical
  obtain ⟨p, e, A, he, hz⟩ := exists_indep (T := T) (Sum.elim ε r)
  have h1 : ∑ i, ε i • θb (w i) = ∑ l, e l • θb (∑ i, A (Sum.inl i) l • w i) :=
    sum_smul_theta_eq_sum_basis_smul_theta θb hc ε w (fun i => A (Sum.inl i)) e (fun i => hz (Sum.inl i))
  have h2 : ∑ k, r k • θb (y k) = ∑ l, e l • θb (∑ k, A (Sum.inr k) l • y k) :=
    sum_smul_theta_eq_sum_basis_smul_theta θb hc r y (fun k => A (Sum.inr k)) e (fun k => hz (Sum.inr k))
  have key : ∀ l, ∑ i, A (Sum.inl i) l • w i - ∑ k, A (Sum.inr k) l • y k = 0 := by
    intro l
    refine symm_indep θb hc hL he
      (fun l => ∑ i, A (Sum.inl i) l • w i - ∑ k, A (Sum.inr k) l • y k) ?_ l
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib]
    rw [← h1, ← h2, h, sub_self]
  have hmem : ∀ l, ∑ i, A (Sum.inl i) l • w i ∈ N := fun l => by
    rw [sub_eq_zero.mp (key l)]
    exact N.sum_mem fun k _ => N.smul_mem _ (hy k)
  have hB : LinearIndependent T (fun i l => A (Sum.inl i) l) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    apply Fintype.linearIndependent_iff.mp hε g
    have hz' : ∀ i, ε i = ∑ l, A (Sum.inl i) l • e l := fun i => hz (Sum.inl i)
    have hg' : ∀ l, ∑ i, g i * A (Sum.inl i) l = 0 := fun l => by
      simpa using congrFun hg l
    calc ∑ i, g i • ε i = ∑ l, (∑ i, g i * A (Sum.inl i) l) • e l := by
          simp only [hz', Finset.smul_sum, smul_smul, Finset.sum_smul]
          exact Finset.sum_comm
      _ = 0 := by simp [hg']
  obtain ⟨D, t, ht, hD⟩ := exists_dual_coeffs_of_linearIndependent (fun i l => A (Sum.inl i) l) hB j
  have hD' : ∀ a, ∑ l, D l * A (Sum.inl a) l = if a = j then t else 0 := hD
  refine ⟨t, ht, ?_⟩
  have ht' : t • w j = ∑ l, D l • ∑ i, A (Sum.inl i) l • w i := by
    calc t • w j = ∑ i, (if i = j then t else 0) • w i := by simp [ite_smul]
      _ = ∑ i, (∑ l, D l * A (Sum.inl i) l) • w i :=
          Finset.sum_congr rfl fun i _ => by rw [hD' i]
      _ = ∑ l, D l • ∑ i, A (Sum.inl i) l • w i := by
          simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
          exact Finset.sum_comm
  rw [ht']
  exact N.sum_mem fun l _ => N.smul_mem _ (hmem l)

private theorem sum_smul_thetab_expand_in_basis {T E F' FE : Type} [CommRing T] [CommRing E] [CommRing F'] [CommRing FE]
    [Algebra T E] [Algebra T F'] [Algebra E FE] (θb : F' →+* FE)
    (hc : θb.comp (algebraMap T F') = (algebraMap E FE).comp (algebraMap T E))
    {K : Type} [Fintype K] {p : ℕ} (c : K → E) (z : K → F') (A : K → Fin p → T) (e : Fin p → E)
    (hcA : ∀ k, c k = ∑ l, A k l • e l) :
    ∑ k, c k • θb (z k) = ∑ l, e l • θb (∑ k, A k l • z k) := by
  simp only [hcA, Finset.sum_smul, map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    (map_smul' θb hc _ _ _).symm

end

theorem gaussAt_comp_alg {T E F F' FE : Type} [CommRing T] [IsDomain T] [IsPrincipalIdealRing T] [CommRing E]
    [IsDomain E] [CommRing F] [CommRing F'] [CommRing FE] [Algebra T E] [Algebra T F'] [Algebra E FE]
    [Module.IsTorsionFree T F'] [Module.IsTorsionFree T E] (θ : F →+* F') (θb : F' →+* FE)
    (q : Ideal T) [q.IsPrime] (Q : Ideal E) [Q.IsPrime] (W : Set F) (W' : Submodule T F') (WE : Set FE)
    (hq : ∀ s, s ∉ q → algebraMap T E s ∉ Q)
    (hc : θb.comp (algebraMap T F') = (algebraMap E FE).comp (algebraMap T E))
    (hL : LinDisj (algebraMap T F') (algebraMap E FE) θb)
    (G₁ : GaussAt (algebraMap T F') q θ W W') (G₂ : GaussAt (algebraMap E FE) Q θb W' WE) :
    GaussAt (algebraMap E FE) Q (θb.comp θ) W WE := by
  classical
  have hcT : ∀ t : T, θb (algebraMap T F' t) = algebraMap E FE (algebraMap T E t) :=
    fun t => congrArg (fun g => g t) hc
  have h1q : (1 : T) ∉ q := fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one q).mpr h)
  have hW : ∀ u ∈ W, θ u ∈ W' := by
    intro u hu
    refine (G₁ (θ u) ⟨1, one_ne_zero, ?_⟩).mpr ⟨1, h1q, ?_⟩
    · rw [map_one, _root_.one_mul]; exact subset_spanBy _ _ (Set.mem_range_self u)
    · rw [map_one, _root_.one_mul]; exact subset_spanBy _ _ (Set.mem_image_of_mem θ hu)
  have himg : ∀ x ∈ Submodule.span T (θ '' W), θb x ∈ Submodule.span E ((θb.comp θ) '' W) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, hcT, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx
  intro v hv
  obtain ⟨d, hd, hdv⟩ := hv
  have hdv' : algebraMap E FE d * v ∈ spanBy (algebraMap E FE) (Set.range θb) := by
    rw [mem_spanBy_iff]
    exact Submodule.span_mono (Set.range_comp_subset_range θ θb) ((mem_spanBy_iff _ _).mp hdv)
  rw [G₂ v ⟨d, hd, hdv'⟩]
  constructor
  · rintro ⟨s, hs, hsv⟩
    rw [mem_spanBy_iff, Submodule.mem_span_set'] at hsv
    obtain ⟨n, f, g, hfg⟩ := hsv
    have hg : ∀ i, ∃ x, x ∈ W' ∧ θb x = (g i : FE) := fun i => (g i).2
    choose w hw hwg using hg
    obtain ⟨m, ε, A, hε, hA⟩ := exists_indep (T := T) f
    set w' : Fin m → F' := fun l => ∑ i, A i l • w i with hw'
    have hw'W : ∀ l, w' l ∈ W' := fun l => W'.sum_mem fun i _ => W'.smul_mem _ (hw i)
    have e1 : algebraMap E FE s * v = ∑ l, ε l • θb (w' l) := by
      rw [← hfg]
      simp_rw [← hwg]
      exact sum_smul_thetab_expand_in_basis θb hc f w A ε hA
    rw [mem_spanBy_iff, Submodule.mem_span_set'] at hdv
    obtain ⟨n', r, g', hrg⟩ := hdv
    have hg'' : ∀ k, ∃ x, (θb.comp θ) x = (g' k : FE) := fun k => (g' k).2
    choose fk hfk using hg''
    have hdε : LinearIndependent T (fun l => d * ε l) := by
      rw [Fintype.linearIndependent_iff] at hε ⊢
      intro c hc0
      apply hε c
      have h0 : d * ∑ l, c l • ε l = 0 := by
        calc d * ∑ l, c l • ε l = ∑ l, c l • (d * ε l) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => mul_smul_comm _ _ _
          _ = 0 := hc0
      exact (mul_eq_zero.mp h0).resolve_left hd
    have heq : ∑ l, (d * ε l) • θb (w' l) = ∑ k, (s * r k) • θb (θ (fk k)) := by
      have hl : ∑ l, (d * ε l) • θb (w' l) = algebraMap E FE d * (algebraMap E FE s * v) := by
        rw [e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, _root_.mul_assoc]
      have hr : ∑ k, (s * r k) • θb (θ (fk k)) = algebraMap E FE s * (algebraMap E FE d * v) := by
        rw [← hrg, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hfk k, RingHom.comp_apply, Algebra.smul_def, Algebra.smul_def, map_mul, _root_.mul_assoc]
      rw [hl, hr, _root_.mul_left_comm]
    have hG : ∀ l, ∃ σ : T, σ ∉ q ∧ σ • w' l ∈ Submodule.span T (θ '' W) := by
      intro l
      obtain ⟨t, ht, htm⟩ := exists_mul_mem θb hc hL (Submodule.span T (Set.range θ)) hdε w'
        (fun k => s * r k) (fun k => θ (fk k)) (fun k => Submodule.subset_span ⟨fk k, rfl⟩) heq l
      have hpre : ∃ d' : T, d' ≠ 0 ∧
          algebraMap T F' d' * w' l ∈ spanBy (algebraMap T F') (Set.range θ) :=
        ⟨t, ht, by rw [mem_spanBy_iff, ← Algebra.smul_def]; exact htm⟩
      obtain ⟨σ, hσ, hσm⟩ := (G₁ (w' l) hpre).mp (hw'W l)
      rw [mem_spanBy_iff, ← Algebra.smul_def] at hσm
      exact ⟨σ, hσ, hσm⟩
    choose σ hσq hσm using hG
    have hτ : (∏ l, σ l) ∉ q := by
      have hτ' : (∏ l, σ l) ∈ q.primeCompl := Submonoid.prod_mem _ fun l _ => hσq l
      exact hτ'
    have hτm : ∀ l, (∏ k, σ k) • w' l ∈ Submodule.span T (θ '' W) := by
      intro l
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ l), mul_smul]
      exact Submodule.smul_mem _ _ (hσm l)
    refine ⟨algebraMap T E (∏ l, σ l) * s, ?_, ?_⟩
    · intro hmem
      rcases (inferInstance : Q.IsPrime).mem_or_mem hmem with h | h
      · exact hq _ hτ h
      · exact hs h
    · rw [mem_spanBy_iff]
      have e2 : algebraMap E FE (algebraMap T E (∏ l, σ l) * s) * v =
          ∑ l, ε l • θb ((∏ k, σ k) • w' l) := by
        rw [map_mul, _root_.mul_assoc, e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Algebra.smul_def (∏ k, σ k) (w' l), map_mul, hcT, Algebra.smul_def, Algebra.smul_def]
        ring
      rw [e2]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (himg _ (hτm l))
  · rintro ⟨s, hs, hsv⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_spanBy_iff] at hsv ⊢
    refine Submodule.span_mono ?_ hsv
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨θ u, hW u hu, rfl⟩

theorem gaussAt_comp : ∀ (T E F F' FE : Type) [CommRing T] [IsDomain T] [IsPrincipalIdealRing T] [CommRing E] [IsDomain E] [Field F] [Field F'] [Field FE] (b : T →+* E) (c' : T →+* F') (cE : E →+* FE) (θ : F →+* F') (θb : F' →+* FE) (q : Ideal T) [q.IsPrime] (Q : Ideal E) [Q.IsPrime] (W : Set F) (W' : Set F') (WE : Set FE), Function.Injective b → Function.Injective c' → (∀ s, s ∉ q → b s ∉ Q) → θb.comp c' = cE.comp b → LinDisj c' cE θb → (0 : F') ∈ W' → (∀ u ∈ W', ∀ v ∈ W', u + v ∈ W') → (∀ (t : T), ∀ u ∈ W', c' t * u ∈ W') → GaussAt c' q θ W W' → GaussAt cE Q θb W' WE → GaussAt cE Q (θb.comp θ) W WE := by
  intro T E F F' FE _ _ _ _ _ _ _ _ b c' cE θ θb q _ Q _ W W' WE hb hc' hq hcomm hL h0 hadd hsmul G₁ G₂
  letI : Algebra T E := b.toAlgebra
  letI : Algebra T F' := c'.toAlgebra
  letI : Algebra E FE := cE.toAlgebra
  have : Module.IsTorsionFree T F' := Module.isTorsionFree_iff_smul_eq_zero.mpr fun t x h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl ((map_eq_zero_iff c' hc').mp h)
    · exact Or.inr h
  have : Module.IsTorsionFree T E := Module.isTorsionFree_iff_smul_eq_zero.mpr fun t x h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl ((map_eq_zero_iff b hb).mp h)
    · exact Or.inr h
  let W'' : Submodule T F' :=
    { carrier := W'
      add_mem' := fun hx hy => hadd _ hx _ hy
      zero_mem' := h0
      smul_mem' := fun t x hx => hsmul t x hx }
  exact gaussAt_comp_alg θ θb q Q W W'' WE hq hcomm hL G₁ G₂

end GlobalTheory.Desc.GaussComp
