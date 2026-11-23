import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuationsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundlesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeInvariantLinearEquivStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeAdditiveSubQuotientStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactFirstTermBundleStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNegStatement

open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ch

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {C : ACurve K} {V : Type} [AddCommGroup V] [Module K V]

theorem basis_mem {i : C.I} {n : ℕ} {b : Module.Basis (Fin n) K V} {L : AddSubgroup V}
    (h : IsLatOf C i b L) (q : Fin n) : b q ∈ L := by
  refine (h _).2 fun r => ?_
  by_cases e : q = r <;> simp [e, Finsupp.single_apply]

theorem smul_mem_lat {i : C.I} {n : ℕ} {b : Module.Basis (Fin n) K V} {L : AddSubgroup V}
    (h : IsLatOf C i b L) {a : K} (ha : C.v i a ≤ 1) {x : V} (hx : x ∈ L) : a • x ∈ L := by
  refine (h _).2 fun r => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' ha ((h _).1 hx r)

theorem v_det_le {i : C.I} {n : ℕ} {b b' : Module.Basis (Fin n) K V} {L L' : AddSubgroup V}
    (h : IsLatOf C i b L) (h' : IsLatOf C i b' L') (hle : L ≤ L') : C.v i (b'.det b) ≤ 1 := by
  rw [Module.Basis.det_apply, Matrix.det_apply']
  refine (C.v i).map_sum_le fun σ _ => ?_
  rw [map_mul, map_prod]
  refine mul_le_one' ?_ (Finset.prod_le_one' fun q _ => (h' _).1 (hle (basis_mem h q)) _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]

theorem deg_triv [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    {L : C.I → AddSubgroup V} (h : ∀ i, IsLatOf C i b (L i)) : IsBun C L ∧ deg C L = 0 := by
  have hb : IsBun C L := Inhab.isBun_of_basis C b L h
  refine ⟨hb, ?_⟩
  rw [(GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L n b (fun _ => b) hb h).2]
  simp [Module.Basis.det_self]

end SlopeTestRemainingChoices

theorem deg_mono : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' := by
  intro K _ C V _ _ _ L L' hL hL' hle
  choose b hb using hL.1
  choose b' hb' using hL'.1
  obtain ⟨hf, e⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (Module.finBasis K V) b hL hb
  obtain ⟨hf', e'⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L' _ (Module.finBasis K V) b' hL' hb'
  rw [e, e']
  refine finsum_le_finsum' (hf.subset fun i hi h1 => hi (by simp [h1]))
    (hf'.subset fun i hi h1 => hi (by simp [h1])) fun i => ?_
  refine mul_le_mul_of_nonneg_left ?_ (Int.natCast_nonneg _)
  have n1 : C.v i ((Module.finBasis K V).det (b i)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((Module.finBasis K V).isUnit_det (b i)).ne_zero
  have n2 : C.v i ((Module.finBasis K V).det (b' i)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((Module.finBasis K V).isUnit_det (b' i)).ne_zero
  rw [WithZero.log_le_log n1 n2, ← Module.Basis.det_mul_det _ (b' i) (b i), map_mul]
  exact mul_le_of_le_one_right' (v_det_le (hb i) (hb' i) (hle i))

theorem deg_le_of_equiv {K : Type} [Field K] {C : ACurve K} {V V' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} (e : V ≃ₗ[K] V') (hL : IsBun C L)
    (hL' : IsBun C L') (h : ∀ i, ∀ x ∈ L i, e x ∈ L' i) : deg C L ≤ deg C L' := by
  obtain ⟨hM, hd⟩ := GlobalTheory.T.degree_invariant_linear_equiv K C V V' L
    (fun i => (L i).comap e.symm.toLinearMap.toAddMonoidHom) e hL (fun i x => by simp)
  rw [← hd]
  refine deg_mono K C V' _ _ hM hL' fun i y hy => ?_
  simpa using h i (e.symm y) hy

theorem deg_inj : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) := by
  intro K _ C V _ _ _ V' _ _ _ L L' f W hL hL' hf hh
  exact deg_le_of_equiv (Submodule.equivMapOfInjective f hf W) (GlobalTheory.T.sub_and_quotient_bundles K C V L W hL).1
    (GlobalTheory.T.sub_and_quotient_bundles K C V' L' _ hL').1 fun i x hx => hh i x hx

theorem subdeg_trivial : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 := by
  intro K _ C V _ _ _ n b L W h
  obtain ⟨hL, h0⟩ := deg_triv b h
  have hs := GlobalTheory.T.degree_additive_sub_quotient K C V L W hL
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K (fun q => W.mkQ (b q))
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have htop : ⊤ ≤ Submodule.span K (Set.range ((fun q => W.mkQ (b q)) ∘ a)) := by
    rw [hsp, show (Set.range fun q => W.mkQ (b q)) = W.mkQ '' Set.range b from
      Set.range_comp _ _, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_mkQ]
  let c := (Module.Basis.mk hli htop).reindex (Fintype.equivFin κ)
  have hc : ∀ q, c q = W.mkQ (b (a ((Fintype.equivFin κ).symm q))) := fun q => by simp [c]
  obtain ⟨hM, hM0⟩ := deg_triv (C := C) c (fun i => Inhab.isLatOf_latOf C i c)
  have := deg_mono K C _ _ _ hM (GlobalTheory.T.sub_and_quotient_bundles K C V L W hL).2 fun i y hy => by
    rw [← c.sum_repr y]
    refine sum_mem fun q _ => ⟨c.repr y q • b (a ((Fintype.equivFin κ).symm q)),
      smul_mem_lat (h i) (hy q) (basis_mem (h i) _), ?_⟩
    rw [hc]; simp
  omega

theorem ses_restrict {K : Type} [Field K] {C : ACurve K} {V V' V'' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    [AddCommGroup V''] [Module K V''] [FiniteDimensional K V'']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} {L'' : C.I → AddSubgroup V''}
    {f : V →ₗ[K] V'} {g : V' →ₗ[K] V''} (hL' : IsBun C L') (h : ShortExact C L L' L'' f g)
    (A : Submodule K V) (X : Submodule K V') (B : Submodule K V'')
    (hA : ∀ x, x ∈ A ↔ f x ∈ X) (hB : ∀ z, z ∈ B ↔ ∃ y ∈ X, g y = z) :
    ∃ I : C.I → AddSubgroup B, IsBun C I ∧ subDeg C L' X = subDeg C L A + deg C I ∧
      ∀ i z, z ∈ I i ↔ ∃ y ∈ L' i, y ∈ X ∧ g y = z := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  let f' : A →ₗ[K] X := f.restrict fun x hx => (hA x).1 hx
  let g' : X →ₗ[K] B := g.restrict fun y hy => (hB _).2 ⟨y, hy, rfl⟩
  have hse : ShortExact C (sub C L A) (sub C L' X)
      (fun i => (sub C L' X i).map g'.toAddMonoidHom) f' g' := by
    refine ⟨fun x y e => Subtype.ext (h1 (congrArg Subtype.val e)), fun y => ⟨fun hy => ?_, ?_⟩,
      fun z => ?_, fun i x => h4 i x, fun i z => Iff.rfl⟩
    · obtain ⟨x, hx⟩ := (h2 y).1 (congrArg Subtype.val hy)
      exact ⟨⟨x, (hA x).2 (hx ▸ y.2)⟩, Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext (h2.apply_apply_eq_zero x)
    · obtain ⟨y, hy, e⟩ := (hB z).1 z.2
      exact ⟨⟨y, hy⟩, Subtype.ext e⟩
  obtain ⟨-, hI, hd⟩ := GlobalTheory.T.short_exact_first_term_bundle K C _ _ _ _ _ _ f' g' (GlobalTheory.T.sub_and_quotient_bundles K C V' L' X hL').1 hse
  refine ⟨_, hI, hd, fun i z => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, y.2, rfl⟩
  · rintro ⟨y, hy, hX, e⟩
    exact ⟨⟨y, hX⟩, hy, Subtype.ext e⟩

theorem subdeg_ses : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g X hL' h
  obtain ⟨I, hI, hd, hm⟩ := ses_restrict hL' h (X.comap f) X (X.map g) (fun _ => Iff.rfl)
    (fun _ => Iff.rfl)
  have hL'' := (GlobalTheory.T.short_exact_first_term_bundle K C _ _ _ _ _ _ f g hL' h).2.1
  have : deg C I ≤ subDeg C L'' (X.map g) :=
    deg_mono K C _ _ _ hI (GlobalTheory.T.sub_and_quotient_bundles K C V'' L'' _ hL'').1 fun i z hz => by
      obtain ⟨y, hy, -, e⟩ := (hm i z).1 hz
      exact (h.2.2.2.2 i z).2 ⟨y, hy, e⟩
  omega

theorem exists_dot {K : Type} [Field K] {d : ℕ} (ψ : Module.Dual K (Fin d → K)) :
    ∃ u : Fin d → K, ∀ x, u ⬝ᵥ x = ψ x := by
  refine ⟨fun j => ψ (Pi.single j 1), fun x => ?_⟩
  conv_rhs => rw [pi_eq_sum_univ' x, map_sum]
  simp [dotProduct, mul_comm]

theorem subdeg_orth : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W := by
  intro K _ C d L W X hL hW
  have hbij : Function.Bijective (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun u hu => funext fun j => ?_, fun ψ => ?_⟩
    · simpa using LinearMap.congr_fun hu (Pi.single j 1)
    · obtain ⟨u, hu⟩ := exists_dot ψ
      exact ⟨u, LinearMap.ext hu⟩
  obtain ⟨hD, -, hbi⟩ := GlobalTheory.T.dual_lattice_degree_neg K C _ _ L _ hL hbij
  let B₀ : (Fin d → K) →ₗ[K] W →ₗ[K] K := ((dotProductBilin K K).comp W.subtype).flip
  have hB₀ : ∀ φ (w : W), B₀ φ w = (w : Fin d → K) ⬝ᵥ φ := fun _ _ => rfl
  let B : ((Fin d → K) ⧸ X) →ₗ[K] W →ₗ[K] K :=
    X.liftQ B₀ fun φ hφ => LinearMap.ext fun w => (hW w).1 w.2 φ hφ
  have hB : ∀ φ (w : W), B (X.mkQ φ) w = (w : Fin d → K) ⬝ᵥ φ := fun _ _ => rfl
  have hBb : Function.Bijective B := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun ψ => ?_⟩
    · obtain ⟨φ, rfl⟩ := X.mkQ_surjective y
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        ← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
      intro ψ hψ
      obtain ⟨u, hu⟩ := exists_dot ψ
      have hu' : u ∈ W := (hW u).2 fun x hx => by
        rw [hu]; exact (Submodule.mem_dualAnnihilator ψ).1 hψ x hx
      rw [← hu, ← hB φ ⟨u, hu'⟩, hy]; rfl
    · obtain ⟨ψ', rfl⟩ := LinearMap.dualMap_surjective_of_injective W.injective_subtype ψ
      obtain ⟨u, hu⟩ := exists_dot ψ'
      refine ⟨X.mkQ u, LinearMap.ext fun w => ?_⟩
      rw [hB, dotProduct_comm, hu]; rfl
  obtain ⟨-, hq, -⟩ := GlobalTheory.T.dual_lattice_degree_neg K C _ _ _ B (GlobalTheory.T.sub_and_quotient_bundles K C _ _ X hD).2 hBb
  have he : dualLat C (quot C (dualLat C L (dotProductBilin K K)) X) B = sub C L W := by
    funext i; ext w
    have : (w : Fin d → K) ∈ L i ↔ (w : Fin d → K) ∈
        dualLat C (dualLat C L (dotProductBilin K K)) (dotProductBilin K K).flip i := by rw [hbi]
    refine Iff.trans ?_ this.symm
    constructor
    · intro H φ hφ
      exact H _ ⟨φ, hφ, rfl⟩
    · rintro H _ ⟨φ, hφ, rfl⟩
      exact H φ hφ
  have hs := GlobalTheory.T.degree_additive_sub_quotient K C _ _ X hD
  rw [he] at hq
  unfold dotDual
  unfold subDeg at hs ⊢
  omega

end PositivityTheory.HtPt.Ch
