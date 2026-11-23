import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

section Top

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {a : ℕ}

theorem isCompact_boundedGL (R : ℝ) :
    IsCompact {g : GLw a w | ∀ i j, ‖g.val i j‖ ≤ R ∧ ‖(g⁻¹).val i j‖ ≤ R} := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  have hK : IsCompact {A : Matrix (Fin a) (Fin a) (w.adicCompletion E) | ∀ i j, ‖A i j‖ ≤ R} := by
    have h : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a =>
        Metric.closedBall (0 : w.adicCompletion E) R) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have e : {A : Matrix (Fin a) (Fin a) (w.adicCompletion E) | ∀ i j, ‖A i j‖ ≤ R} =
        (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a =>
          Metric.closedBall (0 : w.adicCompletion E) R) :=
      Set.ext fun A => ⟨fun hA i _ j _ => by simpa using hA i j, fun hA i j => by simpa using hA i trivial j trivial⟩
    rw [e]
    exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin a) (Fin a) (w.adicCompletion E))).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    (MulOpposite.op_injective).mem_set_image]
  exact ⟨fun hg => ⟨fun i j => (hg i j).1, fun i j => (hg i j).2⟩, fun hg i j => ⟨hg.1 i j, hg.2 i j⟩⟩

theorem isCompact_closure_zpowers_iff (g : GLw a w) :
    IsCompact (closure (Subgroup.zpowers g : Set (GLw a w))) ↔
      ∃ R : ℝ, ∀ n : ℤ, ∀ i j, ‖(g ^ n).val i j‖ ≤ R := by
  constructor
  · intro hc
    have hb : ∀ i j : Fin a, ∃ C : ℝ, ∀ h ∈ closure (Subgroup.zpowers g : Set (GLw a w)), ‖h.val i j‖ ≤ C :=
      fun i j => hc.exists_bound_of_continuousOn (f := fun h : GLw a w => h.val i j)
        ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (w.adicCompletion E))).matrix_elem i j).continuousOn
    choose C hC using hb
    refine ⟨∑ i, ∑ j, max (C i j) 0, fun n i j => ?_⟩
    have h1 := hC i j (g ^ n) (subset_closure (Subgroup.zpow_mem_zpowers g n))
    calc _ ≤ max (C i j) 0 := h1.trans (le_max_left _ _)
      _ ≤ ∑ j', max (C i j') 0 :=
        Finset.single_le_sum (f := fun j' => max (C i j') 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', max (C i' j') 0)
        (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ i)
  · rintro ⟨R, hR⟩
    refine (isCompact_boundedGL R).closure_of_subset ?_
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    refine fun i j => ⟨hR n i j, ?_⟩
    rw [← _root_.zpow_neg]
    exact hR (-n) i j

end Top

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

omit [IsCMField E] in
theorem norm_le_one_iff_mem (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (x : K.E) :
    ‖e x‖ ≤ 1 ↔ x ∈ (algebraMap K.O K.E).range := by
  rw [he]
  exact Valued.toNormedField.norm_le_one_iff

omit [IsCMField E] in

theorem exists_norm_ge (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (R : ℝ) :
    ∃ c : K.E, c ≠ 0 ∧ R ≤ ‖e c‖ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hπ0 : algebraMap K.O K.E π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]
    exact hπ.ne_zero
  have hn : ¬ (algebraMap K.O K.E π)⁻¹ ∈ (algebraMap K.O K.E).range := by
    rintro ⟨o, ho⟩
    apply hπ.not_isUnit
    have h : π * o = 1 := IsFractionRing.injective K.O K.E (by rw [map_mul, ho, mul_inv_cancel₀ hπ0, map_one])
    exact isUnit_iff_exists_inv.2 ⟨o, h⟩
  have h1 : 1 < ‖e (algebraMap K.O K.E π)⁻¹‖ := by
    rw [← not_le, norm_le_one_iff_mem e he]
    exact hn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R h1
  refine ⟨((algebraMap K.O K.E π)⁻¹) ^ n, pow_ne_zero _ (inv_ne_zero hπ0), ?_⟩
  rw [map_pow, norm_pow]
  exact hn.le

omit [IsCMField E] in

theorem exists_fg_of_crd_le (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (R : ℝ) :
    ∃ M : Submodule K.O B.A, M.FG ∧ ∀ y, (∀ i, ‖crd e b y i‖ ≤ R) → y ∈ M := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_ge e he R
  refine ⟨Submodule.span K.O (Set.range fun j => c • b j), Submodule.fg_span (Set.finite_range _), fun y hy => ?_⟩
  have hec : e c ≠ 0 := by rwa [Ne, map_eq_zero_iff _ e.injective]
  rw [← b.sum_repr y]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hm : b.repr y j / c ∈ (algebraMap K.O K.E).range := by
    rw [← norm_le_one_iff_mem e he, map_div₀, norm_div, div_le_one (norm_pos_iff.2 hec)]
    exact (hy j).trans hc
  obtain ⟨o, ho⟩ := hm
  have : b.repr y j • b j = o • (c • b j) := by
    rw [← algebraMap_smul K.E o, smul_smul, ho, div_mul_cancel₀ _ hc0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isIntegral_of_bounded (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (u : B.A)
    (R : ℝ) (hR : ∀ n : ℕ, ∀ i j, ‖mulHom e b (u ^ n) i j‖ ≤ R) : IsIntegral K.O u := by
  obtain ⟨M, hMfg, hM⟩ := exists_fg_of_crd_le e b he (∑ j, R * ‖crd e b 1 j‖)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin K.O {u}) ≤ M := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le, ← Submonoid.powers_eq_closure]
    rintro _ ⟨n, rfl⟩
    refine hM _ fun i => ?_
    have h1 : crd e b (u ^ n) = mulHom e b (u ^ n) *ᵥ crd e b 1 := by rw [← crd_mul, mul_one]
    rw [h1]
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hR n i j) (norm_nonneg _)
  haveI : IsNoetherian K.O M := isNoetherian_of_fg_of_noetherian M hMfg
  haveI : IsNoetherian K.O (Subalgebra.toSubmodule (Algebra.adjoin K.O {u})) := isNoetherian_of_le hle
  exact isIntegral_of_submodule_noetherian _ this u (Algebra.self_mem_adjoin_singleton K.O u)

theorem bounded_of_fg (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (M : Submodule K.O B.A)
    (hM : M.FG) : ∃ R : ℝ, ∀ y ∈ M, ∀ i j, ‖mulHom e b y i j‖ ≤ R := by
  obtain ⟨S, rfl⟩ := hM
  refine ⟨∑ y ∈ S, ∑ i, ∑ j, ‖mulHom e b y i j‖, fun x hx i j => ?_⟩
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.1 hx
  have hsum : mulHom e b (∑ y ∈ S, f y • y) i j = ∑ y ∈ S, e (algebraMap K.O K.E (f y)) * mulHom e b y i j := by
    rw [mulHom_apply]
    simp only [mulHom_apply, Finset.sum_mul, smul_mul_assoc]
    simp only [← algebraMap_smul K.E (f _), map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, map_mul]
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_mul]
  have h1 : ‖e (algebraMap K.O K.E (f y))‖ ≤ 1 := (norm_le_one_iff_mem e he _).2 ⟨f y, rfl⟩
  calc _ ≤ 1 * ‖mulHom e b y i j‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖mulHom e b y i j‖ := one_mul _
    _ ≤ ∑ j', ‖mulHom e b y i j'‖ :=
      Finset.single_le_sum (f := fun j' => ‖mulHom e b y i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖mulHom e b y i' j'‖ :=
      Finset.single_le_sum (f := fun i' => ∑ j', ‖mulHom e b y i' j'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

end Alg

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

theorem mulGL_zpow_val (t : B.Aˣ) (n : ℤ) : ((mulGL e b t) ^ n).val = mulHom e b ((t ^ n : B.Aˣ) : B.A) := by
  rw [← map_zpow]
  rfl

theorem isCompact_closure_zpowers_mulGL_iff' (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1)
    (t : B.Aˣ) : IsCompact (closure (Subgroup.zpowers (mulGL e b t) : Set (GLw a w))) ↔
      t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  rw [isCompact_closure_zpowers_iff]
  simp only [mulGL_zpow_val]
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨isIntegral_of_bounded e b he _ R fun n i j => ?_, isIntegral_of_bounded e b he _ R fun n i j => ?_⟩
    · have := hR n i j
      rwa [zpow_natCast, Units.val_pow_eq_pow_val] at this
    · have := hR (-(n : ℤ)) i j
      rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val] at this
  · rintro ⟨h1, h2⟩
    obtain ⟨R, hR⟩ := bounded_of_fg e b he _
      (fg_adjoin_of_finite (s := {(t : B.A), ((t⁻¹ : B.Aˣ) : B.A)}) (Set.toFinite _)
        (by rintro x (rfl | rfl); exacts [h1, h2]))
    refine ⟨R, fun n i j => hR _ ((Subalgebra.mem_toSubmodule _).2 ?_) i j⟩
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [zpow_natCast, Units.val_pow_eq_pow_val]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) k
    · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))) k

end Main

theorem isCompact_closure_zpowers_mulGL_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (t : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwOrbLat.mulGL e b t) : Set (GLw a w))) ↔ t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A :=
  fun _ _ _ _ _ _ e he _ _ b t => isCompact_closure_zpowers_mulGL_iff' e b he t

end GlobalTheory.TwOrbLat
