import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureOnTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTangentInjectiveAwayFromEtalePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCardKernelEqNormPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev.GeoCard

theorem card_ker_elt {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {w0 : Ideal (𝓞 D.F)} (hw : IsEtPlace b w0) {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S) (c : 𝓞 D.F) (hc : c ≠ 0)
    (hcw : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w) :
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} =
      (Algebra.norm ℤ c).natAbs ^ (D.m * D.n) := by
  obtain ⟨ℓ, hℓ1, hℓ⟩ := Nat.exists_infinite_primes (p + ringChar k + 1)
  have hℓp : ℓ ≠ p := by omega
  have hℓk : (ℓ : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k (ringChar k)]
    intro hd
    rcases (Nat.dvd_prime hℓ).1 hd with h1 | h1
    · exact CharP.ringChar_ne_one (R := k) h1
    · omega
  exact GlobalTheory.T.abelianScheme_card_kernel_eq_norm_pow S o.A o.ab D.F (o.act.toF D) k x (D.m * D.n) ℓ hℓ hℓk (GlobalTheory.T.exists_level_structure_on_torsion p D R b N S s o k x ℓ hℓ hℓp) c hc
    (GlobalTheory.T.harrisTaylor_tangent_injective_away_from_etalePlace p D R b N w0 hw S s o k x c hc hcw)

theorem card_ker_place : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (w0 : Ideal (𝓞 D.F)), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S), Nat.card {g : Over.mk x ⟶ o.A // ∀ c ∈ w0,
      g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} = Nat.card (𝓞 D.F ⧸ w0) ^ (D.m * D.n) := by
  intro p _ D R _ b N w0 hw S s o k _ _ x
  letI : CommGroup (Over.mk x ⟶ o.A) := Hom.commGroup
  have act0 : o.act.act 0 = 1 := by
    have h := o.act.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  letI : Module (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) :=
    { smul := fun c g => Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c))
      one_smul := fun g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 1)) = g
        rw [map_one, o.act.one, Category.comp_id]; rfl
      mul_smul := fun a b g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a * b))) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O b)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
        rw [map_mul, o.act.mul, Category.assoc]
      smul_zero := fun c => by
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        show Additive.ofMul ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) = Additive.ofMul 1
        rw [MonObj.one_comp]
      smul_add := fun c g g' => by
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        show Additive.ofMul ((g.toMul * g'.toMul) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) *
            (g'.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)))
        rw [MonObj.mul_comp]
      add_smul := fun a b g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a + b))) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) *
            (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O b)))
        rw [map_add, o.act.add, MonObj.comp_mul]
      zero_smul := fun g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 0)) = Additive.ofMul 1
        rw [map_zero, act0, MonObj.comp_one] }
  have hsm : ∀ (c : 𝓞 D.F) (g : Additive (Over.mk x ⟶ o.A)),
      c • g = Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) := fun _ _ => rfl
  have hmax : w0.IsMaximal := hw.1
  have hne : w0 ≠ ⊥ := by
    intro h0
    have hp : ((p : ℕ) : 𝓞 D.F) ∈ w0 := hw.2.1
    rw [h0, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

  have hdiv : ∀ c : 𝓞 D.F, c ≠ 0 → Function.Surjective (fun g : Additive (Over.mk x ⟶ o.A) => c • g) := by
    intro c hc g
    set n := Ideal.absNorm (Ideal.span {c}) with hn
    have hn0 : 0 < n := by
      rw [hn, Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hc
    have hmem : ((n : ℕ) : 𝓞 D.F) ∈ Ideal.span {c} := Ideal.absNorm_mem _
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨g', hg'⟩ := GlobalTheory.T.exists_pow_eq_point_of_isAbelianScheme S o.A o.ab k x n hn0 g.toMul
    refine ⟨c' • Additive.ofMul g', ?_⟩
    show c • c' • Additive.ofMul g' = g
    rw [smul_smul, mul_comm, hc', Nat.cast_smul_eq_nsmul, ← ofMul_pow, hg']
    rfl

  have hT : ∀ I : Ideal (𝓞 D.F), Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      (I : Set (𝓞 D.F))) = Nat.card {g : Over.mk x ⟶ o.A // ∀ c ∈ I,
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} := by
    intro I
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun g => ?_))
    rw [Submodule.mem_torsionBySet_iff]
    constructor
    · intro h c hc
      have := h ⟨c, hc⟩
      rw [hsm] at this
      exact this
    · intro h c
      rw [hsm]
      exact congrArg Additive.ofMul (h c.1 c.2)

  have hw0nz : w0 ∈ nonZeroDivisors (Ideal (𝓞 D.F)) := mem_nonZeroDivisors_of_ne_zero hne
  set H := orderOf (ClassGroup.mk0 ⟨w0, hw0nz⟩) with hH
  have hH0 : 0 < H := orderOf_pos _
  have hpowz : w0 ^ H ∈ nonZeroDivisors (Ideal (𝓞 D.F)) := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hne)
  have hprin : Submodule.IsPrincipal (w0 ^ H) := by
    rw [← ClassGroup.mk0_eq_one_iff hpowz]
    have : (⟨w0 ^ H, hpowz⟩ : nonZeroDivisors (Ideal (𝓞 D.F))) = ⟨w0, hw0nz⟩ ^ H := rfl
    rw [this, map_pow, hH, pow_orderOf_eq_one]
  obtain ⟨c, hcgen⟩ := hprin.principal
  have hspan : w0 ^ H = Ideal.span {c} := hcgen
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hspan
    exact pow_ne_zero _ hne hspan
  have hcw : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w := by
    intro w hwm _ hww hcw
    apply hww
    have h1 : w0 ^ H ≤ w := by rw [hspan, Ideal.span_le, Set.singleton_subset_iff]; exact hcw
    exact (hmax.eq_of_le hwm.ne_top (hwm.isPrime.le_of_pow_le h1)).symm
  have hcount := card_ker_elt hw o k x c hc0 hcw
  have hnorm : (Algebra.norm ℤ c).natAbs = Nat.card (𝓞 D.F ⧸ w0) ^ H := by
    rw [← Ideal.absNorm_span_singleton, ← hspan, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]

  have hTH : Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F))) = Nat.card (𝓞 D.F ⧸ w0) ^ (H * (D.m * D.n)) := by
    rw [hspan, Submodule.torsionBySet_span_singleton_eq, pow_mul, ← hnorm, ← hcount]
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun g => ?_))
    rw [Submodule.mem_torsionBy_iff, hsm]
    exact ⟨fun h => congrArg Additive.toMul h, fun h => congrArg Additive.ofMul h⟩

  have hq : 1 < Nat.card (𝓞 D.F ⧸ w0) := by
    have hfin : Finite (𝓞 D.F ⧸ w0) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hne
    letI := Ideal.Quotient.field w0
    exact Finite.one_lt_card

  have hTHfin : Finite (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F))) := by
    apply Nat.finite_of_card_ne_zero
    rw [hTH]
    exact pow_ne_zero _ (by omega)
  have hsub : Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F)) ≤
      Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F)) :=
    Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_le_self hH0.ne')
  have hT1fin : Finite (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) :=
    Finite.of_injective _ (Submodule.inclusion_injective hsub)
  letI := Ideal.Quotient.field w0
  haveI : Module.Finite (𝓞 D.F ⧸ w0)
      (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) :=
    Module.Finite.of_finite
  set h' := Module.finrank (𝓞 D.F ⧸ w0)
      (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) with hh'
  have hT1 : Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) =
      Nat.card (𝓞 D.F ⧸ w0) ^ h' := Module.natCard_eq_pow_finrank
  have hall := GlobalTheory.T.card_torsionBySet_pow_of_divisible_numberField D.F _ w0 h' hmax hne hdiv hT1 H
  rw [hTH] at hall
  have he : H * (D.m * D.n) = H * h' := Nat.pow_right_injective hq hall
  have he' : h' = D.m * D.n := (Nat.eq_of_mul_eq_mul_left hH0 he).symm
  rw [← hT, hT1, he']

end GlobalTheory.UPel.HT.EtLev.GeoCard
