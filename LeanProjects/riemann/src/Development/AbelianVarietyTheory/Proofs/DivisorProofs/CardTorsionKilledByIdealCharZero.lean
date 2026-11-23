import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsZeroPtEpsScalePt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RemainderTermSummable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCardKernelEqNormPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CharZeroCount

section Alg

variable (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (h : ℕ)

omit [NumberField F] in
theorem smul_mem_torsion_left {x y : Ideal (𝓞 F)} {b : 𝓞 F} (hb : b ∈ y) {m : M}
    (hm : m ∈ Submodule.torsionBySet (𝓞 F) M ((x * y : Ideal (𝓞 F)) : Set (𝓞 F))) :
    b • m ∈ Submodule.torsionBySet (𝓞 F) M (x : Set (𝓞 F)) := by
  rw [Submodule.mem_torsionBySet_iff] at hm ⊢
  intro r
  rw [smul_smul]
  exact hm ⟨(r : 𝓞 F) * b, Ideal.mul_mem_mul r.2 hb⟩

omit [NumberField F] in
theorem mem_torsion_mul {x y : Ideal (𝓞 F)} {m : M}
    (hm : m ∈ Submodule.torsionBySet (𝓞 F) M (x : Set (𝓞 F))) :
    m ∈ Submodule.torsionBySet (𝓞 F) M ((x * y : Ideal (𝓞 F)) : Set (𝓞 F)) :=
  Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.mul_le_inf.trans inf_le_left) hm

def torsionMulEquiv {x y : Ideal (𝓞 F)} {a b : 𝓞 F} (ha : a ∈ x) (hb : b ∈ y) (hab : a + b = 1) :
    Submodule.torsionBySet (𝓞 F) M ((x * y : Ideal (𝓞 F)) : Set (𝓞 F)) ≃
      Submodule.torsionBySet (𝓞 F) M (x : Set (𝓞 F)) × Submodule.torsionBySet (𝓞 F) M (y : Set (𝓞 F)) where
  toFun m := (⟨b • (m : M), smul_mem_torsion_left F M hb m.2⟩,
    ⟨a • (m : M), smul_mem_torsion_left F M ha (by rw [mul_comm]; exact m.2)⟩)
  invFun uv := ⟨(uv.1 : M) + uv.2, Submodule.add_mem _ (mem_torsion_mul F M uv.1.2)
    (by rw [mul_comm]; exact mem_torsion_mul F M uv.2.2)⟩
  left_inv m := by
    apply Subtype.ext
    show b • (m : M) + a • (m : M) = m
    rw [← add_smul, add_comm, hab, one_smul]
  right_inv uv := by
    have hu : a • (uv.1 : M) = 0 := (Submodule.mem_torsionBySet_iff _ _).1 uv.1.2 ⟨a, ha⟩
    have hv : b • (uv.2 : M) = 0 := (Submodule.mem_torsionBySet_iff _ _).1 uv.2.2 ⟨b, hb⟩
    have hb' : b = 1 - a := by rw [← hab]; ring
    have ha' : a = 1 - b := by rw [← hab]; ring
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show b • ((uv.1 : M) + uv.2) = uv.1
      rw [smul_add, hv, add_zero, hb', sub_smul, one_smul, hu, sub_zero]
    · show a • ((uv.1 : M) + uv.2) = uv.2
      rw [smul_add, hu, zero_add, ha', sub_smul, one_smul, hv, sub_zero]

variable {F M h}

theorem card_torsion_maximal (hdiv : ∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g))
    (helt : ∀ c : 𝓞 F, c ≠ 0 → Nat.card (Submodule.torsionBy (𝓞 F) M c) = (Algebra.norm ℤ c).natAbs ^ h)
    (P : Ideal (𝓞 F)) (hmax : P.IsMaximal) (hne : P ≠ ⊥) :
    Nat.card (Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ P) ^ h := by
  have hw0nz : P ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero hne
  set H := orderOf (ClassGroup.mk0 ⟨P, hw0nz⟩) with hH
  have hH0 : 0 < H := orderOf_pos _
  have hpowz : P ^ H ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hne)
  have hprin : Submodule.IsPrincipal (P ^ H) := by
    rw [← ClassGroup.mk0_eq_one_iff hpowz]
    have : (⟨P ^ H, hpowz⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨P, hw0nz⟩ ^ H := rfl
    rw [this, map_pow, hH, pow_orderOf_eq_one]
  obtain ⟨c, hcgen⟩ := hprin.principal
  have hspan : P ^ H = Ideal.span {c} := hcgen
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hspan
    exact pow_ne_zero _ hne hspan
  have hnorm : (Algebra.norm ℤ c).natAbs = Nat.card (𝓞 F ⧸ P) ^ H := by
    rw [← Ideal.absNorm_span_singleton, ← hspan, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hTH : Nat.card (Submodule.torsionBySet (𝓞 F) M ((P ^ H : Ideal (𝓞 F)) : Set (𝓞 F))) =
      Nat.card (𝓞 F ⧸ P) ^ (H * h) := by
    rw [hspan, Submodule.torsionBySet_span_singleton_eq, pow_mul, ← hnorm, helt c hc0]
  have hq : 1 < Nat.card (𝓞 F ⧸ P) := by
    have hfin : Finite (𝓞 F ⧸ P) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hne
    letI := Ideal.Quotient.field P
    exact Finite.one_lt_card
  have hTHfin : Finite (Submodule.torsionBySet (𝓞 F) M ((P ^ H : Ideal (𝓞 F)) : Set (𝓞 F))) := by
    apply Nat.finite_of_card_ne_zero
    rw [hTH]
    exact pow_ne_zero _ (by omega)
  have hsub : Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F)) ≤
      Submodule.torsionBySet (𝓞 F) M ((P ^ H : Ideal (𝓞 F)) : Set (𝓞 F)) :=
    Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_le_self hH0.ne')
  have hT1fin : Finite (Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F))) :=
    Finite.of_injective _ (Submodule.inclusion_injective hsub)
  letI := Ideal.Quotient.field P
  haveI : Module.Finite (𝓞 F ⧸ P) (Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F))) :=
    Module.Finite.of_finite
  set h' := Module.finrank (𝓞 F ⧸ P) (Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F))) with hh'
  have hT1 : Nat.card (Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ P) ^ h' :=
    Module.natCard_eq_pow_finrank
  have hall := GlobalTheory.torsion_pow_card F M P h' hmax hne hdiv hT1 H
  rw [hTH] at hall
  have he : H * h = H * h' := Nat.pow_right_injective hq hall
  have he' : h' = h := (Nat.eq_of_mul_eq_mul_left hH0 he).symm
  rw [hT1, he']

theorem card_torsion_ideal (hdiv : ∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g))
    (helt : ∀ c : 𝓞 F, c ≠ 0 → Nat.card (Submodule.torsionBy (𝓞 F) M c) = (Algebra.norm ℤ c).natAbs ^ h)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Nat.card (Submodule.torsionBySet (𝓞 F) M (I : Set (𝓞 F))) = Ideal.absNorm I ^ h := by
  refine UniqueFactorizationMonoid.induction_on_coprime
    (P := fun I : Ideal (𝓞 F) => I ≠ ⊥ → Nat.card (Submodule.torsionBySet (𝓞 F) M (I : Set (𝓞 F))) =
      Ideal.absNorm I ^ h) I ?_ ?_ ?_ ?_ hI
  · intro h0
    exact absurd rfl h0
  · intro u hu _
    rw [Ideal.isUnit_iff] at hu
    subst hu
    have hbot : Submodule.torsionBySet (𝓞 F) M ((⊤ : Ideal (𝓞 F)) : Set (𝓞 F)) = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have := (Submodule.mem_torsionBySet_iff _ _).1 hm ⟨1, Submodule.mem_top⟩
      rw [Submodule.mem_bot]
      simpa using this
    rw [hbot, Ideal.absNorm_top, one_pow]
    simp
  · intro P i hp _
    have hpI : P.IsPrime := Ideal.isPrime_of_prime hp
    have hne : P ≠ ⊥ := hp.ne_zero
    have hmax : P.IsMaximal := hpI.isMaximal hne
    rw [GlobalTheory.torsion_pow_card F M P h hmax hne hdiv (card_torsion_maximal hdiv helt P hmax hne) i, map_pow,
      Ideal.absNorm_apply P, Submodule.cardQuot_apply, ← pow_mul, mul_comm]
  · intro x y hrel hx hy hxy
    have hx0 : x ≠ ⊥ := fun h0 => hxy (by rw [h0, Submodule.bot_mul])
    have hy0 : y ≠ ⊥ := fun h0 => hxy (by rw [h0, Submodule.mul_bot])
    have hsup : x ⊔ y = ⊤ := by
      have hu := hrel (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right)
      exact Ideal.isUnit_iff.1 hu
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top (x := (1 : 𝓞 F)))
    rw [Nat.card_congr (torsionMulEquiv F M ha hb hab), Nat.card_prod, hx hx0, hy hy0, map_mul, mul_pow]

end Alg

end GlobalTheory.UPel.HT.ES.CharZeroCount

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CharZeroCount

open GlobalTheory.TanPtMod

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}
  {s : S ⟶ Sp R}

theorem tan_eq_one_charZero (o : Obj b N s) (k : Type) [Field k] [CharZero k] (x : Sp k ⟶ S) (c : 𝓞 D.F)
    (hc0 : c ≠ 0) (v : epsPtR x ⟶ o.A)
    (hv0 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left)
    (hv : v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) : v = 1 := by
  let L : 𝓞 D.F →+* Module.End k (Tan x o.A) := (actEnd o.act).comp (algebraMap (𝓞 D.F) D.O)
  have hL : ∀ c (u : Tan x o.A), (L c u).hom = u.hom ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) := fun _ _ => rfl
  have hmv : v ∈ tanSub x o.A := (mem_tanSub_iff x o.A _).mpr hv0
  have hLu : L c (Tan.mk v hmv) = 0 := Tan.ext (by rw [hL]; exact hv)
  set n := Ideal.absNorm (Ideal.span {c}) with hn
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {c}))
  have hn0 : n ≠ 0 := by
    rw [hn, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  have h1 : L ((n : ℕ) : 𝓞 D.F) (Tan.mk v hmv) = 0 := by
    rw [← hd, map_mul, Module.End.mul_apply, hLu, map_zero]
  rw [map_natCast, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul k] at h1
  have hu : Tan.mk v hmv = 0 := (smul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr hn0)
  exact congrArg Tan.hom hu

theorem card_ker_elt_charZero (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S)
    (c : 𝓞 D.F) (hc : c ≠ 0) :
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} =
      (Algebra.norm ℤ c).natAbs ^ (D.m * D.n) := by
  obtain ⟨ℓ, hℓ1, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  have hℓp : ℓ ≠ p := by omega
  have hℓk : (ℓ : k) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  exact GlobalTheory.T.abelianScheme_card_kernel_eq_norm_pow S o.A o.ab D.F (o.act.toF D) k x (D.m * D.n) ℓ hℓ hℓk
    (GlobalTheory.QuotientCardinalityFinrank.torsion_points_free p D R b N S s o k x ℓ hℓ hℓp) c hc
    (fun v hv0 hv => tan_eq_one_charZero o k x c hc v hv0 hv)

end GlobalTheory.UPel.HT.ES.CharZeroCount

namespace GlobalTheory.UPel.HT.ES.CharZeroCount

theorem card_killedBy_charZero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w : Ideal (𝓞 D.F)), w ≠ ⊥ →
    ∀ (κ : Type) [Field κ] [IsAlgClosed κ] [CharZero κ] (x : Sp κ ⟶ S),
      Nat.card {g : Over.mk x ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * D.n) := by
  intro p _ D R _ b N S s o w hw k _ _ _ x
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
  have hdiv : ∀ c : 𝓞 D.F, c ≠ 0 → Function.Surjective (fun g : Additive (Over.mk x ⟶ o.A) => c • g) := by
    intro c hc g
    set n := Ideal.absNorm (Ideal.span {c}) with hn
    have hn0 : 0 < n := by
      rw [hn, Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hc
    have hmem : ((n : ℕ) : 𝓞 D.F) ∈ Ideal.span {c} := Ideal.absNorm_mem _
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨g', hg'⟩ := GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed S o.A o.ab k x n hn0 g.toMul
    refine ⟨c' • Additive.ofMul g', ?_⟩
    show c • c' • Additive.ofMul g' = g
    rw [smul_smul, mul_comm, hc', Nat.cast_smul_eq_nsmul, ← ofMul_pow, hg']
    rfl
  have helt : ∀ c : 𝓞 D.F, c ≠ 0 → Nat.card (Submodule.torsionBy (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) c) =
      (Algebra.norm ℤ c).natAbs ^ (D.m * D.n) := by
    intro c hc
    rw [← card_ker_elt_charZero o k x c hc]
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun g => ?_))
    rw [Submodule.mem_torsionBy_iff, hsm]
    exact ⟨fun h => congrArg Additive.toMul h, fun h => congrArg Additive.ofMul h⟩
  rw [← card_torsion_ideal hdiv helt w hw]
  refine (Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul (fun g => ?_)))
  rw [Submodule.mem_torsionBySet_iff]
  constructor
  · intro h c
    rw [hsm]
    exact congrArg Additive.ofMul (h c.1 c.2)
  · intro h c hc
    have := h ⟨c, hc⟩
    rw [hsm] at this
    exact this

end GlobalTheory.UPel.HT.ES.CharZeroCount
