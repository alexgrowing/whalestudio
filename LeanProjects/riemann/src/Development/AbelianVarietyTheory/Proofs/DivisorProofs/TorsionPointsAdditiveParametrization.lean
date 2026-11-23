import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionBySetPowFreeOfCardPowNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByPrimeAtEtalePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev.TorFree
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {S : Scheme.{0}}

theorem act_zero {G : Over S} [GrpObj G] (act : OActN D.O G) : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

def ptModule {G : Over S} [GrpObj G] [IsCommMonObj G] (act : OActN D.O G) (T : Over S) :
    letI : CommGroup (T ⟶ G) := Hom.commGroup
    Module (𝓞 D.F) (Additive (T ⟶ G)) :=
  letI : CommGroup (T ⟶ G) := Hom.commGroup
  { smul := fun c g => Additive.ofMul (g.toMul ≫ act.act (algebraMap (𝓞 D.F) D.O c))
    one_smul := fun g => by
      show Additive.ofMul (g.toMul ≫ act.act (algebraMap (𝓞 D.F) D.O 1)) = g
      rw [map_one, act.one, Category.comp_id]; rfl
    mul_smul := fun a b g => by
      show Additive.ofMul (g.toMul ≫ act.act (algebraMap (𝓞 D.F) D.O (a * b))) =
        Additive.ofMul ((g.toMul ≫ act.act (algebraMap (𝓞 D.F) D.O b)) ≫ act.act (algebraMap (𝓞 D.F) D.O a))
      rw [map_mul, act.mul, Category.assoc]
    smul_zero := fun c => by
      haveI := act.hom (algebraMap (𝓞 D.F) D.O c)
      show Additive.ofMul ((1 : T ⟶ G) ≫ act.act (algebraMap (𝓞 D.F) D.O c)) = Additive.ofMul 1
      rw [MonObj.one_comp]
    smul_add := fun c g g' => by
      haveI := act.hom (algebraMap (𝓞 D.F) D.O c)
      show Additive.ofMul ((g.toMul * g'.toMul) ≫ act.act (algebraMap (𝓞 D.F) D.O c)) =
        Additive.ofMul ((g.toMul ≫ act.act (algebraMap (𝓞 D.F) D.O c)) * (g'.toMul ≫ act.act (algebraMap (𝓞 D.F) D.O c)))
      rw [MonObj.mul_comp]
    add_smul := fun a b g => by
      show Additive.ofMul (g.toMul ≫ act.act (algebraMap (𝓞 D.F) D.O (a + b))) =
        Additive.ofMul ((g.toMul ≫ act.act (algebraMap (𝓞 D.F) D.O a)) * (g.toMul ≫ act.act (algebraMap (𝓞 D.F) D.O b)))
      rw [map_add, act.add, MonObj.comp_mul]
    zero_smul := fun g => by
      show Additive.ofMul (g.toMul ≫ act.act (algebraMap (𝓞 D.F) D.O 0)) = Additive.ofMul 1
      rw [map_zero, act_zero, MonObj.comp_one] }

end GlobalTheory.UPel.HT.EtLev.TorFree

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev.TorFree

theorem free_torsion_geomPt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ),
  IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
  ∃ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → (Over.mk x ⟶ o.A), (∀ a a', f (a + a') = f a * f a') ∧
    (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (w0 ^ r) c • a) = f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ∧
    Function.Injective f ∧
    ∀ g : Over.mk x ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ a, f a = g := by
  intro p _ D R _ b N w0 r hw S s o k _ _ x
  letI : CommGroup (Over.mk x ⟶ o.A) := Hom.commGroup
  letI : Module (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) := ptModule o.act (Over.mk x)
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
  have hcard1 : Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) =
      Nat.card (𝓞 D.F ⧸ w0) ^ (D.m * D.n) := by
    rw [← GlobalTheory.T.card_torsion_killed_by_prime_at_etale_place p D R b N w0 hw S s o k x]
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
  have hall := GlobalTheory.T.card_torsionBySet_pow_of_divisible_numberField D.F _ w0 (D.m * D.n) hmax hne hdiv hcard1
  obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.T.torsionBySet_pow_free_of_card_pow_numberField D.F _ w0 (D.m * D.n) r hmax hne hall
  refine ⟨fun a => (f a).toMul, ?_, ?_, ?_, ?_⟩
  · intro a a'
    show Additive.toMul (f (a + a')) = Additive.toMul (f a) * Additive.toMul (f a')
    rw [map_add]; rfl
  · intro c a
    show Additive.toMul (f (Ideal.Quotient.mk (w0 ^ r) c • a)) = Additive.toMul (f a) ≫ _
    rw [hf1, hsm]; rfl
  · intro a a' h
    exact hf2 (Additive.toMul.injective h)
  · intro g hg
    obtain ⟨a, ha⟩ := hf3 (Additive.ofMul g) (fun c hc => by rw [hsm]; exact congrArg Additive.ofMul (hg c hc))
    exact ⟨a, by show Additive.toMul (f a) = g; rw [ha]; rfl⟩

end GlobalTheory.UPel.HT.EtLev.TorFree
