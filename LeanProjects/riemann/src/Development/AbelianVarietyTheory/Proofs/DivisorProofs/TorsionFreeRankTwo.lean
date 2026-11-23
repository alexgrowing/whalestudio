import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDiagNatCastSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallCoprimeNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatLevelOf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMult

namespace TorsRankTwo

open LevFlat

@[reducible] def addModule {M O : Type} [CommGroup M] [CommRing O] {ρ : O → M →* M} (h : IsAct ρ) :
    Module O (Additive M) where
  smul a x := Additive.ofMul (ρ a x.toMul)
  one_smul x := h.one x.toMul
  mul_smul a b x := by
    show ρ (a * b) x.toMul = ρ a (ρ b x.toMul)
    rw [mul_comm, h.mul]
  smul_zero a := map_one (ρ a)
  smul_add a x y := map_mul (ρ a) x.toMul y.toMul
  add_smul a b x := h.add a b x.toMul
  zero_smul x := h.zero x.toMul

theorem exists_charExp (F : Type) [Field F] [NumberField F] (N : ℕ) (Ω : Type) [Field Ω] (hN : (N : Ω) ≠ 0) :
    ∃ q : ℕ, 1 ≤ q ∧ (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 → IsCoprime 𝔭 (Ideal.span {(q : 𝓞 F)})) ∧
      ∀ b : 𝓞 F, b ≠ 0 → IsCoprime (Algebra.norm ℤ b) (q : ℤ) → ((Algebra.norm ℤ b : ℤ) : Ω) ≠ 0 := by
  obtain ⟨p, hp⟩ := CharP.exists Ω
  rcases CharP.char_is_prime_or_zero Ω p with hpp | rfl
  · refine ⟨p, hpp.one_le, fun 𝔭 h𝔭 hN𝔭 => ?_, fun b _ hb h0 => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      have hp𝔭 : (p : 𝓞 F) ∈ 𝔭 := by
        rw [h𝔭.eq_of_le hne le_sup_left]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      have hc : Nat.Coprime p N := hpp.coprime_iff_not_dvd.2 fun h => hN ((CharP.cast_eq_zero_iff Ω p N).2 h)
      obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 F))
      simp only [map_natCast] at huv
      exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ 𝔭.add_mem (𝔭.mul_mem_left u hp𝔭) (𝔭.mul_mem_left v hN𝔭)))
    · obtain ⟨u, v, huv⟩ := hb.map (Int.castRingHom Ω)
      rw [map_natCast, CharP.cast_eq_zero, eq_intCast, h0] at huv
      simp at huv
  · haveI := CharP.charP_to_charZero Ω
    refine ⟨1, le_rfl, fun 𝔭 _ _ => ?_, fun b hb _ => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq, Nat.cast_one, Ideal.span_singleton_one, sup_top_eq]
    · exact Int.cast_ne_zero.2 (Algebra.norm_ne_zero_iff.2 hb)

theorem exists_ptEquiv {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S}
    {X' : Obj F 𝔠 S'} {t : S' ⟶ S} {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X t φ) :
    ∃ e : (𝟙_ (Over S') ⟶ X'.A) ≃* (Over.mk t ⟶ X.A), ∀ x a, e (x ≫ X'.rm.act a) = e x ≫ X.rm.act a := by
  have key : ∀ t' : S' ⟶ S, (𝟙_ (Over S')).hom ≫ t = t' →
      ∃ e : (𝟙_ (Over S') ⟶ X'.A) ≃* (Over.mk t' ⟶ X.A), ∀ x a, e (x ≫ X'.rm.act a) = e x ≫ X.rm.act a := by
    rintro _ rfl
    obtain ⟨e, he⟩ := ptEquiv h.grp (𝟙_ (Over S'))
    refine ⟨e, fun x a => Over.OverMorphism.ext ?_⟩
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, h.act]
  exact key t (Category.id_comp t)

end TorsRankTwo

open LevFlat TorsRankTwo

theorem torsion_free_rank_two :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (S : Scheme.{0}) (X : Obj F 𝔠 S)
    (N : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), (N : Ω) ≠ 0 →
    ∃ p : Fin 2 → (Over.mk t ⟶ X.A), (∀ i, p i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : Over.mk t ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) := by
  intro F _ _ _ 𝔠 S X N Ω _ _ t hN
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN Nat.cast_zero
  obtain ⟨X', φ, hφ⟩ := X.exists_isPullBy t
  obtain ⟨e, he⟩ := exists_ptEquiv hφ
  letI : Module (𝓞 F) (Additive (Over.mk t ⟶ X.A)) := addModule (isAct_ptAct X (Over.mk t))
  obtain ⟨q, hq, hq𝔭, hqb⟩ := exists_charExp F N Ω hN
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.RealMultKernel.card_ker_act_le F 𝔠 Ω X'
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.SmallNorm.exists_small_coprime_norm F q hq
  obtain ⟨p, h1, h2, h3⟩ := GlobalTheory.RankTwoTorsion.rank_two_torsion F (Additive (Over.mk t ⟶ X.A)) N
    (Nat.one_le_iff_ne_zero.2 hN0)
    (fun j => by
      rw [← GlobalTheory.abMulN_holds Ω X'.A _ (N ^ j) X'.ab X'.dim (by rw [Nat.cast_pow]; exact pow_ne_zero j hN)]
      refine Nat.card_congr (Equiv.subtypeEquiv (Additive.toMul.trans e.symm.toEquiv) fun x => ?_)
      show x.toMul ^ (N ^ j) = 1 ↔ e.symm x.toMul ^ (N ^ j) = 1
      rw [← map_pow e.symm, e.symm.map_eq_one_iff])
    (fun 𝔭 h𝔭 hN𝔭 => ⟨C₀ * C₁ ^ 2, fun n => by
      have hI : 𝔭 ^ n ≠ ⊥ := fun h0 => by
        have := Ideal.pow_mem_pow hN𝔭 n
        rw [h0, Ideal.mem_bot] at this
        exact pow_ne_zero n (Nat.cast_ne_zero.2 hN0) this
      obtain ⟨b, hbI, hb0, hbq, k, hk, hkf⟩ := hC₁ (𝔭 ^ n) hI (hq𝔭 𝔭 h𝔭 hN𝔭).pow_left
      obtain ⟨hfin, hle⟩ := hC₀ b k (hqb b hb0 hbq) hk
      let f : {x : Additive (Over.mk t ⟶ X.A) // ∀ a ∈ 𝔭 ^ n, a • x = 0} →
          {y : 𝟙_ (Over (Sp Ω)) ⟶ X'.A // y ≫ X'.rm.act b = 1} := fun x =>
        ⟨e.symm x.1.toMul, e.injective (by
          rw [he, e.apply_symm_apply, map_one]
          exact x.2 b hbI)⟩
      have hf : Function.Injective f := fun x y hxy =>
        Subtype.ext (Additive.toMul.injective (e.symm.injective (congrArg Subtype.val hxy)))
      refine (Nat.card_le_card_of_injective f hf).trans (hle.trans ?_)
      rw [map_pow] at hkf
      calc C₀ * k ^ (2 * Module.finrank ℚ F) = C₀ * (k ^ Module.finrank ℚ F) ^ 2 := by ring
        _ ≤ C₀ * (C₁ * Ideal.absNorm 𝔭 ^ n) ^ 2 := by gcongr
        _ = C₀ * C₁ ^ 2 * Ideal.absNorm 𝔭 ^ (2 * n) := by ring⟩)
  exact ⟨fun i => (p i).toMul, h1, h2, fun y hy => h3 (Additive.ofMul y) hy⟩

end GlobalTheory.RealMult
