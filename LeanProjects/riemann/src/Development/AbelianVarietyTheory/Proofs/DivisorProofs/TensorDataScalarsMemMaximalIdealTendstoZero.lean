import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEvenCubicalValuesNotMemMaximalIdealPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInIffScalarMem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitsK
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPolScal

theorem exists_bilin (R : Type) [CommRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    (k : X → X → (FractionRing R)ˣ) (hs : ∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b)
    (ha : ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) :
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] Additive (FractionRing R)ˣ, ∀ a b, ∃ u ∈ unitsK R, k a b = u * (B a b).toMul := by
  set H := unitsK R
  have h1 : ∀ u ∈ H, (QuotientGroup.mk' H) u = 1 := fun u hu => (QuotientGroup.eq_one_iff u).2 hu
  let g : X → X → Additive ((FractionRing R)ˣ ⧸ H) := fun a b => Additive.ofMul (QuotientGroup.mk' H (k a b))
  have gs : ∀ a b, g b a = g a b := fun a b => by
    obtain ⟨u, hu, e⟩ := hs a b
    simp only [g, e, map_mul, h1 u hu, _root_.one_mul]
  have ga : ∀ a a' b, g (a + a') b = g a b + g a' b := fun a a' b => by
    obtain ⟨u, hu, e⟩ := ha a a' b
    simp only [g, e, map_mul, h1 u hu, _root_.one_mul, ofMul_mul]
  have gb : ∀ a b b', g a (b + b') = g a b + g a b' := fun a b b' => by
    rw [gs, ga, gs b, gs b']
  have gsa : ∀ (c : ℤ) a b, g (c • a) b = c • g a b := fun c a b =>
    map_zsmul (AddMonoidHom.mk' (fun a => g a b) (fun a a' => ga a a' b)) c a
  have gsb : ∀ (c : ℤ) a b, g a (c • b) = c • g a b := fun c a b => by
    rw [gs, gsa, gs]
  let F : X →ₗ[ℤ] X →ₗ[ℤ] Additive ((FractionRing R)ˣ ⧸ H) := LinearMap.mk₂ ℤ g ga gsa gb gsb
  let π : Additive (FractionRing R)ˣ →+ Additive ((FractionRing R)ˣ ⧸ H) := MonoidHom.toAdditive (QuotientGroup.mk' H)
  let bs := Module.Free.chooseBasis ℤ X
  let B : X →ₗ[ℤ] X →ₗ[ℤ] Additive (FractionRing R)ˣ :=
    bs.constr ℤ fun i => bs.constr ℤ fun j => Additive.ofMul (k (bs i) (bs j))
  have e : B.compr₂ π.toIntLinearMap = F := LinearMap.ext_basis bs bs fun i j => by
    simp [B, F, g, π]
  refine ⟨B, fun a b => ⟨k a b * ((B a b).toMul)⁻¹, ?_, by rw [inv_mul_cancel_right]⟩⟩
  have e1 : QuotientGroup.mk' H (B a b).toMul = QuotientGroup.mk' H (k a b) :=
    congrArg Additive.toMul (congrArg (fun C => C a b) e)
  rw [← QuotientGroup.eq_one_iff]
  show QuotientGroup.mk' H _ = 1
  rw [map_mul, map_inv, ← e1, mul_inv_cancel]

end GlobalTheory.Mum.TensPolScal

namespace GlobalTheory.Mum.TensPolScal

theorem scalars_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X → X → (FractionRing R)ˣ), (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) → (∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) → (∀ y, y ≠ 0 → ∃ s ∈ maximalIdeal R, (k y y : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (a' : (Fin r → X) → (FractionRing R)ˣ), (∀ z, ∃ u ∈ unitsK R, a' z = u * ∏ i, ∏ j, k (z i) (z j) ^ W i j) → (∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (a' z : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {z | ¬ ∃ s ∈ maximalIdeal R ^ n, (a' z : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ _ k hs ha hp r W hW a' h'
  obtain ⟨B, hB⟩ := exists_bilin R X k hs ha
  choose u hu eu using hB
  let κ : X → (FractionRing R)ˣ := fun x => (B x x).toMul
  let κ' : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (κ (z i + z j) * (κ (z i))⁻¹ * (κ (z j))⁻¹) ^ W i j
  let P : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (B (z i) (z j)).toMul ^ W i j
  let Q : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (B (z j) (z i)).toMul ^ W i j
  have eP : ∀ z, Additive.ofMul (P z) = ∑ i, ∑ j, W i j • B (z i) (z j) := fun z => by
    simp only [P, ofMul_prod, ofMul_zpow, ofMul_toMul]
  have eQ : ∀ z, Additive.ofMul (Q z) = ∑ i, ∑ j, W i j • B (z j) (z i) := fun z => by
    simp only [Q, ofMul_prod, ofMul_zpow, ofMul_toMul]
  have eκ' : ∀ z, κ' z = P z * Q z := by
    intro z
    apply Additive.ofMul.injective
    rw [ofMul_mul, eP, eQ, ← Finset.sum_add_distrib]
    simp only [κ', κ, ofMul_prod, ofMul_zpow, ofMul_mul, ofMul_inv, ofMul_toMul, map_add, LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_add]
    congr 1
    abel

  have hBs : ∀ a b, ∃ v ∈ unitsK R, (B b a).toMul = v * (B a b).toMul := by
    intro a b
    obtain ⟨w, hw, e⟩ := hs a b
    refine ⟨(u b a)⁻¹ * w * u a b, mul_mem (mul_mem (inv_mem (hu b a)) hw) (hu a b), ?_⟩
    rw [show (B b a).toMul = (u b a)⁻¹ * k b a by rw [eu b a, inv_mul_cancel_left], e, eu a b]
    group
  choose v hv ev using hBs
  have eQP : ∀ z, Q z = (∏ i, ∏ j, v (z i) (z j) ^ W i j) * P z := by
    intro z
    simp only [Q, P, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [ev (z i) (z j), mul_zpow]
  have κn : ∀ x, κ (-x) = κ x := fun x => by simp [κ]
  have κc : ∀ x y w, κ (x + y + w) * κ x * κ y * κ w = κ (x + y) * κ (x + w) * κ (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [κ, ofMul_mul, ofMul_toMul, map_add, LinearMap.add_apply]
    abel
  have κp : ∀ x, x ≠ 0 → ∃ s ∈ maximalIdeal R, (κ x : FractionRing R) = algebraMap R _ s := fun x hx => by
    have := mem_of_unit _ ((unitsK R).inv_mem (hu x x)) (hp x hx)
    rwa [eu x x, inv_mul_cancel_left] at this
  have κ'p := GlobalTheory.Mum.TPos.tensor_pos R X κ κn κc κp W hW

  have Pp : ∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (P z : FractionRing R) = algebraMap R _ s := by
    intro z hz
    have hd : (∏ i, ∏ j, v (z i) (z j) ^ W i j) ∈ unitsK R :=
      prod_mem fun i _ => prod_mem fun j _ => zpow_mem (hv _ _) _
    have e2 : P z ^ 2 = (∏ i, ∏ j, v (z i) (z j) ^ W i j)⁻¹ * κ' z := by
      rw [eκ', eQP, mul_left_comm, inv_mul_cancel_left, pow_two]
    obtain ⟨s, hsm, es⟩ := mem_of_unit _ ((unitsK R).inv_mem hd) (κ'p z hz)
    rw [← e2, Units.val_pow_eq_pow_val] at es
    have hint : IsIntegral R ((P z : (FractionRing R)ˣ) : FractionRing R) :=
      IsIntegral.of_pow (by norm_num : 0 < 2) (es ▸ isIntegral_algebraMap)
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have ht2 : t ^ 2 = s := by
      apply IsFractionRing.injective R (FractionRing R)
      rw [map_pow, ht, es]
    exact ⟨t, (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem 2 (ht2 ▸ hsm), ht.symm⟩
  have Pn : ∀ z, P (-z) = P z := fun z => by
    apply Additive.ofMul.injective
    simp [eP]
  have Pc : ∀ x y w, P (x + y + w) * P x * P y * P w = P (x + y) * P (x + w) * P (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, eP, ← Finset.sum_add_distrib, ← smul_add, Pi.add_apply, map_add, LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => congrArg _ ?_
    abel
  have Pt := GlobalTheory.QuadTend.finite_not_mem_pow R (Fin r → X) P Pn Pc Pp
  have ea : ∀ z, ∃ v ∈ unitsK R, a' z = v * P z := fun z => by
    obtain ⟨w, hw, e⟩ := h' z
    refine ⟨w * ∏ i, ∏ j, u (z i) (z j) ^ W i j,
      mul_mem hw (prod_mem fun i _ => prod_mem fun j _ => zpow_mem (hu _ _) _), ?_⟩
    rw [e, _root_.mul_assoc]
    congr 1
    simp only [P, eu, mul_zpow, Finset.prod_mul_distrib]
  refine ⟨fun z hz => ?_, fun n => (Pt n).subset fun z hz hm => hz ?_⟩
  · obtain ⟨w, hw, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hw (Pp z hz)
  · obtain ⟨w, hw, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hw hm

end GlobalTheory.Mum.TensPolScal
