import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEvenCubicalValuesNotMemMaximalIdealPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositiveStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInIffScalarMem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU

noncomputable section

namespace GlobalTheory.Mum.TensPos

theorem exists_bilin_lift {X A Q : Type} [AddCommGroup X] [Module.Free ℤ X] [AddCommGroup A] [AddCommGroup Q] (π : A →+ Q)
    (hπ : Function.Surjective π) (f : X → Q) (hn : ∀ a, f (-a) = f a)
    (hc : ∀ a a' b, f (a + a' + b) + f a + f a' + f b = f (a + a') + f (a + b) + f (a' + b)) :
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] A, ∀ x, π (B x x) = f x := by
  have h0 : f 0 = 0 := by
    have := hc 0 0 0
    simp only [add_zero] at this
    linear_combination (norm := abel) this
  have hadd : ∀ a a' b, QuadraticMap.polar f (a + a') b = QuadraticMap.polar f a b + QuadraticMap.polar f a' b := by
    intro a a' b
    simp only [QuadraticMap.polar]
    linear_combination (norm := abel) hc a a' b
  have hsm : ∀ (n : ℤ) a b, QuadraticMap.polar f (n • a) b = n • QuadraticMap.polar f a b := fun n a b =>
    map_zsmul (AddMonoidHom.mk' (fun a => QuadraticMap.polar f a b) (fun a a' => hadd a a' b)) n a
  have hxx : ∀ x, QuadraticMap.polar f x x = f x + f x := by
    intro x
    have := hsm (-1) x x
    rw [neg_one_zsmul, neg_one_zsmul, QuadraticMap.polar, neg_add_cancel, h0, hn] at this
    linear_combination (norm := abel) this
  have hq : ∀ (n : ℤ) x, f (n • x) = (n * n) • f x := by
    intro n x
    induction n using Int.induction_on with
    | zero => simp [h0]
    | succ n ih =>
      have := hsm n x x
      rw [hxx, QuadraticMap.polar, ih] at this
      rw [add_zsmul, one_zsmul]
      linear_combination (norm := module) this
    | pred n ih =>
      have := hsm (n : ℤ) x x
      rw [neg_zsmul, hn] at ih
      rw [hxx, QuadraticMap.polar, ih] at this
      rw [show (-(n : ℤ) - 1) = -((n : ℤ) + 1) by ring, neg_zsmul, hn, add_zsmul, one_zsmul]
      linear_combination (norm := module) this
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (QuadraticMap.ofPolar (R := ℤ) f hq hadd hsm)
  let b := Module.Free.chooseBasis ℤ X
  choose s hs using hπ
  let B' : X →ₗ[ℤ] X →ₗ[ℤ] A := b.constr ℤ fun i => b.constr ℤ fun j => s (B (b i) (b j))
  have e : B'.compr₂ π.toIntLinearMap = B := LinearMap.ext_basis b b fun i j => by
    simp [B', hs]
  refine ⟨B', fun x => ?_⟩
  have e1 := congrArg (fun C => C x x) e
  have e2 := congrArg (fun C => C x) hB
  exact e1.trans e2

theorem exists_exact {X G : Type} [AddCommGroup X] [Module.Free ℤ X] [CommGroup G] (H : Subgroup G) (a : X → G)
    (hn : ∀ x, ∃ u ∈ H, a (-x) = u * a x)
    (hc : ∀ x y w, ∃ u ∈ H, a (x + y + w) * a x * a y * a w = u * (a (x + y) * a (x + w) * a (y + w))) :
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] Additive G, ∀ x, ∃ u ∈ H, a x = u * (B x x).toMul := by
  have h1 : ∀ u ∈ H, (QuotientGroup.mk' H) u = 1 := fun u hu => (QuotientGroup.eq_one_iff u).2 hu
  obtain ⟨B, hB⟩ := exists_bilin_lift (X := X) (MonoidHom.toAdditive (QuotientGroup.mk' H)) (QuotientGroup.mk'_surjective H)
    (fun x => Additive.ofMul (QuotientGroup.mk' H (a x)))
    (fun x => by
      obtain ⟨u, hu, e⟩ := hn x
      simp only [e, map_mul, h1 u hu, _root_.one_mul])
    (fun x y w => by
      obtain ⟨u, hu, e⟩ := hc x y w
      have := congrArg (QuotientGroup.mk' H) e
      simp only [map_mul, h1 u hu, _root_.one_mul] at this
      exact congrArg Additive.ofMul this)
  refine ⟨B, fun x => ⟨a x * ((B x x).toMul)⁻¹, ?_, by rw [inv_mul_cancel_right]⟩⟩
  have : QuotientGroup.mk' H (B x x).toMul = QuotientGroup.mk' H (a x) := congrArg Additive.toMul (hB x)
  rw [← QuotientGroup.eq_one_iff]
  show QuotientGroup.mk' H _ = 1
  rw [map_mul, map_inv, this, mul_inv_cancel]

def unitsK (R : Type) [CommRing R] : Subgroup (FractionRing R)ˣ :=
  (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range

theorem mem_of_unit {R : Type} [CommRing R] (I : Ideal R) {u x : (FractionRing R)ˣ} (hu : u ∈ unitsK R)
    (hx : ∃ s ∈ I, (x : FractionRing R) = algebraMap R _ s) : ∃ s ∈ I, ((u * x : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s := by
  obtain ⟨v, rfl⟩ := hu
  obtain ⟨s, hs, e⟩ := hx
  exact ⟨v * s, I.mul_mem_left _ hs, by rw [Units.val_mul, e, map_mul]; rfl⟩

theorem scalars (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R]
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (a : X → (FractionRing R)ˣ)
    (hn : ∀ x, ∃ u ∈ unitsK R, a (-x) = u * a x)
    (hc : ∀ x y w, ∃ u ∈ unitsK R, a (x + y + w) * a x * a y * a w = u * (a (x + y) * a (x + w) * a (y + w)))
    (hp : ∀ x, x ≠ 0 → ∃ s ∈ maximalIdeal R, (a x : FractionRing R) = algebraMap R _ s)
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (hW : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef)
    (a' : (Fin r → X) → (FractionRing R)ˣ)
    (h' : ∀ z, ∃ u ∈ unitsK R, a' z = u * ∏ i, ∏ j, (a (z i + z j) * (a (z i))⁻¹ * (a (z j))⁻¹) ^ W i j) :
    (∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (a' z : FractionRing R) = algebraMap R _ s) ∧
      ∀ n : ℕ, {z | ¬ ∃ s ∈ maximalIdeal R ^ n, (a' z : FractionRing R) = algebraMap R _ s}.Finite := by
  obtain ⟨B, hB⟩ := exists_exact (unitsK R) a hn hc
  choose u hu eu using hB
  let κ : X → (FractionRing R)ˣ := fun x => (B x x).toMul
  let κ' : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (κ (z i + z j) * (κ (z i))⁻¹ * (κ (z j))⁻¹) ^ W i j
  have eκ' : ∀ z, Additive.ofMul (κ' z) = ∑ i, ∑ j, W i j • (B (z i) (z j) + B (z j) (z i)) := by
    intro z
    simp only [κ', κ, ofMul_prod, ofMul_zpow, ofMul_mul, ofMul_inv, ofMul_toMul, map_add, LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => congrArg _ ?_
    abel
  have κn : ∀ x, κ (-x) = κ x := fun x => by simp [κ]
  have κc : ∀ x y w, κ (x + y + w) * κ x * κ y * κ w = κ (x + y) * κ (x + w) * κ (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [κ, ofMul_mul, ofMul_toMul, map_add, LinearMap.add_apply]
    abel
  have κp : ∀ x, x ≠ 0 → ∃ s ∈ maximalIdeal R, (κ x : FractionRing R) = algebraMap R _ s := fun x hx => by
    have := mem_of_unit _ ((unitsK R).inv_mem (hu x)) (hp x hx)
    rwa [eu x, inv_mul_cancel_left] at this
  have κ'n : ∀ x, κ' (-x) = κ' x := fun x => by
    apply Additive.ofMul.injective
    simp [eκ']
  have κ'c : ∀ x y w, κ' (x + y + w) * κ' x * κ' y * κ' w = κ' (x + y) * κ' (x + w) * κ' (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, eκ', ← Finset.sum_add_distrib, ← smul_add, Pi.add_apply, map_add, LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => congrArg _ ?_
    abel
  have κ'p := GlobalTheory.T.even_cubical_tensor_posDef_form_positive R X κ κn κc κp W hW
  have κ't := GlobalTheory.T.finite_even_cubical_values_not_mem_maximalIdeal_pow R (Fin r → X) κ' κ'n κ'c κ'p
  have ea : ∀ z, ∃ v ∈ unitsK R, a' z = v * κ' z := fun z => by
    obtain ⟨v, hv, e⟩ := h' z
    refine ⟨v * ∏ i, ∏ j, (u (z i + z j) * (u (z i))⁻¹ * (u (z j))⁻¹) ^ W i j, mul_mem hv (prod_mem fun i _ => prod_mem fun j _ =>
      zpow_mem (mul_mem (mul_mem (hu _) (inv_mem (hu _))) (inv_mem (hu _))) _), ?_⟩
    rw [e, _root_.mul_assoc, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← mul_zpow, eu (z i + z j), eu (z i), eu (z j)]
    refine congrArg (· ^ W i j) (Additive.ofMul.injective ?_)
    simp only [κ, ofMul_mul, ofMul_inv]
    abel
  refine ⟨fun z hz => ?_, fun n => (κ't n).subset fun z hz hm => hz ?_⟩
  · obtain ⟨v, hv, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hv (κ'p z hz)
  · obtain ⟨v, hv, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hv hm

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

open GlobalTheory.PsiScalUnit

def unitsS (z : (TK R).left) : Subgroup ((TK R).left.presheaf.stalk z)ˣ := (unitsK R).map (Units.map (ev z).toMonoidHom)

theorem gm_mem (z : (TK R).left) {Y : Scheme.{0}} (p : Spec (CommRingCat.of R) ⟶ Y) (U : Y.Opens)
    (h : p (closedPoint R) ∈ U) (s : Γ(Y, U)ˣ) : gm (Y := (TK R).left) (jK R ≫ p) z U s ∈ unitsS z := by
  have hle : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ p ⁻¹ᵁ U := fun y _ =>
    (IsLocalRing.specializes_closedPoint y).mem_open (p ⁻¹ᵁ U).isOpen h
  obtain ⟨u, hu⟩ := ev_unit z (res hle (pullU p U s))
  refine ⟨_, ⟨u, rfl⟩, Units.ext (hu.symm.trans (congrArg Units.val ?_))⟩
  exact (gm_res _ _ hle trivial _).trans (gm_pull (jK R) p z U (hle trivial) _)

theorem exists_int (P : PolAV (Spec (CommRingCat.of R))) (z : (TK R).left) : ∃ J, Good P.L z J ∧
    ∀ p : Spec (CommRingCat.of R) ⟶ P.A.left, p ≫ P.A.hom = 𝟙 _ → p (closedPoint R) ∈ P.L.U (J (jK R ≫ p)) := by
  have : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ P.A.left => exists_chart P.isLB (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good P.L P.isLB (Z := (TK R).left) z
    (K := {p : Spec (CommRingCat.of R) ⟶ P.A.left // p ≫ P.A.hom = 𝟙 _}) (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) P.A.hom
      (a.2.trans b.2.symm) (jK R) h))
    (fun p => (IsLocalRing.specializes_closedPoint (jK R z)).mem_open (p.1 ⁻¹ᵁ P.L.U (pick p.1)).isOpen (hpk p.1))
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem val_mem (P : PolAV (Spec (CommRingCat.of R))) (z : (TK R).left) {J : ((TK R).left ⟶ P.A.left) → P.L.ι}
    (hJ : ∀ p : Spec (CommRingCat.of R) ⟶ P.A.left, p ≫ P.A.hom = 𝟙 _ → p (closedPoint R) ∈ P.L.U (J (jK R ≫ p)))
    (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A) (e : ℤ)
    (t : LB.Gen (LB.LinComb P.L (K := PUnit) (fun _ => c.left) (fun _ => e))) :
    val t (toUnit (TK R)).left z J ∈ unitsS z := by
  have := gm_mem z (𝟙 _) (LB.wchart P.L (fun _ : PUnit => c.left) (fun _ => J (jK R ≫ c.left)))
    (Set.mem_iInter.2 fun _ => hJ c.left (Over.w c)) (t.s (fun _ => J (jK R ≫ c.left)))
  rw [Category.comp_id] at this
  exact this

theorem scalar_tens {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} (T : Tens D D' W)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a)
    (ga' : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (K := PUnit) (fun _ => (D'.c χ).left) (fun _ => -1)))
    (a' : D'.X → (FractionRing R)ˣ) (h' : PsiScal D' ga' a') (y : D'.X) :
    ∃ u ∈ unitsK R, a' y = u * ∏ i, ∏ j, (a (T.xe y i + T.xe y j) * (a (T.xe y i))⁻¹ * (a (T.xe y j))⁻¹) ^ W i j := by
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨J, hJ, iJ⟩ := exists_int D.P z
  obtain ⟨J', hJ', iJ'⟩ := exists_int D'.P z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hE : Function.Injective E := Units.map_injective (ev_inj z)
  have hψ : ∀ χ, val (D.psi χ) (𝟙 _) z J = E (a χ) * val (ga χ) (toUnit (TK R)).left z J := fun χ =>
    Units.ext (((h χ).2 (TK R) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have hψ' : val (D'.psi y) (𝟙 _) z J' = E (a' y) * val (ga' y) (toUnit (TK R)).left z J' :=
    Units.ext (((h' y).2 (TK R) (𝟙 _) z J' hJ').trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (toUnit (TK R)).left z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
  have mρ : val D.rigK (𝟙 _) z J ∈ unitsS z := vρ ▸ val_mem D.P z iJ η[D.P.A] 1 D.rig
  have mg : ∀ χ, val (ga χ) (toUnit (TK R)).left z J ∈ unitsS z := fun χ => val_mem D.P z iJ _ _ _
  have mg' : val (ga' y) (toUnit (TK R)).left z J' ∈ unitsS z := val_mem D'.P z iJ' _ _ _
  have mτ : ∀ b c : D.X, ∃ u ∈ unitsS z, val (D.tau b c) (𝟙 _) z J = u * E (a (b + c) * (a b)⁻¹ * (a c)⁻¹) := fun b c => by
    refine ⟨_, mul_mem (mul_mem (mul_mem (mg (b + c)) (inv_mem (mg b))) (inv_mem (mg c))) (inv_mem mρ), ?_⟩
    rw [vτ, hψ, hψ, hψ, map_mul, map_mul, map_inv, map_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  choose u hu eu using mτ
  have e := T.psi y z J J' hJ hJ'
  have hφ : ∀ k, tensφ T.pr k ≫ D.P.A.hom = D'.P.A.hom := by
    rintro ⟨⟨i, j⟩, k⟩
    fin_cases k <;> exact Over.w _
  have mw : gm (D'.xK y) z _ (T.w.s (fun k => J (D'.xK y ≫ tensφ T.pr k), J' (D'.xK y))) ∈ unitsS z := by
    refine gm_mem z (D'.c y).left
      (LB.wchart D.P.L (tensφ T.pr) (fun k => J (D'.xK y ≫ tensφ T.pr k)) ⊓ D'.P.L.U (J' (D'.xK y)))
      ⟨Set.mem_iInter.2 fun k => ?_, iJ' _ (Over.w _)⟩ _
    have := iJ ((D'.c y).left ≫ tensφ T.pr k) (by rw [Category.assoc, hφ]; exact Over.w _)
    rw [← Category.assoc] at this
    exact this
  rw [hψ'] at e
  simp only [eu, mul_zpow, Finset.prod_mul_distrib] at e
  obtain ⟨v, hv, ev'⟩ := mul_mem (mul_mem (inv_mem mg') mw)
    (prod_mem fun i (_ : i ∈ Finset.univ) => prod_mem fun j (_ : j ∈ Finset.univ) => zpow_mem (hu (T.xe y i) (T.xe y j)) (W i j))
  refine ⟨v, hv, hE ?_⟩
  rw [map_mul, map_prod]
  simp only [map_prod, map_zpow]
  rw [show E v = _ from ev', eq_mul_inv_of_mul_eq e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem psi_pos_tendsto : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Tens D.toPre D' W → (∀ χ : D'.X, χ ≠ 0 → D'.PsiIn χ (maximalIdeal R)) ∧ ∀ n : ℕ, {χ : D'.X | ¬ D'.PsiIn χ (maximalIdeal R ^ n)}.Finite := by
  intro R _ _ _ hR D D' r W hW T
  obtain ⟨_, -, _, -⟩ := hR
  obtain ⟨ga, a, h⟩ := exists_psiScal R D.toPre
  obtain ⟨ga', a', h'⟩ := exists_psiScal R D'
  obtain ⟨hp, ht⟩ := scalars R D.toPre.X a
    (fun x => by
      obtain ⟨u, e⟩ := even_part D.toPre ga a h D.psi_even x
      exact ⟨_, ⟨u, rfl⟩, Units.ext e⟩)
    (fun x y w => by
      obtain ⟨u, e⟩ := cub_part D.toPre ga a h D.tau_bimult x y w
      exact ⟨_, ⟨u, rfl⟩, Units.ext e⟩)
    (fun x hx => by
      obtain ⟨s, hs, e⟩ := (PsiScalIn.main_local D.toPre ga a h x _).1 (D.psi_pos x hx)
      exact ⟨s, hs, e.symm⟩)
    W hW (fun z => a' (T.xe.symm z))
    (fun z => by simpa only [AddEquiv.apply_symm_apply] using scalar_tens T ga a h ga' a' h' (T.xe.symm z))
  refine ⟨fun χ hχ => ?_, fun n => ((ht n).preimage T.xe.injective.injOn).subset fun χ hχ hm => hχ ?_⟩
  · obtain ⟨s, hs, e⟩ := hp (T.xe χ) (fun h0 => hχ (T.xe.map_eq_zero_iff.1 h0))
    rw [AddEquiv.symm_apply_apply] at e
    exact (PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩
  · obtain ⟨s, hs, e⟩ := hm
    rw [AddEquiv.symm_apply_apply] at e
    exact (PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩

end GlobalTheory.Mum.TensPos
