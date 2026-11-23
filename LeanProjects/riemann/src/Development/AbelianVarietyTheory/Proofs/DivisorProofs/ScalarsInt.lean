import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitsK
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
open GlobalTheory.UU GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit

noncomputable section

namespace GlobalTheory.MumInt

theorem bal_part {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (k : D.X → (FractionRing R)ˣ) (hk : PsiScal D ga k) {a a' : D.P.A ⟶ D.P.A} {h h' : D.X →+ D.X}
    (hE : EndData D a a' h h') (y w : D.X) :
    ∃ u ∈ unitsK R, k (h y + w) * k y * k (h' w) = u * (k (y + h' w) * k (h y) * k w) := by
  obtain ⟨ha, ha', hr, -, -, hb⟩ := hE
  obtain ⟨t, ht, t₀⟩ := exists_ros GlobalTheory.globalFns_holds D.P.isAb D.P.isLB a a' hr
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨J, hJ, iJ⟩ := GlobalTheory.Mum.TensPos.exists_int D.P z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hψ : ∀ χ, val (D.psi χ) (𝟙 _) z J = E (k χ) * val (ga χ) (toUnit (TK R)).left z J := fun χ =>
    Units.ext (((hk χ).2 (TK R) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have mg : ∀ χ, val (ga χ) (toUnit (TK R)).left z J ∈ unitsS z := fun χ => GlobalTheory.Mum.TensPos.val_mem D.P z iJ _ _ _
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hb t ht t₀ y w) (𝟙 _))
  have ep : 𝟙 _ ≫ D.pt2 y w = (toUnit (TK R)).left ≫ (lift (D.c y) (D.c w)).left := by
    rw [Category.id_comp, ← Over.comp_left, comp_lift]; rfl
  have mt : val t (𝟙 _ ≫ D.pt2 y w) z J ∈ unitsS z := by
    rw [ep, ← val_pull hJ]
    refine GlobalTheory.Mum.TensPol.val_mem z iJ _ (fun i => ?_) _ _
    have hφ : rosatiφ D.P.A a a' i ≫ D.P.A.hom = (D.P.A ⊗ D.P.A).hom := by
      fin_cases i <;> exact Over.w _
    rw [Category.assoc, hφ]
    exact Over.w _
  rw [vτ, vτ] at e
  simp only [hψ] at e
  generalize val t (𝟙 _ ≫ D.pt2 y w) z J = v at e mt
  refine ⟨k (h y + w) * k y * k (h' w) * (k (y + h' w) * k (h y) * k w)⁻¹, GlobalTheory.Mum.TensPol.mem_unitsK z ?_,
    by rw [inv_mul_cancel_right]⟩
  have : E (k (h y + w) * k y * k (h' w) * (k (y + h' w) * k (h y) * k w)⁻¹) =
      val (ga (y + h' w)) (toUnit (TK R)).left z J * val (ga (h y)) (toUnit (TK R)).left z J *
        val (ga w) (toUnit (TK R)).left z J * (val (ga (h y + w)) (toUnit (TK R)).left z J *
        val (ga y) (toUnit (TK R)).left z J * val (ga (h' w)) (toUnit (TK R)).left z J * v)⁻¹ := by
    simp only [map_mul, map_inv]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  exact this ▸ mul_mem (mul_mem (mul_mem (mg _) (mg _)) (mg _))
    (inv_mem (mul_mem (mul_mem (mul_mem (mg _) (mg _)) (mg _)) mt))

theorem scalars_int {R : Type} [CommRing R] [IsDomain R] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (k : X → (FractionRing R)ˣ) (h h' : X →+ X) (N : ℕ)
    (hn : ∀ x, ∃ u ∈ unitsK R, k (-x) = u * k x)
    (hc : ∀ x y w, ∃ u ∈ unitsK R, k (x + y + w) * k x * k y * k w = u * (k (x + y) * k (x + w) * k (y + w)))
    (hi : ∀ x, x ≠ 0 → ∃ s : R, (k x : FractionRing R) = algebraMap R _ s)
    (hb : ∀ y w, ∃ u ∈ unitsK R, k (h y + w) * k y * k (h' w) = u * (k (y + h' w) * k (h y) * k w))
    (hP : ∀ (κ : X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 →
      (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) →
      (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) →
      (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) =
        algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) →
      ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y)) (y : X) :
    (∃ s : R, (k y : FractionRing R) = algebraMap R _ s) ∧
      ∃ ρ : R, ((k y ^ N * (k (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ ρ * k y := by
  obtain ⟨B, hB⟩ := exists_exact (unitsK R) k hn hc
  choose u hu eu using hB
  let κ : X → (FractionRing R)ˣ := fun x => (B x x).toMul
  have eκ : ∀ x, k x = u x * κ x := eu
  have κn : ∀ x, κ (-x) = κ x := fun x => by simp [κ]
  have κ0 : κ 0 = 1 := by simp [κ]
  have κc : ∀ x y w, κ (x + y + w) * κ x * κ y * κ w = κ (x + y) * κ (x + w) * κ (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [κ, ofMul_mul, ofMul_toMul, map_add, LinearMap.add_apply]
    abel
  have κi : ∀ x, ∃ s : R, (κ x : FractionRing R) = algebraMap R _ s := fun x => by
    by_cases hx : x = 0
    · exact ⟨1, by rw [hx, κ0, map_one, Units.val_one]⟩
    · obtain ⟨s, hs⟩ := hi x hx
      obtain ⟨s', -, e⟩ := mem_of_unit ⊤ ((unitsK R).inv_mem (hu x)) ⟨s, trivial, hs⟩
      rw [eκ x, inv_mul_cancel_left] at e
      exact ⟨s', e⟩
  have κb : ∀ y z, ∃ v : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) =
      algebraMap R _ (v : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R) := fun y z => by
    obtain ⟨v, hv, e⟩ := hb y z
    obtain ⟨v', ev'⟩ := mul_mem (mul_mem hv (mul_mem (mul_mem (hu (y + h' z)) (hu (h y))) (hu z)))
      (inv_mem (mul_mem (mul_mem (hu (h y + z)) (hu y)) (hu (h' z))))
    refine ⟨v', congrArg Units.val (?_ : _ = Units.map (algebraMap R (FractionRing R)).toMonoidHom v' * _)⟩
    rw [ev']
    simp only [eκ] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  obtain ⟨ρ, eρ⟩ := hP κ κn κ0 κc κi κb y
  obtain ⟨v, ev'⟩ := mul_mem (pow_mem (hu y) N) (inv_mem (mul_mem (hu y) (hu (h y))))
  refine ⟨?_, v * ρ, ?_⟩
  · obtain ⟨s, hs⟩ := κi y
    obtain ⟨s', -, e⟩ := mem_of_unit ⊤ (hu y) ⟨s, trivial, hs⟩
    exact ⟨s', eκ y ▸ e⟩
  · have e1 : algebraMap R (FractionRing R) v = ((u y ^ N * (u y * u (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) :=
      congrArg Units.val ev'
    rw [map_mul, e1, eκ y, eκ (h y), mul_pow]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, eρ]
    have := (u y).ne_zero
    have := (u (h y)).ne_zero
    have := (κ (h y)).ne_zero
    field_simp

theorem gs_scal {R : Type} [CommRing R] [IsDomain R] (z : (TK R).left) (r : R) :
    gs (𝟙 _) z ⊤ (scal (jK R) r) = ev z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  rw [gs_eq _ z ⊤ trivial]
  exact congrArg ((TK R).left.presheaf.germ ⊤ z trivial).hom nat.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∃ (r : D.toPre.X → R) (g : ∀ y : D.toPre.X, LB.Gen (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => (D.toPre.c y).left) (fun _ => -1))), (∀ y, (g y).IsGen) ∧ (∀ y, y ≠ 0 → r y ∈ maximalIdeal R) ∧ (∀ e : ℕ, {y | r y ∉ maximalIdeal R ^ e}.Finite) ∧ ∀ y (z : (TK R).left) (J), Good D.toPre.P.L z J → (val (D.toPre.psi y) (𝟙 _) z J ^ N * (val (D.toPre.psi (h y)) (𝟙 _) z J)⁻¹).val = gs (𝟙 _) z ⊤ (scal (jK R) (r y)) * (val (g y) (toUnit (TK R)).left z J ^ N * (val (g (h y)) (toUnit (TK R)).left z J)⁻¹).val := by
  intro R _ _ _ _ D a a' h h' hE N _ hP
  obtain ⟨ga, k, hk⟩ := exists_psiScal R D.toPre
  have key := scalars_int k h h' N
    (fun x => by
      obtain ⟨u, e⟩ := even_part D.toPre ga k hk D.psi_even x
      exact ⟨_, ⟨u, rfl⟩, Units.ext e⟩)
    (fun x y w => by
      obtain ⟨u, e⟩ := cub_part D.toPre ga k hk D.tau_bimult x y w
      exact ⟨_, ⟨u, rfl⟩, Units.ext e⟩)
    (fun x hx => by
      obtain ⟨s, -, e⟩ := (PsiScalIn.main_local D.toPre ga k hk x _).1 (D.psi_pos x hx)
      exact ⟨s, e.symm⟩)
    (bal_part D.toPre ga k hk hE) hP.2
  choose s hs using fun y => (key y).1
  choose ρ hρ using fun y => (key y).2
  have hm : ∀ y (I : Ideal R), D.toPre.PsiIn y I → ρ y * s y ∈ I := fun y I hy => by
    obtain ⟨t, ht, e⟩ := (PsiScalIn.main_local D.toPre ga k hk y _).1 hy
    obtain rfl : t = s y := IsFractionRing.injective R (FractionRing R) (e.trans (hs y))
    exact I.mul_mem_left _ ht
  refine ⟨fun y => ρ y * s y, ga, fun y => (hk y).1, fun y hy => hm y _ (D.psi_pos y hy),
    fun e => (D.psi_tendsto e).subset fun y hy hi => hy (hm y _ hi), fun y z J hJ => ?_⟩
  have hψ : ∀ χ, val (D.toPre.psi χ) (𝟙 _) z J =
      Units.map (ev z).toMonoidHom (k χ) * val (ga χ) (toUnit (TK R)).left z J := fun χ =>
    Units.ext (((hk χ).2 (TK R) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have e : algebraMap R (FractionRing R) (ρ y * s y) = (k y ^ N * (k (h y))⁻¹).val := by
    rw [hρ, map_mul, hs]
  rw [gs_scal, e, hψ, hψ]
  refine congrArg Units.val (?_ : _ = Units.map (ev z).toMonoidHom (k y ^ N * (k (h y))⁻¹) * _)
  rw [map_mul, map_pow, map_inv, mul_pow, mul_inv, _root_.mul_mul_mul_comm]

end GlobalTheory.MumInt
