import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteDimensionalField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevQuot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem over_of_fix (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3) {l₀ l₁ : Level H} {X₀ : Moduli D l₀}
    {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X} {ν : SABMap X₁.univ.t X₀.univ.t r} (hA : l₀.A = 1)
    (hc : LevComp X₁.univ X₀.univ r ν) {f : X₁.X ⟶ X₁.X} (m : SABMap X₁.univ.t X₁.univ.t f)
    (hm : ∀ a, (X₁.univ.eta a).left ≫ m.φ = f ≫ (X₁.univ.eta a).left) (hs : (f ≫ r) ≫ X₀.s = r ≫ X₀.s) :
    f ≫ r = r ∧ m.φ ≫ ν.φ = ν.φ := by
  obtain ⟨n, hn⟩ := LevelCover.sab_comp m ν rfl
  rw [← hn]
  refine LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ X₀ _ _ _ _ X₁.univ _ _ n ν (isReduced_moduli X₁) hs
    ⟨fun a => ?_, fun a => ?_⟩ hc
  · rw [hn, ← Category.assoc, LevelCover.sec_pow m _ _ (hm a), Category.assoc, hc.1, Category.assoc]
  · have e : X₁.univ.etaA a ^ (l₁.A / l₀.A) = X₁.univ.eta 0 ^ 0 := by
      rw [hA, Nat.div_one, pow_zero, ← Moduli.LevelAction.map_nsmul_of_add X₁.univ.etaA_add, X₁.univ.etaA_ker]
    rw [hn, Category.assoc, ← hc.2, e, ← Category.assoc, LevelCover.sec_pow m _ _ (hm 0), Category.assoc]

theorem exists_twist_of_fibre (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3) (hN : ToroidalLevelCompatibility (H := H) (D := D))
    {l₀ l₁ : Level H} {X₀ : Moduli D l₀} {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X} {ν : SABMap X₁.univ.t X₀.univ.t r}
    {j : KA l₀ →+* KA l₁} (hd : l₀.Dvd l₁) (hM : l₁.M = l₀.M) (hMb : l₁.Mb = l₀.Mb)
    (hj : IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom j) (hr : r ≫ X₀.s = X₁.s ≫ spMap j)
    (hc : LevComp X₁.univ X₀.univ r ν) {k : Type} [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X₁.X)
    (h₁ : y ≫ r = y' ≫ r) (h₂ : y ≫ X₁.s = y' ≫ X₁.s) :
    ∃ (ρ : X₁.X ≅ X₁.X) (m : SABMap X₁.univ.t X₁.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La),
      SemiTwist X₁ ρ.hom m.φ g (RingHom.id _) ∧ y' = y ≫ ρ.hom := by
  let c := LevelExist.minCoeff l₁
  have hM' : 0 < l₁.M' := LevelExist.M'_pos l₁
  have hz : ∀ a, a ∣ l₁.M' → zeta a ∈ c.F := fun a ha => by
    rw [LevelCover.zeta_dvd hM' ha]
    exact pow_mem c.zeta_mem _
  have hle : KA l₀ ≤ c.F := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x (rfl | rfl)
    · exact c.le (baseKA l₁).ρ.2
    · exact hz _ (hd.2.2.trans (Nat.dvd_lcm_right _ _))
  let c₀ : Coeff l₀ := ⟨c.F, c.fin, c.conj, hz _ (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _))
    (hd.2.2.trans (Nat.dvd_lcm_right _ _))), hle⟩
  obtain ⟨r', j', ν', hj', hr', e₁, e₂, -, hF⟩ := hN l₀ l₁ X₀ X₁ hd
  obtain rfl : j = j' := RingHom.ext fun x => Subtype.ext ((hj x).trans (hj' x).symm)
  obtain rfl : r = r' := (LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ X₀ _ _ _ _ X₁.univ _ _ ν ν'
    (isReduced_moduli X₁) (hr.trans hr'.symm) hc ⟨e₁, e₂⟩).1
  obtain ⟨rF, a₁, a₂, -, -, -, htr⟩ := hF c₀ c rfl
  obtain ⟨β, hβ⟩ := LevCover.exists_spMap (y ≫ X₁.s)
  obtain ⟨θ, hθ⟩ : ∃ θ : c.F →+* k, θ.comp (IntermediateField.inclusion c.le).toRingHom = β := by
    letI : Algebra (KA l₁) k := β.toAlgebra
    letI : Algebra (KA l₁) c.F := (IntermediateField.inclusion c.le).toRingHom.toAlgebra
    haveI := c.fin
    haveI : IsScalarTower ℚ (KA l₁) c.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : Algebra.IsAlgebraic (KA l₁) c.F := Algebra.IsAlgebraic.tower_top (K := ℚ) (KA l₁)
    exact ⟨(IsAlgClosed.lift (R := KA l₁) (S := c.F) (M := k)).toRingHom,
      (IsAlgClosed.lift (R := KA l₁) (S := c.F) (M := k)).comp_algebraMap⟩
  have w : y ≫ X₁.s = spMap θ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [LevCover.spMap_comp'', hθ, hβ]
  obtain ⟨⟨g, ρ, hg, ⟨hs, m, b₁, b₂⟩, -, hy⟩, -⟩ := htr k (pullback.lift y (spMap θ) w)
    (pullback.lift y' (spMap θ) (h₂ ▸ w)) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, a₁, pullback.lift_fst_assoc, pullback.lift_fst_assoc, h₁]
      · rw [Category.assoc, Category.assoc, a₂, pullback.lift_snd_assoc, pullback.lift_snd_assoc])
  rw [pullback.lift_fst, pullback.lift_fst_assoc] at hy
  refine ⟨ρ, m, g.f l₁.A, ⟨by rw [hs, LevelCover.spMap_id', Category.comp_id], fun a => ?_, b₂⟩, hy⟩
  rw [← b₁, Moduli.LevelAction.eta_congr X₁.univ (x := g.f l₁.M a) (y := a) (by rw [hM, hMb]; exact hg.2.1 a)]

theorem exists_finite_invariant {l : Level H} (Xo : Moduli D l) :
    ∃ (κ : Type) (_ : Finite κ) (q : (D.La →ₗ[𝓞 E] D.La) → κ), ∀ g g', q g = q g' →
      ∀ x, Xo.univ.etaA (g x) = Xo.univ.etaA (g' x) := by
  obtain ⟨_, _⟩ := LevCover.datum_free D
  obtain ⟨κ, _, q, hq⟩ := LevCover.exists_finite_mod D.La l.A_pos
  haveI : Nonempty D.La := ⟨0⟩
  refine ⟨κ → κ, inferInstance, fun g c => q (g (Function.invFun q c)), fun g g' h x => ?_⟩
  obtain ⟨c, hc⟩ := hq _ _ (Function.invFun_eq (f := q) ⟨x, rfl⟩)
  obtain ⟨c', hc'⟩ := hq _ _ (congrFun h (q x))
  generalize Function.invFun q (q x) = y at hc hc'
  subst hc
  simp only [map_add, map_nsmul, hc', Xo.univ.etaA_add, Xo.univ.etaA_ker, _root_.mul_one]

section

variable {l₀ l₁ : Level H} {X₀ : Moduli D l₀} {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X}

def twistMonoid (τ : autOver r →* Aut X₁.univ.t.G.left) : Submonoid (autOver r) :=
  { carrier := {ω | ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧
      SemiTwist X₁ ω.1.hom (τ ω).hom g σ.toRingHom}
    mul_mem' := by
      rintro a b ⟨g, σ, h₁, h₂⟩ ⟨g', σ', h₁', h₂'⟩
      refine ⟨g' ∘ₗ g, σ.trans σ', by rw [RingEquiv.trans_apply, h₁, h₁'], ?_⟩
      have e₁ : (a * b).1.hom = b.1.hom ≫ a.1.hom := rfl
      have e₂ : (τ (a * b)).hom = (τ b).hom ≫ (τ a).hom := by rw [map_mul]; rfl
      have e₃ : (σ.trans σ').toRingHom = σ'.toRingHom.comp σ.toRingHom := RingHom.ext fun _ => rfl
      rw [e₁, e₂, e₃, LinearMap.coe_comp]
      exact h₂'.comp h₂
    one_mem' := by
      refine ⟨LinearMap.id, RingEquiv.refl _, rfl, ?_⟩
      rw [map_one]
      exact ⟨(Category.id_comp _).trans ((Category.comp_id _).symm.trans
          (congrArg _ (LevelCover.spMap_id' _).symm)),
        fun a => (Category.comp_id _).trans (Category.id_comp _).symm,
        fun a => (Category.comp_id _).trans (Category.id_comp _).symm⟩ }

theorem inv_comp_square {X P : Scheme.{0}} (a : X ≅ X) (t : P ≅ P) {b : X ⟶ X} {u : P ⟶ P} {x y : X ⟶ P}
    (p₁ : y ≫ t.hom = a.hom ≫ x) (p₂ : y ≫ u = b ≫ x) : x ≫ t.inv ≫ u = (a.inv ≫ b) ≫ x := by
  rw [Category.assoc, ← p₂, Iso.eq_inv_comp, ← Category.assoc, ← p₁, Category.assoc, Iso.hom_inv_id_assoc]

theorem finite_twistMonoid (τ : autOver r →* Aut X₁.univ.t.G.left)
    (mu : ∀ ω : autOver r, SABMap X₁.univ.t X₁.univ.t ω.1.hom) (hmu : ∀ ω, (mu ω).φ = (τ ω).hom) :
    Finite (twistMonoid τ) := by
  obtain ⟨κ, _, q, hq⟩ := exists_finite_invariant X₁
  haveI := finite_fieldAut l₁
  have hch : ∀ ω : twistMonoid τ, ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁),
      SemiTwist X₁ ω.1.1.hom (τ ω.1).hom g σ.toRingHom := fun ω => by
    obtain ⟨g, σ, -, h⟩ := ω.2
    exact ⟨g, σ, h⟩
  choose g σ hg using hch
  refine Finite.of_injective (fun ω => (q (g ω), σ ω)) fun a b hab => ?_
  have h₁ := hq _ _ (congrArg Prod.fst hab)
  have h₂ : σ a = σ b := congrArg Prod.snd hab
  have e₀ : (b.1 * a.1⁻¹).1.hom = a.1.1.inv ≫ b.1.1.hom := rfl
  have e₁ : (τ (b.1 * a.1⁻¹)).hom = (τ a.1).inv ≫ (τ b.1).hom := by rw [map_mul, map_inv]; rfl
  have key : ∀ {x y : X₁.X ⟶ X₁.univ.t.G.left}, y ≫ (τ a.1).hom = a.1.1.hom ≫ x →
      y ≫ (τ b.1).hom = b.1.1.hom ≫ x → x ≫ (mu (b.1 * a.1⁻¹)).φ = (b.1 * a.1⁻¹).1.hom ≫ x := by
    intro x y p₁ p₂
    rw [hmu, e₀, e₁]
    exact inv_comp_square (a.1.1 : X₁.X ≅ X₁.X) (τ a.1) p₁ p₂
  have hid : (b.1 * a.1⁻¹).1.hom = 𝟙 _ :=
    SemiTwist.eq_id (g := id) (σ := RingHom.id _) (mu (b.1 * a.1⁻¹)) ⟨by
      rw [e₀, Category.assoc, (hg b).1, ← h₂, ← (hg a).1, LevelCover.spMap_id', Category.comp_id]
      exact Iso.inv_hom_id_assoc (a.1.1 : X₁.X ≅ X₁.X) _,
      fun x => key ((hg a).2.1 x) ((hg b).2.1 x),
      fun x => key ((hg a).2.2 x) (h₁ x ▸ (hg b).2.2 x)⟩ rfl fun _ => rfl
  have : b.1 * a.1⁻¹ = 1 := Subtype.ext (Iso.ext hid)
  exact Subtype.ext (mul_inv_eq_one.1 this).symm

theorem exists_mem_twistMonoid (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3)
    {ν : SABMap X₁.univ.t X₀.univ.t r} {k : KA l₀ →+* KA l₁} (hA : l₀.A = 1)
    (hk : IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k) (hr : r ≫ X₀.s = X₁.s ≫ spMap k)
    (hc : LevComp X₁.univ X₀.univ r ν) (τ : autOver r →* Aut X₁.univ.t.G.left)
    (hτ : ∀ ω, (τ ω).hom ≫ ν.φ = ν.φ ∧ (τ ω).hom ≫ X₁.univ.t.G.hom = X₁.univ.t.G.hom ≫ ω.1.hom)
    (ρ : X₁.X ≅ X₁.X) (m : SABMap X₁.univ.t X₁.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁)
    (h₁ : σ (baseKA l₁).ρ = (baseKA l₁).ρ) (h₂ : SemiTwist X₁ ρ.hom m.φ g σ.toRingHom) :
    ∃ ω ∈ twistMonoid τ, ω.1.hom = ρ.hom := by
  have hkρ : k (baseKA l₀).ρ = (baseKA l₁).ρ := Subtype.ext (hk _)
  have hz : (baseKA l₀).ζ = 1 := by
    have := (baseKA l₀).ζ_prim.pow_eq_one
    rwa [hA, pow_one] at this
  have hσ : σ.toRingHom.comp k = k := field_hom_ext l₀ _ _ (by rw [RingHom.comp_apply, hkρ]; exact h₁)
    (by rw [hz, map_one, map_one])
  obtain ⟨o₁, o₂⟩ := over_of_fix hL hL2 hL3 hA hc m h₂.2.1 (by
    rw [Category.assoc, hr, ← Category.assoc, h₂.1, Category.assoc, LevCover.spMap_comp'', hσ])
  have e : m.φ = (τ ⟨ρ, o₁⟩).hom :=
    ν.cart.1.hom_ext (o₂.trans (hτ _).1.symm) (m.cart.1.w.trans (hτ ⟨ρ, o₁⟩).2.symm)
  exact ⟨⟨ρ, o₁⟩, ⟨g, σ, h₁, e ▸ h₂⟩, rfl⟩

end

theorem exists_level_quotient : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (k : KA l₀ →+* KA l₁), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k → r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k → LevComp (Xo l₁).univ (Xo l₀).univ r ν → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* Aut (Xo l₁).X) (τ : Γ →* Aut (Xo l₁).univ.t.G.left) (mu : ∀ g, SABMap (Xo l₁).univ.t (Xo l₁).univ.t (ρ g).hom), Function.Injective ρ ∧ (IsAffineHom r ∧ (∀ g, (ρ g).hom ≫ r = r) ∧ ∀ V : (Xo l₀).X.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ((Xo l₁).X, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) ∧ ∀ ω, (mu ω).φ = (τ ω).hom ∧ (τ ω).hom ≫ ν.φ = ν.φ ∧ (∀ x, ((Xo l₁).univ.eta x).left ≫ (τ ω).hom = (ρ ω).hom ≫ ((Xo l₁).univ.eta x).left) ∧ ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧ (ρ ω).hom ≫ (Xo l₁).s = (Xo l₁).s ≫ spMap σ.toRingHom ∧ ∀ x, ((Xo l₁).univ.etaA (g x)).left ≫ (τ ω).hom = (ρ ω).hom ≫ ((Xo l₁).univ.etaA x).left := by
  intro hL hL2 hL3 E _ _ _ H D Xo hpq hN l₀ l₁ r ν k hA hM hMb hk hr hc
  have hd : l₀.Dvd l₁ := ⟨hM ▸ dvd_rfl, hMb.le, hA ▸ one_dvd _⟩
  obtain ⟨hfin, het, hsur⟩ : IsFinite r ∧ Etale r ∧ Surjective r := by
    obtain ⟨k', r', ν', hr', hk', hc', -, -, -, h⟩ := LevelMap.exists_levelMap E H D Xo hN l₀ l₁ hd
    obtain rfl : k = k' := RingHom.ext fun x => Subtype.ext ((hk x).trans (hk' x).symm)
    obtain rfl : r = r' := (LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ _ _ _ _ _ (Xo l₁).univ _ _ ν ν'
      (isReduced_moduli _) (hr.trans hr'.symm) hc hc').1
    exact h
  obtain ⟨τ, hτ⟩ := exists_liftAut ν.cart.1
  have hmu : ∀ ω : autOver r, ∃ m : SABMap (Xo l₁).univ.t (Xo l₁).univ.t ω.1.hom, m.φ = (τ ω).hom := fun ω => by
    obtain ⟨m, hm⟩ := LevelCover.sab_cancel ν ν ω.1.hom ω.2
    exact ⟨m, ν.cart.1.hom_ext (hm.trans (hτ ω).1.symm) (m.cart.1.w.trans (hτ ω).2.symm)⟩
  choose mu hmu using hmu
  let S := twistMonoid τ
  have hS := exists_mem_twistMonoid hL hL2 hL3 hA hk hr hc τ hτ
  haveI : Finite S := finite_twistMonoid τ mu hmu
  obtain ⟨T, hT⟩ := exists_subgroup_of_finite S
  refine ⟨T, inferInstance, Finite.of_injective (fun t : T => (⟨t.1, (hT _).1 t.2⟩ : S))
      fun a b h => Subtype.ext (congrArg (fun s : S => s.1) h),
    (autOver r).subtype.comp T.subtype, τ.comp T.subtype, fun t => mu t.1,
    Subtype.val_injective.comp Subtype.val_injective, ⟨inferInstance, fun t => t.1.2, ?_⟩, fun t => ?_⟩
  · refine invariant_descends r (fun t : T => t.1.1.hom) (fun t => t.1.2) fun F _ _ y y' hy => ?_
    obtain ⟨β, hβ⟩ := LevCover.exists_spMap (y ≫ (Xo l₁).s)
    obtain ⟨β', hβ'⟩ := LevCover.exists_spMap (y' ≫ (Xo l₁).s)
    have hkρ : k (baseKA l₀).ρ = (baseKA l₁).ρ := Subtype.ext (hk _)
    have hb : β.comp k = β'.comp k := LevCover.spMap_inj' (by
      rw [← LevCover.spMap_comp'', ← LevCover.spMap_comp'', ← hβ, ← hβ', Category.assoc, Category.assoc, ← hr,
        ← Category.assoc, hy, Category.assoc])
    obtain ⟨σ, h₁, h₂⟩ := exists_fieldAut l₁ β β' (hkρ ▸ DFunLike.congr_fun hb (baseKA l₀).ρ)
    obtain ⟨ρ, m, g, h₃⟩ := exists_semiTwist_iso hpq l₀ hA hM hMb (Xo l₁) σ h₁
    obtain ⟨a, ha, ea⟩ := hS ρ m g σ h₁ h₃
    obtain ⟨ρ', m', g', h₄, h₅⟩ := exists_twist_of_fibre hL hL2 hL3 hN hd hM hMb hk hr hc (y ≫ ρ.hom) y'
      (by rw [Category.assoc, ← ea, show a.1.hom ≫ r = r from a.2, hy])
      (by rw [Category.assoc, h₃.1, ← Category.assoc, hβ, hβ', LevCover.spMap_comp'', h₂])
    obtain ⟨b, hb', eb⟩ := hS ρ' m' g' (RingEquiv.refl _) rfl h₄
    refine ⟨⟨b * a, (hT _).2 (S.mul_mem hb' ha)⟩, ?_⟩
    rw [h₅, Category.assoc, ← ea, ← eb]
    rfl
  · obtain ⟨g, σ, h₁, h₂⟩ := (hT _).1 t.2
    exact ⟨hmu _, (hτ _).1, h₂.2.1, g, σ, h₁, h₂.1, h₂.2.2⟩

end GlobalTheory.LevQuot
