import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaPowFixesOfCommutativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InertiaTate

theorem iterate_map_mul' {M : Type} [CommGroup M] (φ : M →* M) (j : ℕ) (a b : M) :
    (⇑φ)^[j] (a * b) = (⇑φ)^[j] a * (⇑φ)^[j] b := by
  induction j generalizing a b with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_mul, ih]

theorem pow_fix_of_fix {M : Type} [CommGroup M] (φ : M →* M) (l : ℕ)
    (h : ∀ x : M, x ^ l = 1 → φ x = x) :
    ∀ (k : ℕ) (x : M), x ^ l ^ (k + 1) = 1 → (⇑φ)^[l ^ k] x = x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [pow_zero, Function.iterate_one]
    exact h x (by simpa using hx)
  | succ k ih =>
    intro x hx
    let ψ : M →* M := MonoidHom.mk' ((⇑φ)^[l ^ k]) (iterate_map_mul' φ _)
    have hψ : ∀ y, ψ y = (⇑φ)^[l ^ k] y := fun _ => rfl
    have ih' : ∀ y : M, y ^ l ^ (k + 1) = 1 → ψ y = y := fun y hy => by rw [hψ]; exact ih y hy
    have hxl : ψ (x ^ l) = x ^ l := ih' _ (by rw [← pow_mul, ← pow_succ', hx])
    obtain ⟨d, hd⟩ : ∃ d : M, d = ψ x * x⁻¹ := ⟨_, rfl⟩
    have hψx : ψ x = x * d := by rw [hd, mul_comm (ψ x), mul_inv_cancel_left]
    have hdl : d ^ l = 1 := by
      rw [hd, mul_pow, inv_pow, ← map_pow, hxl, mul_inv_cancel]
    have hdψ : ψ d = d := ih' d (by rw [pow_succ', pow_mul, hdl, one_pow])
    have hit : ∀ j : ℕ, (⇑ψ)^[j] x = x * d ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        rw [Function.iterate_succ_apply', ihj, map_mul, map_pow, hdψ, hψx, _root_.mul_assoc, ← pow_succ']
    have e : (⇑φ)^[l ^ (k + 1)] x = (⇑ψ)^[l] x := by
      rw [pow_succ, Function.iterate_mul]
      rfl
    rw [e, hit, hdl, _root_.mul_one]

theorem mem_of_pow_mem_of_coprime {G : Type} [Group G] (H : Subgroup G) (g : G) {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : g ^ m ∈ H) (hn : g ^ n ∈ H) : g ∈ H := by
  have e : ((Nat.gcd m n : ℕ) : ℤ) = m * Nat.gcdA m n + n * Nat.gcdB m n := Nat.gcd_eq_gcd_ab m n
  rw [hmn.gcd_eq_one, Nat.cast_one] at e
  have : g = (g ^ m) ^ Nat.gcdA m n * (g ^ n) ^ Nat.gcdB m n := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← e, zpow_one]
  rw [this]
  exact H.mul_mem (H.zpow_mem hm _) (H.zpow_mem hn _)

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]

def stab (x : ptOver K Ω ⟶ A) : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {σ | specAut σ ≫ x = x}
  one_mem' := by
    change specAut 1 ≫ x = x
    rw [specAut_one, Category.id_comp]
  mul_mem' := by
    intro a b ha hb
    change specAut (a * b) ≫ x = x
    change specAut a ≫ x = x at ha
    change specAut b ≫ x = x at hb
    rw [specAut_mul, Category.assoc, hb, ha]
  inv_mem' := by
    intro a ha
    change specAut a ≫ x = x at ha
    change specAut a⁻¹ ≫ x = x
    conv_lhs => rw [← ha]
    rw [← Category.assoc, ← specAut_mul, inv_mul_cancel, specAut_one, Category.id_comp]

theorem mem_stab_iff (x : ptOver K Ω ⟶ A) (σ : Ω ≃ₐ[K] Ω) : σ ∈ stab A x ↔ galPts A σ x = x := Iff.rfl

theorem galPts_pow (σ : Ω ≃ₐ[K] Ω) (j : ℕ) (x : ptOver K Ω ⟶ A) :
    galPts A (σ ^ j) x = (⇑(galPts A σ))^[j] x := by
  induction j generalizing x with
  | zero =>
    change specAut (σ ^ 0) ≫ x = x
    rw [pow_zero, specAut_one, Category.id_comp]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← ih]
    change specAut (σ ^ (j + 1)) ≫ x = specAut σ ≫ (specAut (σ ^ j) ≫ x)
    rw [pow_succ', specAut_mul, Category.assoc]

theorem exists_field_of_point [Algebra.IsAlgebraic K Ω] [LocallyOfFiniteType A.hom] (x : ptOver K Ω ⟶ A) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ stab A x ↔ σ ∈ E.fixingSubgroup := by
  obtain ⟨E, hE1, -, hE3⟩ := GlobalTheory.SS.exists_fieldOfValues A.left Ω x.left
  obtain ⟨L, hL, hLE⟩ := hE3 K A.hom inferInstance (Over.w x) inferInstance
  refine ⟨L, hL, fun σ => ?_⟩
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [← Spec.map_id]
    congr 1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have h1 : σ ∈ stab A x ↔ spMap (σ : Ω →+* Ω) ≫ x.left = spMap (RingHom.id Ω) ≫ x.left := by
    rw [hid, Category.id_comp]
    constructor
    · intro h
      exact congrArg CommaMorphism.left h
    · intro h
      exact Over.OverMorphism.ext h
  rw [h1, hE1]
  constructor
  · intro h c hc
    exact h c (by rw [← hLE]; exact hc)
  · intro h c hc
    exact h c (by rw [← hLE] at hc; exact hc)

end GlobalTheory.InertiaTate

namespace GlobalTheory.InertiaTate

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]

theorem exists_galois_field_of_finite [IsGalois K Ω] [LocallyOfFiniteType A.hom] (S : Set (ptOver K Ω ⟶ A))
    (hS : S.Finite) (hst : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ S, galPts A σ x ∈ S) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ L.fixingSubgroup ↔ ∀ x ∈ S, σ ∈ stab A x := by
  choose E hE hEs using fun x : S => exists_field_of_point A x.1
  haveI : Finite S := hS.to_subtype
  haveI := hE
  have key : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ (⨆ x : S, E x).fixingSubgroup ↔ ∀ x ∈ S, σ ∈ stab A x := by
    intro σ
    rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, iSup_le_iff]
    constructor
    · intro h x hx
      exact (hEs ⟨x, hx⟩ σ).2 (Subgroup.zpowers_le.1 ((IntermediateField.le_iff_le _ _).1 (h ⟨x, hx⟩)))
    · intro h x
      exact (IntermediateField.le_iff_le _ _).2 (Subgroup.zpowers_le.2 ((hEs x σ).1 (h x.1 x.2)))
  refine ⟨⨆ x : S, E x, inferInstance, ?_, key⟩
  refine (InfiniteGalois.normal_iff_isGalois _).1 ⟨fun n hn g => ?_⟩
  rw [key] at hn ⊢
  intro x hx
  have h1 := hn _ (hst g⁻¹ x hx)
  change specAut n ≫ (specAut g⁻¹ ≫ x) = specAut g⁻¹ ≫ x at h1
  change specAut (g * n * g⁻¹) ≫ x = x
  rw [specAut_mul, specAut_mul, Category.assoc, Category.assoc, h1, ← Category.assoc, ← specAut_mul,
    mul_inv_cancel, specAut_one, Category.id_comp]

theorem aut_comm_of_galTate_comm (l : ℕ) [Fact l.Prime]
    (hc : ∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ)
    (L : IntermediateField K Ω) [Normal K L] [Normal K Ω] (n : ℕ)
    (hL : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ L.fixingSubgroup ↔
      ∀ x ∈ Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n), σ ∈ stab A x) :
    ∀ α β : L ≃ₐ[K] L, α * β = β * α := by
  intro α β
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω α
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω β
  rw [← map_mul, ← map_mul, MonoidHom.eq_iff, IntermediateField.restrictNormalHom_ker, hL]
  rintro _ ⟨t, rfl⟩
  have h1 : galTate A l ((τ * σ)⁻¹ * (σ * τ)) = 1 := by
    rw [map_mul, map_mul (galTate A l) σ τ, hc σ τ, ← map_mul (galTate A l) τ σ, ← map_mul, inv_mul_cancel,
      map_one]
  exact (congrArg (fun f => Tate.lev (f t) n) h1 :)

end GlobalTheory.InertiaTate

open GlobalTheory.InertiaTate in

theorem GlobalTheory.InertiaTate.exists_exponent_inertia_galTate : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) → ∃ E : ℕ, 0 < E ∧ ∀ σ ∈ inertia K V, galTate A l σ ^ E = 1 := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA l _ hl hc
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : LocallyOfFiniteType A.hom := by
    haveI := hA.smooth
    infer_instance
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K A hA
  have hlK : (l : K) ≠ 0 := by
    intro h0
    apply hl
    have : (l : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, h0, map_zero])
    rw [← map_natCast (residue R), this, map_zero]
  have hfin : ∀ n : ℕ, {x : ptOver K Ω ⟶ A | x ^ (l ^ n) = 1}.Finite := by
    intro n
    have h := GlobalTheory.T.card_abelianVariety_torsion_sepClosed K Ω A hA g hg (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK)
    have : Finite {x : ptOver K Ω ⟶ A // x ^ (l ^ n) = 1} :=
      Nat.finite_of_card_ne_zero (by
        rw [h]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
    exact Set.finite_coe_iff.mp this
  have hSfin : ∀ n, (Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n)).Finite := fun n =>
    (hfin n).subset (by rintro _ ⟨t, rfl⟩; exact t.lev_pow n)
  have hSst : ∀ n, ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n),
      galPts A σ x ∈ Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n) := by
    rintro n σ _ ⟨t, rfl⟩
    exact ⟨galTate A l σ t, rfl⟩
  have h1st : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ {x : ptOver K Ω ⟶ A | x ^ l = 1},
      galPts A σ x ∈ {x : ptOver K Ω ⟶ A | x ^ l = 1} := by
    intro σ x hx
    change galPts A σ x ^ l = 1
    rw [← map_pow, show x ^ l = 1 from hx, map_one]
  obtain ⟨L₁, hL₁f, hL₁g, hL₁⟩ := exists_galois_field_of_finite A {x : ptOver K Ω ⟶ A | x ^ l = 1}
    (by simpa using hfin 1) h1st
  have hq : 1 < Nat.card (ResidueField R) := Finite.one_lt_card
  have hN : 0 < Nat.card (L₁ ≃ₐ[K] L₁) := Nat.card_pos
  refine ⟨(Nat.card (ResidueField R) - 1) * Nat.card (L₁ ≃ₐ[K] L₁), Nat.mul_pos (by omega) hN, ?_⟩
  intro σ hσ
  obtain ⟨g0, hg0⟩ : ∃ g0, g0 = (σ ^ (Nat.card (ResidueField R) - 1)) ^ Nat.card (L₁ ≃ₐ[K] L₁) := ⟨_, rfl⟩
  rw [← map_pow, pow_mul, ← hg0]
  refine LinearMap.ext fun t => Tate.ext fun n => ?_
  change galPts A g0 (t.lev n) = t.lev n
  rw [← mem_stab_iff]
  have hp : (ringChar (ResidueField R)).Prime := CharP.char_is_prime (ResidueField R) _
  have hpl : ringChar (ResidueField R) ≠ l := by
    intro h
    apply hl
    rw [← h, ringChar.Nat.cast_ringChar]
  have hA1 : ∀ y : ptOver K Ω ⟶ A, y ^ l = 1 → galPts A g0 y = y := by
    intro y hy
    have : g0 ∈ L₁.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, hg0, map_pow, pow_card_eq_one']
    exact (hL₁ g0).1 this y hy
  have hlp : g0 ^ (l ^ n) ∈ stab A (t.lev n) := by
    rw [mem_stab_iff, galPts_pow]
    exact pow_fix_of_fix (galPts A g0) l hA1 n _ (by rw [pow_succ, pow_mul, t.lev_pow, one_pow])
  obtain ⟨Ln, hLnf, hLng, hLn⟩ := exists_galois_field_of_finite A _ (hSfin n) (hSst n)
  have hcomm := aut_comm_of_galTate_comm A l hc Ln n hLn
  obtain ⟨a, ha⟩ := GlobalTheory.T.inertia_pow_fixes_of_commutative_alt R K Ω V hV Ln hLnf hLng hcomm σ hσ
  have hpp : g0 ^ (ringChar (ResidueField R) ^ a) ∈ stab A (t.lev n) := by
    have h2 : σ ^ ((Nat.card (ResidueField R) - 1) * ringChar (ResidueField R) ^ a) ∈ Ln.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 ha
    have h3 := (hLn _).1 h2 _ ⟨t, rfl⟩
    have e : g0 ^ (ringChar (ResidueField R) ^ a) =
        (σ ^ ((Nat.card (ResidueField R) - 1) * ringChar (ResidueField R) ^ a)) ^ Nat.card (L₁ ≃ₐ[K] L₁) := by
      rw [hg0, ← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [e]
    exact Subgroup.pow_mem _ h3 _
  exact mem_of_pow_mem_of_coprime _ g0 (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Fact.out).2 hpl)) hpp hlp
