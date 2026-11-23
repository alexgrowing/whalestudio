import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLatticeIsLatticeSelfDualHermitianModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLatticeStableIffConjIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLatticeEqIffInvMulIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeStandardHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryCentralizerEquivNormOneTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerIffIntegralUnitsOfModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralIndicatorEqFinsumRelIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexEqOfMulEquivSubgroupStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma
theorem unitLat_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := GlobalTheory.T.unitaryLattice_isLattice_selfDual_hermitianModel
theorem unitLat_stable_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := GlobalTheory.T.unitLattice_stable_iff_conj_integral
theorem unitLat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ q q' : UL n w, unitLat e B ψ q = unitLat e B ψ q' ↔ q⁻¹ * q' ∈ KL n w := GlobalTheory.T.unitaryLattice_eq_iff_inv_mul_integral
theorem exists_unitLat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → (∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) → ∃ q : UL n w, unitLat e B ψ q = L := GlobalTheory.T.self_dual_lattice_standard_hermitian
theorem exists_torus_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∃ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y := GlobalTheory.T.localUnitaryCentralizer_equiv_normOneTorus
theorem cptPart_iff_intUnits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∀ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, (∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ t : twCent (MonoidHom.id (UL n w)) γ, ((t : UL n w) ∈ cptPart (twCent (MonoidHom.id (UL n w)) γ) ↔ ((τ t : B.Aˣ)) ∈ intUnits K.O B.A) := GlobalTheory.T.compactPart_centralizer_iff_integralUnits_of_model
theorem twOrb_unit : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G), twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := GlobalTheory.T.orbitalIntegral_indicator_eq_finsum_relIndex
theorem relIndex_transport : ∀ (G H : Type) [Group G] [Group H] (T : Subgroup G) (S : Subgroup H) (τ : T ≃* S) (A₁ A₂ : Subgroup G) (B₁ B₂ : Subgroup H), A₁ ≤ T → A₂ ≤ T → (∀ t : T, (t : G) ∈ A₁ ↔ ((τ t : S) : H) ∈ B₁) → (∀ t : T, (t : G) ∈ A₂ ↔ ((τ t : S) : H) ∈ B₂) → A₁.relIndex A₂ = (B₁ ⊓ S).relIndex (B₂ ⊓ S) := GlobalTheory.T.relIndex_eq_relIndex_inf_of_mulEquiv_subgroup
end GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem mem_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (L : Submodule O A) (a : Aˣ) (y : A) :
    y ∈ mulLat O (a : A) L ↔ ((a⁻¹ : Aˣ) : A) * y ∈ L := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [← mul_assoc] using hz
  · intro h
    exact ⟨((a⁻¹ : Aˣ) : A) * y, h, by simp [← mul_assoc]⟩

theorem mem_stabLat_iff : ∀ (O : Type) [CommRing O] (A : Type) [CommRing A] [Algebra O A] (L : Submodule O A) (u : Aˣ), u ∈ stabLat O L ↔ mulLat O (u : A) L = L := by
  intro O _ A _ _ L u
  constructor
  · intro h
    have h' : ∀ y, y ∈ L ↔ (u : A) * y ∈ L := h
    ext y
    rw [mem_mulLat_unit, h', ← mul_assoc, Units.mul_inv, one_mul]
  · intro h y
    have hy := mem_mulLat_unit L u ((u : A) * y)
    rw [h, ← mul_assoc, Units.inv_mul, one_mul] at hy
    exact hy.symm

theorem unitLat_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (t q : UL n w) (a : B.Aˣ), (∀ y, ψ ((a : B.A) * y) = ((((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → unitLat e B ψ (t * q) = mulLat K.O (a : B.A) (unitLat e B ψ q) := by
  intro E _ _ _ hE w hw K e he hint n B ψ t q a ha
  have hmap : ∀ (g h : UL n w), ((((g * h : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) =
      (((g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm *
        (((h : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm := by
    intro g h
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul (f := (e.symm : w.adicCompletion E →+* K.E))
  have hinv : ∀ y, ((((t⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y =
      ψ (((a⁻¹ : B.Aˣ) : B.A) * y) := by
    intro y
    have h1 : ψ y = ((((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ
        ψ (((a⁻¹ : B.Aˣ) : B.A) * y) := by
      rw [← ha, ← mul_assoc, Units.mul_inv, one_mul]
    rw [h1, Matrix.mulVec_mulVec, ← hmap, inv_mul_cancel]
    simp
  have key : ∀ (r : UL n w) (z : B.A), z ∈ unitLat e B ψ r ↔
      ∀ i, (((((r⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ z) i ∈
        (algebraMap K.O K.E).range := fun r z => Iff.rfl
  ext y
  rw [key, _root_.mul_inv_rev, hmap, ← Matrix.mulVec_mulVec, hinv, ← key, mem_mulLat_unit]

end GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem mulLat_one' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (L : Submodule O A) :
    mulLat O (1 : A) L = L := by
  simp [mulLat]

theorem mulLat_mul' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (a b : A) (L : Submodule O A) :
    mulLat O (a * b) L = mulLat O a (mulLat O b L) := by
  rw [mulLat, mulLat, mulLat, LinearMap.mulLeft_mul, Submodule.map_comp]

theorem orbRel_equivalence {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (G : Subgroup Aˣ)
    (X : Set (Submodule O A)) :
    Equivalence (fun L M : X => ∃ t ∈ G, (M : Submodule O A) = mulLat O (t : A) (L : Submodule O A)) where
  refl L := ⟨1, G.one_mem, by simp [mulLat_one']⟩
  symm := by
    rintro L M ⟨t, ht, h⟩
    refine ⟨t⁻¹, G.inv_mem ht, ?_⟩
    rw [h, ← mulLat_mul', Units.inv_mul, mulLat_one']
  trans := by
    rintro L M N ⟨t, ht, h⟩ ⟨s, hs, h'⟩
    refine ⟨s * t, G.mul_mem hs ht, ?_⟩
    rw [h', h, Units.val_mul, mulLat_mul']

theorem ratCast_finsum' {α : Type} (f : α → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, ((f i : ℚ) : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact AddMonoidHom.map_finsum (Rat.castHom ℂ).toAddMonoidHom h
  · rw [finsum_of_infinite_support h, finsum_of_infinite_support]
    · simp
    · have : Function.support (fun i => ((f i : ℚ) : ℂ)) = Function.support f := by
        ext i; simp
      rwa [this]

theorem finsum_ite_subtype' {α M : Type} [AddCommMonoid M] (p : α → Prop) [DecidablePred p] (f : α → M) :
    ∑ᶠ i, (if p i then f i else 0) = ∑ᶠ i : Subtype p, f i := by
  rw [finsum_subtype_eq_finsum_cond]
  exact finsum_congr fun i => finsum_eq_if.symm

theorem orb_eq_N : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (γ : UL n w) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B (γ.1.val.map e.symm) x ψ → twOrb (MonoidHom.id _) (KL n w) γ ((KL n w : Set (UL n w)).indicator 1) = ((B.N x : ℚ) : ℂ) := by
  intro E _ _ _ hE w hw K e he hint n B hsep γ x ψ hM
  obtain ⟨hx, hg, hh⟩ := hM
  obtain ⟨τ, hτ⟩ := exists_torus_equiv E hE w hw K e he hint n B ψ x γ ⟨hx, hg, hh⟩ hsep
  have hcpt := cptPart_iff_intUnits E hE w hw K e he hint n B ψ x γ ⟨hx, hg, hh⟩ hsep τ hτ
  have hS1 := unitLat_selfDual E hE w hw K e he hint n B ψ x hx hh
  have hS1b := unitLat_stable_iff E hE w hw K e he hint n B ψ γ hg
  have hS2 := unitLat_eq_iff E hE w hw K e he hint n B ψ
  have hS3 := exists_unitLat_eq E hE w hw K e he hint n B ψ x hx hh
  have hS6 : ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (q : UL n w),
      unitLat e B ψ ((t : UL n w) * q) = mulLat K.O ((τ t : B.Aˣ) : B.A) (unitLat e B ψ q) :=
    fun t q => unitLat_mul E hE w hw K e he hint n B ψ t q (τ t) (hτ t)
  have hcomm : ∀ s t : twCent (MonoidHom.id (UL n w)) γ, (s : UL n w) * t = t * s := by
    intro s t
    have h1 : τ (s * t) = τ (t * s) := by rw [map_mul, map_mul, mul_comm]
    have := congrArg Subtype.val (τ.injective h1)
    simpa using this
  have hX : ∀ q : UL n w, q⁻¹ * γ * q ∈ KL n w → unitLat e B ψ q ∈ B.X x := fun q hq =>
    ⟨(hS1 q).1, (hS1b q).2 hq, (hS1 q).2⟩
  have hrel : ∀ L M : B.X x, (Quot.mk _ L : Orb K.O B.T (B.X x)) = Quot.mk _ M →
      ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) L := fun L M h =>
    (orbRel_equivalence B.T (B.X x)).eqvGen_iff.mp (Quot.eqvGen_exact h)
  have hcle : cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ twCent (MonoidHom.id (UL n w)) γ :=
    (Subgroup.closure_le _).mpr fun s hs => hs.1
  have hconj : ∀ (Q s : UL n w), s ∈ (KL n w).map (MulAut.conj Q).toMonoidHom ↔ Q⁻¹ * s * Q ∈ KL n w := by
    intro Q s
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [twOrb_unit]
  unfold InvAlg.N orbSum
  rw [ratCast_finsum']
  rw [finsum_ite_subtype']
  let φ : {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) γ : Set (UL n w)) (KL n w : Set (UL n w)) //
      (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ KL n w} → Orb K.O B.T (B.X x) :=
    fun q => Quot.mk _ ⟨unitLat e B ψ (Quotient.out q.1), hX _ q.2⟩
  refine finsum_eq_of_bijective φ ⟨?_, ?_⟩ ?_
  · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
    obtain ⟨a, ha, hQ⟩ := hrel _ _ h
    set t := τ.symm ⟨a, ha⟩
    have hta : ((τ t : B.Aˣ) : B.A) = a := by simp [t]
    rw [← hta, ← hS6, hS2] at hQ
    apply Subtype.ext
    show q = q'
    rw [← DoubleCoset.out_eq' _ _ q, ← DoubleCoset.out_eq' _ _ q', DoubleCoset.eq]
    exact ⟨t, t.2, _, (KL n w).inv_mem hQ, by group⟩
  · intro o
    set R := Quot.out o
    obtain ⟨q0, hq0⟩ := hS3 R.1 R.2.1 R.2.2.2
    have hq0K : q0⁻¹ * γ * q0 ∈ KL n w := (hS1b q0).1 (hq0 ▸ R.2.2.1)
    obtain ⟨h, k, hh, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0
    have hhγ : h * γ = γ * h := hh
    have hP : (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0))⁻¹ * γ *
        Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0) ∈ KL n w := by
      rw [hout]
      have : (h * q0 * k)⁻¹ * γ * (h * q0 * k) = k⁻¹ * (q0⁻¹ * γ * q0) * k := by
        calc (h * q0 * k)⁻¹ * γ * (h * q0 * k) = k⁻¹ * q0⁻¹ * (h⁻¹ * (γ * h)) * q0 * k := by group
          _ = k⁻¹ * (q0⁻¹ * γ * q0) * k := by rw [← hhγ]; group
      rw [this]
      exact (KL n w).mul_mem ((KL n w).mul_mem ((KL n w).inv_mem hk) hq0K) hk
    refine ⟨⟨_, hP⟩, ?_⟩
    show Quot.mk _ _ = o
    rw [← Quot.out_eq o]
    refine (Quot.sound ?_).symm
    refine ⟨τ ⟨h, hh⟩, (τ ⟨h, hh⟩).2, ?_⟩
    show unitLat e B ψ _ = mulLat K.O _ R.1
    rw [hout, ← hq0, ← hS6]
    exact ((hS2 _ _).2 (by simpa [mul_assoc] using hk)).symm
  · rintro ⟨q, hq⟩
    set R := Quot.out (φ ⟨q, hq⟩)
    have hR : (Quot.mk _ R : Orb K.O B.T (B.X x)) = φ ⟨q, hq⟩ := Quot.out_eq _
    obtain ⟨a, ha, hRa⟩ := hrel _ _ hR.symm
    set t := τ.symm ⟨a, ha⟩
    have hta : ((τ t : B.Aˣ) : B.A) = a := by simp [t]
    rw [← hta, ← hS6] at hRa
    simp only [one_mul, Rat.cast_natCast]
    congr 1
    refine relIndex_transport (UL n w) B.Aˣ _ B.T τ _ _ (stabLat K.O R.1) (intUnits K.O B.A) inf_le_left hcle ?_ hcpt
    intro s
    rw [mem_stabLat_iff, hRa, ← hS6, hS2, Subgroup.mem_inf, hconj]
    simp only [SetLike.coe_mem, true_and]
    have : ((s : UL n w) * ((t : UL n w) * Quotient.out q))⁻¹ * ((t : UL n w) * Quotient.out q) =
        ((Quotient.out q)⁻¹ * s * Quotient.out q)⁻¹ := by
      rw [← mul_assoc (s : UL n w), hcomm s t]
      group
    rw [this]
    exact inv_mem_iff.symm

end GlobalTheory.InertUnitOrb
