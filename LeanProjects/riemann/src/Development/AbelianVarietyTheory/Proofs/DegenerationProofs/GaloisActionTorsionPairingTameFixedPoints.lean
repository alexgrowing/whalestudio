import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

section
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

noncomputable def galSpecHom (τ : Ω ≃ₐ[K] Ω) :
    Over.mk (spMap (algebraMap K Ω)) ⟶ Over.mk (spMap (algebraMap K Ω)) :=
  Over.homMk (spMap τ.toRingEquiv.toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact τ.commutes c)

theorem galSpecHom_one : galSpecHom (1 : Ω ≃ₐ[K] Ω) = 𝟙 _ := by
  ext1
  exact Spec.map_id _

theorem galSpecHom_mul (τ τ' : Ω ≃ₐ[K] Ω) :
    galSpecHom (τ * τ') = galSpecHom τ ≫ galSpecHom τ' := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

noncomputable def galPointAct (A : Over (Sp K)) [MonObj A] :
    (Ω ≃ₐ[K] Ω) →* MulAut (Over.mk (spMap (algebraMap K Ω)) ⟶ A) where
  toFun τ :=
    { toFun := fun x => galSpecHom τ ≫ x
      invFun := fun x => galSpecHom τ⁻¹ ≫ x
      left_inv := fun x => by
        simp only [← Category.assoc, ← galSpecHom_mul, inv_mul_cancel, galSpecHom_one,
          Category.id_comp]
      right_inv := fun x => by
        simp only [← Category.assoc, ← galSpecHom_mul, mul_inv_cancel, galSpecHom_one,
          Category.id_comp]
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  map_one' := by
    ext1 x
    change galSpecHom 1 ≫ x = x
    rw [galSpecHom_one, Category.id_comp]
  map_mul' τ τ' := by
    ext1 x
    change galSpecHom (τ * τ') ≫ x = galSpecHom τ ≫ galSpecHom τ' ≫ x
    rw [galSpecHom_mul, Category.assoc]

theorem galPointAct_left (A : Over (Sp K)) [MonObj A] (τ : Ω ≃ₐ[K] Ω)
    (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) :
    (galPointAct A τ x).left = spMap τ.toRingEquiv.toRingHom ≫ x.left := rfl

theorem galPointAct_eq_of_agree (A : Over (Sp K)) [MonObj A] (L : IntermediateField K Ω)
    (τ τ' : Ω ≃ₐ[K] Ω) (h : ∀ c ∈ L, τ c = τ' c) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A)
    (y : Sp L ⟶ A.left) (hy : spMap (algebraMap L Ω) ≫ y = x.left) :
    galPointAct A τ x = galPointAct A τ' x := by
  ext1
  rw [galPointAct_left, galPointAct_left, ← hy, ← Category.assoc, ← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact h c c.2

theorem algEquiv_mem_of_normal (L : IntermediateField K Ω) [Normal K L] (τ : Ω ≃ₐ[K] Ω)
    {c : Ω} (hc : c ∈ L) : τ c ∈ L := by
  have := AlgEquiv.restrictNormal_commutes τ L ⟨c, hc⟩
  change ((τ.restrictNormal L ⟨c, hc⟩ : L) : Ω) = τ c at this
  rw [← this]
  exact Subtype.prop _

theorem pow_tame_relation (L : IntermediateField K Ω) [Normal K L] (σ φ : Ω ≃ₐ[K] Ω) (q : ℕ)
    (h : ∀ c ∈ L, φ (σ c) = (σ ^ q) (φ c)) (N : ℕ) :
    ∀ c ∈ L, (φ ^ N * σ) c = (σ ^ q ^ N * φ ^ N) c := by
  have h1 : ∀ (a : ℕ), ∀ c ∈ L, φ ((σ ^ a) c) = (σ ^ (q * a)) (φ c) := by
    intro a
    induction a with
    | zero => intro c _; simp
    | succ a ih =>
      intro c hc
      rw [pow_succ', AlgEquiv.mul_apply, h _ (algEquiv_mem_of_normal L _ hc), ih c hc,
        ← AlgEquiv.mul_apply, ← pow_add, Nat.mul_succ, Nat.add_comm]
  induction N with
  | zero => intro c _; simp
  | succ N ih =>
    intro c hc
    have := ih c hc
    simp only [AlgEquiv.mul_apply] at this
    rw [pow_succ' φ, pow_succ' q]
    simp only [AlgEquiv.mul_apply]
    rw [this, h1 _ _ (algEquiv_mem_of_normal L _ hc)]

end

theorem galois_action_torsion_points : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l q : ℕ), l.Prime → (∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ (σ φ : Ω ≃ₐ[K] Ω) (K' : Type) [Field K'] (j : K' →+* Ω), (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) → (∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → x ∈ j.fieldRange)) → ∃ (e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ) (act : (Ω ≃ₐ[K] Ω) →* MulAut (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), (∀ τ x, (act τ x).left = spMap τ.toRingEquiv.toRingHom ≫ x.left) ∧ ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ (∀ N n x y, x ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (act σ x) (act σ y) = e n x y ∧ e n (act (φ ^ N) x) (act (φ ^ N) y) = e n x y ^ (q ^ N)) ∧ (∀ N n x, x ^ l ^ n = 1 → act (φ ^ N) (act σ x) = (act σ)^[q ^ N] (act (φ ^ N) x)) ∧ ∀ n x, x ^ l ^ n = 1 → act σ x = x → ∃ y : Sp K' ⟶ P.A.left, spMap j ≫ y = x.left := by
  intro K _ _ P Ω _ _ _ l q hl hrat σ φ K' _ j hζ hL
  obtain ⟨-, ⟨e, he, hgal⟩, hfield⟩ := GlobalTheory.T.torsion_points_polarised_abelianVariety_galois K P Ω l hl
  have hφ : ∀ (m N : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → (φ ^ N) ζ = ζ ^ q ^ N := by
    intro m N ζ h
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, (hζ m ζ h).2, ← pow_mul, pow_succ']
  refine ⟨e, galPointAct P.A, fun τ x => rfl, he, ?_, ?_, ?_⟩
  · intro N n x y hx hy
    obtain ⟨h1, h2⟩ := hgal σ n x y _ _ hx hy (galPointAct_left _ σ x) (galPointAct_left _ σ y)
    obtain ⟨-, h3⟩ := hgal (φ ^ N) n x y _ _ hx hy (galPointAct_left _ _ x)
      (galPointAct_left _ _ y)
    refine ⟨Units.ext ?_, Units.ext ?_⟩
    · rw [h2, (hζ n _ h1).1]
    · rw [h3, hφ n N _ h1, Units.val_pow_eq_pow_val]
  · intro N n x hx
    obtain ⟨L, hfin, hnorm, hp, hpts⟩ := hfield hrat n
    obtain ⟨y, hy⟩ := hpts x hx
    have := galPointAct_eq_of_agree P.A L _ _
      (pow_tame_relation L σ φ q (fun c hc => (hL L hfin hnorm hp c hc).1) N) x y hy
    rw [map_mul, map_mul, map_pow (galPointAct P.A) σ] at this
    rw [← MulAut.mul_apply, this, MulAut.mul_apply]
    generalize galPointAct P.A (φ ^ N) x = z
    generalize q ^ N = k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
  · intro n x hx hfix
    obtain ⟨L, hfin, hnorm, hp, hpts⟩ := hfield hrat n
    obtain ⟨E, hE1, hE2, -⟩ := exists_fieldOfValues P.A.left Ω x.left
    have hEL := (hE2 L (algebraMap L Ω)).2 (hpts x hx)
    have hσ := (hE1 σ.toRingEquiv.toRingHom (RingHom.id Ω)).1 (by
      rw [← galPointAct_left, hfix]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ x.left) (Spec.map_id _).symm))
    refine (hE2 K' j).1 fun c hc => ?_
    obtain ⟨d, rfl⟩ := hEL hc
    exact (hL L hfin hnorm hp _ d.2).2 (hσ _ hc)

end GlobalTheory.SS
