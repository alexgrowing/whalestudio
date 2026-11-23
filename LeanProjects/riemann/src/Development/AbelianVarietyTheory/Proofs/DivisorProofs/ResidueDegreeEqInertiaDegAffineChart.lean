import Mathlib
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.ResidueDegreeChart

theorem inertiaDeg_eq_finrank_of_ker {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R S] [Algebra K L] (φ : R →+* K) (ψ : S →+* L) (q : Ideal S)
    (hq : ∀ s, s ∈ q ↔ ψ s = 0)
    (hφ : ∀ z : K, ∃ a b, z = φ a / φ b) (hψ : ∀ z : L, ∃ a b, z = ψ a / ψ b)
    (hc : ∀ r, algebraMap K L (φ r) = ψ (algebraMap R S r)) :
    q.inertiaDeg R = Module.finrank K L := by
  have hq' : q = RingHom.ker ψ := by ext s; simp [hq, RingHom.mem_ker]
  subst hq'
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : (RingHom.ker ψ).LiesOver (RingHom.ker φ) := ⟨by
    ext r
    simp only [RingHom.mem_ker, Ideal.under, Ideal.mem_comap, ← hc]
    simp⟩
  let _ : Algebra R K := φ.toAlgebra
  let _ : Algebra S L := ψ.toAlgebra
  let _ : Algebra R L := (ψ.comp (algebraMap R S)).toAlgebra
  let _ : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  let _ : Algebra (S ⧸ RingHom.ker ψ) L := (RingHom.kerLift ψ).toAlgebra
  have : FaithfulSMul (R ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  have : FaithfulSMul (S ⧸ RingHom.ker ψ) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ψ)
  have : IsFractionRing (R ⧸ RingHom.ker φ) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hφ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsFractionRing (S ⧸ RingHom.ker ψ) L := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hψ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsScalarTower R (R ⧸ RingHom.ker φ) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower S (S ⧸ RingHom.ker ψ) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => (hc r).symm
  exact Ideal.inertiaDeg_eq_of_isFractionRing (RingHom.ker φ) (RingHom.ker ψ) K L

theorem mem_primeIdealOf_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔ (X.evaluation U x hx).hom s = 0 := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s, ← IsLocalRing.residue_eq_zero_iff]
  rfl

theorem exists_eq_div_evaluation {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (z : X.residueField x) :
    ∃ a b, z = (X.evaluation U x hx).hom a / (X.evaluation U x hx).hom b := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨t, rfl⟩ := X.residue_surjective x z
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk x) t
  refine ⟨a, b, ?_⟩
  have hb : (X.evaluation U x hx).hom b ≠ 0 := fun h0 =>
    b.2 ((mem_primeIdealOf_iff hU x hx b).2 h0)
  rw [eq_div_iff hb]
  have := congrArg (X.residue x).hom h
  rw [map_mul] at this
  exact this

theorem residueDegree_eq_inertiaDeg : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by
  intro X Y g V hV hU w hw
  let _ : Algebra Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := (g.app V).hom.toAlgebra
  let _ : Algebra (X.residueField (g w)) (Y.residueField w) := (g.residueFieldMap w).hom.toAlgebra
  symm
  exact inertiaDeg_eq_finrank_of_ker (X.evaluation V (g w) hw).hom
    (Y.evaluation (g ⁻¹ᵁ V) w hw).hom _ (mem_primeIdealOf_iff hU w hw)
    (exists_eq_div_evaluation hV (g w) hw) (exists_eq_div_evaluation hU w hw)
    (fun r => Scheme.evaluation_naturality_apply g w hw r)

end GlobalTheory.ResidueDegreeChart
