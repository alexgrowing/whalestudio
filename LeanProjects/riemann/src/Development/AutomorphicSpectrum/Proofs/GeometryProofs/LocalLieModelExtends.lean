import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieSections

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (d.comp c) = spMap d ≫ spMap c := by
  simp only [spMap, ← Spec.map_comp]
  rfl

omit [GrpObj G] in

theorem ringHom_ext_of_mono {R A : Type} [CommRing R] [CommRing A] (x : Sp R ⟶ X) [Mono x] {a b : R →+* A}
    (h : spMap a ≫ x = spMap b ≫ x) : a = b :=
  congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h))

theorem extends_of_tr {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
    (M : LieModel G ξ E) {R : Type} [CommRing R] {x : Sp R ⟶ X} {F : Type} [AddCommGroup F] [Module R F]
    (MR : LieModel G x F) (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1) (hψ : spMap ψ ≫ x = X.fromSpecStalk q.1)
    (j : F → E) (hj : ∀ e, (M.pt (j e)).left = spMap (dualMap ((genMap ξ q).comp ψ)) ≫ (MR.pt e).left) (e : F)
    (v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G)
    (hv : v.left = spMap (dualMap ψ) ≫ (MR.pt e).left) : M.Extends q (j e) v := by
  refine ⟨?_, ?_⟩
  · rw [(left_eq_iff ψ hψ v (MR.pt e)).1 hv]
    exact isTanAt_base ψ hψ (MR.tan e)
  · rw [hj, ← spMap_dual_comp, Category.assoc, ← hv]

variable [Smooth G.hom] [IsCommMonObj G]

theorem exists_affine_chart (G : Over X) [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (y : X) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (F : Type) (_ : AddCommGroup F) (_ : Module Γ(X, U) F)
      (_ : LieModel G (R := Γ(X, U)) hU.fromSpec F) (n : ℕ) (_ : Module.Basis (Fin n) Γ(X, U) F), y ∈ U := by
  obtain ⟨R₁, _, x₁, hx₁, F₁, _, _, M₁, n, b₁, hy⟩ := exists_chart G y
  have hU : IsAffineOpen x₁.opensRange := isAffineOpen_opensRange x₁
  let R₀ : Type := Γ(X, x₁.opensRange)
  let x₀ : Sp R₀ ⟶ X := hU.fromSpec
  have hr : Set.range x₀ ⊆ Set.range x₁ := by
    change Set.range hU.fromSpec ⊆ _
    rw [hU.range_fromSpec]
    exact subset_of_eq (Scheme.Hom.coe_opensRange x₁)
  let τ : R₁ →+* R₀ := (Spec.preimage (IsOpenImmersion.lift x₁ x₀ hr)).hom
  have hτ : spMap τ ≫ x₁ = x₀ := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x₁ x₀ hr)).hom) ≫ x₁ = x₀
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  obtain ⟨F₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G R₀ x₀
  obtain ⟨-, B, -, -⟩ := basis_tr τ x₁ x₀ hτ M₁ M₀ b₁
  exact ⟨_, hU, F₀, _, _, M₀, n, B, hy⟩

theorem exists_germs {R : Type} [CommRing R] {x : Sp R ⟶ X} {F : Type} [AddCommGroup F] [Module R F]
    (MR : LieModel G x F) {n : ℕ} (b : Module.Basis (Fin n) R F) {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (φ : R →+* Ω) (j : F →ₛₗ[φ] E)
    (hj : ∀ e, (M.pt (j e)).left = spMap (dualMap φ) ≫ (MR.pt e).left) (p : Cpt ξ)
    (ψ : R →+* X.presheaf.stalk p.1) (hψ : spMap ψ ≫ x = X.fromSpecStalk p.1) (hg : (genMap ξ p).comp ψ = φ)
    {c : E} (hc : c ∈ M.lat p) :
    ∃ s : Fin n → X.presheaf.stalk p.1, c = ∑ k, genMap ξ p (s k) • j (b k) := by
  obtain ⟨v, hv⟩ := (M.mem_lat_iff p c).1 hc
  obtain ⟨Fq, _, _, ⟨Mq⟩⟩ := lieModel_exists X G (X.presheaf.stalk p.1) (X.fromSpecStalk p.1)
  obtain ⟨β, Bq, hBq, hβ⟩ := basis_tr (A := X.presheaf.stalk p.1) ψ x (X.fromSpecStalk p.1) hψ MR Mq b
  obtain ⟨jq, hjq⟩ := exists_tr (A := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ξ (genMap ξ p)
    (spec_genMap ξ p) Mq M
  have hcomp : ∀ e, jq (β e) = j e := fun e => pt_left_inj M (by
    rw [hjq, hβ, ← Category.assoc, spMap_dual_comp, hg, hj])
  obtain ⟨y, rfl⟩ := Mq.onto v hv.1
  have hy : c = jq y := pt_left_inj M (hv.2.trans (hjq y).symm)
  refine ⟨fun k => Bq.repr y k, ?_⟩
  rw [hy]
  conv_lhs => rw [← Bq.sum_repr y, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [jq.map_smulₛₗ, hBq, hcomp]

end GlobalTheory.CompanionTheory.Ar.LieSections

namespace GlobalTheory.CompanionTheory.Ar.LieSections

theorem exists_common_denom {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (y : X) (hy : y ∈ U) {I : Type} [Finite I]
    (s : I → X.presheaf.stalk y) : ∃ (f : Γ(X, U)) (r : I → Γ(X, U)), y ∈ X.basicOpen f ∧
      ∀ i, (X.presheaf.germ U y hy).hom f * s i = (X.presheaf.germ U y hy).hom (r i) := by
  let u : U := ⟨y, hy⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk (u : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf u
  have hloc := hU.isLocalization_stalk u
  obtain ⟨⟨f, hf⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (hU.primeIdealOf u).asIdeal.primeCompl (S := X.presheaf.stalk (u : X)) s
  choose r hr using hint
  refine ⟨f, r, (Scheme.mem_basicOpen _ _ _ hy).2 ?_, fun i => ?_⟩
  · exact IsLocalization.map_units (M := (hU.primeIdealOf u).asIdeal.primeCompl)
      (X.presheaf.stalk (u : X)) ⟨f, hf⟩
  · have := hr i
    rw [Algebra.smul_def] at this
    exact this.symm

end GlobalTheory.CompanionTheory.Ar.LieSections

namespace GlobalTheory.CompanionTheory.Ar

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieSections in

theorem lieLat_germs_eq_sections : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (F : Type) (_ : AddCommGroup F) (_ : Module R F) (MR : LieModel G x F) (e : J → F), p.1 ∈ x.opensRange ∧ x.opensRange ≤ N ∧ ∀ (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1), spMap ψ ≫ x = X.fromSpecStalk q.1 → ∀ (i : J) (v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G), v.left = spMap (dualMap ψ) ≫ (MR.pt (e i)).left → M.Extends q (c i) v := by
  intro X G _ _ _ Ω _ ξ E _ _ M p N J _ c hN hc
  obtain ⟨U, hU, F₀, _, _, M₀, n, b₀, hpU⟩ := exists_affine_chart G p.1
  let R₀ : Type := Γ(X, U)
  let x₀ : Sp R₀ ⟶ X := hU.fromSpec
  have hx₀ : IsOpenImmersion x₀ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hrange : x₀.opensRange = U := hU.opensRange_fromSpec
  have hgen : genPt ξ ∈ x₀.opensRange := p.2.mem_open x₀.opensRange.isOpen (by rw [hrange]; exact hpU)
  obtain ⟨φ₀, hφ₀⟩ := exists_lift x₀ ξ hgen
  let ψ₀ : R₀ →+* X.presheaf.stalk p.1 := (X.presheaf.germ U p.1 hpU).hom
  have hψ₀ : spMap ψ₀ ≫ x₀ = X.fromSpecStalk p.1 := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hpU]
    rfl
  have hg : (genMap ξ p).comp ψ₀ = φ₀ := ringHom_ext_of_mono x₀ (by
    rw [spMap_comp', Category.assoc, hψ₀, hφ₀]
    exact spec_genMap ξ p)
  obtain ⟨j₀, hj₀⟩ := exists_tr x₀ ξ φ₀ hφ₀ M₀ M
  choose s hs using fun i => exists_germs M₀ b₀ M φ₀ j₀ hj₀ p ψ₀ hψ₀ hg (hc i)
  obtain ⟨f, r, hpf, hr⟩ := exists_common_denom hU p.1 hpU (fun ik : J × Fin n => s ik.1 ik.2)
  obtain ⟨g, hgN, hpg⟩ := hU.exists_basicOpen_le (V := N) ⟨p.1, hN⟩ hpU
  let D : X.Opens := X.basicOpen (f * g)
  have hD : IsAffineOpen D := hU.basicOpen (f * g)
  have hDU : D ≤ U := X.basicOpen_le (f * g)
  have hpD : p.1 ∈ D := by
    change p.1 ∈ X.basicOpen (f * g)
    rw [Scheme.basicOpen_mul]
    exact ⟨hpf, hpg⟩
  let R : Type := Γ(X, D)
  let x : Sp R ⟶ X := hD.fromSpec
  have hx : IsOpenImmersion x := inferInstanceAs (IsOpenImmersion hD.fromSpec)
  have hxr : x.opensRange = D := hD.opensRange_fromSpec
  let ρ : R₀ →+* R := (X.presheaf.map (homOfLE hDU).op).hom
  have hρ : spMap ρ ≫ x₀ = x := hU.map_fromSpec hD (homOfLE hDU).op
  obtain ⟨F, _, _, ⟨MF⟩⟩ := lieModel_exists X G R x
  obtain ⟨β, hβ⟩ := exists_tr x₀ x ρ hρ M₀ MF
  have hu : IsUnit (ρ (f * g)) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace (f * g)
  obtain ⟨w, hw⟩ : ∃ w : R, ρ f * w = 1 := by
    rw [map_mul] at hu
    exact (isUnit_of_mul_isUnit_left hu).exists_right_inv
  refine ⟨R, inferInstance, x, hx, F, inferInstance, inferInstance, MF,
    fun i => ∑ k, (ρ (r (i, k)) * w) • β (b₀ k), ?_, ?_, fun q ψ hψ i v hv => ?_⟩
  · rw [hxr]; exact hpD
  · rw [hxr]
    have hDg : D = X.basicOpen f ⊓ X.basicOpen g := X.basicOpen_mul f g
    exact (hDg.le.trans inf_le_right).trans hgN
  let φ : R →+* Ω := (genMap ξ q).comp ψ
  have hφ : spMap φ ≫ x = ξ := by
    rw [spMap_comp', Category.assoc, hψ]
    exact spec_genMap ξ q
  have hφρ : φ.comp ρ = φ₀ := ringHom_ext_of_mono x₀ (by
    rw [spMap_comp', Category.assoc, hρ, hφ, hφ₀])
  obtain ⟨j, hj⟩ := exists_tr x ξ φ hφ MF M
  have hjβ : ∀ u, j (β u) = j₀ u := fun u => pt_left_inj M (by
    rw [hj, hβ, ← Category.assoc, spMap_dual_comp, hφρ, hj₀])
  have hjc : j (∑ k, (ρ (r (i, k)) * w) • β (b₀ k)) = c i := by
    rw [hs i, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [j.map_smulₛₗ, hjβ]
    congr 1
    have h1 : φ (ρ f) * φ w = 1 := by rw [← map_mul, hw, map_one]
    have h2 : φ (ρ (r (i, k))) = φ₀ (r (i, k)) := congrArg (fun t => t (r (i, k))) hφρ
    have h3 : φ (ρ f) = φ₀ f := congrArg (fun t => t f) hφρ
    have h4 : φ₀ f * genMap ξ p (s i k) = φ₀ (r (i, k)) := by
      have := congrArg (genMap ξ p) (hr (i, k))
      rw [map_mul] at this
      have e : ∀ a, genMap ξ p (ψ₀ a) = φ₀ a := fun a => congrArg (fun t => t a) hg
      rw [show (X.presheaf.germ U p.1 hpU).hom f = ψ₀ f from rfl,
        show (X.presheaf.germ U p.1 hpU).hom (r (i, k)) = ψ₀ (r (i, k)) from rfl, e, e] at this
      exact this
    rw [map_mul, h2, ← h4, ← h3, mul_comm (φ (ρ f)), _root_.mul_assoc, h1, _root_.mul_one]
  rw [← hjc]
  exact extends_of_tr M MF q ψ hψ j hj _ v hv

end GlobalTheory.CompanionTheory.Ar
