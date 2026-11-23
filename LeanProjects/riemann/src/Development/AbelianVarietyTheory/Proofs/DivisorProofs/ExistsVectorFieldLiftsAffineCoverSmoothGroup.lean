import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomLiftOfFormallySmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecVectorFieldOfDualNumberSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldAffineOpenTransportStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSLift

def twist {R A : Type} [CommRing R] [CommRing A] (ρ : R →+* A) (D : Derivation ℤ R R) : R →+* DualNumber A where
  toFun r := TrivSqZeroExt.inl (ρ r) + TrivSqZeroExt.inr (ρ (D r))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [Derivation.leibniz, smul_eq_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

def epsIdeal (A : Type) [CommRing A] : Ideal (DualNumber A) := RingHom.ker (TrivSqZeroExt.fstHom A A A).toRingHom

theorem mem_epsIdeal {A : Type} [CommRing A] (x : DualNumber A) : x ∈ epsIdeal A ↔ x.fst = 0 := Iff.rfl

theorem isNilpotent_epsIdeal (A : Type) [CommRing A] : IsNilpotent (epsIdeal A) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  rw [mem_epsIdeal] at hx hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]

theorem exists_lift {R A : Type} [CommRing R] [CommRing A] (ρ : R →+* A) (hρ : ρ.FormallySmooth)
    (D : Derivation ℤ R R) : ∃ σ : A →+* DualNumber A, (∀ a, (σ a).fst = a) ∧ ∀ r, (σ (ρ r)).snd = ρ (D r) := by
  have hg : ((Ideal.Quotient.mk (epsIdeal A)).comp (algebraMap A (DualNumber A))).comp ρ =
      (Ideal.Quotient.mk (epsIdeal A)).comp (twist ρ D) := by
    ext r
    simp only [RingHom.comp_apply]
    rw [Ideal.Quotient.eq, mem_epsIdeal]
    simp [twist, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨F, hF1, hF2⟩ := GlobalTheory.DI.exists_ringHom_lift_of_formallySmooth ρ hρ (twist ρ D) (epsIdeal A)
    (isNilpotent_epsIdeal A) _ hg
  refine ⟨F, fun a => ?_, fun r => ?_⟩
  · have h := hF1 a
    simp only [RingHom.comp_apply] at h
    rw [Ideal.Quotient.eq, mem_epsIdeal] at h
    simpa [sub_eq_zero, TrivSqZeroExt.algebraMap_eq_inl] using h
  · rw [hF2]; simp [twist]

theorem main (LA : ∀ (A : Type) [CommRing A] (σ : A →+* DualNumber A), (∀ a, (σ a).fst = a) → ∃ d : ∀ O : (Sp A).Opens, Γ(Sp A, O) → Γ(Sp A, O), IsField ⊤ d ∧ ∀ a : A, d ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd) (LB : ∀ (Z : Scheme.{0}) (W : Z.Opens) (hW : IsAffineOpen W) (δ : Γ(Z, W) → Γ(Z, W)) (d' : ∀ O : (Spec Γ(Z, W)).Opens, Γ(Spec Γ(Z, W), O) → Γ(Spec Γ(Z, W), O)), IsField ⊤ d' → (∀ a, d' ⊤ ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom a) = (Scheme.ΓSpecIso Γ(Z, W)).inv.hom (δ a)) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField W d ∧ ∀ a, d W a = δ a) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) := by
  intro E _ _ _ H X t U D
  have key : ∀ (V : t.G.left.affineOpens) (h : V.1 ≤ t.G.hom ⁻¹ᵁ U.1),
      ∃ d : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O), IsField V.1 d ∧
        ∀ r, d V.1 ((t.G.hom.appLE U.1 V.1 h).hom r) = (t.G.hom.appLE U.1 V.1 h).hom (D r) := by
    intro V h
    have hsm : (t.G.hom.appLE U.1 V.1 h).hom.Smooth := t.semi.smooth.smooth_appLE U.2 V.2 h
    obtain ⟨σ, hσ1, hσ2⟩ := exists_lift _ hsm.formallySmooth D
    obtain ⟨d', hd'1, hd'2⟩ := LA _ σ hσ1
    obtain ⟨d, hd1, hd2⟩ := LB t.G.left V.1 V.2 (fun a => (σ a).snd) d' hd'1 hd'2
    exact ⟨d, hd1, fun r => by rw [hd2, hσ2]⟩
  choose dd hdd1 hdd2 using key
  let J := {p : t.G.left.affineOpens × t.PP.L.ι // p.1.1 ≤ t.G.hom ⁻¹ᵁ U.1 ⊓ t.PP.L.U p.2}
  refine ⟨J, fun i => i.1.1.1, fun i => i.1.2, fun i => dd i.1.1 (i.2.trans inf_le_left),
    fun i => i.1.1.2, ?_, fun i => i.2.trans inf_le_right, fun i => hdd1 _ _, fun i h r => hdd2 _ _ r⟩
  refine le_antisymm (iSup_le fun i => i.2.trans inf_le_left) fun x hx => ?_
  have hx' : x ∈ (⨆ k, t.PP.L.U k) := by rw [t.PP.isLB.cover]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := t.G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ t.G.hom ⁻¹ᵁ U.1 ⊓ t.PP.L.U k from ⟨hx, hk⟩) (t.G.hom ⁻¹ᵁ U.1 ⊓ t.PP.L.U k).2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, k), hVle⟩, hxV⟩

theorem exists_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) :=
  main GlobalTheory.T.exists_spec_vectorField_of_dualNumber_section GlobalTheory.T.exists_vectorField_affineOpen_transport

end GlobalTheory.KSLift
