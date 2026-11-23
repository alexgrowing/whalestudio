import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

private theorem eq_specMap_comp_of_apply_eq {X : Scheme.{0}} {B K Ω : Type} [CommRing B] [Field K]
    [Field Ω] (h : X ⟶ Spec (CommRingCat.of B)) (β : B →+* K)
    (hβ : ∀ x : K, ∃ r u : B, β u ≠ 0 ∧ x * β u = β r)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ h = Spec.map (CommRingCat.ofHom β))
    (k : K →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ X)
    (hy : y ≫ h = Spec.map (CommRingCat.ofHom (k.comp β)))
    (a : Spec (CommRingCat.of Ω)) (b : Spec (CommRingCat.of K)) (hab : y a = s b) :
    y = Spec.map (CommRingCat.ofHom k) ≫ s := by
  have hpt : ∀ (L : Type) [Field L] (p q : Spec (CommRingCat.of L)), p = q := by
    intro L _ p q
    let p' : PrimeSpectrum L := p
    let q' : PrimeSpectrum L := q
    exact (PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p'.asIdeal).trans
      (Ideal.eq_bot_of_prime q'.asIdeal).symm) : p' = q')
  obtain ⟨W, hW, hbW, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (s b))
  haveI := hW.isOpenImmersion_fromSpec
  have hrange : ∀ {Y : Scheme.{0}} (e : Y ⟶ X) (z : Y), (∀ z', z' = z) → e z ∈ W →
      Set.range e ⊆ Set.range hW.fromSpec := by
    intro Y e z hz he
    rintro _ ⟨z', rfl⟩
    rw [hW.range_fromSpec, hz z']
    exact he
  have hyW := hrange y a (fun z' => hpt Ω z' a) (by rw [hab]; exact hbW)
  have hsW := hrange s b (fun z' => hpt K z' b) hbW
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec y hyW)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec s hsW)
  obtain ⟨α, hα⟩ := Spec.map_surjective (hW.fromSpec ≫ h)
  have hσβ : α ≫ σ = CommRingCat.ofHom β := Spec.map_injective (by
    rw [Spec.map_comp, hσ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hs])
  have hψβ : α ≫ ψ = CommRingCat.ofHom (k.comp β) := Spec.map_injective (by
    rw [Spec.map_comp, hψ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hy])
  have hpts : (Spec.map ψ) a = (Spec.map σ) b := by
    apply (Scheme.Hom.isOpenEmbedding hW.fromSpec).injective
    rw [← Scheme.Hom.comp_apply (Spec.map ψ) hW.fromSpec a,
      ← Scheme.Hom.comp_apply (Spec.map σ) hW.fromSpec b, hψ, hσ, IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, hab]
  have hker : ∀ x, σ.hom x = 0 → ψ.hom x = 0 := by
    intro x hx
    let a' : PrimeSpectrum Ω := a
    let b' : PrimeSpectrum K := b
    have ha : a'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have hb : b'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have e := congrArg PrimeSpectrum.asIdeal hpts
    have hmem : x ∈ PrimeSpectrum.asIdeal ((Spec.map σ) b) := by
      rw [Spec.map_apply]
      change σ.hom x ∈ b'.asIdeal
      rw [hb, Ideal.mem_bot]
      exact hx
    rw [← e, Spec.map_apply] at hmem
    change ψ.hom x ∈ a'.asIdeal at hmem
    rwa [ha, Ideal.mem_bot] at hmem
  have hψσ : ψ = σ ≫ CommRingCat.ofHom k := by
    apply CommRingCat.hom_ext
    ext x
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    obtain ⟨r, u, hu, hxu⟩ := hβ (σ.hom x)
    have hσα : ∀ z, σ.hom (α.hom z) = β z := fun z => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, hσβ, CommRingCat.hom_ofHom]
    have hψα : ∀ z, ψ.hom (α.hom z) = k (β z) := fun z => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, hψβ, CommRingCat.hom_ofHom,
        RingHom.comp_apply]
    have h0 : ψ.hom (x * α.hom u - α.hom r) = 0 := hker _ (by
      rw [map_sub, map_mul, hσα, hσα, hxu, sub_self])
    rw [map_sub, map_mul, hψα, hψα, sub_eq_zero] at h0
    have hku : k (β u) ≠ 0 := (map_ne_zero k).mpr hu
    apply mul_right_cancel₀ hku
    rw [h0, ← map_mul, hxu]
  calc y = IsOpenImmersion.lift hW.fromSpec y hyW ≫ hW.fromSpec :=
        (IsOpenImmersion.lift_fac _ _ _).symm
    _ = Spec.map ψ ≫ hW.fromSpec := by rw [hψ]
    _ = Spec.map (CommRingCat.ofHom k) ≫ s := by
        rw [hψσ, Spec.map_comp, Category.assoc, hσ, IsOpenImmersion.lift_fac]

theorem QFGroup.exists_eq_comp_pt : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
    (Ω : Type) [Field Ω] (k : FractionRing R →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ Γ.G.left),
    y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) →
    ∃ t, y = Spec.map (CommRingCat.ofHom k) ≫ (Γ.pt t).left := by
  intro R _ _ T _ Γ
  cases Γ
  rename_i pt _ pt_onto _
  dsimp only
  intro Ω _ k y hy
  let a0 : Spec (CommRingCat.of Ω) := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum Ω)
  obtain ⟨t, x, hx⟩ := pt_onto (y a0) (by
    rw [← Scheme.Hom.comp_apply y _ a0, hy, Spec.map_apply]
    change Ideal.comap (k.comp (algebraMap R (FractionRing R))) (⊥ : Ideal Ω) = ⊥
    exact Ideal.comap_bot_of_injective _ (k.injective.comp (IsFractionRing.injective R (FractionRing R))))
  refine ⟨t, eq_specMap_comp_of_apply_eq _ (algebraMap R (FractionRing R)) ?_ (pt t).left
    (Over.w (pt t)) k y hy a0 x hx.symm⟩
  intro z
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) z
  exact ⟨n, d, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2, hnd⟩

end GlobalTheory.CompanionTheory.Ar.BT
