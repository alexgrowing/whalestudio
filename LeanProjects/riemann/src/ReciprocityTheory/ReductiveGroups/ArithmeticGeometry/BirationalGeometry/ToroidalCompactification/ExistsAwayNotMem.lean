import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PairCompat

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

theorem ofId_ext {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B] (f g : S →ₐ[S] B) : f = g := Subsingleton.elim f g

theorem exists_away_not_mem {S : Type} [CommRing S] {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (p : Ideal S) [p.IsPrime] : ∃ k, s k ∉ p := by
  by_contra hne
  push_neg at hne
  have hle : Ideal.span (Set.range s) ≤ p := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hne k
  rw [hs, top_le_iff] at hle
  exact Ideal.IsPrime.ne_top ‹p.IsPrime› hle

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] [∀ s : S, Smooth (Gs G s).hom]

section Prime

variable (p : Ideal S) [p.IsPrime]

@[instance_reducible]
def awayAtPrime (t : S) (ht : t ∉ p) : Algebra (Localization.Away t) (Localization.AtPrime p) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers t) p.primeCompl
    ((Submonoid.powers_le (P := p.primeCompl)).mpr ht)

theorem tan_prime_lift {y' : sp (R₀ := S) (DualNumber (Localization.AtPrime p)) ⟶ G} (hy' : TanS y') :
    ∃ q ∈ p.primeCompl, ∃ w : sp (R₀ := S) (DualNumber S) ⟶ G, TanS w ∧
      spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ w =
        spMap (scaleS (S := S) (algebraMap S (Localization.AtPrime p) q)) ≫ y' := by
  obtain ⟨n, s, hs, hC⟩ := exists_cover G
  have C : ∀ k, Chart (Gs G (s k)) := fun k => (hC k).some
  obtain ⟨k0, hk0⟩ := exists_away_not_mem s hs p
  have hle : Submonoid.powers (s k0) ≤ p.primeCompl := (Submonoid.powers_le (P := p.primeCompl)).mpr hk0
  let _ := awayAtPrime p (s k0) hk0
  have : IsScalarTower S (Localization.Away (s k0)) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  have : Algebra.FinitePresentation (Localization.Away (s k0)) Γ((Gs G (s k0)).left, (C k0).U) := fp_chart (C k0)
  let M := p.primeCompl.map (algebraMap S (Localization.Away (s k0)))
  have hM : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M) (Localization.AtPrime p) := by
    have e : Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M = M := by
      rw [Algebra.algebraMapSubmonoid, Algebra.algebraMap_self]
      ext x
      simp
    rw [e]
    exact IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  obtain ⟨_, ⟨q, hq, rfl⟩, y₀, hy₀, he⟩ := tanS_lift (C k0) (A := Localization.Away (s k0)) M hy'
  obtain ⟨N, w, hw, hwr⟩ := tan_extend s hs C k0 hy₀
  refine ⟨s k0 ^ N * q, p.primeCompl.mul_mem (p.primeCompl.pow_mem hk0 N) hq, w, hw, ?_⟩
  rw [show Algebra.ofId S (Localization.AtPrime p) =
      (IsScalarTower.toAlgHom S (Localization.Away (s k0)) (Localization.AtPrime p)).comp
        (Algebra.ofId S (Localization.Away (s k0))) from ofId_ext _ _, ← res_res, hwr, res_scale, he, scale_scale,
    map_pow, AlgHom.commutes, ← IsScalarTower.algebraMap_apply, map_mul, map_pow]

theorem tan_prime_uniq {w : sp (R₀ := S) (DualNumber S) ⟶ G} (hw : TanS w)
    (h1 : spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ w = 1) :
    ∃ q ∈ p.primeCompl, spMap (scaleS (S := S) q) ≫ w = 1 := by
  classical
  obtain ⟨n, s, hs, hC⟩ := exists_cover G
  have C : ∀ k, Chart (Gs G (s k)) := fun k => (hC k).some
  obtain ⟨k0, hk0⟩ := exists_away_not_mem s hs p
  have hle : Submonoid.powers (s k0) ≤ p.primeCompl := (Submonoid.powers_le (P := p.primeCompl)).mpr hk0
  let _ := awayAtPrime p (s k0) hk0
  have : IsScalarTower S (Localization.Away (s k0)) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  have : Algebra.FinitePresentation (Localization.Away (s k0)) Γ((Gs G (s k0)).left, (C k0).U) := fp_chart (C k0)
  let M := p.primeCompl.map (algebraMap S (Localization.Away (s k0)))
  have hM : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M) (Localization.AtPrime p) := by
    have e : Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M = M := by
      rw [Algebra.algebraMapSubmonoid, Algebra.algebraMap_self]
      ext x
      simp
    rw [e]
    exact IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  have hwk : ∀ k, TanS (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ w) :=
    fun k => tanS_restrict _ hw
  have hone : ∀ (A : Type) [CommRing A] [Algebra S A], TanS (1 : sp (R₀ := S) (DualNumber A) ⟶ G) :=
    fun A _ _ => comp_one' _
  obtain ⟨_, ⟨q₀, hq₀, rfl⟩, hc0⟩ := tanS_uniq (C k0) (A := Localization.Away (s k0))
    (A' := Localization.AtPrime p) M (hwk k0) (hone _) (by
      rw [res_res, comp_one', show (IsScalarTower.toAlgHom S (Localization.Away (s k0)) (Localization.AtPrime p)).comp
        (Algebra.ofId S (Localization.Away (s k0))) = Algebra.ofId S (Localization.AtPrime p) from ofId_ext _ _, h1])
  rw [comp_one'] at hc0
  have h2 : ∀ k, ∃ N : ℕ, spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ N)) ≫
      spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) q₀)) ≫
        spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ w =
      spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ N)) ≫ 1 := by
    intro k
    apply tanS_away_uniq (C k) (A := Localization.Away (s k)) (s k0) (tanS_scale _ (hwk k)) (hone _)
    rw [comp_one', res_scale, res_res, AlgHom.commutes,
      show (qL (s k) (s k0)).comp (Algebra.ofId S (Localization.Away (s k))) =
        (qR (s k) (s k0)).comp (Algebra.ofId S (Localization.Away (s k0))) from ofId_ext _ _,
      ← res_res, show algebraMap S (Qv (s k) (s k0)) q₀ = qR (s k) (s k0) (algebraMap S (Localization.Away (s k0)) q₀)
        from ((qR (s k) (s k0)).commutes q₀).symm, ← res_scale]
    rw [show algebraMap (Localization.Away (s k0)) (Localization.Away (s k0)) (algebraMap S (Localization.Away (s k0)) q₀) =
      algebraMap S (Localization.Away (s k0)) q₀ from rfl] at hc0
    rw [hc0, comp_one']
  choose N hN using h2
  let N₂ := Finset.univ.sup N
  refine ⟨s k0 ^ N₂ * q₀, p.primeCompl.mul_mem (p.primeCompl.pow_mem hk0 N₂) hq₀, ?_⟩
  refine tan_ext_cover s hs fun k => ?_
  rw [comp_one', res_scale, Algebra.ofId_apply, map_mul, map_pow, ← scale_scale,
    scale_pow_mono _ (Finset.le_sup (f := N) (Finset.mem_univ k)) (hN k), comp_one']

end Prime

end ReciprocityTheory.ChartRestriction.G.Chart
