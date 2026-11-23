import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ULAPf
open LateralTheory.E.t_E3Cut

theorem spS_of_integral_injective {C D : CommRingCat.{0}} (g : C ⟶ D) (hi : g.hom.IsIntegral)
    (hj : Function.Injective g.hom) : SpS g := by
  intro r hr
  letI := g.hom.toAlgebra
  have : Algebra.IsIntegral C D := ⟨hi⟩
  have hk : RingHom.ker (algebraMap C D) ≤ r := by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap C D)).1 hj]; exact bot_le
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral r ⊥ (by rw [← RingHom.ker_eq_comap_bot (algebraMap C D)]; exact hk)
  exact ⟨Q, hQ, hQc⟩

theorem SpS.comp {C D E : CommRingCat.{0}} {f : C ⟶ D} {g : D ⟶ E} (hf : SpS f) (hg : SpS g) : SpS (f ≫ g) := by
  intro r hr
  obtain ⟨Q0, hQ0, hQ0c⟩ := hf r hr
  obtain ⟨Q, hQ, hQc⟩ := hg Q0 hQ0
  exact ⟨Q, hQ, by rw [CommRingCat.hom_comp, ← Ideal.comap_comap, hQc, hQ0c]⟩

theorem ULA_of (hS : Stalk) (hP : AlgResProps) (hE : AICExt) (hD : DomCover) (hL : LocIE) (hU : ULAStalk) : ULA := by
  intro H q _ i A X h hq hA hX hIE hloc C c hc
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP
  refine hS H q i (pC A ≫ h) hq (fun _ c => AlgRes c) ?_ ?_ ?_ C c hc
  · intro C D E Z c f g u v hpo _ hf hg
    have hv : AlgRes v := p3 f g u v hpo (p2 c f hf)
    have := p1 (c ≫ g) v hg hv
    rw [hpo.w, ← Category.assoc]; exact this
  · intro C D c f hc hf
    exact p1 c f hc (p4 f hf)
  · intro C c hc
    obtain ⟨D0, g0, hg0i, hg0j, hg0a⟩ := hE C
    obtain ⟨D, g1, hg1i, hg1s, hg1d⟩ := hD D0 hg0a
    have hgi : (g0 ≫ g1).hom.IsIntegral := by
      rw [CommRingCat.hom_comp]; exact RingHom.IsIntegral.trans _ _ hg0i hg1i
    refine ⟨D, g0 ≫ g1, hgi, SpS.comp (spS_of_integral_injective g0 hg0i hg0j) hg1s,
      p1 c (g0 ≫ g1) hc (p5 _ hgi), ?_⟩
    intro r hr
    have := hr
    obtain ⟨hdom, haic⟩ := hg1d r
    let o : D ⟶ CommRingCat.of (Localization.AtPrime r) := CommRingCat.ofHom (algebraMap D _)
    have ho : AlgRes o := p6 D (Localization.AtPrime r) r.primeCompl
    refine ⟨CommRingCat.of (Localization.AtPrime r), o, IsLocalRing.maximalIdeal _,
      hL D (Localization.AtPrime r) r.primeCompl, inferInstance,
      IsLocalization.AtPrime.comap_maximalIdeal _ r, ?_⟩
    haveI : IsDomain (CommRingCat.of (Localization.AtPrime r)) := hdom
    haveI : IsLocalRing (CommRingCat.of (Localization.AtPrime r)) :=
      inferInstanceAs (IsLocalRing (Localization.AtPrime r))
    exact hU H q i h hq hA hX hIE hloc _ (c ≫ (g0 ≫ g1) ≫ o) haic
      (p1 c _ hc (p1 _ o (p5 _ hgi) ho))

end LateralTheory.E.ULAPf

end
