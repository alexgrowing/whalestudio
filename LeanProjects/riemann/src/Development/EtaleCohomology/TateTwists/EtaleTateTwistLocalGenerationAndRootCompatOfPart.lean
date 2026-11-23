import Development.EtaleCohomology.TateTwists.EtaleTensorPairingSectionsLocallyFiniteSums

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (a : Sec (tw q i) U),
    Loc U fun V g => Sec.res g a = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g a = c • twGen i ζ

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange : Prop :=
  ∀ (q : ℕ) [NeZero q] (j : ℤ),
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen j ζ) = twGen j (ζ.map g.appTop.hom)) ∧
    ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), Loc U fun _ g => ∃ c : ℕ, Sec.res g (twGen j ξ) = c • twGen j (ζ.map g.appTop.hom)

namespace LateralTheory.EtaleFoundations.GenIsoSurjPf
theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := by
  simp [Sec.res]

theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x := by
  simp [Sec.map]
end LateralTheory.EtaleFoundations.GenIsoSurjPf

open LateralTheory.EtaleFoundations.GenIsoSurjPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_hits_products_locally (hl : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator)
    (hr : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapHitsProductsLocally := by
  intro q _ i j k T μ hk φ hφ U a b
  refine loc_bind' (loc_mono' (loc_and' (hl q i U a) (hl q j U b)) fun V g hab => ?_)
  rcases hab with ⟨ha | ⟨ζ, c, ha⟩, hb | ⟨ξ, d, hb⟩⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res, ha]; simp⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res, ha]; simp⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res (F := tw q j), hb]; simp⟩
  · refine loc_mono' ((hr q j).2 V ζ ξ) fun W h ⟨e, he⟩ => ?_
    refine ⟨(c * (d * e)) • twGen k (ζ.map h.appTop.hom), ?_⟩
    rw [← res_res, ← res_res (F := tw q j), ha, hb, res_nsmul, res_nsmul, he, (hr q i).1, smul_smul,
      map_nsmul', map_nsmul', map_nsmul', map_nsmul', hφ]
    simp only [map_nsmul, LinearMap.smul_apply, smul_smul]
    ring_nf

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_surjective_of_local_and_root (hl : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator)
    (hr : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective :=
  LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_locally_surjective_of_pairs (LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_hits_products_locally hl hr)
