import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import GroundTheory.GlobalFields.ExistenceTheorem.PowerIndex

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem index_range_eq_card_ker {T : Type*} [CommGroup T] [Finite T] (f : T →* T) :
    f.range.index = Nat.card f.ker := by
  have h1 := Subgroup.card_mul_index f.range
  have h2 := Subgroup.card_mul_index f.ker
  have hk : f.ker.index = Nat.card f.range := by
    show Nat.card (T ⧸ f.ker) = _
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hk] at h2
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have h3 : Nat.card f.range * f.range.index = Nat.card f.range * Nat.card f.ker := by
    rw [h1, ← h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos h3

private theorem mem_unit_of_pow_mem {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {p : ℕ}
    (hp : p ≠ 0) {b : Kˣ} (hb : b ^ p ∈ S.unit K) : b ∈ S.unit K := by
  intro v hv
  have h := hb v hv
  rw [Units.val_pow_eq_pow_val, map_pow] at h
  simpa [hp] using h

private theorem powK_subgroupOf {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) {p : ℕ}
    (hp : p ≠ 0) : (powK K p).subgroupOf (S.unit K) = (powMonoidHom p : S.unit K →* S.unit K).range := by
  ext x
  rw [Subgroup.mem_subgroupOf, powK.eq_1, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    rw [powMonoidHom_apply] at hb
    have hbS : b ∈ S.unit K := mem_unit_of_pow_mem hp (by rw [hb]; exact x.2)
    refine ⟨⟨b, hbS⟩, ?_⟩
    apply Subtype.ext
    simpa using hb
  · rintro ⟨c, hc⟩
    refine ⟨c.1, ?_⟩
    rw [← hc]
    simp

private theorem card_ker_eq {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n] :
    Nat.card (powMonoidHom n : CommGroup.torsion (S.unit K) →* CommGroup.torsion (S.unit K)).ker =
      Nat.card (rootsOfUnity n K) := by
  have hfin : ∀ ζ : rootsOfUnity n K, IsOfFinOrder (ζ : Kˣ) := fun ζ =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, (mem_rootsOfUnity _ _).mp ζ.2⟩
  have hS : ∀ ζ : rootsOfUnity n K, (ζ : Kˣ) ∈ S.unit K := fun ζ v _ =>
    GroundTheory.Global.SUnit.valuation_eq_one_of_isOfFinOrder (hfin ζ) v
  refine Nat.card_congr
    { toFun := fun t => ⟨t.1.1.1, (mem_rootsOfUnity _ _).mpr (by
        have h := congrArg (fun y : CommGroup.torsion (S.unit K) => ((y : S.unit K) : Kˣ))
          (MonoidHom.mem_ker.mp t.2)
        simpa using h)⟩
      invFun := fun ζ => ⟨⟨⟨ζ.1, hS ζ⟩, (CommGroup.mem_torsion _).mpr
          (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, Subtype.ext (by
            simpa using (mem_rootsOfUnity _ _).mp ζ.2)⟩)⟩,
        MonoidHom.mem_ker.mpr (Subtype.ext (Subtype.ext (by
            simpa using (mem_rootsOfUnity _ _).mp ζ.2)))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem UpperTheory.V.Kum.cardSUnit :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n], S.Finite → Nat.card (S.unit K ⧸ (powK K n).subgroupOf (S.unit K)) = n ^ (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 + Nat.card S) * Nat.card (rootsOfUnity n K) := by
  intro K _ _ S n _ hS
  haveI : Finite S := hS
  rw [← Subgroup.index_eq_card, powK_subgroupOf S (NeZero.ne n),
    GroundTheory.Global.index_range_powMonoidHom_eq_pow_mul (NeZero.ne n), GroundTheory.Global.SUnit.finrank_quotient_torsion,
    index_range_eq_card_ker, card_ker_eq, Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
