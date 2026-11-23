import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_quotDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Group G] (D : GDet n A G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G], D.IsCont (maximalIdeal A) → ∀ Z : Set (MonoidAlgebra A G), (∀ z ∈ Z, D.Kills z) → ∃ DE : Det n A (D.CHQuot Z), DE.IsCH ∧ DE.pull (D.toQuot Z) = D.toDet := by
  intro n A G _ _ _ _ D _ _ _ _ hc Z hZ
  set f := D.toQuot Z
  have hsurj : Function.Surjective f := RingCon.mkₐ_surjective _
  have hmem : ∀ x, x ∈ D.chBar Z → f x = 0 := by
    intro x hx
    have hr : (D.chBar Z).ringCon x 0 := (TwoSidedIdeal.rel_iff _ _ _).2 (by rwa [sub_zero])
    rw [← map_zero f]
    exact (RingCon.eq _).2 hr
  have hker : ∀ x, f x = 0 → x ∈ D.chBar Z := by
    intro x hx
    rw [← map_zero f] at hx
    have hr := (RingCon.eq _).1 hx
    simpa using (TwoSidedIdeal.rel_iff _ _ _).1 hr
  have hle : TwoSidedIdeal.span (D.CH ∪ Z) ≤ D.chBar Z := by
    unfold GDet.chBar closureIdeal
    refine le_iInf fun N => le_iInf fun H => fun y hy => ?_
    exact TwoSidedIdeal.mem_span_iff.1 hy _ fun z hz =>
      TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) (Or.inl (Or.inl hz))
  have hsub : D.CH ∪ Z ⊆ D.chBar Z := fun x hx =>
    hle (TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) hx)
  have hCHk : ∀ z ∈ D.CH, D.Kills z := by
    intro z hz
    have hz' : z ∈ D.toDet.CH := by
      rw [d_toDet_CH]
      exact TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) hz
    exact (d_toDet D z).2.2.2.1 ((d_ker _ z).1.1 (d_ch_ker _ hz'))
  have hK : ∀ x, f x = 0 → x ∈ D.toDet.ker := fun x hx =>
    (d_ker _ x).1.2 ((d_toDet D x).2.2.2.2
      (d_closed D (maximalIdeal A) hc (D.CH ∪ Z)
        (by
          rintro z (hz | hz)
          exacts [hCHk z hz, hZ z hz]) x (hker x hx)))
  obtain ⟨DE, hDE, -⟩ := d_factor D.toDet f hsurj hK
  refine ⟨DE, ?_, hDE⟩
  show DE.CH = ⊥
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := ((d_pull DE f).2.2.2 hsurj).2 y hy
    rw [hDE, d_toDet_CH] at hx
    rw [hmem x ((TwoSidedIdeal.mem_span_iff.1 hx) _ fun z hz => hsub (Or.inl hz))]
    exact TwoSidedIdeal.zero_mem _
  · intro hy
    rw [TwoSidedIdeal.mem_bot] at hy
    rw [hy]
    exact TwoSidedIdeal.zero_mem _
