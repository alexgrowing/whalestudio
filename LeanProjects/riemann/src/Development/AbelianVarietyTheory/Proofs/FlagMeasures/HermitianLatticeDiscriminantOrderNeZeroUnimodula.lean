import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.DiscOrder

section General

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem idxN_eq_card (A B : Submodule R W) : idxN A B = Nat.card (A ⧸ B.comap A.subtype) := rfl

theorem idxN_mul {A B C : Submodule R W} (h1 : A ≤ B) (h2 : B ≤ C) :
    idxN B A * idxN C B = idxN C A :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr h1)
    ((Submodule.toAddSubgroup_le _ _).mpr h2)

theorem idxN_eq_one {A B : Submodule R W} : idxN A B = 1 ↔ A ≤ B :=
  AddSubgroup.relIndex_eq_one.trans (Submodule.toAddSubgroup_le _ _)

theorem exists_max_of_covBy {X Y : Submodule R W} (h : X ⋖ Y) :
    ∃ P : Ideal R, P.IsMaximal ∧ (∀ r : R, r ∈ P ↔ ∀ y ∈ Y, r • y ∈ X) ∧ idxN Y X = Nat.card (R ⧸ P) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 ((covBy_iff_quot_is_simple h.le).1 h)
  refine ⟨P, hP, fun r => ⟨fun hr y hy => ?_, fun hr => ?_⟩, by rw [idxN_eq_card]; exact Nat.card_congr e.toEquiv⟩
  · have : r • (Submodule.Quotient.mk ⟨y, hy⟩ : Y ⧸ X.comap Y.subtype) = 0 := by
      apply e.injective
      rw [map_smul, map_zero]
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective P (e (Submodule.Quotient.mk ⟨y, hy⟩))
      rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact P.mul_mem_right a hr
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
    have h0 : r • e.symm (Submodule.Quotient.mk 1) = 0 := by
      rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hr y y.2
    rw [← map_smul, EmbeddingLike.map_eq_zero_iff, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at h0
    simpa using h0

theorem exists_covBy {X Y : Submodule R W} (hY : Y.FG) (h : X < Y) : ∃ Z, X ≤ Z ∧ Z ⋖ Y := by
  have := CompleteLattice.Iic_coatomic_of_compact_element ((Submodule.fg_iff_compact Y).1 hY)
  rcases eq_top_or_exists_le_coatom (⟨X, h.le⟩ : Set.Iic Y) with e | ⟨Z, hZ, hle⟩
  · exact absurd (congrArg Subtype.val e) h.ne
  · exact ⟨Z.1, hle, (covBy_iff_coatom_Iic Z.2).2 hZ⟩

end General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in

theorem idxN_ne_zero {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X) (hY : Y.FG) :
    idxN Y X ≠ 0 := by
  obtain ⟨d, hd, hdY⟩ := indexBasic_denom (nonZeroDivisors (𝓞 K)) Y X hY
    (by rw [indexBasic_locS_top (K := K) X hX.span_eq_top]; exact le_top)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  have hn : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
  have : Module.Finite (𝓞 K) Y := Module.Finite.iff_fg.mpr hY
  have : Module.Finite ℤ (Y ⧸ X.comap Y.subtype) := Module.Finite.trans (𝓞 K) _
  have : Finite (Y ⧸ X.comap Y.subtype) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (X.comap Y.subtype) q
    refine ⟨⟨(Ideal.absNorm (Ideal.span {d}) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩, ?_⟩
    change (Ideal.absNorm (Ideal.span {d}) : ℤ) • Submodule.mkQ (X.comap Y.subtype) y = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (Ideal.absNorm (Ideal.span {d}) : ℤ) • (y : V) ∈ X
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 K), ← hc, mul_smul]
    exact X.smul_mem c (hdY y y.2)
  rw [idxN_eq_card]
  exact Nat.card_pos.ne'

omit [StarRing K] [FiniteDimensional K V] in
theorem lattice_between {X Y Z : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X)
    (hY : Submodule.IsLattice K Y) (h1 : X ≤ Z) (h2 : Z ≤ Y) : Submodule.IsLattice K Z :=
  Submodule.IsLattice.of_le_of_isLattice_of_fg K h1 (hY.fg.of_le h2)

variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn

theorem dual_covBy {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X)
    (hY : Submodule.IsLattice K Y) (hc : X ⋖ Y) : dual h Y ⋖ dual h X := by
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  have an := (dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).1
  refine ⟨lt_of_le_of_ne (an _ _ hc.le) fun e => hc.ne ?_, fun Z h1 h2 => ?_⟩
  · rw [← (dl X hX).2.1, ← e, (dl Y hY).2.1]
  · have hZ := lattice_between (dl Y hY).1 (dl X hX).1 h1.le h2.le
    have a1 := an _ _ h1.le
    have a2 := an _ _ h2.le
    rw [(dl Y hY).2.1] at a1
    rw [(dl X hX).2.1] at a2
    rcases hc.eq_or_eq a2 a1 with e | e
    · exact h2.ne (by rw [← e, (dl Z hZ).2.1])
    · exact h1.ne (by rw [← e, (dl Z hZ).2.1])

theorem idxN_dual_of_covBy {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X)
    (hY : Submodule.IsLattice K Y) (hc : X ⋖ Y) : idxN (dual h X) (dual h Y) = idxN Y X := by
  obtain ⟨P, hP, hPm, hPi⟩ := exists_max_of_covBy hc
  obtain ⟨Q, hQ, hQm, hQi⟩ := exists_max_of_covBy (dual_covBy h hs hn hX hY hc)
  set σ := locBasic_sigma (genusCovol_hinj (K := K)) star_algebraMap_ringOfIntegers_mem_range with hσ
  have hσσ : ∀ r, σ (σ r) = r := fun r => genusCovol_hinj (by
    rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])
  let e : 𝓞 K ≃+* 𝓞 K := RingEquiv.ofBijective σ (Function.Involutive.bijective hσσ)
  have hle : P ≤ Q.comap σ := by
    intro r hr
    rw [Ideal.mem_comap, hQm]
    intro x hx
    rw [dualBasic_mem_dual] at hx ⊢
    intro y hy
    have := hx _ ((hPm r).1 hr y hy)
    rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range] at this
    rw [genusBasic_hsmul_right]
    exact this
  have hPQ : P = Q.comap σ := hP.eq_of_le (Ideal.comap_ne_top σ hQ.ne_top) hle
  have hm : Q = P.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [hPQ]
    exact (Ideal.map_comap_of_surjective σ e.surjective Q).symm
  rw [hPi, hQi]
  exact (Nat.card_congr (Ideal.quotientEquiv P Q e hm).toEquiv).symm

theorem idxN_dual {X : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X) : ∀ (n : ℕ)
    (Y : Submodule (𝓞 K) V), Submodule.IsLattice K Y → X ≤ Y → idxN Y X = n →
    idxN (dual h X) (dual h Y) = n := by
  have an := (dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hY hle hi
  rcases hle.eq_or_lt with rfl | hlt
  · rw [← hi, idxN_eq_one.2 le_rfl, idxN_eq_one.2 le_rfl]
  obtain ⟨Z, hXZ, hc⟩ := exists_covBy hY.fg hlt
  have hZ := lattice_between hX hY hXZ hc.le
  have m1 := idxN_mul hXZ hc.le
  have n1 := idxN_ne_zero hX hZ.fg
  have n2 := idxN_ne_zero hZ hY.fg
  have n3 : idxN Y Z ≠ 1 := fun e => hc.lt.not_ge (idxN_eq_one.1 e)
  have hlt' : idxN Z X < n := by
    rw [← hi, ← m1]
    exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero n1) (by omega)
  rw [← idxN_mul (an _ _ hc.le) (an _ _ hXZ), ih _ hlt' Z hZ hXZ rfl, idxN_dual_of_covBy h hs hn hZ hY hc,
    ← hi, ← m1, mul_comm]

end GlobalTheory.Mass.DiscOrder

namespace GlobalTheory.Mass.DiscOrder

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → discN h M ≠ 0 ∧ (discN h M = 1 ↔ IsUnimodular h M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → idxN M' M ≠ 0 ∧ discN h M = discN h M' * idxN M' M ^ 2) ∧ (∀ N ∈ genus h M, IsIntLat h N ∧ discN h N = discN h M) ∧ (∀ P : Ideal (𝓞 K), P.IsMaximal → ((discN h M : ℕ) : 𝓞 K) ∉ P → IsUnimodularAt h P M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P M → loc (K := K) P M = loc (K := K) P M') := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hn M hM
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨an, -, -, hint, huni⟩ := dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have hMd := (hint M).1 hM.2
  have h0 : ∀ N, IsIntLat h N → discN h N ≠ 0 := fun N hN => idxN_ne_zero hN.1 (dl N hN.1).1.fg
  refine ⟨h0 M hM, ?_, fun M' hM' hle => ⟨idxN_ne_zero hM.1 hM'.1.fg, ?_⟩, fun N hN => ?_,
    fun P hP hd => ?_, fun M' hM' hle P hP hu => ?_⟩
  · rw [huni, discN, idxN_eq_one]
    exact ⟨fun e => ⟨hM.2, e⟩, fun e => e.2⟩
  · have hMd' := (hint M').1 hM'.2
    rw [discN, discN, ← idxN_mul (hle.trans hMd') (an _ _ hle), ← idxN_mul hle hMd',
      idxN_dual h hs hn hM.1 _ M' hM'.1 hle rfl]
    ring
  · have hNi : IsIntLat h N := ⟨hN.1,
      (((genusBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).2.2 M N hM.1.fg hN.1.fg hN.2).2).1 hM.2⟩
    refine ⟨hNi, genusCovol_lemmaS _ M (dual h M) N (dual h N) hMd ((hint N).1 hNi.2) rfl (h0 M hM)
      (h0 N hNi) fun P hP => ?_⟩
    obtain ⟨g, hg, hgL⟩ := hN.2 P hP
    have hle := locBasic_hcompl_le (K := K) P
    have key : ∀ A B : Submodule (𝓞 K) V, gmap g (loc (K := K) P A) = loc (K := K) P B →
        gmap g (locS P.primeCompl A) = locS P.primeCompl B := by
      intro A B e
      rw [← genusCovol_locS_locS hle A, gmap_locS_comm]
      change locS P.primeCompl (gmap g (loc (K := K) P A)) = _
      rw [e]
      exact genusCovol_locS_locS hle B
    obtain ⟨a1, a2, -, -, a5⟩ := isomAct (𝓞 K) K V h g hg M
    have b1 := (ld (gmap g M) (a5.2 hM.1).fg).1 P hP.isPrime
    have b2 := (ld N hN.1.fg).1 P hP.isPrime
    refine ⟨_, g.injective, genusCovol_addData g _ _ (key _ _ hgL), genusCovol_addData g _ _ (key _ _ ?_)⟩
    rw [b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (dual h M)).2.1 P]
  · have b := (ld M hM.1.fg).1 P hP.isPrime
    rw [IsUnimodularAt, b.2, ← b.1]
    refine le_antisymm ((locBasic_locS_mono _ fun x hx => ?_).trans (locBasic_locS_idem _ M).le)
      (locBasic_locS_mono _ hMd)
    refine ⟨(discN h M : 𝓞 K), Submonoid.subset_closure ⟨hd, fun t ht => ?_⟩, ?_⟩
    · have : t = (discN h M : 𝓞 K) := genusCovol_hinj (by rw [ht]; simp)
      rwa [this]
    · rw [Nat.cast_smul_eq_nsmul]
      have := AddSubgroup.nsmul_index_mem (H := M.toAddSubgroup.addSubgroupOf (dual h M).toAddSubgroup) ⟨x, hx⟩
      exact this
  · have b := (ld M hM.1.fg).1 P hP.isPrime
    rw [IsUnimodularAt, b.2, ← b.1] at hu
    refine le_antisymm (locBasic_locS_mono _ hle) ?_
    rw [← hu]
    exact locBasic_locS_mono _ (((hint M').1 hM'.2).trans (an _ _ hle))

end GlobalTheory.Mass.DiscOrder
