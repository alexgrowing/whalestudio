import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsRegularSectionGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecialFibreClosedSpecializationStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.DegreeZeroCurvePositive
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.ProperZeroNumerical

theorem subset_of_specializes {T : Type} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T] [QuasiSober T]
    {Z V : Set T} (hZ : IsClosed Z) (hc : IsPreconnected Z) (hV : IsOpen V) (hne : (Z ∩ V).Nonempty)
    (hs : ∀ y x : T, y ∈ Z → y ∈ V → y ⤳ x → x ∈ V) : Z ⊆ V := by
  have hcl : IsClosed (Z ∩ V) := by
    obtain ⟨S, hfin, hScl, hSirr, hU⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
    have e : Z ∩ V = ⋃ t ∈ {t ∈ S | (t ∩ V).Nonempty}, t := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨hx, hxV⟩
        rw [hU] at hx
        obtain ⟨t, ht, hxt⟩ := hx
        exact ⟨t, ⟨ht, x, hxt, hxV⟩, hxt⟩
      · rintro ⟨t, ⟨ht, htV⟩, hxt⟩
        have hsub : t ⊆ Z := by rw [hU]; exact Set.subset_sUnion_of_mem ht
        obtain ⟨y, hy⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
        exact ⟨hsub hxt, hs y x (hsub hy.mem) ((hy.mem_open_set_iff hV).2 htV) (hy.specializes hxt)⟩
    rw [e]
    exact (hfin.subset fun t ht => ht.1).isClosed_biUnion fun t ht => hScl t ht.1
  intro x hx
  by_contra hxV
  obtain ⟨z, hz, hzV, hz'⟩ := hc V (Z ∩ V)ᶜ hV hcl.isOpen_compl
    (fun w hw => by
      by_cases h : w ∈ V
      · exact Or.inl h
      · exact Or.inr fun h' => h h'.2) hne ⟨x, hx, fun h => hxV h.2⟩
  exact hz' ⟨hz, hzV⟩

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unit_mul {p : Cpt ξ} {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem unit_inv {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unit_pow {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) (n : ℕ) : unitAt ξ p (a ^ n) :=
  ⟨pow_ne_zero n ha.1, pow_mem ha.2.1 n, by rw [← inv_pow]; exact pow_mem ha.2.2 n⟩

theorem unit_change {L : Lat ξ Ω} {p : Cpt ξ} {σ π e f : Ω} {M : ℕ} (he : L.IsGenAt p e) (hf : L.IsGenAt p f)
    (h : unitAt ξ p (π / (σ / f) ^ M)) : unitAt ξ p (π / (σ / e) ^ M) := by
  rw [CurvePositivity.change_gen σ π e f M hf.1]
  exact unit_mul h (unit_pow (ProjectiveLinePlaces.unitAt_div he hf) M)

theorem exists_local_gen {L : Lat ξ Ω} (h : L.IsVB 1 ⊤) (p : Cpt ξ) :
    ∃ (U : X.Opens) (e : Ω), p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → L.IsGenAt q e := by
  obtain ⟨U, hp, b, -, hb⟩ := h p (Set.mem_univ p)
  refine ⟨U, b 0, hp, fun q hq => ?_⟩
  obtain ⟨hli, hspan⟩ := hb q (Set.mem_univ q) hq
  refine ⟨hli.ne_zero 0, ?_⟩
  rw [hspan]
  congr 1
  ext x
  simp [eq_comm]

end PositivityTheory.Xgn.ProperZeroNumerical

open PositivityTheory.Xgn.ProperZeroNumerical in
theorem PositivityTheory.Xgn.normal_proper_line_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → NumTrivMod L (algebraMap O Ω ϖ) → (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, OrderAt L σ (algebraMap O Ω ϖ) M a p := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hconn L σ hvb hnum hgen
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian X := { }
  obtain ⟨M, a, hM, hreg, p₀, hp₀, -, e₀, c₀, he₀, hL₀, hσ₀, hu₀⟩ :=
    exists_regular_section_generator X Ω ξ O s ϖ hϖ hinj hs hg hn hconn.1 L σ hvb hgen
  have hunit : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal :=
    fun p o => (ConstReg.regular_const X Ω ξ O s hs p o).2 hg
  set π : Ω := algebraMap O Ω ϖ ^ a with hπ
  let Good : Cpt ξ → Prop := fun p => ∃ e, L.IsGenAt p e ∧ unitAt ξ p (π / (σ / e) ^ M)
  let V : Set X := ⋃₀ {W | IsOpen W ∧ ∀ q : Cpt ξ, q.1 ∈ W → Good q}
  have hVo : IsOpen V := isOpen_sUnion fun W hW => hW.1
  have hV : ∀ q : Cpt ξ, q.1 ∈ V ↔ Good q := by
    intro q
    constructor
    · rintro ⟨W, hW, hq⟩
      exact hW.2 q hq
    · rintro ⟨e, he, hu⟩
      obtain ⟨U, b, hqU, hb⟩ := exists_local_gen hvb q
      obtain ⟨U', hqU', hU'⟩ := (regAt_unitAt_open X Ω ξ q _).2 (unit_change (hb q hqU) he hu)
      exact ⟨(U : Set X) ∩ U', ⟨U.isOpen.inter U'.isOpen, fun r hr => ⟨b, hb r hr.1, hU' r hr.2⟩⟩, hqU, hqU'⟩
  have hZ : IsClosed (zeroSet ξ (algebraMap O Ω ϖ)) := by
    have e : zeroSet ξ (algebraMap O Ω ϖ) =
        closure {genPt ξ} ∩ s ⁻¹' (PrimeSpectrum.zeroLocus ({ϖ} : Set O)) := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨specializes_iff_mem_closure.1 h1,
          Set.singleton_subset_iff.2 (not_not.1 fun h => h2 ((hunit ⟨x, h1⟩ ϖ).2 h))⟩
      · rintro ⟨h1, h2⟩
        exact ⟨specializes_iff_mem_closure.2 h1, fun h =>
          (hunit ⟨x, specializes_iff_mem_closure.2 h1⟩ ϖ).1 h (Set.singleton_subset_iff.1 h2)⟩
    rw [e]
    exact isClosed_closure.inter ((PrimeSpectrum.isClosed_zeroLocus _).preimage s.continuous)
  have hsub : zeroSet ξ (algebraMap O Ω ϖ) ⊆ V := by
    refine subset_of_specializes hZ hconn.2 hVo ⟨p₀.1, ⟨p₀.2, hp₀⟩, (hV p₀).2 ⟨e₀, ⟨he₀, hL₀⟩, ?_⟩⟩ ?_
    · have e1 : σ / e₀ = c₀ := by rw [hσ₀, smul_eq_mul, mul_div_cancel_right₀ _ he₀]
      rw [e1, ← inv_div]
      exact unit_inv hu₀
    · rintro y x ⟨hy, hyn⟩ hyV hyx
      obtain ⟨x', hx', hcl⟩ :=
        (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton ⟨x, subset_closure rfl⟩
      have hxx : x ⤳ x' := specializes_iff_mem_closure.2 hx'
      refine hxx.mem_open hVo ?_
      have hyx' : y ⤳ x' := hyx.trans hxx
      let q : Cpt ξ := ⟨x', hy.trans hyx'⟩
      obtain ⟨U, b, hqU, hb⟩ := exists_local_gen hvb q
      refine (hV q).2 ⟨b, hb q hqU, ?_⟩
      by_contra hnu
      obtain ⟨e, he, hue⟩ := (hV ⟨y, hy⟩).1 hyV
      obtain ⟨Γ, i, -, hη, hz⟩ := GlobalTheory.T.special_fibre_closed_specialization X Ω ξ O s ϖ hϖ hinj hs hg ⟨y, hy⟩ q (π / (σ / b) ^ M) hyn hyx' hcl
        (hreg q b (hb q hqU)) (unit_change (hb ⟨y, hy⟩ (hyx'.mem_open U.isOpen hqU)) he hue) hnu
      have hq : q = ⟨centre (Γ.z i), Γ.z_spec i⟩ := Subtype.ext hz.symm
      have hηU : centre Γ.η ∈ U := (Γ.generic_centre_specializes i).mem_open U.isOpen (by rw [hz]; exact hqU)
      apply hnu
      have hbq := hb q hqU
      rw [hq] at hbq ⊢
      exact PositivityTheory.Xgn.degree_zero_curve_positive X Ω ξ O s _ L σ π M Γ hg hvb hM (hnum Γ) hreg
        (fun e' he' => unit_change he' (hb ⟨centre Γ.η, Γ.η_spec⟩ hηU) hη) i (Γ.z_spec i) b hbq
  refine ⟨M, a, hM, fun p => ?_⟩
  by_cases hu : unitAt ξ p (algebraMap O Ω ϖ)
  · have hp : p ∈ genFibre O ξ := by
      intro o ho
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ
      rw [map_mul, map_pow]
      refine unit_mul ((hunit p _).2 fun h => ?_) (unit_pow hu n)
      exact (s p.1).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
    refine ⟨σ, 1, (hgen p hp).1, (hgen p hp).2, (one_smul _ _).symm, ?_⟩
    rw [one_pow, one_div]
    refine unit_inv ⟨zpow_ne_zero a hu.1, ZLat.zpow_mem_regAt hu a, ?_⟩
    rw [← zpow_neg]
    exact ZLat.zpow_mem_regAt hu _
  · obtain ⟨e, he, hue⟩ := (hV p).1 (hsub ⟨p.2, hu⟩)
    refine ⟨e, σ / e, he.1, he.2, ?_, ?_⟩
    · rw [smul_eq_mul, div_mul_cancel₀ _ he.1]
    · rw [← inv_div]
      exact unit_inv hue
