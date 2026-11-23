import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionMap

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeTateLevel

open GlobalTheory.KernelNoTorsion GlobalTheory.TangentPow GlobalTheory.TorsionCharacter GlobalTheory.HTLat.OmegaRank GlobalTheory.GmPoints
open GlobalTheory.CompHt.FormalChar GlobalTheory.RaynaudTorsionMap GlobalTheory.HodgeTateImage

theorem exists_lift_of_nilpotent {O : Type} [CommRing O] {H Y : Over (Sp O)} (j : H ⟶ Y) [IsOpenImmersion j.left]
    {R : Type} [CommRing R] [Algebra O R] (I : Ideal R) (hI : IsNilpotent I) (g : specO O R ⟶ Y)
    (z : specO O (R ⧸ I) ⟶ H) (hz : z ≫ j = ptMap (Ideal.Quotient.mkₐ O I) ≫ g) :
    ∃ w : specO O R ⟶ H, w ≫ j = g := by
  have hr : Set.range g.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      obtain ⟨k, hk⟩ := hI
      intro a ha
      refine y.isPrime.mem_of_pow_mem k ?_
      have h0 : a ^ k ∈ I ^ k := Ideal.pow_mem_pow ha k
      rw [hk] at h0
      rw [show a ^ k = 0 from h0]
      exact Ideal.zero_mem _
    obtain ⟨y', rfl⟩ := hy
    exact ⟨z.left y', congrArg (fun q => q.left y') hz⟩
  refine ⟨Over.homMk (IsOpenImmersion.lift j.left g.left hr) ?_,
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w]

theorem hom_ext_open {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G] {N : ℕ} {H T : Over (Sp O)}
    (j : H ⟶ torsion G N) [IsOpenImmersion j.left] {w w' : T ⟶ H}
    (h : w ≫ j ≫ torsion.ι G N = w' ≫ j ≫ torsion.ι G N) : w = w' := by
  have e : w ≫ j = w' ≫ j := torsion_hom_ext (by rw [Category.assoc, Category.assoc, h])
  refine Over.OverMorphism.ext ?_
  rw [← cancel_mono j.left]
  exact congrArg (·.left) e

theorem exists_lift_near_unit {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G] {N : ℕ} {H : Over (Sp O)}
    {j : H ⟶ torsion G N} (hj : IsOpenFiniteFlatSubgroup G N j) {R : Type} [CommRing R] [Algebra O R]
    (I : Ideal R) (hI : IsNilpotent I) (g : specO O R ⟶ G) (hg : g ^ N = 1)
    (h1 : ptMap (Ideal.Quotient.mkₐ O I) ≫ g = 1) : ∃ w : specO O R ⟶ H, w ≫ j ≫ torsion.ι G N = g := by
  haveI := hj.1
  obtain ⟨z, hz⟩ := hj.2.2.2.1 (specO O (R ⧸ I))
  obtain ⟨w, hw⟩ := exists_lift_of_nilpotent j I hI (torsionLift g hg) z (torsion_hom_ext (by
    rw [Category.assoc, Category.assoc, hz, torsionLift_ι, h1]))
  exact ⟨w, by rw [← Category.assoc, hw, torsionLift_ι]⟩

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem exists_corr {N : ℕ} {H : Over (Sp O)} {j : H ⟶ torsion P.G N} (hj : IsOpenFiniteFlatSubgroup P.G N j)
    {A : Type} [CommRing A] [Algebra O A] (hc : IsAdicComplete (Ideal.span {(p : A)}) A) (I : Ideal A) {k : ℕ}
    (hI : I ^ k ≤ Ideal.span {(p : A)}) (x : specO O A ⟶ P.Gt) (hx : x ^ N = 1)
    (h1 : ptMap (Ideal.Quotient.mkₐ O I) ≫ x = 1) :
    ∃ Q : specO O A ⟶ H, Corr P x (Q ≫ j ≫ torsion.ι P.G N) := by
  haveI := P.isLocalRing
  haveI := hj.1
  haveI := hj.2.1
  haveI := hj.2.2.1
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := exists_finite_free H
  have ex : ∀ m : ℕ, ∃ w : specO O (A ⧸ Ideal.span {(p : A) ^ m}) ⟶ H,
      w ≫ j ≫ torsion.ι P.G N = P.cmp _ (nilpR m) (ptMap (redR p O A m) ≫ x) := fun m => by
    let θ := redR p O A m
    refine exists_lift_near_unit hj (I.map θ) ⟨k * m, eq_bot_iff.2 ?_⟩ _ ?_ ?_
    · rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap, pow_mul]
      refine (Ideal.pow_right_mono hI _).trans fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ?_
      rwa [Ideal.span_singleton_pow] at ha
    · rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one]
    · have h' : IsNilpotent (p : (A ⧸ Ideal.span {(p : A) ^ m}) ⧸ I.map θ) := by
        simpa using (nilpR (p := p) (R := A) m).map (Ideal.Quotient.mk (I.map θ))
      have e1 : (Ideal.Quotient.mkₐ O (I.map θ)).comp θ =
          (Ideal.quotientMapₐ (I.map θ) θ Ideal.le_comap_map).comp (Ideal.Quotient.mkₐ O I) := rfl
      rw [← P.cmp_nat _ _ (nilpR m) h', ← Category.assoc, ptMap_comp_ptMap, e1, ← ptMap_comp_ptMap, Category.assoc, h1,
        MonObj.comp_one, map_one]
  choose w hw using ex
  obtain ⟨Q, hQ⟩ := exists_lim_affine hc (fun m => w m ≫ e.inv) fun m => by
    rw [← Category.assoc]
    congr 1
    apply hom_ext_open j
    rw [Category.assoc, hw, hw, ← P.cmp_nat _ _ (nilpR (m + 1)) (nilpR m), ← Category.assoc, factor_redR]
  refine ⟨Q ≫ e.hom, fun m => ?_⟩
  rw [Category.assoc, ← Category.assoc, hQ, Category.assoc, Iso.inv_hom_id_assoc, hw]

theorem weil_mul_swap [IsAlgClosed C] [CharZero C] {A : Out.PolAV (Sp C)} {k : ℕ} (hk : 1 ≤ k) {z s : ChTor.Pts A.A}
    (hz : z ^ k = 1) (hs : s ^ k = 1) : weil A k z s * weil A k s z = 1 := by
  have hzs : (z * s) ^ k = 1 := by rw [mul_pow, hz, hs, _root_.mul_one]
  have h := weil_self hk hzs
  rwa [weil_mul_left hk hz hs hzs, weil_mul_right hk hz hs hz, weil_mul_right hk hz hs hs, weil_self hk hz,
    weil_self hk hs, _root_.one_mul, _root_.mul_one] at h

theorem levelReduction : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), LevelReduction P := by
  intro p hp C _ _ _ v O _ _ _ hO _ _ _ Λ _ _ P n H j hj t χ _ hχ R _ _ hR x w hw
  have hv := P.integers
  have hp0 := hp.out.ne_zero
  have hN := one_le_ppow p n
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI := ValuationRing.of_integers v hv
  haveI := (P.finite_flat _ hN).1
  haveI := (P.finite_flat _ hN).2
  haveI := hj.1
  obtain ⟨A, _, _, X, I, m, _, _, hsep, hX, hI, hl⟩ := exists_connected_part hv hp0 P.Gt (p ^ n) (pow_ne_zero n hp0)
  have hAc : IsAdicComplete (Ideal.span {(p : A)}) A := by
    have := FlatComplete.isAdicComplete_of_finite_flat _ _ hO A
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  obtain ⟨Q, hQ⟩ := exists_corr P hj hAc I hI (X ≫ torsion.ι P.Gt (p ^ n))
    (by rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]) hX
  have e : (unitOf (Q ≫ χ) : A) * (unitOf (X ≫ (P.weilChar t).χ n) : A) = 1 := hsep _ _ fun φ => hv.hom_inj (by
    have h1 : P.toG ((ptMap φ ≫ X) ≫ torsion.ι P.Gt (p ^ n)) = (ptMap φ ≫ Q) ≫ j ≫ torsion.ι P.G (p ^ n) :=
      P.hom_ext_red fun k => by
        rw [P.red_toG, Category.assoc (ptMap φ), Category.assoc (ptMap φ)]
        exact (hQ.comp φ k).symm
    have h2 := hχ (ptMap φ ≫ Q) _ (h1 ▸ (P.eq_toA_iff _ _).1 rfl)
    rw [map_mul, map_mul, ← unitOf_ptMap, ← unitOf_ptMap, ← Category.assoc, ← Category.assoc, h2,
      P.isWeilChar_weilChar, ← Units.val_mul, weil_mul_swap hN (t.lev_pow n) (P.toA_pow _), map_one, map_one,
      Units.val_one])
  have hn := isNilpotent_dual hR
  have hpow : (ptMap (dualBC (Algebra.ofId O R)) ≫ x.1) ^ p ^ n = 1 := (P.cmp _ hn).injective (by
    rw [map_pow, ← hw, map_one, ← MonObj.comp_pow, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one, MonObj.comp_one])
  obtain ⟨ψ, hψ⟩ := hl R (torsionLift _ hpow) (by rw [torsionLift_ι]; exact fst_bc R x)
  have hx : (ptMap ψ ≫ X) ≫ torsion.ι P.Gt (p ^ n) = ptMap (dualBC (Algebra.ofId O R)) ≫ x.1 := by
    rw [← hψ, torsionLift_ι]
  have hw' : w = ptMap ψ ≫ Q := hom_ext_open j (by
    rw [hw, ← hx, Category.assoc, cmp_of_corr P hQ, Category.assoc])
  have h3 := isAl_dlogTv (P.weilChar t) n R hR x _ hx
  have h4 := congrArg ψ e
  rw [map_mul, map_one, ← unitOf_ptMap, ← unitOf_ptMap, ← Category.assoc, ← Category.assoc, ← hw', h3] at h4
  have h5 : algebraMap O R ((alLeft P t).1 x) = -algebraMap O R ((dlogTv (P.weilChar t)).1 x) := by
    rw [← map_neg]
    rfl
  rw [h5]
  generalize algebraMap O R ((dlogTv (P.weilChar t)).1 x) = a at h4 ⊢
  have h6 : (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr a : DualNumber R) *
      (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (-a)) = 1 := by
    ext <;> simp
  rw [← _root_.mul_one (unitOf (w ≫ χ) : DualNumber R), ← h6, ← _root_.mul_assoc, h4, _root_.one_mul]

end GlobalTheory.HodgeTateLevel
