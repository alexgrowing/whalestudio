import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IteratedWeightAtVanishingOrder
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WedgeDetNz

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

section LinAlg

theorem exists_minor_of_li {F : Type} [Field F] {ρ d : ℕ} (u : Fin ρ → Fin d → F) (hu : LinearIndependent F u) :
    ∃ J : Fin ρ → Fin d, (Matrix.of fun i k => u k (J i)).det ≠ 0 := by
  classical

  have hspan : Submodule.span F (Set.range fun l : Fin d => fun k : Fin ρ => u k l) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Matrix.rank_eq_finrank_span_cols (u : Matrix (Fin ρ) (Fin d) F)
    have h2 := Matrix.rank_eq_finrank_span_row (u : Matrix (Fin ρ) (Fin d) F)
    have h3 : Module.finrank F (Submodule.span F (Set.range u)) = ρ := by
      rw [finrank_span_eq_card hu, Fintype.card_fin]
    rw [Module.finrank_fin_fun]
    exact h1.symm.trans (h2.trans h3)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (K := F) (fun l : Fin d => fun k : Fin ρ => u k l)
  haveI : Finite κ := Finite.of_injective a ha
  haveI := Fintype.ofFinite κ
  have hcard : Fintype.card κ = ρ := by
    have h := finrank_span_eq_card hli
    rw [hsp, hspan, finrank_top, Module.finrank_fin_fun] at h
    exact h.symm
  let e : Fin ρ ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hrows : LinearIndependent F (fun i => (Matrix.of fun i k => u k ((a ∘ e) i)) i) :=
    hli.comp e e.injective
  have hU := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero

theorem exists_max_indep {A F : Type} [CommRing A] [Field F] [Algebra A F] {I : Type} [Finite I] {d : ℕ}
    (c : I → Fin d → A) :
    ∃ (ρ : ℕ) (e : Fin ρ → I) (J : Fin ρ → Fin d), (Matrix.of fun i k => c (e k) (J i)).det ≠ 0 ∧
      ∀ i0, ∃ a : Fin ρ → F, ∀ l, algebraMap A F (c i0 l) = ∑ k, a k * algebraMap A F (c (e k) l) := by
  classical
  haveI := Fintype.ofFinite I
  set v : I → Fin d → F := fun i l => algebraMap A F (c i l) with hv
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (K := F) v
  haveI : Finite κ := Finite.of_injective a ha
  haveI := Fintype.ofFinite κ
  let e0 : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hli' : LinearIndependent F (v ∘ (a ∘ e0)) := hli.comp e0 e0.injective
  obtain ⟨J, hJ⟩ := exists_minor_of_li (v ∘ (a ∘ e0)) hli'
  refine ⟨Fintype.card κ, a ∘ e0, J, ?_, ?_⟩
  · intro h
    apply hJ
    have hM : (algebraMap A F).mapMatrix (Matrix.of fun i k => c ((a ∘ e0) k) (J i)) =
        Matrix.of fun i k => (v ∘ (a ∘ e0)) k (J i) := by
      ext i k
      simp [hv]
    rw [← hM, ← RingHom.map_det, h, map_zero]
  · intro i0
    have hr : Set.range (v ∘ (a ∘ e0)) = Set.range (v ∘ a) := e0.surjective.range_comp (v ∘ a)
    have hmem : v i0 ∈ Submodule.span F (Set.range (v ∘ (a ∘ e0))) := by
      rw [hr, hsp]
      exact Submodule.subset_span (Set.mem_range_self i0)
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (R := F)).1 hmem
    refine ⟨b, fun l => ?_⟩
    simpa [hv, Finset.sum_apply, smul_eq_mul] using (congrFun hb l).symm

end LinAlg

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Transport

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

theorem jF_injective : Function.Injective (jF X la N) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hne
  obtain ⟨β, hβ⟩ := MvPolynomial.ne_zero_iff.mp hne
  have := addVal_le_vAdd X la N p β 0 hβ (by rw [map_zero, hp])
  rw [IsDiscreteValuationRing.addVal_zero] at this
  exact absurd (top_le_iff.mp this) (ENat.natCast_ne_top _)

theorem emb_smul_jF (a : B.KO) (F : X.Forms) :
    emb X la N (a • F) = jF X la N (MvPolynomial.C a) • emb X la N F := by
  rw [emb_smul, jF_C, algebraMap_smul (Kp X la N) (algebraMap B.KO (X.Kl la) a)]

theorem psi_eq_sum_coord (ka : WeightFamilies.Wt D j) {d : ℕ} (b : Basis (Fin d) B.KO (B.Cusp j ka))
    (p : MvPolynomial (Idx D j N) X.Forms) (zc : (Idx D j N →₀ ℕ) →₀ B.Cusp j ka)
    (h : ∀ β, X.inc ka (zc β) = p.coeff β) :
    psi X la N p = ∑ l, jF X la N (SizeBoundsAlt.polyOf (b.coord l) zc) • emb X la N (X.inc ka (b l)) := by
  rw [SizeBoundsAlt.polynomial_eq_sum_monomials (inc := fun w => (X.inc w).toAddMonoidHom) zc h, map_sum]
  have h1 : ∀ l, jF X la N (SizeBoundsAlt.polyOf (b.coord l) zc) =
      ∑ β ∈ zc.support, jF X la N (MvPolynomial.monomial β 1) * jF X la N (MvPolynomial.C (b.coord l (zc β))) := by
    intro l
    unfold SizeBoundsAlt.polyOf
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← map_mul, mul_comm, MvPolynomial.C_mul_monomial, mul_one]
  simp only [h1, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [psi_monomial]
  show jF X la N (MvPolynomial.monomial β 1) • emb X la N (X.inc ka (zc β)) = _
  conv_lhs => rw [← b.sum_repr (zc β)]
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, emb_smul_jF, smul_smul]
  rfl

end Transport

section Coeff

theorem exists_zc (X : PJ D B P j) {wL w0 : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → B.Cusp j wL)
    (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j w0) :
    ∃ z : ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j (SizeBoundsAlt.wtIter wadd wL w0 (∑ i, al i)),
      ∀ β, X.inc _ (z β) = (SizeBoundsAlt.zPoly X w al θ).coeff β := by
  have pmul : ∀ (w w' : WeightFamilies.Wt D j) (F : B.Cusp j w) (F' : B.Cusp j w'), True → True →
      ∃ H : B.Cusp j (wadd w w'),
        (X.inc _).toAddMonoidHom H = (X.inc w).toAddMonoidHom F * (X.inc w').toAddMonoidHom F' ∧ True := by
    intro w w' F F' _ _
    obtain ⟨H, hH⟩ := X.inc_mul w w' F F'
    exact ⟨H, hH.symm, trivial⟩
  have hs : ∀ i : Fin (WeightFamilies.dimY D j), SizeBoundsAlt.Cf (fun w => (X.inc w).toAddMonoidHom) (fun _ _ => True) wL
      (∑ k, MvPolynomial.X (i.succ, k) * MvPolynomial.C (X.inc wL (w k))) :=
    fun i => SizeBoundsAlt.Cf_lin (fun _ => trivial) (fun _ _ _ _ _ => trivial) (fun k => (i.succ, k)) w fun _ => trivial
  obtain ⟨z, hz, -⟩ := SizeBoundsAlt.Cf_word (inc := fun w => (X.inc w).toAddMonoidHom) (Pr := fun _ _ => True)
    (fun _ => trivial) (fun _ _ _ _ _ => trivial) pmul _ hs θ trivial al
  exact ⟨z, hz⟩

end Coeff

section Choice

theorem exists_zChoice (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (hwt : SizeBoundsAlt.wtIter wadd wL (X.wF0 wL wF) (a0 D j T) = ka) {N : ℕ} (w : Fin N → B.Cusp j wL)
    (Sh : Finset (B.Cusp j (X.wF0 wL wF))) :
    ∃ (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ) (th0 : Fin rz → B.Cusp j (X.wF0 wL wF))
      (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka),
      (∀ k, ∑ i, alz k i = a0 D j T) ∧ (∀ k, th0 k ∈ Sh) ∧
      (∀ k β, X.inc ka (zc k β) = (SizeBoundsAlt.zPoly X w (alz k) (th0 k)).coeff β) ∧
      (∃ φ : Fin rz → B.Cusp j ka →ₗ[B.KO] B.KO, SizeBoundsAlt.detPoly φ zc ≠ 0) ∧
      ∀ la : HeightOneSpectrum (𝓞 B.KO),
        Submodule.span (Kp X la N)
            {v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j (X.wF0 wL wF)), ∑ i, al i = a0 D j T ∧
              θ ∈ Submodule.span B.KO (Sh : Set (B.Cusp j (X.wF0 wL wF))) ∧
              v = secPow X la w al * emb X la N (X.inc _ θ)} ≤
          Submodule.span (Kp X la N)
            (Set.range fun k => secPow X la w (alz k) * emb X la N (X.inc _ (th0 k))) := by
  classical
  let I : Type := ↥(Finset.piAntidiag (Finset.univ : Finset (Fin (WeightFamilies.dimY D j))) (a0 D j T)) × ↥Sh
  have hI : ∀ i : I, ∑ m, i.1.1 m = a0 D j T := fun i => (Finset.mem_piAntidiag.mp i.1.2).1
  have hex : ∀ i : I, ∃ z : ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka,
      ∀ β, X.inc ka (z β) = (SizeBoundsAlt.zPoly X w i.1.1 i.2.1).coeff β := by
    intro i
    have := exists_zc X w i.1.1 i.2.1
    rw [hI i, hwt] at this
    exact this
  choose zI hzI using hex
  let b : Basis (Fin (finrank B.KO (B.Cusp j ka))) B.KO (B.Cusp j ka) := Module.finBasis B.KO (B.Cusp j ka)
  let A : Type := MvPolynomial (Idx D j N) B.KO
  obtain ⟨ρ, e, J, hdet, hsp⟩ := exists_max_indep (A := A) (F := FractionRing A) (I := I)
    (fun i l => SizeBoundsAlt.polyOf (b.coord l) (zI i))
  refine ⟨ρ, fun k => (e k).1.1, fun k => (e k).2.1, fun k => zI (e k), fun k => hI (e k), fun k => (e k).2.2,
    fun k β => hzI (e k) β, ⟨fun i => b.coord (J i), hdet⟩, fun la => ?_⟩
  let g : FractionRing A →+* Kp X la N := IsFractionRing.lift (jF_injective X la N)
  have hg : ∀ q : A, g (algebraMap A (FractionRing A) q) = jF X la N q :=
    fun q => IsFractionRing.lift_algebraMap (jF_injective X la N) q
  have hval : ∀ i : I, secPow X la w i.1.1 * emb X la N (X.inc _ i.2.1) =
      ∑ l, jF X la N (SizeBoundsAlt.polyOf (b.coord l) (zI i)) • emb X la N (X.inc ka (b l)) := fun i => by
    rw [← psi_zPoly, psi_eq_sum_coord X la N ka b _ (zI i) (hzI i)]
  rw [Submodule.span_le]
  rintro _ ⟨al, θ, hal, hθ, rfl⟩
  induction hθ using Submodule.span_induction with
  | mem θ hθ =>
    let i0 : I := (⟨al, Finset.mem_piAntidiag.mpr ⟨hal, fun _ _ => Finset.mem_univ _⟩⟩, ⟨θ, hθ⟩)
    obtain ⟨a, ha⟩ := hsp i0
    have hsum : secPow X la w al * emb X la N (X.inc _ θ) =
        ∑ k, g (a k) • (secPow X la w (e k).1.1 * emb X la N (X.inc _ (e k).2.1)) := by
      rw [hval i0]
      simp only [hval (e _), Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← hg, ha l, map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hg, smul_smul]
    show secPow X la w al * emb X la N (X.inc _ θ) ∈ _
    rw [hsum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  | zero => simp only [map_zero, mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => simp only [map_add, mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    simp only [map_smul, emb_smul_jF, mul_smul_comm]
    exact Submodule.smul_mem _ _ hx

theorem exists_zChoice_addL (X : PJ D B P j) (wL wF : WeightFamilies.Wt D j) (T : ℕ) (hDT : WeightFamilies.dimY D j ≤ T) {N : ℕ}
    (w : Fin N → B.Cusp j wL) (Sh : Finset (B.Cusp j (X.wF0 wL wF))) :
    ∃ (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ) (th0 : Fin rz → B.Cusp j (X.wF0 wL wF))
      (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j (addL wF wL T)),
      (∀ k, ∑ i, alz k i = a0 D j T) ∧ (∀ k, th0 k ∈ Sh) ∧
      (∀ k β, X.inc _ (zc k β) = (SizeBoundsAlt.zPoly X w (alz k) (th0 k)).coeff β) ∧
      (∃ φ : Fin rz → B.Cusp j (addL wF wL T) →ₗ[B.KO] B.KO, SizeBoundsAlt.detPoly φ zc ≠ 0) ∧
      ∀ la : HeightOneSpectrum (𝓞 B.KO),
        Submodule.span (Kp X la N)
            {v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j (X.wF0 wL wF)), ∑ i, al i = a0 D j T ∧
              θ ∈ Submodule.span B.KO (Sh : Set (B.Cusp j (X.wF0 wL wF))) ∧
              v = secPow X la w al * emb X la N (X.inc _ θ)} ≤
          Submodule.span (Kp X la N)
            (Set.range fun k => secPow X la w (alz k) * emb X la N (X.inc _ (th0 k))) :=
  exists_zChoice X (addL wF wL T) wL wF T (iterated_weight_at_vanishingOrder X wL wF T hDT) w Sh

theorem exists_global_family_zero_choice {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (S : Scal B) (T : ℕ) (Gc : ℝ)
    (hwt : SizeBoundsAlt.wtIter wadd wL (X.wF0 wL wF) (a0 D j T) = ka)
    (hS4 : ShortG X (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF)) (Gc * (X.wF0 wL wF).size))
    (hM : X.Thc S.s0 (X.wF0 wL wF) ≤ B.Mlat j (X.wF0 wL wF)) :
    ∃ (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ) (th0 : Fin rz → B.Cusp j (X.wF0 wL wF))
      (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G0.N) →₀ ℕ) →₀ B.Cusp j ka),
      ({ G0 with rz := rz, alz := alz, th0 := th0, zc := zc } : GlobalFamilyData X ka wL wF).TiedZ S T Gc ∧
      ∀ la, InContainZ ({ G0 with rz := rz, alz := alz, th0 := th0, zc := zc } : GlobalFamilyData X ka wL wF) la S T := by
  obtain ⟨Sh, hSh, hspan, hshort⟩ := hS4
  obtain ⟨rz, alz, th0, zc, hal, hth, hzc, hdet, hin⟩ := exists_zChoice X ka wL wF T hwt G0.w Sh
  refine ⟨rz, alz, th0, zc, ⟨fun k => ⟨hSh (hth k), hM (hSh (hth k)), hshort _ (hth k), hal k⟩, hzc, hdet⟩, fun la => ?_⟩
  refine le_trans (Submodule.span_mono ?_) (hin la)
  rintro v ⟨al, θ, h1, -, h3⟩
  exact ⟨al, θ, h1, by rw [hspan]; trivial, h3⟩

end Choice

section Rank

theorem zFam_linearIndependent (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N ρ : ℕ} {wL w0 : WeightFamilies.Wt D j}
    (w : Fin N → B.Cusp j wL) (ka : WeightFamilies.Wt D j) (al : Fin ρ → Fin (WeightFamilies.dimY D j) → ℕ) (th : Fin ρ → B.Cusp j w0)
    (zc : Fin ρ → (Idx D j N →₀ ℕ) →₀ B.Cusp j ka)
    (hzc : ∀ k β, X.inc ka (zc k β) = (SizeBoundsAlt.zPoly X w (al k) (th k)).coeff β)
    (hdet : ∃ φ : Fin ρ → B.Cusp j ka →ₗ[B.KO] B.KO, SizeBoundsAlt.detPoly φ zc ≠ 0) :
    LinearIndependent (Kp X la N) fun k => secPow X la w (al k) * emb X la N (X.inc w0 (th k)) := by
  classical
  obtain ⟨φ, hφ⟩ := hdet
  choose φ1 hφ1 using fun i => exists_ext X la N ka (φ i)
  let z1 : Fin ρ → ↥(Vw X la N ka) := fun k =>
    ∑ β ∈ (zc k).support, jF X la N (MvPolynomial.monomial β 1) • uV X la N ka (zc k β)
  have hent : ∀ i k, φ1 i (z1 k) = jF X la N (SizeBoundsAlt.polyOf (φ i) (zc k)) := by
    intro i k
    unfold SizeBoundsAlt.polyOf
    rw [Finsupp.sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [map_smul, smul_eq_mul, hφ1, ← map_mul, mul_comm, MvPolynomial.C_mul_monomial, mul_one]
  have hd : (Matrix.of fun i k => φ1 i (z1 k)).det = jF X la N (SizeBoundsAlt.detPoly φ zc) := by
    unfold SizeBoundsAlt.detPoly
    rw [RingHom.map_det]
    congr 1
    funext i k
    simp [hent]
  have hd0 : (Matrix.of fun i k => φ1 i (z1 k)).det ≠ 0 := by
    rw [hd]; exact (map_ne_zero_iff _ (jF_injective X la N)).mpr hφ
  have hli : LinearIndependent (Kp X la N) z1 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hmv : (Matrix.of fun i k => φ1 i (z1 k)).mulVec g = 0 := by
      funext i
      have := congrArg (φ1 i) hg
      rw [map_sum, map_zero] at this
      simp only [map_smul, smul_eq_mul] at this
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    exact fun k => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hd0 hmv) k
  have h2 := hli.map' (Vw X la N ka).subtype (Submodule.ker_subtype _)
  have h3 : (⇑(Vw X la N ka).subtype ∘ z1) = fun k => secPow X la w (al k) * emb X la N (X.inc w0 (th k)) := by
    funext k
    exact coe_zSum X la w ka (al k) (th k) (zc k) (hzc k)
  rwa [h3] at h2

theorem rz_eq_finrank {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (S : Scal B) (T : ℕ) (Gc : ℝ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (hT : G.TiedZ S T Gc) (hZ : InContainZ G la S T) :
    finrank (Kp X la G.N) ↥(Submodule.span (Kp X la G.N)
      {v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j (X.wF0 wL wF)), ∑ i, al i = a0 D j T ∧
          θ ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ v = secPow X la G.w al * emb X la G.N (X.inc _ θ)}) = G.rz := by
  have hli : LinearIndependent (Kp X la G.N) (zK G la) :=
    zFam_linearIndependent X la G.w ka G.alz G.th0 G.zc hT.2.1 hT.2.2
  have heq : Submodule.span (Kp X la G.N)
      {v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j (X.wF0 wL wF)), ∑ i, al i = a0 D j T ∧
          θ ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ v = secPow X la G.w al * emb X la G.N (X.inc _ θ)} =
      Submodule.span (Kp X la G.N) (Set.range (zK G la)) := by
    refine le_antisymm hZ (Submodule.span_mono ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨G.alz k, G.th0 k, (hT.1 k).2.2.2, (hT.1 k).1, rfl⟩
  rw [heq, finrank_span_eq_card hli, Fintype.card_fin]

end Rank

end Formalism.MainNotions.Gaps.EtaleWeightGaps
