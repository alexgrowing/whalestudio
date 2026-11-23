import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugatePrimeBoundPointKernelOfCoefficientKerne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TilLatticesOfLevel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulMemLocPOfVal
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairBDual

noncomputable section

namespace GlobalTheory.LvT.Built.ValLat

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2
open Formalism.MainNotions.product_first_zeroth_parts (Ow blk IntSpan)

section Poly

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem roundAct_eq {R : Type} [CommRing R] (l : DomWeight n) (g : GL (Fin n) R) (f : MvPolynomial (Fin n × Fin n) R) :
    roundAct R n l g f = sqAct R n l (inside₂ R n g) f := by
  unfold roundAct sqAct Formalism.UG.dwAct detPow
  have h : Matrix.GeneralLinearGroup.det (inside₂ R n g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
    rw [← map_inv]
    apply Units.ext
    exact Matrix.det_transpose _
  rw [h, _root_.inv_zpow', show ((inside₂ R n g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ = _ from Matrix.transpose_transpose _]

theorem blk_roundAct (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) :
    blk (fun τ => roundAct ℂ n (lam τ) (g τ)) = actP lam (invTrK g) := by
  apply (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext
  intro m
  unfold blk
  rw [Module.Basis.constr_basis]
  have h := Formalism.MainNotions.product_first_zeroth_parts.ten_monomial (fun τ => m.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn)
  have e : (∑ σ, (m.comapDomain (Prod.mk σ) (Prod.mk_right_injective σ).injOn).mapDomain (Prod.mk σ)) = m := by
    ext ⟨τ, x⟩
    have := congrArg (fun f => f x) (Formalism.MainNotions.product_first_zeroth_parts.comap_sum
      (fun τ => m.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) τ)
    exact this
  rw [e] at h
  rw [MvPolynomial.coe_basisMonomials]
  simp only []
  rw [← h]
  refine Eq.trans ?_ (actTen ℂ ι n lam (invTrK g) _).symm
  simp only [roundAct_eq]
  rfl

theorem map_actP {K : Type} [Field K] (σ : K →+* ℂ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map σ (actP lam g F) = actP lam (fun τ => Formalism.UG.bc σ (g τ)) (MvPolynomial.map σ F) := by
  have e2 : σ (detTwK lam g) = detTwK lam (fun τ => Formalism.UG.bc σ (g τ)) := by
    rw [detTwK, detTwK, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [detPow, Units.val_zpow_eq_zpow_val, map_zpow₀, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  simp only [actP, trAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.map_C, map_blockAct, transpose_map, e2]
  rfl

theorem map_ten_int {K : Type} [Field K] (σ : K →+* ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℤ) :
    MvPolynomial.map σ (ten fun τ => MvPolynomial.map (Int.castRingHom K) (f τ)) =
      Formalism.MainNotions.product_first_zeroth_parts.ten fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ) := by
  unfold ten Formalism.MainNotions.product_first_zeroth_parts.ten Formalism.GradedWeylDivisibility.blockEmb
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.map_rename, MvPolynomial.map_map, RingHom.ext_int (σ.comp (Int.castRingHom K)) (Int.castRingHom ℂ)]

end Poly

section Span

variable {K ι : Type} [Field K] [NumberField K] [Fintype ι] {n : ℕ}

theorem mem_closure_iff (σ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) (O : Subring K) (hO : ∀ x, x ∈ O ↔ w.valuation K x ≤ 1)
    (lam : ι → DomWeight n) (z : Pol ℂ ι n) :
    z ∈ AddSubgroup.closure {p | ∃ (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ), r ∈ O ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
      p = σ r • Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))} ↔
    ∃ z₀ ∈ localization₂ w.asIdeal (delStd K lam), z = MvPolynomial.map σ z₀ := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem q hq =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hq
      have h0 := GlobalTheory.JetOpWeylLat.ten_mem_delStd (K := K) lam hf
      have h1 := GlobalTheory.JetOpWeylLat.smul_mem_localizationAt_of_valuation w ((hO r).1 hr) h0
      refine ⟨_, h1, ?_⟩
      rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_ten_int]
    | zero => exact ⟨0, Submodule.zero_mem _, (map_zero (MvPolynomial.map σ)).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      exact ⟨a + b, Submodule.add_mem _ ha hb, (map_add (MvPolynomial.map σ) _ _).symm⟩
    | neg a _ ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      exact ⟨-a, Submodule.neg_mem _ ha, (map_neg (MvPolynomial.map σ) _).symm⟩
  · rintro ⟨z₀, hz, rfl⟩
    generalize hS : (AddSubgroup.closure _ : AddSubgroup (Pol ℂ ι n)) = S
    have key : ∀ y ∈ delStd K lam, ∀ r ∈ O, MvPolynomial.map σ (r • y) ∈ S := by
      intro y hy
      have hy' := GlobalTheory.JetOpWeylLat.delStd_le_span lam hy
      clear hy
      induction hy' using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨f, hf, rfl⟩ := hq
        intro r hr
        rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_ten_int, ← MvPolynomial.smul_eq_C_mul, ← hS]
        exact AddSubgroup.subset_closure ⟨r, f, hr, hf, rfl⟩
      | zero => intro r _; rw [smul_zero, map_zero]; exact S.zero_mem
      | add a b _ _ ha hb => intro r hr; rw [smul_add, map_add]; exact S.add_mem (ha r hr) (hb r hr)
      | smul c a _ ha =>
        intro r hr
        rw [← algebraMap_smul K c a, smul_smul]
        exact ha _ (O.mul_mem hr ((hO _).2 (w.valuation_le_one c)))
    obtain ⟨s, hs, hz⟩ := (lc_mem_locP w _ _).1 hz
    have hv : w.valuation K (algebraMap (𝓞 K) K s) = 1 := (w.valuation_eq_one_iff_notMem).2 hs
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hv
      exact zero_ne_one hv
    have := key _ hz (algebraMap (𝓞 K) K s)⁻¹ ((hO _).2 (by rw [map_inv₀, hv, inv_one]))
    rwa [← algebraMap_smul K s z₀, smul_smul, inv_mul_cancel₀ hs0, one_smul] at this

end Span

theorem mem_intSpan_iff (D : D7) (w : D.what₂.places.Pl) {n : ℕ} (lam lam' : D.what₂.Tau → DomWeight n)
    (hl : ∀ τ, (lam τ).natW = (lam' τ).natW) (z : Pol ℂ D.what₂.Tau n) :
    z ∈ IntSpan D w lam ↔ ∃ z₀ ∈ localization₂ (D.plEq w).asIdeal (delStd D.what₂.LL lam'), z = MvPolynomial.map D.what₂.embLL z₀ := by
  have hd : ∀ τ, delSq ℤ n (lam τ) = delSq ℤ n (lam' τ) := fun τ => by unfold delSq; rw [hl τ]
  unfold IntSpan
  simp only [hd]
  exact mem_closure_iff D.what₂.embLL (D.plEq w) (Ow D w) (D.val_nonneg_iff w) lam' z

section Lat

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem mem_localization_delAtr (emb : ι → E →+* K) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K))
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : Submodule.IsLattice E L) (B : ι → GL (Fin n) K)
    (hB : ∀ τ, IsBasisAt w (dualFr (tauLat emb τ L)) (B τ)) (F : Formalism.L2.DIV.VV K lam) :
    F ∈ localization₂ w.asIdeal (delAtr emb lam L) ↔ ∃ z ∈ localization₂ w.asIdeal (delStd K lam), F.1 = actP lam B z := by
  have hM : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ L)) := fun τ =>
    du_dualFr_lattice basisAtEx _ (tauLatLattice E K ι n emb τ L hL)
  have h1 : F ∈ localization₂ w.asIdeal (delAtr emb lam L) ↔
      F.1 ∈ localization₂ w.asIdeal (delP lam fun τ => dualFr (tauLat emb τ L)) := Iff.rfl
  rw [h1, (nabDelLoc K ι n lam _ hM w B hB).2]
  exact ⟨fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩, fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩⟩

theorem mem_VV_of_locP (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) {z : Pol K ι n}
    (hz : z ∈ localization₂ w.asIdeal (delStd K lam)) : z ∈ Formalism.L2.DIV.VV K lam := by
  obtain ⟨s, hs, hz⟩ := (lc_mem_locP w _ _).1 hz
  have h1 : ∀ y ∈ delStd K lam, y ∈ Formalism.L2.DIV.VV K lam := by
    intro y hy
    have hy' := GlobalTheory.JetOpWeylLat.delStd_le_span lam hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨f, hf, rfl⟩ := hq
      exact Submodule.subset_span ⟨_, fun τ => Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (natW_anti (lam τ))
        (GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom K) _ _ _ (hf τ)), rfl⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul c a _ ha => rw [← algebraMap_smul K c a]; exact Submodule.smul_mem _ _ ha
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    rintro rfl
    exact hs (zero_mem _)
  have := (Formalism.L2.DIV.VV K lam).smul_mem (algebraMap (𝓞 K) K s)⁻¹ (h1 _ hz)
  rwa [← algebraMap_smul K s z, smul_smul, inv_mul_cancel₀ hs0, one_smul] at this

theorem bcBelow_eq (j : E →+* K) (w : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ x, w.valuation K (j x) ≤ 1 ↔ P.valuation E x ≤ 1) : bcBelow j w = P := by
  apply HeightOneSpectrum.ext
  ext r
  rw [bc_mem_below, ← w.valuation_lt_one_iff_mem (K := K), ← P.valuation_lt_one_iff_mem (K := E)]
  change w.valuation K (j (r : E)) < 1 ↔ P.valuation E (r : E) < 1
  by_cases hr : (r : E) = 0
  · simp [hr]
  · have h1 := h (r : E)⁻¹
    have a1 : 0 < w.valuation K (j (r : E)) := (Valuation.pos_iff _).2 ((map_ne_zero j).2 hr)
    have a2 : 0 < P.valuation E (r : E) := (Valuation.pos_iff _).2 hr
    rw [map_inv₀, map_inv₀, map_inv₀, inv_le_one₀ a1, inv_le_one₀ a2] at h1
    rw [← not_le, ← not_le, h1]

omit [Fintype ι] in
theorem basis_seen (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ x, w.valuation K (emb τ x) ≤ 1 ↔ P.valuation E x ≤ 1) {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsLattice E L) {g : GL (Fin n) E} (hg : IsBasisAt P L g) :
    IsBasisAt w (dualFr (tauLat emb τ L)) (inside₂ K n (Formalism.UG.bc (emb τ) g)) :=
  pb_isBasisAt_dualFr w _ (tauLatLattice E K ι n emb τ L hL).fg _
    (bc_isBasisAt (emb τ) w (by rw [bcBelow_eq _ w P h]; exact hg))

omit [Fintype ι] in
theorem basis_conj [StarRing E] (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ x, w.valuation K (emb τ (star x)) ≤ 1 ↔ P.valuation E x ≤ 1) {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsLattice E L) {g : GL (Fin n) E} (hg : IsBasisAt P L g) :
    IsBasisAt w (dualFr (tauLat emb τ (dual (hStd E n) L))) (Formalism.UG.bc ((emb τ).comp (starRingEnd E)) g) := by
  have e := roundLat E K ι n emb (starRingEnd E) τ (fun x => star_star x) 1 (dual (hStd E n) L) L (dual_lattice hL)
    (by ext a b; simp [Formalism.UG.cT, Matrix.one_apply, eq_comm]) (fun y => by
      conv_lhs => rw [← dual_dual hL, mem_dual]
      refine forall₂_congr fun x _ => ?_
      have : Formalism.UG.hform (starRingEnd E) ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) x y = hStd E n x y := by
        simp [Formalism.UG.hform, hStd_apply, Matrix.one_apply, starRingEnd_apply]
      rw [this, Submodule.mem_one]
      rfl)
  rw [e, inv_one, map_one, map_one, Pi.one_apply, du_gLat_one]
  exact bc_isBasisAt ((emb τ).comp (starRingEnd E)) w (by rw [bcBelow_eq _ w P h]; exact hg)

theorem mem_localization_one (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    x ∈ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) ↔ P.valuation E x ≤ 1 := by
  constructor
  · intro hx
    obtain ⟨s, hs, h⟩ := (lc_mem_locP P _ _).1 hx
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 h
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := (P.valuation_eq_one_iff_notMem).2 hs
    have h2 : P.valuation E (algebraMap (𝓞 E) E r) ≤ 1 := P.valuation_le_one (K := E) r
    rwa [hr, Algebra.smul_def, map_mul, h1, one_mul] at h2
  · intro hx
    have := GlobalTheory.JetOpWeylLat.smul_mem_localizationAt_of_valuation P (T := (1 : Submodule (𝓞 E) E)) hx (Submodule.one_le.1 le_rfl)
    rwa [smul_eq_mul, mul_one] at this

theorem isBasisAt_iff (P : HeightOneSpectrum (𝓞 E)) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) E) :
    IsBasisAt P L g ↔ ∀ x, (g : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ localization₂ P.asIdeal L ↔ ∀ a, P.valuation E (x a) ≤ 1 := by
  have e : ∀ x : Fin n → E, ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((g : Matrix (Fin n) (Fin n) E) *ᵥ x) = x :=
    fun x => by rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have e' : ∀ x : Fin n → E, (g : Matrix (Fin n) (Fin n) E) *ᵥ (((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) = x :=
    fun x => by rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  unfold IsBasisAt
  constructor
  · intro h x
    rw [h, mem_localized_columnLattice_iff, e]
    simp only [mem_localization_one]
  · intro h
    ext y
    rw [mem_localized_columnLattice_iff]
    simp only [mem_localization_one]
    rw [← h, e']

end Lat

section Deco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}

theorem exists_sepElt (h : ∀ P ∈ ST, ∀ Q ∈ ST, Q ≠ conjPrime₂ P) : ∃ a, SepElt ST a := by
  classical
  have hex : ∀ P : ST, ∃ a : 𝓞 E, a ∈ (conjPrime₂ P.1).asIdeal ∧ ∀ Q : ST, a ∉ Q.1.asIdeal := by
    intro P
    by_contra H
    push Not at H
    have hsub : ((conjPrime₂ P.1).asIdeal : Set (𝓞 E)) ⊆ ⋃ Q ∈ (↑(Finset.univ : Finset ST) : Set ST), (Q.1.asIdeal : Set (𝓞 E)) := by
      intro a ha
      obtain ⟨Q, hQ⟩ := H a ha
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ Q)) hQ
    obtain ⟨Q, -, hQ⟩ := (Ideal.subset_union_prime P P (fun Q _ _ _ => Q.1.isPrime)).1 hsub
    exact h P.1 P.2 Q.1 Q.2 (HeightOneSpectrum.ext ((conjPrime₂ P.1).isMaximal.eq_of_le Q.1.isPrime.ne_top hQ).symm)
  choose a ha ha' using hex
  refine ⟨∏ P, a P, fun P => ?_, fun P hm => ?_⟩
  · exact (mem_conjP P.1 _).1 (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a (Finset.mem_univ P)) (ha P))
  · obtain ⟨Q, -, hQ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.1.isPrime)).1 hm
    exact ha' Q P hQ

theorem locP_Lsh_off {d : Deco E n ST ∅} (hd : d.Ok) {T : ℕ} (hT : ∀ P ∈ ST, (T : 𝓞 E) ∈ P.asIdeal)
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : (T : 𝓞 E) ∉ Q.asIdeal) : localization₂ Q.asIdeal d.Lsh = localization₂ Q.asIdeal d.N :=
  le_antisymm (localization_le_of_smul_mem hQ fun _ hx => hd.smul_Lsh_mem_N (fun P => by rw [map_natCast]; exact hT P.1 P.2) hx)
    (localization_le_of_smul_mem (one_notMem Q) fun x hx => by rw [one_smul]; exact hd.N_le_Lsh hx)

theorem delAtr_off {K ι : Type} [Field K] [NumberField K] [Fintype ι] (emb : ι → E →+* K) (lam : ι → DomWeight n)
    {d d' : Deco E n ST ∅} (hd : d.Ok) (hd' : d'.Ok) {T : ℕ} (hT : ∀ P ∈ ST, (T : 𝓞 E) ∈ P.asIdeal)
    (h : SameOff ST d.N d'.N) {w : HeightOneSpectrum (𝓞 K)} (hw : (T : 𝓞 K) ∉ w.asIdeal) :
    localization₂ w.asIdeal (delAtr emb lam d.Lsh) = localization₂ w.asIdeal (delAtr emb lam d'.Lsh) := by
  refine (round_locP_congr emb lam w hd.Lsh_lattice hd'.Lsh_lattice fun τ => ?_).1
  have hQ : (T : 𝓞 E) ∉ (bcBelow (emb τ) w).asIdeal := by rwa [bc_mem_below, map_natCast]
  have e : localization₂ (bcBelow (emb τ) w).asIdeal d.Lsh = localization₂ (bcBelow (emb τ) w).asIdeal d'.Lsh := by
    rw [locP_Lsh_off hd hT hQ, locP_Lsh_off hd' hT hQ]
    refine h _ fun P hP => ⟨?_, ?_⟩
    · rintro e
      exact hQ (e ▸ hT P hP)
    · rintro e
      apply hQ
      rw [e, mem_conjP, map_natCast]
      exact hT P hP
  constructor
  · intro x hx
    exact (mem_locP _ _ _).1 (e ▸ le_locP _ _ hx)
  · intro x hx
    exact (mem_locP _ _ _).1 (e ▸ le_locP _ _ hx)

theorem localization_kerAt_eq {d : Deco E n ST ∅} (hd : d.Ok) (P : ST) : localization₂ P.1.asIdeal (d.kerAt P) = localization₂ P.1.asIdeal d.L := by
  apply le_antisymm
  · refine localization_le_of_le_localization _ fun x hx => ?_
    obtain ⟨h1, h2⟩ := (hd.mem_kerAt P x).1 hx
    exact (hd.mem_locP_L P x).2 ⟨le_locP _ _ h1, h2⟩
  · refine localization_mono _ fun x hx => ?_
    obtain ⟨h1, h2⟩ := (hd.mem_L x).1 hx
    exact (hd.mem_kerAt P x).2 ⟨h1, h2 P⟩

end Deco

end GlobalTheory.LvT.Built.ValLat
