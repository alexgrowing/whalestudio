import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPDelAtrEqLocPNabAtr
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubHalfRankInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
import Formalism.LocalToGlobal.Columns.AtTOwedS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open scoped Matrix

noncomputable section

namespace GlobalTheory.BarStd

open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (adj suppBar StdAtT InIntClosure Induces jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis detFac extLat admitted InClosure ptTable)
open GlobalTheory.CharVal (intAt_iff valuation_conjP conjP_conjP')

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n a b : ℕ}

theorem mem_localization_dual {M : Submodule (𝓞 E) (Sp E n)} (hM : M.FG) (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ localization₂ (conjPrime₂ P).asIdeal (dual (hStd E n) M) ↔
      ∀ y ∈ localization₂ P.asIdeal M, (conjPrime₂ P).valuation E (hStd E n y x) ≤ 1 := by
  constructor
  · intro hx y hy
    obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hx
    obtain ⟨t, ht, hty⟩ := (mem_locP _ _ _).1 hy
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 ((mem_dual _ _).1 hsx _ hty)
    refine (intAt_iff _).1 ⟨r, cO E t * s, fun h => ((conjPrime₂ P).isPrime.mem_or_mem h).elim
      (fun h' => ht (by rwa [mem_conjP, cO_cO] at h')) hs, ?_⟩
    rw [hr, hStd_osmul_left, ← mul_smul, ← algebraMap_smul E (cO E t * s) x, map_smul, smul_eq_mul]
  · intro H
    let M' : Submodule (𝓞 E) (Sp E n) := (1 : Submodule (𝓞 E) E).comap ((hStd E n x).restrictScalars (𝓞 E))
    have h1 : localization₂ P.asIdeal M ≤ localization₂ P.asIdeal M' := by
      intro y hy
      have h2 := H y hy
      rw [valuation_conjP, ← starRingEnd_apply, hStd_isSymm.eq] at h2
      obtain ⟨r, s, hs, e⟩ := (intAt_iff _).2 h2
      refine (mem_locP _ _ _).2 ⟨s, hs, ?_⟩
      change hStd E n x (s • y) ∈ (1 : Submodule (𝓞 E) E)
      rw [← algebraMap_smul E s y, map_smul, smul_eq_mul, e]
      exact Submodule.mem_one.2 ⟨r, rfl⟩
    obtain ⟨c, hc, hcM⟩ := GlobalTheory.StdReps.exists_smul_of_le hM h1
    refine (mem_locP _ _ _).2 ⟨cO E c, by rwa [mem_conjP, cO_cO], (mem_dual _ _).2 fun y hy => ?_⟩
    rw [← hStd_osmul_left]
    exact hStd_mem_one_symm (hcM y hy)

omit [NumberField E] in
theorem hStd_mulVec (A : Matrix (Fin b) (Fin a) E) (z : Sp E a) (x : Sp E b) :
    hStd E b (A *ᵥ z) x = hStd E a z (Aᴴ *ᵥ x) := by
  change star (A *ᵥ z) ⬝ᵥ x = star z ⬝ᵥ (Aᴴ *ᵥ x)
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

omit [NumberField E] in
theorem hStd_adj (x : HomE E a b) (l : Sp E a) (y : Sp E b) : hStd E a l (adj x y) = hStd E b (x l) y := by
  rw [adj, Matrix.toLin'_apply, ← hStd_mulVec, LinearMap.toMatrix'_mulVec]

variable {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

theorem adj_mem (d : DecoSet E a ST SG) (d' : DecoSet E b ST SG') {x : HomE E a b} (hx : x ∈ suppBar d.1 d'.1) (P : ST)
    {y : Sp E b} (hy : y ∈ d'.1.Lsh) : adj x y ∈ localization₂ (conjPrime₂ P.1).asIdeal d.1.Lsh := by
  rw [Deco.Lsh, mem_localization_dual d.2.L_lattice.fg]
  intro l hl
  rw [hStd_adj]
  refine (mem_localization_dual d'.2.L_lattice.fg P.1 y).1 (le_locP _ _ hy) _ ?_
  rw [d.2.mem_locP_L] at hl
  rw [d'.2.mem_locP_L]
  exact ⟨(hx P l hl.1).1, (hx P l hl.1).2.trans hl.2⟩

omit [StarRing E] in
theorem mem_stdAt (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) : x ∈ stdAt E n P ↔ ∀ i, P.valuation E (x i) ≤ 1 := by
  let _ : StarRing E := starRingOfComm
  rw [stdAt, mem_localization_standardLattice]
  exact forall_congr' fun i => intAt_iff _

theorem exists_coeff (d : DecoSet E n ST SG) (P : ST) (h : d.1.at P.1 = stdAt E n P.1) :
    ∃ c : Fin n → 𝓞 E, ∀ x ∈ stdAt E n P.1,
      (d.1.f P x = 0 ↔ P.1.valuation E (∑ j, algebraMap (𝓞 E) E (c j) * x j) < 1) := by
  classical
  choose c hc using fun j : Fin n => Ideal.Quotient.mk_surjective (d.1.f P (Pi.single j 1))
  refine ⟨c, fun x hx => ?_⟩
  obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hx
  choose r hr using (mem_stdLat _).1 hsx
  have he : ∀ j, (Pi.single j (1 : E) : Sp E n) ∈ d.1.at P.1 := fun j => by
    rw [h]
    exact le_locP _ _ (by simpa using single_mem_stdLat (E := E) j 1)
  have h1 : ∀ F : Finset (Fin n), d.1.f P (∑ j ∈ F, r j • (Pi.single j (1 : E) : Sp E n)) =
      Ideal.Quotient.mk P.1.asIdeal (∑ j ∈ F, c j * r j) := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa using d.2.f_zero P
    | insert j F hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, d.2.f_add P _ (Submodule.smul_mem _ _ (he j)) _
        (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (he k)), ih, d.2.f_smul P _ _ (he j), ← hc, map_add,
        map_mul, mul_comm]
  have h2 : s • x = ∑ j, r j • (Pi.single j (1 : E) : Sp E n) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
  have h3 := d.2.f_smul P s x (h ▸ hx)
  rw [h2, h1] at h3
  have h4 : algebraMap (𝓞 E) E (∑ j, c j * r j) = algebraMap (𝓞 E) E s * ∑ j, algebraMap (𝓞 E) E (c j) * x j := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hr, Pi.smul_apply, Algebra.smul_def]
    ring
  have h5 : P.1.valuation E (algebraMap (𝓞 E) E s) = 1 := (P.1.valuation_eq_one_iff_notMem).2 hs
  have h6 : P.1.valuation E (algebraMap (𝓞 E) E (∑ j, c j * r j)) < 1 ↔ _ :=
    P.1.valuation_lt_one_iff_mem (K := E) (∑ j, c j * r j)
  rw [h4, map_mul, h5, one_mul] at h6
  rw [h6, ← Ideal.Quotient.eq_zero_iff_mem, h3, mul_eq_zero, or_iff_right (mk_ne_zero hs)]

theorem exists_matrix_ker (d : DecoSet E n ST SG) (P : ST) (h : d.1.at P.1 = stdAt E n P.1) {q : E}
    (hq : P.1.valuation E q = WithZero.exp (-1 : ℤ)) :
    ∃ A : Matrix (Fin n) (Fin n) E, P.1.valuation E (q * A.det) = 1 ∧
      ∀ x, x ∈ localization₂ P.1.asIdeal d.1.L ↔ A *ᵥ x ∈ stdAt E n P.1 := by
  classical
  obtain ⟨c, hc⟩ := exists_coeff d P h
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hq
    exact WithZero.exp_ne_zero hq.symm
  obtain ⟨k, hk⟩ : ∃ k, c k ∉ P.1.asIdeal := by
    by_contra H
    push Not at H
    obtain ⟨x, hx, hne⟩ := d.2.f_ne P
    have hx' : x ∈ stdAt E n P.1 := h ▸ le_locP _ _ hx
    refine hne ((hc x hx').2 (Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_))
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le ((P.1.valuation_lt_one_iff_mem (K := E) _).2 (H j)) ((mem_stdAt _ _).1 hx' j)
  have hk1 : P.1.valuation E (algebraMap (𝓞 E) E (c k)) = 1 := (P.1.valuation_eq_one_iff_notMem).2 hk
  have hlt : ∀ z : E, P.1.valuation E (q⁻¹ * z) ≤ 1 ↔ P.1.valuation E z < 1 := by
    intro z
    rw [map_mul, map_inv₀, hq, inv_mul_le_one₀ WithZero.exp_pos]
    by_cases hz : P.1.valuation E z = 0
    · simp [hz]
    · rw [← WithZero.exp_log hz, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_lt_exp]
      omega
  let A : Matrix (Fin n) (Fin n) E := (1 : Matrix (Fin n) (Fin n) E).updateRow k fun j => q⁻¹ * algebraMap (𝓞 E) E (c j)
  have hA1 : ∀ x : Sp E n, (A *ᵥ x) k = q⁻¹ * ∑ j, algebraMap (𝓞 E) E (c j) * x j := by
    intro x
    simp only [A, Matrix.mulVec, dotProduct, Matrix.updateRow_self, Finset.mul_sum, mul_assoc]
  have hA2 : ∀ (x : Sp E n) j, j ≠ k → (A *ᵥ x) j = x j := by
    intro x j hj
    simp [A, Matrix.mulVec, dotProduct, Matrix.updateRow_ne hj, Matrix.one_apply]
  refine ⟨A, ?_, fun x => ?_⟩
  · have e : (fun j => q⁻¹ * algebraMap (𝓞 E) E (c j)) =
        ∑ j, (q⁻¹ * algebraMap (𝓞 E) E (c j)) • (1 : Matrix (Fin n) (Fin n) E) j := by
      funext l
      simp [Finset.sum_apply, Matrix.one_apply]
    simp only [A]
    rw [e, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one, mul_inv_cancel_left₀ hq0, hk1]
  · rw [d.2.mem_locP_L, h]
    constructor
    · rintro ⟨h1, h2⟩
      rw [mem_stdAt]
      intro j
      by_cases hj : j = k
      · rw [hj, hA1, hlt]
        exact (hc x h1).1 h2
      · rw [hA2 x j hj]
        exact (mem_stdAt _ _).1 h1 j
    · intro H
      rw [mem_stdAt] at H
      have h1 := H k
      rw [hA1, hlt] at h1
      have h2 : x ∈ stdAt E n P.1 := by
        rw [mem_stdAt]
        intro j
        by_cases hj : j = k
        · subst hj
          have h3 : algebraMap (𝓞 E) E (c j) * x j = (∑ l, algebraMap (𝓞 E) E (c l) * x l) -
              ∑ l ∈ Finset.univ.erase j, algebraMap (𝓞 E) E (c l) * x l := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_right]
          have h4 : P.1.valuation E (algebraMap (𝓞 E) E (c j) * x j) ≤ 1 := by
            rw [h3]
            refine Valuation.map_sub_le _ h1.le (Valuation.map_sum_le _ fun l hl => ?_)
            rw [map_mul, ← hA2 x l (Finset.ne_of_mem_erase hl)]
            exact mul_le_one' (P.1.valuation_le_one _) (H l)
          rwa [map_mul, hk1, one_mul] at h4
        · rw [← hA2 x j hj]
          exact H j
      exact ⟨h2, (hc x h2).2 h1⟩

theorem isBasisAt_of (Q : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (B : GL (Fin n) E)
    (h : ∀ z, (B : Matrix (Fin n) (Fin n) E) *ᵥ z ∈ localization₂ Q.asIdeal M ↔ z ∈ stdAt E n Q) : IsBasisAt Q M B := by
  classical
  let f : Sp E n ≃ₗ[E] Sp E n := Matrix.toLin'OfInv (M := ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
    (M' := (B : Matrix (Fin n) (Fin n) E)) (Units.inv_mul B) (Units.mul_inv B)
  have hf : ∀ x, f x = (B : Matrix (Fin n) (Fin n) E) *ᵥ x := fun x => rfl
  have e : colLat B = gmap f (stdLat E n) := by
    rw [stdLat_eq_span]
    unfold gmap colLat
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j i
    simp [hf]
  ext y
  rw [e, mem_localization_gmap, ← f.apply_symm_apply y, hf, h, ← hf, f.symm_apply_apply]
  rfl

theorem exists_basis_Lsh (d : DecoSet E n ST SG) (P : ST) (h : d.1.at P.1 = stdAt E n P.1) {q : ℕ}
    (hq : P.1.valuation E (q : E) = WithZero.exp (-1 : ℤ)) :
    ∃ B : GL (Fin n) E, IsBasisAt (conjPrime₂ P.1) d.1.Lsh B ∧
      (conjPrime₂ P.1).valuation E (q * (B : Matrix (Fin n) (Fin n) E).det) = 1 := by
  obtain ⟨A, hA, hL⟩ := exists_matrix_ker d P h hq
  have hA0 : A.det ≠ 0 := by
    intro h0
    simp [h0] at hA
  have hB0 : Aᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 hA0
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hB0, isBasisAt_of _ _ _ fun z => ?_, ?_⟩
  · change Aᴴ *ᵥ z ∈ _ ↔ _
    rw [Deco.Lsh, mem_localization_dual d.2.L_lattice.fg, stdAt, ← show dual (hStd E n) (stdLat E n) = _ from stdLat_unimodular,
      mem_localization_dual stdLat_lattice.fg]
    constructor
    · intro H m hm
      obtain ⟨l, rfl⟩ := (Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 hA0.isUnit)) m
      rw [hStd_mulVec]
      exact H l ((hL l).2 hm)
    · intro H l hl
      rw [← hStd_mulVec]
      exact H _ ((hL l).1 hl)
  · change (conjPrime₂ P.1).valuation E (q * Aᴴ.det) = 1
    rw [valuation_conjP, Matrix.det_conjTranspose, star_mul', star_star, star_natCast, hA]

end Lat

section Closure

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ}

theorem finite_inDeg {ι : Type} [Fintype ι] (lam : ι → DomWeight a) (s' : ι → ℤ) :
    {m : DVar ι a b →₀ ℕ | InDeg lam s' m}.Finite := by
  refine (Finsupp.finite_of_degree_le (∑ τ, ∑ i : Fin a, ((lam τ).w i + s' τ)).toNat).subset fun m hm => ?_
  have h : (m.degree : ℤ) = ∑ τ, ∑ i : Fin a, ((lam τ).w i + s' τ) := by
    rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, Nat.cast_sum]
    exact Finset.sum_congr rfl fun τ _ => by rw [← hm τ, Fintype.sum_prod_type]
  rw [Set.mem_setOf_eq, ← h, Int.toNat_natCast]

theorem val_le_one_iff {ι : X.K →+* ℂ_[p]} {w : HeightOneSpectrum (𝓞 X.K)} (h : Induces ι w) (x : X.K) :
    NormedField.valuation (ι x) ≤ 1 ↔ w.valuation X.K x ≤ 1 := by
  rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact ⟨GlobalTheory.DatumJets.Place.valuation_le_one_of_norm ι w h x, GlobalTheory.MomPlace.norm_le_one_of_valuation X.K p ι w h x⟩

def ptMat (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]) (x : HomE X.E a b) (τ : X.Tau) : Matrix (Fin a) (Fin b) ℂ_[p] :=
  Matrix.of fun α β => un τ * ι (X.emb τ (adj x (Pi.single β 1) α))

theorem ptMat_mulVec (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]) (x : HomE X.E a b) (τ : X.Tau) (y : Sp X.E b) :
    ptMat ι un x τ *ᵥ (fun i => ι (X.emb τ (y i))) = un τ • fun i => ι (X.emb τ (adj x y i)) := by
  funext α
  conv_rhs => rw [← LinearMap.toMatrix'_mulVec]
  simp only [ptMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    LinearMap.toMatrix'_apply, Finset.mul_sum, mul_assoc]

theorem admissible_adjointRationalPointPadicMatrix {ι : X.K →+* ℂ_[p]} {w : HeightOneSpectrum (𝓞 X.K)} (h : Induces ι w) {un : X.Tau → ℂ_[p]}
    (hun : ∀ τ, ‖un τ‖ = 1) {L : Submodule (𝓞 X.E) (Sp X.E a)} {L' : Submodule (𝓞 X.E) (Sp X.E b)} {x : HomE X.E a b}
    (hx : ∀ τ, ∀ y ∈ L', adj x y ∈ localization₂ (pullW τ w).asIdeal L) :
    admitted NormedField.valuation ι (fun τ => tauLat X.emb τ L) (fun τ => tauLat X.emb τ L') (ptMat ι un x) := by
  intro τ y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    beta_reduce
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      beta_reduce
      rw [ptMat_mulVec]
      have h1 : (fun i => X.emb τ (adj x l i)) ∈ localization₂ w.asIdeal (tauLat X.emb τ L) := by
        obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 (hx τ l hl)
        refine (mem_locP _ _ _).2 ⟨X.embO τ s, hs, Submodule.subset_span ⟨_, hsx, ?_⟩⟩
        exact bc_bcV_osmul (X.emb τ) s _
      have h2 : NormedField.valuation (un τ) ≤ 1 := by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, hun, NNReal.coe_one]
      exact Submodule.smul_mem _ (⟨un τ, h2⟩ : (NormedField.valuation (K := ℂ_[p])).integer)
        (GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP (val_le_one_iff h) _ _ h1)
    | zero =>
      have : (fun i => ι ((0 : Fin b → X.K) i)) = 0 := by funext i; simp
      rw [this, Matrix.mulVec_zero]
      exact zero_mem _
    | add z z' _ _ hz hz' =>
      have : (fun i => ι ((z + z') i)) = (fun i => ι (z i)) + fun i => ι (z' i) := by funext i; simp
      rw [this, Matrix.mulVec_add]
      exact add_mem hz hz'
    | smul c z _ hz =>
      have : (fun i => ι ((c • z) i)) = ι (c : X.K) • fun i => ι (z i) := by
        funext i
        exact map_mul ι (c : X.K) (z i)
      rw [this, Matrix.mulVec_smul]
      exact Submodule.smul_mem _ (⟨ι (c : X.K), (val_le_one_iff h _).2 (w.valuation_le_one c)⟩ :
        (NormedField.valuation (K := ℂ_[p])).integer) hz
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul c y _ hy => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hy

theorem jetOp_of_closure {ι : X.K →+* ℂ_[p]} {w : HeightOneSpectrum (𝓞 X.K)} (h : Induces ι w) {un : X.Tau → ℂ_[p]}
    (hun : ∀ τ, ‖un τ‖ = 1) {hab : a < b} {lam : X.Tau → DomWeight a} {lam' : X.Tau → DomWeight b} {s s' : X.Tau → ℤ}
    {n : X.Tau → ℕ} (hw : WtCompat hab lam lam' s s' n) {L : Submodule (𝓞 X.E) (Sp X.E a)} {L' : Submodule (𝓞 X.E) (Sp X.E b)}
    (hL : Submodule.IsLattice X.E L) (hL' : Submodule.IsLattice X.E L') {B : X.Tau → GL (Fin a) X.E} {B' : X.Tau → GL (Fin b) X.E}
    (hB : ∀ τ, IsBasisAt (pullW τ w) L (B τ)) (hB' : ∀ τ, IsBasisAt (pullW τ w) L' (B' τ)) {Sup : Set (HomE X.E a b)}
    (hS : ∀ x ∈ Sup, ∀ τ, ∀ y ∈ L', adj x y ∈ localization₂ (pullW τ w).asIdeal L) (κ : X.K) {M : Set (DVar X.Tau a b →₀ ℕ)}
    (hM : ∀ m, InDeg lam s' m → m ∈ M) {J : (DVar X.Tau a b →₀ ℕ) → X.K}
    (hJ : InIntClosure Sup (fun x m => ι κ * GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.ptTab ι un x m) M fun m => ι (J m)) :
    ∀ F ∈ localization₂ w.asIdeal (nabAtr X.emb lam L), ∃ G ∈ localization₂ w.asIdeal (nabAtr X.emb lam' L'),
      jetOp lam lam' J n F =
        (κ * detFac s s' (fun τ => Formalism.UG.bc (X.emb τ) (B τ)) fun τ => Formalism.UG.bc (X.emb τ) (B' τ)) • G := by
  classical
  let _ : StarRing X.K := starRingOfComm
  refine GlobalTheory.JetPoint.closureIntegral X.K w ℂ_[p] _ NormedField.valuation ι (val_le_one_iff h) X.Tau a b hab lam lam' s s' n hw
    (fun τ => tauLat X.emb τ L) (fun τ => tauLat X.emb τ L') _ _
    (fun τ => ⟨(GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ L hL).fg, bc_isBasisAt (X.emb τ) w (hB τ)⟩)
    (fun τ => ⟨(GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ L' hL').fg, bc_isBasisAt (X.emb τ) w (hB' τ)⟩) κ J
    fun ε hε => ?_
  obtain ⟨c, hc1, hc2, hc3⟩ := hJ (finite_inDeg lam s').toFinset (fun m hm => hM m (by simpa using hm)) ‖ι ε‖
    (norm_pos_iff.2 ((map_ne_zero ι).2 hε))
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun i => c (e i), fun i => ptMat ι un (e i), fun i => ?_,
    fun i => admissible_adjointRationalPointPadicMatrix h hun (hS _ (hc1 (e i).2)), fun m hm => ?_⟩
  · rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    exact hc2 _
  · rw [NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    refine le_of_eq_of_le ?_ (hc3 m (by simpa using hm)).le
    congr 2
    rw [Finsupp.sum, ← Finset.sum_coe_sort c.support, ← e.sum_comp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _

end Closure

section Step

variable {X : Fields} {Pr : Primes X}

theorem unramOver {S : Set ℕ} (mu : Tup X.F X.E X.K S) {l : ℕ} (hl : l.Prime) (hS : l ∈ S) :
    GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.UnramOver (mu : Chr X.F X.E X.K) l := by
  intro v h5 hv
  have hgood : GoodPl X.E S v := by
    by_contra hn
    exact hv (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 mu.2).2 v) hn)
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

theorem stdOver (hPr : Pr.Ok) {u : Pr.Word} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (d : DecoSet X.E n (Pr.vT u) SG) (h : StdAtT d.1) : GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.T u) d.1.N := by
  intro P hP
  rw [← hPr.piT_norm u] at hP
  rcases P.isPrime.mem_or_mem hP with h1 | h1
  · exact h ⟨P, (mem_divs (hPr.piT_ne_zero u) _).2 h1⟩
  · have h2 := GlobalTheory.StdReps.at_conj_eq d (h ⟨conjPrime₂ P, (mem_divs (hPr.piT_ne_zero u) _).2 h1⟩)
    rwa [conjP_conjP'] at h2

theorem sub_eq_half {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {i : ℕ} (hi : i < R.m) {hab : R.N i < R.N (i + 1)}
    {s s' : X.Tau → ℤ} {n : X.Tau → ℕ} (hw : WtCompat hab (W.lamTrue u i) (W.lamTrue u (i + 1)) s s' n) (τ : X.Tau) :
    s τ - s' τ = ((R.t + 1) / 2 : ℕ) := by
  have h1 := congrArg (Int.cast : ℤ → ℚ) (hw.1 τ ⟨0, R.N_pos i⟩)
  have h2 : _ = ((W.lamTrue u i τ).w ⟨0, R.N_pos i⟩ : ℚ) + _ - _ :=
    W.lamTrue_old u hi τ (Fin.castLE hab.le ⟨0, R.N_pos i⟩) (R.N_pos i)
  have h3 := cast_t_add_one_div_two R
  push_cast at h1
  rw [h2] at h1
  unfold sExp sExp' Ranks.N at h1
  rw [Nat.add_sub_cancel] at h1
  have h4 : ((s τ - s' τ : ℤ) : ℚ) = ((((R.t + 1) / 2 : ℕ) : ℤ) : ℚ) := by
    rw [Int.cast_natCast, h3]
    push_cast at h1 ⊢
    linarith
  exact_mod_cast h4

end Step

theorem barStd : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → JetsAll Z.W sel mu cst (ambOf s B χ cD) u i (i + 1) → AlcoveAt Z.W u (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), seenBarC Z.Pr u w → ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet Z.X.E (Z.R.N i) (Z.Pr.vT u) SG) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet Z.X.E (Z.R.N (i + 1)) (Z.Pr.vT u) SG') (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ∃ y' ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.Lsh, term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y = ((Z.Pr.T u : Z.X.K) ^ (Z.X.f * ((Z.R.t + 1) / 2))) • y' := by
  intro hJM hP Z H s cc δ B χ cD sel S mu cst u i hi hyp hJ hAl w hw SG SG' d fr d' fr' Ξ₀ hstd hfr hfr' hbox hint y hy
  classical
  have hX := hyp.ok.fields
  have hPr := hyp.ok.primes
  haveI : Fact (Z.Pr.T u).Prime := ⟨hPr.T_prime u⟩
  have hTw := hw.T_mem hX hPr
  have hsd : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hsd' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  have hv : ∀ τ, conjPrime₂ (pullW τ w) ∈ Z.Pr.vT u := fun τ => (conjP_pullW_mem_vT_iff hPr u τ w).2 (hw τ)

  obtain ⟨ι, hι⟩ := GlobalTheory.DatumJets.Place.exists_embedding (p := Z.Pr.T u) w hTw
  have hind : Induces ι w := fun y => by rw [hι]; rfl
  have hcop : Nat.Coprime (Ideal.absNorm cc) (Z.Pr.T u) := by
    obtain ⟨τ⟩ := hX.nonempty_Tau
    rw [← hPr.vT_norm u _ (hv τ)]
    exact hyp.cop _ (Finset.mem_union_left _ (hv τ))
  obtain ⟨un, hun, hmom⟩ := hJM Z hyp.ok H s cc δ B χ cD hyp.ana u hcop w ι hind
  have hclo := (hmom sel S mu cst hyp.isSel hyp.host (fun P hP => hyp.cop P (Finset.mem_union_right _ hP)) i _ hi rfl SG SG'
    d d' hstd.1 hstd.2 Ξ₀ (fun x _ => ⟨hint x, hbox.2 x⟩)).1 hw

  obtain ⟨m0, eta, ht, hq⟩ := hyp.tied
  have hscal := (((GlobalTheory.CharVal.charValAtT Z H s χ u hyp.ok hyp.ana.1 hyp.ana.2.1 hyp.ana.2.2.2.2.1 hyp.chiK).2.2 m0 eta ht sel
    hyp.isSel S mu (unramOver mu (hPr.T_prime u) (hyp.host (Or.inr ⟨u, rfl⟩)))
    (fun k => unramOver mu (hPr.g_prime k) (hyp.host (Or.inl (by fin_cases k <;> simp)))) cst hq ⟨i, hi⟩).1 w hTw).1.2
    _ _ d.1.N fr d'.1.N fr' hsd hsd' (stdOver hPr d hstd.1) (stdOver hPr d' hstd.2) hfr hfr'

  obtain ⟨σ, σ', hwt, -⟩ := GlobalTheory.ColPeriod.chainWeights Z.X Z.Pr Z.R Z.W u i hi
  have hval := fun τ => (GlobalTheory.CharVal.splitOver_vT hX hPr u (hv τ)).val
  choose Bs hBs hBd using fun τ => exists_basis_Lsh d ⟨_, hv τ⟩ (hstd.1 _) (hval τ)
  choose Bt hBt hBd' using fun τ => exists_basis_Lsh d' ⟨_, hv τ⟩ (hstd.2 _) (hval τ)
  simp only [conjP_conjP'] at hBs hBd hBt hBd'
  obtain ⟨G, hG, hGe⟩ := jetOp_of_closure hind hun hwt d.2.Lsh_lattice d'.2.Lsh_lattice hBs hBt (Sup := suppBar d.1 d'.1)
    (fun x hx τ y hy => by
      have := adj_mem d d' hx ⟨_, hv τ⟩ hy
      rwa [conjP_conjP'] at this) 1
    (M := RatIdx (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
      fun x => phiT Z.X.K d.1 d'.1 x * Ξ₀ x)
    (fun m hm x hx _ => hJ _ _ hsd hsd' x hx m fun τ => by
      refine (hm τ).trans (Finset.sum_congr rfl fun a _ => ?_)
      rw [hwt.2.2 τ]
      ring)
    (by simpa only [map_one, one_mul] using hclo) y
    (localization_mono _ (Submodule.comap_mono (usage₁₁ _ _)) hy)
  rw [← GlobalTheory.KerT.localization_delAtr_eq_localization_nabAtr hP Z.X _ _ _ (hPr.T_prime u) hAl w hTw _ d'.2.Lsh_lattice] at hG
  have hT0 : (Z.Pr.T u : Z.X.K) ≠ 0 := Nat.cast_ne_zero.2 (hPr.T_prime u).ne_zero
  have hvT : w.valuation Z.X.K (Z.Pr.T u) ≠ 0 := by simpa using hT0
  have hdet : ∀ {n : ℕ} (τ : Z.X.Tau) (C : GL (Fin n) Z.X.E),
      (pullW τ w).valuation Z.X.E (Z.Pr.T u * (C : Matrix (Fin n) (Fin n) Z.X.E).det) = 1 →
      w.valuation Z.X.K ((Formalism.UG.bc (Z.X.emb τ) C : GL (Fin n) Z.X.K) : Matrix (Fin n) (Fin n) Z.X.K).det =
        (w.valuation Z.X.K (Z.Pr.T u))⁻¹ := by
    intro n τ C hC
    have h1 := GlobalTheory.CharVal.val_emb_eq_one (GlobalTheory.CharVal.mem_pullW τ w) hC
    rw [map_mul, map_natCast, map_mul, RingHom.map_det] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hfac : w.valuation Z.X.K (detFac σ σ' (fun τ => Formalism.UG.bc (Z.X.emb τ) (Bs τ)) fun τ => Formalism.UG.bc (Z.X.emb τ) (Bt τ)) =
      w.valuation Z.X.K (Z.Pr.T u) ^ (Z.X.f * ((Z.R.t + 1) / 2)) := by
    rw [detFac, map_prod, Fields.f, mul_comm, pow_mul, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_mul, map_zpow₀, map_zpow₀, hdet τ _ (hBd τ), hdet τ _ (hBd' τ), inv_zpow', inv_zpow', ← zpow_add₀ hvT,
      ← zpow_natCast, ← sub_eq_half Z.W u hi hwt τ]
    congr 1
    ring
  rw [term, ker, stepT, GlobalTheory.ColPeriod.kerOf_thDistC _ _ _ (GlobalTheory.ColPeriod.cAof_pos sel mu cst)
    (GlobalTheory.ColPeriod.cBof_pos sel mu cst hPr u) _ _ _ _ _ _ d.2.lat d'.2.lat, LinearMap.smul_apply, hGe, one_mul, smul_smul]
  refine ⟨(((Z.Pr.T u : Z.X.K) ^ (Z.X.f * ((Z.R.t + 1) / 2)))⁻¹ * _) • G, GlobalTheory.ColPeriod.smul_mem_localizationAt_of_le w _ ?_ hG,
    by rw [smul_smul, mul_inv_cancel_left₀ (pow_ne_zero _ hT0)]⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.UnitAt GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.scal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.muInv at hscal
  rw [map_mul, map_mul, hfac, hscal, one_mul, map_inv₀, map_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hvT)]

end GlobalTheory.BarStd
