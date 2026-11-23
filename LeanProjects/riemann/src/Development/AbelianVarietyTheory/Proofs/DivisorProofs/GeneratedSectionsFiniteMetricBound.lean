import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory.TrueGeo.FinLow

open SmallSec

variable {F : Type} [Field F] [NumberField F]

theorem exists_mem {O R : Type} [CommRing O] [IsDomain O] [CommRing R] (ρ : O →+* R) (I : Ideal R)
    (h : ∀ P : Ideal R, P.IsPrime → P.comap ρ = ⊥ → ¬ I ≤ P) : ∃ a : O, a ≠ 0 ∧ ρ a ∈ I := by
  by_contra hne
  obtain ⟨P, hP, hIP, hd⟩ := Ideal.exists_le_prime_disjoint I ((nonZeroDivisors O).map ρ)
    (Set.disjoint_left.2 fun _ hI ⟨a, ha, e⟩ => hne ⟨a, nonZeroDivisors.ne_zero ha, e ▸ hI⟩)
  refine h P hP (eq_bot_iff.2 fun a ha => ?_) hIP
  by_contra h0
  exact Set.disjoint_left.1 hd ha ⟨a, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩

theorem exists_w_le {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {ι : Type} [Fintype ι] (c b : ι → e.O)
    (h0 : ((∑ j, c j * b j : e.O) : AlgebraicClosure F) ≠ 0) :
    ∃ j, e.w (∑ j, c j * b j : e.O) ≤ e.w (b j) := by
  by_contra hne
  push Not at hne
  have h₁ (j) : e.O.valuation (c j * b j : e.O) < e.O.valuation (∑ j, c j * b j : e.O) := by
    have h₂ : e.w ((b j : AlgebraicClosure F) / (∑ j, c j * b j : e.O)) < 1 := by
      rw [map_div₀, div_lt_one (e.w.pos h0)]
      exact hne j
    rw [← valuation_lt_one_iff, map_div₀, div_lt_one₀ ((Valuation.pos_iff _).2 h0)] at h₂
    rw [MulMemClass.coe_mul, map_mul]
    exact (mul_le_of_le_one_left' (e.O.valuation_le_one _)).trans_lt h₂
  have h₃ := e.O.valuation.map_sum_lt ((Valuation.ne_zero_iff _).2 h0) (s := Finset.univ) fun j _ => h₁ j
  rw [← AddSubmonoidClass.coe_finset_sum] at h₃
  exact h₃.false

theorem exists_bound_affine {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp (𝓞 F)) {W : X.Opens} (hW : IsAffineOpen W)
    {x : X} (hxW : x ∈ W) {κ : Type} [Fintype κ] (h : κ → X.functionField)
    (hgen : ∀ z ∈ W, (p z).asIdeal = ⊥ → (∀ j, RegAt z (h j)) ∧ ∃ j, UnitAt z (h j)) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (yt : Sp e.O ⟶ X),
      (spMap e.O.subtype ≫ yt) ≫ p =
        spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) →
      (∀ j, RegAt (below (spMap e.O.subtype ≫ yt)) (h j)) → ⊤ ≤ yt ⁻¹ᵁ W →
      ∃ j, NumberField.HeightOneSpectrum.adicAbv F v a ≤ e.w (valAt (spMap e.O.subtype ≫ yt) (h j)) := by
  let ρ := Spec.preimage (hW.fromSpec ≫ p)
  have hρ : Spec.map ρ = hW.fromSpec ≫ p := Spec.map_preimage _
  have hP (P : PrimeSpectrum Γ(X, W)) : (p (hW.fromSpec P)).asIdeal = P.asIdeal.comap ρ.hom :=
    congrArg (fun q : Spec Γ(X, W) ⟶ Sp (𝓞 F) => (q P).asIdeal) hρ.symm
  have hPW (P : PrimeSpectrum Γ(X, W)) : hW.fromSpec P ∈ W := hW.range_fromSpec.le ⟨P, rfl⟩
  have hbo (P : PrimeSpectrum Γ(X, W)) (b : Γ(X, W)) :
      UnitAt (hW.fromSpec P) (fnOf W (gen_mem hxW) b) ↔ b ∉ P.asIdeal := by
    rw [unitAt_fnOf_iff (hPW P)]
    exact iff_of_eq (congrArg (P ∈ ·) (hW.fromSpec_preimage_basicOpen b))
  choose a ha b hab using fun j => BddFin.exists_denom ρ.hom (fnOf W (gen_mem hxW)) (h j) fun P hPp hP0 => by
    obtain ⟨c, hc⟩ := (hgen _ (hPW ⟨P, hPp⟩) ((hP ⟨P, hPp⟩).trans hP0)).1 j
    rw [← hc]
    let := X.presheaf.algebra_section_stalk (⟨_, hPW ⟨P, hPp⟩⟩ : W)
    have := hW.isLocalization_stalk' ⟨P, hPp⟩ (hPW ⟨P, hPp⟩)
    obtain ⟨⟨b, a⟩, e⟩ := @IsLocalization.surj _ _ P.primeCompl _ _ _ this c
    refine ⟨a, a.2, b, ?_⟩
    rw [← algebraMap_germ (hPW ⟨P, hPp⟩), ← algebraMap_germ (hPW ⟨P, hPp⟩), ← map_mul, mul_comm]
    exact congrArg _ e
  obtain ⟨d, hd, hdI⟩ := exists_mem ρ.hom (Ideal.span (Set.range b)) fun P hPp hP0 hle => by
    obtain ⟨j, hj⟩ := (hgen _ (hPW ⟨P, hPp⟩) ((hP ⟨P, hPp⟩).trans hP0)).2
    have h₁ := ((hbo ⟨P, hPp⟩ (ρ.hom (a j))).2 fun hm => ha j (hP0.le hm)).mul hj
    rw [hab] at h₁
    exact (hbo ⟨P, hPp⟩ _).1 h₁ (hle (Ideal.subset_span ⟨j, rfl⟩))
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hdI
  refine ⟨d, hd, fun v e yt hy hr hyt => ?_⟩
  have h₁ : below (spMap e.O.subtype ≫ yt) ∈ W :=
    hyt (x := spMap e.O.subtype (IsLocalRing.closedPoint _)) trivial
  have h₂ := (Points.le_preimage_iff _ _).2 h₁
  have h₃ (a : 𝓞 F) : valAt (spMap e.O.subtype ≫ yt) (fnOf W (gen_mem hxW) (ρ.hom a)) =
      algebraMap F (AlgebraicClosure F) a := by
    rw [valAt_fnOf h₁, Points.valR_eq _ _ h₂]
    have h₄ := Points.specMap_valMap_fromSpec hW _ h₂
    rw [← h₄, Category.assoc, ← hρ, ← Spec.map_comp, ← Spec.map_comp] at hy
    exact congrArg (fun q => q.hom a) (Spec.map_injective hy)
  have h₄ (b : Γ(X, W)) : valAt (spMap e.O.subtype ≫ yt) (fnOf W (gen_mem hxW) b) =
      ((Points.valMap yt W hyt).hom b : e.O) := by
    rw [valAt_fnOf h₁, Points.valR_spMap_comp _ _ _ hyt, Points.valR_eq _ _ hyt]
    rfl
  have h₅ : algebraMap F (AlgebraicClosure F) d =
      (∑ j, (Points.valMap yt W hyt).hom (c j) * (Points.valMap yt W hyt).hom (b j) : e.O) := by
    rw [← h₃, h₄, ← hc, map_sum]
    simp only [map_mul]
  obtain ⟨j, hj⟩ := exists_w_le e _ _ (h₅.symm.trans_ne (by simpa using hd))
  refine ⟨j, ?_⟩
  rw [← h₅, ← h₄, ← hab, valAt_mul (regAt_fnOf h₁ _ _) (hr j), h₃, map_mul, e.w_alg, e.w_alg] at hj
  exact hj.trans (mul_le_of_le_one_left (e.w.nonneg _)
    (v.adicAbv_coe_le_one (K := F) (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _))

theorem exists_bound {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] (p : X ⟶ Sp (𝓞 F)) {ι : Type}
    (U : ι → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i) {κ : Type} [Fintype κ] (h : ι → κ → X.functionField)
    (hgen : ∀ i, ∀ z ∈ U i, (p z).asIdeal = ⊥ → (∀ j, RegAt z (h i j)) ∧ ∃ j, UnitAt z (h i j)) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (yt : Sp e.O ⟶ X),
      (spMap e.O.subtype ≫ yt) ≫ p =
        spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) →
      ∃ i, ⊤ ≤ yt ⁻¹ᵁ U i ∧ ((∀ j, RegAt (below (spMap e.O.subtype ≫ yt)) (h i j)) →
      ∃ j, NumberField.HeightOneSpectrum.adicAbv F v a ≤ e.w (valAt (spMap e.O.subtype ≫ yt) (h i j))) := by
  classical
  choose i hi using hU
  choose W hW hxW hWU using fun x => Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (hi x)
  choose a ha hb using fun x => exists_bound_affine p (hW x) (hxW x) (h (i x))
    fun z hz => hgen _ z (hWU x hz)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X)) (fun x => (W x).isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩
  refine ⟨∏ x ∈ t, a x, Finset.prod_ne_zero_iff.2 fun x _ => ha x, fun v e yt hy => ?_⟩
  obtain ⟨x, hx, hm⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (yt (IsLocalRing.closedPoint e.O))))
  have h₁ := (Points.le_preimage_iff yt (W x)).2 hm
  refine ⟨i x, h₁.trans (Scheme.Hom.preimage_mono _ (hWU x)), fun hr =>
    (hb x v e yt hy hr h₁).imp fun j hj => le_trans ?_ hj⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a hx
  rw [hc, show ((a x * c : 𝓞 F) : F) = a x * c from map_mul (algebraMap (𝓞 F) F) _ _, map_mul]
  exact mul_le_of_le_one_right (AbsoluteValue.nonneg _ _)
    (v.adicAbv_coe_le_one (K := F) (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) c)

theorem main : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : Model Y)
    (L : GlobalTheory.HermLB M.p) (k : ℕ+), A.Induced M L k 0 → ∀ (N : ℕ) (s : Fin N → Y.Fn),
    (∀ i, s i ∈ Y.H0 ((k : ℕ) • A.D)) → (∀ x : Y.X, ∃ i, ((k : ℕ) • A.D).GeneratesAt x (s i)) →
    ∃ c : HeightOneSpectrum (𝓞 F) → ℝ, (Function.support c).Finite ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y), ∃ j,
        Real.exp (-c v) ≤ e.w (valAt y.1 (s j * (eqn A.D (below y.1) : Y.Fn) ^ (k : ℕ))) *
          Real.exp ((k : ℕ) * A.lg v e y) := by
  intro F _ _ C Y A M L k ⟨_, r, hr, _, hfin⟩ N s hs hg
  have := M.ar.isIntegral
  have := isPreimmersion_j M
  have : QuasiCompact M.p := by
    obtain ⟨N, c, hc, h⟩ := M.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← h]
    infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace M.p
  have hη := j_gen_specializes M
  choose t ht using fun (i : L.B.ι) (j : Fin N) => fnMap_surjective M.j hη (s j * (r fun _ => i))
  have hmem {x : Y.X} {i : L.B.ι} (h : M.j x ∈ L.B.U i) :
      x ∈ (L.B.pull M.j).U fun _ => i := Set.mem_iInter.2 fun _ => h
  have hreg (x : Y.X) (i : L.B.ι) (h : M.j x ∈ L.B.U i) (j) : RegAt (M.j x) (t i j) := by
    rw [← regAt_fnMap_iff M.j hη, ht]
    exact (hr.isEqn _ x (hmem h)).regularAt_iff.1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hs j) _)
  obtain ⟨a, ha, hb⟩ := exists_bound M.p L.B.U (exists_chart L.isLB) t fun i z hz h => by
    obtain ⟨z, rfl⟩ := mem_range_j M h
    obtain ⟨j, hj⟩ := hg z
    have h₁ := (hr.isEqn _ z (hmem hz)).generatesAt_iff.1 hj
    rw [← ht] at h₁
    refine ⟨hreg z i hz, j, (unitAt_iff fun h0 => h₁.ne_zero (by rw [h0, map_zero])).2 ⟨hreg z i hz j, ?_⟩⟩
    rw [← regAt_fnMap_iff M.j hη, map_inv₀]
    exact h₁.inv.regAt
  have h0 (v : HeightOneSpectrum (𝓞 F)) : 0 < NumberField.HeightOneSpectrum.adicAbv F v a := AbsoluteValue.pos _ (by simpa using ha)
  refine ⟨fun v => -Real.log (NumberField.HeightOneSpectrum.adicAbv F v a), ?_, fun v e y => ?_⟩
  · refine (Ideal.finite_factors (I := Ideal.span {a}) (by simpa using ha)).subset fun v hv => ?_
    by_contra h₁
    have h₄ : 1 ≤ NumberField.HeightOneSpectrum.adicAbv F v a := not_lt.1 fun h' => h₁
      (Ideal.dvd_span_singleton.2
        ((v.adicAbv_coe_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a).1 h'))
    have h₅ : NumberField.HeightOneSpectrum.adicAbv F v a = 1 := le_antisymm
      (v.adicAbv_coe_le_one (K := F) (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a) h₄
    exact hv (by simp only [h₅, Real.log_one, neg_zero])
  obtain ⟨yt, h⟩ := exists_lift M e y
  obtain ⟨i, hi, h₁⟩ := hb v e yt (by rw [h, Category.assoc, M.pb.w, ← Category.assoc, y.2])
  have h₂ : M.j (below y.1) ∈ L.B.U i := by
    change below (y.1 ≫ M.j) ∈ _
    rw [← h]
    exact hi (x := spMap e.O.subtype (IsLocalRing.closedPoint _)) trivial
  rw [h] at h₁
  obtain ⟨j, hj⟩ := h₁ (hreg _ i h₂)
  refine ⟨j, ?_⟩
  have hu : A.D.IsEqn _ (eqn A.D (below y.1)) := Base.isEqn_eqn _ _
  have hw := unitAt_quot hu (hr.isEqn _ _ (hmem h₂))
  have hb := ((hu.nsmul k).regularAt_iff).1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hs j) _)
  have hl := hfin v e y yt (fun _ => i) h hi
  rw [Units.val_pow_eq_pow_val] at hb
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Pi.zero_apply, mul_zero, sub_zero] at hl
  have h₃ := mul_pow_eq (s j) (eqn A.D (below y.1)) (r fun _ => i) k 1
  rw [pow_one, pow_one, one_mul] at h₃
  rw [neg_neg, Real.exp_log (h0 v), hl, Real.exp_log (e.w.pos (valAt_ne_zero hw)), ← map_mul,
    ← valAt_mul hb hw.regAt, ← h₃, ← ht, valAt_fnMap _ _ _ (hreg _ i h₂ j)]
  exact hj

end GlobalTheory.TrueGeo.FinLow
