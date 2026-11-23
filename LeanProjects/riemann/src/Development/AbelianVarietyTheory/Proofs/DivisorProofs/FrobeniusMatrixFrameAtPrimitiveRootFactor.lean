import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffExpSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLinesOfLatticeAtLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionAtLowLevelPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeAtLevelsIffUpToLevel

noncomputable section

namespace GlobalTheory.WachRoots

open PowerSeries GlobalTheory.SenLines GlobalTheory.SenLines.Coords GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries GlobalTheory.WachPlace

section Series

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

theorem zc_X_pow_mul (c : F⟦X⟧) (m : ℕ) (j : ℤ) : zc (X ^ m * c) (j + m) = zc c j := by
  rcases lt_or_ge j 0 with h | h
  · rw [zc_neg c h]
    unfold zc
    split_ifs with h'
    · rw [coeff_X_pow_mul', if_neg (by omega)]
    · rfl
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [← Nat.cast_add, zc_nat, zc_nat, coeff_X_pow_mul]

theorem lines_zero_eq {r : ℕ} (U : Fin r → ℤ) (hU : ∀ a, 0 ≤ U a) (d : Fin r → M) (c : Fin r → F⟦X⟧) :
    lines (fun _ => 0) d c =
      lines U d ((Matrix.diagonal fun a => (X : F⟦X⟧) ^ (U a).toNat).mulVec c) := by
  funext m
  rw [lines_apply, lines_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_diagonal, add_zero, ← zc_X_pow_mul (c k) (U k).toNat m, Int.toNat_of_nonneg (hU k)]

theorem shiftSer_eq_graded {r : ℕ} (d : Fin r → M) :
    shiftSer 0 (Submodule.span F (Set.range d)) =
      gradedSer fun a : ℤ => Submodule.span F (d '' {k | a ≤ (fun _ => (0 : ℤ)) k}) := by
  apply le_antisymm
  · refine le_iSup_of_le (f := fun a : ℤ => shiftSer a (Submodule.span F (d '' {k | a ≤ (fun _ => (0 : ℤ)) k}))) 0 ?_
    simp
  · refine iSup_le fun a y hy => ⟨fun k hk => ?_, fun k => Submodule.span_mono (Set.image_subset_range _ _) (hy.2 k)⟩
    by_cases ha : a ≤ 0
    · exact hy.1 k (by omega)
    · simpa [ha] using hy.2 k

theorem rescale_C_X_pow (χ : F) (m : ℕ) : rescale χ ((X : F⟦X⟧) ^ m) = C (χ ^ m) * X ^ m := by
  rw [map_pow, rescale_X, mul_pow, map_pow]

theorem matrices_of_lines {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] (lev : A →+* F⟦X⟧)
    (L : N →+ (ℤ → M)) {n : ℕ} (b : Module.Basis (Fin n) A N) (U : Fin n → ℤ) (hU : ∀ a, 0 ≤ U a) (d : Fin n → M)
    (hd : LinearIndependent F d) (hL : ∀ a x, L (a • x) = serAct (lev a) (L x)) (hS : SpanIsLines L U d F)
    (φ : N → N) (hφ : ∀ y, ∃ a : Fin n → A, φ y = ∑ k, a k • φ (b k))
    (hS' : SpanIsLines (fun y => L (φ y)) (fun _ => 0) d F)
    (P Γ : Mx A n n) (hP : ∀ k, φ (b k) = ∑ m, P m k • b m) (χ : F) (hχ : χ ≠ 0)
    (hΓ : ∀ k (j : ℤ), L (∑ m, Γ m k • b m) j = χ ^ j • L (b k) j) :
    ∃ G H : (Mx F⟦X⟧ n n)ˣ,
      P.map lev = (G : Mx F⟦X⟧ n n) * Matrix.diagonal (fun a => (X : F⟦X⟧) ^ (U a).toNat) * (H : Mx F⟦X⟧ n n) ∧
      Γ.map lev * ((G : Mx F⟦X⟧ n n) * Matrix.diagonal (fun a => (X : F⟦X⟧) ^ (U a).toNat)).map (rescale χ) =
        (G : Mx F⟦X⟧ n n) * Matrix.diagonal (fun a => (X : F⟦X⟧) ^ (U a).toNat) := by
  classical
  set T : Mx F⟦X⟧ n n := Matrix.diagonal (fun a => (X : F⟦X⟧) ^ (U a).toNat) with hT
  have hex : ∀ x : N, ∃ c : Fin n → F⟦X⟧, L x = lines U d c := fun x =>
    (hS (L x)).mp ⟨1, fun _ => x, fun _ => 1, by simp [serAct_one]⟩
  choose e he using hex
  have hinj := lines_injective U hd
  let E : Mx F⟦X⟧ n n := Matrix.of fun j k => e (b k) j
  have hE : ∀ a : Fin n → A, e (∑ m, a m • b m) = E.mulVec fun m => lev (a m) := fun a => by
    apply hinj
    rw [← he, map_sum]
    simp only [hL, he, serAct_lines]
    rw [← lines_sum]
    congr 1
    funext j
    simp only [Matrix.mulVec, dotProduct, E, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hEu : IsUnit E := by
    refine Matrix.mulVec_surjective_iff_isUnit.1 fun c => ?_
    obtain ⟨s, x, f, h⟩ := (hS (lines U d c)).mpr ⟨c, rfl⟩
    refine ⟨∑ j, f j • fun m => lev (b.repr (x j) m), hinj ?_⟩
    rw [h, Matrix.mulVec_sum, lines_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, ← hE, b.sum_repr, ← serAct_lines, ← he]
  have hφe : ∀ a : Fin n → A, e (∑ k, a k • φ (b k)) = (E * P.map lev).mulVec fun m => lev (a m) := fun a => by
    have : ∑ k, a k • φ (b k) = ∑ m, (P.mulVec a m) • b m := by
      simp only [hP, Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    rw [this, hE, ← Matrix.mulVec_mulVec]
    congr 1
    funext m
    exact RingHom.map_mulVec lev P a m
  have h1 : ∀ k, ∃ c, (E * P.map lev).mulVec (Pi.single k 1) = T.mulVec c := fun k => by
    obtain ⟨c, hc⟩ := (hS' (L (φ (b k)))).mp ⟨1, fun _ => b k, fun _ => 1, by simp [serAct_one]⟩
    refine ⟨c, hinj ?_⟩
    have h2 := hφe (Pi.single k 1)
    rw [show (∑ m, (Pi.single k 1 : Fin n → A) m • φ (b m)) = φ (b k) by simp [Pi.single_apply],
      show (fun m => lev ((Pi.single k 1 : Fin n → A) m)) = Pi.single k 1 by
        funext m; simp [Pi.single_apply, apply_ite lev]] at h2
    rw [← h2, ← he, hc, ← lines_zero_eq U hU]
    rfl
  have h2 : ∀ k, ∃ c, T.mulVec (Pi.single k 1) = (E * P.map lev).mulVec c := fun k => by
    obtain ⟨s, x, f, h⟩ := (hS' (lines (fun _ => 0) d (Pi.single k 1))).mpr ⟨_, rfl⟩
    choose a ha using hφ
    refine ⟨∑ j, f j • fun m => lev (a (x j) m), hinj ?_⟩
    rw [← lines_zero_eq U hU, h, Matrix.mulVec_sum, lines_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, ← hφe, ← ha, ← serAct_lines, ← he]
  choose c1 hc1 using h1
  choose c2 hc2 using h2
  have e1 : E * P.map lev = T * Matrix.of fun j k => c1 k j := by
    ext1 j k
    have := congrFun (hc1 k) j
    rw [Matrix.mulVec_single_one] at this
    exact this
  have e2 : T = (E * P.map lev) * Matrix.of fun j k => c2 k j := by
    ext1 j k
    have := congrFun (hc2 k) j
    rw [Matrix.mulVec_single_one] at this
    exact this
  have hH : (Matrix.of fun j k => c1 k j : Mx F⟦X⟧ n n) * (Matrix.of fun j k => c2 k j) = 1 := by
    rw [e1, mul_assoc] at e2
    ext1 j k
    have := congrFun (congrFun e2 j) k
    rw [hT, Matrix.diagonal_mul, ← mul_one (Matrix.diagonal _), Matrix.diagonal_mul] at this
    exact (mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) this).symm
  have hHu : IsUnit (Matrix.of fun j k => c1 k j : Mx F⟦X⟧ n n) := IsUnit.of_mul_eq_one _ hH
  have e3 : E * Γ.map lev = Matrix.diagonal (fun j => C (χ ^ (-U j))) * E.map (rescale χ) := by
    ext1 j k
    have h3 : (E * Γ.map lev) j k = e (∑ m, Γ m k • b m) j := by rw [hE]; rfl
    rw [h3, Matrix.diagonal_mul]
    ext m
    have := coeff_eq_of_apply U hd (e (∑ m, Γ m k • b m)) (e (b k)) (χ ^ ((m : ℤ) - U j)) (m - U j)
      (by rw [← he, ← he, hΓ]) j
    rw [sub_add_cancel, zc_nat, zc_nat] at this
    rw [this, coeff_C_mul, Matrix.map_apply, coeff_rescale, sub_eq_add_neg, zpow_add₀ hχ, zpow_natCast]
    simp only [E, Matrix.of_apply]
    ring
  obtain ⟨G, hG⟩ := hEu
  refine ⟨G⁻¹, hHu.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, mul_assoc, ← e1, ← hG, Units.inv_mul_cancel_left]
  · rw [eq_comm, Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, hG, e3, mul_assoc, ← Matrix.map_mul, ← hG,
      Units.mul_inv_cancel_left, hT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    rw [rescale_C_X_pow, ← mul_assoc, ← map_mul, ← zpow_natCast, Int.toNat_of_nonneg (hU j), ← zpow_add₀ hχ]
    simp

end Series

theorem exists_perm_of_map_eq {ι α : Type} [Fintype ι] {a b : ι → α}
    (h : Finset.univ.val.map a = Finset.univ.val.map b) : ∃ s : Equiv.Perm ι, ∀ i, b (s i) = a i := by
  classical
  refine ⟨Equiv.ofFiberEquiv (f := a) (g := b) fun c => Fintype.equivOfCardEq ?_, Equiv.ofFiberEquiv_map _⟩
  have := congrArg (Multiset.count c) h
  simp only [Multiset.count_map] at this
  simpa [Fintype.card_subtype, eq_comm, Finset.card, Finset.filter] using this

theorem eq_exp {L : Type} [Field L] [CharZero L] [Algebra ℚ L] (E : L⟦X⟧) (h0 : constantCoeff E = 1)
    (h1 : derivative L E = E) : E = exp L := by
  have h2 : derivative L (exp L) = exp L := derivative_exp L
  ext m
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    have a := congrArg (coeff m) h1
    have b := congrArg (coeff m) h2
    rw [coeff_derivative] at a b
    exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero m) (by rw [a, b, ih])

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD LL O v f) (T : LocLat G Qp LL O) (i : ZMod f) (ζ : LL)

theorem φD_smulA (a : LetA O f) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O f) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

theorem phiNlev_eq (φ : ↥(W.N T) → ↥(W.N T)) (hφ : ∀ y, (φ y : W.DD T) = W.φD T y) {w : LL⟦X⟧} (hw : IsUnit w)
    (hQ : W.lev i ζ W.Q = X * w) :
    phiNlev W T i ζ = serSpan LL (Set.range fun y => W.levN T i ζ (φ y)) := by
  unfold phiNlev
  congr 1
  ext u
  constructor
  · rintro ⟨y, hy, hu, m, hm, h⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    have hl : IsLaurent (W.levN T i ζ (φ ⟨y, hy⟩)) := W.levN_supp T i ζ _
    rw [show (⟨_, hm⟩ : ↥(W.N T)) = W.Q ^ m • φ ⟨y, hy⟩ from Subtype.ext (by rw [Submodule.coe_smul, hφ]),
      LevelCompare.levN_smul, map_pow, hQ] at h
    obtain ⟨w', hw'⟩ := hw.exists_right_inv
    have h2 := congrArg (serMul (w' ^ m)) h
    rw [← LevelCompare.serMul_mul _ _ hu, ← LevelCompare.serMul_mul _ _ hl, ← mul_pow, mul_left_comm, mul_comm w',
      hw', mul_one] at h2
    funext j
    have := congrFun h2 (j + m)
    rw [LevelCompare.serMul_X_pow, LevelCompare.serMul_X_pow, add_sub_cancel_right] at this
    exact this.symm
  · rintro ⟨y, rfl⟩
    refine ⟨y, y.2, W.levN_supp T i ζ _, 0, by rw [pow_zero, one_smul, ← hφ]; exact (φ y).2, ?_⟩
    rw [← LevelCompare.levN_smul]
    congr 1
    exact Subtype.ext (congrArg (W.Q ^ 0 • ·) (hφ y))

theorem lev_const (a : LetA O f) : W.lev i ζ a = W.lev i ζ (fun _ => a i) := by
  have := W.lev_letter i ζ (a - fun _ => a i) (by simp)
  rwa [map_sub, sub_eq_zero] at this

theorem exists_levOne : ∃ ψ : O⟦X⟧ →+* LL⟦X⟧, (∀ c, ψ (C c) = C (algebraMap O LL c)) ∧ ψ X = W.lev i ζ letπ ∧
    ∀ a, W.lev i ζ a = ψ (a i) :=
  ⟨(W.lev i ζ).toRingHom.comp (Pi.constRingHom (ZMod f) O⟦X⟧), fun c => ((congrArg (W.lev i ζ) (funext fun _ => (PowerSeries.algebraMap_apply (R := O) (A := O)).symm)).trans
      ((W.lev i ζ).commutes c)).trans (PowerSeries.algebraMap_apply (R := O) (A := LL)), rfl,
    lev_const W i ζ⟩

theorem matrices_at [CharZero LL] {n : ℕ} (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (U : Fin n → ℤ)
    (hU : ∀ a, 0 ≤ U a) (d : Fin n → T.V ⊗[Qp] BdR) (hd : LinearIndependent LL d)
    (hζ : IsPrimitiveRoot ζ (PD.p ^ W.s)) (hS : SpanIsLines (W.levN T i ζ) U d LL)
    (hS' : phiNlev W T i ζ = shiftSer 0 (Submodule.span LL (Set.range d))) (γ : W.Gam) (P Γ : Mx (LetA O f) n n)
    (hP : ∀ k, W.φD T (b k : W.DD T) = ∑ m, P m k • (b m : W.DD T))
    (hΓ : ∀ k, W.γD T γ (b k : W.DD T) = ∑ m, Γ m k • (b m : W.DD T)) (χ : LL) (hχ : χ ≠ 0)
    (hγ : ∀ (x : ↥(W.N T)) (j : ℤ), W.levN T i ζ ⟨_, W.N_Γ T γ x x.2⟩ j = χ ^ j • W.levN T i ζ x j) :
    ∃ G H : (Mx LL⟦X⟧ n n)ˣ,
      P.map (W.lev i ζ) =
        (G : Mx LL⟦X⟧ n n) * Matrix.diagonal (fun a => (X : LL⟦X⟧) ^ (U a).toNat) * (H : Mx LL⟦X⟧ n n) ∧
      Γ.map (W.lev i ζ) *
          ((G : Mx LL⟦X⟧ n n) * Matrix.diagonal (fun a => (X : LL⟦X⟧) ^ (U a).toNat)).map (rescale χ) =
        (G : Mx LL⟦X⟧ n n) * Matrix.diagonal (fun a => (X : LL⟦X⟧) ^ (U a).toNat) := by
  have h1 : ∀ y : ↥(W.N T), W.φD T y = ∑ k, W.φA (b.repr y k) • W.φD T (b k : W.DD T) := fun y => by
    conv_lhs => rw [← b.sum_repr y]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, φD_smulA]
  have h2 : ∀ y : ↥(W.N T), W.φD T y ∈ W.N T := fun y => by
    rw [h1]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [hP]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (b m).2
  obtain ⟨w, hw, hQ⟩ := ((GlobalTheory.NL.LevPt.lev_values W i ζ ⟨_, hζ⟩).2.2.1 hζ).1
  rw [phiNlev_eq W T i ζ (fun y => ⟨_, h2 y⟩) (fun _ => rfl) hw hQ, shiftSer_eq_graded] at hS'
  refine matrices_of_lines (W.lev i ζ).toRingHom (W.levN T i ζ) b U hU d hd
    (fun a x => funext (W.levN_smul T i ζ a x)) hS (fun y => ⟨_, h2 y⟩)
    (fun y => ⟨fun k => W.φA (b.repr y k), Subtype.ext ?_⟩)
    (SplitFil.spanIsLines_of_graded _ _ d _ (fun y => W.levN_supp T i ζ _) (fun _ => rfl) hS') P Γ
    (fun k => Subtype.ext ?_) χ hχ fun k j => ?_
  · simpa only [Submodule.coe_sum, Submodule.coe_smul] using h1 y
  · simpa only [Submodule.coe_sum, Submodule.coe_smul] using hP k
  · rw [← hγ]
    refine congrArg (fun z => W.levN T i ζ z j) (Subtype.ext ?_)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using (hΓ k).symm

theorem toDR_Dlet_eq (τ : K →ₐ[Qp] LL) (hb : Function.Surjective (algebraMap K₀ K))
    (hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i)
    (hF : ∀ a, toDR (PD := PD) T (FilLet W T i τ a) = FildR PD T.ρ τ a) {n : ℕ} (U : Fin n → ℤ)
    (d : Fin n → T.V ⊗[Qp] BdR) (hs : ∀ a, FildR PD T.ρ τ a = Submodule.span LL (d '' {k | a ≤ U k})) :
    toDR (PD := PD) T (Dlet W T i) = Submodule.span LL (Set.range d) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
      GlobalTheory.Per.FilLetUnram.ι_mem_DdRE PD T.ρ hb τ (by rw [hτ]; exact hx)
    obtain ⟨a, ha⟩ := GlobalTheory.Per.FilCount.filV_exhaustive PD (LL := LL) (ιV PD (LL := LL) (V := T.V) x)
    have h2 : ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ a := ⟨h1, ha⟩
    rw [hs] at h2
    exact Submodule.span_mono (Set.image_subset_range _ _) h2
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have h6 : d k ∈ FildR PD T.ρ τ (U k) := by
      rw [hs]
      exact Submodule.subset_span ⟨k, le_refl (U k), rfl⟩
    rw [← hF] at h6
    exact Submodule.map_mono inf_le_left h6

end Generic

section Local

open GlobalTheory.AdmLoc

set_option maxHeartbeats 1000000 in

theorem exists_lines {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {E : LocFon l P AI H} {C : LocCmpT l P AI H E} (hT : LocTied l P AI)
    (h4 : GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.LatticeAtLevels l P AI H E C) {K LL : FinExt l} (hA : CaseA K LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {n : ℕ} (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Fin n → ℤ)
    (hc : CrysWith (P.PD K) (H.W K 1 LL hA.2.2).emb T.ρ fun i => Finset.univ.val.map (U i))
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ l) :
    ∃ d : Fin n → T.V ⊗[ℚ_[l]] P.R.BdR, LinearIndependent ↥LL.1 d ∧
      SpanIsLines ((H.W K 1 LL hA.2.2).levN T i ζ) (U i) d ↥LL.1 ∧
      phiNlev (H.W K 1 LL hA.2.2) T i ζ = shiftSer 0 (Submodule.span ↥LL.1 (Set.range d)) := by
  obtain ⟨τ, hpt⟩ := AllRoots.exists_isPt H hA.2.2 i ζ (by rwa [pow_one])
  have hbij : Function.Bijective (algebraMap ↥(K0 K) ↥K.1) :=
    ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩
  have hτ : (resEmb hA.2.2 τ).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) =
      (H.W K 1 LL hA.2.2).emb i := AlgHom.ext fun x => hpt.1 x _ rfl
  let e : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 := AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) hbij
  have hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 := by
    rw [← Nat.card_congr (e.arrowCongr AlgEquiv.refl), ← Nat.card_eq_of_bijective _ (H.W K 1 LL hA.2.2).emb_bij,
      Nat.card_zmod, e.toLinearEquiv.finrank_eq]
  obtain ⟨hdr, hspan⟩ := GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T.V T.ρ hc.1
  have hfil := GlobalTheory.Per.DdREqDcris.FildR_eq (P.PD K) T.ρ hbij.2
    (GlobalTheory.Per.DdREqDcris.map_Dcris_eq (P.PD K) T.ρ hbij.2 hspan) (resEmb hA.2.2 τ)
  rw [hτ] at hfil
  have hr := (GlobalTheory.Per.LetterDim.tied_letter_component_finrank l P AI hT K LL T.V T.ρ).2 hcard hdr
    (resEmb hA.2.2 τ)
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI hT K LL T.V T.ρ).1
  have : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) T.ρ (resEmb hA.2.2 τ)) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) T.ρ) inf_le_left
  have hexh : ∀ x ∈ DdRE (P.PD K) T.ρ (resEmb hA.2.2 τ), ∃ a, x ∈ FildR (P.PD K) T.ρ (resEmb hA.2.2 τ) a :=
    fun x hx => (GlobalTheory.Per.FilCount.filV_exhaustive (P.PD K) (LL := ↥LL.1) x).imp fun a ha => ⟨hx, ha⟩
  obtain ⟨u, d, hu, hd, hs⟩ := GlobalTheory.Per.Sen.adapted_basis_jumps (DdRE (P.PD K) T.ρ (resEmb hA.2.2 τ))
    (FildR (P.PD K) T.ρ (resEmb hA.2.2 τ)) (Finset.univ.val.map (U i)) _ hr
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.Per.FilCount.filV_antitone (P.PD K) hab)) (fun a => inf_le_left) hexh
    (fun x hx => GlobalTheory.Cmp.JumpDict.filV_sep (P.PD K) (LL := ↥LL.1) x fun a => (hx a).2)
    (hc.2 i _ fun x => congrArg (fun f => f x) hτ)
  have hn : Module.finrank ↥LL.1 T.V = n := by simpa using congrArg Multiset.card hu
  subst hn
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq hu.symm
  have hs' : ∀ a, FildR (P.PD K) T.ρ (resEmb hA.2.2 τ) a =
      Submodule.span ↥LL.1 ((d ∘ σ) '' {k | a ≤ U i k}) := fun a => by
    rw [hs a, Set.image_comp]
    congr 2
    ext k
    constructor
    · intro hk
      exact ⟨σ.symm k, by simpa [← hσ] using hk, σ.apply_symm_apply k⟩
    · rintro ⟨k', hk', rfl⟩
      simpa [hσ] using hk'
  have hF := fun a => GlobalTheory.Per.FilLetUnram.toDR_FilLet (H.W K 1 LL hA.2.2) T i _ a hbij.2 hτ (hfil a)
  have h5 := (h4 K 1 LL hA.2.2 T hc.1 i ζ).2.1 τ hpt
  refine ⟨d ∘ σ, hd.comp _ σ.injective, SplitFil.spanIsLines_of_graded _ _ _ _
    ((H.W K 1 LL hA.2.2).levN_supp T i ζ) hs' (h5.2.trans (congrArg _ (funext hF))), h5.1.trans (congrArg _ ?_)⟩
  exact toDR_Dlet_eq (H.W K 1 LL hA.2.2) T i _ hbij.2 hτ hF _ _ hs'

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} {f : ℕ}
  (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) f)

theorem lev_eq_exp (i : ZMod f) (ζ : ↥(OL LL)) (hζ : IsPrimitiveRoot (ζ : ↥LL.1) l) (jj : (↥(OL LL))⟦X⟧ →+* (↥LL.1)⟦X⟧)
    (hj : IsExpAt (OL LL).val.toRingHom ζ jj) (a : LetA ↥(OL LL) f) : W.lev i (ζ : ↥LL.1) a = jj (a i) := by
  haveI : CharZero ↥LL.1 := algebraRat.charZero _
  obtain ⟨E, h0, h1, hE⟩ := W.lev_π i (ζ : ↥LL.1) ⟨1, by rwa [P.PD_p, pow_one]⟩
  rw [eq_exp E h0 h1] at hE
  obtain ⟨ψ, g1, g2, g3⟩ := exists_levOne W i (ζ : ↥LL.1)
  have h := GlobalTheory.WachExp.ev_unique LL (C (ζ : ↥LL.1) * exp ↥LL.1 - 1)
    (by simpa using GlobalTheory.WachExp.norm_root_sub_one_lt LL hζ.pow_eq_one) ψ jj
    g1 hj.1 (g2.trans (eq_sub_of_add_eq' hE)) hj.2
  rw [g3, h]

end Local

open NumberField Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing

set_option maxHeartbeats 1000000 in

theorem frame_at_root : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n : ℕ) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Fin n → ℤ) (γ : ((HW l).W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (u c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ (fun i => Finset.univ.val.map (U i)) → (∀ i a, 0 ≤ U i a) → IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N → (((HW l).W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u → u = 1 + (l : ℤ_[l]) * c → IsPrimitiveRoot ζ l → IsExpAt (OL LL).val.toRingHom ζ jj → ∀ i, ∃ G H : (Mx (PowerSeries ↥LL.1) n n)ˣ, (N.P i).map (fun y => jj (inc l ↥(OL LL) y)) = (G : Mx (PowerSeries ↥LL.1) n n) * Matrix.diagonal (fun a => (X : PowerSeries ↥LL.1) ^ (U i a).toNat) * (H : Mx (PowerSeries ↥LL.1) n n) ∧ ((1 + (X : PowerSeries ↥(OL LL)) • N.D i).map (fun y => jj (inc l ↥(OL LL) y))) * ((G : Mx (PowerSeries ↥LL.1) n n) * Matrix.diagonal (fun a => (X : PowerSeries ↥LL.1) ^ (U i a).toNat)).map (rescale ((OL LL).val.toRingHom (algebraMap ℤ_[l] ↥(OL LL) u))) = (G : Mx (PowerSeries ↥LL.1) n n) * Matrix.diagonal (fun a => (X : PowerSeries ↥LL.1) ^ (U i a).toNat) := by
  intro D HW F Cm l _ K LL hA T n U γ b N u c ζ jj hc hU hfr hχ hu hζ hj i
  haveI : CharZero ↥LL.1 := algebraRat.charZero _
  have hζ' : IsPrimitiveRoot (ζ : ↥LL.1) l := hζ.map_of_injective (f := (OL LL).val) Subtype.val_injective
  obtain ⟨d, hd, hS, hS'⟩ := exists_lines (D.locT l)
    ((LevelCompare.coeffForm_iff_latticeAtLevels D HW F Cm).1 (GlobalTheory.NL.LatLevel.lattice_at_level D HW F Cm) l)
    hA T U hc i ζ hζ'
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      (((HW l).W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) - ((1 : ℕ) : ↥LL.1)) := by
    have h0 : 0 ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c)) :=
      ((D.loc l).v_O LL _).2 (algebraMap ℤ_[l] ↥(OL LL) c).2
    rw [hχ, hu, map_add, map_add, map_one, map_one, Nat.cast_one, Nat.cast_one, add_sub_cancel_left, map_mul, map_mul,
      map_natCast, map_natCast, AddValuation.map_mul, (D.loc l).v_l]
    exact le_add_of_nonneg_right h0
  obtain ⟨G, H, h1, h2⟩ := matrices_at ((HW l).W K 1 LL hA.2.2) T i (ζ : ↥LL.1) b (U i) (hU i) d hd
    (by rwa [(D.loc l).PD_p, (HW l).W_s, pow_one]) hS hS' γ
    (Matrix.of fun m k i => inc l ↥(OL LL) (N.P i m k))
    (Matrix.of fun m k i => inc l ↥(OL LL) ((1 + (X : (↥(OL LL))⟦X⟧) • N.D i) m k)) hfr.2.1 hfr.2.2.1
    (algebraMap ↥(OL LL) ↥LL.1 (((HW l).W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)))
    ((((HW l).W K 1 LL hA.2.2).χΓ γ).isUnit.map _).ne_zero fun x k => by
      have h1 := ((Cm l).C K 1 LL hA.2.2).tie.levB_Γ T hc.1 γ i ζ ζ 1 1
        (by rwa [(D.loc l).PD_p, pow_one]) hv (pow_one _).symm x (((HW l).W K 1 LL hA.2.2).N_Γ T γ x x.2) k
      have h2 := ((Cm l).C K 1 LL hA.2.2).tie.levN_eq T i ζ ⟨_, ((HW l).W K 1 LL hA.2.2).N_Γ T γ x x.2⟩ k
      have h3 := ((Cm l).C K 1 LL hA.2.2).tie.levN_eq T i ζ x k
      exact h2.trans (((congrArg _ h1).trans (LinearMap.map_smul _ _ _)).trans (congrArg _ h3.symm))
  have key := lev_eq_exp ((HW l).W K 1 LL hA.2.2) i ζ hζ' jj hj
  rw [hχ] at h2
  refine ⟨G, H, Eq.trans ?_ h1, Eq.trans (congrArg₂ (· * ·) ?_ rfl) h2⟩
  · ext1 m k
    exact (key fun i => inc l ↥(OL LL) (N.P i m k)).symm
  · ext1 m k
    exact (key fun i => inc l ↥(OL LL) ((1 + (X : (↥(OL LL))⟦X⟧) • N.D i) m k)).symm

end GlobalTheory.WachRoots
