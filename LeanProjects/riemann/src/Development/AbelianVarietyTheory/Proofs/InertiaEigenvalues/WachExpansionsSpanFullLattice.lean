import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesEvaluation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachImageDeRhamPlusComponentLevelStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

noncomputable section

namespace GlobalTheory.NL.FullLevel

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_eq_zero (e : PowerSeries L) (f : ℤ → M) (w : ℕ) (h0 : ∀ k : ℤ, k < -(w : ℤ) → f k = 0)
    (k : ℤ) (hk : k < -(w : ℤ)) : conv e f k = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun j => by rw [h0 _ (by omega), smul_zero]

theorem conv_apply (e : PowerSeries L) (f : ℤ → M) (w : ℕ) (h0 : ∀ k : ℤ, k < -(w : ℤ) → f k = 0)
    (n : ℕ) : conv e f ((n : ℤ) - w) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 e • f ((p.2 : ℤ) - w) := by
  rw [conv, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1)),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun p q : ℕ => PowerSeries.coeff p e • f ((q : ℤ) - w))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    congr 2
    omega
  · intro j hj
    by_contra hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    exact hj (by simp only []; rw [h0 _ (by omega), smul_zero])

theorem full_of_det {ι : Type} (D : Submodule L M) {r : ℕ} (d : Module.Basis (Fin r) L D)
    (ex : ι → ℤ → M) (x : Fin r → ι) (w : ℕ) (U : Matrix (Fin r) (Fin r) (PowerSeries L))
    (h0 : ∀ j (k : ℤ), k < -(w : ℤ) → ex (x j) k = 0)
    (hU : ∀ j (n : ℕ), ex (x j) ((n : ℤ) - w) = ∑ a, PowerSeries.coeff n (U a j) • (d a : M))
    (hdet : U.det ≠ 0) : Full D (latSpan ex) := by
  refine ⟨U.det.order.toNat, fun f hf hf0 => ?_⟩
  obtain ⟨u, hu⟩ := (PowerSeries.isUnit_divided_by_X_pow_order hdet).exists_right_inv
  let F : Fin r → PowerSeries L := fun a => PowerSeries.mk fun n => d.repr ⟨f ((n : ℤ) - w), hf _⟩ a
  have hF : ∀ a, U.det ∣ F a := by
    intro a
    have h1 : U.det ∣ PowerSeries.X ^ U.det.order.toNat :=
      ⟨u, by
        conv_rhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := U.det)]
        rw [mul_assoc, hu, mul_one]⟩
    refine h1.trans (PowerSeries.X_pow_dvd_iff.2 fun n hn => ?_)
    have : (⟨f ((n : ℤ) - w), hf _⟩ : D) = 0 := Subtype.ext (hf0 _ (by omega))
    simp [F, this]
  choose F' hF' using hF
  let e : Fin r → PowerSeries L := U.adjugate.mulVec F'
  have he : U.mulVec e = F := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    funext a
    simp [hF']
  have hsum : f = ∑ j, conv (e j) (ex (x j)) := by
    funext k
    rw [Finset.sum_apply]
    rcases lt_or_ge k (-(w : ℤ)) with hk | hk
    · rw [hf0 k (by omega), Finset.sum_eq_zero fun j _ => conv_eq_zero _ _ w (h0 j) k hk]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) - w := ⟨(k + w).toNat, by omega⟩
      have h1 : f ((n : ℤ) - w) = ∑ a, PowerSeries.coeff n (F a) • (d a : M) := by
        have := congrArg Subtype.val (d.sum_repr ⟨f ((n : ℤ) - w), hf _⟩)
        simpa only [F, PowerSeries.coeff_mk, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul] using this.symm
      rw [h1, ← he]
      simp only [conv_apply _ _ w (h0 _), hU, Matrix.mulVec, dotProduct, map_sum, Finset.sum_smul,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm, PowerSeries.coeff_mul, Finset.sum_smul]
  rw [hsum]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨e j, x j, rfl⟩

theorem exists_coord (D : Submodule L M) {r : ℕ} (d : Module.Basis (Fin r) L D) (f : ℤ → M)
    (hf : ∀ k, f k ∈ D) (w : ℕ) : ∃ g : Fin r → PowerSeries L,
      ∀ n : ℕ, f ((n : ℤ) - w) = ∑ a, PowerSeries.coeff n (g a) • (d a : M) := by
  refine ⟨fun a => PowerSeries.mk fun n => d.repr ⟨f ((n : ℤ) - w), hf _⟩ a, fun n => ?_⟩
  have := congrArg Subtype.val (d.sum_repr ⟨f ((n : ℤ) - w), hf _⟩)
  simpa only [PowerSeries.coeff_mk, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul] using this.symm

end Series

theorem exists_det_ne_zero {R ι : Type} [CommRing R] [Nontrivial R] {r : ℕ} (g : ι → Fin r → R)
    (hg : Submodule.span R (Set.range g) = ⊤) : ∃ x : Fin r → ι, (Matrix.of fun j => g (x j)).det ≠ 0 := by
  by_contra h
  push Not at h
  have h1 : (Matrix.detRowAlternating (n := Fin r) (R := R)).toMultilinearMap = 0 :=
    MultilinearMap.ext_of_span_eq_top (g := fun _ => g) (fun _ => hg) fun x => h x
  have h2 := congrArg (fun f => f (1 : Matrix (Fin r) (Fin r) R)) h1
  exact one_ne_zero ((Matrix.det_one (n := Fin r) (R := R)).symm.trans h2)

theorem eq_sum_ev {L R : Type} [Field L] [CommRing R] (Fil : ℤ → AddSubgroup R) (hanti : Antitone Fil)
    (hmul : ∀ a b x y, x ∈ Fil a → y ∈ Fil b → x * y ∈ Fil (a + b)) (hexh : ∀ x, ∃ a, x ∈ Fil a)
    (hsep : ∀ x, (∀ a, x ∈ Fil a) → x = 0) (ι : L → R) (t : R) (ev : PowerSeries L → R)
    (hev : ∀ (f : PowerSeries L) (M : ℕ),
      ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * t ^ k ∈ Fil (M : ℤ))
    {r : ℕ} (P : Fin r → R) (g : Fin r → PowerSeries L) (y : R) (c : ℤ)
    (hy : ∀ M : ℕ, y - ∑ k ∈ Finset.range M, t ^ k * ∑ a, ι (PowerSeries.coeff k (g a)) * P a ∈
      Fil ((M : ℤ) - c)) : y = ∑ a, ev (g a) * P a := by
  choose β hβ using hexh
  obtain ⟨b, hb⟩ := (Set.finite_range fun a => β (P a)).bddBelow
  rw [← sub_eq_zero]
  refine hsep _ fun n => ?_
  obtain ⟨M, h1, h2⟩ : ∃ M : ℕ, n ≤ (M : ℤ) - c ∧ n ≤ (M : ℤ) + b :=
    ⟨(n + c).toNat + (n - b).toNat, by omega, by omega⟩
  have e : y - ∑ a, ev (g a) * P a =
      (y - ∑ k ∈ Finset.range M, t ^ k * ∑ a, ι (PowerSeries.coeff k (g a)) * P a) -
        ∑ a, (ev (g a) - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k (g a)) * t ^ k) * P a := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (s := Finset.range M)]
    simp only [mul_comm, mul_left_comm]
    ring
  rw [e]
  refine sub_mem (hanti h1 (hy M)) (sum_mem fun a _ => hanti h2 ?_)
  exact hmul _ _ _ _ (hev _ M) (hanti (hb ⟨a, rfl⟩) (hβ _))

section Comp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR)

def form (φ : T.V →ₗ[LL] LL) : T.V ⊗[Qp] BdR →ₗ[Qp] BdR :=
  TensorProduct.lift ((LinearMap.mul Qp BdR) ∘ₗ ι.toLinearMap ∘ₗ φ.restrictScalars Qp)

theorem form_tmul (φ : T.V →ₗ[LL] LL) (x : T.V) (b : BdR) : form T ι φ (x ⊗ₜ b) = ι (φ x) * b := by
  simp [form]

theorem form_mul (φ : T.V →ₗ[LL] LL) (b : BdR) (y : T.V ⊗[Qp] BdR) :
    form T ι φ (mulVR T b y) = b * form T ι φ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul x c => simp [mulVR, form_tmul, mul_left_comm]

theorem form_smul (φ : T.V →ₗ[LL] LL) (c : LL) (y : T.V ⊗[Qp] BdR) :
    form T ι φ (c • y) = ι c * form T ι φ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy, mul_add]
  | tmul x b => rw [smul_tmul', form_tmul, form_tmul, map_smul, smul_eq_mul, map_mul, mul_assoc]

theorem form_ker (φ : T.V →ₗ[LL] LL) {y : T.V ⊗[Qp] BdR} (hy : y ∈ compKer T ι) : form T ι φ y = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, y, rfl⟩ := hz
    rw [map_sub, form_smul, form_mul, sub_self]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [form_smul, hx, mul_zero]

theorem form_fil (hι : ∀ c, ι c ∈ PD.Fil 0) (φ : T.V →ₗ[LL] LL) (n : ℤ) {y : T.V ⊗[Qp] BdR}
    (hy : y ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) n) : form T ι φ y ∈ PD.Fil n := by
  obtain ⟨y', hy', _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
  clear hy
  rw [map_add, form_ker T ι φ hy', zero_add]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add]; exact add_mem ha hb
  | tmul x b =>
    have := PD.Fil_mul _ _ _ _ (hι (φ x)) b.2
    rw [zero_add] at this
    simpa [form_tmul] using this

theorem full_of_span {X : Type} (D : Submodule LL (T.V ⊗[Qp] B)) [Module.Finite LL D]
    (hD : Module.finrank LL D = Module.finrank LL T.V) (ex : X → ℤ → T.V ⊗[Qp] B)
    (hmem : ∀ x k, ex x k ∈ D) (hsupp : ∀ x, ∃ m : ℤ, ∀ k < m, ex x k = 0)
    (t : BdR) (ht : IsUnit t) (ev : PowerSeries LL →+* BdR)
    (hev : ∀ (f : PowerSeries LL) (M : ℕ),
      ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * t ^ k ∈ PD.Fil (M : ℤ))
    (Ψ : X → T.V ⊗[Qp] BdR)
    (hspan : ∀ z ∈ FilV PD (LL := LL) (V := T.V) 0, ∃ (m : ℕ) (b : Fin m → BdR) (x : Fin m → X),
      z - ∑ j, mulVR T (b j) (Ψ (x j)) ∈ compKer T ι)
    (hΨ : ∀ (x : X) (a : ℕ), (∀ r : ℤ, r < -(a : ℤ) → ex x r = 0) → ∃ c : ℤ, ∀ M : ℕ,
      mulVR T (t ^ a) (Ψ x) - ∑ r ∈ Finset.range M, mulVR T (t ^ r)
        (ιV PD (LL := LL) (V := T.V) (ex x ((r : ℤ) - (a : ℤ)))) ∈
        compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c)) :
    Full D (latSpan ex) := by
  have : Nontrivial BdR := ⟨⟨PD.ι PD.t, 0, fun h => PD.not_mem_filtration_two (h ▸ zero_mem _)⟩⟩
  have hι : ∀ c, ι c ∈ PD.Fil 0 := by
    intro c
    have h0 := hev (PowerSeries.C c) 0
    have h1 := PD.Fil_anti 0 (hev (PowerSeries.C c) 1)
    have := sub_mem h0 h1
    simpa using this
  set r := Module.finrank LL T.V
  let v : Module.Basis (Fin r) LL T.V := Module.finBasis LL T.V
  let d : Module.Basis (Fin r) LL D := Module.finBasisOfFinrankEq LL D hD
  let g : X → Fin r → BdR := fun x a => form T ι (v.coord a) (Ψ x)
  have hg : Submodule.span BdR (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun BdR (Fin r)).span_eq, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨m, b, x, hx⟩ := hspan (v a ⊗ₜ 1) ⟨v a ⊗ₜ ⟨1, PD.one_mem⟩, by simp⟩
    have : Pi.basisFun BdR (Fin r) a = ∑ j, b j • g (x j) := by
      funext a'
      have := form_ker T ι (v.coord a') hx
      rw [map_sub, sub_eq_zero, map_sum, form_tmul] at this
      simp only [form_mul] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, g, ← this]
      by_cases h : a' = a
      · subst h; simp
      · simp [h]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x j, rfl⟩)
  obtain ⟨x, hx⟩ := exists_det_ne_zero g hg
  choose m hm using hsupp
  obtain ⟨m₀, hm₀⟩ := (Set.finite_range fun j => m (x j)).bddBelow
  let w : ℕ := (-m₀).toNat
  have h0 : ∀ j (k : ℤ), k < -(w : ℤ) → ex (x j) k = 0 := fun j k hk =>
    hm _ _ (lt_of_lt_of_le (by omega) (hm₀ ⟨j, rfl⟩))
  choose U hU using fun j => exists_coord D d (ex (x j)) (hmem _) w
  refine full_of_det D d ex x w (Matrix.of U).transpose h0 hU fun hdet => hx ?_
  let P : Matrix (Fin r) (Fin r) BdR := Matrix.of fun a a' =>
    form T ι (v.coord a') (ιV PD (LL := LL) (V := T.V) (d a))
  have key : (t ^ w) • (Matrix.of fun j => g (x j)) = ev.mapMatrix (Matrix.of U) * P := by
    ext j a'
    obtain ⟨c, hc⟩ := hΨ (x j) w (h0 j)
    refine eq_sum_ev (fun n => (PD.Fil n).toAddSubgroup)
      (fun m n h => antitone_int_of_succ_le PD.Fil_anti h) PD.Fil_mul PD.Fil_exh PD.Fil_sep ι t ev hev
      (fun a => P a a') (U j) _ c fun M => ?_
    have := form_fil PD T ι hι (v.coord a') _ (hc M)
    simp only [map_sub, map_sum, form_mul, hU, map_smul, form_smul] at this
    simp only [Finset.mul_sum, mul_left_comm (t ^ _)]
    exact this
  have := congrArg Matrix.det key
  rw [Matrix.det_transpose] at hdet
  rw [Matrix.det_smul, Matrix.det_mul, ← RingHom.map_det, hdet, map_zero, zero_mul] at this
  exact ((ht.pow w).pow _).mul_right_eq_zero.1 this

end Comp

set_option maxHeartbeats 1600000 in

theorem full_lat : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → Full (Di (HW l) h T i) (Lat C h T i ζ) := by
  intro D HW F Cm l _ K s LL h W E C T hT i ζ hζ
  obtain ⟨h1, h2, -, -, hc⟩ := Points.points D HW l K s LL h
  obtain ⟨τ, hτ⟩ := h1 i ζ hζ
  obtain ⟨-, -, ι, hι⟩ := h2 i ζ τ hτ
  obtain ⟨Ψ, -, hspan, hΨ⟩ := GlobalTheory.T.wach_image_deRham_plus_component_level D HW F Cm l K s LL h T hT i ζ τ ι hι
  obtain ⟨ev, hev, -, ht, -⟩ := EvdR.exists_ev_dR D l K LL s ι
  have := GlobalTheory.Per.LetterDim.finite_Dcris ((D.loc l).PD K) T.ρ hT
  have : Module.Finite ↥LL.1 ↥(Di (HW l) h T i) :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : Di (HW l) h T i ≤ Dcris _ T.ρ))
      (Submodule.inclusion_injective _)
  refine full_of_span ((D.loc l).PD K) T ι (Di (HW l) h T i)
    ((GlobalTheory.Per.LetterDim.tied_letter_component_finrank l _ _ (D.locT l) K LL T.V T.ρ).1 hc hT _)
    (ex C h T i ζ) (fun x k => (C.C K s LL h).tie.levB_mem T i ζ x k)
    (fun x => (C.C K s LL h).tie.levB_supp T i ζ x) (tS (D.loc l) s) ht ev hev Ψ (fun z hz => ?_) hΨ
  obtain ⟨m, b, x, -, hx⟩ := hspan z hz
  exact ⟨m, b, x, hx⟩

end GlobalTheory.NL.FullLevel
