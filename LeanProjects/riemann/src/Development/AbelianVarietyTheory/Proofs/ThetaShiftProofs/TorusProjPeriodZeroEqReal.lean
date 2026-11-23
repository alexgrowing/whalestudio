import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix

namespace PolarisedLattice

theorem real_pos_of_int_pos {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (hs : ∀ i j, M i j = M j i)
    (hp : ∀ x : ι → ℤ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x) : (M.map (Int.cast : ℤ → ℝ)).PosDef := by
  set N : Matrix ι ι ℝ := M.map (Int.cast : ℤ → ℝ) with hN
  have hH : N.IsHermitian := by
    ext i j; simp [hN, hs i j]
  have hcast : ∀ x : ι → ℤ, (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ)) = ((x ⬝ᵥ M *ᵥ x : ℤ) : ℝ) := by
    intro x
    simp [hN, dotProduct, mulVec]
  have hq : ∀ x : ι → ℚ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ)) := by
    intro x
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
    choose y hy using hd
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    have hxy : (fun i => (y i : ℝ)) = ((d : ℤ) : ℝ) • (fun i => (x i : ℝ)) := by
      funext i
      have := congrArg (fun q : ℚ => (q : ℝ)) (hy i)
      simpa [Submonoid.smul_def] using this
    have h1 : (0 : ℝ) ≤ ((y ⬝ᵥ M *ᵥ y : ℤ) : ℝ) := by
      by_cases h : y = 0
      · simp [h]
      · exact_mod_cast (hp y h).le
    rw [← hcast, hxy, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
    exact nonneg_of_mul_nonneg_right h1 (mul_self_pos.2 hd0)
  have hsd : N.PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun x => ?_⟩
    have hd : DenseRange (Pi.map fun (_ : ι) => (Rat.cast : ℚ → ℝ)) := DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on (p := fun x => 0 ≤ star x ⬝ᵥ N *ᵥ x) x ?_ (fun q => ?_)
    · exact isClosed_le continuous_const (by fun_prop)
    · exact hq q
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, h0⟩ := exists_mulVec_eq_zero_iff.2 h
    have := hp v hv
    simp [h0] at this
  refine hsd.posDef_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (IsUnit.mk0 _ ?_))
  have : N.det = (M.det : ℝ) := (Int.cast_det M).symm
  rw [this]; exact_mod_cast hdet

theorem exists_posDef_smul_add {ι : Type} [Fintype ι] {N C : Matrix ι ι ℝ} (hN : N.PosDef) (hC : C.IsHermitian) :
    ∃ T₀ : ℝ, ∀ t, T₀ < t → (t • N + C).PosDef := by
  have hp : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ N *ᵥ x := fun x hx => by
    simpa using (posDef_iff_dotProduct_mulVec.1 hN).2 hx
  have hc : ContinuousOn (fun x : ι → ℝ => -(x ⬝ᵥ C *ᵥ x) / (x ⬝ᵥ N *ᵥ x)) (Metric.sphere 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (hp x ?_).ne'
    rintro rfl; simp at hx
  obtain ⟨T₀, hT⟩ := ((isCompact_sphere (0 : ι → ℝ) 1).image_of_continuousOn hc).bddAbove
  refine ⟨T₀, fun t ht => posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩⟩
  · refine IsHermitian.add ?_ hC
    rw [IsHermitian, conjTranspose_smul, hN.1]; simp
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h1 := hT ⟨‖x‖⁻¹ • x, by simp [norm_smul, hn.ne'], rfl⟩
    have h2 := hp x hx
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h1
    have h3 : -(‖x‖⁻¹ * (‖x‖⁻¹ * x ⬝ᵥ C *ᵥ x)) / (‖x‖⁻¹ * (‖x‖⁻¹ * x ⬝ᵥ N *ᵥ x)) =
        -(x ⬝ᵥ C *ᵥ x) / (x ⬝ᵥ N *ᵥ x) := by field_simp
    rw [h3, div_le_iff₀ h2] at h1
    simp only [star_trivial, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
    nlinarith

theorem lattice_of_im {L W : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] [NormedAddCommGroup W]
    [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℝ W]
    (E : LinearMap.BilinForm ℤ L) (hE : Function.Injective E) (P : L →+ W) (S : W → W →ₗ[ℂ] ℂ)
    (hS : ∀ a b, (S (P b) (P a)).im = E a b) (hr : Module.finrank ℤ L = Module.finrank ℝ W) :
    Function.Injective P ∧ DiscreteTopology P.range ∧ Submodule.span ℝ (Set.range P) = ⊤ := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let M : Matrix _ _ ℤ := Matrix.of fun i j => E (b i) (b j)
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, h0⟩ := exists_vecMul_eq_zero_iff.2 h
    have h1 : E (∑ i, v i • b i) = 0 := b.ext fun j => by
      have := congrFun h0 j
      simpa [M, vecMul, dotProduct] using this
    have h2 : ∑ i, v i • b i = 0 := hE (by rw [h1, map_zero])
    exact hv (funext (Fintype.linearIndependent_iff.1 b.linearIndependent v h2))
  have hdet' : (M.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [← Int.cast_det]; exact_mod_cast hdet
  have hli : LinearIndependent ℝ fun i => P (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    have : c ᵥ* M.map (Int.cast : ℤ → ℝ) = 0 := by
      funext j
      have h1 := congrArg (fun v => (S (P (b j)) v).im) hc
      simp only [map_sum, ← algebraMap_smul ℂ (c _) (P _), map_smul, map_zero, Complex.im_sum, smul_eq_mul,
        Complex.coe_algebraMap, Complex.im_ofReal_mul, hS, Complex.zero_im] at h1
      simpa [M, vecMul, dotProduct] using h1
    exact congrFun (eq_zero_of_vecMul_eq_zero hdet' this)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℝ W := by
    rw [← hr, Module.finrank_eq_card_chooseBasisIndex]
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => P (b i)) :=
    (hli.span_eq_top_of_card_eq_finrank' hcard).ge
  let B := Module.Basis.mk hli htop
  have hB : Set.range B = Set.range fun i => P (b i) := by simp [B]
  have hrange : P.range = (Submodule.span ℤ (Set.range B)).toAddSubgroup := by
    have : Submodule.span ℤ (Set.range B) = LinearMap.range P.toIntLinearMap := by
      rw [hB, LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp]; rfl
    rw [this]; rfl
  refine ⟨(injective_iff_map_eq_zero P).2 fun a ha => hE ?_, ?_, ?_⟩
  · rw [map_zero]
    refine LinearMap.ext fun c => ?_
    have := hS a c
    rw [ha, map_zero, Complex.zero_im] at this
    exact_mod_cast this.symm
  · rw [hrange]; infer_instance
  · exact eq_top_iff.2 (htop.trans (Submodule.span_mono (Set.range_comp_subset_range _ _)))

end PolarisedLattice

namespace AnArc

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem EF_bijective : Function.Bijective A.EF := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have h : ∀ v', A.EF v v' = 0 := fun v' => by rw [hv]; rfl
    refine La.ext ?_ (AddMonoidHom.ext fun x => ?_) ?_
    · refine (Module.Free.chooseBasis ℤ A.X).ext_elem fun i => ?_
      have := h (La.mk 0 ((Module.Free.chooseBasis ℤ A.X).coord i).toAddMonoidHom 0)
      simpa [EF_apply] using this
    · have := h (La.mk x 0 0)
      simpa [EF_apply] using this
    · refine A.Ef_bij.1 (LinearMap.ext fun m => ?_)
      have := h (La.mk 0 0 m)
      simpa [EF_apply] using this
  · intro φ
    let φ₁ : A.X →+ ℤ := AddMonoidHom.mk' (fun y => φ (La.mk y 0 0)) fun y y' => by
      rw [← map_add]; congr 1; ext <;> simp
    let φ₂ : Module.Dual ℤ (Module.Dual ℤ A.X) :=
      (AddMonoidHom.mk' (fun n : Module.Dual ℤ A.X => φ (La.mk 0 n.toAddMonoidHom 0)) fun n n' => by
        rw [← map_add]; congr 1; ext <;> simp).toIntLinearMap
    let φ₃ : Module.Dual ℤ A.abelian₂ :=
      (AddMonoidHom.mk' (fun l : A.abelian₂ => φ (La.mk 0 0 l)) fun n n' => by
        rw [← map_add]; congr 1; ext <;> simp).toIntLinearMap
    obtain ⟨y, hy⟩ := (Module.evalEquiv ℤ A.X).surjective φ₂
    obtain ⟨l, hl⟩ := A.Ef_bij.2 φ₃
    refine ⟨La.mk y (-φ₁) l, LinearMap.ext fun v => ?_⟩
    have h2 : v.n y = φ (La.mk 0 v.n 0) := congrArg (fun f => f v.n.toIntLinearMap) hy
    have h3 : A.Ef l v.l = φ (La.mk 0 0 v.l) := congrArg (fun f => f v.l) hl
    conv_rhs => rw [La.eq_add_parts v, map_add, map_add]
    rw [EF_apply, La.mk_y, La.mk_n, La.mk_l, h2, h3]
    simp [φ₁]; ring

theorem finrank_La : Module.finrank ℤ A.La = Module.finrank ℝ A.V := by
  have h1 : Module.finrank ℤ (A.X →+ ℤ) = Module.finrank ℤ A.X := by
    rw [(addMonoidHomLequivInt ℤ (A := A.X) (B := ℤ)).finrank_eq]
    simp [Module.finrank_linearMap]
  have h2 : Module.finrank ℤ A.abelian₂ = 2 * A.gB := by
    rw [ZLattice.rank ℝ A.abelian₂, finrank_real_of_complex]; simp
  have h3 : Module.finrank ℝ A.V = 2 * Module.finrank ℂ A.V := by
    rw [← Module.finrank_mul_finrank ℝ ℂ A.V, Complex.finrank_real_complex]
  rw [A.laEquiv.finrank_eq, Module.finrank_prod, Module.finrank_prod, h1, h2, h3, finrank_V]; ring

def kappa : (Fin A.gB → ℂ) →ₗ[ℂ] (A.X →+ ℂ) where
  toFun z :=
    { toFun := fun x => A.H z (A.ct x) / (2 * Complex.I)
      map_zero' := by simp
      map_add' := fun x x' => by rw [map_add, H_add_right, add_div] }
  map_add' z z' := AddMonoidHom.ext fun x => by
    show A.H (z + z') _ / _ = _ / _ + _ / _
    rw [H_add_left, add_div]
  map_smul' c z := AddMonoidHom.ext fun x => by
    show A.H (c • z) _ / _ = c * (_ / _)
    rw [H_smul_left, mul_div_assoc]

@[simp] theorem kappa_apply (z : Fin A.gB → ℂ) (x : A.X) : A.kappa z x = A.H z (A.ct x) / (2 * Complex.I) := rfl

def torusProj : A.V →ₗ[ℂ] (A.X →+ ℂ) := LinearMap.fst ℂ _ _ + A.kappa ∘ₗ LinearMap.snd ℂ _ _

theorem torusProj_def (v : A.V) : A.torusProj v = v.1 + A.kappa v.2 := rfl

theorem torusProj_apply (v : A.V) (x : A.X) :
    A.torusProj v x = v.1 x + A.H v.2 (A.ct x) / (2 * Complex.I) := rfl

def Bw (w : ℂ) : A.X →+ A.X →+ ℝ :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun x => (A.T y x + w * A.be y x + A.kappa (A.ct y) x).im)
    fun x x' => by simp only [map_add, ← Complex.add_im]; push_cast; ring_nf)
    fun y y' => AddMonoidHom.ext fun x => by
      simp only [map_add, AddMonoidHom.add_apply, LinearMap.add_apply, AddMonoidHom.mk'_apply, ← Complex.add_im]
      push_cast; ring_nf

theorem Bw_apply (w : ℂ) (y x : A.X) : A.Bw w y x = (A.T y x + w * A.be y x + A.kappa (A.ct y) x).im := rfl

theorem div_two_I (h : ℂ) : h / (2 * Complex.I) = (h.im / 2 : ℝ) + (-(h.re / 2) : ℝ) * Complex.I := by
  rw [div_eq_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
  apply Complex.ext <;> simp

theorem H_re_symm (z z' : Fin A.gB → ℂ) : (A.H z z').re = (A.H z' z).re := by
  rw [← A.H_conj z z', Complex.conj_re]

theorem H_im_symm (z z' : Fin A.gB → ℂ) : (A.H z z').im = -(A.H z' z).im := by
  rw [← A.H_conj z z', Complex.conj_im, neg_neg]

theorem Bw_eq (w : ℂ) (y x : A.X) :
    A.Bw w y x = (A.T y x).im + w.im * A.be y x - (A.H (A.ct y) (A.ct x)).re / 2 := by
  rw [Bw_apply, kappa_apply, div_two_I]; simp; ring

theorem Bw_symm (w : ℂ) (y x : A.X) : A.Bw w y x = A.Bw w x y := by
  rw [Bw_eq, Bw_eq, A.T_symm, A.be_symm, H_re_symm]

theorem torusProj_Pw_im (w : ℂ) (v : A.La) (x : A.X) : (A.torusProj (A.Pw w v) x).im = A.Bw w v.y x := by
  rw [torusProj_apply, Pw_fst_apply, Pw_snd, H_add_left, Bw_eq, div_two_I, div_two_I]
  simp [A.H_re_symm (A.ct x) v.l]; ring

theorem torusProj_Pw_re (w : ℂ) (v : A.La) (x : A.X) : (A.torusProj (A.Pw w v) x).re =
    v.n x + (A.H v.l (A.ct x)).im + (A.T v.y x).re + w.re * A.be v.y x + (A.H (A.ct v.y) (A.ct x)).im / 2 := by
  rw [torusProj_apply, Pw_fst_apply, Pw_snd, H_add_left, div_two_I, div_two_I]
  simp [A.H_im_symm (A.ct x) v.l]; ring

theorem torusProj_periodZero_eq_real (n : A.X →+ ℤ) (l : A.abelian₂) (x : A.X) :
    A.torusProj (A.P0 (La.mk 0 n l)) x = ((n x + (A.H l (A.ct x)).im : ℝ) : ℂ) := by
  rw [← A.degeneratingTori_periodMap_eq_base_of_y_eq_zero 0 (La.mk_y 0 n l)]
  apply Complex.ext
  · rw [torusProj_Pw_re]; simp
  · rw [torusProj_Pw_im]; simp

def BwMat (w : ℂ) : Matrix (Module.Free.ChooseBasisIndex ℤ A.X) (Module.Free.ChooseBasisIndex ℤ A.X) ℝ :=
  Matrix.of fun i j => A.Bw w (Module.Free.chooseBasis ℤ A.X i) (Module.Free.chooseBasis ℤ A.X j)

theorem BwMat_apply (w : ℂ) (i j) :
    A.BwMat w i j = A.Bw w (Module.Free.chooseBasis ℤ A.X i) (Module.Free.chooseBasis ℤ A.X j) := rfl

theorem exists_BwMat_posDef : ∃ T₀ : ℝ, ∀ w : ℂ, T₀ < w.im → (A.BwMat w).PosDef := by
  classical
  let b := Module.Free.chooseBasis ℤ A.X
  let M : Matrix _ _ ℤ := Matrix.of fun i j => A.be (b i) (b j)
  have hM : (M.map (Int.cast : ℤ → ℝ)).PosDef := by
    refine PolarisedLattice.real_pos_of_int_pos M (fun i j => A.be_symm _ _) fun x hx => ?_
    have h0 : ∑ i, x i • b i ≠ 0 := fun h =>
      hx (funext (Fintype.linearIndependent_iff.1 b.linearIndependent x h))
    have := A.be_pos _ h0
    convert this using 1
    simp only [M, dotProduct, mulVec, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum, Matrix.of_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hC : (A.BwMat 0).IsHermitian := by
    ext i j; simp [BwMat_apply, A.Bw_symm 0 (Module.Free.chooseBasis ℤ A.X i)]
  obtain ⟨T₀, hT⟩ := PolarisedLattice.exists_posDef_smul_add hM hC
  refine ⟨T₀, fun w hw => ?_⟩
  convert hT _ hw using 1
  ext i j
  simp [BwMat_apply, Bw_eq, M, b]; ring

theorem map_eq_sum_repr {M : Type} [Ring M] (f : A.X →+ M) (y : A.X) :
    f y = ∑ i, ((Module.Free.chooseBasis ℤ A.X).repr y i : M) * f (Module.Free.chooseBasis ℤ A.X i) := by
  conv_lhs => rw [← (Module.Free.chooseBasis ℤ A.X).sum_repr y]
  simp only [map_sum, map_zsmul, zsmul_eq_mul]

theorem Bw_pos {w : ℂ} (hw : (A.BwMat w).PosDef) {y : A.X} (hy : y ≠ 0) : 0 < A.Bw w y y := by
  have h0 : (fun i => ((Module.Free.chooseBasis ℤ A.X).repr y i : ℝ)) ≠ 0 := fun h => hy <|
    (Module.Free.chooseBasis ℤ A.X).ext_elem fun i => by simpa using congrFun h i
  have := (posDef_iff_dotProduct_mulVec.1 hw).2 h0
  refine this.trans_eq (Eq.symm ?_)
  rw [A.map_eq_sum_repr (A.Bw w y) y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Bw_symm, A.map_eq_sum_repr (A.Bw w _) y]
  simp [mulVec, dotProduct, BwMat_apply, mul_comm]

open Classical in

def dualForm (w : ℂ) : (A.X →+ ℂ) →ₗ[ℂ] (A.X →+ ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun r r' => A.coord r ⬝ᵥ ((A.BwMat w)⁻¹.map Complex.ofReal) *ᵥ star (A.coord r'))
    (fun _ _ _ => by rw [map_add, add_dotProduct])
    (fun _ _ _ => by rw [map_smul, smul_dotProduct]; rfl)
    (fun _ _ _ => by rw [map_add, star_add, mulVec_add, dotProduct_add])
    (fun _ _ _ => by rw [map_smul, star_smul, mulVec_smul, dotProduct_smul]; rfl)

open Classical in

theorem dualForm_apply (w : ℂ) (r r' : A.X →+ ℂ) :
    A.dualForm w r r' = A.coord r ⬝ᵥ ((A.BwMat w)⁻¹.map Complex.ofReal) *ᵥ star (A.coord r') := rfl

theorem dualForm_conj (w : ℂ) (r r' : A.X →+ ℂ) : starRingEnd ℂ (A.dualForm w r r') = A.dualForm w r' r := by
  classical
  have hC : (A.BwMat w).IsHermitian := by
    ext i j; simp [BwMat_apply, A.Bw_symm w (Module.Free.chooseBasis ℤ A.X i)]
  have h : ∀ i k, (A.BwMat w)⁻¹ i k = (A.BwMat w)⁻¹ k i := fun i k => by simpa using hC.inv.apply k i
  simp only [dualForm_apply, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj, Matrix.map_apply, Complex.conj_ofReal]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [h k i]; ring

def BwC (w : ℂ) (y : A.X) : A.X →+ ℂ := Complex.ofRealHom.toAddMonoidHom.comp (A.Bw w y)

@[simp] theorem BwC_apply (w : ℂ) (y x : A.X) : A.BwC w y x = A.Bw w y x := rfl

theorem dualForm_BwC {w : ℂ} (hw : (A.BwMat w).PosDef) (r : A.X →+ ℂ) (y : A.X) :
    A.dualForm w r (A.BwC w y) = r y := by
  classical
  have h1 : star (A.coord (A.BwC w y)) =
      ((A.BwMat w).map Complex.ofReal) *ᵥ fun i => ((Module.Free.chooseBasis ℤ A.X).repr y i : ℂ) := by
    funext i
    rw [Pi.star_apply, coord_apply, BwC_apply, Bw_symm, A.map_eq_sum_repr (A.Bw w _) y]
    simp [mulVec, dotProduct, BwMat_apply, mul_comm]
  have h2 : (A.BwMat w)⁻¹.map Complex.ofReal * (A.BwMat w).map Complex.ofReal = 1 := by
    have := Matrix.map_mul (f := Complex.ofRealHom) (L := (A.BwMat w)⁻¹) (M := A.BwMat w)
    rw [nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hw.isUnit), Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this.symm
  rw [dualForm_apply, h1, mulVec_mulVec, h2, one_mulVec, A.map_eq_sum_repr r y]
  simp [dotProduct, coord_apply, mul_comm]

theorem dualForm_re_im (w : ℂ) (r r' : A.X →+ ℂ) (M : Matrix _ _ ℝ) (hM : M = by classical exact (A.BwMat w)⁻¹) :
    (A.dualForm w r r').re = (fun i => (A.coord r i).re) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).re) +
      (fun i => (A.coord r i).im) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).im) ∧
    (A.dualForm w r r').im = (fun i => (A.coord r i).im) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).re) -
      (fun i => (A.coord r i).re) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).im) := by
  subst hM
  simp only [dualForm_apply, dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, Complex.im_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  constructor <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_ <;> simp <;> ring

theorem dualForm_pos {w : ℂ} (hw : (A.BwMat w).PosDef) {r : A.X →+ ℂ} (hr : r ≠ 0) : 0 < (A.dualForm w r r).re := by
  classical
  rw [(A.dualForm_re_im w r r _ rfl).1]
  have hp : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (A.BwMat w)⁻¹ *ᵥ x := fun x hx => by
    simpa using (posDef_iff_dotProduct_mulVec.1 hw.inv).2 hx
  have hn : ∀ x, 0 ≤ x ⬝ᵥ (A.BwMat w)⁻¹ *ᵥ x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hp x hx).le
  by_cases h : (fun i => (A.coord r i).re) = 0
  · refine add_pos_of_nonneg_of_pos (hn _) (hp _ fun h' => hr (A.coord.map_eq_zero_iff.1 (funext fun i => ?_)))
    exact Complex.ext (congrFun h i) (congrFun h' i)
  · exact add_pos_of_pos_of_nonneg (hp _ h) (hn _)

theorem dualForm_im_of_real (w : ℂ) {r r' : A.X →+ ℂ} (hr : ∀ x, (r x).im = 0) (hr' : ∀ x, (r' x).im = 0) :
    (A.dualForm w r r').im = 0 := by
  rw [(A.dualForm_re_im w r r' _ rfl).2]
  simp [coord_apply, hr, hr', dotProduct, mulVec]

def Hw (w : ℂ) : A.V →ₗ[ℂ] A.V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v v' => A.H v.2 v'.2 + A.dualForm w (A.torusProj v) (A.torusProj v'))
    (fun _ _ _ => by simp only [Prod.snd_add, H_add_left, map_add, LinearMap.add_apply]; ring)
    (fun _ _ _ => by
      simp only [Prod.smul_snd, H_smul_left, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)
    (fun _ _ _ => by simp only [Prod.snd_add, H_add_right, map_add]; ring)
    (fun _ _ _ => by
      simp only [Prod.smul_snd, H_smul_right, map_smul, LinearMap.map_smulₛₗ, smul_eq_mul]; ring)

theorem Hw_apply (w : ℂ) (v v' : A.V) :
    A.Hw w v v' = A.H v.2 v'.2 + A.dualForm w (A.torusProj v) (A.torusProj v') := rfl

theorem Hw_conj (w : ℂ) (v v' : A.V) : starRingEnd ℂ (A.Hw w v v') = A.Hw w v' v := by
  rw [Hw_apply, Hw_apply, map_add, H_conj, dualForm_conj]

theorem Hw_pos {w : ℂ} (hw : (A.BwMat w).PosDef) {v : A.V} (hv : v ≠ 0) : 0 < (A.Hw w v v).re := by
  rw [Hw_apply, Complex.add_re]
  by_cases h : A.torusProj v = 0
  · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext (by simpa [torusProj_def, h2] using h) h2)
    simpa [h] using A.H_pos h2
  · refine add_pos_of_nonneg_of_pos ?_ (A.dualForm_pos hw h)
    by_cases h2 : v.2 = 0
    · simp [h2]
    · exact (A.H_pos h2).le

theorem im_Hw_Pw {w : ℂ} (hw : (A.BwMat w).PosDef) (a b : A.La) :
    (A.Hw w (A.Pw w a) (A.Pw w b)).im = A.EF a b := by
  have hre : ∀ (v : A.La) x, ((A.torusProj (A.Pw w v) - Complex.I • A.BwC w v.y) x).im = 0 := fun v x => by
    simp [torusProj_Pw_im]
  have h1 := A.dualForm_im_of_real w (hre a) (hre b)
  have h2 : A.dualForm w (A.BwC w a.y) (A.torusProj (A.Pw w b)) = starRingEnd ℂ (A.torusProj (A.Pw w b) a.y) := by
    rw [← dualForm_conj, A.dualForm_BwC hw]
  simp only [map_sub, map_smul, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
    A.dualForm_BwC hw, h2, smul_eq_mul] at h1
  simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re,
    Complex.I_im, RingHom.id_apply, torusProj_Pw_re, torusProj_Pw_im, BwC_apply, Complex.ofReal_re,
    Complex.ofReal_im] at h1
  rw [Hw_apply, Complex.add_im, EF_apply, Pw_snd, Pw_snd]
  simp only [H_add_left, H_add_right, Complex.add_im]
  push_cast
  rw [Ef_eq_im]
  rw [A.T_symm b.y a.y, A.be_symm b.y a.y, A.H_im_symm (A.ct b.y) (A.ct a.y), A.H_im_symm b.l (A.ct a.y)] at h1
  linarith

theorem Pw_lattice {w : ℂ} (hw : (A.BwMat w).PosDef) : Function.Injective (A.Pw w) ∧
    DiscreteTopology (A.Pw w).range ∧ Submodule.span ℝ (Set.range (A.Pw w)) = ⊤ :=
  PolarisedLattice.lattice_of_im A.EF A.EF_bijective.1 (A.Pw w) (fun v => (A.Hw w).flip v)
    (fun a b => A.im_Hw_Pw hw a b) A.finrank_La

theorem Hw_actV {w : ℂ} (hw : (A.BwMat w).PosDef) (a : O) (v v' : A.V) :
    A.Hw w (A.actV a v) v' = A.Hw w v (A.actV (star a) v') := by
  have hsp := (A.Pw_lattice hw).2.2
  have him : ∀ v v' : A.V, (A.Hw w (A.actV a v) v').im = (A.Hw w v (A.actV (star a) v')).im := by
    intro v v'
    have hv : v ∈ Submodule.span ℝ (Set.range (A.Pw w)) := hsp ▸ Submodule.mem_top
    have hv' : v' ∈ Submodule.span ℝ (Set.range (A.Pw w)) := hsp ▸ Submodule.mem_top
    induction hv, hv' using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      rw [← Pw_smul, ← Pw_smul, A.im_Hw_Pw hw, A.im_Hw_Pw hw, EF_smul]
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h h' => simp only [map_add, LinearMap.add_apply, Complex.add_im, h, h']
    | add_right x y z _ _ _ h h' => simp only [map_add, Complex.add_im, h, h']
    | smul_left r x y _ _ h =>
      rw [← algebraMap_smul ℂ r x]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.coe_algebraMap, Complex.im_ofReal_mul, h]
    | smul_right r x y _ _ h =>
      rw [← algebraMap_smul ℂ r y]
      simp only [map_smul, LinearMap.map_smulₛₗ, smul_eq_mul, Complex.coe_algebraMap, Complex.conj_ofReal,
        Complex.im_ofReal_mul, h]
  refine Complex.ext ?_ (him v v')
  have := him (Complex.I • v) v'
  simpa using this

def HwMat (w : ℂ) {g : ℕ} (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i j => A.Hw w (h.symm (Pi.single i 1)) (h.symm (Pi.single j 1))

theorem HwMat_isHermitian (w : ℂ) {g : ℕ} (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) : (A.HwMat w h).IsHermitian := by
  ext i j
  exact A.Hw_conj w _ _

theorem hermForm_HwMat (w : ℂ) {g : ℕ} (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) (v v' : A.V) :
    hermForm (A.HwMat w h) (h v) (h v') = A.Hw w v v' := by
  have e : ∀ v : A.V, v = ∑ i, h v i • h.symm (Pi.single i 1) := fun v => h.injective <| by
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    exact pi_eq_sum_univ' _
  conv_rhs => rw [e v, e v']
  simp only [hermForm, HwMat, dotProduct, mulVec, map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
    RingHom.id_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem period_clauses {w : ℂ} (hw : (A.BwMat w).PosDef) {g : ℕ} (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) {L : Type}
    [AddCommGroup L] (e : L ≃+ A.La) (P : L →+ (Fin g → ℂ)) (hP : ∀ x, P x = h (A.Pw w (e x))) :
    Function.Injective P ∧ DiscreteTopology P.range ∧ Submodule.span ℝ (Set.range P) = ⊤ ∧
      ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
        ∀ x y, (hermForm Hm (P x) (P y)).im = A.EF (e x) (e y) := by
  let P' : A.La →+ (Fin g → ℂ) := h.toLinearMap.toAddMonoidHom.comp (A.Pw w)
  have hr : Module.finrank ℤ A.La = Module.finrank ℝ (Fin g → ℂ) :=
    A.finrank_La.trans (h.restrictScalars ℝ).finrank_eq
  obtain ⟨h1, h2, h3⟩ := PolarisedLattice.lattice_of_im A.EF A.EF_bijective.1 P'
    (fun z => (A.Hw w).flip (h.symm z) ∘ₗ h.symm.toLinearMap)
    (fun a b => by simpa [P'] using A.im_Hw_Pw hw a b) hr
  have hPP : (P : L → _) = P' ∘ e := funext hP
  have hrange : Set.range P = Set.range P' := by rw [hPP, e.surjective.range_comp]
  have hrange' : P.range = P'.range := SetLike.coe_injective hrange
  refine ⟨hPP ▸ h1.comp e.injective, hrange' ▸ h2, hrange ▸ h3, A.HwMat w h, A.HwMat_isHermitian w h,
    fun z hz => ?_, fun x y => ?_⟩
  · obtain ⟨v, rfl⟩ := h.surjective z
    rw [hermForm_HwMat]
    exact A.Hw_pos hw fun hv => hz (by simp [hv])
  · rw [hP, hP, hermForm_HwMat, A.im_Hw_Pw hw]

theorem periods_polarised :
    A.EF.IsAlt ∧ Function.Bijective A.EF ∧ (∀ (a : O) x y, A.EF (a • x) y = A.EF x (star a • y)) ∧
    ∃ T₀ : ℝ, ∀ w : ℂ, T₀ < w.im →
      (A.BwMat w).PosDef ∧ Function.Injective (A.Pw w) ∧ (∀ (a : O) x, A.Pw w (a • x) = A.actV a (A.Pw w x)) ∧
      DiscreteTopology (A.Pw w).range ∧ Submodule.span ℝ (Set.range (A.Pw w)) = ⊤ ∧
      (∀ v v', starRingEnd ℂ (A.Hw w v v') = A.Hw w v' v) ∧ (∀ v, v ≠ 0 → 0 < (A.Hw w v v).re) ∧
      (∀ a b, (A.Hw w (A.Pw w a) (A.Pw w b)).im = A.EF a b) ∧
      ∀ (g : ℕ) (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) (P : A.La →+ (Fin g → ℂ)), (∀ x, P x = h (A.Pw w x)) →
        Function.Injective P ∧ DiscreteTopology P.range ∧ Submodule.span ℝ (Set.range P) = ⊤ ∧
          ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            ∀ x y, (hermForm Hm (P x) (P y)).im = A.EF x y := by
  obtain ⟨T₀, hT⟩ := A.exists_BwMat_posDef
  refine ⟨A.EF_isAlt, A.EF_bijective, A.EF_smul, T₀, fun w hw => ?_⟩
  have h := hT w hw
  obtain ⟨h1, h2, h3⟩ := A.Pw_lattice h
  exact ⟨h, h1, A.Pw_smul w, h2, h3, A.Hw_conj w, fun v hv => A.Hw_pos h hv, A.im_Hw_Pw h,
    fun g k P hP => A.period_clauses h k (AddEquiv.refl _) P hP⟩

end AnArc

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField in

theorem AnArc.isPeriod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
    (A : AnArc (𝓞 E)) {w : ℂ} (hw : (A.BwMat w).PosDef) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) (hh : ∀ (a : 𝓞 E) v i, h (A.actV a v) i = ty i (a : E) * h v i)
    (e : D.La ≃+ A.La) (he : ∀ (a : 𝓞 E) x, e (a • x) = a • e x) (hE : ∀ x y, A.EF (e x) (e y) = D.EF x y)
    (P : D.La →+ (Fin g → ℂ)) (hP : ∀ x, P x = h (A.Pw w (e x))) : IsPeriod D ty P := by
  obtain ⟨h1, h2, h3, Hm, h4, h5, h6⟩ := A.period_clauses hw h e P hP
  refine ⟨fun a x i => ?_, h1, h2, h3, Hm, h4, h5, fun x y => by rw [h6, hE]⟩
  rw [hP, hP, he, A.Pw_smul, hh]

end GlobalTheory
