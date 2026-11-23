import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDomainFramesEqGramFramesUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddSmulMemUnitary

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.BaseFrame

open ReciprocityTheory.ChartRestriction.G.FD

section Central

variable {n : ℕ} {Hm P a : Mt n} {S : Set ℂ}

theorem conj_eq_of_path (hH : Hm.det ≠ 0) (hP : P.det ≠ 0) (ha : a.det ≠ 0) (hS : S.Countable)
    (h : ∀ u ∈ Formalism.QuantumDeterminants.UH Hm, ∃ δ : Mt n, (∀ i j, δ i j ∈ S) ∧ δ * (P * (a⁻¹ * u * a)) = P * u)
    (u : ℝ → Mt n) (hu : Continuous u) (h0 : u 0 = 1) (hm : ∀ s, u s ∈ Formalism.QuantumDeterminants.UH Hm) :
    a⁻¹ * u 1 * a = u 1 := by
  let F : ℝ → Mt n := fun s => P * u s * (a⁻¹ * (Hm⁻¹ * (u s)ᴴ * Hm) * a * P⁻¹)
  have hF : Continuous F := by
    have := hu.matrix_conjTranspose
    refine (continuous_const.matrix_mul hu).matrix_mul ?_
    exact ((continuous_const.matrix_mul ((continuous_const.matrix_mul this).matrix_mul
      continuous_const)).matrix_mul continuous_const).matrix_mul continuous_const
  have hinv : ∀ s, u s * (Hm⁻¹ * (u s)ᴴ * Hm) = 1 := fun s => by
    have h1 : (u s)ᴴ * Hm * u s = Hm := hm s
    rw [mul_eq_one_comm, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ Hm, h1,
      Matrix.nonsing_inv_mul _ hH.isUnit]
  have hinv2 : ∀ s, P * (a⁻¹ * u s * a) * (a⁻¹ * (Hm⁻¹ * (u s)ᴴ * Hm) * a * P⁻¹) = 1 := fun s => by
    calc P * (a⁻¹ * u s * a) * (a⁻¹ * (Hm⁻¹ * (u s)ᴴ * Hm) * a * P⁻¹)
        = P * (a⁻¹ * (u s * (a * (a⁻¹ * (Hm⁻¹ * (u s)ᴴ * Hm)))) * a) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv_cancel_left _ _ ha.isUnit, hinv, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ ha.isUnit, Matrix.mul_one, Matrix.mul_nonsing_inv _ hP.isUnit]
  have hδ : ∀ s, (∀ i j, F s i j ∈ S) ∧ F s * (P * (a⁻¹ * u s * a)) = P * u s := fun s => by
    obtain ⟨δ, h1, h2⟩ := h _ (hm s)
    have : F s = δ := by
      show P * u s * _ = δ
      rw [← h2, Matrix.mul_assoc δ, hinv2, Matrix.mul_one]
    rw [this]
    exact ⟨h1, h2⟩
  have hc : F 1 = F 0 := by
    ext i j
    have hij : Continuous fun s => F s i j := hF.matrix_elem i j
    exact hS.isTotallyDisconnected _ (by rintro _ ⟨s, rfl⟩; exact (hδ s).1 i j) (isPreconnected_range hij)
      ⟨1, rfl⟩ ⟨0, rfl⟩
  have hF0 : F 0 = 1 := by
    have := hinv2 0
    rw [h0, Matrix.mul_one, Matrix.nonsing_inv_mul _ ha.isUnit] at this
    show P * u 0 * _ = 1
    rw [h0]
    exact this
  have := (hδ 1).2
  rw [hc, hF0, Matrix.one_mul] at this
  have h3 := congrArg (P⁻¹ * ·) this
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hP.isUnit] using h3

theorem refl_mem (hH : Hm.IsHermitian) (v : Fin n → ℂ) (z : ℂ)
    (hz : star z + z + star z * z * (star v ⬝ᵥ Hm *ᵥ v) = 0) :
    1 + z • (vecMulVec v (star v) * Hm) ∈ Formalism.QuantumDeterminants.UH Hm := by
  first
  | exact @_root_.GlobalTheory.UnitaryPerturbation.one_add_smul_mem_unitary
  | exact _root_.GlobalTheory.UnitaryPerturbation.one_add_smul_mem_unitary
  | (apply _root_.GlobalTheory.UnitaryPerturbation.one_add_smul_mem_unitary <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitaryPerturbation.one_add_smul_mem_unitary <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitaryPerturbation.one_add_smul_mem_unitary <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitaryPerturbation.one_add_smul_mem_unitary ..)

theorem polar (x y : Fin n → ℂ) : vecMulVec x (star y) = (1 / 2 : ℂ) •
    ((vecMulVec (x + y) (star (x + y)) - vecMulVec x (star x) - vecMulVec y (star y)) +
      Complex.I • (vecMulVec (x + Complex.I • y) (star (x + Complex.I • y)) - vecMulVec x (star x) -
        vecMulVec y (star y))) := by
  ext i j
  simp only [vecMulVec_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Pi.add_apply, Pi.smul_apply,
    Pi.star_apply, smul_eq_mul, star_add, star_mul', Complex.star_def, Complex.conj_I]
  linear_combination (1 / 2 * (x i * (starRingEnd ℂ) (y j) - y i * (starRingEnd ℂ) (x j) +
    Complex.I * y i * (starRingEnd ℂ) (y j))) * Complex.I_mul_I

theorem conj_eq (hH : Hm.IsHermitian) (hd : Hm.det ≠ 0) (hP : P.det ≠ 0) (ha : a.det ≠ 0) (hS : S.Countable)
    (h : ∀ u ∈ Formalism.QuantumDeterminants.UH Hm, ∃ δ : Mt n, (∀ i j, δ i j ∈ S) ∧ δ * (P * (a⁻¹ * u * a)) = P * u) (m : Mt n) :
    a⁻¹ * m * a = m := by
  let L : Mt n →ₗ[ℂ] Mt n :=
    { toFun := fun W => a⁻¹ * (W * Hm) * a - W * Hm
      map_add' := fun W W' => by simp only [Matrix.add_mul, Matrix.mul_add]; abel
      map_smul' := fun c W => by simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, RingHom.id_apply] }
  have h1 : ∀ v : Fin n → ℂ, L (vecMulVec v (star v)) = 0 := fun v => by
    obtain ⟨q, hq⟩ : ∃ q : ℝ, star v ⬝ᵥ Hm *ᵥ v = q :=
      ⟨_, (Complex.conj_eq_iff_re.1 (Complex.conj_eq_iff_im.2 (hH.im_star_dotProduct_mulVec_self v))).symm⟩
    have hden : ∀ s : ℝ, (1 - Complex.I * s * q : ℂ) ≠ 0 := fun s h0 => by
      have := congrArg Complex.re h0
      simp at this
    have hden' : ∀ s : ℝ, (1 + Complex.I * s * q : ℂ) ≠ 0 := fun s h0 => by
      have := congrArg Complex.re h0
      simp at this
    let z : ℝ → ℂ := fun s => 2 * Complex.I * s / (1 - Complex.I * s * q)
    have hz : Continuous z := Continuous.div (by fun_prop) (by fun_prop) hden
    have := conj_eq_of_path hd hP ha hS h (fun s => 1 + z s • (vecMulVec v (star v) * Hm))
      (continuous_const.add (hz.smul continuous_const)) (by simp [z]) fun s => refl_mem hH v _ (by
        have e : star (z s) = -(2 * Complex.I * s) / (1 + Complex.I * s * q) := by simp [z]
        rw [hq, e]
        have := hden s
        have := hden' s
        simp only [z]
        field_simp
        ring)
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ ha.isUnit, add_right_inj,
      Matrix.mul_smul, Matrix.smul_mul] at this
    have hz1 : z 1 ≠ 0 := div_ne_zero (by simp) (hden 1)
    exact sub_eq_zero.2 (smul_right_injective _ hz1 this)
  have h2 : ∀ x y : Fin n → ℂ, L (vecMulVec x (star y)) = 0 := fun x y => by
    rw [polar]
    simp only [map_smul, map_add, map_sub, h1, sub_zero, smul_zero, add_zero]
  have h3 : ∀ W, L W = 0 := fun W => by
    rw [Matrix.matrix_eq_sum_single W]
    simp only [map_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have : Matrix.single i j (W i j) = vecMulVec (Pi.single i (W i j)) (star (Pi.single j (1 : ℂ))) := by
      ext k l
      by_cases h1 : i = k <;> by_cases h2 : j = l <;> simp [vecMulVec_apply, h1, h2, eq_comm]
    rw [this, h2]
  have h4 : a⁻¹ * (m * Hm⁻¹ * Hm) * a - m * Hm⁻¹ * Hm = 0 := h3 (m * Hm⁻¹)
  rwa [Matrix.nonsing_inv_mul_cancel_right _ _ hd.isUnit, sub_eq_zero] at h4

end Central

variable {D : D7}

theorem nNeg_eq {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (ρ : D.what₂.Tau) {p : ℕ} (hp : p ≤ V.rank)
    (h : ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) (x0Mat M ρ) =
      Matrix.diagonal fun a : Fin V.rank => ((sgn p (a : ℕ) : ℝ) : ℂ)) : p = nNeg (M.ε ρ) := by
  have h1 : (x0Mat M ρ)ᴴ * gramAt D V ρ * x0Mat M ρ = _ :=
    ModelRep.orth_sub (M.fr_unit ρ) (M.fr_gram ρ) (arr (nNeg (M.ε ρ)))
  rw [FdDom.gram_neg_transpose] at h
  have h2 : ∀ a : Fin V.rank, M.ε ρ (arr (nNeg (M.ε ρ)) a) = false ↔ (a : ℕ) < p := fun a => by
    have e1 := congrFun (congrFun h a) a
    have e2 := congrFun (congrFun h1 a) a
    rw [transpose_apply, Matrix.neg_apply, diagonal_apply_eq] at e1
    have e3 : -((Formalism.REAL.Jm (M.ε ρ)).submatrix (arr (nNeg (M.ε ρ))) (arr (nNeg (M.ε ρ))) a a) = _ :=
      (congrArg Neg.neg e2).symm.trans e1
    simp only [Formalism.REAL.Jm, submatrix_apply, diagonal_apply_eq, sgn] at e3
    split_ifs at e3 with c1 c2 c2
    · norm_num at e3
    · simp [c1, c2]
    · simp [c1, c2]
    · norm_num at e3
  have h3 : (Finset.univ.filter fun a : Fin V.rank => (a : ℕ) < p).card = nNeg (M.ε ρ) := by
    refine Finset.card_equiv (ModelRep.arrEquiv (nNeg_le (M.ε ρ))) fun a => ?_
    simp only [negS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (h2 a).symm
  rw [← h3, Fin.card_filter_val_lt, min_eq_right hp]

theorem archM_mul (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D V) :
    archM V θ (g * g') = archM V θ g * archM V θ g' := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem archM_det (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    (archM V θ g).det ≠ 0 := by
  have h := archM_mul V θ g g⁻¹
  rw [mul_inv_cancel, GlobalTheory.Member.Arch.archM_of_one V θ (map_one _)] at h
  have := congrArg Matrix.det h
  rw [det_one, det_mul] at this
  exact left_ne_zero_of_mul_eq_one this.symm

theorem baseFr_of {V W : HSp D} (hV : V = W) {S : D.what₂.Tau → SPar} (M : DSModel W S) {θ : InfFam D} (hθ : IsInfFam θ)
    {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r) {Comp : Type} {X : Comp → Data D.host.E r}
    {dict : GA D V → Σ k, Frame (X k).Ψ r} {Kf : Subgroup (GA D V)}
    {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hth : ∀ k τ, IsInfEmb τ.1 (th k τ))
    (hd : DictIsUnif V dict Kf th hr) {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (hx : IsModelBaseFrameFamily M hr' x₀)
    (hΨ : ∀ k ρ, tauE D ρ ∈ (X k).Ψ) (hW : ∀ k, ModelW V hr (X k)) (ho : ∀ k, IsOrthogonalFrame (X k) x₀)
    (hf : ∀ h, ∃ γ ∈ GQ V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (γ * h)) * x₀ τ.1) :
    BaseFr M θ hr' (castDict hV dict) := by
  subst hV
  subst hr
  show BaseFr M θ rfl dict
  have hx' : ∀ ρ, x₀ (tauE D ρ) = x0Mat M ρ := hx
  have hΨ' : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (X k).Ψ ↔ ∃ ρ, τ = tauE D ρ := fun k τ => by
    refine ⟨fun h => ?_, fun ⟨ρ, h⟩ => h ▸ hΨ k ρ⟩
    have h1 := ((X k).cmType τ).1 h
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.SmoothForms.RealPts.tauE_cm D τ).2 (fun ⟨ρ, hρ⟩ => h1 (hρ ▸ hΨ k ρ))
    exact ⟨ρ, hρ.symm⟩
  have hθ' : ∀ k ρ (τ : (X k).Ψ), τ.1 = tauE D ρ → th k τ = θ ρ := fun k ρ τ e =>
    GlobalTheory.SmoothForms.RealPts.infEmb_unique _ _ _ (hth k τ) (e ▸ hθ ρ)
  have hf' : ∀ g c x, dict g = ⟨c, x⟩ → ∃ γ ∈ GQ V, ∀ ρ (τ : (X c).Ψ), τ.1 = tauE D ρ →
      mat x τ = archM V (θ ρ) (γ * g) * x0Mat M ρ := by
    intro g c x hg
    have := hf g
    rw [hg] at this
    obtain ⟨γ, hγ, h⟩ := this
    refine ⟨γ, hγ, fun ρ τ e => ?_⟩
    rw [h τ, hθ' c ρ τ e, e, hx']
    rfl
  refine ⟨hΨ', fun k ρ => nNeg_eq M ρ (X k).p0_le ?_, fun h => ?_⟩
  · have h1 := ho k _ (hΨ k ρ)
    have hGm : (X k).Gm = -V.gramᵀ := (hW k).1
    rwa [hGm, hx'] at h1
  obtain ⟨γ, hγ, hfr⟩ := hf' h _ _ rfl
  refine ⟨γ, hγ, hfr, ?_⟩
  obtain ⟨-, -, ⟨x0, h0, h3⟩, -⟩ := hd
  obtain ⟨hdom, g, hg⟩ := h0 (dict h).1
  obtain ⟨β, -, hβ⟩ := hf' g _ _ hg
  obtain ⟨L, hL, -, -, -, -, -, -, -, hH⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have calc1 : ∀ u ρ (τ : (X (dict h).1).Ψ), τ.1 = tauE D ρ →
      mat (rmul (dict h).2 (archMat V th rfl x0 u (dict h).1)) τ = archM V (θ ρ) (γ * h) *
        ((archM V (θ ρ) (β * g))⁻¹ * archM V (θ ρ) u * archM V (θ ρ) (β * g)) * x0Mat M ρ ∧ (x0Mat M ρ).det ≠ 0 := by
    intro u ρ τ e
    have hy := (hdom τ).1
    rw [hβ ρ τ e, det_mul] at hy
    have hy' := right_ne_zero_of_mul hy
    refine ⟨?_, hy'⟩
    show (mat (dict h).2 τ * ((mat (x0 (dict h).1) τ)⁻¹ * archM V (th (dict h).1 τ) u * mat (x0 (dict h).1) τ) :
      Mt V.rank) = _
    rw [hfr ρ τ e, hβ ρ τ e, hθ' _ ρ τ e, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hy'.isUnit]
  have central : ∀ ρ m, (archM V (θ ρ) (β * g))⁻¹ * m * archM V (θ ρ) (β * g) = m := by
    classical
    intro ρ
    have : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
    refine conj_eq (S := Set.range (tauE D ρ)) (hH ρ).1 (hH ρ).2 (archM_det V (θ ρ) (γ * h)) (archM_det V _ _)
      (Set.countable_range _) fun u hu => ?_
    have hu' : (Pi.mulSingle ρ u : D.what₂.Tau → Mt V.rank) ∈ UG (gramAt D V) := fun ρ' => by
      by_cases c : ρ' = ρ
      · subst c
        rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne c]
        show (1 : Mt V.rank)ᴴ * _ * 1 = _
        simp
    obtain ⟨h1, h2⟩ := hL _ hu'
    have h2' := h2 ρ
    rw [Pi.mulSingle_eq_same] at h2'
    obtain ⟨γ', -, e1⟩ := h3 h _ h1
    obtain ⟨δ, hδ, e2⟩ := hf' _ _ _ e1
    let τ : (X (dict h).1).Ψ := ⟨tauE D ρ, hΨ _ ρ⟩
    obtain ⟨c1, c2⟩ := calc1 (L (Pi.mulSingle ρ u)) ρ τ rfl
    have e3 : γ'.1.map (tauE D ρ) *
        mat (rmul (dict h).2 (archMat V th rfl x0 (L (Pi.mulSingle ρ u)) (dict h).1)) τ = _ := e2 ρ τ rfl
    obtain ⟨r1, -, -, -, r5⟩ := GlobalTheory.Member.RatElt.rational_elements D V
    obtain ⟨ε, hε⟩ := (r1 _).1 (mul_mem hγ (inv_mem hδ))
    have e4 := (r5 _ _ hε).2 _ _ (hθ ρ)
    refine ⟨(ε.1 * γ'.1).map (tauE D ρ), fun i j => ⟨_, rfl⟩, ?_⟩
    rw [c1, h2', ← Matrix.mul_assoc] at e3
    have e5 := congrArg (· * (x0Mat M ρ)⁻¹) e3
    simp only [Matrix.mul_nonsing_inv_cancel_right _ _ c2.isUnit] at e5
    rw [Matrix.map_mul, Matrix.mul_assoc, e5, ← e4, ← archM_mul, ← h2', ← archM_mul, h2']
    congr 1
    group
  intro u hu
  obtain ⟨γ', hγ', e1⟩ := h3 h u hu
  refine ⟨γ', hγ', _, e1, fun ρ τ e => ?_⟩
  rw [(calc1 u ρ τ e).1, central, ← archM_mul]
  rfl

theorem baseFrT_of_tieIn : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → BaseFrT T.toCore R := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hR ht i σ hσ hV
  have hj : InR D ((i : ℕ) + 1) := inR i
  obtain ⟨th, hr, hth, hd⟩ := ht.laws.dictU _ hj _ hσ
  obtain ⟨hr', g, e, F, ik, φ, th', -, -, hth', -, hL⟩ := ht.laws.adPin _ hj _ hσ
  obtain ⟨hr'', hW⟩ := ht.laws.modelW _ hj _ hσ
  have e' : th' = th := funext fun k => funext fun τ => GlobalTheory.SmoothForms.RealPts.infEmb_unique _ _ _ (hth' k τ) (hth k τ)
  subst e'
  exact baseFr_of hV _ hR.inf hr _ hth hd (ht.x0 i σ hσ)
    (fun k ρ => (((ht.laws.unf _ hj _ hσ).2.1 k).2 _).2 (ht.laws.pins.1.2.2.2 ρ)) hW (ht.laws.familyUniformisationBasePointOrthogonal _ hj _ hσ)
    fun h => (hL h).imp fun γ hγ => ⟨hγ.1, hγ.2.2.2⟩

end GlobalTheory.HolDict.BaseFrame
