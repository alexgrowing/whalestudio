import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.EvFinIdemSelf

noncomputable section

namespace GlobalTheory.ThK.Dbl.Bad

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem cartan_pm {M θ : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (hs : HasSig M r s) (h0 : min r s = 0)
    (hM : ∀ i j, star (M j i) = M i j) (h : IsCartan M θ) : θ = 1 ∨ θ = -1 := by
  by_contra hn
  push Not at hn
  have ex : ∀ A : Matrix (Fin n) (Fin n) ℂ, A ≠ 0 → ∃ u, A *ᵥ u ≠ 0 := fun A hA => by
    by_contra c
    push Not at c
    exact hA (Matrix.ext_iff_mulVec.2 fun u => by rw [c, Matrix.zero_mulVec])
  obtain ⟨u, hu⟩ := ex _ (fun e => hn.2 (eq_neg_of_add_eq_zero_left e) : θ + 1 ≠ 0)
  obtain ⟨u', hu'⟩ := ex _ (sub_ne_zero.2 hn.1)
  set x := (θ + 1) *ᵥ u
  set y := (θ - 1) *ᵥ u'
  have hx : θ *ᵥ x = x := by rw [Matrix.mulVec_mulVec, mul_add, h.1, mul_one, add_comm]
  have hy : θ *ᵥ y = -y := by rw [Matrix.mulVec_mulVec, mul_sub, h.1, mul_one, ← Matrix.neg_mulVec, neg_sub]
  have iso : ∀ a b : Fin n → ℂ, (θ *ᵥ a) ⬝ᵥ M *ᵥ star (θ *ᵥ b) = a ⬝ᵥ M *ᵥ star b := fun a b => by
    have : star (θ *ᵥ b) = θ.map star *ᵥ star b := funext fun i => by simp [Matrix.mulVec, dotProduct]
    conv_rhs => rw [← h.2.1, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [this, Matrix.mulVec_mulVec]
  have re : ∀ a : Fin n → ℂ, a ⬝ᵥ M *ᵥ star a = ((a ⬝ᵥ M *ᵥ star a).re : ℂ) := fun a => by
    refine (Complex.conj_eq_iff_re.1 ?_).symm
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum, map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [← hM i j, Complex.star_def]; ring
  have p1 := h.2.2 x hu
  have p2 := h.2.2 y hu'
  have c1 := iso x y
  have c2 := iso y x
  rw [hx] at p1
  rw [hy, neg_dotProduct, Complex.neg_re] at p2
  rw [hx, hy] at c1 c2
  rw [star_neg, Matrix.mulVec_neg, dotProduct_neg, neg_eq_self] at c1
  rw [neg_dotProduct, neg_eq_self] at c2
  set a := (x ⬝ᵥ M *ᵥ star x).re
  set b := (y ⬝ᵥ M *ᵥ star y).re
  have z := HasSig.aniso hs h0 (x := (Real.sqrt (-b) : ℂ) • x + (Real.sqrt a : ℂ) • y) (by
    simp only [star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, c1, c2, smul_eq_mul, Complex.star_def, Complex.conj_ofReal, mul_zero, add_zero, zero_add]
    rw [re x, re y, ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul (Real.sqrt a), Real.mul_self_sqrt p1.le,
      Real.mul_self_sqrt p2.le]
    change ((-b : ℝ) : ℂ) * a + a * b = 0
    push_cast
    ring)
  have z' := congrArg (θ *ᵥ ·) z
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hx, hy, Matrix.mulVec_zero] at z'
  have : (2 * Real.sqrt a : ℂ) • y = 0 := by linear_combination (norm := module) z - z'
  exact hu' ((smul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 p1).ne')))

variable {Y : Spc F E n} {B : Base F E} {v : Pl F} {r s : ℕ}

theorem theta_pm (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) : Y.θ w = 1 ∨ Y.θ w = -1 :=
  cartan_pm (h.sig w) h0 (fun i j => (hB.cm.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))) (h.cartan w)

theorem commute_theta (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) (A) : Commute A (Y.θ w) := by
  rcases theta_pm hB h h0 w with e | e <;> rw [e]
  exacts [Commute.one_right _, Commute.neg_one_right _]

omit [NumberField E] in
theorem real_latHat {z} (hz : z ∈ latHat Y) : realAd F 1 • z = 0 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, h0, -, x, -, rfl⟩ := hz
    rw [smul_smul, mul_comm, ← smul_smul, at_real _ b h0]
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | neg x _ hx => rw [smul_neg, hx, neg_zero]

theorem idem_int (v u : Pl F) : evFin F u (idem F v) ∈ u.adicCompletionIntegers F := by
  rcases eq_or_ne u v with rfl | h
  · rw [evFin_idem_self]; exact one_mem _
  · rw [evFin_idem_ne h]; exact zero_mem _

theorem mulVec_mem (hL : Y.L.IsLattice E) {A : Matrix (Fin n) (Fin n) (AE F E)}
    (h : ∀ v, ∀ z ∈ latHat Y, At (evFin F v) z → A *ᵥ z ∈ latHat Y) {z} (hz : z ∈ latHat Y) : A *ᵥ z ∈ latHat Y := by
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have t := (tendsto_aS (F := F)).smul_const (A *ᵥ z)
  rw [one_smul] at t
  refine (Euler.isClosed_latHat hL).mem_of_tendsto t (.of_forall fun S => ?_)
  rw [aS, add_smul, ← Matrix.mulVec_smul, real_latHat hz, Matrix.mulVec_zero, zero_add, Finset.sum_smul]
  exact sum_mem fun v _ => by
    rw [← Matrix.mulVec_smul]; exact h v _ (latHat_smul (idem_int v) hz) (at_idem v z)

theorem stab_iff (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (UA σ Y.J)} (hK : IsStab B K)
    {g : UA σ Y.J} : g ∈ K ↔ ∀ v, IntAt v g :=
  (hK g).trans ⟨fun a _ z hz _ => a.2 z hz, fun a => ⟨fun w => commute_theta hB h h0 w _, fun _ hz =>
    ⟨mulVec_mem h.lat (fun v z h1 h2 => (a v z h1 h2).1) hz, mulVec_mem h.lat (fun v z h1 h2 => (a v z h1 h2).2) hz⟩⟩⟩

theorem emb_mem (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K)
    {e : UA σ Y.J × UA σ Y.J →* G2 σ Y} (he : ∀ g g', IsEmb g g' (e (g, g'))) {g : UA σ Y.J} (hg : ∀ v, IntAt v g) :
    e (g, 1) ∈ K := by
  refine (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k hk => ?_⟩
  · rw [he g 1, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
    simp only [Commute, SemiconjBy, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      (commute_theta hB h h0 w _).eq, (commute_theta hB h h0 w _).neg_right.eq]
  · obtain ⟨g', e1, hg'⟩ : ∃ g', k = e (g', 1) ∧ mat g' *ᵥ z ∈ latHat Y := by
      rcases hk with rfl | rfl
      · exact ⟨g, rfl, mulVec_mem h.lat (fun v z h1 h2 => (hg v z h1 h2).1) hz⟩
      · exact ⟨g⁻¹, by rw [← map_inv, Prod.inv_mk, inv_one], mulVec_mem h.lat (fun v z h1 h2 => (hg v z h1 h2).2) hz⟩
    rw [e1, he g' 1, Matrix.fromBlocks_mulVec, show mat (1 : UA σ Y.J) = 1 from rfl]
    simpa using ⟨hg', hz'⟩

theorem int_nhds (hL : Y.L.IsLattice E) : {g : UA σ Y.J | ∀ v, IntAt v g} ∈ 𝓝 (1 : UA σ Y.J) := by
  classical
  obtain ⟨m, x, hs, hx⟩ := Euler.lat_gen hL
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let U : Set (Fin m → AF F) := {a | ∀ i v, evFin F v (a i) ∈ v.adicCompletionIntegers F}
  have hO : IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hU : IsOpen U := by
    rw [show U = ⋂ i, {a | ∀ v, evFin F v (a i) ∈ v.adicCompletionIntegers F} from Set.ext fun _ => by
      rw [Set.mem_iInter]; rfl]
    exact isOpen_iInter_of_finite fun i => hO.preimage (continuous_snd.comp (continuous_apply i))
  have hV := IsModuleTopology.isOpenMap_of_surjective (Euler.gen_surj hL hs) U hU
  set V := (Fintype.linearCombination (AF F) fun i => incV F (x i).1) '' U with eV
  have key : ∀ A : Matrix (Fin n) (Fin n) (AE F E), (∀ i, A *ᵥ incV F (x i).1 ∈ V) → ∀ v, ∀ z ∈ latHat Y, At (evFin F v) z →
      A *ᵥ z ∈ latHat Y := fun A hA v z hz h => by
    obtain ⟨a, ha, rfl⟩ := (hx z).1 hz
    rw [← Euler.at_iff.1 h, Finset.smul_sum, Matrix.mulVec_sum]
    refine sum_mem fun i _ => ?_
    obtain ⟨b, hb, e⟩ := hA i
    rw [smul_smul, Matrix.mulVec_smul, ← e, Fintype.linearCombination_apply, Finset.smul_sum]
    refine sum_mem fun j _ => ?_
    rw [smul_smul, mul_assoc]
    exact Euler.gen_mem (Euler.idem_mem (by rw [map_mul]; exact mul_mem ((ha i).2 v) (hb j v))) (x j).2
  have o : IsOpen {g : UA σ Y.J | ∀ i, mat g *ᵥ incV F (x i).1 ∈ V} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => hV.preimage (Euler.cont_mat.matrix_mulVec continuous_const)
  have o1 : ∀ i, mat (1 : UA σ Y.J) *ᵥ incV F (x i).1 ∈ V := fun i => by
    rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.one_mulVec]
    refine ⟨Pi.single i 1, fun j v => ?_, by rw [Fintype.linearCombination_apply_single, one_smul]⟩
    rw [Pi.single_apply, apply_ite (evFin F v), map_one, map_zero]
    split_ifs
    exacts [one_mem _, zero_mem _]
  exact mem_of_superset ((o.inter (o.preimage continuous_inv)).mem_nhds ⟨o1, by rw [Set.mem_preimage, inv_one]; exact o1⟩)
    fun g hg v z hz h => ⟨key _ hg.1 v z hz h, key _ hg.2 v z hz h⟩

theorem idem_smul {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} (h : At (evFin F v) z) : idem F v • z = z :=
  Euler.at_iff.1 h

theorem idem_off {z : AE F E} (h : compFin F E v z = 0) : idem F v • z = 0 := by
  let j : Fv F v ⊗[F] E →ₗ[F] AE F E := TensorProduct.map (LinearMap.inr F (Ainf F) (Af F) ∘ₗ singleFin v) LinearMap.id
  have : ∀ z, idem F v • z = j (compFin F E v z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]
    | tmul a x =>
      refine congrArg (· ⊗ₜ[F] x) (af_ext' ((evI_mul _ _).trans (by rw [evI_idem, zero_mul]; exact evI_zero.symm)) fun u => ?_)
      rcases eq_or_ne u v with rfl | h
      · rw [smul_eq_mul, map_mul, evFin_idem_self, one_mul]; exact (evalV_singleFin_self _ _).symm
      · rw [smul_eq_mul, map_mul, evFin_idem_ne h, zero_mul]; exact (evalV_singleFin_ne h _).symm
  rw [this, h, map_zero]

theorem comm_off {e : UA σ Y.J × UA σ Y.J →* G2 σ Y} (he : ∀ g g', IsEmb g g' (e (g, g'))) {g : UA σ Y.J} (hg : OffAt v g)
    {k : G2 σ Y} (hk : At (evFin F v) (mat2 k - 1)) : k * e (g, 1) = e (g, 1) * k := by
  have h1 : idem F v • (mat2 (e (g, 1)) - 1) = 0 := by
    have : idem F v • (mat g - 1) = 0 := Matrix.ext fun i j => idem_off (by
      have := congrFun₂ hg i j
      rw [Matrix.map_apply] at this
      simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
    rw [he g 1, show mat (1 : UA σ Y.J) = 1 from rfl, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_add, Matrix.fromBlocks_smul, ← sub_eq_add_neg, this]
    simp
  have a1 : (mat2 k - 1) * (mat2 (e (g, 1)) - 1) = 0 := by rw [← idem_smul hk, smul_mul_assoc, ← mul_smul_comm, h1, mul_zero]
  have a2 : (mat2 (e (g, 1)) - 1) * (mat2 k - 1) = 0 := by rw [← idem_smul hk, mul_smul_comm, ← smul_mul_assoc, h1, zero_mul]
  refine Subtype.ext (Units.ext (show mat2 k * mat2 (e (g, 1)) = mat2 (e (g, 1)) * mat2 k from ?_))
  linear_combination (norm := noncomm_ring) a1 - a2

theorem loc_iwa {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {a : G2 σ Y → ℝ} (ha : IsHgt K a) {x : G2 σ Y}
    (hx : At (evFin F v) (mat2 x - 1)) : ∃ p t k, IsPar p t ∧ k ∈ K ∧ At (evFin F v) (mat2 k - 1) ∧ x = p * k := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
  have h1 := idem_mul_self v
  let π : G2 σ Y →* G2 σ Y := MonoidHom.mk' (fun g => ⟨⟨Euler.cut (idem F v) (mat2 g), Euler.cut (idem F v) (mat2 g⁻¹),
    by rw [Euler.cut_mul h1, show mat2 g * mat2 g⁻¹ = 1 from g.1.mul_inv]; exact Euler.cut_one,
    by rw [Euler.cut_mul h1, show mat2 g⁻¹ * mat2 g = 1 from g.1.inv_mul]; exact Euler.cut_one⟩,
    Euler.cut_form h1 _ g.2⟩) fun g h => Subtype.ext (Units.ext (Euler.cut_mul h1 _ _).symm)
  have hπ : ∀ g, mat2 (π g) = (1 - idem F v) • 1 + idem F v • mat2 g := fun _ => rfl
  have h2 : ∀ g, mat2 (π g) - 1 = idem F v • (mat2 g - 1) := fun _ => Euler.cut_sub _
  refine ⟨π p, ⟨Euler.cut (idem F v) t.1, Euler.cut (idem F v) (t⁻¹).1,
    by rw [Euler.cut_mul h1, t.mul_inv]; exact Euler.cut_one, by rw [Euler.cut_mul h1, t.inv_mul]; exact Euler.cut_one⟩, π k, ?_,
    (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k' hk' => ?_⟩, by rw [h2]; exact at_idem v _, ?_⟩
  · rw [isPar_iff] at hp ⊢
    change mat2 (π p) * _ = _ * Euler.cut (idem F v) t.1
    rw [hπ, Euler.cut, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, hp,
      Matrix.one_mul, Matrix.mul_one]
  · have : (mat2 (π k)).map (piInf (B.emb w)) = 1 := by
      rw [eq_add_of_sub_eq (h2 k), Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
      exact add_eq_right.2 (Matrix.ext fun i j => piInf_idem _ v _)
    rw [this]; exact Commute.one_left _
  · obtain ⟨k₁, rfl, h3⟩ : ∃ k₁, k' = π k₁ ∧ k₁ ∈ ({k, k⁻¹} : Set (G2 σ Y)) := by
      rcases hk' with rfl | rfl
      exacts [⟨k, rfl, .inl rfl⟩, ⟨k⁻¹, (map_inv π k).symm, .inr rfl⟩]
    obtain ⟨b1, b2⟩ := ((hK k).1 hk).2 z z' hz hz' k₁ h3
    have i2 : ∀ u, evFin F u (1 - idem F v) ∈ u.adicCompletionIntegers F := fun u => by
      rw [map_sub, map_one]; exact sub_mem (one_mem _) (idem_int v u)
    rw [hπ, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact ⟨add_mem (latHat_smul i2 hz) (latHat_smul (idem_int v) b1), add_mem (latHat_smul i2 hz') (latHat_smul (idem_int v) b2)⟩
  · rw [← map_mul]
    exact Subtype.ext (Units.ext (Euler.cut_eq.2 (idem_smul hx)).symm)

end GlobalTheory.ThK.Dbl.Bad

end
