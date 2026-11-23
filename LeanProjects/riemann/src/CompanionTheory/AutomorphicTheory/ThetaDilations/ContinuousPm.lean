import CompanionTheory.AutomorphicTheory.ThetaDilations.ParAlg
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  (R : Type) [CommRing R] [Algebra F R]

theorem exists_anti (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hss : ∀ x, σ (σ x) = x := GlobalTheory.GaussMean.OneVec.sigma_sigma h
  by_contra hne
  push Not at hne
  have := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have h2 : σ y = y := by
    by_contra h3
    exact hne (y - σ y) (sub_ne_zero.2 (Ne.symm h3)) (by rw [map_sub, hss, neg_sub])
  have := h.2.2.2 τ y
  rw [h2] at this
  simpa using this.symm

theorem norm_sigR (h : IsCMExt F E σ) (a : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.norm R a) = a * sigR R σ a := by
  have ht : a + sigR R σ a = algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) a) :=
    GlobalTheory.GaussMean.OneVec.add_sigR R h a
  let B := Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h.2.2.1)
  have key : algebraMap R (R ⊗[F] E) (Algebra.norm R a) =
      algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) a) * a - a * a := by
    apply Algebra.leftMulMatrix_injective B
    rw [map_sub, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, Algebra.norm_eq_matrix_det B,
      Algebra.trace_eq_matrix_trace B]
    generalize Algebra.leftMulMatrix B a = A
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.algebraMap_eq_diagonal, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply] <;> ring
  rw [key, ← ht]; ring

theorem cT_JR {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : cT (sigR R σ) (JR R J) = JR R J := by
  ext i j; simp [cT, JR, sigR, inclR, hJ.1]

theorem hform_conj {K : Type} [CommRing K] {M : ℕ} {s : K →+* K} {J : Matrix (Fin M) (Fin M) K} (hs : ∀ x, s (s x) = x)
    (hJ : cT s J = J) (x y : Fin M → K) : s (hform s J x y) = hform s J y x := by
  have : ∀ i j, s (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j
  simp only [hform, map_sum, map_mul, hs, this]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hform_add {K : Type} [CommRing K] {M : ℕ} (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (x y : Fin M → K) :
    hform s J (x + y) (x + y) = hform s J x x + hform s J x y + hform s J y x + hform s J y y := by
  have e : (s : K → K) ∘ (x + y) = s ∘ x + s ∘ y := funext fun _ => map_add s _ _
  simp only [hform_eq, e, Matrix.add_vecMul, add_dotProduct, dotProduct_add]; ring

theorem hform_U {K : Type} [CommRing K] {M : ℕ} {s : K →+* K} {J U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J)
    (x : Fin M → K) : hform s J (U *ᵥ x) (U *ᵥ x) = hform s J x x := by
  have e : (s : K → K) ∘ (U *ᵥ x) = (s ∘ x) ᵥ* cT s U := by
    funext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, mul_comm]
  rw [hform_eq, hform_eq, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hU]

theorem hyp_inv {K : Type} [CommRing K] {M : ℕ} {J Ji : Matrix (Fin M) (Fin M) K} (h : Ji * J = 1) :
    hypJ Ji * hypJ J = 1 := by
  rw [← pm_one]
  simp [hypJ_eq, blk_mul, pm, h]

theorem continuous_pm {X K : Type} [TopologicalSpace X] [CommRing K] [TopologicalSpace K] {M : ℕ} {a b d : X → K}
    {r w : X → Fin M → K} {U : X → Matrix (Fin M) (Fin M) K} (ha : Continuous a) (hb : Continuous b)
    (hr : Continuous r) (hd : Continuous d) (hw : Continuous w) (hU : Continuous U) :
    Continuous fun x => pm (a x) (b x) (r x) (d x) (w x) (U x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  exacts [ha, hb, (continuous_apply j).comp hr, continuous_const, hd, continuous_const, continuous_const,
    (continuous_apply i).comp hw, hU.matrix_elem i j]

set_option maxHeartbeats 1600000 in
theorem par : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ (nn : (Fin 1 → Fin M → AF F ⊗[F] E) × AF F → HA (AF F) σ (hypJ J)) (ι : HA (AF F) σ J →* HA (AF F) σ (hypJ J)) (mm : (AF F ⊗[F] E)ˣ →* HA (AF F) σ (hypJ J)) (c : (Fin 1 → Fin M → AF F ⊗[F] E) → (Fin 1 → Fin M → AF F ⊗[F] E) → AF F), IsClosedEmbedding (fun z : ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) × HA (AF F) σ J × (AF F ⊗[F] E)ˣ => nn z.1 * ι z.2.1 * mm z.2.2) ∧ Continuous nn ∧ Continuous ι ∧ Continuous mm ∧ (Continuous fun p : (Fin 1 → Fin M → AF F ⊗[F] E) × (Fin 1 → Fin M → AF F ⊗[F] E) => c p.1 p.2) ∧ nn (0, 0) = 1 ∧ (∀ w s w' s', nn (w, s) * nn (w', s') = nn (w + w', s + s' + c w w')) ∧ (∀ w, c 0 w = 0) ∧ (∀ u w s, ι u * nn (w, s) = nn (actW (AF F) σ J u w, s) * ι u) ∧ (∀ (a : (AF F ⊗[F] E)ˣ) w s, mm a * nn (w, s) = nn (sigR (AF F) σ (a : AF F ⊗[F] E) • w, Algebra.norm (AF F) (a : AF F ⊗[F] E) * s) * mm a) ∧ (∀ u a, mm a * ι u = ι u * mm a) ∧ (∀ p u (a : (AF F ⊗[F] E)ˣ), actW (AF F) σ _ (nn p * ι u * mm a) (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ (∀ (h : HA (AF F) σ (hypJ J)) (a : (AF F ⊗[F] E)ˣ), actW (AF F) σ _ h (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1) → ∃ p u, h = nn p * ι u * mm a) ∧ (∀ (w : Fin 1 → Fin M → E) (s : F), HA.mat (AF F) σ (hypJ J) (nn (ratTup (AF F) w, algebraMap F (AF F) s)) ∈ HFin (AF F) σ (hypJ J)) ∧ (∀ u, HA.mat (AF F) σ J u ∈ HFin (AF F) σ J → HA.mat (AF F) σ (hypJ J) (ι u) ∈ HFin (AF F) σ (hypJ J)) ∧ ∀ (l : Eˣ) (a : (AF F ⊗[F] E)ˣ), (a : AF F ⊗[F] E) = inclR (AF F) (l : E) → HA.mat (AF F) σ (hypJ J) (mm a) ∈ HFin (AF F) σ (hypJ J) := by
  intro F E _ _ _ _ _ σ hcm M J hJ
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, -, -, _, hsc, htc, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  obtain ⟨δ, hδ0, hδ⟩ := exists_anti hcm
  set s := sigR (AF F) σ with hsdef
  have hs : ∀ x, s (s x) = x := GlobalTheory.GaussMean.OneVec.sigR_sigR (AF F) hcm
  have hsa : ∀ t : AF F, s (algebraMap _ _ t) = algebraMap _ _ t := GlobalTheory.GaussMean.OneVec.sigR_algebraMap (AF F)
  have hsi : ∀ x : E, s (inclR (AF F) x) = inclR (AF F) (σ x) := fun x => by simp [hsdef, sigR, inclR]
  have hJc := cT_JR (AF F) hJ
  have hJi : JR (F := F) (AF F) J⁻¹ * JR (F := F) (AF F) J = 1 := by
    rw [JR, JR, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ.2), Matrix.map_one _ (map_zero _) (map_one _)]
  have hH : JR (F := F) (AF F) (hypJ J) = hypJ (JR (F := F) (AF F) J) := hypJ_map _ J
  have hHi : hypJ (JR (F := F) (AF F) J⁻¹) * JR (F := F) (AF F) (hypJ J) = 1 := by rw [hH]; exact hyp_inv hJi
  set κ : AF F ⊗[F] E := inclR (AF F) (1 / 2 : E) with hκ
  set dl : AF F ⊗[F] E := inclR (AF F) δ with hdl
  set di : AF F ⊗[F] E := inclR (AF F) δ⁻¹ with hdi
  have hκ2 : 2 * κ = 1 := by rw [hκ, ← map_ofNat (inclR (F := F) (E := E) (AF F)) 2, ← map_mul]; norm_num
  have hκs : s κ = κ := by rw [hκ, hsi, map_div₀, map_one, map_ofNat]
  have hdls : s dl = -dl := by rw [hdl, hsi, hδ, map_neg]
  have hdis : s di = -di := by rw [hdi, hsi, map_inv₀, hδ, inv_neg, map_neg]
  have hdd : di * dl = 1 := by rw [hdi, hdl, ← map_mul, inv_mul_cancel₀ hδ0, map_one]
  set sc : AF F ⊗[F] E → AF F := fun y => algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) _ (di * y) with hsc'
  have hscc : Continuous sc := continuous_const.mul (htc.comp (continuous_const.mul continuous_id))
  have sc1 : ∀ y, s y = -y → algebraMap _ _ (sc y) * dl = y := fun y hy => by
    have : algebraMap _ _ (sc y) = di * y :=
      GlobalTheory.GaussMean.OneVec.fixed_eq (AF F) hcm (show s (di * y) = di * y by rw [map_mul, hdis, hy, neg_mul_neg])
    rw [this, mul_right_comm, hdd, one_mul]
  have sc2 : ∀ t : AF F, sc (algebraMap _ _ t * dl) = t := fun t => by
    simp only [hsc', mul_left_comm di, hdd, mul_one]
    exact GlobalTheory.GaussMean.OneVec.half_trace (AF F) hcm t
  set hf := hform s (JR (AF F) J) with hhf
  have hfc : ∀ x y, s (hf x y) = hf y x := hform_conj hs hJc
  set z : (Fin 1 → Fin M → AF F ⊗[F] E) × AF F → AF F ⊗[F] E :=
    fun p => -(κ * hf (p.1 0) (p.1 0)) + algebraMap _ _ p.2 * dl with hz
  have hzu : ∀ p, z p + s (z p) + hf (p.1 0) (p.1 0) = 0 := fun p => by
    simp only [hz, map_add, map_neg, map_mul, hκs, hfc, hsa, hdls]
    linear_combination (-hf (p.1 0) (p.1 0)) * hκ2
  have ext : ∀ g g' : HA (AF F) σ (hypJ J), g.1.val = g'.1.val → g = g' := fun g g' h =>
    Subtype.ext (Units.ext h)
  let nn : (Fin 1 → Fin M → AF F ⊗[F] E) × AF F → HA (AF F) σ (hypJ J) := fun p =>
    mkU s hHi (nM s (JR (AF F) J) (p.1 0) (z p)) (by rw [hH]; exact nM_unit hs hJc (hzu p))
  let ι : HA (AF F) σ J →* HA (AF F) σ (hypJ J) :=
    { toFun := fun u => mkU s hHi (pm 1 0 0 1 0 u.1.val) (by rw [hH]; exact iM_unit u.2)
      map_one' := ext _ _ pm_one
      map_mul' := fun u v => ext _ _ (by
        show pm 1 0 0 1 0 (u.1.val * v.1.val) = pm 1 0 0 1 0 u.1.val * pm 1 0 0 1 0 v.1.val
        simp [pm_mul]) }
  let mm : (AF F ⊗[F] E)ˣ →* HA (AF F) σ (hypJ J) :=
    { toFun := fun a => mkU s hHi (pm (a : AF F ⊗[F] E) 0 0 (s (a⁻¹ : (AF F ⊗[F] E)ˣ)) 0 1) (by rw [hH]; exact mM_unit hs a)
      map_one' := ext _ _ (by
        show pm _ 0 0 (s _) 0 1 = 1
        rw [inv_one, Units.val_one, map_one, pm_one])
      map_mul' := fun a b => ext _ _ (by
        show pm _ 0 0 (s _) 0 1 = pm _ 0 0 (s _) 0 1 * pm _ 0 0 (s _) 0 1
        simp [pm_mul, mul_comm]) }
  have hval : ∀ p u a, (nn p * ι u * mm a).1.val = pm (a : AF F ⊗[F] E) (z p * s (a⁻¹ : (AF F ⊗[F] E)ˣ))
      (-(((s ∘ p.1 0) ᵥ* JR (AF F) J) ᵥ* u.1.val)) (s (a⁻¹ : (AF F ⊗[F] E)ˣ))
      (s (a⁻¹ : (AF F ⊗[F] E)ˣ) • p.1 0) u.1.val := fun p u a => nim _ _ _ _ _
  have I1 : IsInducing fun g : HA (AF F) σ J => g.1.val := continuous_UJ hsc hJi
  have I2 : IsInducing fun g : HA (AF F) σ (hypJ J) => g.1.val := continuous_UJ hsc hHi
  have hfC : Continuous fun p : (Fin M → AF F ⊗[F] E) × (Fin M → AF F ⊗[F] E) => hf p.1 p.2 := by
    simp only [hhf, hform]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hsc.comp ((continuous_apply i).comp continuous_fst)).mul continuous_const).mul
        ((continuous_apply j).comp continuous_snd)
  have halg : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) := by
    have := GlobalTheory.GaussMean.OneVec.isModTop (F := F) (E := E) (AF F)
    have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  have c0 : Continuous fun p : (Fin 1 → Fin M → AF F ⊗[F] E) × AF F => p.1 0 := (continuous_apply 0).comp continuous_fst
  have hzc : Continuous z :=
    (continuous_const.mul (hfC.comp (c0.prodMk c0))).neg.add ((halg.comp continuous_snd).mul continuous_const)
  have hvm : ∀ A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E), Continuous fun w : Fin M → AF F ⊗[F] E => (s ∘ w) ᵥ* A :=
    fun A => (continuous_pi fun i => hsc.comp (continuous_apply i)).matrix_vecMul continuous_const
  have cn : Continuous nn := I2.continuous_iff.2 (continuous_pm continuous_const hzc ((hvm _).comp c0).neg
    continuous_const c0 continuous_const)
  have ci : Continuous ι := I2.continuous_iff.2 (continuous_pm continuous_const continuous_const continuous_const
    continuous_const continuous_const I1.continuous)
  have cm : Continuous mm := I2.continuous_iff.2 (continuous_pm Units.continuous_val continuous_const continuous_const
    (hsc.comp Units.continuous_coe_inv) continuous_const continuous_const)
  have dec : ∀ h : HA (AF F) σ (hypJ J), (∀ i : Fin (M + 1), h.1.val i.succ 0 = 0) →
      ∃ p u a, h = nn p * ι u * mm a := fun h h0 => by
    obtain ⟨w, y, U, a, e1, e2, e3⟩ := par_dec hs (J := JR (AF F) J) (by rw [← hH]; exact h.2) h0
    have e4 : z (fun _ => w, sc (y + κ * hf w w)) = y := by
      simp only [hz]
      rw [sc1 _ (by rw [map_add, map_mul, hκs, hfc]; linear_combination e1 + hf w w * hκ2)]; ring
    exact ⟨(fun _ => w, sc (y + κ * hf w w)), mkU s hJi U e2, a, ext _ _ (e3.trans (congrArg (fun y => nM s (JR (AF F) J) w y *
      pm 1 0 0 1 0 U * pm (a : AF F ⊗[F] E) 0 0 (s (a⁻¹ : (AF F ⊗[F] E)ˣ)) 0 1) e4.symm))⟩
  have act : ∀ (h : HA (AF F) σ (hypJ J)) i, actW (AF F) σ _ h (eOne _ (M + 1)) 0 i = h.1.val i 0 :=
    fun h i => by simp [actW, actTup, eOne, HA.mat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have rat : ∀ (g : Matrix (Fin (M + 2)) (Fin (M + 2)) E) (h : HA (AF F) σ (hypJ J)),
      cT (σ : E →+* E) g * hypJ J * g = hypJ J → h.1.val = g.map (inclR (AF F)) →
      HA.mat (AF F) σ (hypJ J) h ∈ HFin (AF F) σ (hypJ J) := fun g h hg e =>
    ⟨_, (mkU (σ : E →+* E) (hyp_inv (Matrix.nonsing_inv_mul _ (Ne.isUnit hJ.2))) g hg).2, Units.ext e.symm⟩
  have hss : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := GlobalTheory.GaussMean.OneVec.sigma_sigma hcm
  have hJE : cT (σ : E →+* E) J = J := by ext i j; exact hJ.1 i j
  refine ⟨nn, ι, mm, fun w w' => sc (-(κ * (hf (w 0) (w' 0) - hf (w' 0) (w 0)))), ⟨⟨?_, ?_⟩, ?_⟩, cn, ci, cm, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let G : Matrix (Fin (M + 2)) (Fin (M + 2)) (AF F ⊗[F] E) → ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) ×
        Matrix (Fin M) (Fin M) (AF F ⊗[F] E) × (AF F ⊗[F] E) × (AF F ⊗[F] E)ᵐᵒᵖ := fun g =>
      ((fun _ i => s (g 0 0) * g i.succ.succ 1, sc (g 0 1 * s (g 0 0) +
        κ * hf (fun i => s (g 0 0) * g i.succ.succ 1) (fun i => s (g 0 0) * g i.succ.succ 1))),
        Matrix.of fun i j => g i.succ.succ j.succ.succ, g 0 0, MulOpposite.op (s (g 1 1)))
    have e0 : ∀ i j, Continuous fun g : Matrix (Fin (M + 2)) (Fin (M + 2)) (AF F ⊗[F] E) => g i j :=
      fun i j => continuous_id.matrix_elem i j
    have e1 : Continuous fun (g : Matrix (Fin (M + 2)) (Fin (M + 2)) (AF F ⊗[F] E)) (i : Fin M) =>
        s (g 0 0) * g i.succ.succ 1 := continuous_pi fun i => (hsc.comp (e0 _ _)).mul (e0 _ _)
    have hG : Continuous G := ((continuous_pi fun _ => e1).prodMk (hscc.comp (((e0 _ _).mul (hsc.comp (e0 _ _))).add
      (continuous_const.mul (hfC.comp (e1.prodMk e1)))))).prodMk ((continuous_matrix fun i j => e0 _ _).prodMk
      ((e0 _ _).prodMk (MulOpposite.continuous_op.comp (hsc.comp (e0 _ _)))))
    have := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).1
    refine IsInducing.of_comp (I2.continuous_iff.2 ?_) (hG.comp I2.continuous) ?_
    · exact ((I2.continuous.comp (cn.comp continuous_fst)).matrix_mul
        (I2.continuous.comp (ci.comp continuous_snd.fst))).matrix_mul (I2.continuous.comp (cm.comp continuous_snd.snd))
    · have h3 := IsInducing.id (X := (Fin 1 → Fin M → AF F ⊗[F] E) × AF F) |>.prodMap
        (I1.prodMap (Units.isInducing_embedProduct (M := AF F ⊗[F] E)))
      refine (congrArg IsInducing (funext fun ⟨p, u, a⟩ => ?_)).mp h3
      have h1 : s a * s (a⁻¹ : (AF F ⊗[F] E)ˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      have h2 : (fun i => s a * (s (a⁻¹ : (AF F ⊗[F] E)ˣ) • p.1 0) i) = p.1 0 := by
        funext i; rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, h1, one_mul]
      show _ = G (nn p * ι u * mm a).1.val
      rw [hval]
      refine Prod.ext (Prod.ext (funext fun i => ?_) ?_) (Prod.ext rfl (Prod.ext rfl (congrArg MulOpposite.op (hs _).symm)))
      · rw [Subsingleton.elim i 0]; exact h2.symm
      · show p.2 = sc (z p * s _ * s a + κ * hf (fun i => s a * (s _ • p.1 0) i) (fun i => s a * (s _ • p.1 0) i))
        rw [h2, mul_assoc, mul_comm (s _) (s a), h1, mul_one, hz]
        simp only [neg_add_cancel_comm, sc2]
  · rintro ⟨p, u, a⟩ ⟨p', u', a'⟩ h
    have h1 := (hval p u a).symm.trans ((congrArg (fun g : HA (AF F) σ (hypJ J) => g.1.val) h).trans
      (hval p' u' a'))
    obtain ⟨e1, e2, -, -, -, -, -, e3, e4⟩ := blk_inj h1
    obtain rfl : a = a' := Units.ext e1
    have hu : IsUnit (s (a⁻¹ : (AF F ⊗[F] E)ˣ)) := (Units.isUnit _).map s
    have e5 : p.1 0 = p'.1 0 := hu.smul_left_cancel.1 e3
    have e6 := hu.mul_right_cancel e2
    simp only [hz, e5, add_right_inj] at e6
    have e7 : p.2 = p'.2 := by rw [← sc2 p.2, e6, sc2]
    exact Prod.ext (Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; exact e5) e7)
      (Prod.ext (Subtype.ext (Units.ext e4)) rfl)
  · have e : Set.range (fun y : ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) × HA (AF F) σ J × (AF F ⊗[F] E)ˣ =>
        nn y.1 * ι y.2.1 * mm y.2.2) = ⋂ i : Fin (M + 1), {h | h.1.val i.succ 0 = 0} := by
      ext h
      rw [Set.mem_iInter]
      refine ⟨?_, fun h0 => ?_⟩
      · rintro ⟨⟨p, u, a⟩, rfl⟩ i
        show (nn p * ι u * mm a).1.val i.succ 0 = 0
        rw [hval]
        exact Fin.cases rfl (fun _ => rfl) i
      · obtain ⟨p, u, a, e⟩ := dec h h0
        exact ⟨(p, u, a), e.symm⟩
    exact e ▸ isClosed_iInter fun i => isClosed_eq (I2.continuous.matrix_elem _ _) continuous_const
  · have c1 : Continuous fun p : (Fin 1 → Fin M → AF F ⊗[F] E) × (Fin 1 → Fin M → AF F ⊗[F] E) => p.1 0 :=
      (continuous_apply 0).comp continuous_fst
    have c2 : Continuous fun p : (Fin 1 → Fin M → AF F ⊗[F] E) × (Fin 1 → Fin M → AF F ⊗[F] E) => p.2 0 :=
      (continuous_apply 0).comp continuous_snd
    exact hscc.comp (continuous_const.mul ((hfC.comp (c1.prodMk c2)).sub (hfC.comp (c2.prodMk c1)))).neg
  · refine ext _ _ ?_
    show nM s _ 0 (z (0, 0)) = 1
    have z0 : (s : _ → _) ∘ (0 : Fin M → AF F ⊗[F] E) = 0 := funext fun _ => map_zero s
    simp [nM, hz, hhf, hform, z0, pm_one]
  · intro w t w' t'
    refine ext _ _ ((nM_mul _ _ _ _).trans (congrArg (nM s _ _) ?_))
    have := sc1 (-(κ * (hf (w 0) (w' 0) - hf (w' 0) (w 0)))) (by simp only [map_neg, map_mul, map_sub, hκs, hfc]; ring)
    simp only [hz, map_add, add_mul, Pi.add_apply, hhf, hform_add] at this ⊢
    linear_combination (hform s (JR (AF F) J) (w 0) (w' 0)) * hκ2 - this
  · intro w
    simp [hsc', hhf, hform]
  · intro u w t
    refine ext _ _ ((iM_nM u.2 _ _).trans (congrArg (fun y => nM s _ _ y * _) ?_))
    exact congrArg (fun y => -(κ * y) + _) (hform_U u.2 _).symm
  · intro a w t
    refine ext _ _ ((mM_nM hs a _ _).trans (congrArg (fun y => nM s _ _ y * _) ?_))
    have e : (s : _ → _) ∘ (s a • w 0) = (a : AF F ⊗[F] E) • (s ∘ w 0) := by funext i; simp [hs]
    simp only [hz, map_mul, norm_sigR _ hcm, Pi.smul_apply, hhf, hform_eq, e, Matrix.smul_vecMul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  · intro u a
    refine ext _ _ ?_
    show pm _ 0 0 (s _) 0 1 * pm 1 0 0 1 0 _ = pm 1 0 0 1 0 _ * pm _ 0 0 (s _) 0 1
    simp [pm_mul]
  · intro p u a
    funext k i
    rw [Subsingleton.elim k 0, act, hval]
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;> simp [pm, blk, eOne]
  · intro h a ha
    obtain ⟨p, u, a', e⟩ := dec h fun i => by rw [← act, ha]; simp [eOne]
    have : a' = a := Units.ext (by
      have h1 := act h 0
      rw [ha, e, hval] at h1
      simpa [eOne, pm, blk] using h1.symm)
    exact ⟨p, u, this ▸ e⟩
  · intro w t
    refine rat (nM (σ : E →+* E) J (w 0) (-(1 / 2 * hform (σ : E →+* E) J (w 0) (w 0)) + algebraMap F E t * δ)) _
      (nM_unit hss hJE ?_) ?_
    · simp only [map_add, map_neg, map_mul, hform_conj hss hJE, RingHom.coe_coe, AlgHom.commutes, hδ, map_div₀, map_one,
        map_ofNat]
      ring
    · show nM s _ _ (z _) = _
      rw [nM, nM, pm_map, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
      congr 1
      · simp only [hz, hhf, hform, map_add, map_neg, map_mul, map_sum, ratTup, hsi, JR, Matrix.map_apply, hκ, hdl]
        congr 2
        exact ((Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes t).symm
      · funext i
        simp [Matrix.vecMul, dotProduct, ratTup, hsi, JR]
  · rintro u ⟨g, hg, e⟩
    refine rat (pm 1 0 0 1 0 g.val) _ (iM_unit hg) ?_
    have e' : u.1.val = g.val.map (inclR (AF F)) := (congrArg Units.val e).symm
    show pm 1 0 0 1 0 u.1.val = _
    rw [pm_map, e', map_one, map_zero]
    congr 1 <;> exact funext fun _ => (map_zero _).symm
  · intro l a ha
    refine rat _ _ (mM_unit hss l) ?_
    have e : ((a⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (AF F) ((l⁻¹ : Eˣ) : E) :=
      Units.inv_eq_of_mul_eq_one_right (by rw [ha, ← map_mul, Units.mul_inv, map_one])
    show pm _ 0 0 (s _) 0 1 = _
    rw [pm_map, e, ha, hsi, map_zero, Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1 <;> exact funext fun _ => (map_zero _).symm

end CompanionTheory.PlacePermOperatorBicommutantSpan
