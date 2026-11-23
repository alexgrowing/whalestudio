import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.MemIntLocOfIdem
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Vf

open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v : Pl F}

theorem std_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : Pl F) : ψ ≠ 1 := fun h =>
  GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v (by rw [h]; rfl)

theorem tens_smul {κ : Type} (c : ℂ) (φ : (κ → Fv F v) → ℂ) (r) : tens (evFin F v) (c • φ) r = c • tens (evFin F v) φ r :=
  (tensL v r).map_smul c φ

theorem eigen {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ)
    {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (Γ : Set W) (hAt : ∀ γ ∈ Γ, At (evFin F v) γ)
    (hΓ : ∀ z, At (evFin F v) z → (∀ γ ∈ Γ, ψ (B γ z) = 1) → z ∈ Γ) (χ : W → ℂ) {φ : (κ → Fv F v) → ℂ}
    (hs : φ ∈ SB _) (h0 : φ ≠ 0) (hφ : ∀ γ ∈ Γ, schr (psiAt ψ v) (locCo co v γ) φ = χ γ • φ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (hp : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ)
    (ha : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ) (A : W → W)
    (hi : ∀ w, ∀ Φ ∈ schA F κ, T (co.rho ψ w Φ) = co.rho ψ (A w) (T Φ)) (hw : ∀ u, sg v 1 • u = 0 → A u = u)
    (hA : ∀ γ ∈ Γ, ∃ γ' ∈ Γ, A γ' = γ ∧ χ γ' = χ γ) : ∃ c : ℂ, Acts (evFin F v) T φ (c • φ) := by
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base κ v
  have ac : Acts (evFin F v) T φ (res v x₀ (T (tens (evFin F v) φ r₀))) := by
    refine acts_res v hψ.1 (std_ne_one hψ v) hψ.2.1 hp ha (fun w h1 h2 Φ hΦ => ?_) h₁ hs (h₀ φ hs)
    obtain ⟨u, rfl⟩ := co.e.surjective w
    have hu : sg v 1 • u = 0 := by
      apply co.e.injective
      rw [map_smul, map_zero]
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · change sg v 1 * (co.e u).1 i = 0
        rw [mul_comm, mul_sg, show evFin F v ((co.e u).1 i) = 0 from congrFun h1 i, zero_mul, map_zero]
      · change sg v 1 * (co.e u).2 i = 0
        rw [mul_comm, mul_sg, show evFin F v ((co.e u).2 i) = 0 from congrFun h2 i, zero_mul, map_zero]
    have := hi u Φ hΦ
    rwa [hw u hu] at this
  set φ' := res v x₀ (T (tens (evFin F v) φ r₀))
  have hs' : φ' ∈ SB _ := res_mem v x₀ (hp _ (h₀ φ hs).2)
  have rt : ∀ f : (κ → Fv F v) → ℂ, res v x₀ (tens (evFin F v) f r₀) = f := fun f => funext fun y => by
    change f (evA κ v (putA v x₀ y)) * r₀ (putA v x₀ y) = _
    rw [ev_put (evA_inA v), inv_putA v (h₀ φ hs).1, h₁, mul_one]
  obtain ⟨c, hc⟩ := local_line co hψ v Γ hAt hΓ χ hs hs' h0 hφ fun γ hγ => by
    obtain ⟨γ', hγ', e1, e2⟩ := hA γ hγ
    have a1 := GlobalTheory.VacBridge.rho_acts_locCo co ψ v γ (hAt γ hγ) φ' r₀ (h₀ _ hs')
    have a2 := GlobalTheory.VacBridge.rho_acts_locCo co ψ v γ' (hAt γ' hγ') φ r₀ (h₀ _ hs)
    have a3 := hi γ' _ (h₀ φ hs).2
    rw [a2, hφ γ' hγ', tens_smul, map_smul, e1, e2, ac r₀ (h₀ φ hs), a1, ← tens_smul] at a3
    rw [← rt (schr _ _ _), ← a3, rt]
  exact ⟨c, hc ▸ ac⟩

section Alg

variable {R A α β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype α] [Fintype β]

theorem hTens_tr (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JB JA xᵀ yᵀ = hTens c JA JB x y := by
  simp only [hTens, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem hTens_dbl (JA : Matrix α α A) (JB : Matrix β β A) (x₁ x₂ y₁ y₂ : Matrix α β A) :
    hTens c JA (dbl JB) (Matrix.fromCols x₁ x₂) (Matrix.fromCols y₁ y₂) = hTens c JA JB x₁ y₁ - hTens c JA JB x₂ y₂ := by
  simp [hTens, dbl, Fintype.sum_sum_type, Finset.sum_add_distrib, sub_eq_add_neg]

theorem symp_dbl (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (x₁ x₂ y₁ y₂ : Matrix α β A) :
    symp c ξ JB (dbl JA) (Matrix.fromCols x₁ᵀ x₂ᵀ) (Matrix.fromCols y₁ᵀ y₂ᵀ) = symp c ξ JA JB x₁ y₁ - symp c ξ JA JB x₂ y₂ := by
  rw [symp, hTens_dbl, hTens_tr, hTens_tr, mul_sub, map_sub]; rfl

theorem symp_smul (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (u : R) (x y : Matrix α β A) :
    symp c ξ JA JB (u • x) y = u * symp c ξ JA JB x y := by
  rw [symp, symp, ← smul_eq_mul u, ← map_smul, ← mul_smul_comm]
  simp [hTens, Finset.smul_sum]

theorem symp_zero (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (y : Matrix α β A) : symp c ξ JA JB 0 y = 0 := by
  simp [symp, hTens]

end Alg

theorem star_psiAt {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : Fv F v) : star (psiAt ψ v t) = psiAt ψ v (-t) := by
  have h := norm_addChar _ (GlobalTheory.SplitWeil.isCompact_int (Fv F v)) _ (GlobalTheory.VacAny.continuous_psiV hψ.1 v) t
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj h).symm

theorem star_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {a : AF F} (ha : At (evFin F v) a) : star (ψ a) = ψ (-a) := by
  have hn : At (evFin F v) (-a) := fun u hu => by rw [smul_neg, ha u hu, neg_zero]
  rw [GlobalTheory.StdVacuum.psi_eq_psiLoc ψ v a ha, GlobalTheory.StdVacuum.psi_eq_psiLoc ψ v _ hn, map_neg]
  exact star_psiAt hψ _

theorem schr_box {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a b : (κ → Fv F v) × (κ → Fv F v))
    (φ φ' : (κ → Fv F v) → ℂ) : schr (psiAt ψ v) (Sum.elim a.1 b.1, Sum.elim a.2 (-b.2)) (boxFun φ (star φ')) =
      boxFun (schr (psiAt ψ v) a φ) (star (schr (psiAt ψ v) b φ')) := by
  funext x
  simp only [schr, boxFun, Pi.star_apply, star_mul', star_psiAt hψ]
  rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
  congr 2
  · simp [dotProduct, Fintype.sum_sum_type]; ring
  all_goals first | rfl | congr 2

theorem sb_star {κ : Type} [TopologicalSpace κ] {φ : κ → ℂ} (h : φ ∈ SB κ) : star φ ∈ SB κ :=
  ⟨h.1.comp star, h.2.comp_left (g := star) (star_zero _)⟩

theorem sb_box_loc {κ K : Type} [Fintype κ] [TopologicalSpace K] [T2Space K] {φ φ' : (κ → K) → ℂ} (h : φ ∈ SB _) (h' : φ' ∈ SB _) :
    boxFun φ φ' ∈ SB (κ ⊕ κ → K) := by
  have c1 : Continuous fun z : κ ⊕ κ → K => z ∘ Sum.inl := continuous_pi fun j => continuous_apply _
  have c2 : Continuous fun z : κ ⊕ κ → K => z ∘ Sum.inr := continuous_pi fun j => continuous_apply _
  refine ⟨(h.1.comp_continuous c1).mul (h'.1.comp_continuous c2), ?_⟩
  have hc : IsCompact ((fun p : (κ → K) × (κ → K) => (Sum.elim p.1 p.2 : κ ⊕ κ → K)) '' (tsupport φ ×ˢ tsupport φ')) :=
    (h.2.isCompact.prod h'.2.isCompact).image (continuous_pi fun i => by cases i <;> simp <;> fun_prop)
  refine HasCompactSupport.of_support_subset_isCompact hc fun z hz => ?_
  have := mul_ne_zero_iff.1 hz
  exact ⟨(z ∘ Sum.inl, z ∘ Sum.inr), ⟨subset_tsupport _ this.1, subset_tsupport _ this.2⟩, Sum.elim_comp_inl_inr z⟩

theorem star_mem_schA {κ : Type} [Fintype κ] {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) : star Φ ∈ schA F κ := by
  classical
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨f.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ), star g, sb_star hg, funext fun x => ?_⟩
    simp [pureA]
  | zero => rw [star_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
  | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

open GlobalTheory.DiagForm in
theorem lDiag_ne {κ : Type} [Fintype κ] {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (h0 : Φ ≠ 0) :
    lDiag F κ (boxFun Φ (star Φ)) ≠ 0 := by
  classical
  letI := GlobalTheory.DiagForm.measAf (F := F)
  haveI := GlobalTheory.DiagForm.borelAf (F := F)
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  have hm := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ Φ h _ (star_mem_schA h)
  have hi := integrable_resD hm
  have hc : ∀ Ψ ∈ schA F (κ ⊕ κ), Continuous (resD F κ Ψ) := fun Ψ hΨ => by
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      rw [show resD F κ (pureA F f g) = _ from funext (resD_pureA f g)]
      exact ((compD F κ f).continuous.comp continuous_fst).mul (hg.1.continuous.comp
        (continuous_pi fun i => by cases i <;> exact (continuous_apply _).comp continuous_snd))
    | zero => rw [map_zero]; exact continuous_zero
    | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
    | smul c x _ hx => rw [map_smul]; exact hx.const_smul c
  have e : resD F κ (boxFun Φ (star Φ)) = fun p => ((Complex.normSq (Φ (glue p)) : ℝ) : ℂ) := funext fun p =>
    Complex.mul_conj _
  rw [lDiag, LinearMap.comp_apply, Lext_apply _ hi]
  have hc' := hc _ hm
  rw [e] at hc' hi ⊢
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  have g0 : glue (0 + shiftOf x) = x := by
    rw [glue_add_shiftOf]
    funext i
    refine Prod.ext ?_ (zero_add _)
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ 0 i) + _ = _
    simp
  haveI : (mu F κ).IsOpenPosMeasure := by unfold mu; infer_instance
  refine (integral_pos_of_integrable_nonneg_nonzero (x := 0 + shiftOf x) (Complex.continuous_re.comp hc') hi.re
    (fun p => Complex.normSq_nonneg _) ?_).ne'
  change Complex.normSq (Φ (glue _)) ≠ 0
  rw [g0]
  exact (map_ne_zero _).2 hx

theorem mul_latAtV {X : Spc F E n} {W : Spc F E d} {k : Matrix (Fin n) (Fin n) (AE F E)} (hk : k ∈ Pres v X) {γ}
    (hγ : γ ∈ latAtV X W v) : k * γ ∈ latAtV X W v := by
  have key : ∀ y ∈ W.L, ∀ w ∈ latW X v, Matrix.vecMulVec w (incV y) ∈ latAtV X W v := fun y hy w hw => by
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, x, hx, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨a, ha, hav, x, hx, y, hy, ?_⟩
      ext i j
      simp [incM, incV, Matrix.vecMulVec_apply]
    | zero =>
      have : Matrix.vecMulVec (0 : Fin n → AE F E) (incV (F := F) y) = 0 := by ext i j; exact zero_mul _
      rw [this]; exact zero_mem _
    | add y z _ _ hy hz => rw [Matrix.add_vecMulVec]; exact add_mem hy hz
    | neg y _ hy => rw [Matrix.neg_vecMulVec]; exact neg_mem hy
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    have e : a • incM F (Matrix.vecMulVec x y) = Matrix.vecMulVec (fun i => a • inclR (F := F) (AF F) (x i)) (incV y) := by
      ext i j
      simp [incM, incV, Matrix.vecMulVec_apply]
    rw [e, Matrix.mul_vecMulVec]
    exact key y hy _ (hk _ (AddSubgroup.subset_closure ⟨a, ha, hav, x, hx, rfl⟩))
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mul_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mul_neg]; exact neg_mem hy

variable (v) in

def PresD (X : Spc F E n) (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) : Prop :=
  ∃ a ∈ Pres v X, ∃ b ∈ Pres v X, ∃ c ∈ Pres v X, ∃ e ∈ Pres v X, g = Matrix.fromBlocks a b c e

theorem PresD.mul {X : Spc F E n} {g g'} (h : PresD v X g) (h' : PresD v X g') : PresD v X (g * g') := by
  obtain ⟨a, ha, b, hb, c, hc, e, he, rfl⟩ := h
  obtain ⟨a', ha', b', hb', c', hc', e', he', rfl⟩ := h'
  exact ⟨_, add_mem (mul_mem ha ha') (mul_mem hb hc'), _, add_mem (mul_mem ha hb') (mul_mem hb he'), _,
    add_mem (mul_mem hc ha') (mul_mem he hc'), _, add_mem (mul_mem hc hb') (mul_mem he he'), Matrix.fromBlocks_multiply ..⟩

theorem dbl_eigen {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') {M : Model σ X W} {φ} (hφ : M.IsVac B.ψ v φ)
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)} (hd' : ∀ x, d'.e xᵀ = M.co.e x)
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))}
    (hdd : IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd) {omd}
    (hsp : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd) (g : UG (cA σ) (dbl (incM F X.J)))
    (hg : At (evFin F v) (g.1.1 - 1)) (hg' : PresD v X (g⁻¹).1.1) :
    ∃ c : ℂ, Acts (evFin F v) (omd g) (boxFun φ (star φ)) (c • boxFun φ (star φ)) := by
  obtain ⟨hs, h0, θ, -, hθ⟩ := hφ
  have hAt := (latAtV_at_stable X W v).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  have hv : ∀ γ ∈ latAtV X W v, schr (psiAt B.ψ v) (locCo M.co v γ) φ = _ := fun γ hγ =>
    (eq_of_acts v h₁ (h₀ φ hs) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hAt γ hγ) φ)).trans
      (eq_of_acts v h₁ (h₀ φ hs) (hθ γ hγ)).symm
  set θ' := inclR (F := F) (AF F) (θ : E)
  refine eigen dd hB.std {z | ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, z = Matrix.fromCols γ₁ᵀ γ₂ᵀ} ?_ ?_
    (fun z => B.ψ (⅟(2 : AF F) * symp (cA σ) θ' (incM F W.J) (dbl (incM F X.J)) z z)) (sb_box_loc hs (sb_star hs)) ?_ ?_
    (omd g) (hsp.pres g) (hsp.adm g) (actB (cA σ) g) (hsp.impl g) ?_ ?_
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩ u hu
    ext i (j | j)
    exacts [congrFun (congrFun (hAt _ h1 u hu) j) i, congrFun (congrFun (hAt _ h2 u hu) j) i]
  · intro z hz h
    have ez : z = Matrix.fromCols (z.toCols₁ᵀ)ᵀ (z.toCols₂ᵀ)ᵀ := (Matrix.fromCols_toCols z).symm
    refine ⟨_, mem_latAtV hB hX hW v (fun u hu => ?_) fun γ hγ => ?_, _, mem_latAtV hB hX hW v (fun u hu => ?_) fun γ hγ => ?_, ez⟩
    · ext i j; exact congrFun (congrFun (hz u hu) j) (Sum.inl i)
    · have := h _ ⟨γ, hγ, 0, zero_mem _, rfl⟩
      rwa [ez, symp_dbl, symp_zero, sub_zero] at this
    · ext i j; exact congrFun (congrFun (hz u hu) j) (Sum.inr i)
    · have := h _ ⟨0, zero_mem _, -γ, neg_mem hγ, rfl⟩
      rwa [ez, symp_dbl, symp_zero, zero_sub, ← neg_one_smul (AF F) γ, symp_smul, neg_one_mul, neg_neg] at this
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    exact fun e => mul_ne_zero hx (star_ne_zero.2 hx) (congrFun e (Sum.elim x x))
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩
    have e : locCo dd v (Matrix.fromCols γ₁ᵀ γ₂ᵀ) = (Sum.elim (locCo M.co v γ₁).1 (locCo M.co v γ₂).1,
        Sum.elim (locCo M.co v γ₁).2 (-(locCo M.co v γ₂).2)) := by
      have := hdd γ₁ᵀ γ₂ᵀ
      rw [hd', hd'] at this
      ext (i | i) <;> simp [locCo, this]
    have a2 : At (evFin F v) (⅟(2 : AF F) * symp (cA σ) θ' (incM F X.J) (incM F W.J) γ₂ γ₂) := fun u hu => by
      rw [smul_eq_mul, mul_left_comm, ← symp_smul, hAt _ h2 u hu, symp_zero, mul_zero]
    rw [e, schr_box hB.std, hv _ h1, hv _ h2, symp_dbl, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← star_psi hB.std a2]
    funext x
    simp only [boxFun, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul']
    ring
  · intro u hu
    have : u * (g.1.1 - 1)ᵀ = 0 := by
      rw [← idem_smul hg, Matrix.transpose_smul, Matrix.mul_smul, ← Matrix.smul_mul]
      change (sg v 1 • u) * _ = 0
      rw [hu, Matrix.zero_mul]
    rwa [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩
    obtain ⟨a, ha, b, hb, c, hc, e, he, eg⟩ := hg'
    refine ⟨Matrix.fromCols γ₁ᵀ γ₂ᵀ * ((g⁻¹).1.1)ᵀ, ⟨a * γ₁ + b * γ₂, add_mem (mul_latAtV ha h1) (mul_latAtV hb h2),
      c * γ₁ + e * γ₂, add_mem (mul_latAtV hc h1) (mul_latAtV he h2), ?_⟩, ?_, ?_⟩
    · rw [eg, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp only [Matrix.transpose_add, Matrix.transpose_mul]
    · have : g.1.1 * (g⁻¹).1.1 = 1 := g.1.mul_inv
      rw [actB, Matrix.mul_assoc, ← Matrix.transpose_mul, this, Matrix.transpose_one, Matrix.mul_one]
    · rw [symp, symp, hTens_mul (cA σ) _ (g⁻¹).2]

theorem rule_diag {ψ : AddChar (AF F) ℂ} {JX : Matrix (Fin n) (Fin n) (AE F E)} {JW : Matrix (Fin d) (Fin d) (AE F E)}
    {κ : Type} [Fintype κ] {d' : Darboux (symp (R := AF F) (cA σ) (-1) JW JX) κ}
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) JW (dbl JX)) (κ ⊕ κ)} (hdd : IsDblCoord (cA σ) (-1) JW JX d' dd)
    {χ : Chr F E} {omd} (hr : SiegelRule (cA σ) (adeleClass F) ψ (-1) JW (dbl JX) dd χ (diagCols (Fin n)) omd)
    (p : UG (cA σ) (dbl JX)) (t : GL (Fin n) (AE F E))
    (hp : p.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = (diagCols (Fin n) : Matrix _ _ (AE F E)) * t.1)
    (ht : χ (Matrix.GeneralLinearGroup.det t) = 1) {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (h0 : Φ ≠ 0) {c : ℂ}
    (hc : omd p (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ)) :
    c = ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^
      ((d : ℝ) / 2) : ℝ) : ℂ) := by
  have := hr (GlobalTheory.DiagForm.lDiag F κ) GlobalTheory.DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin n) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols]; simp
    rw [e, Darboux.rho, hdd]
    exact GlobalTheory.DiagForm.lDiag_schr ψ _ _ hφ) p t hp _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ Φ h _ (star_mem_schA h))
  rw [hc, map_smul, smul_eq_mul, ht, Circle.coe_one, one_mul, Fintype.card_fin] at this
  exact mul_right_cancel₀ (lDiag_ne h h0) this

end PositivityTheory.ThKG.Loc.Cone.Vf

end
