import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.ContinuousExpG
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Grp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Tow.Levi

variable {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁}

variable (σ) in

def fa (J : Matrix (Fin d) (Fin d) E) (w z : Fin d → AE F E) : AE F E := w ⬝ᵥ incM F J *ᵥ fun i => cA σ (z i)

theorem fa_inc (J : Matrix (Fin d) (Fin d) E) (w z : Fin d → E) :
    fa σ J (incV F w) (incV F z) = inclR (F := F) (AF F) (form σ J w z) := by
  simp only [fa, form, dotProduct, Matrix.mulVec, map_sum, map_mul]
  rfl

theorem fa_mat {J : Matrix (Fin d) (Fin d) E} (g : UA σ J) (w z : Fin d → AE F E) : fa σ J (mat g *ᵥ w) (mat g *ᵥ z) = fa σ J w z := by
  have e : (fun i => cA σ ((mat g *ᵥ z) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (z i) :=
    funext fun i => RingHom.map_mulVec (cA σ).toRingHom (mat g) z i
  rw [fa, fa, e]
  conv_rhs => rw [← mat_unit g, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w, Matrix.vecMul_transpose]

theorem fa_smul (J : Matrix (Fin d) (Fin d) E) (w z : Fin d → AE F E) (a : AE F E) : fa σ J w (a • z) = cA σ a * fa σ J w z := by
  have e : (fun i => cA σ ((a • z) i)) = cA σ a • fun i => cA σ (z i) := funext fun i => map_mul _ _ _
  rw [fa, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, fa]

def Par {J : Matrix (Fin d) (Fin d) E} (x : Fin d → E) (t : (AE F E)ˣ) (m : UA σ J) : Prop :=
  mat m *ᵥ incV F x = t.1 • incV F x ∧ ∀ w, fa σ J w (incV F x) = 0 → ∃ a : AE F E, mat m *ᵥ w = w + a • incV F x

section Par

variable {J : Matrix (Fin d) (Fin d) E} {x x' : Fin d → E} {s t : (AE F E)ˣ} {m m' g : UA σ J}

theorem inv_vec {a b : Fin d → AE F E} (h : mat g *ᵥ a = b) : mat g⁻¹ *ᵥ b = a := by
  rw [← h, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]

theorem Par.div (h : Par x t m) (h' : Par x t m') : Par x 1 (m * m'⁻¹) := by
  have e : mat m'⁻¹ *ᵥ incV F x = (t⁻¹).1 • incV F x :=
    inv_vec (by rw [Matrix.mulVec_smul, h'.1, smul_smul, Units.inv_mul, one_smul])
  refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul, h.1, smul_smul, Units.inv_mul, Units.val_one], fun w hw => ?_⟩
  obtain ⟨a, ha⟩ := h.2 w hw
  obtain ⟨b, hb⟩ := h'.2 w hw
  have e2 : mat m'⁻¹ *ᵥ w = w - (b * (t⁻¹).1) • incV F x := by
    rw [eq_sub_iff_add_eq, mul_smul, ← e, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
    exact inv_vec hb
  refine ⟨a - b, ?_⟩
  rw [mat_mul, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_sub, ha, Matrix.mulVec_smul, h.1, smul_smul, mul_assoc, Units.inv_mul,
    mul_one, sub_smul, add_sub_assoc]

theorem Par.conj (h : Par x t m) (hg : mat g *ᵥ incV F x = s.1 • incV F x') : Par x' t (g * m * g⁻¹) := by
  have e : mat g⁻¹ *ᵥ incV F x' = (s⁻¹).1 • incV F x :=
    inv_vec (by rw [Matrix.mulVec_smul, hg, smul_smul, Units.inv_mul, one_smul])
  constructor
  · rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul, h.1, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hg, smul_comm t.1, smul_smul _ s.1, Units.inv_mul, one_smul]
  · intro w hw
    obtain ⟨a, ha⟩ := h.2 (mat g⁻¹ *ᵥ w) (by
      rw [← fa_mat g, hg, fa_smul, Matrix.mulVec_mulVec, mat_mul_inv, Matrix.one_mulVec, hw, mul_zero])
    refine ⟨a * s.1, ?_⟩
    rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_mulVec, mat_mul_inv,
      Matrix.one_mulVec, Matrix.mulVec_smul, hg, smul_smul]

end Par

theorem form_yx (h : IsCMExt F E σ) (hJ : (∀ i j, σ (W.J j i) = W.J i j) ∨ ∀ i j, σ (W.J j i) = -W.J i j) (hH : IsPlane σ H W W₁) :
    form σ W.J H.y H.x ≠ 0 := by
  have hs := sig_sig h
  rcases hJ with hJ | hJ
  · have : form σ W.J H.y H.x = σ (form σ W.J H.x H.y) := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, hs, hJ]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, hH.xy, map_one]; exact one_ne_zero
  · rw [form_skew hs hJ, hH.xy, map_one]; simp

theorem fr_vec {R : Type} [CommRing R] (ι : Matrix (Fin d) (Fin d₁) R) (x y : Fin d → R) (c : Fin d₁ ⊕ Fin 2 → R) :
    fr ι x y *ᵥ c = ι *ᵥ (fun j => c (Sum.inl j)) + c (Sum.inr 0) • x + c (Sum.inr 1) • y := by
  ext i
  simp [fr, Matrix.mulVec, dotProduct, mul_comm, add_assoc]

theorem fr_inv (hyx : form σ W.J H.y H.x ≠ 0) (hH : IsPlane σ H W W₁) :
    ∃ A' : Matrix (Fin d₁ ⊕ Fin 2) (Fin d) E, fr H.ι H.x H.y * A' = 1 ∧ A' * fr H.ι H.x H.y = 1 := by
  have inj : LinearMap.ker (fr H.ι H.x H.y).mulVecLin = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun c hc => ?_
    rw [Matrix.mulVecLin_apply, fr_vec] at hc
    have l : ∀ z, form σ W.J (H.ι *ᵥ fun j => c (Sum.inl j)) z + c (Sum.inr 0) * form σ W.J H.x z +
        c (Sum.inr 1) * form σ W.J H.y z = 0 := fun z => by
      have := congrArg (fun v => form σ W.J v z) hc
      simpa only [form, add_dotProduct, smul_dotProduct, zero_dotProduct, smul_eq_mul] using this
    have h0 := l H.y
    have h1 := l H.x
    rw [(hH.orth _).2, hH.xy, hH.yy, zero_add, mul_zero, add_zero, mul_one] at h0
    rw [(hH.orth _).1, hH.xx, zero_add, mul_zero, zero_add, mul_eq_zero, or_iff_left hyx] at h1
    rw [h0, h1, zero_smul, zero_smul, add_zero, add_zero] at hc
    have h2 : (fun j => c (Sum.inl j)) = 0 := Matrix.eq_zero_of_vecMul_eq_zero hH.nondeg (by
      rw [← hH.gram, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hc, Matrix.zero_vecMul,
        Matrix.zero_vecMul])
    ext (j | j)
    · exact congrFun h2 j
    · fin_cases j
      exacts [h0, h1]
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective _ inj
  have h2 : LinearMap.toMatrix' p * fr H.ι H.x H.y = 1 := Matrix.ext_iff_mulVec.2 fun z => by
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]
    exact LinearMap.congr_fun hp z
  exact ⟨_, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hH.rank])).1 h2, h2⟩

theorem fa_iota (hH : IsPlane σ H W W₁) (z : Fin d₁ → AE F E) : fa σ W.J (incM F H.ι *ᵥ z) (incV F H.x) = 0 := by
  have e : H.ιᵀ *ᵥ (W.J *ᵥ fun i => σ (H.x i)) = 0 := funext fun j => by
    have := (hH.orth (Pi.single j 1)).1
    rw [form, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, single_one_dotProduct] at this
    exact this
  change _ ⬝ᵥ incM F W.J *ᵥ incV F (fun i => σ (H.x i)) = 0
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, incM_mulVec]
  change z ⬝ᵥ incM F H.ιᵀ *ᵥ _ = 0
  rw [incM_mulVec, e, show incV F (0 : Fin d₁ → E) = 0 from funext fun _ => map_zero _, dotProduct_zero]

theorem exists_decomp_of_fa_incV_x_eq_zero (hyx : form σ W.J H.y H.x ≠ 0) (hH : IsPlane σ H W W₁) {w : Fin d → AE F E} (hw : fa σ W.J w (incV F H.x) = 0) :
    ∃ (z : Fin d₁ → AE F E) (a : AE F E), w = incM F H.ι *ᵥ z + a • incV F H.x := by
  obtain ⟨A, h1, -⟩ := fr_inv hyx hH
  have e : w = fr (incM F H.ι) (incV F H.x) (incV F H.y) *ᵥ (incM F A *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, show fr (incM F H.ι) (incV F H.x) (incV F H.y) = incM F (fr H.ι H.x H.y) from
      fr_map (inclR (F := F) (AF F)), ← incM_mul, h1, incM_one, Matrix.one_mulVec]
  rw [fr_vec] at e
  generalize incM F A *ᵥ w = c at e
  have h2 := fa_iota hH fun j => c (Sum.inl j)
  have h3 := fa_inc (σ := σ) W.J H.x H.x
  have h4 := fa_inc (σ := σ) W.J H.y H.x
  rw [e] at hw
  simp only [fa, add_dotProduct, smul_dotProduct, smul_eq_mul] at hw h2 h3 h4
  rw [h2, h3, h4, hH.xx, map_zero, mul_zero, add_zero, zero_add, (hyx.isUnit.map _).mul_left_eq_zero] at hw
  exact ⟨_, _, by rw [e, hw, zero_smul, add_zero]⟩

theorem par_of (hyx : form σ W.J H.y H.x ≠ 0) (hH : IsPlane σ H W W₁) {t : (AE F E)ˣ} {m : UA σ W.J}
    (h1 : mat m *ᵥ incV F H.x = t.1 • incV F H.x)
    (h2 : ∀ z, ∃ a : AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) : Par H.x t m :=
  ⟨h1, fun w hw => by
    obtain ⟨z, a, rfl⟩ := exists_decomp_of_fa_incV_x_eq_zero hyx hH hw
    obtain ⟨b, hb⟩ := h2 z
    refine ⟨b + a * t - a, ?_⟩
    rw [Matrix.mulVec_add, hb, Matrix.mulVec_smul, h1, smul_smul, sub_smul, add_smul]
    abel⟩

theorem IsLevi.par (hyx : form σ W.J H.y H.x ≠ 0) (hH : IsPlane σ H W W₁) {t : (AE F E)ˣ} {m : UA σ W.J}
    (h : IsLevi (W₁ := W₁) H t 1 m) : Par H.x t m :=
  par_of hyx hH h.1 fun z => ⟨0, by rw [Matrix.mulVec_mulVec, h.2.2, mat_one, Matrix.mul_one, zero_smul, add_zero]⟩

theorem line_iff (hH : IsPlane σ H W W₁) (hyx : form σ W.J H.y H.x ≠ 0) (m : UA σ W.J) :
    (mat m *ᵥ incV F H.x = incV F H.x ∧ ∀ z, ∃ a : AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) ↔
    (∀ u ∈ Submodule.span E {H.x}, mat m *ᵥ incV F u = incV F u) ∧ ∀ z : Fin d → E, (∀ u ∈ Submodule.span E {H.x}, form σ W.J z u = 0) →
      mat m *ᵥ incV F z - incV F z ∈ Submodule.span (AE F E) (incV F '' (Submodule.span E {H.x} : Set (Fin d → E))) := by
  have sm : ∀ a : E, incV F (a • H.x) = inclR (F := F) (AF F) a • incV F H.x := fun a => funext fun _ => map_mul _ _ _
  have hx := Submodule.mem_span_singleton_self (R := E) H.x
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun u hu => ?_, fun z hz => ?_⟩
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
      rw [sm, Matrix.mulVec_smul, h1]
    · obtain ⟨a, ha⟩ := (par_of (t := 1) hyx hH (by simpa using h1) h2).2 (incV F z) (by rw [fa_inc, hz _ hx, map_zero])
      rw [ha, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx, rfl⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨h1 _ hx, fun z => ?_⟩
    have le : Submodule.span (AE F E) (incV F '' (Submodule.span E {H.x} : Set (Fin d → E))) ≤
        Submodule.span (AE F E) {incV F H.x} := Submodule.span_le.2 (by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
      rw [sm]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    have : mat m *ᵥ (incM F H.ι *ᵥ z) - incM F H.ι *ᵥ z ∈ Submodule.span (AE F E) {incV F H.x} := by
      rw [pi_eq_sum_univ' z]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, ← Finset.sum_sub_distrib, ← smul_sub]
      refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (le ?_)
      have e : (Pi.single j 1 : Fin d₁ → AE F E) = incV F (Pi.single j 1) := funext fun i => by
        by_cases k : i = j <;> simp [incV, k]
      rw [e, incM_mulVec]
      refine h2 _ fun u hu => ?_
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
      have e2 : (fun i => σ ((a • H.x) i)) = σ a • fun i => σ (H.x i) := funext fun i => map_mul _ _ _
      rw [form, e2, Matrix.mulVec_smul, dotProduct_smul]
      exact smul_eq_zero_of_right _ (hH.orth _).1
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    exact ⟨a, by rw [ha, add_sub_cancel]⟩

theorem unipLine : UnipLine := fun _ _ _ _ _ _ _ _ h _ _ _ _ _ hJ hH =>
  congrArg Subgroup.closure (Set.ext (line_iff hH (form_yx h hJ hH)))

theorem mem_unip (h : IsCMExt F E σ) (hJ : (∀ i j, σ (W.J j i) = W.J i j) ∨ ∀ i j, σ (W.J j i) = -W.J i j) (hH : IsPlane σ H W W₁)
    {u : UA σ W.J} : u ∈ unip σ W H ↔ Par H.x 1 u := by
  have hyx := form_yx h hJ hH
  rw [unipLine F E σ h d d₁ W W₁ H hJ hH, (unipU_eq _).choose_spec.choose_spec.2, ← line_iff hH hyx]
  exact ⟨fun k => par_of hyx hH (by simpa using k.1) k.2, fun k => ⟨by simpa using k.1, fun z => k.2 _ (fa_iota hH z)⟩⟩

theorem unipGood (h : IsCMExt F E σ) (hJ : (∀ i j, σ (W.J j i) = W.J i j) ∨ ∀ i j, σ (W.J j i) = -W.J i j) (hd : W.J.det ≠ 0)
    (hH : IsPlane σ H W W₁) : UnipGood (unip σ W H) :=
  unipLine F E σ h d d₁ W W₁ H hJ hH ▸ (unipUGood F E σ h d W hJ hd _).1

theorem isFr_plane (h : IsCMExt F E σ) (hJ : ∀ i j, σ (W.J j i) = -W.J i j) (hH : IsPlane σ H W W₁) :
    IsFr (σ : E →+* E) W.J W₁.J H.ι H.x H.y := by
  have hsk := form_skew (sig_sig h) hJ
  have ent : ∀ a b, ((fr H.ι H.x H.y)ᵀ * W.J * (fr H.ι H.x H.y).map (σ : E →+* E)) a b =
      form σ W.J (fun i => fr H.ι H.x H.y i a) (fun i => fr H.ι H.x H.y i b) := fun a b => by
    rw [Matrix.mul_assoc]; rfl
  have col : ∀ j, (fun i => fr H.ι H.x H.y i (Sum.inl j)) = H.ι *ᵥ Pi.single j 1 := fun j => by
    ext i; simp [fr]
  refine ⟨?_, fr_inv (form_yx h (Or.inr hJ) hH) hH⟩
  ext (a | a) (b | b)
  · exact congrFun (congrFun hH.gram a) b
  · rw [ent, col]
    fin_cases b
    exacts [(hH.orth _).1, (hH.orth _).2]
  · rw [ent, col, hsk]
    fin_cases a
    · exact (congrArg (fun z => -σ z) (hH.orth _).1).trans (by simp [gr])
    · exact (congrArg (fun z => -σ z) (hH.orth _).2).trans (by simp [gr])
  · rw [ent]
    fin_cases a <;> fin_cases b
    exacts [hH.xx, hH.xy, (hsk _ _).trans ((congrArg (fun z => -σ z) hH.xy).trans (by simp [gr])), hH.yy]

theorem leviPlane : LeviPlane := by
  intro F E _ _ _ _ _ σ h d d₁ W W₁ H hJ hH
  refine ⟨fun t h₁ => ?_, fun t h₁ m hm u hu => ?_⟩
  · obtain ⟨m, m', e1, e2, e3, e4, e5⟩ := ((isFr_plane h hJ hH).map (inclR (F := F) (AF F)) (c' := (cA σ : AE F E →+* AE F E))
      fun _ => rfl).levi (cA_cA h) t.mul_inv h₁.1.mul_inv h₁.2
    obtain ⟨p, rfl⟩ := exists_UA e1 e2
    exact ⟨p, e3, e4, e5⟩
  · rw [mem_unip h (Or.inr hJ) hH] at hu ⊢
    exact hu.conj hm.1

theorem witt_step (h : IsCMExt F E σ) {J : Matrix (Fin d) (Fin d) E} (hJ : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0)
    {x x' : Fin d → E} (h0 : form σ J x x = 0) (h0' : form σ J x' x' = 0) (hn : form σ J x x' ≠ 0) :
    ∃ g : GL (Fin d) E, g.1ᵀ * J * g.1.map σ = J ∧ g.1 *ᵥ x = x' := by
  have hs := sig_sig h
  have hsk := form_skew hs hJ
  set b := form σ J x x' with hb
  set w := x - x' with hw
  set l : Fin d → E := J *ᵥ fun i => σ (w i) with hl
  have sub : ∀ u, u ⬝ᵥ l = form σ J u x - form σ J u x' := fun u => by
    rw [hl, show (fun i => σ (w i)) = (fun i => σ (x i)) - fun i => σ (x' i) from funext fun i => map_sub _ _ _,
      Matrix.mulVec_sub, dotProduct_sub]; rfl
  have hb' : σ b ≠ 0 := (map_ne_zero _).2 hn
  have ww : w ⬝ᵥ l = σ b - b := by
    rw [hw, sub_dotProduct, sub, sub, h0, h0', hsk x' x]; ring
  have act : ∀ u, (1 + b⁻¹ • Matrix.vecMulVec w l) *ᵥ u = u + (b⁻¹ * (u ⬝ᵥ l)) • w := fun u => by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul,
      dotProduct_comm]
  have iso : ∀ g : Matrix (Fin d) (Fin d) E, (∀ u v, form σ J (g *ᵥ u) (g *ᵥ v) = form σ J u v) → gᵀ * J * g.map σ = J := fun g k => by
    ext i j
    have := k (Pi.single i 1) (Pi.single j 1)
    rw [Matrix.mul_assoc]
    simpa [form, Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite] using this
  have un := iso (1 + b⁻¹ • Matrix.vecMulVec w l) fun u v => by
    have e : ∀ (z : Fin d → E) (c : E), form σ J z (v + c • w) = form σ J z v + σ c * (z ⬝ᵥ l) := fun z c => by
      rw [form, show (fun i => σ ((v + c • w) i)) = (fun i => σ (v i)) + σ c • fun i => σ (w i) from
        funext fun i => by simp, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul]; rfl
    have e2 : form σ J w v = -σ (v ⬝ᵥ l) := hsk w v
    rw [act, act, e, add_dotProduct, smul_dotProduct, ww, form, add_dotProduct, smul_dotProduct, map_mul, map_inv₀]
    change form σ J u v + _ • form σ J w v + _ = _
    rw [e2, smul_eq_mul, smul_eq_mul]
    field_simp
    ring
  have hu : (1 + b⁻¹ • Matrix.vecMulVec w l).det ≠ 0 := fun k => hd (by
    rw [← un, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, k, zero_mul, zero_mul])
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hu, un, ?_⟩
  change (1 + b⁻¹ • Matrix.vecMulVec w l) *ᵥ x = x'
  rw [act, sub, h0, zero_sub, mul_neg, inv_mul_cancel₀ hn, hw]
  simp

theorem wittVec : WittVec := by
  intro F E _ _ _ _ _ σ h d J hJ hd x x' hx hx' h0 h0'
  have hs := sig_sig h
  have hsk := form_skew hs hJ
  by_cases hn : form σ J x x' ≠ 0
  · exact witt_step h hJ hd h0 h0' hn
  rw [not_not] at hn
  have add : ∀ z u v (c : E), form σ J z (u + c • v) = form σ J z u + σ c * form σ J z v := fun z u v c => by
    rw [form, show (fun i => σ ((u + c • v) i)) = (fun i => σ (u i)) + σ c • fun i => σ (v i) from
      funext fun i => by simp, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul]; rfl
  have nd : ∀ z, z ≠ 0 → ∃ v, form σ J z v ≠ 0 := fun z hz => by
    by_contra! k
    refine hz (Matrix.eq_zero_of_vecMul_eq_zero hd (funext fun j => ?_))
    have := k (Pi.single j 1)
    rw [form, Matrix.dotProduct_mulVec] at this
    simpa [dotProduct, Pi.single_apply, apply_ite] using this
  obtain ⟨v, v1, v2⟩ : ∃ v, form σ J x v ≠ 0 ∧ form σ J x' v ≠ 0 := by
    obtain ⟨a, ha⟩ := nd x hx
    obtain ⟨b, hb⟩ := nd x' hx'
    by_cases k : form σ J x' a = 0
    · by_cases k' : form σ J x b = 0
      · exact ⟨a + (1 : E) • b, by rwa [add, k', mul_zero, add_zero], by rwa [add, k, map_one, one_mul, zero_add]⟩
      · exact ⟨b, k', hb⟩
    · exact ⟨a, ha, k⟩
  have hn' : form σ J x' x = 0 := by rw [hsk, hn, map_zero, neg_zero]
  set c := -form σ J v v / (2 * form σ J x v) with hc
  have y0 : form σ J (v + c • x) (v + c • x) = 0 := by
    have e : ∀ z, form σ J (v + c • x) z = form σ J v z + c * form σ J x z := fun z => by
      rw [form, add_dotProduct, smul_dotProduct]; rfl
    have s1 : σ (form σ J v v) = -form σ J v v := by rw [← neg_eq_iff_eq_neg, ← hsk]
    have s2 : σ (form σ J x v) ≠ 0 := (map_ne_zero _).2 v1
    rw [add, e, e, h0, hsk v x, hc, map_div₀, map_neg, s1, map_mul, map_ofNat]
    field_simp
    ring
  obtain ⟨g, g1, g2⟩ := witt_step h hJ hd h0 y0 (by rwa [add, h0, mul_zero, add_zero])
  obtain ⟨g', g1', g2'⟩ := witt_step h hJ hd y0 h0' (by
    rw [hsk, add, hn', mul_zero, add_zero]; simpa using v2)
  exact ⟨g' * g, (UG σ J).mul_mem g1' g1, by rw [Units.val_mul, ← Matrix.mulVec_mulVec, g2, g2']⟩

end PositivityTheory.ThKEnd.Grp

end
