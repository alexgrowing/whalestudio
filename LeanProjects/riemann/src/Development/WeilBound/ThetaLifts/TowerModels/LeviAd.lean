import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration
import Development.WeilBound.ThetaLifts.TowerModels.LeviAlg
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

noncomputable section

namespace PositivityTheory.ThKG.Tow.Levi

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open Classical in

def sgI (w : InfinitePlace F) : w.Completion →ₗ[F] AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).comp (LinearMap.single F (fun u : InfinitePlace F => u.Completion) w)

omit [NumberField E] in
theorem compInf_sgI_self (w : InfinitePlace F) (y : w.Completion ⊗[F] E) :
    compInf F E w (TensorProduct.map (sgI w) LinearMap.id y) = y := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact congrArg (· ⊗ₜ[F] x) (Pi.single_eq_same (M := fun u : InfinitePlace F => u.Completion) w a)
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in
theorem compInf_sgI_ne {w u : InfinitePlace F} (h : u ≠ w) (y : w.Completion ⊗[F] E) :
    compInf F E u (TensorProduct.map (sgI w) LinearMap.id y) = 0 := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    exact (congrArg (· ⊗ₜ[F] x) (Pi.single_eq_of_ne (M := fun u : InfinitePlace F => u.Completion) h a)).trans
      (TensorProduct.zero_tmul _ _)
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

omit [NumberField E] in
theorem compFin_sgI (w : InfinitePlace F) (v : Pl F) (y : w.Completion ⊗[F] E) :
    compFin F E v (TensorProduct.map (sgI w) LinearMap.id y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    exact (congrArg (· ⊗ₜ[F] x) (map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v))).trans (TensorProduct.zero_tmul _ _)
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem exists_inf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → ℂ) :
    ∃ a : AE F E, (∀ w, piInf (τ w) a = z w) ∧ ∀ v, compFin F E v a = 1 := by
  choose b hb using fun w => (infEmb_bijective h (τ w)).2 (z w - 1)
  refine ⟨1 + ∑ w, TensorProduct.map (sgI w) LinearMap.id (b w), fun w => ?_, fun v => ?_⟩
  · rw [map_add, map_one, piInf, RingHom.comp_apply, map_sum, Finset.sum_eq_single w (fun u _ hu => compInf_sgI_ne hu.symm _)
      (fun h => absurd (Finset.mem_univ w) h), compInf_sgI_self, hb, add_sub_cancel]
  · simp [map_sum, compFin_sgI]

theorem ad_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {a b : AE F E}
    (h1 : ∀ w, piInf (τ w) a = piInf (τ w) b) (h2 : ∀ v, compFin F E v a = compFin F E v b) : a = b :=
  Supp.adTens_ext (fun w => (infEmb_bijective h (τ w)).1 (h1 w)) h2

theorem mat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m n : Type} {a b : Matrix m n (AE F E)}
    (h1 : ∀ w, a.map (piInf (τ w)) = b.map (piInf (τ w))) (h2 : ∀ v, a.map (compFin F E v) = b.map (compFin F E v)) : a = b :=
  Matrix.ext fun i j => ad_ext h τ (fun w => congrFun (congrFun (h1 w) i) j) fun v => congrFun (congrFun (h2 v) i) j

theorem exists_inf_mat (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {n : Type} [DecidableEq n]
    (z : InfinitePlace F → Matrix n n ℂ) :
    ∃ a : Matrix n n (AE F E), (∀ w, a.map (piInf (τ w)) = z w) ∧ ∀ v, a.map (compFin F E v) = 1 := by
  choose a h1 h2 using fun i j => exists_inf h τ fun w => z w i j + 1 - (1 : Matrix n n ℂ) i j
  refine ⟨Matrix.of fun i j => a i j - 1 + (1 : Matrix n n (AE F E)) i j, fun w => ?_, fun v => ?_⟩
  · ext i j
    by_cases e : i = j <;> simp [h1, Matrix.one_apply, e]
  · refine Matrix.ext fun i j => ?_
    by_cases e : i = j <;> simp [h2, Matrix.one_apply, e]

omit [NumberField E] in
theorem piInf_incl {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, compInf, inclR, infEmb_tmul]

omit [NumberField E] in
theorem compFin_cA (v : Pl F) (z : AE F E) : compFin F E v (cA σ z) = sigR _ σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  refine Eq.trans (congrArg (infEmb τ) ?_) (infEmb_sigR h τ _).symm
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem cA_cA (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sig_sig h x)
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in
theorem iso_map_piInf (hc : ∀ {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E), piInf τ (cA σ z) = star (piInf τ z))
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (AE F E)) {w : InfinitePlace F} (τ : EmbOver E w) :
    (gᵀ * incM F J * g.map (cA σ)).map (piInf τ) = (g.map (piInf τ))ᵀ * J.map τ.1 * (g.map (piInf τ)).map star := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 1
  · congr 1
    exact Matrix.ext fun i j => piInf_incl τ _
  · exact Matrix.ext fun i j => hc τ _

omit [NumberField E] in
theorem exists_UA {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g g' : Matrix (Fin n) (Fin n) (AE F E)} (h1 : g * g' = 1)
    (h2 : gᵀ * incM F J * g.map (cA σ) = incM F J) : ∃ p : UA σ J, mat p = g :=
  ⟨⟨⟨g, g', h1, mul_eq_one_comm.1 h1⟩, h2⟩, rfl⟩

theorem exists_lift (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g g' : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) (h1 : ∀ w, g w * g' w = 1)
    (h2 : ∀ w, (g w)ᵀ * J.map (τ w).1 * (g w).map star = J.map (τ w).1) :
    ∃ p : UA σ J, (∀ w, (mat p).map (piInf (τ w)) = g w) ∧ ∀ v, (mat p).map (compFin F E v) = 1 := by
  obtain ⟨a, a1, a2⟩ := exists_inf_mat h τ g
  obtain ⟨b, b1, b2⟩ := exists_inf_mat h τ g'
  obtain ⟨p, hp⟩ := exists_UA (σ := σ) (J := J) (g := a) (g' := b)
    (mat_ext h τ (fun w => by rw [Matrix.map_mul, a1, b1, h1, Matrix.map_one _ (map_zero _) (map_one _)])
      fun v => by rw [Matrix.map_mul, a2, b2, mul_one, Matrix.map_one _ (map_zero _) (map_one _)])
    (mat_ext h τ (fun w => by
        rw [iso_map_piInf (fun τ z => piInf_cA h τ z), a1, h2]
        exact Matrix.ext fun i j => (piInf_incl _ _).symm)
      fun v => by
        have e : (a.map (cA σ)).map (compFin F E v) = (a.map (compFin F E v)).map (sigR _ σ) :=
          Matrix.ext fun i j => compFin_cA v _
        rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, a2, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.transpose_one, one_mul, mul_one])
  exact ⟨p, hp ▸ a1, hp ▸ a2⟩

variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ r s : ℕ}

theorem det_ne_zero (hW : W.IsSkew σ B r s) : W.J.det ≠ 0 := by
  obtain ⟨u⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro h0
  have hm : (Complex.I • W.J.map (B.emb u).1).det = 0 := by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hm
  have := (hW.cartan u).2.2 (star x) (by simpa using hx)
  rw [star_star, e, dotProduct_zero] at this
  exact lt_irrefl _ this

omit [NumberField F] [NumberField E] in
theorem form_skew (hs : ∀ x, σ (σ x) = x) {J : Matrix (Fin d) (Fin d) E} (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin d → E) :
    form σ J x y = -σ (form σ J y x) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, hs, hJ, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem isFr (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) :
    IsFr (σ : E →+* E) W.J W₁.J H.ι H.x H.y := by
  have hsk := form_skew (sig_sig hB.cm) hW.skew
  have ent : ∀ a b, ((fr H.ι H.x H.y)ᵀ * W.J * (fr H.ι H.x H.y).map (σ : E →+* E)) a b =
      form σ W.J (fun i => fr H.ι H.x H.y i a) (fun i => fr H.ι H.x H.y i b) := fun a b => by
    rw [Matrix.mul_assoc]; rfl
  have col : ∀ j, (fun i => fr H.ι H.x H.y i (Sum.inl j)) = H.ι *ᵥ Pi.single j 1 := fun j => by
    ext i; simp [fr]
  have c0 : (fun i => fr H.ι H.x H.y i (Sum.inr 0)) = H.x := rfl
  have c1 : (fun i => fr H.ι H.x H.y i (Sum.inr 1)) = H.y := rfl
  refine ⟨?_, ?_⟩
  · ext (a | a) (b | b)
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
  · have hs : ∀ z : Fin d → E, z ∈ LinearMap.range (Matrix.toLin' (fr H.ι H.x H.y)) := fun z => by
      have hz : z ∈ Submodule.span E (W.L : Set (Fin d → E)) := by rw [hW.lat.span_eq_top]; trivial
      refine (Submodule.span_le.2 fun z hz => ?_) hz
      obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
      refine ⟨Sum.elim u ![s, t], ?_⟩
      rw [Matrix.toLin'_apply, fr, Matrix.fromCols_mulVec_sumElim]
      ext i
      simp [Matrix.mulVec, dotProduct]
      ring
    choose f hf using fun j => hs (Pi.single j 1)
    have h1 : fr H.ι H.x H.y * (Matrix.of fun a j => f j a) = 1 := by
      ext i j
      rw [Matrix.one_apply, ← Pi.single_apply, ← hf j]; rfl
    exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hH.rank])).1 h1⟩

theorem isFrA (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) :
    IsFr (cA σ : AE F E →+* AE F E) (incM F W.J) (incM F W₁.J) (incM F H.ι) (incV F H.x) (incV F H.y) :=
  (isFr hB hW hH).map (inclR (F := F) (AF F)) fun _ => rfl

theorem exists_levi (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) (t : (AE F E)ˣ)
    (h₁ : UA σ W₁.J) : ∃ m : UA σ W.J, IsLevi H t h₁ m := by
  obtain ⟨m, m', e1, e2, e3, e4, e5⟩ := (isFrA hB hW hH).levi (cA_cA hB.cm) t.mul_inv h₁.1.mul_inv h₁.2
  obtain ⟨p, rfl⟩ := exists_UA e1 e2
  exact ⟨p, e3, e4, e5⟩

end PositivityTheory.ThKG.Tow.Levi

end
