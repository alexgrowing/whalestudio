import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.EmbeddingTransposeVectorZero
import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ExistsTorus
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealLift PositivityTheory.ThKG.Loc
open FockH1Action (Mat Ix cPair)
open Formalism.BasicNotions.TH (upq Jm)
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKG.CayleyTransformDarboux

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {R S R₁ S₁ d d₁ : ℕ}

theorem piInf_incV {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (x : Fin n → E) :
    (piInf τ ∘ incV F x) = fun i => τ.1 (x i) := by
  funext i
  simp [incV, piInf, compInf, inclR, infEmb_tmul]

theorem map_mulVec' {w : InfinitePlace F} (τ : EmbOver E w) {n k : ℕ} (M : Matrix (Fin n) (Fin k) (AE F E)) (v : Fin k → AE F E) :
    piInf τ ∘ (M *ᵥ v) = M.map (piInf τ) *ᵥ (piInf τ ∘ v) := funext fun i => RingHom.map_mulVec _ M v i

theorem at_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evI F) (M - 1)) (z : Fin n → AE F E) (i : Fin n) :
    (M *ᵥ z) i - z i ∈ atI F E := by
  have : (M *ᵥ z) i - z i = ((M - 1) *ᵥ z) i := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  rw [this]
  change ∑ j, (M - 1) i j * z j ∈ _
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (at_entry h i j)

structure FD (B : Base F E) (H' : Plane E d d₁) (m : Emb R S R₁ S₁) (C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ)
    (C₁ : InfinitePlace F → Matrix (Fin d₁) (Ix R₁ S₁) ℂ) (n n' : InfinitePlace F → ℂ) : Prop where
  cm : IsCMExt F E σ
  n0 : ∀ w, n w ≠ 0
  hx : ∀ w, (fun i => (B.emb w).1 (H'.x i)) = n w • C w *ᵥ m.x
  hy : ∀ w, (fun i => (B.emb w).1 (H'.y i)) = n' w • C w *ᵥ m.y
  hι : ∀ w, C w * m.P = H'.ι.map (B.emb w).1 * C₁ w
  inv : ∀ w, ∃ A : Matrix (Ix R₁ S₁) (Fin d₁) ℂ, C₁ w * A = 1

variable {B : Base F E} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {m : Emb R S R₁ S₁}
  {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ} {C₁ : InfinitePlace F → Matrix (Fin d₁) (Ix R₁ S₁) ℂ}
  {n n' : InfinitePlace F → ℂ}

theorem gen_vec {γ : Multiplicative ℝ →* UA σ W.J} {Y} (h : IsGen B.emb C γ Y) (s : ℝ) (w) (v : Ix R S → ℂ) :
    (mat (γ (Multiplicative.ofAdd s))).map (piInf (B.emb w)) *ᵥ (C w *ᵥ v) = C w *ᵥ (NormedSpace.exp (s • Y w) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (· *ᵥ v) (h s w)

theorem real_mulVec (s : ℝ) (Y : Mat R S) (v : Ix R S → ℂ) : (s • Y) *ᵥ v = (s : ℂ) • (Y *ᵥ v) := by
  rw [Matrix.smul_mulVec]; rfl

theorem eig_vec (hc : IsCMExt F E σ) {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Y} (h : IsGen B.emb C γ Y) (s : ℝ)
    (x : Fin d → E) (k l : InfinitePlace F → ℂ) (v : Ix R S → ℂ) (hx : ∀ w, (fun i => (B.emb w).1 (x i)) = k w • C w *ᵥ v)
    (hY : ∀ w, Y w *ᵥ v = l w • v) (t : AE F E) (ht : t - 1 ∈ atI F E) (ht' : ∀ w, piInf (B.emb w) t = Complex.exp (s * l w)) :
    mat (γ (Multiplicative.ofAdd s)) *ᵥ incV F x = t • incV F x := by
  funext i
  refine eq_of_inf hc B.emb ?_ fun w => ?_
  · have := sub_mem (at_mulVec (hγ.2 (Multiplicative.ofAdd s)) (incV F x) i) (Ideal.mul_mem_right (incV F x i) _ ht)
    rwa [sub_mul, one_mul, sub_sub_sub_cancel_right] at this
  · have e := map_mulVec' (B.emb w) (mat (γ (Multiplicative.ofAdd s))) (incV F x)
    rw [piInf_incV, hx, Matrix.mulVec_smul, gen_vec h,
      exp_eig (c := s * l w) (by rw [real_mulVec, hY, smul_smul]), Matrix.mulVec_smul, smul_comm, ← hx] at e
    refine (congrFun e i).trans ?_
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, ht']
    exact congrArg _ (congrFun (piInf_incV (B.emb w) x) i).symm

theorem FD.iota (h : FD (σ := σ) B H' m C C₁ n n') (w) (z : Fin d₁ → ℂ) :
    ∃ u, z = C₁ w *ᵥ u ∧ H'.ι.map (B.emb w).1 *ᵥ z = C w *ᵥ (m.P *ᵥ u) := by
  obtain ⟨A, hA⟩ := h.inv w
  refine ⟨A *ᵥ z, by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec], ?_⟩
  rw [Matrix.mulVec_mulVec, h.hι, Matrix.mulVec_mulVec, Matrix.mul_assoc, hA, Matrix.mul_one]

theorem FD.levi (h : FD (σ := σ) B H' m C C₁ n n') {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Y}
    (hg : IsGen B.emb C γ Y) {γ₁ : Multiplicative ℝ →* UA σ W₁.J} (hγ₁ : γ₁ ∈ Lines σ W₁) {Y₁} (hg₁ : IsGen B.emb C₁ γ₁ Y₁)
    {l : InfinitePlace F → ℂ} (h1 : ∀ w, Y w *ᵥ m.x = l w • m.x) (h2 : ∀ w, Y w *ᵥ m.y = (-star (l w)) • m.y)
    (h3 : ∀ w, Y w * m.P = m.P * Y₁ w) (s : ℝ) (t : (AE F E)ˣ) (ht : (t : AE F E) - 1 ∈ atI F E)
    (ht' : ∀ w, piInf (B.emb w) t = Complex.exp (s * l w)) :
    IsLevi H' t (γ₁ (Multiplicative.ofAdd s)) (γ (Multiplicative.ofAdd s)) := by
  refine ⟨eig_vec h.cm hγ hg s _ _ _ _ h.hx h1 _ ht ht', eig_vec h.cm hγ hg s _ _ _ _ h.hy h2 _ ?_ fun w => ?_, ?_⟩
  · have := at_cA (σ := σ) (inv_at ht)
    rwa [map_sub, map_one] at this
  · have h3 := congrArg (piInf (B.emb w)) t.mul_inv
    rw [map_mul, ht', map_one] at h3
    rw [piInf_cA h.cm, eq_inv_of_mul_eq_one_right h3, ← Complex.exp_neg]
    refine (Complex.exp_conj _).symm.trans ?_
    simp
  · refine Matrix.ext_iff_mulVec.2 fun z => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    funext i
    refine eq_of_inf h.cm B.emb ?_ fun w => ?_
    · have a1 := at_mulVec (hγ.2 (Multiplicative.ofAdd s)) (incM F H'.ι *ᵥ z) i
      have a2 : (incM F H'.ι *ᵥ (mat (γ₁ (Multiplicative.ofAdd s)) *ᵥ z - z)) i ∈ atI F E := by
        change ∑ j, incM F H'.ι i j * (mat (γ₁ (Multiplicative.ofAdd s)) *ᵥ z - z) j ∈ _
        exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (at_mulVec (hγ₁.2 (Multiplicative.ofAdd s)) z j)
      have := sub_mem a1 a2
      rwa [Matrix.mulVec_sub, Pi.sub_apply, sub_sub_sub_cancel_right] at this
    · refine congrFun (?_ : piInf (B.emb w) ∘ _ = piInf (B.emb w) ∘ _) i
      obtain ⟨u, e1, e2⟩ := h.iota w (piInf (B.emb w) ∘ z)
      rw [map_mulVec', map_mulVec', map_mulVec', map_mulVec', incM_map, e2, gen_vec hg, e1, gen_vec hg₁,
        exp_int (B := s • Y₁ w) (by rw [Matrix.smul_mul, h3, Matrix.mul_smul]), Matrix.mulVec_mulVec _ (C w), h.hι,
        ← Matrix.mulVec_mulVec]

theorem FD.unip (h : FD (σ := σ) B H' m C C₁ n n') {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Y}
    (hg : IsGen B.emb C γ Y) (h1 : ∀ w, Y w *ᵥ m.x = 0) (h2 : ∀ w u, ∃ a : ℂ, Y w *ᵥ (m.P *ᵥ u) = a • m.x) (s) :
    γ s ∈ unip σ W H' := by
  obtain ⟨s, rfl⟩ := Multiplicative.ofAdd.surjective s
  refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
  · have := eig_vec h.cm hγ hg s _ _ 0 m.x h.hx (fun w => by simp [h1]) 1 (by simp) fun w => by simp
    rwa [one_smul] at this
  · choose u e1 e2 using fun w => h.iota w (piInf (B.emb w) ∘ z)
    choose a ha using fun w => h2 w (u w)
    obtain ⟨b, hb, hb'⟩ := exists_inf h.cm B.emb fun w => s * a w / n w
    refine ⟨b, funext fun i => eq_of_inf h.cm B.emb ?_ fun w => ?_⟩
    · have := sub_mem (at_mulVec (hγ.2 (Multiplicative.ofAdd s)) (incM F H'.ι *ᵥ z) i)
        (Ideal.mul_mem_right (incV F H'.x i) (atI F E) hb)
      rwa [sub_sub] at this
    · have e3 := map_mulVec' (B.emb w) (mat (γ (Multiplicative.ofAdd s))) (incM F H'.ι *ᵥ z)
      have e4 := map_mulVec' (B.emb w) (incM F H'.ι) z
      rw [incM_map, e2] at e4
      rw [e4, gen_vec hg, exp_nil (by rw [real_mulVec, real_mulVec, ha, smul_smul, Matrix.mulVec_smul, h1]; simp), real_mulVec,
        ha, Matrix.mulVec_add, ← e4] at e3
      refine (congrFun e3 i).trans ?_
      have e5 := congrFun ((piInf_incV (B.emb w) H'.x).trans (h.hx w)) i
      have := h.n0 w
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at e5
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hb', e5, Matrix.mulVec_smul, Function.comp_apply]
      field_simp

theorem single_prop {ι A A' : Type} [DecidableEq ι] [Zero A] [Zero A'] (P : A → A' → Prop) (w : ι) {a : A} {a' : A'} (h : P a a')
    (h0 : P 0 0) (i : ι) : P ((Pi.single w a : ι → A) i) ((Pi.single w a' : ι → A') i) := by
  by_cases e : i = w
  · subst e; simpa using h
  · simpa [Pi.single_eq_of_ne e] using h0

theorem core (hD : Dic) {a a' a₁ a₁' : ℕ} {G : Geo σ a a'} {G₁ : Geo σ a₁ a₁'} {X : Chars F E} {om om' om₁ om₁'}
    {Rm : RealMaps F a a'} {Rm₁ : RealMaps F a₁ a₁'} (hT : IsTriple B G X om om') (hR : IsRealMaps B G om om' Rm)
    (hT₁ : IsTriple B G₁ X om₁ om₁') (hR₁ : IsRealMaps B G₁ om₁ om₁' Rm₁) {H' : Plane E (a + a') (a₁ + a₁')} {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B G.W G₁.W i₀ i₁) (m : Emb (a₁ + a₁' - (G₁.p + G₁.q) + 1) (G₁.p + G₁.q + 1)
      (a₁ + a₁' - (G₁.p + G₁.q)) (G₁.p + G₁.q)) (hs : ∀ b, sg (m.e b) = sg b) (hy : G₁.p + G₁.q + 1 = G.p + G.q)
    (hΛ : ∀ w b, lamW B (a - G.p) G.p _ _ w (m.e b) = lamW B (a₁ - G₁.p) G₁.p _ _ w b) {χ : Chr F E} {k} (hχ : HasExp B.emb χ k)
    (r : ℝ) {lam lam' : Rm.Pi →ₗ[ℂ] Rm₁.Pi} (h : IsArchimedeanLocalEquivariantMap B G.M G₁.M om om₁ H' χ r Rm.p Rm₁.p lam)
    (h' : IsArchimedeanLocalEquivariantMap B G.M G₁.M om om₁ H' χ r Rm.p Rm₁.p lam') (h0 : lam ≠ 0) : ∃ c : ℂ, lam' = c • lam := by
  have hc := hT.base.cm
  have rk := hH.rank
  have b1 := hT₁.geo.aBig
  choose C₁ hC₁ hθ₁ using fun w => hD.frame _ _ _ _ _ (hT₁.geo.hW.sig w) (hT₁.geo.hW.cartan w)
  have fm : ∀ (w) (x y : Fin (a + a') → E), hf (Complex.I • G.W.J.map (B.emb w).1) (fun i => (B.emb w).1 (x i))
      (fun i => (B.emb w).1 (y i)) = Complex.I * (B.emb w).1 (form σ G.W.J x y) := fun w x y => by
    simp only [hf, form, dotProduct, Matrix.mulVec, map_sum, map_mul, hc.2.2.2, Finset.mul_sum, Matrix.smul_apply,
      Matrix.map_apply, Pi.star_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [Complex.star_def]; ring
  have col : ∀ j, H'.ι *ᵥ Pi.single j 1 = fun r => H'.ι r j := fun j => Matrix.mulVec_single_one _ _
  choose c' c0' hcy using fun w => (hH.cartan w).2
  have ex := fun w => exists_frame m hs (d := a + a') (by omega) (M := Complex.I • G.W.J.map (B.emb w).1)
      (fun i j => by
        simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul']
        rw [← hc.2.2.2, hT.geo.hW.skew, Complex.star_def, Complex.conj_I, map_neg, neg_mul_neg])
      (hT.geo.hW.cartan w) (x := fun i => (B.emb w).1 (H'.x i)) (y := fun i => (B.emb w).1 (H'.y i))
      (ι := H'.ι.map (B.emb w).1)
      (fun e => by
        have := fm w H'.x H'.y
        rw [e, hH.xy] at this
        rw [map_one, mul_one, hf, zero_dotProduct] at this
        exact Complex.I_ne_zero this.symm)
      (by rw [fm, hH.xx]; simp) (c0' w) (hcy w)
      (fun j => by
        have := fm w (H'.ι *ᵥ Pi.single j 1) H'.x
        rw [(hH.orth _).1, col] at this
        simpa using this)
      (fun j => by
        have := fm w (H'.ι *ᵥ Pi.single j 1) H'.y
        rw [(hH.orth _).2, col] at this
        simpa using this)
      (by
        rw [← hH.gram, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_map]
        congr 2
        ext i j
        exact (hc.2.2.2 _ _).symm)
      (hH.cartan w).1 (hC₁ w) (hθ₁ w)
  choose C n n' hC hθ n0 hx hy' hι using ex
  have fd : FD (σ := σ) B H' m C C₁ n n' := ⟨hc, n0, hx, hy', hι, fun w => (hC₁ w).2⟩
  have hC' : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by rw [incM_map]; exact hC w
  have hC₁' : ∀ w, IsFrame (Complex.I • (incM F G₁.W.J).map (piInf (B.emb w))) (C₁ w) := fun w => by
    rw [incM_map]; exact hC₁ w
  obtain ⟨act, f, hM, ha⟩ := exists_mod hD hT hR (by omega) hy C hC' hθ
  obtain ⟨act₁, f₁, hM₁, ha₁⟩ := exists_mod hD hT₁ hR₁ (by omega) rfl C₁ hC₁' hθ₁
  have tor := fun l => exists_torus hc B.emb l χ hχ r
  choose t c ht hd using tor
  have onto : ∀ v : Rm.Pi, ∃ f ∈ G.M.Pol B.ψ B.emb, Rm.p f = v := fun v => (hR.quot.onto ▸ Submodule.mem_top : v ∈ _)
  have onto₁ : ∀ v : Rm₁.Pi, ∃ f ∈ G₁.M.Pol B.ψ B.emb, Rm₁.p f = v := fun v => (hR₁.quot.onto ▸ Submodule.mem_top : v ∈ _)
  have c0 : c 0 = 0 := by
    refine (hd 0).unique ?_
    have : ∀ s, t 0 s = 1 := fun s => Units.ext (eq_of_inf hc B.emb (ht 0 s).1 fun w => by simp [(ht 0 s).2])
    simp only [this]
    exact hasDerivAt_const _ _
  have ij : (Sum.inl m.i : Ix _ _) ≠ Sum.inr m.j := Sum.inl_ne_inr
  have par : ∀ D : Rm.Pi →ₗ[ℂ] Rm₁.Pi, IsArchimedeanLocalEquivariantMap B G.M G₁.M om om₁ H' χ r Rm.p Rm₁.p D →
      IsPar m act act₁ (fun w => -Complex.I * c (Pi.single w Complex.I)) (fun w => c (Pi.single w 1)) D := by
    intro D hP
    have L : ∀ Y Y₁ l, (∀ w, Y w ∈ upq _ _) → (∀ w, Y₁ w ∈ upq _ _) → (∀ w, Y w *ᵥ m.x = l w • m.x) →
        (∀ w, Y w *ᵥ m.y = (-star (l w)) • m.y) → (∀ w, Y w * m.P = m.P * Y₁ w) →
        ∀ v, D (act Y v) = c l • D v + act₁ Y₁ (D v) := by
      intro Y Y₁ l u1 u2 h1 h2 h3 v
      obtain ⟨γ, hγ, hg⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C hc hC' Y u1
      obtain ⟨γ₁, hγ₁, hg₁⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C₁ hc hC₁' Y₁ u2
      obtain ⟨g, hg0, rfl⟩ := onto v
      obtain ⟨g₁, hg₁0, e⟩ := onto₁ (D (Rm.p g))
      obtain ⟨g', q1, q2⟩ := ha γ hγ Y hg g hg0
      obtain ⟨g₁', q3, q4⟩ := ha₁ γ₁ hγ₁ Y₁ hg₁ g₁ hg₁0
      rw [← q2, ← e, ← q4]
      exact hP.levi γ hγ γ₁ hγ₁ (t l) (fun s => fd.levi hγ hg hγ₁ hg₁ h1 h2 h3 s _ (ht l s).1 (ht l s).2) _ (hd l) g hg0 g₁ hg₁0
        g' g₁' q1 q3 e.symm
    have U : ∀ w Y, Y ∈ upq _ _ → Y *ᵥ m.x = 0 → (∀ u, ∃ a : ℂ, Y *ᵥ (m.P *ᵥ u) = a • m.x) →
        ∀ v, D (act (Pi.single w Y) v) = 0 := by
      intro w Y u1 h1 h2 v
      obtain ⟨γ, hγ, hg⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C hc hC' _ (single_upq w u1)
      obtain ⟨g, hg0, rfl⟩ := onto v
      obtain ⟨g', q1, q2⟩ := ha γ hγ _ hg g hg0
      rw [← q2]
      exact hP.unip γ hγ (fd.unip hγ hg (single_prop (fun Z (_ : ℂ) => Z *ᵥ m.x = 0) w (a' := 0) h1 (by simp))
        (single_prop (fun Z (_ : ℂ) => ∀ u, ∃ a : ℂ, Z *ᵥ (m.P *ᵥ u) = a • m.x) w (a' := 0) h2 fun u => ⟨0, by simp⟩)) g hg0 g' q1
    have T : ∀ w Y (l : ℂ), Y ∈ upq _ _ → Y *ᵥ m.x = l • m.x → Y *ᵥ m.y = (-star l) • m.y → (∀ u, Y *ᵥ (m.P *ᵥ u) = 0) →
        ∀ v, D (act (Pi.single w Y) v) = c (Pi.single w l) • D v := by
      intro w Y l u1 h1 h2 h3 v
      have := L (Pi.single w Y) 0 (Pi.single w l) (single_upq w u1) (fun _ => zero_upq _ _)
        (single_prop (fun Z (l : ℂ) => Z *ᵥ m.x = l • m.x) w h1 (by simp))
        (single_prop (fun Z (l : ℂ) => Z *ᵥ m.y = (-star l) • m.y) w h2 (by simp))
        (fun i => Matrix.ext_iff_mulVec.2 fun u => by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Pi.zero_apply, Matrix.zero_mulVec, Matrix.mulVec_zero]
          exact single_prop (fun Z (_ : ℂ) => Z *ᵥ (m.P *ᵥ u) = 0) w (a' := 0) (h3 u) (Matrix.zero_mulVec _) i) v
      simpa using this
    have xi : m.x (.inl m.i) = 1 ∧ m.x (.inr m.j) = 1 ∧ m.y (.inl m.i) = 1 ∧ m.y (.inr m.j) = -1 ∧ ∀ b, m.x (m.e b) = 0 := by
      simp [Emb.x, Emb.y, Pi.single_eq_of_ne (m.ne_i _), Pi.single_eq_of_ne (m.ne_j _)]
    have N : ∀ w b (s : ℂ) v, s • D (act (un w (m.e b) (.inl m.i) - un w (m.e b) (.inr m.j)) v) -
        (star s * sg (m.e b)) • D (act (un w (.inl m.i) (m.e b) + un w (.inr m.j) (m.e b)) v) = 0 := fun w b s v => by
      have := U w (s • (Matrix.single (m.e b) (.inl m.i) 1 - Matrix.single (m.e b) (.inr m.j) 1) -
          (star s * sg (m.e b)) • (Matrix.single (.inl m.i) (m.e b) 1 + Matrix.single (.inr m.j) (m.e b) 1))
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
            Matrix.conjTranspose_single, star_one, star_mul', star_star, star_sg, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
            Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, J_single, single_J, sg_l, sg_r]
          module)
        (by simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp)
        (fun u => ⟨-(star s * sg (m.e b) * u b), by
          simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', m.embeddingMatrix_mulVec, Emb.x]
          module⟩) v
      simpa only [Pi.single_sub, Pi.single_smul, Pi.single_add, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        un, map_add, LinearMap.add_apply] using this
    have sg0 : ∀ b, sg (m.e b) ≠ 0 := fun b e => by simpa [e] using sg_sq (m.e b)
    refine ⟨fun w a b v => ?_, fun w v => ?_, fun w v => ?_, fun w v => ?_, fun w b v => ?_, fun w b v => ?_⟩
    · have key : ∀ Y : Mat _ _, D (act (Pi.single w (m.P * Y * m.Pᵀ)) v) = act₁ (Pi.single w Y) (D v) := by
        have k1 : ∀ Y ∈ upq _ _, D (act (Pi.single w (m.P * Y * m.Pᵀ)) v) = act₁ (Pi.single w Y) (D v) := fun Y hY => by
          have := L (Pi.single w (m.P * Y * m.Pᵀ)) (Pi.single w Y) 0 (single_upq w (m.conj_upq hs hY)) (single_upq w hY)
            (single_prop (fun Z (_ : ℂ) => Z *ᵥ m.x = (0 : ℂ) • m.x) w (a' := 0)
              (by rw [← Matrix.mulVec_mulVec, m.embedding_transpose_vector_zero]; simp) (by simp))
            (single_prop (fun Z (_ : ℂ) => Z *ᵥ m.y = (-star (0 : ℂ)) • m.y) w (a' := 0)
              (by rw [← Matrix.mulVec_mulVec, m.transpose_mulVec_y_eq_zero]; simp) (by simp))
            (single_prop (fun Z Z₁ => Z * m.P = m.P * Z₁) w (by rw [Matrix.mul_assoc, m.tPP, Matrix.mul_one]) (by simp)) v
          rwa [c0, zero_smul, zero_add] at this
        intro Y
        obtain ⟨Y₁, h₁, Y₂, h₂, rfl⟩ := upq_split Y
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Pi.single_add, Pi.single_smul, map_add,
          map_smul, LinearMap.add_apply, LinearMap.smul_apply, k1 _ h₁, k1 _ h₂]
      have := key (Matrix.single a b 1)
      rwa [m.conj_single] at this
    · have := T w (Complex.I • (Matrix.single (.inl m.i) (.inl m.i) 1 + Matrix.single (.inr m.j) (.inr m.j) 1)) Complex.I
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
            Matrix.conjTranspose_single, star_one, Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.smul_mul,
            Matrix.mul_add, Matrix.mul_smul, J_single, single_J, sg_l, sg_r, map_one]
          module)
        (by simp only [Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp [Emb.x])
        (by simp only [Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp [Emb.y, sub_eq_add_neg])
        (fun u => by simp only [Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', m.embeddingMatrix_mulVec]; simp) v
      rw [Pi.single_smul, map_smul, LinearMap.smul_apply, map_smul, Pi.single_add] at this
      rw [mul_smul, ← this, smul_smul]
      simp [un]
    · have := T w (Matrix.single (.inl m.i) (.inr m.j) 1 + Matrix.single (.inr m.j) (.inl m.i) 1) 1
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_single, star_one, Matrix.add_mul,
            Matrix.mul_add, J_single, single_J, sg_l, sg_r]
          module)
        (by simp only [Matrix.add_mulVec, single_mulVec', xi]; simp [Emb.x])
        (by simp only [Matrix.add_mulVec, single_mulVec', xi]; simp [Emb.y, neg_add_eq_sub])
        (fun u => by simp only [Matrix.add_mulVec, single_mulVec', m.embeddingMatrix_mulVec]; simp) v
      rwa [Pi.single_add] at this
    · have := U w (Complex.I • (Matrix.single (.inl m.i) (.inl m.i) 1 - Matrix.single (.inl m.i) (.inr m.j) 1 +
          Matrix.single (.inr m.j) (.inl m.i) 1 - Matrix.single (.inr m.j) (.inr m.j) 1))
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
            Matrix.conjTranspose_single, star_one, Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.smul_mul,
            Matrix.mul_add, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, J_single, single_J, sg_l, sg_r, map_one]
          module)
        (by simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp)
        (fun u => ⟨0, by simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, single_mulVec', m.embeddingMatrix_mulVec]; simp⟩) v
      rw [Pi.single_smul, map_smul, LinearMap.smul_apply, map_smul, Pi.single_sub, Pi.single_add, Pi.single_sub,
        smul_eq_zero] at this
      exact this.resolve_left Complex.I_ne_zero
    · have a1 := N w b 1 v
      have a2 := N w b Complex.I v
      rw [Complex.star_def, Complex.conj_I] at a2
      rw [star_one] at a1
      have : (2 * Complex.I) • D (act (un w (m.e b) (.inl m.i) - un w (m.e b) (.inr m.j)) v) = 0 := by
        linear_combination (norm := module) Complex.I • a1 + a2
      exact (smul_eq_zero.1 this).resolve_left (by simp)
    · have a1 := N w b 1 v
      have a2 := N w b Complex.I v
      rw [Complex.star_def, Complex.conj_I] at a2
      rw [star_one] at a1
      have : (2 * Complex.I * sg (m.e b)) • D (act (un w (.inl m.i) (m.e b) + un w (.inr m.j) (m.e b)) v) = 0 := by
        linear_combination (norm := module) a2 - Complex.I • a1
      exact (smul_eq_zero.1 this).resolve_left (by simp [sg0])
  exact par_line hM hM₁ (fun w b => congrArg _ (hΛ w b)) (par _ h) (par _ h') h0

theorem archimedean_multiplicity_one_of (hD : Dic) : ArchimedeanMultiplicityOne := by
  intro F E _ _ _ _ _ σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' i₀ i₁ χ r hM hM₁ hS hH lam lam' h h' h0
  have b1 := hM₁.triple.geo.aBig
  have b2 := hM₁.triple.geo.eBig
  rcases hS with ⟨rfl, e1, e2, e3, rfl, rfl⟩ | ⟨e0, rfl, e2, e3, rfl, rfl⟩
  · refine core hD hM.triple hM.real hM₁.triple hM₁.real hH (embB _ _) (sg_embB _ _) (by omega) ?_ hM.triple.chars.expβ _ h h' h0
    rintro w (b | b) <;> simp [lamW, embB, e2, FockH1Action.cPair]
  · refine core hD hM.triple hM.real hM₁.triple hM₁.real hH (embA _ _) (sg_embA _ _) (by omega) ?_ hM.triple.chars.expα _ h h' h0
    have e4 : a - G.p = a₁ - G₁.p + 1 := by omega
    rw [e4, ← e2]
    rintro w (b | b) <;> simp [lamW, embA, FockH1Action.cPair]

end PositivityTheory.ThKG.CayleyTransformDarboux

end
