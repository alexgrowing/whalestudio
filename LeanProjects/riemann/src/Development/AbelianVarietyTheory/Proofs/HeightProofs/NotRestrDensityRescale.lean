import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FrameNormRestrictedDensity
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjCmHostRootNeSelf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LowerBoundCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity

variable {D : D7} {T : Core D}

theorem conjEmb_invol {E : Type} [Field E] (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x
  simp [conjEmb]

theorem wtA_conj_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  have h1 : ∀ t', conjEmb (DV.tauEmb D t) ≠ DV.tauEmb D t' := fun t' h =>
    GlobalTheory.LeafCompare.tauEmb_ne_conj Q hp t' t h.symm
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [h1]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h =>
      ht' (GlobalTheory.LeafCompare.tauEmb_inj (by
        rw [← conjEmb_invol (DV.tauEmb D t'), ← h, conjEmb_invol]))
    simp [h1, this]
  · simp

theorem wt_ext (Q : Par D) (hp : Q.PinHost) {j : ℕ} {w w' : WeightFamilies.Wt D j} (hA : wtA w = wtA w') (hn : w.n = w'.n) :
    w = w' := by
  have hP : w.aP = w'.aP := by
    funext t i
    have := congrFun hA (DV.tauEmb D t, i.1)
    rw [GlobalTheory.LeafCompare.wtA_tau Q hp, GlobalTheory.LeafCompare.wtA_tau Q hp] at this
    simpa [ext0, i.2] using this
  have hM : w.aM = w'.aM := by
    funext t i
    have := congrFun hA (conjEmb (DV.tauEmb D t), i.1)
    rw [wtA_conj_tau Q hp, wtA_conj_tau Q hp] at this
    simpa [ext0, i.2] using this
  cases w
  cases w'
  simp only at hP hM hn
  subst hP hM hn
  rfl

theorem wtA_wsmul_apply {j : ℕ} (k : ℕ) (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA (WeightAlgebra.wsmul k w) x = k * wtA w x := by
  have h0 : ∀ {p : ℕ} (f : Fin p → ℕ) (i : ℕ), ext0 (fun s => k * f s) i = k * ext0 f i := by
    intro p f i
    unfold ext0
    split_ifs <;> simp
  simp only [wtA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((WeightAlgebra.wsmul k w).aP t) x.2 = k * ext0 (w.aP t) x.2 := h0 _ _
  have h2 : ext0 ((WeightAlgebra.wsmul k w).aM t) x.2 = k * ext0 (w.aM t) x.2 := h0 _ _
  rw [h1, h2]
  split_ifs <;> simp [mul_add]

theorem eq_wsmul_iff (h : LawsCore T) {j : ℕ} (ka wL : WeightFamilies.Wt D j) (n : ℕ) :
    wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n ↔ ka = WeightAlgebra.wsmul n wL := by
  constructor
  · intro H
    refine wt_ext T.Q h.pins.1 (funext fun x => ?_) ?_
    · have : (wtA ka x : ℤ) = n • (wtA wL x : ℤ) := congrFun (congrArg Prod.fst H) x
      rw [nsmul_eq_mul] at this
      rw [wtA_wsmul_apply]
      exact_mod_cast this
    · have : (ka.n : ℤ) = n • (wL.n : ℤ) := congrArg Prod.snd H
      rw [nsmul_eq_mul] at this
      show ka.n = n * wL.n
      exact_mod_cast this
  · rintro rfl
    refine Prod.ext (funext fun x => ?_) ?_
    · simp only [wtZ, Prod.smul_fst, Pi.smul_apply, nsmul_eq_mul, wtA_wsmul_apply]
      push_cast
      rfl
    · simp only [wtZ, Prod.smul_snd, nsmul_eq_mul]
      show ((n * wL.n : ℕ) : ℤ) = _
      push_cast
      rfl

theorem prod_iff (h : LawsCore T) (j : ℕ) (ka wL : WeightFamilies.Wt D j) {N : ℕ} (w : Fin (N + 1) → T.R j) (n : ℕ)
    (hka : wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n) :
    ProdInLat h j ka w n ↔ ProdInLattice h j wL w n := by
  obtain rfl := (eq_wsmul_iff h ka wL n).1 hka
  exact Iff.rfl

theorem const_iff (large₂ : SizeData₂ D) {j : ℕ} (ka wL : WeightFamilies.Wt D j) (C A P : ℝ) (n : ℕ) :
    LamConst j large₂ C A ka P n wL.size ↔ ConstBound large₂ ka C A P n wL := Iff.rfl

def DensityWith (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j)
    (yP : GenericFrames T j) (ka : WeightFamilies.Wt D j) (R : Comp (T.Q.Xo j) T.Q.c → T.R j → T.R j → Prop) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (F : (recB h).Cusp j ka), F ∈ (recB h).Mlat j ka → evC hG Z (F : T.R j) ≠ 0 →
    ∃ F' ∈ (recB h).Mlat j ka, F' ≠ 0 ∧ R Z (F : T.R j) (F' : T.R j) ∧
      ∀ σ : T.Q.c.F →+* ℂ, (recB h).supN j ka σ F' ≤ genSup hG fn yP ka (F : T.R j) Z σ

section Density

variable (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j) (yP : GenericFrames T j)
  (ka : WeightFamilies.Wt D j)

theorem DensityWith.mono {R R' : Comp (T.Q.Xo j) T.Q.c → T.R j → T.R j → Prop}
    (hR : ∀ Z f f', R Z f f' → R' Z f f') (H : DensityWith h j hG fn yP ka R) : DensityWith h j hG fn yP ka R' := by
  intro Z F hF hZ
  obtain ⟨F', h1, h2, h3, h4⟩ := H Z F hF hZ
  exact ⟨F', h1, h2, hR _ _ _ h3, h4⟩

theorem supPTGe_iff : SupPTGe h j hG fn yP ka ↔ DensityWith h j hG fn yP ka (fun _ _ _ => True) := by
  constructor
  · intro H Z F hF hZ
    obtain ⟨F', h1, h2, h3⟩ := H Z F hF hZ
    exact ⟨F', h1, h2, trivial, h3⟩
  · intro H Z F hF hZ
    obtain ⟨F', h1, h2, -, h3⟩ := H Z F hF hZ
    exact ⟨F', h1, h2, h3⟩

theorem restrDensity_iff : RestrDensity h j hG fn yP ka ↔ DensityWith h j hG fn yP ka (IsRestr hG) := by
  constructor
  · intro H Z F hF hZ
    obtain ⟨F', h1, h2, h3⟩ := H F hF Z hZ
    refine ⟨F', h1, fun h0 => hZ ?_, h2, h3⟩
    have h4 : evC hG Z (F' : T.R j) = evC hG Z (F : T.R j) := h2.1
    rw [← h4, h0]
    exact evC_zero hG Z
  · intro H F hF Z hZ
    obtain ⟨F', h1, -, h2, h3⟩ := H Z F hF hZ
    exact ⟨F', h1, h2, h3⟩

theorem supPTGe_of_restrDensity (H : RestrDensity h j hG fn yP ka) : SupPTGe h j hG fn yP ka :=
  (supPTGe_iff h j hG fn yP ka).2
    (DensityWith.mono h j hG fn yP ka (fun _ _ _ _ => trivial) ((restrDensity_iff h j hG fn yP ka).1 H))

end Density

section Separate

variable {j : ℕ}

def rescale (fn : FrameNorms T j) (a : T.Q.c.F) : FrameNorms T j := fun σ y i =>
  match i with
  | none => fn σ y none / ‖σ a‖
  | some u => fn σ y (some u)

theorem genNorm_rescale (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j) (yP : GenericFrames T j)
    (ka : WeightFamilies.Wt D j) (a : T.Q.c.F) (f : T.R j) (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ) :
    genNorm hG (rescale fn a) yP ka f Z P = ‖sgOf P a‖ ^ ka.n * genNorm hG fn yP ka f Z P := by
  unfold genNorm nrmC
  rw [Fintype.prod_option, Fintype.prod_option]
  have h1 : exZ (T.Q.Dw j) (wtZ (wtA ka) ka.n) none = (ka.n : ℤ) := rfl
  have h2 : |rescale fn a (sgOf P) (yP Z P) none| ^ (-(ka.n : ℤ)) =
      ‖sgOf P a‖ ^ ka.n * |fn (sgOf P) (yP Z P) none| ^ (-(ka.n : ℤ)) := by
    show |fn (sgOf P) (yP Z P) none / ‖sgOf P a‖| ^ (-(ka.n : ℤ)) = _
    rw [abs_div, abs_norm, div_zpow, zpow_neg ‖sgOf P a‖, div_inv_eq_mul, zpow_natCast, mul_comm]
  rw [h1, h2]
  have h3 : ∀ u, rescale fn a (sgOf P) (yP Z P) (some u) = fn (sgOf P) (yP Z P) (some u) := fun _ => rfl
  simp only [h3]
  ring

theorem genSup_rescale (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j) (yP : GenericFrames T j)
    (ka : WeightFamilies.Wt D j) (a : T.Q.c.F) (f : T.R j) (Z : Comp (T.Q.Xo j) T.Q.c) (σ : T.Q.c.F →+* ℂ) :
    genSup hG (rescale fn a) yP ka f Z σ = ‖σ a‖ ^ ka.n * genSup hG fn yP ka f Z σ := by
  unfold genSup
  rw [Real.mul_iSup_of_nonneg (by positivity)]
  refine iSup_congr fun P => ?_
  have hP : sgOf (P : Om Z →+* ℂ) = σ := P.2
  rw [genNorm_rescale, hP]

theorem supPTGe_rescale (h : LawsCore T) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j)
    (yP : GenericFrames T j) (ka : WeightFamilies.Wt D j) (a : 𝓞 T.Q.c.F) (ha : a ≠ 0) (H : SupPTGe h j hG fn yP ka) :
    SupPTGe h j hG (rescale fn (a : T.Q.c.F)) yP ka := by
  rw [supPTGe_iff] at H ⊢
  intro Z F hF hZ
  obtain ⟨F', h1, h2, -, h3⟩ := H Z F hF hZ
  have ha' : (a : T.Q.c.F) ≠ 0 := fun h0 => ha (Subtype.ext h0)
  have hs : ∀ σ : T.Q.c.F →+* ℂ, (recB h).supN j ka σ ((a ^ ka.n) • F') =
      ‖σ (a : T.Q.c.F)‖ ^ ka.n * (recB h).supN j ka σ F' := fun σ => by
    have := (recB h).supN_smul j ka σ ((a : T.Q.c.F) ^ ka.n) F'
    rw [map_pow, norm_pow] at this
    exact this
  refine ⟨(a ^ ka.n) • F', Submodule.smul_mem _ _ h1, fun h0 => h2 ?_, trivial, fun σ => ?_⟩
  · have h4 := hs T.σ₀
    rw [((recB h).supN_eq_zero j ka T.σ₀ _).2 h0] at h4
    have h5 : ‖T.σ₀ (a : T.Q.c.F)‖ ^ ka.n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ((map_ne_zero _).2 ha'))
    exact ((recB h).supN_eq_zero j ka T.σ₀ _).1 ((mul_eq_zero.1 h4.symm).resolve_left h5)
  · rw [hs, genSup_rescale]
    exact mul_le_mul_of_nonneg_left (h3 σ) (by positivity)

theorem not_restrDensity_rescale (h : LawsCore T) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j)
    (yP : GenericFrames T j) (ka : WeightFamilies.Wt D j) (hn : ka.n ≠ 0) (a : T.Q.c.F) (σ : T.Q.c.F →+* ℂ) (hσ : ‖σ a‖ < 1)
    (Z : Comp (T.Q.Xo j) T.Q.c)
    (hle : ∀ G : (recB h).Cusp j ka, genSup hG fn yP ka (G : T.R j) Z σ ≤ (recB h).supN j ka σ G)
    (F : (recB h).Cusp j ka) (hF : F ∈ (recB h).Mlat j ka) (hZ : evC hG Z (F : T.R j) ≠ 0) :
    ¬ RestrDensity h j hG (rescale fn a) yP ka := by
  rw [restrDensity_iff]
  intro H
  obtain ⟨F', -, h2, h3, h4⟩ := H Z F hF hZ
  have h5 : genSup hG fn yP ka (F : T.R j) Z σ = genSup hG fn yP ka (F' : T.R j) Z σ := by
    have h6 : evC hG Z (F' : T.R j) = evC hG Z (F : T.R j) := h3.1
    simp only [genSup, genNorm, valC, h6]
  have hpos : 0 < (recB h).supN j ka σ F' :=
    lt_of_le_of_ne ((recB h).supN_nonneg _ _ _ _) fun h0 => h2 (((recB h).supN_eq_zero _ _ _ _).1 h0.symm)
  have h7 := h4 σ
  rw [genSup_rescale, h5] at h7
  have h8 : ‖σ a‖ ^ ka.n < 1 := pow_lt_one₀ (norm_nonneg _) hσ hn
  have h9 := mul_le_mul_of_nonneg_left (hle F') (pow_nonneg (norm_nonneg (σ a)) ka.n)
  nlinarith

theorem exists_small_integer (K : Type) [Field K] [NumberField K] (v w : InfinitePlace K) (hvw : w ≠ v) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ‖w.embedding (a : K)‖ < 1 := by
  obtain ⟨u, hu⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit K v
  refine ⟨(u : 𝓞 K), u.ne_zero, ?_⟩
  have h1 := hu w hvw
  rw [InfinitePlace.norm_embedding_eq]
  have h2 : 0 < w ((u : 𝓞 K) : K) := InfinitePlace.pos_iff.2 (fun h0 => u.ne_zero (Subtype.ext h0))
  exact (Real.log_neg_iff h2).1 h1

theorem density_separated (h : LawsCore T) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j)
    (yP : GenericFrames T j) (ka : WeightFamilies.Wt D j) (hn : ka.n ≠ 0) (v w : InfinitePlace T.Q.c.F) (hvw : w ≠ v)
    (H : SupPTGe h j hG fn yP ka) (Z : Comp (T.Q.Xo j) T.Q.c)
    (hle : ∀ (σ : T.Q.c.F →+* ℂ) (G : (recB h).Cusp j ka),
      genSup hG fn yP ka (G : T.R j) Z σ ≤ (recB h).supN j ka σ G)
    (F : (recB h).Cusp j ka) (hF : F ∈ (recB h).Mlat j ka) (hZ : evC hG Z (F : T.R j) ≠ 0) :
    ∃ fn' : FrameNorms T j, SupPTGe h j hG fn' yP ka ∧ ¬ RestrDensity h j hG fn' yP ka := by
  obtain ⟨a, ha, hw⟩ := exists_small_integer T.Q.c.F v w hvw
  exact ⟨rescale fn (a : T.Q.c.F), supPTGe_rescale h hG fn yP ka a ha H,
    not_restrDensity_rescale h hG fn yP ka hn _ _ hw Z (hle _) F hF hZ⟩

end Separate

theorem lamInputs_iff (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j)
    (yP : GenericFrames T j) (large₂ : SizeData₂ D) (C A P : ℝ) (ka wL : WeightFamilies.Wt D j) {N : ℕ} (w : Fin (N + 1) → T.R j)
    (n : ℕ) (hka : wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n) :
    (LamInputs h j hG fn yP large₂ C A P wL w n ↔
      ProdInLat h j ka w n ∧ DensityWith h j hG fn yP ka (IsRestr hG) ∧ LamConst j large₂ C A ka P n wL.size) ∧
    (SupPTGe h j hG fn yP ka ↔ DensityWith h j hG fn yP ka (fun _ _ _ => True)) := by
  obtain rfl := (eq_wsmul_iff h ka wL n).1 hka
  exact ⟨and_congr Iff.rfl (and_congr (restrDensity_iff h j hG fn yP _) Iff.rfl), supPTGe_iff h j hG fn yP _⟩

theorem inputs_of_lamInputs (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j)
    (yP : GenericFrames T j) (large₂ : SizeData₂ D) (C A P : ℝ) (ka wL : WeightFamilies.Wt D j) {N : ℕ} (w : Fin (N + 1) → T.R j)
    (n : ℕ) (hka : wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n) (H : LamInputs h j hG fn yP large₂ C A P wL w n) :
    ProdInLat h j ka w n ∧ SupPTGe h j hG fn yP ka ∧ LamConst j large₂ C A ka P n wL.size := by
  obtain rfl := (eq_wsmul_iff h ka wL n).1 hka
  exact ⟨H.1, supPTGe_of_restrDensity h j hG fn yP _ H.2.1, H.2.2⟩

end GlobalTheory.LowerBoundCompare
