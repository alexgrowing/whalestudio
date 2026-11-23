import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieGenericEigenMetricSetup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFramePartitionFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionValueCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairCovCx

open GlobalTheory.GradedNorm GlobalTheory.FlagCovDivCore GlobalTheory.FlagCovWeight Matrix

section Matrices

variable {R : Type} [CommRing R] {n : ℕ}

theorem det_block_dvd (S : Matrix (Fin n) (Fin n) R) {k : ℕ} (hk : k ≤ n)
    (h : ∀ a b : Fin n, (b : ℕ) < k → k ≤ a → S a b = 0) :
    (S.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ∣ S.det := by
  rw [Matrix.twoBlockTriangular_det S (fun a => (a : ℕ) < k) fun a ha b hb => h a b hb (not_lt.1 ha)]
  let e : Fin k ≃ {a : Fin n // (a : ℕ) < k} := ⟨fun a => ⟨Fin.castLE hk a, a.2⟩, fun a => ⟨a.1, a.2⟩,
    fun _ => rfl, fun _ => rfl⟩
  rw [← det_submatrix_equiv_self e]
  exact Dvd.intro _ rfl

theorem det_block_succ (S : Matrix (Fin n) (Fin n) R) (i : Fin n) (h : ∀ b : Fin n, b < i → S i b = 0) :
    (S.submatrix (Fin.castLE i.2) (Fin.castLE i.2) : Matrix (Fin (i + 1)) (Fin (i + 1)) R).det =
      (S.submatrix (Fin.castLE i.2.le) (Fin.castLE i.2.le) : Matrix (Fin i) (Fin i) R).det * S i i := by
  rw [Matrix.det_succ_row _ (Fin.last i), Finset.sum_eq_single (Fin.last i)]
  · rw [Even.neg_one_pow ⟨_, rfl⟩, one_mul, mul_comm, Fin.succAbove_last]
    rfl
  · intro b _ hb
    have : S i (Fin.castLE i.2 b) = 0 := h _ (Fin.lt_last_iff_ne_last.2 hb)
    rw [submatrix_apply]
    erw [this]
    simp
  · simp

theorem mul_block {m : Type} (A : Matrix m (Fin n) R) (T : Matrix (Fin n) (Fin n) R) {k : ℕ} (hk : k ≤ n)
    (h : ∀ a b : Fin n, (b : ℕ) < k → k ≤ a → T a b = 0) :
    (A * T).submatrix id (Fin.castLE hk) = A.submatrix id (Fin.castLE hk) * T.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
  ext a b
  simp only [submatrix_apply, mul_apply, id]
  refine (Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ (fun c hc => ?_) fun _ => rfl).symm
  rw [h c _ b.2 (not_lt.1 fun hc' => hc ⟨⟨c, hc'⟩, rfl⟩), mul_zero]

theorem lminor_block (M T : Matrix (Fin n) (Fin n) ℂ) (k : Fin (n + 1))
    (h : ∀ a b : Fin n, (b : ℕ) < k → (k : ℕ) ≤ a → T a b = 0) :
    FD.lminor (Tᴴ * M * T) k = starRingEnd ℂ (FD.lminor T k) * FD.lminor M k * FD.lminor T k := by
  have hk := Nat.le_of_lt_succ k.2
  have e1 := mul_block (Tᴴ * M) T hk h
  have e2 := mul_block Mᴴ T hk h
  have e3 : (Tᴴ * M).submatrix (Fin.castLE hk) (Fin.castLE hk) =
      (T.submatrix (Fin.castLE hk) (Fin.castLE hk))ᴴ * M.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
    ext a b
    have := congrArg star (congrFun (congrFun e2 (Fin.castLE hk b)) a)
    simpa [mul_apply, mul_comm] using this
  have e4 : (Tᴴ * M * T).submatrix (Fin.castLE hk) (Fin.castLE hk) =
      (Tᴴ * M).submatrix (Fin.castLE hk) (Fin.castLE hk) * T.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
    ext a b
    exact congrFun (congrFun e1 (Fin.castLE hk a)) b
  simp only [FD.lminor]
  rw [e4, e3, det_mul, det_mul, det_conjTranspose]
  rfl

theorem isUnit_block {S : Matrix (Fin n) (Fin n) R} (hS : IsUnit S.det) (i : Fin n)
    (h : ∀ a b : Fin n, b < i → i ≤ a → S a b = 0) (h' : ∀ a : Fin n, i < a → S a i = 0) :
    IsUnit (S.submatrix (Fin.castLE i.2.le) (Fin.castLE i.2.le) : Matrix (Fin i) (Fin i) R).det ∧ IsUnit (S i i) := by
  have := isUnit_of_dvd_unit (det_block_dvd S (k := i + 1) i.2 fun a b hb ha => by
    rcases (Nat.lt_succ_iff.1 hb).lt_or_eq with hb | hb
    · exact h a b hb (Nat.le_of_succ_le ha)
    · rw [Fin.ext hb]; exact h' a ha) hS
  rw [det_block_succ S i fun b hb => h i b hb le_rfl] at this
  exact IsUnit.mul_iff.1 this

theorem grSq_block_tri (M : Matrix (Fin n) (Fin n) ℂ) {T : Matrix (Fin n) (Fin n) ℂ} (hT : IsUnit T.det) (i : Fin n)
    (h : ∀ a b : Fin n, b < i → i ≤ a → T a b = 0) (h' : ∀ a : Fin n, i < a → T a i = 0) :
    grSq (Tᴴ * M * T) i = ‖T i i‖ ^ 2 * grSq M i := by
  have e1 := lminor_block M T i.castSucc h
  have e2 := lminor_block M T i.succ fun a b hb ha => by
    rcases (Nat.lt_succ_iff.1 hb).lt_or_eq with hb | hb
    · exact h a b hb (Nat.le_of_succ_le ha)
    · rw [Fin.ext hb]; exact h' a ha
  have e3 : FD.lminor T i.succ = FD.lminor T i.castSucc * T i i := det_block_succ T i fun b hb => h i b hb le_rfl
  have h0 : FD.lminor T i.castSucc ≠ 0 := (isUnit_block hT i h h').1.ne_zero
  have h1 : starRingEnd ℂ (FD.lminor T i.castSucc) ≠ 0 := (map_ne_zero _).2 h0
  rw [grSq, grSq, e1, e2, e3, ← Complex.re_ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_mul]
  congr 1
  field_simp

theorem tri_mulVec {T : Matrix (Fin n) (Fin n) R} (hT : ∀ a c, c < a → T a c = 0) {c : Fin n → R} {i : Fin n}
    (hc : ∀ k, i < k → c k = 0) : (T *ᵥ c) i = T i i * c i ∧ ∀ a, i < a → (T *ᵥ c) a = 0 :=
  ⟨Finset.sum_eq_single (s := Finset.univ) (f := fun a => T i a * c a) i
    (fun a _ ha => ha.lt_or_gt.elim (fun h => by rw [hT _ _ h, zero_mul]) fun h => by rw [hc _ h, mul_zero]) (by simp),
    fun a ha => Finset.sum_eq_zero (s := Finset.univ) (f := fun b => T a b * c b) fun b _ =>
      (lt_or_ge i b).elim (fun h => by rw [hc _ h, mul_zero]) fun h => by rw [hT _ _ (h.trans_lt ha), zero_mul]⟩

end Matrices

theorem exists_step {X : Scheme.{0}} {M : X.Modules} {N : ℕ} (fl : Vert.Flag M N) (l j : Fin (N + 1)) (h : l ≤ j) :
    ∃ g : fl.F l ⟶ fl.F j, g ≫ fl.ι j = fl.ι l := by
  induction j using Fin.induction with
  | zero => obtain rfl : l = 0 := Fin.le_zero_iff.1 h; exact ⟨𝟙 _, by simp⟩
  | succ j ih =>
    rcases h.lt_or_eq with h | rfl
    · obtain ⟨g, hg⟩ := ih (Fin.le_castSucc_iff.2 h)
      exact ⟨g ≫ fl.step j, by rw [Category.assoc, fl.step_ι, hg]⟩
    · exact ⟨𝟙 _, by simp⟩

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem grSq_of_block {R K : Type} [CommRing R] [Field K] {ψ : R →+* K} (hψ : Function.Injective ψ) {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} {φ' : c.F →+* K} {x' : Sp K ⟶ Z.X} {f : EigFrame Z φ x} {v : EigFrame Z φ' x'}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (hf : f.Tri ψ v t) {τ : E →+* ℂ}
    {u : Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u)
    {A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R} (hA : IsUnit A.det) (ρ : Kˣ) (i : Fin (Dw.mult τ))
    (h : ∀ a : Fin (Dw.mult τ) → R, ((a = fun b => A b i) ∨ ∃ k < i, a = fun b => A b i + A b k) →
      ∃ (w : Sp (DualNumber K) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → K),
      IsCombAtG Z.t x' (fun b => spMap (dualMap ψ) ≫ u b) (fun b => ψ (a b)) w ∧ IsCombAtG Z.t x' (v.v τ) cf w ∧
        cf i = (ρ⁻¹ : Kˣ) ∧ ∀ k, i < k → cf k = 0)
    {σ : c.F →+* ℂ} (Gm : EigMet Z σ) {yc : CxPts (genStr Z) σ} {g : EigFrame Z σ (yc.1 ≫ genι Z)} {χ : R →+* ℂ}
    (hg : f.Tri χ g 1) {M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ}
    (hM : ∀ g' : EigFrame Z σ (yc.1 ≫ genι Z), (∀ i, g'.v τ i = spMap (dualMap χ) ≫ u i) →
      M = (Gm.gram yc g' τ)ᵀ) :
    ∃ a : R, IsUnit a ∧ ψ a = t τ i * (ρ⁻¹ : Kˣ) ∧
      grSq (HermFrame.chg (A.map χ) M) i = ‖χ a‖ ^ 2 * grSq (Gm.gram yc g τ) i := by
  obtain ⟨k, rfl⟩ := exists_frame_of_basis f hu
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨k', hk'⟩ := k.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨f₁, hf₁⟩ := f.exists_isMap χ hg.2.1 hg.1
  obtain ⟨k₁, hk₁⟩ := k.exists_isMap χ hg.2.1 hg.1
  obtain ⟨T1, T2⟩ := hf.co τ hf'
  obtain ⟨U1, U2⟩ := hg.co τ hf₁
  have key (a : Fin (Dw.mult τ) → R) (ha : (a = fun b => A b i) ∨ ∃ k < i, a = fun b => A b i + A b k) :
      ψ ((f.co k τ *ᵥ a) i) = t τ i * (ρ⁻¹ : Kˣ) ∧ ∀ b, i < b → (f.co k τ *ᵥ a) b = 0 := by
    obtain ⟨w, cf, h1, h2, h3, h4⟩ := h a ha
    rw [← funext (hk' τ)] at h1
    have e (b) : ψ ((f.co k τ *ᵥ a) b) = (f'.co v τ *ᵥ cf) b := by
      rw [RingHom.map_mulVec, ← hf'.co τ hk' hf.1]
      exact congrFun (co_mulVec f' k' v τ h1 h2) b
    obtain ⟨e1, e2⟩ := tri_mulVec T1 h4
    exact ⟨by rw [e, e1, T2, h3], fun b hb => hψ (by rw [e, e2 b hb, map_zero])⟩
  obtain ⟨a1, a2⟩ := key _ (.inl rfl)
  have s1 : ∀ a b, b < i → i ≤ a → (f.co k τ * A) a b = 0 := fun a b hb ha => by
    obtain ⟨b1, b2⟩ := key _ (.inr ⟨b, hb, rfl⟩)
    have e : (f.co k τ *ᵥ fun d => A d i + A d b) a = (f.co k τ *ᵥ fun d => A d i) a + (f.co k τ * A) a b :=
      congrFun (mulVec_add (f.co k τ) (fun d => A d i) fun d => A d b) a
    rcases ha.lt_or_eq with ha | rfl
    · rw [b2 a ha, a2 a ha, zero_add] at e
      exact e.symm
    · rw [hψ (b1.trans a1.symm)] at e
      exact (left_eq_add.1 e)
  have s2 : ∀ a, i < a → (f.co k τ * A) a i = 0 := a2
  have hS : IsUnit (f.co k τ * A).det := by rw [Matrix.det_mul]; exact (f.isUnit_det_co k τ).mul hA
  refine ⟨_, (isUnit_block hS i s1 s2).2, a1, ?_⟩
  have e1 : HermFrame.chg (A.map χ) M =
      (((f.co k τ * A).map χ)ᴴ * Gm.gram yc f₁ τ * (f.co k τ * A).map χ)ᵀ := by
    rw [hM k₁ (hk₁ τ), Gm.change yc f₁ k₁, Matrix.map_mul, ← hf₁.co τ hk₁ hg.1]
    simp only [HermFrame.chg, transpose_mul, conjTranspose_mul, Matrix.mul_assoc]
  have e2 := grSq_tri (Gm.gram yc f₁ τ) U1 (fun a => U2 a ▸ Units.ne_zero _) i
  rw [← Gm.change, U2] at e2
  have hS' : IsUnit ((f.co k τ * A).map χ).det := by
    have := hS.map χ
    rwa [RingHom.map_det] at this
  rw [e1, grSq_transpose, grSq_block_tri _ hS' i (fun a b hb ha => (congrArg χ (s1 a b hb ha)).trans (map_zero _))
    fun a ha => (congrArg χ (s2 a ha)).trans (map_zero _)]
  simp only [Pi.one_apply, Units.val_one, norm_one, one_pow, one_mul] at e2
  exact congrArg₂ (· * ·) rfl e2.symm

end Frames

set_option maxHeartbeats 1600000 in

theorem weight_lie {D : D7} {O : Setup D} {c : O.s.Comp} {Bs : Scheme.{0}} {q : Bs ⟶ Sp (𝓞 D.what₂.LL)}
    {Bg : Scheme.{0}} {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen O.s.T.Z} (Gm : ∀ σ', EigMet O.s.T.Z σ')
    {Y X G : Scheme.{0}} [IsIntegral G] {π : Y ⟶ Bs} {ρ : X ⟶ Y} {j : G ⟶ X} {πG : G ⟶ (O.var c).X}
    {φ : (O.var c).Fn →+* G.functionField} {jG : G ⟶ Bg}
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (c1 : jG ≫ jB = j ≫ ρ ≫ π) (c2 : jG ≫ πB = πG ≫ (O.Φ.C c).π)
    {τ : D.host.E →+* ℂ} {M : Bs.Modules} {h : VMetric q M (O.S.Dw.mult τ)} (H : h.IsCInf)
    {u : FrAssign O.s.T.Z M (O.S.Dw.mult τ) jB} (frB : IsLieFrames O.s.T.Z O.κ.e jB πB M _ τ false u)
    (lm : IsLieMet O.s.T.Z O.κ.e q jB πB M _ τ false rfl Gm h u)
    (fl : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult τ))
    (i : Fin (O.S.Dw.mult τ)) (r : ((fl.root i).pull j).ι → G.functionFieldˣ)
    (c3 : GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) τ h.isVB jB πB u π ρ fl j φ jG i r)
    (σ : D.what₂.LL →+* ℂ) (z : CxPts (πG ≫ (O.var c).str) σ) (y : Pts (O.var c) σ)
    (y' : CxPts (ρ ≫ π ≫ q) (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) (ch : ((fl.root i).pull j).ι)
    (t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → (O.var c).Fnˣ) (g : (O.Φ.C c).FrameAt y)
    (had : (O.Φ.C c).Adapted y t g 1) (ey : y.1 = z.1 ≫ πG) (ey' : y'.1 = z.1 ≫ j)
    (hx : under z ∈ ((fl.root i).pull j).U ch) :
    UnitAt (under z) ((((r ch)⁻¹ : G.functionFieldˣ) : G.functionField) * φ (t τ i : (O.var c).Fn)) ∧
      Real.exp (-((VMetric.grLB fl i ((H.pull π rfl).pull ρ rfl)).φ (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))).φ
          (ch PUnit.unit) y') =
        ‖ratVal ((((r ch)⁻¹ : G.functionFieldˣ) : G.functionField) * φ (t τ i : (O.var c).Fn)) z‖ ^ 2 *
          grSq ((Gm (embOf O.κ.e σ)).gram _ g τ) i := by
  have hqc := h.isVB.isQuasicoherent
  have hqc' := (h.isVB.pullback π).isQuasicoherent
  set x := under z with hxz

  obtain ⟨cc, hci, hcc⟩ : ∃ cc : ∀ k, (fl.root k).ι, cc i = ch PUnit.unit ∧ ∀ k, j x ∈ (cc k).U := by
    choose U e hU he using fun k => fl.isVB_gr k (j x)
    let c₀ : ∀ k, (fl.root k).ι := fun k => ⟨U k, e k, he k⟩
    refine ⟨Function.update c₀ i (ch PUnit.unit), Function.update_self _ _ _, fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self]
      exact LB.pull_U_le j ch hx
    · rw [Function.update_of_ne hk]
      exact hU k
  obtain ⟨ch', rfl⟩ : ∃ ch' : (fl.root i).ι, ch = fun _ => ch' := ⟨ch PUnit.unit, rfl⟩
  subst hci
  obtain ⟨V, f, hV, hf⟩ := h.isVB (π (ρ (j x)))
  obtain ⟨W, hWV, hW, s, hxW, hs, hfr⟩ := exists_lifts_isFrame fl cc hcc (U := ρ ⁻¹ᵁ (π ⁻¹ᵁ V)) hV
  let ψ := algebraMap (G.presheaf.stalk x) G.functionField
  have hψ : Function.Injective ψ := IsFractionRing.injective _ _
  obtain ⟨χ, hχ⟩ : ∃ χ : G.presheaf.stalk x →+* ℂ, spMap χ ≫ G.fromSpecStalk x = z.1 :=
    ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1⟩
  have hg : FlagCov.genPt G = spMap ψ ≫ G.fromSpecStalk x := (spMap_fromSpecStalk G x).symm
  have hRW : ⊤ ≤ (G.fromSpecStalk x ≫ j) ⁻¹ᵁ W := top_le_fromSpecStalk (U := j ⁻¹ᵁ W) hxW
  have hRV : ⊤ ≤ ((G.fromSpecStalk x ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, c1]
    exact top_le_fromSpecStalk (U := (j ≫ ρ ≫ π) ⁻¹ᵁ V) hV
  have hKW : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W := by
    rw [hg, Category.assoc]
    exact fun w _ => hRW (x := spMap ψ w) trivial
  have hV' {K : Type} [CommRing K] (ρ : G.presheaf.stalk x →+* K) {w : Sp K ⟶ Bg}
      (hw : w = spMap ρ ≫ G.fromSpecStalk x ≫ jG) : ∃ hw' : ⊤ ≤ (w ≫ jB) ⁻¹ᵁ V,
        u V f hf K w hw' = fun b => spMap (dualMap ρ) ≫ u V f hf _ (G.fromSpecStalk x ≫ jG) hRV b := by
    subst hw
    refine ⟨?_, funext (frB.2.2 V f hf _ _ ρ _ hRV _)⟩
    rw [Category.assoc]
    exact fun w _ => hRV (x := spMap ρ w) trivial
  obtain ⟨hKV, hu'⟩ := hV' ψ (w := FlagCov.genPt G ≫ jG) (by rw [hg, Category.assoc])
  obtain ⟨hCV, hu''⟩ := hV' χ (w := z.1 ≫ jG) (by rw [← Category.assoc, hχ])
  obtain ⟨φy, fy, a1, a2⟩ := had
  obtain ⟨ψ₀, fR, v, e1, e2, e3, e4⟩ := exists_frame_pull (O.Φ.C c) πG φ φs x
    (xR := (G.fromSpecStalk x ≫ jG) ≫ πB ≫ genι O.s.T.Z)
    (by rw [Category.assoc, ← Category.assoc jG, c2, Category.assoc])
    (xK := FlagCov.genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z) (by rw [← Category.assoc jG, c2, Category.assoc]; rfl)
    (show Var.base y = πG x by rw [Var.base, ey]; rfl) a1 (χ := χ)
    (by rw [FlagCpt.spMap_evStalk, ← Category.assoc, hχ, ey]) a2
  have hu := frB.1 V f hf _ (G.fromSpecStalk x ≫ jG) hRV ψ₀ (by
    refine Eq.trans ?_ e1
    refine (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).symm.trans ?_))
    rw [c2]
    exact (Category.assoc _ _ _).trans (congrArg _ (O.Φ.C c).π_str))
  let bas := ((hf.pullback π).pullback ρ).basis hWV
  let A₀ := bas.toMatrix fun k => (fl.ι k.succ).app W (s k)
  have hA₀ : IsUnit A₀.det := by
    have := (((hf.pullback π).pullback ρ).detUnit hfr hWV le_rfl).isUnit
    simpa only [IsFrame.val_detUnit, Twist.resM_self, Module.Basis.det_apply] using this
  let evR := TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW
  let A := A₀.map evR
  have hA : IsUnit A.det := by
    have := hA₀.map evR
    rwa [RingHom.map_det] at this
  have hev {K : Type} [CommRing K] (ρ : G.presheaf.stalk x →+* K) {w : Sp K ⟶ X} (hw' : ⊤ ≤ w ⁻¹ᵁ W)
      (hw : w = spMap ρ ≫ G.fromSpecStalk x ≫ j) (a) : TangentOrigin.evalPt w W hw' a = ρ (evR a) := by
    subst hw
    exact TangentOrigin.evalPt_spMap_comp ρ _ W hRW hw' _
  have hv : (fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v τ k) = v.v τ := (funext (e2 _)).symm
  have hsec (s' : Γ(fl.F i.succ, W)) (hs' : (fl.π i).app W s' = (fl.π i).app W (s i)) :
      ∃ (w : Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left) (cf : Fin (O.S.Dw.mult τ) → G.functionField),
      IsCombAtG O.s.T.Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z)
        (fun b => spMap (dualMap ψ) ≫ u V f hf _ (G.fromSpecStalk x ≫ jG) hRV b)
        (fun b => ψ (evR (bas.repr ((fl.ι i.succ).app W s') b))) w ∧
      IsCombAtG O.s.T.Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z) (v.v τ) cf w ∧
        cf i = ((r fun _ => cc i)⁻¹ : G.functionFieldˣ) ∧ ∀ k, i < k → cf k = 0 := by
    have := c3 (fun _ => cc i) V f hf W (hW i) hWV s' (hs'.trans (hs i)) hKW hKV
    dsimp only at this
    rw [hu', hv] at this
    simp only [hev ψ hKW (by rw [hg, Category.assoc])] at this
    exact this
  have hy'W : y' ∈ ptsIn (ρ ≫ π ≫ q) _ W := mem_ptsIn.2 (by rw [ey']; exact hxW)
  have hy'V : y' ∈ ptsIn (ρ ≫ π ≫ q) _ (ρ ⁻¹ᵁ (π ⁻¹ᵁ V)) := mem_ptsIn.2 (hWV (mem_ptsIn.1 hy'W))
  have hy''V : Points.PtsOver.map ρ rfl _ y' ∈ ptsIn (π ≫ q) _ (π ⁻¹ᵁ V) := mem_ptsIn.2 (mem_ptsIn.1 hy'V)
  let cV : Chart M _ := ⟨V, f, hf⟩
  have hM := lm σ (Points.PtsOver.map π rfl _ (Points.PtsOver.map ρ rfl _ y')) (z.1 ≫ jG) ((O.Φ.C c).down y)
    (by rw [Category.assoc, c1, ← Category.assoc, ← ey', ← Category.assoc]; rfl)
    (by rw [Category.assoc, c2, ← Category.assoc, ← ey]; rfl) cV hCV
  have hgram : (((h.pull π rfl).pull ρ rfl).met _).gram (fun k => (fl.ι k.succ).app W (s k)) y' =
      HermFrame.chg (A.map χ) ((h.met _).G cV (Points.PtsOver.map π rfl _ (Points.PtsOver.map ρ rfl _ y'))) := by
    rw [Met.gram_eq _ ((cV.pull h.isVB π).pull (h.isVB.pullback π) ρ) hy'V _ hy'W]
    refine congrArg₂ _ ?_ ((Met.pull_G _ ρ rfl (cV.pull h.isVB π) hy'V).trans (Met.pull_G _ π rfl cV hy''V))
    ext b k
    refine (Chart.crd_eq _ _ le_rfl hWV hy'W b).trans ?_
    rw [ev_eq hy'W, evHom_eq_evalPt, Twist.resM_self]
    exact hev χ _ (by rw [ey', ← Category.assoc, hχ]) _
  have hw := GlobalTheory.GradedWeight.exp_neg_grLB_φ ((h.pull π rfl).pull ρ rfl) ((H.pull π rfl).pull ρ rfl) fl i _ y' W hy'W cc
    (fun k _ => hW k) s fun k _ => hs k
  replace hw := hw.trans ((grSq_block _ i).trans (congrArg (grSq · i) hgram))
  obtain ⟨d, hd, ed, en⟩ := grSq_of_block hψ e3 hu hA (r fun _ => cc i) i (by
    rintro a (rfl | ⟨k, hk, rfl⟩)
    · exact hsec (s i) rfl
    · obtain ⟨gk, hgk⟩ := exists_step fl k.succ i.castSucc (Fin.succ_le_castSucc_iff.2 hk)
      have e0 : (gk ≫ fl.step i) ≫ fl.π i = 0 := by
        have e : fl.step i ≫ fl.π i = 0 := Limits.cokernel.condition _
        rw [Category.assoc, e, Limits.comp_zero]
      have e1 : (gk ≫ fl.step i) ≫ fl.ι i.succ = fl.ι k.succ := by rw [Category.assoc, fl.step_ι, hgk]
      have := hsec (s i + (gk ≫ fl.step i).app W (s k)) (by
        rw [map_add]
        exact add_eq_left.2 (congr(($e0).app W (s k))))
      have e2 : (fl.ι i.succ).app W (s i + (gk ≫ fl.step i).app W (s k)) =
          (fl.ι i.succ).app W (s i) + (fl.ι k.succ).app W (s k) := by
        rw [map_add]
        exact congrArg _ (congr(($e1).app W (s k)))
      rw [e2] at this
      simp only [map_add, Finsupp.add_apply] at this ⊢
      exact this) (Gm (embOf O.κ.e σ)) e4 (fun g' hg' => hM g' fun k => (hg' k).trans (congrFun hu'' k).symm)
  have ed' : (((r fun _ => cc i)⁻¹ : G.functionFieldˣ) : G.functionField) * φ (t τ i : (O.var c).Fn) = ψ d := by
    rw [ed, mul_comm]
    rfl
  refine ⟨⟨d, hd, ed'.symm⟩, hw.trans (en.trans ?_)⟩
  exact congrArg (fun s => ‖s‖ ^ 2 * _) ((ratVal_stalk z hχ d).symm.trans (congrArg (ratVal · z) ed'.symm))

theorem frameSecX_norm_cx : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
  ∀ (D : D7) (O : Setup D) (hO : O.Core) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp) (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j)) (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z) (G : ∀ σ', EigMet O.s.T.Z σ')
    (Y X Gs : Scheme.{0}) [IsIntegral Y] [IsIntegral X] [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg),
    IsArithVar (ρ ≫ π ≫ q) (O.var c).dim → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    GlobalTheory.PairCov.CovCommon O R c q jB πB G π ρ j πG φ jG →
    ∀ (σ : D.host.E →+* ℂ) (M : Bs.Modules) (hM : VMetric q M (O.S.Dw.mult σ)) (HM : hM.IsCInf)
      (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB), IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t →
    IsLieMet O.s.T.Z O.κ.e q jB πB M _ σ false rfl G hM t →
    ∀ (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ))
      (i : Fin (O.S.Dw.mult σ)) (r : ((F.root i).pull j).ι → Gs.functionFieldˣ),
      GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM.isVB jB πB t π ρ F j φ jG i r →
    ∀ st, letterOf O.S.Dw st = some ⟨σ, i⟩ →
    ∀ (τ : D.what₂.LL →+* ℂ) (z : CxPts (πG ≫ (O.var c).str) τ) (y : Pts (O.var c) τ)
      (y' : CxPts (ρ ≫ π ≫ q) (τ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) (ch : ((VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.pull j).ι),
      y.1 = z.1 ≫ πG → y'.1 = z.1 ≫ j → under z ∈ ((VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.pull j).U ch →
        (Real.exp (-(2 * ((lineAdl O R c st 1).n : ℕ) * (lineAdl O R c st 1).ci (InfinitePlace.mk τ))) *
          (cxSt D.what₂.LL).pn (O.var c) τ (lineAdl O R c st 1).D ((lineAdl O R c st 1).m τ)
            ((cxSt D.what₂.LL).cx (O.var c) τ (genAt (lineAdl O R c st 1).D (under y))) y) ^ 1 =
        ‖ratVal (φ (genAt (lineAdl O R c st 1).D (under y)) ^ 1 * (r ch : Gs.functionField)) z‖ ^ 2 *
          Real.exp (-((VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).φ _).φ (ch PUnit.unit) y') := by
  intro _ _ _ D O _ R _ c Bs _ q _ _ Bg jB πB Gm Y X G _ _ _ π ρ j πG φ jG _ _ hc τ M h H u frB lm fl i r c3 st hst
    σ z y y' ch hy hy' hz
  obtain ⟨-, -, -, hmet, -, _, _, φs, c1, c2⟩ := hc
  obtain ⟨⟨t, g⟩, -, hadp⟩ := (O.Φ.C c).exists_adapted y
  set w : Pad.Sym D.host.E →₀ ℤ := Finsupp.single (ArIn.ind ∅, some R, st) 1 with hw
  have hpar : Pad.parOf w = some R := by
    have hne : w.support.Nonempty := ⟨_, Finsupp.mem_support_iff.2 (by rw [hw, Finsupp.single_eq_same]; exact one_ne_zero)⟩
    rw [Pad.parOf, dif_pos hne, Finset.mem_singleton.1 (Finsupp.support_single_subset hne.choose_spec)]
  have hn (x : Pad.Letter O.S.Dw) : Pad.expo O.S.Dw w x = if τ = x.1 ∧ (i : ℕ) = x.2 then 1 else 0 := by
    rw [Pad.expo, hw, Finsupp.sum_single_index (by simp), hst]
    refine if_congr ?_ rfl rfl
    obtain ⟨τ', k⟩ := x
    constructor
    · intro e
      cases e
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, e⟩
      obtain rfl : i = k := Fin.ext e
      rfl
  have ep : prodPow t (Pad.expo O.S.Dw w) = t _ i := prod_zpow_single (fun w => t w.1 w.2) _ _ _ hn
  have eg : (O.Φ.C c).genSq (Gm (embOf O.κ.e σ)) (Pad.expo O.S.Dw w) g =
      grSq ((Gm (embOf O.κ.e σ)).gram _ g _) i :=
    prod_zpow_single (fun w => grSq ((Gm (embOf O.κ.e σ)).gram _ g w.1) w.2) _ _ _ hn
  refine (pn_adlOf_genAt_of_adapted D O c R Gm hmet w hpar σ y t g hadp).trans ?_
  obtain ⟨hU, hW⟩ := weight_lie Gm φs c1 c2 H frB lm fl i r c3 σ z y y' ch t g hadp hy hy' hz
  have h1 := FlagCpt.prodPow_mem (Pad.expo O.S.Dw w) hadp.mem_eqnSet
  erw [hW]
  rw [eg]
  rw [ep] at h1 ⊢
  set Pf : (O.var c).Fn := (t τ i : (O.var c).Fn) with hPf
  set s : (O.var c).Fn := genAt (adlOf (O.Φ.C c) (O.met.hm c) w).D (under y) with hs
  set X0 : G.functionField := (((r ch)⁻¹ : G.functionFieldˣ) : G.functionField) * φ Pf with hX0
  have hsP : UnitAt (under y) (s * Pf) := by
    have h2 : CartierDiv.IsEqn (divOf (O.Φ.C c) (Pad.expo O.S.Dw w)) (Var.base y)
        (eqn (adlOf (O.Φ.C c) (O.met.hm c) w).D (under y)) := GlobalTheory.TrueGeo.Base.isEqn_eqn _ _
    have h3 := (CartierDiv.IsEqn.iff_unitAt h2).1 h1
    have e : s * Pf = Pf / ((eqn (adlOf (O.Φ.C c) (O.met.hm c) w).D (under y) : (O.var c).Fnˣ) : (O.var c).Fn) := by
      rw [hs, genAt, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]
    rw [e]
    exact h3
  obtain ⟨hv, hu⟩ := GlobalTheory.RatValPull.regAt_ratVal_pull (O.var c).str πG φ φs σ z y hy (s * Pf)
  have hUz := hu hsP
  have hreg : RegAt (under z) (φ s * (r ch : G.functionField)) := by
    obtain ⟨b, hb, hbX⟩ := hU
    obtain ⟨b', -, hb'X⟩ := hUz
    refine ⟨b' * ↑hb.unit⁻¹, ?_⟩
    have hP0 : φ Pf ≠ 0 := (map_ne_zero φ).2 (Units.ne_zero _)
    have hr0 : (r ch : G.functionField) ≠ 0 := Units.ne_zero _
    rw [map_mul, hb'X]
    have : algebraMap _ G.functionField (↑hb.unit⁻¹ : G.presheaf.stalk (under z)) = (algebraMap _ G.functionField b)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, IsUnit.val_inv_mul, map_one])
    rw [this, hbX, hX0, map_mul, Units.val_inv_eq_inv_val, mul_inv, inv_inv]
    field_simp
  have hfac : φ (s * Pf) = (φ s * (r ch : G.functionField)) * X0 := by
    rw [hX0, map_mul, mul_assoc, Units.mul_inv_cancel_left]
  have hrv := (hv hsP.regAt).2
  rw [hfac, ratVal_mul hreg (hU.regAt)] at hrv
  rw [← hrv, pow_one]
  simp only [norm_mul, mul_pow]
  ring

end GlobalTheory.PairCovCx

end
