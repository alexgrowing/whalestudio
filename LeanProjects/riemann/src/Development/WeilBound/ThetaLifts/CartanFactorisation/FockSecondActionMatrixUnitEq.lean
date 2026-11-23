import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsGreatestProperInvariantSubmoduleOfSide
import Development.WeilBound.ThetaLifts.CartanFactorisation.TensMax
import Development.WeilBound.ThetaLifts.CartanFactorisation.UnitDef
import Development.WeilBound.ThetaLifts.CartanFactorisation.PolCount
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLParity

noncomputable section

namespace PositivityTheory.ThKF.Unit

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.ThK PiTensorProduct

theorem linePos_eq (p q r s : ℕ) : (FockH1Action.linePos : Ln p q r s → Bool) = linePos := by
  funext l; rcases l with ⟨_ | _, _ | _⟩ <;> rfl

theorem omAct_eq (p q r s : ℕ) : FockH1Action.omAct p q r s = omAct p q r s := by
  simp only [FockH1Action.omAct, omAct, FockH1Action.omE, omE, FockH1Action.raiB, raiB, FockH1Action.lowB, lowB, linePos_eq]

theorem fockFirstAction_matrixUnit_eq (p q r s : ℕ) : FockH1Action.fockAct1 p q r s = fockAct1 p q r s := by
  rw [FockH1Action.fockAct1, fockAct1, omAct_eq]

theorem fockSecondAction_matrixUnit_eq (p q r s : ℕ) : FockH1Action.fockAct2 p q r s = fockAct2 p q r s := by
  rw [FockH1Action.fockAct2, fockAct2, omAct_eq]

theorem Jm_sq (p q : ℕ) : Jm p q * Jm p q = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem Jm_ct (p q : ℕ) : (Jm p q)ᴴ = Jm p q := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem decomp {p q : ℕ} (Z : Mat p q) :
    ∃ Z₁ ∈ upq p q, ∃ Z₂ ∈ upq p q, Z = Z₁ + Complex.I • Z₂ ∧ Jm p q * Zᴴ * Jm p q = -Z₁ + Complex.I • Z₂ := by
  have a1 : (Jm p q * Zᴴ * Jm p q)ᴴ * Jm p q = Jm p q * Z := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_ct, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      Matrix.mul_assoc, Jm_sq, Matrix.mul_one]
  have a2 : Jm p q * (Jm p q * Zᴴ * Jm p q) = Zᴴ * Jm p q := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_sq, Matrix.one_mul]
  generalize Jm p q * Zᴴ * Jm p q = S at a1 a2
  refine ⟨(1 / 2 : ℂ) • (Z - S), ?_, (-Complex.I / 2) • (Z + S), ?_, ?_, ?_⟩
  · show _ + _ = 0
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, a1, a2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]; module
  · show _ + _ = 0
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, a1, a2]
    have : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by simp
    rw [this]; module
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]; module
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]; module

theorem tr_upq {p q : ℕ} {Y : Mat p q} (h : Y ∈ upq p q) : starRingEnd ℂ Y.trace = -Y.trace := by
  have h1 : Jm p q * (Yᴴ * Jm p q + Jm p q * Y) = 0 := by rw [show _ + _ = (0 : Mat p q) from h, Matrix.mul_zero]
  have h2 := congrArg Matrix.trace h1
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_comm, Matrix.mul_assoc, Jm_sq, Matrix.mul_one, ← Matrix.mul_assoc, Jm_sq,
    Matrix.one_mul, Matrix.trace_conjTranspose, Matrix.trace_zero] at h2
  exact eq_neg_of_add_eq_zero_left h2

theorem star_E {p q : ℕ} (a b : Ix p q) :
    Jm p q * (FockH1Action.Eab a b)ᴴ * Jm p q = PositivityTheory.KReal.epsB a b • FockH1Action.Eab b a := by
  have e : Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => -1) := by
    ext (i | i) (j | j) <;> simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  rw [e]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    rcases a with a | a <;> rcases b with b | b <;> simp [FockH1Action.Eab, PositivityTheory.KReal.epsB, FockH1Action.sameBlock]
  · have h' : ¬ (a = j ∧ b = i) := fun h' => h h'.symm
    simp [FockH1Action.Eab, Matrix.single, h, h']

section At

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

def atL (w : ι) : Module.End ℂ V →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : ι, V) :=
  (mapMultilinear ℂ (fun _ : ι => V) fun _ => V).toLinearMap (fun _ => LinearMap.id) w

theorem atL_eq (w : ι) (L : Module.End ℂ V) : atL w L = atPl (V := fun _ => V) w L := rfl

theorem atL_one (w : ι) : atL w (1 : Module.End ℂ V) = 1 := by
  rw [atL_eq, atPl, show (1 : Module.End ℂ V) = LinearMap.id from rfl, Function.update_eq_self]
  exact map_id

theorem atL_tprod (w : ι) (L : Module.End ℂ V) (t : ι → V) (x : V) :
    atL w L (tprod ℂ (Function.update t w x)) = tprod ℂ (Function.update t w (L x)) := by
  rw [atL_eq, atPl, map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem sum_single {r s : ℕ} (act : Mat r s →ₗ[ℂ] Module.End ℂ V) (c : ι → ℂ) (w : ι) (Z : Mat r s) :
    sumPl (V := fun _ => V) (fun w' => act (Function.update (fun _ => (0 : Mat r s)) w Z w') +
      (c w' * (Function.update (fun _ => (0 : Mat r s)) w Z w').trace) • 1) = atL w (act Z) + (c w * Z.trace) • 1 := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · rw [← atL_eq, map_add, map_smul, atL_one, Function.update_self]
  · intro w' _ h
    rw [← atL_eq]; simp [Function.update_of_ne h]
  · simp

end At

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem line_at {m P Q R S r s : ℕ} {κ : Type} [Fintype κ] (hcm : IsCMExt F E σ) {τ : ∀ w : InfinitePlace F, EmbOver E w}
    {J : Matrix (Fin m) (Fin m) (AE F E)} {b : ℂ} {C : InfinitePlace F → Matrix (Fin m) (Ix r s) ℂ}
    (hC : ∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) {o : UG (cA σ) J →* Module.End ℂ ((κ → AF F) → ℂ)}
    {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} {act : Mat r s →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)} {c : InfinitePlace F → ℂ}
    (h : ActsBy τ C o Φ act c) (w : InfinitePlace F) {Z : Mat r s} (hZ : Z ∈ upq r s) :
    ∃ γ ∈ RLines σ J, ∀ T, ActsD (evI F) (fun t => o (γ (Multiplicative.ofAdd t))) (Φ T)
      (Φ (atL w (act Z) T + (c w * Z.trace) • T)) := by
  obtain ⟨γ, hγ, hg⟩ := PositivityTheory.RL.lineEx F E σ (Fin m) r s τ J b C hcm hC (Function.update (fun _ => 0) w Z) fun w' => by
    by_cases e : w' = w
    · subst e; simpa using hZ
    · simp [Function.update_of_ne e, upq]
  refine ⟨γ, hγ, fun T => (PositivityTheory.RL.actsLaws F κ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) ?_⟩
  have := h γ hγ _ hg T
  rw [sum_single] at this
  exact this

theorem radMax_pair {n d P Q R S : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {om : Rep σ X W}
    (hcm : IsCMExt F E σ) {A : InfinitePlace F → Matrix (Fin n) (Ix P Q) ℂ} {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ}
    (fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C) {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (inj : Function.Injective Φ) (hr : LinearMap.range Φ = M.Pol B.ψ B.emb) {c₁ c₂ : InfinitePlace F → ℂ}
    (h1 : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 P Q R S) c₁)
    (h2 : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c₂) (hc₂ : ∀ w, starRingEnd ℂ (c₂ w) = c₂ w)
    (ho : ∀ w, One P Q R S (-c₁ w)) : RadMaxAt B M om := by
  intro β hs hX hW N hN hNs
  let φ : Tens F P Q R S →ₗ[ℂ] M.Pol B.ψ B.emb := Φ.codRestrict _ fun T => hr ▸ LinearMap.mem_range_self Φ T
  have sj : Function.Surjective φ := fun y => by
    obtain ⟨T, hT⟩ : y.1 ∈ LinearMap.range Φ := by rw [hr]; exact y.2
    exact ⟨T, Subtype.ext hT⟩
  let β' : Tens F P Q R S →ₗ⋆[ℂ] Tens F P Q R S →ₗ[ℂ] ℂ := (β.compl₂ φ).comp φ
  have hβ' : ∀ x y, β' x y = β (φ x) (φ y) := fun _ _ => rfl
  have sA : ∀ w Z T y, β' (atL w (fockAct1 P Q R S Z) T + (c₁ w * Z.trace) • T) y = 0 := fun w Z T y => by
    have u : ∀ Z ∈ upq P Q, β' (atL w (fockAct1 P Q R S Z) T + (c₁ w * Z.trace) • T) y = 0 := fun Z hZ => by
      obtain ⟨γ, hγ, h⟩ := line_at hcm fr.2.1 h1 w hZ
      rw [hβ', hX γ hγ (φ T) (φ _) (h T)]; rfl
    obtain ⟨Z₁, a1, Z₂, a2, rfl, -⟩ := decomp Z
    have e : atL w (fockAct1 P Q R S (Z₁ + Complex.I • Z₂)) T + (c₁ w * (Z₁ + Complex.I • Z₂).trace) • T =
        (atL w (fockAct1 P Q R S Z₁) T + (c₁ w * Z₁.trace) • T) +
          Complex.I • (atL w (fockAct1 P Q R S Z₂) T + (c₁ w * Z₂.trace) • T) := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
      module
    rw [e, map_add, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, u Z₁ a1, u Z₂ a2, smul_zero, add_zero]
  have sB : ∀ w (Z : Mat R S) x y, β' (atL w (fockAct2 P Q R S Z) x) y =
      β' x (atL w (fockAct2 P Q R S (Jm R S * Zᴴ * Jm R S)) y) := fun w Z x y => by
    have u : ∀ Z ∈ upq R S, β' (atL w (fockAct2 P Q R S Z) x) y = -β' x (atL w (fockAct2 P Q R S Z) y) := fun Z hZ => by
      obtain ⟨γ, hγ, h⟩ := line_at hcm fr.2.2 h2 w hZ
      have := hW γ hγ (φ x) (φ _) (φ y) (φ _) (h x) (h y)
      rw [← hβ', ← hβ'] at this
      simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_mul, hc₂, tr_upq hZ,
        smul_eq_mul, RingHom.id_apply] at this
      linear_combination this
    obtain ⟨Z₁, a1, Z₂, a2, e1, e2⟩ := decomp Z
    rw [e2, e1]
    simp only [map_add, map_neg, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.map_smulₛₗ,
      u Z₁ a1, u Z₂ a2, Complex.conj_I, smul_eq_mul, RingHom.id_apply]
    ring
  choose K k1 k2 k3 k4 using ho
  have key := tens_max (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) (A := fun _ => Mat R S)
    (fun _ Z => fockAct2 P Q R S Z) K
    (fun _ => by rw [← (MvPolynomial.basisMonomials _ ℂ).mk_eq_rank'']; exact Cardinal.mk_le_aleph0) k1
    (fun w Z x hx => fockSecondAction_matrixUnit_eq P Q R S ▸ k2 w Z x hx) (fun w N h h' => k3 w N h (fockSecondAction_matrixUnit_eq P Q R S ▸ h'))
    (LinearMap.ker β') (fun f w hf => by
      refine LinearMap.mem_ker.2 (PiTensorProduct.ext (MultilinearMap.ext fun t => ?_))
      let j : (InfinitePlace F → Formalism.BasicNotions.TH.Pol P Q R S) → Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] Tens F P Q R S := fun t =>
        (PiTensorProduct.tprod ℂ).toLinearMap t w
      have hj : ∀ t (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)) x, j t (L x) = atL w L (j t x) := fun t L x => (atL_tprod w L t x).symm
      have b1 : ∀ t Z x, j t (fockAct1 P Q R S Z x - (-c₁ w * Z.trace) • x) =
          atL w (fockAct1 P Q R S Z) (j t x) + (c₁ w * Z.trace) • j t x := fun t Z x => by
        rw [map_sub, map_smul, hj t, neg_mul, neg_smul, sub_neg_eq_add]
      have := k4 w ((β'.compl₂ (j t)).comp (j f))
        (fun Z x y => by rw [fockFirstAction_matrixUnit_eq]; exact (congrArg (fun z => β' z (j t y)) (b1 f Z x)).trans (sA w Z _ _))
        (fun Z x y => by
          rw [fockFirstAction_matrixUnit_eq]
          show β' (j f y) (j t _) = 0
          rw [b1, hβ', hs, ← hβ', sA, map_zero])
        (fun a b x y => by
          rw [fockSecondAction_matrixUnit_eq]
          show β' (j f _) (j t y) = _ * β' (j f x) (j t _)
          rw [hj f, hj t, sB, star_E, map_smul, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul])
        (f w) hf
      have h3 : β' (j f (f w)) (j t (t w)) = 0 := LinearMap.congr_fun this (t w)
      simpa [j] using h3)
    (N.comap φ) (fun x hx => hN (LinearMap.ext fun y => by
      obtain ⟨y, rfl⟩ := sj y
      exact LinearMap.congr_fun hx y))
    (fun w Z x hx => by
      have u : ∀ Z ∈ upq R S, atL w (fockAct2 P Q R S Z) x ∈ N.comap φ := fun Z hZ => by
        obtain ⟨γ, hγ, h⟩ := line_at hcm fr.2.2 h2 w hZ
        have : _ ∈ N.comap φ := hNs γ hγ (φ x) hx (φ _) (h x)
        simpa using (N.comap φ).sub_mem this ((N.comap φ).smul_mem (c₂ w * Z.trace) hx)
      obtain ⟨Z₁, a1, Z₂, a2, rfl, -⟩ := decomp Z
      show atL w (fockAct2 P Q R S _) x ∈ _
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
      exact add_mem (u Z₁ a1) (Submodule.smul_mem _ _ (u Z₂ a2)))
  rcases key with e | e
  · refine Or.inl fun x hx => ?_
    obtain ⟨x, rfl⟩ := sj x
    refine LinearMap.ext fun y => ?_
    obtain ⟨y, rfl⟩ := sj y
    exact LinearMap.congr_fun (e hx) y
  · refine Or.inr (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨x, rfl⟩ := sj x
    exact (e ▸ Submodule.mem_top : x ∈ N.comap φ)

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h0 : piInf (τ w) (z : AE F E) ≠ 0 := (z.isUnit.map (piInf (τ w))).ne_zero
  rw [zpow_sub₀ (div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0))]

theorem radMax_of (hF : FockEx) (hP : PolRange) (h1 : LieFirst) (h2 : LieSecond) : RadMax := by
  intro F E _ _ _ _ _ σ B a a' G X om om' t
  have par := PositivityTheory.RL.even_im_hermitian_sub F E σ B a a' G X om om' t
  have hg := t.geo
  have hb := t.base
  have hc := t.chars
  have od : ∀ w, One (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) (-(((B.mβ w - B.mα w : ℤ) : ℂ) / 2)) ∧
      One G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) (-(((B.mα w - B.mβ w : ℤ) : ℂ) / 2)) := fun w => by
    have k := hg.kappa w
    obtain ⟨m, hm⟩ := par w
    obtain ⟨m', hm'⟩ := hg.even
    have e1 := hg.lt
    have e2 := hg.eBig
    have e3 := hg.aBig
    have ek : (((B.mα w - B.mβ w).toNat : ℕ) : ℤ) = B.mα w - B.mβ w := Int.toNat_of_nonneg (by omega)
    have := one_data ⟨a, a', G.p, G.q, (B.mα w - B.mβ w).toNat⟩ (by constructor <;> simp only <;> omega)
    have ec : (((B.mα w - B.mβ w).toNat : ℕ) : ℂ) = ((B.mα w - B.mβ w : ℤ) : ℂ) := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) ek
    simp only [ec] at this
    refine ⟨?_, this.2⟩
    rw [show -(((B.mβ w - B.mα w : ℤ) : ℂ) / 2) = ((B.mα w - B.mβ w : ℤ) : ℂ) / 2 by push_cast; ring]
    exact this.1
  obtain ⟨A, C, Φ, fr, a1, a2, hΦ⟩ := PC.exists_fock hF (PositivityTheory.ThKG.pairV t)
  obtain ⟨A', C', Φ', fr', a1', a2', hΦ'⟩ := PC.exists_fock hF (PositivityTheory.ThKG.pairV' t)
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := t.weil
  have hwp' : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := t.weil'
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  obtain ⟨d', hd', hB1'⟩ := hwp'.2.1
  exact ⟨radMax_pair hb.cm fr hΦ.1 (hP F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr a1 a2 hΦ)
      (h1 F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
        (hasExp_div B.emb hc.expβ hc.expα))
      (h2 F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ)
      (fun w => by simp [map_ofNat]) fun w => (od w).1,
    radMax_pair hb.cm fr' hΦ'.1 (hP F E σ _ _ _ _ _ _ G.V' G.W G.M' B.ψ B.emb A' C' Φ' hb.cm hb.std fr' a1' a2' hΦ')
      (h1 F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co d' 1 Complex.I A' C' Φ' _ _ _ hb.cm hb.std fr' hΦ' hd' hB1'
        (hasExp_div B.emb hc.expα hc.expβ))
      (h2 F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A' C' Φ' _ X.α B.mα hb.cm hb.std fr' hΦ' hwp'.1 hc.expα)
      (fun w => by simp [map_ofNat]) fun w => (od w).2⟩

end PositivityTheory.ThKF.Unit

end
