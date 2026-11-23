import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.LiftSingleAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.AevalSingleZero

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open PositivityTheory.Rg.Fx

private noncomputable def cm {κ R R' : Type} [CommRing R] [CommRing R'] (φ : R → R') (P : MvPolynomial κ R) :
    MvPolynomial κ R' := ∑ β ∈ P.support, monomial β (φ (P.coeff β))

private theorem coeff_cm {κ R R' : Type} [CommRing R] [CommRing R'] {φ : R → R'} (h0 : φ 0 = 0)
    (P : MvPolynomial κ R) (β : κ →₀ ℕ) : (cm φ P).coeff β = φ (P.coeff β) := by
  classical
  rw [cm, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, h0]

private noncomputable def sb {κ κ' R T : Type} [CommRing R] [CommRing T] (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T)
    (ψ : R →+* T) : MvPolynomial κ R →+* MvPolynomial κ' T :=
  eval₂Hom (C.comp ψ) fun x => map a (h x)

private theorem sb_monomial {κ κ' R T : Type} [CommRing R] [CommRing T] (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T)
    (ψ : R →+* T) (β : κ →₀ ℕ) (r : R) :
    sb h a ψ (monomial β r) = C (ψ r) * map a (β.prod fun i k => h i ^ k) := by
  rw [sb, eval₂Hom_monomial, map_finsuppProd]
  simp only [map_pow, RingHom.comp_apply]

private theorem cm_sb {κ κ' R R' T T' : Type} [CommRing R] [CommRing R'] [CommRing T] [CommRing T']
    (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T) (a' : ℂ →+* T') (ψ : R →+* T) (ψ' : R' →+* T')
    (φ : R → R') (φ' : T → T') (h0 : φ 0 = 0) (h0' : φ' 0 = 0) (ha : ∀ x y, φ (x + y) = φ x + φ y)
    (ha' : ∀ x y, φ' (x + y) = φ' x + φ' y) (hl : ∀ x c, φ' (x * a c) = φ' x * a' c)
    (hc : ∀ r, φ' (ψ r) = ψ' (φ r)) (P : MvPolynomial κ R) :
    cm φ' (sb h a ψ P) = sb h a' ψ' (cm φ P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial β r =>
    have e : cm φ (monomial β r) = monomial β (φ r) := by
      ext γ
      rw [coeff_cm h0, coeff_monomial, coeff_monomial]
      split_ifs
      · rfl
      · exact h0
    rw [e, sb_monomial, sb_monomial]
    ext γ
    rw [coeff_cm h0', coeff_C_mul, coeff_C_mul, coeff_map, coeff_map, hl, hc]
  | add p q hp hq =>
    have e : cm φ (p + q) = cm φ p + cm φ q := by
      ext γ
      rw [coeff_add, coeff_cm h0, coeff_cm h0, coeff_cm h0, coeff_add, ha]
    rw [e, map_add, map_add, ← hp, ← hq]
    ext γ
    rw [coeff_add, coeff_cm h0', coeff_cm h0', coeff_cm h0', coeff_add, ha']

private theorem homog_eq {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) (s : Finset (ι →₀ ℕ)) (hs : p.support ⊆ s) :
    homog d p = ∑ α ∈ s, X none ^ (d - α.degree) * rename some (monomial α (p.coeff α)) := by
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [notMem_support_iff.mp hα]
  simp

private theorem homog_add {ι : Type} (d : ℕ) (p q : MvPolynomial ι ℂ) : homog d (p + q) = homog d p + homog d q := by
  classical
  rw [homog_eq d _ _ support_add, homog_eq d p _ Finset.subset_union_left, homog_eq d q _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_add, map_add, map_add, mul_add]

private theorem homog_monomial {ι : Type} (d : ℕ) (α : ι →₀ ℕ) (c : ℂ) :
    homog d (monomial α c) = X none ^ (d - α.degree) * rename some (monomial α c) := by
  classical
  rw [homog_eq d _ _ support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]

private theorem homog_mul {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) (c : ℂ) : homog d (p * C c) = homog d p * C c := by
  induction p using MvPolynomial.induction_on' with
  | monomial α r =>
    rw [homog_monomial, mul_comm, C_mul_monomial, homog_monomial, ← C_mul_monomial, map_mul, rename_C]
    ring
  | add p q hp hq => rw [add_mul, homog_add, homog_add, hp, hq, add_mul]

private theorem homog_rename {ι ι' : Type} (δ : ι → ι') (d : ℕ) (p : MvPolynomial ι ℂ) :
    homog d (rename δ p) = rename (Option.map δ) (homog d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α r =>
    rw [homog_monomial, map_mul, map_pow, rename_X, rename_rename]
    conv_lhs => rw [rename_monomial, homog_monomial, ← rename_monomial, rename_rename, Finsupp.degree_mapDomain]
    rfl
  | add p q hp hq => rw [map_add, homog_add, homog_add, hp, hq, map_add]

private theorem piece_mul {ι : Type} [Fintype ι] (k : ℕ) (f : EP ι) (c : ℂ) :
    piece k (f * algebraMap ℂ (EP ι) c) = piece k f * C c := by
  obtain ⟨ha, h0, hs⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι k
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, h0, zero_mul]
  | add f g hf hg => rw [add_mul, ha, ha, hf, hg, add_mul]
  | single v p =>
    have e : algebraMap ℂ (EP ι) c = AddMonoidAlgebra.single 0 (C c) := rfl
    rw [e, AddMonoidAlgebra.single_mul_single, add_zero, hs, hs, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm p, homogeneousComponent_C_mul]
    ring

private theorem lift_alg {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A) (τ : Multiplicative (ι → ℝ) →* A) (c : ℂ) :
    lift x τ (algebraMap ℂ (EP ι) c) = algebraMap ℂ A c := by
  have e : algebraMap ℂ (EP ι) c = AddMonoidAlgebra.single 0 (C c) := rfl
  rw [e]
  simp [lift, AddMonoidAlgebra.liftNCRingHom]

private theorem ren_ren {ι ι' ι'' : Type} [Fintype ι] [Fintype ι'] [Fintype ι''] [DecidableEq ι'] [DecidableEq ι'']
    (δ : ι → ι') (δ' : ι' → ι'') (f : EP ι) : ren δ' (ren δ f) = ren (δ' ∘ δ) f := by
  unfold ren
  rw [(UpperTheory.ConvolutionTheory.FX.subst ι ι' _ _ f).2]
  congr 2
  · funext i
    simp
  · ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (δ i)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

private theorem ev_ren {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι']
    (δ : ι → ι') (L : ι' → ℂ) (f : EP ι) : ev L (ren δ f) = ev (fun i => L (δ i)) f := by
  unfold ren
  rw [(UpperTheory.ConvolutionTheory.FX.subst ι ι' _ _ f).1]
  congr 2
  funext i
  simp [apply_ite]

private theorem eval_powE {n : ℕ} (f : ℕ) (i : Fin n) (s : Multiset ℂ) (hs : s.card = n) :
    eval (fun j : Fin n => s.esymm (j + 1)) (powE f i) = (s.map (· ^ f)).esymm (i + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin n → ℂ, s = Finset.univ.val.map a := by
    induction s using Quotient.inductionOn with
    | h l =>
      have hl : l.length = n := by simpa using hs
      subst hl
      refine ⟨l.get, ?_⟩
      rw [Fin.univ_val_map, List.ofFn_get]
      rfl
  have h1 : aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) (powE f i)
      = expand f (esymm (Fin n) ℂ (i + 1)) := by
    rw [← esymmAlgHom_apply]
    have := congrArg Subtype.val
      ((esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
        ⟨expand f (esymm (Fin n) ℂ (i + 1)), fun w => by rw [rename_expand, esymm_isSymmetric]⟩)
    exact this
  have h2 := congrArg (aeval a) h1
  rw [← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply] at h2
  have h3 : (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).comp (expand f) = aeval fun r => a r ^ f := by
    apply MvPolynomial.algHom_ext
    intro r
    simp
  rw [h3] at h2
  simp only [aeval_esymm_eq_multiset_esymm] at h2
  rw [Multiset.map_map, ← coe_aeval_eq_eval]
  exact h2

private theorem map_eq_cm {κ R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (P : MvPolynomial κ R) :
    map φ P = cm φ P := by
  ext γ
  rw [coeff_map, coeff_cm (map_zero φ)]

private theorem map_sb {κ κ' R R' T T' : Type} [CommRing R] [CommRing R'] [CommRing T] [CommRing T']
    (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T) (a' : ℂ →+* T') (ψ : R →+* T) (ψ' : R' →+* T')
    (φ : R →+* R') (φ' : T →+* T') (hl : ∀ c, φ' (a c) = a' c)
    (hc : ∀ r, φ' (ψ r) = ψ' (φ r)) (P : MvPolynomial κ R) :
    map φ' (sb h a ψ P) = sb h a' ψ' (map φ P) := by
  rw [map_eq_cm, map_eq_cm]
  exact cm_sb h a a' ψ ψ' φ φ' (map_zero _) (map_zero _) (map_add _) (map_add _)
    (fun x c => by rw [map_mul, hl]) hc P

theorem UpperTheory.ConvolutionTheory.Ci.kfBc :
    KfBc := by
  classical
  intro F E _ _ _ _ _ n SE SF hS Φ G hΦ hG
  let res : Ix E n → Ix F n := fun x => (x.1.comp (algebraMap F E), x.2)
  let h : Pl E × Fin n → MvPolynomial (Pl F × Fin n) ℂ := fun x =>
    rename (fun i => (x.1.under (𝓞 F), i)) (powE (resDeg F x.1) x.2)
  refine ⟨sb h (algebraMap ℂ _) (ren res) Φ, fun k => sb h C (rename res).toRingHom (G k), ⟨fun w => ?_, ?_⟩,
    fun k => ?_, fun d => ?_, fun L' t' ht => ?_⟩
  · have h1 := hΦ.1 fun τ => w (τ.comp (algebraMap F E))
    refine (map_sb h (algebraMap ℂ _) (algebraMap ℂ _) (ren res) (ren res)
      (ren fun x : Ix E n => (x.1, w (x.1.comp (algebraMap F E)) x.2)) _ ?_ ?_ Φ).trans (by rw [h1])
    · intro c
      exact lift_alg _ _ c
    · intro r
      rw [ren_ren, ren_ren]
      rfl
  · intro y hy
    have e : sb h (algebraMap ℂ _) (ren res) Φ =
        bind₁ (fun x => map (algebraMap ℂ (EP (Ix F n))) (h x)) (map (ren res) Φ) := by
      rw [bind₁, aeval_def, eval₂_map]
      rfl
    rw [e] at hy
    obtain ⟨y', hy', hy2⟩ := mem_vars_bind₁ _ _ hy
    obtain ⟨i, -, rfl⟩ := mem_vars_rename _ _ (vars_map _ _ hy2)
    exact fun hh => hΦ.2 y' (vars_map _ _ hy') ((hS _).2 hh)
  · obtain ⟨ha, h0, -⟩ := UpperTheory.ConvolutionTheory.FX.piece_add (Ix E n) k
    obtain ⟨ha', h0', -⟩ := UpperTheory.ConvolutionTheory.FX.piece_add (Ix F n) k
    have h1 := hG k
    refine Eq.trans ?_ (cm_sb h (algebraMap ℂ _) C (ren res) (rename res).toRingHom (piece k) (piece k) h0 h0' ha ha'
      (piece_mul k) (fun r => UpperTheory.ConvolutionTheory.FX.piece_ren _ r _ res k) Φ).symm
    refine (map_sb h C C (rename res).toRingHom (rename res).toRingHom (aeval blockE).toRingHom _ ?_ ?_ _).trans
      (by rw [h1]; rfl)
    · intro c
      simp
    · intro r
      have e : (aeval (blockE (τ := F →+* ℂ) (n := n))).comp (rename res) =
          (rename res).comp (aeval (blockE (τ := E →+* ℂ) (n := n))) := by
        apply MvPolynomial.algHom_ext
        intro y
        simp only [AlgHom.comp_apply, rename_X, aeval_X, blockE, rename_rename]
        rfl
      exact DFunLike.congr_fun e r
  · unfold trunc
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact cm_sb h C C (rename res).toRingHom (rename (Option.map res)).toRingHom (homog d) (homog d)
      (by simp [homog]) (by simp [homog]) (homog_add d) (homog_add d) (homog_mul d) (homog_rename res d) (G k)
  · rw [← RingHom.comp_apply]
    refine hom_congr_vars (p₁ := Φ) (p₂ := Φ) ?_ ?_ rfl
    · refine RingHom.ext fun f => ?_
      simp only [evK, sb, RingHom.comp_apply, eval₂Hom_C]
      exact ev_ren res L' f
    · intro y hy _
      have h1 := eval_powE (resDeg F y.1) y.2 _ (ht _ fun hh => hΦ.2 y hy ((hS _).2 hh))
      simp only [evK, sb, h, RingHom.comp_apply, eval₂Hom_X', coe_eval₂Hom, eval₂_map, eval₂_rename, eval₂_X]
      rw [hval, bcSat, ← h1]
      have hc : (ev L').comp (algebraMap ℂ (EP (Ix F n))) = RingHom.id ℂ :=
        RingHom.ext fun c => lift_alg _ _ c
      rw [hc]
      rfl
