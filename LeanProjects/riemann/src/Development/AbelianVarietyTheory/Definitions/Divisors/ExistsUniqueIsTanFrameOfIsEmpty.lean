import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open TrivSqZeroExt hiding map lift
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Der

variable {K : Type} [Field K] [Algebra c.F K] {K₀ : Type} [CommRing K₀] [Algebra c.F K₀]

def IsDef (y : FrPt Xo c K) (v : FrPt Xo c (DualNumber K)) : Prop := FrMap (red c K) v y

def der (φ : K₀ →ₐ[c.F] K) (v : FrPt Xo c (DualNumber K)) (s : RulK Xo c K₀) : K :=
  (val ((cst c K).comp φ) v s).snd

theorem der_add (φ : K₀ →ₐ[c.F] K) (v : FrPt Xo c (DualNumber K)) (s s' : RulK Xo c K₀) :
    der φ v (s + s') = der φ v s + der φ v s' := by
  simp [der]

theorem der_smul (φ : K₀ →ₐ[c.F] K) (v : FrPt Xo c (DualNumber K)) (a : K₀) (s : RulK Xo c K₀) :
    der φ v (a • s) = φ a * der φ v s := by
  simp [der, val_smul]

theorem der_sum (φ : K₀ →ₐ[c.F] K) (v : FrPt Xo c (DualNumber K)) {ι : Type} (I : Finset ι) (a : ι → K₀)
    (s : ι → RulK Xo c K₀) : der φ v (∑ i ∈ I, a i • s i) = ∑ i ∈ I, φ (a i) * der φ v (s i) := by
  induction I using Finset.induction_on with
  | empty => simp [der]
  | insert i I hi h => rw [Finset.sum_insert hi, Finset.sum_insert hi, der_add, der_smul, h]

theorem IsDef.val_eq {y : FrPt Xo c K} {v : FrPt Xo c (DualNumber K)} (h : IsDef y v) (φ : K₀ →ₐ[c.F] K)
    {e : Ix Dw → ℤ} {s : RulK Xo c K₀} (hs : s ∈ secK Xo c K₀ e) :
    val ((cst c K).comp φ) v s = inl (val φ y s) + inr (der φ v s) := by
  rw [val_frMap hs (φ := (cst c K).comp φ) (χ := φ) (fun _ => rfl) h]
  exact (inl_fst_add_inr_snd_eq _).symm

theorem IsDef.der_mul {y : FrPt Xo c K} {v : FrPt Xo c (DualNumber K)} (h : IsDef y v) (φ : K₀ →ₐ[c.F] K)
    {e e' : Ix Dw → ℤ} {f g : Rul Xo c} (hf : f ∈ secZ Xo c e) (hg : g ∈ secZ Xo c e') :
    der φ v (1 ⊗ₜ (f * g)) = evR Xo c f y * der φ v (1 ⊗ₜ g) + evR Xo c g y * der φ v (1 ⊗ₜ f) := by
  have e1 : evR Xo c (f * g) v = evR Xo c f v * evR Xo c g v := evalAt_mul _ _ f g v
  simp only [der, val_tmul, map_one, one_mul, e1, evR_frMap hf.1 h, evR_frMap hg.1 h, DualNumber.snd_mul]
  simp [mul_comm]

def IsShift (N : FIx Dw → K) (v v' : FrPt Xo c (DualNumber K)) : Prop := FrChg (unip K N) (unip₀ K N) v v'

def IsVert (y : FrPt Xo c K) (N : FIx Dw → K) (v : FrPt Xo c (DualNumber K)) : Prop :=
  ∃ y₀, FrMap (cst c K) y y₀ ∧ IsShift N y₀ v

theorem existsUnique_isShift (N : FIx Dw → K) (v : FrPt Xo c (DualNumber K)) : ∃! v', IsShift N v v' :=
  existsUnique_frChg E H Dw l Xo c _ v _ (isUnit_unip₀ N).unit (isUnit_det_unip N)

theorem isShift_zero (v : FrPt Xo c (DualNumber K)) : IsShift (0 : FIx Dw → K) v v := by
  have := (frChg_calculus E H Dw l Xo c _).2.1 v
  unfold IsShift
  convert this using 2 with τ
  · ext i j <;> by_cases h : i = j <;> simp [unip, Matrix.one_apply, h]
  · simp [unip₀]

theorem IsShift.unique {N N' : FIx Dw → K} {v v' : FrPt Xo c (DualNumber K)} (h : IsShift N v v')
    (h' : IsShift N' v v') : N = N' := by
  obtain ⟨h1, h2⟩ := (frChg_exists_unique E H Dw l Xo c _ v v').2 _ _ _ _ h h'
  funext k
  rcases k with _ | ⟨σ, i, j⟩
  · simpa [unip₀] using congrArg snd h2
  · simpa [unip] using congrArg (fun g => (g σ i j).snd) h1

theorem IsDef.shift {y : FrPt Xo c K} {N : FIx Dw → K} {v v' : FrPt Xo c (DualNumber K)} (h : IsDef y v)
    (h' : IsShift N v v') : IsDef y v' := by
  refine (frMap_iff_frChg h' h).2 ?_
  convert (frChg_calculus E H Dw l Xo c _).2.1 y using 2 with τ
  · ext i j; simp [unip]
  · simp [unip₀]

theorem IsDef.exists_isShift {y : FrPt Xo c K} {v v' : FrPt Xo c (DualNumber K)} (h : IsDef y v) (h' : IsDef y v')
    (hx : v'.x = v.x) : ∃ N : FIx Dw → K, IsShift N v v' := by
  obtain ⟨g, a, -, hc⟩ := (frChg_exists_unique E H Dw l Xo c _ v v').1 hx
  obtain ⟨h1, h2⟩ := (frChg_exists_unique E H Dw l Xo c _ y y).2 _ _ _ _ ((frMap_iff_frChg hc h).1 h')
    ((frChg_calculus E H Dw l Xo c _).2.1 y)
  refine ⟨fun k => k.elim (a : DualNumber K).snd fun q => (g q.1 q.2.1 q.2.2).snd, ?_⟩
  unfold IsShift
  convert hc using 1
  · funext τ
    ext i j
    · simpa [unip] using (congrArg (fun g => g τ i j) h1).symm
    · simp [unip]
  · ext
    · simpa [unip₀] using h2.symm
    · simp [unip₀]

theorem isDef_const {y : FrPt Xo c K} {y₀ : FrPt Xo c (DualNumber K)} (h : FrMap (cst c K) y y₀) : IsDef y y₀ :=
  frMap_of_comp h (frMap_id y) fun _ => rfl

theorem IsVert.isDef {y : FrPt Xo c K} {N : FIx Dw → K} {v : FrPt Xo c (DualNumber K)} (h : IsVert y N v) :
    IsDef y v := h.elim fun _ k => (isDef_const k.1).shift k.2

theorem existsUnique_isVert (y : FrPt Xo c K) (N : FIx Dw → K) : ∃! v, IsVert y N v := by
  obtain ⟨y₀, h₀⟩ := exists_frMap (cst c K) y
  obtain ⟨v, hv, hu⟩ := existsUnique_isShift N y₀
  exact ⟨v, ⟨y₀, h₀, hv⟩, fun v' ⟨y₁, h₁, h'⟩ => hu v' (frMap_unique h₁ h₀ ▸ h')⟩

theorem IsVert.unique {y : FrPt Xo c K} {N N' : FIx Dw → K} {v : FrPt Xo c (DualNumber K)} (h : IsVert y N v)
    (h' : IsVert y N' v) : N = N' := by
  obtain ⟨y₀, h₀, h⟩ := h
  obtain ⟨y₁, h₁, h'⟩ := h'
  exact h.unique (frMap_unique h₁ h₀ ▸ h')

theorem exists_isVert_iff {y : FrPt Xo c K} {v : FrPt Xo c (DualNumber K)} :
    (∃ N : FIx Dw → K, IsVert y N v) ↔ IsDef y v ∧ v.x = spMap (cst c K).toRingHom ≫ y.x := by
  refine ⟨fun ⟨N, h⟩ => ⟨h.isDef, h.elim fun _ k => k.2.1.trans k.1.1⟩, fun ⟨h, hx⟩ => ?_⟩
  obtain ⟨y₀, h₀⟩ := exists_frMap (cst c K) y
  obtain ⟨N, hN⟩ := (isDef_const h₀).exists_isShift h (hx.trans h₀.1.symm)
  exact ⟨N, y₀, h₀, hN⟩

theorem der_dir {ι : Type} [Fintype ι] (φ : K₀ →ₐ[c.F] K) {W : FrPt Xo c (TrivSqZeroExt K (ι → K))} {m : ι → K}
    {v : FrPt Xo c (DualNumber K)} (h : FrMap (dir c m) W v) {e : Ix Dw → ℤ} {s : RulK Xo c K₀}
    (hs : s ∈ secK Xo c K₀ e) :
    der φ v s = ∑ k, (val ((inlAlgHom c.F K (ι → K)).comp φ) W s).snd k * m k := by
  rw [der, val_frMap hs (φ := (inlAlgHom c.F K (ι → K)).comp φ) (fun a => by ext <;> simp) h, snd_dir]

theorem IsDef.der_shift {y : FrPt Xo c K} {N : FIx Dw → K} {v v' : FrPt Xo c (DualNumber K)} (h : IsDef y v)
    (h' : IsShift N v v') {z : FIx Dw → FrPt Xo c (DualNumber K)} (hz : ∀ k, IsVert y (Pi.single k (1 : K)) (z k))
    (φ : K₀ →ₐ[c.F] K) {e : Ix Dw → ℤ} {s : RulK Xo c K₀} (hs : s ∈ secK Xo c K₀ e) :
    der φ v' s = der φ v s + ∑ k, N k * der φ (z k) s := by
  let emb : DualNumber K →ₐ[c.F] TrivSqZeroExt K (Option (FIx Dw) → K) :=
    (TrivSqZeroExt.map (LinearMap.single K (fun _ : Option (FIx Dw) => K) none)).restrictScalars c.F
  have e1 : ∀ a, (emb a).fst = a.fst := fun a => fst_map _ a
  have e2 : ∀ a, (emb a).snd = Pi.single none a.snd := fun a => snd_map _ a
  obtain ⟨W₀, hW₀⟩ := exists_frMap emb v
  let n : FIx Dw → Option (FIx Dw) → K := fun k => Pi.single (some k) 1
  obtain ⟨W, hW, -⟩ := existsUnique_frChg E H Dw l Xo c _ W₀ _ (isUnit_unip₀ (K := K) n).unit (isUnit_det_unip n)
  have key : ∀ (m : Option (FIx Dw) → K) (z₀ z : FrPt Xo c (DualNumber K)), FrMap (dir c m) W₀ z₀ →
      IsShift (fun k => m (some k)) z₀ z → FrMap (dir c m) W z := fun m z₀ z k₀ k => by
    refine (frMap_iff_frChg hW k₀).2 ?_
    unfold IsShift at k
    convert k using 2 with τ
    · ext i j <;> simp [unip, n, Pi.single_apply]
    · ext <;> simp [unip₀, n, Pi.single_apply]
  have k1 : ∀ m : Option (FIx Dw) → K, m none = 1 → FrMap (dir c m) W₀ v := fun m hm =>
    frMap_of_comp hW₀ (frMap_id v) fun a => by ext <;> simp [e1, e2, Pi.single_apply, hm]
  rw [der_dir φ (key (fun k => k.elim 1 N) v v' (k1 _ rfl) h') hs,
    der_dir φ (key (Pi.single none 1) v v (k1 _ (by simp)) (by
      convert isShift_zero v using 2; simp)) hs, Fintype.sum_option]
  congr 1
  · simp [Pi.single_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨y₀, h₀, hk⟩ := hz k
  rw [der_dir φ (key (Pi.single (some k) 1) y₀ (z k)
    (frMap_of_comp hW₀ (frMap_comp (χ := (cst c K).comp (red c K)) h h₀ fun _ => rfl) fun a => by
      ext <;> simp [e1, e2, Pi.single_apply]) (by
      convert hk using 2; simp [Pi.single_apply])) hs]
  simp [Pi.single_apply, mul_comm]

def oneAddEps : Multiplicative K →* (DualNumber K)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => inl 1 + inr x.toAdd
      map_one' := by simp
      map_mul' := fun x y => by ext <;> simp [add_comm] }

def diagOf (N : FIx Dw → K) : Ix Dw → K
  | none => N none
  | some q => N (some ⟨q.1, q.2, q.2⟩)

theorem IsVert.der_eq_weight {y : FrPt Xo c K} {N : FIx Dw → K} {v : FrPt Xo c (DualNumber K)}
    (h : IsVert y N v) (hN : ∀ σ i j, i < j → N (some ⟨σ, i, j⟩) = 0) (φ : K₀ →ₐ[c.F] K) {e : Ix Dw → ℤ}
    {s : RulK Xo c K₀} (hs : s ∈ secK Xo c K₀ e) : der φ v s = (∑ k, (e k : K) * diagOf N k) * val φ y s := by
  obtain ⟨y₀, h₀, h⟩ := h
  have hb : FrBor (fun k => oneAddEps (Multiplicative.ofAdd (diagOf N k))) y₀ v :=
    (frBor_iff_frChg _ _ _).2 ⟨unip K N, fun σ i j hij => by simp [unip, hN σ i j hij, hij.ne],
      fun _ _ => by simp [unip, oneAddEps, diagOf], h⟩
  rw [der, val_frBor hs _ hb, val_frMap hs (φ := φ) (fun _ => rfl) h₀, DualNumber.snd_mul]
  simp only [← map_zpow, ← map_prod, ← ofAdd_zsmul, ← ofAdd_sum, zsmul_eq_mul]
  generalize ∑ k, (e k : K) * diagOf N k = a
  simp [oneAddEps]

theorem IsVert.der_of_triangular {y : FrPt Xo c K} {N : FIx Dw → K} {v : FrPt Xo c (DualNumber K)}
    (h : IsVert y N v) (hN : ∀ σ i j, i < j → N (some ⟨σ, i, j⟩) = 0) (φ : K₀ →ₐ[c.F] K) (e : Ix Dw → ℤ) :
    ∃ a : K, ∀ s ∈ secK Xo c K₀ e, der φ v s = a * val φ y s :=
  ⟨_, fun _ hs => h.der_eq_weight hN φ hs⟩

end Der

section Index

def IsHalf (Φ : Finset (E →+* ℂ)) : Prop := ∀ τ, τ ∈ Φ ↔ conjEmb τ ∉ Φ

variable (H) in

def psiSet : Finset (E →+* ℂ) := Finset.univ.filter fun τ => τ (H.rt : E) = H.rt0

variable (H) in

theorem isHalf_psiSet : IsHalf (psiSet H) := fun τ => by
  simp only [psiSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => conj_not_mem ⟨τ, h⟩, fun h => by_contra fun h' => h (conj_mem h')⟩

variable (Dw)

abbrev HIx (Φ : Finset (E →+* ℂ)) : Type := Σ τ : Φ, Fin (Dw.mult (conjEmb τ.1)) × Fin (Dw.mult τ.1)

abbrev VIx : Type := Σ σ : E →+* ℂ, {q : Fin (Dw.mult σ) × Fin (Dw.mult σ) // q.1 < q.2}

abbrev TIx (Φ : Finset (E →+* ℂ)) : Type := HIx Dw Φ ⊕ VIx Dw

def dimFlag : ℕ := Module.finrank ℚ E / 2 * (Dw.p + Dw.q).choose 2

variable {Dw}

def VIx.toF (k : VIx Dw) : FIx Dw := some ⟨k.1, k.2.1⟩

theorem VIx.toF_injective : Function.Injective (VIx.toF (Dw := Dw)) := by
  rintro ⟨σ, q, hq⟩ ⟨σ', q', hq'⟩ e
  obtain ⟨rfl, e⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
  obtain rfl := eq_of_heq e
  rfl

theorem IsHalf.sum_univ {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) (g : (E →+* ℂ) → ℕ) :
    ∑ σ, g σ = ∑ τ ∈ Φ, (g τ + g (conjEmb τ)) := by
  rw [Finset.sum_add_distrib, ← Finset.sum_add_sum_compl Φ]
  congr 1
  refine Finset.sum_bij' (fun σ _ => conjEmb σ) (fun σ _ => conjEmb σ) (fun σ hσ => ?_) (fun σ hσ => ?_)
    (fun σ _ => conjEmb_conjEmb σ) (fun σ _ => conjEmb_conjEmb σ) fun σ _ => by rw [conjEmb_conjEmb]
  · rw [h, conjEmb_conjEmb]; exact Finset.mem_compl.1 hσ
  · exact Finset.mem_compl.2 ((h σ).1 hσ)

theorem IsHalf.card {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) : Φ.card = Module.finrank ℚ E / 2 := by
  have := h.sum_univ fun _ => 1
  simp only [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, smul_eq_mul] at this
  omega

theorem mult_conj (τ : E →+* ℂ) : (Dw.mult τ = Dw.p ∧ Dw.mult (conjEmb τ) = Dw.q) ∨
    (Dw.mult τ = Dw.q ∧ Dw.mult (conjEmb τ) = Dw.p) := by
  by_cases h : τ (H.rt : E) = H.rt0
  · exact .inl ⟨if_pos h, if_neg (conj_not_mem ⟨τ, h⟩)⟩
  · exact .inr ⟨if_neg h, if_pos (conj_mem h)⟩

theorem card_HIx {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) : Fintype.card (HIx Dw Φ) = Dw.dim := by
  have : ∀ τ : Φ, Dw.mult (conjEmb τ.1) * Dw.mult τ.1 = Dw.p * Dw.q := fun τ => by
    rcases mult_conj (Dw := Dw) τ.1 with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]
    exact mul_comm _ _
  simp [Fintype.card_sigma, this, h.card, Datum.dim, mul_assoc]

theorem card_VIx : Fintype.card (VIx Dw) = Module.finrank ℚ E / 2 * (Dw.p.choose 2 + Dw.q.choose 2) := by
  have h1 : ∀ n : ℕ, Fintype.card {q : Fin n × Fin n // q.1 < q.2} = n.choose 2 := fun n => by
    rw [Fintype.card_subtype]
    simpa using Fintype.card_product_filter_lt (α := Fin n)
  have h2 : ∀ τ, (Dw.mult τ).choose 2 + (Dw.mult (conjEmb τ)).choose 2 = Dw.p.choose 2 + Dw.q.choose 2 := fun τ => by
    rcases mult_conj (Dw := Dw) τ with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]
    exact add_comm _ _
  simp only [Fintype.card_sigma, h1]
  rw [(isHalf_psiSet H).sum_univ]
  simp [h2, (isHalf_psiSet H).card]

theorem card_TIx {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) : Fintype.card (TIx Dw Φ) = dimFlag Dw := by
  have : (Dw.p + Dw.q).choose 2 = Dw.p * Dw.q + (Dw.p.choose 2 + Dw.q.choose 2) := by
    induction Dw.q with
    | zero => simp
    | succ n ih => rw [← add_assoc, Nat.choose_succ_succ' (Dw.p + n), ih, Nat.choose_succ_succ' n]; simp; ring
  rw [Fintype.card_sum, card_HIx h, card_VIx, dimFlag, this, Datum.dim]
  ring

variable (Dw)

def kap : Weight Dw := fun _ j =>
  if (j : ℕ) < Dw.p then (Dw.q : ℤ) + 2 * ((j : ℕ) + 1) - Dw.p - 1
  else -(Dw.p : ℤ) + 2 * (((j : ℕ) : ℤ) - Dw.p + 1) - Dw.q - 1

def detTanEx : Ix Dw → ℤ
  | none => 0
  | some k => ((Finset.Iio k.2).card : ℤ) - (Finset.Ioi k.2).card + Dw.mult (conjEmb k.1)

theorem exOf_kap : exOf Dw (kap Dw) 0 = detTanEx Dw := by
  funext k
  rcases k with _ | ⟨σ, i⟩
  · rfl
  show (wtOf Dw (kap Dw) 0).1 (σ, i) = _
  have hi := i.2
  simp only [detTanEx, Fin.card_Iio, Fin.card_Ioi]
  by_cases h : σ (H.rt : E) = H.rt0
  · have a : Dw.mult σ = Dw.p := if_pos h
    have b : Dw.mult (conjEmb σ) = Dw.q := if_neg (conj_not_mem ⟨σ, h⟩)
    have hp : (i : ℕ) < Dw.p := by omega
    rw [wtOf_big _ 0 ⟨σ, h⟩ i hp]
    simp only [kap, hp, if_true]
    omega
  · have a : Dw.mult σ = Dw.q := if_neg h
    have b : Dw.mult (conjEmb σ) = Dw.p := if_pos (conj_mem h)
    have e := wtOf_small (kap Dw) 0 ⟨conjEmb σ, conj_mem h⟩ i (a ▸ hi)
    simp only [conjEmb_conjEmb] at e
    rw [e]
    simp only [kap, add_lt_iff_neg_left, Nat.not_lt_zero, if_false]
    omega

example (hp : Dw.p = 1) (hq : Dw.q = 1) (τ : Psi H) :
    kap Dw τ ⟨0, by omega⟩ = 1 ∧ kap Dw τ ⟨1, by omega⟩ = -1 := by
  simp [kap, hp, hq]

example (hp : Dw.p = 2) (hq : Dw.q = 0) (τ : Psi H) :
    kap Dw τ ⟨0, by omega⟩ = -1 ∧ kap Dw τ ⟨1, by omega⟩ = 1 := by
  simp [kap, hp, hq]

end Index

section KS

open DeRham Cris

def IsKSRow {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A']
    {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (epsRed R) i) (ψ : LinearMap.BilinForm R (HdR A)) {J : Type}
    (hb : J → HdR A) (a : J) (w : epsR R ⟶ A) : Prop :=
  ∃ f ∈ Fil A, (∀ k, ψ f (hb k) = if k = a then 1 else 0) ∧ IsKSValue h f w

variable {K : Type} [Field K] [Algebra c.F K] {K₀ : Type} [CommRing K₀] [Algebra c.F K₀]

def IsTanX (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X) : Prop :=
  x' ≫ Xo.s = sOf c (DualNumber K) ∧ spMap (red c K).toRingHom ≫ x' = y.x

theorem IsDef.isTanX {y : FrPt Xo c K} {v : FrPt Xo c (DualNumber K)} (h : IsDef y v) : IsTanX y v.x :=
  ⟨v.x_over, h.1.symm⟩

def IsKS (Φ : Finset (E →+* ℂ)) (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X) (M : HIx Dw Φ → K) : Prop :=
  ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A')
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (epsRed K) i) (ψ : LinearMap.BilinForm K (HdR A))
    (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A),
    IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧
    IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
    (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧
    ∀ (τ : Φ) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, IsLieComb (fun b => M ⟨τ, a, b⟩) (ub τ.1) w ∧
      IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w

def KSIso (Φ : Finset (E →+* ℂ)) (y : FrPt Xo c K) : Prop :=
  ∃ X : Sp (TrivSqZeroExt K (HIx Dw Φ → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧
    spMap (fstHom c.F K (HIx Dw Φ → K)).toRingHom ≫ X = y.x ∧
    ∀ x', IsTanX y x' → (∃! M : HIx Dw Φ → K, x' = spMap (dir c M).toRingHom ≫ X) ∧
      ∀ M : HIx Dw Φ → K, IsKS Φ y x' M ↔ x' = spMap (dir c M).toRingHom ≫ X

theorem KSIso.existsUnique {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} (h : KSIso Φ y) {x' : Sp (DualNumber K) ⟶ Xo.X}
    (hx : IsTanX y x') : ∃! M, IsKS Φ y x' M := by
  obtain ⟨X, -, -, h⟩ := h
  simpa only [(h x' hx).2] using (h x' hx).1

theorem KSIso.injective {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} (h : KSIso Φ y) {x' x'' : Sp (DualNumber K) ⟶ Xo.X}
    (hx : IsTanX y x') (hx' : IsTanX y x'') {M : HIx Dw Φ → K} (k : IsKS Φ y x' M) (k' : IsKS Φ y x'' M) :
    x' = x'' := by
  obtain ⟨X, -, -, h⟩ := h
  rw [((h x' hx).2 M).1 k, ((h x'' hx').2 M).1 k']

theorem KSIso.exists_universal {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} (h : KSIso Φ y) :
    ∃ (W : FrPt Xo c (TrivSqZeroExt K (HIx Dw Φ → K))) (z : (HIx Dw Φ → K) → FrPt Xo c (DualNumber K)),
      ∀ M, FrMap (dir c M) W (z M) ∧ IsDef y (z M) ∧ IsKS Φ y (z M).x M := by
  obtain ⟨X, h1, h2, h⟩ := h
  obtain ⟨W, rfl, hW⟩ := exists_lift y X h1 h2
  choose z hz using fun M : HIx Dw Φ → K => exists_frMap (dir c M) W
  have hd : ∀ M, IsDef y (z M) := fun M => frMap_of_comp (hz M) hW fun a => fst_dir (c := c) M a
  exact ⟨W, z, fun M => ⟨hz M, hd M, ((h _ (hd M).isTanX).2 M).2 (hz M).1⟩⟩

def IsTanFrame (Φ : Finset (E →+* ℂ)) (y : FrPt Xo c K) (v : TIx Dw Φ → FrPt Xo c (DualNumber K)) : Prop :=
  (∀ k : HIx Dw Φ, IsDef y (v (.inl k)) ∧ IsKS Φ y (v (.inl k)).x (Pi.single k 1)) ∧
    ∀ k : VIx Dw, IsVert y (Pi.single k.toF (1 : K)) (v (.inr k))

theorem IsTanFrame.isDef {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} {v : TIx Dw Φ → FrPt Xo c (DualNumber K)}
    (h : IsTanFrame Φ y v) : ∀ k, IsDef y (v k)
  | .inl k => (h.1 k).1
  | .inr k => (h.2 k).isDef

theorem KSIso.exists_isTanFrame {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} (h : KSIso Φ y) :
    ∃ v, IsTanFrame Φ y v := by
  obtain ⟨W, z, hz⟩ := h.exists_universal
  choose w hw using fun k : VIx Dw => (existsUnique_isVert y (Pi.single k.toF (1 : K))).exists
  exact ⟨Sum.elim (fun k => z (Pi.single k 1)) w, fun k => (hz _).2, hw⟩

theorem existsUnique_isTanFrame_of_isEmpty {Φ : Finset (E →+* ℂ)} [IsEmpty (HIx Dw Φ)] (y : FrPt Xo c K) :
    ∃! v, IsTanFrame Φ y v := by
  choose w hw hu using fun k : VIx Dw => existsUnique_isVert y (Pi.single k.toF (1 : K))
  refine ⟨Sum.elim isEmptyElim w, ⟨isEmptyElim, hw⟩, fun v hv => funext fun k => ?_⟩
  rcases k with k | k
  · exact isEmptyElim k
  · exact hu k _ (hv.2 k)

theorem isEmpty_HIx (Φ : Finset (E →+* ℂ)) (h : Dw.p = 0 ∨ Dw.q = 0) : IsEmpty (HIx Dw Φ) :=
  ⟨fun ⟨τ, a, b⟩ => by
    have ha := a.2
    have hb := b.2
    rcases mult_conj (Dw := Dw) τ.1 with ⟨k, k'⟩ | ⟨k, k'⟩ <;> omega⟩

theorem sum_FIx (g : FIx Dw → K) :
    ∑ k, g k = ∑ k : VIx Dw, g k.toF + ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range VIx.toF), g k := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => k ∈ Set.range VIx.toF)]
  congr 1
  rw [← Finset.sum_image (f := g) fun a _ b _ e => VIx.toF_injective e]
  congr 1
  ext k
  simp

theorem IsDef.der_shift_frame {y : FrPt Xo c K} {v : VIx Dw → FrPt Xo c (DualNumber K)}
    (hv : ∀ k : VIx Dw, IsVert y (Pi.single k.toF (1 : K)) (v k)) {N : FIx Dw → K}
    {w w' : FrPt Xo c (DualNumber K)} (h : IsDef y w) (h' : IsShift N w w') (φ : K₀ →ₐ[c.F] K) (e : Ix Dw → ℤ) :
    ∃ a : K, ∀ s ∈ secK Xo c K₀ e,
      der φ w' s = der φ w s + ∑ k : VIx Dw, N k.toF * der φ (v k) s + a * val φ y s := by
  choose z hz hu using fun k : FIx Dw => existsUnique_isVert y (Pi.single k (1 : K))
  have : ∀ k : FIx Dw, ∃ a : K, k ∉ Set.range VIx.toF → ∀ s ∈ secK Xo c K₀ e, der φ (z k) s = a * val φ y s :=
    fun k => by
      by_cases hk : k ∈ Set.range VIx.toF
      · exact ⟨0, fun h => absurd hk h⟩
      · refine ((hz k).der_of_triangular (fun σ i j hij => Pi.single_eq_of_ne ?_ _) φ e).imp fun a ha _ => ha
        rintro rfl
        exact hk ⟨⟨σ, (i, j), hij⟩, rfl⟩
  choose a ha using this
  refine ⟨∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range VIx.toF), N k * a k, fun s hs => ?_⟩
  rw [h.der_shift h' hz φ hs, sum_FIx, add_assoc, Finset.sum_mul]
  congr 2
  · exact Finset.sum_congr rfl fun k _ => by rw [hu _ _ (hv k)]
  · exact Finset.sum_congr rfl fun k hk => by rw [ha k (Finset.mem_filter.1 hk).2 s hs, mul_assoc]

theorem IsVert.der_eq {y : FrPt Xo c K} {v : VIx Dw → FrPt Xo c (DualNumber K)}
    (hv : ∀ k : VIx Dw, IsVert y (Pi.single k.toF (1 : K)) (v k)) {N : FIx Dw → K}
    {w : FrPt Xo c (DualNumber K)} (h : IsVert y N w) (φ : K₀ →ₐ[c.F] K) (e : Ix Dw → ℤ) :
    ∃ a : K, ∀ s ∈ secK Xo c K₀ e, der φ w s = ∑ k : VIx Dw, N k.toF * der φ (v k) s + a * val φ y s := by
  obtain ⟨y₀, h₀, h⟩ := h
  obtain ⟨a, ha⟩ := (isDef_const h₀).der_shift_frame hv h φ e
  refine ⟨a, fun s hs => ?_⟩
  have : der φ y₀ s = 0 := by rw [der, val_frMap hs (φ := φ) (fun _ => rfl) h₀]; rfl
  rw [ha s hs, this, zero_add]

theorem KSIso.der_eq {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} (h : KSIso Φ y)
    {v : TIx Dw Φ → FrPt Xo c (DualNumber K)} (hv : IsTanFrame Φ y v) {w : FrPt Xo c (DualNumber K)}
    (hw : IsDef y w) {M : HIx Dw Φ → K} (hM : IsKS Φ y w.x M) (φ : K₀ →ₐ[c.F] K) (e : Ix Dw → ℤ) :
    ∃ (C : VIx Dw → K) (a : K), ∀ s ∈ secK Xo c K₀ e, der φ w s =
      ∑ k, M k * der φ (v (.inl k)) s + ∑ k, C k * der φ (v (.inr k)) s + a * val φ y s := by
  obtain ⟨W, z, hz⟩ := h.exists_universal
  have key : ∀ (w : FrPt Xo c (DualNumber K)) (M : HIx Dw Φ → K), IsDef y w → IsKS Φ y w.x M →
      ∃ (C : VIx Dw → K) (a : K), ∀ s ∈ secK Xo c K₀ e, der φ w s =
        ∑ k, (val ((inlAlgHom c.F K (HIx Dw Φ → K)).comp φ) W s).snd k * M k +
          ∑ k, C k * der φ (v (.inr k)) s + a * val φ y s := fun w M hw hM => by
    obtain ⟨N, hN⟩ := (hz M).2.1.exists_isShift hw (h.injective hw.isTanX (hz M).2.1.isTanX hM (hz M).2.2)
    obtain ⟨a, ha⟩ := (hz M).2.1.der_shift_frame hv.2 hN φ e
    exact ⟨_, a, fun s hs => by rw [ha s hs, der_dir φ (hz M).1 hs]⟩
  obtain ⟨C, a, hC⟩ := key w M hw hM
  choose C' a' hC' using fun k => key _ _ (hv.1 k).1 (hv.1 k).2
  refine ⟨fun j => C j - ∑ k, M k * C' k j, a - ∑ k, M k * a' k, fun s hs => ?_⟩
  rw [hC s hs, Finset.sum_congr rfl fun k _ => congrArg (M k * ·) (hC' k s hs)]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_add,
    Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (VIx Dw)))]
  simp only [mul_comm _ (M _)]
  ring

end KS

section Wedge

variable {K : Type} [Field K] [Algebra c.F K] {K₀ : Type} [CommRing K₀] [Algebra c.F K₀] {ι : Type} [Fintype ι]

def wedge (φ : K₀ →ₐ[c.F] K) (v : ι → FrPt Xo c (DualNumber K)) (s : ι → RulK Xo c K₀) : K :=
  (Matrix.of fun i k => der φ (v k) (s i)).det

def jac (φ : K₀ →ₐ[c.F] K) (y : FrPt Xo c K) (v : ι → FrPt Xo c (DualNumber K)) (s₀ : RulK Xo c K₀)
    (s : ι → RulK Xo c K₀) : K :=
  (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => val φ y s₀) (Matrix.of fun _ k => der φ (v k) s₀)
    (Matrix.of fun i _ => val φ y (s i)) (Matrix.of fun i k => der φ (v k) (s i))).det

theorem wedge_comb (φ : K₀ →ₐ[c.F] K) (v : ι → FrPt Xo c (DualNumber K)) (a : Matrix ι ι K₀)
    (s : ι → RulK Xo c K₀) : wedge φ v (fun i => ∑ j, a i j • s j) = φ a.det * wedge φ v s := by
  rw [wedge, wedge, AlgHom.map_det, ← Matrix.det_mul]
  congr 1
  ext i k
  simp [der_sum, Matrix.mul_apply]

theorem wedge_comp {κ : Type} [Fintype κ] (φ : K₀ →ₐ[c.F] K) (v : κ → FrPt Xo c (DualNumber K)) (e : ι ≃ κ)
    (s : ι → RulK Xo c K₀) : wedge φ (v ∘ e) s = wedge φ v (s ∘ e.symm) := by
  rw [wedge, wedge, ← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext i k
  simp

theorem wedge_perm (φ : K₀ →ₐ[c.F] K) (v : ι → FrPt Xo c (DualNumber K)) (σ : Equiv.Perm ι)
    (s : ι → RulK Xo c K₀) : wedge φ (v ∘ σ) s = (Equiv.Perm.sign σ : ℤ) * wedge φ v s :=
  Matrix.det_permute' σ (Matrix.of fun i k => der φ (v k) (s i))

theorem jac_perm (φ : K₀ →ₐ[c.F] K) (y : FrPt Xo c K) (v : ι → FrPt Xo c (DualNumber K)) (σ : Equiv.Perm ι)
    (s₀ : RulK Xo c K₀) (s : ι → RulK Xo c K₀) :
    jac φ y (v ∘ σ) s₀ s = (Equiv.Perm.sign σ : ℤ) * jac φ y v s₀ s := by
  have e : Equiv.Perm.sign σ = Equiv.Perm.sign (Equiv.Perm.sumCongr (1 : Equiv.Perm Unit) σ) := by simp
  rw [jac, jac, e]
  convert Matrix.det_permute' (Equiv.Perm.sumCongr (1 : Equiv.Perm Unit) σ) _ using 2
  ext (i | i) (k | k) <;> simp

theorem wedge_jac_of_comb {φ : K₀ →ₐ[c.F] K} {y : FrPt Xo c K} {v w : ι → FrPt Xo c (DualNumber K)}
    {e : Ix Dw → ℤ} {P : Matrix ι ι K} {a : ι → K}
    (h : ∀ k, ∀ s ∈ secK Xo c K₀ e, der φ (w k) s = ∑ j, P k j * der φ (v j) s + a k * val φ y s)
    {s : ι → RulK Xo c K₀} (hs : ∀ i, s i ∈ secK Xo c K₀ e) :
    ((∀ i, val φ y (s i) = 0) → wedge φ w s = P.det * wedge φ v s) ∧
      ∀ s₀ ∈ secK Xo c K₀ e, jac φ y w s₀ s = P.det * jac φ y v s₀ s := by
  refine ⟨fun h0 => ?_, fun s₀ h₀ => ?_⟩
  · rw [wedge, wedge, mul_comm, ← Matrix.det_transpose P, ← Matrix.det_mul]
    congr 1
    ext i k
    simp [Matrix.mul_apply, h k _ (hs i), h0, mul_comm]
  · have : P.det = (Matrix.fromBlocks (1 : Matrix Unit Unit K) (Matrix.of fun _ k => a k) 0 P.transpose).det := by
      simp
    rw [jac, jac, mul_comm, this, ← Matrix.det_mul]
    congr 1
    ext (i | i) (k | k) <;>
      simp [Matrix.mul_apply, h _ _ (hs _), h _ _ h₀, mul_comm, add_comm]

variable {Φ : Finset (E →+* ℂ)}

theorem KSIso.chain_rule {y : FrPt Xo c K} (h : KSIso Φ y) {v w : TIx Dw Φ → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame Φ y v) {M : HIx Dw Φ → HIx Dw Φ → K} {N : VIx Dw → FIx Dw → K}
    (hM : ∀ k, IsDef y (w (.inl k)) ∧ IsKS Φ y (w (.inl k)).x (M k)) (hN : ∀ k, IsVert y (N k) (w (.inr k)))
    (φ : K₀ →ₐ[c.F] K) {e : Ix Dw → ℤ} {s : TIx Dw Φ → RulK Xo c K₀} (hs : ∀ i, s i ∈ secK Xo c K₀ e) :
    ((∀ i, val φ y (s i) = 0) →
      wedge φ w s = (Matrix.of M).det * (Matrix.of fun k j : VIx Dw => N k j.toF).det * wedge φ v s) ∧
    ∀ s₀ ∈ secK Xo c K₀ e,
      jac φ y w s₀ s = (Matrix.of M).det * (Matrix.of fun k j : VIx Dw => N k j.toF).det * jac φ y v s₀ s := by
  choose C a hC using fun k => h.der_eq hv (hM k).1 (hM k).2 φ e
  choose b hb using fun k => (hN k).der_eq hv.2 φ e
  have := wedge_jac_of_comb (φ := φ) (y := y) (v := v) (w := w) (e := e) (a := Sum.elim a b)
    (P := Matrix.fromBlocks (Matrix.of M) (Matrix.of C) 0 (Matrix.of fun k j : VIx Dw => N k j.toF))
    (fun k s hs => by rcases k with k | k <;> simp [hC _ s hs, hb _ s hs]) hs
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (Matrix.of C)]
  convert this

theorem KSIso.wedge_jac_eq {y : FrPt Xo c K} (h : KSIso Φ y) {v w : TIx Dw Φ → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame Φ y v) (hw : IsTanFrame Φ y w) (φ : K₀ →ₐ[c.F] K) {e : Ix Dw → ℤ}
    {s : TIx Dw Φ → RulK Xo c K₀} (hs : ∀ i, s i ∈ secK Xo c K₀ e) :
    ((∀ i, val φ y (s i) = 0) → wedge φ w s = wedge φ v s) ∧
      ∀ s₀ ∈ secK Xo c K₀ e, jac φ y w s₀ s = jac φ y v s₀ s := by
  have := h.chain_rule hv hw.1 hw.2 φ hs
  have e1 : (Matrix.of fun k : HIx Dw Φ => (Pi.single k 1 : HIx Dw Φ → K)) = 1 := by
    ext i j; simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  have e2 : (Matrix.of fun k j : VIx Dw => (Pi.single k.toF 1 : FIx Dw → K) j.toF) = 1 := by
    ext i j; simp [Pi.single_apply, Matrix.one_apply, VIx.toF_injective.eq_iff, eq_comm]
  simpa only [e1, e2, Matrix.det_one, one_mul] using this

variable (Φ)

def IsWedgeVal (o : ι ≃ TIx Dw Φ) (φ : K₀ →ₐ[c.F] K) (y : FrPt Xo c K) (s : ι → RulK Xo c K₀) (d : K) : Prop :=
  (∀ i, val φ y (s i) = 0) ∧ ∃ v, IsTanFrame Φ y v ∧ d = wedge φ (v ∘ o) s

def IsJacVal (o : ι ≃ TIx Dw Φ) (φ : K₀ →ₐ[c.F] K) (y : FrPt Xo c K) (s₀ : RulK Xo c K₀) (s : ι → RulK Xo c K₀)
    (d : K) : Prop :=
  ∃ v, IsTanFrame Φ y v ∧ d = jac φ y (v ∘ o) s₀ s

variable {Φ}

theorem KSIso.existsUnique_isWedgeVal {y : FrPt Xo c K} (h : KSIso Φ y) (o : ι ≃ TIx Dw Φ) (φ : K₀ →ₐ[c.F] K)
    {e : Ix Dw → ℤ} {s : ι → RulK Xo c K₀} (hs : ∀ i, s i ∈ secK Xo c K₀ e) (h0 : ∀ i, val φ y (s i) = 0) :
    ∃! d, IsWedgeVal Φ o φ y s d := by
  obtain ⟨v, hv⟩ := h.exists_isTanFrame
  refine ⟨_, ⟨h0, v, hv, rfl⟩, ?_⟩
  rintro _ ⟨-, w, hw, rfl⟩
  rw [wedge_comp, wedge_comp]
  exact (h.wedge_jac_eq hv hw φ fun _ => hs _).1 fun _ => h0 _

theorem existsUnique_isWedgeVal_of_isEmpty [IsEmpty (HIx Dw Φ)] (o : ι ≃ TIx Dw Φ) (φ : K₀ →ₐ[c.F] K)
    {y : FrPt Xo c K} {s : ι → RulK Xo c K₀} (h0 : ∀ i, val φ y (s i) = 0) : ∃! d, IsWedgeVal Φ o φ y s d := by
  obtain ⟨v, hv, hu⟩ := existsUnique_isTanFrame_of_isEmpty (Φ := Φ) y
  refine ⟨_, ⟨h0, v, hv, rfl⟩, ?_⟩
  rintro _ ⟨-, w, hw, rfl⟩
  rw [hu w hw]

theorem IsWedgeVal.reorder {o : ι ≃ TIx Dw Φ} {φ : K₀ →ₐ[c.F] K} {y : FrPt Xo c K} {s : ι → RulK Xo c K₀} {d : K}
    (h : IsWedgeVal Φ o φ y s d) (o' : ι ≃ TIx Dw Φ) :
    IsWedgeVal Φ o' φ y s ((Equiv.Perm.sign (o'.trans o.symm) : ℤ) * d) := by
  obtain ⟨h0, v, hv, rfl⟩ := h
  refine ⟨h0, v, hv, ?_⟩
  rw [← wedge_perm]
  congr 1
  funext i
  simp

theorem IsJacVal.reorder {o : ι ≃ TIx Dw Φ} {φ : K₀ →ₐ[c.F] K} {y : FrPt Xo c K} {s₀ : RulK Xo c K₀}
    {s : ι → RulK Xo c K₀} {d : K} (h : IsJacVal Φ o φ y s₀ s d) (o' : ι ≃ TIx Dw Φ) :
    IsJacVal Φ o' φ y s₀ s ((Equiv.Perm.sign (o'.trans o.symm) : ℤ) * d) := by
  obtain ⟨v, hv, rfl⟩ := h
  refine ⟨v, hv, ?_⟩
  rw [← jac_perm]
  congr 1
  funext i
  simp

theorem IsWedgeVal.comb {o : ι ≃ TIx Dw Φ} {φ : K₀ →ₐ[c.F] K} {y : FrPt Xo c K} {s : ι → RulK Xo c K₀} {d : K}
    (h : IsWedgeVal Φ o φ y s d) (a : Matrix ι ι K₀) :
    IsWedgeVal Φ o φ y (fun i => ∑ j, a i j • s j) (φ a.det * d) := by
  obtain ⟨h0, v, hv, rfl⟩ := h
  exact ⟨fun i => by simp [val_smul, h0], v, hv, (wedge_comb φ _ a s).symm⟩

end Wedge

section Norm

variable {T : CDVR} {io : c.F →+* T.Fr} {K₀ : Type} [CommRing K₀] [Algebra c.F K₀] {ι : Type} [Fintype ι]

variable (c) in

abbrev CoefHom (io : c.F →+* T.Fr) (K₀ : Type) [CommRing K₀] [Algebra c.F K₀] : Type :=
  letI := io.toAlgebra
  K₀ →ₐ[c.F] T.Fr

def secOrd (n : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s : RulK Xo c K₀) : EReal :=
  letI := io.toAlgebra
  nval T.V n (val φ y.1 s)

variable (Φ : Finset (E →+* ℂ))

def IsWedgeOrd (n : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s : ι → RulK Xo c K₀) (w : EReal) : Prop :=
  letI := io.toAlgebra
  ∃ (o : ι ≃ TIx Dw Φ) (d : T.Fr), IsWedgeVal Φ o φ y.1 s d ∧ w = nval T.V n d

def IsJacOrd (n : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s₀ : RulK Xo c K₀) (s : ι → RulK Xo c K₀)
    (w : EReal) : Prop :=
  letI := io.toAlgebra
  ∃ (o : ι ≃ TIx Dw Φ) (d : T.Fr), IsJacVal Φ o φ y.1 s₀ s d ∧ w = nval T.V n d

def wedgeOrd (n : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s : ι → RulK Xo c K₀) : EReal :=
  if h : ∃! w, IsWedgeOrd Φ n φ y s w then h.choose else ⊥

def jacOrd (n : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s₀ : RulK Xo c K₀) (s : ι → RulK Xo c K₀) : EReal :=
  if h : ∃! w, IsJacOrd Φ n φ y s₀ s w then h.choose else ⊥

variable (T) in

def ramIdx (p : ℕ) : ℕ := (vV T.V (p : T.Fr)).toNat

def secOrd_vp (p : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s : RulK Xo c K₀) : EReal :=
  secOrd (ramIdx T p) φ y s

def wedgeOrd_vp (p : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s : ι → RulK Xo c K₀) : EReal :=
  wedgeOrd Φ (ramIdx T p) φ y s

def jacOrd_vp (p : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s₀ : RulK Xo c K₀) (s : ι → RulK Xo c K₀) :
    EReal :=
  jacOrd Φ (ramIdx T p) φ y s₀ s

def normOfOrd (p : ℕ) (w : EReal) : ENNReal := EReal.exp (-(w * (Real.log p : ℝ)))

def wedgeNorm (p : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s : ι → RulK Xo c K₀) : ENNReal :=
  normOfOrd p (wedgeOrd_vp Φ p φ y s)

def jacNorm (p : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s₀ : RulK Xo c K₀) (s : ι → RulK Xo c K₀) :
    ENNReal :=
  normOfOrd p (jacOrd_vp Φ p φ y s₀ s)

variable {Φ}

theorem ramIdx_spec {p : ℕ} (hp : p ≠ 0) (h : (p : T.V) ∈ IsLocalRing.maximalIdeal T.V) :
    0 < ramIdx T p ∧ nval T.V (ramIdx T p) (p : T.Fr) = 1 := by
  have h0 : (p : T.Fr) ≠ 0 := by
    rw [← map_natCast (algebraMap T.V T.Fr)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (Nat.cast_ne_zero.2 hp)
  have h1 : valV T.V (p : T.Fr) < 1 := by
    rw [← map_natCast (algebraMap T.V T.Fr)]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 h
  have h2 : 0 < vV T.V (p : T.Fr) := by
    have := (WithZero.log_lt_log (valV_ne_zero (V := T.V) h0) one_ne_zero).2 h1
    rw [WithZero.log_one] at this
    simpa [vV] using this
  have h3 : ((ramIdx T p : ℕ) : ℝ) = (vV T.V (p : T.Fr) : ℝ) := by
    rw [ramIdx, ← Int.cast_natCast, Int.toNat_of_nonneg h2.le]
  refine ⟨by rw [ramIdx]; omega, ?_⟩
  rw [nval_of_ne h0, h3, div_self (by exact_mod_cast h2.ne')]
  rfl

theorem normOfOrd_le_iff {p : ℕ} (hp : 1 < p) (w : EReal) (b : ℝ) :
    normOfOrd p w ≤ ENNReal.ofReal ((p : ℝ) ^ b) ↔ ((-b : ℝ) : EReal) ≤ w := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hl : 0 < Real.log p := Real.log_pos h1
  rw [Real.rpow_def_of_pos (by linarith), ← EReal.exp_coe, normOfOrd, EReal.exp_le_exp_iff]
  induction w with
  | bot => rw [EReal.bot_mul_coe_of_pos hl]; simp [-EReal.coe_mul]
  | top => rw [EReal.top_mul_coe_of_pos hl]; simp
  | coe w =>
    rw [← EReal.coe_mul, ← EReal.coe_neg, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> nlinarith

example {p : ℕ} (hp : 0 < p) : normOfOrd p 1 = ENNReal.ofReal (p : ℝ)⁻¹ := by
  rw [normOfOrd, one_mul, ← EReal.coe_neg, EReal.exp_coe, Real.exp_neg, Real.exp_log (by exact_mod_cast hp)]

theorem wedgeNorm_le_iff {p : ℕ} (hp : 1 < p) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s : ι → RulK Xo c K₀)
    (b : ℝ) : wedgeNorm Φ p φ y s ≤ ENNReal.ofReal ((p : ℝ) ^ b) ↔ ((-b : ℝ) : EReal) ≤ wedgeOrd_vp Φ p φ y s :=
  normOfOrd_le_iff hp _ b

theorem wedgeOrd_ne_bot_iff {n : ℕ} {φ : CoefHom c io K₀} {y : IntFr Xo c T io} {s : ι → RulK Xo c K₀} :
    wedgeOrd Φ n φ y s ≠ ⊥ ↔ ∃! w, IsWedgeOrd Φ n φ y s w := by
  refine ⟨fun h => by_contra fun h' => h (dif_neg h'), fun h => ?_⟩
  obtain ⟨o, d, -, e⟩ := h.choose_spec.1
  rw [wedgeOrd, dif_pos h, e]
  exact nval_ne_bot _ _

theorem wedgeOrd_eq {n : ℕ} {φ : CoefHom c io K₀} {y : IntFr Xo c T io} {s : ι → RulK Xo c K₀}
    (h : wedgeOrd Φ n φ y s ≠ ⊥) {w : EReal} (hw : IsWedgeOrd Φ n φ y s w) : wedgeOrd Φ n φ y s = w := by
  have h' := wedgeOrd_ne_bot_iff.1 h
  rw [wedgeOrd, dif_pos h']
  exact h'.unique h'.choose_spec.1 hw

theorem nval_sign_mul (n : ℕ) (u : ℤˣ) (x : T.Fr) : nval T.V n (((u : ℤ) : T.Fr) * x) = nval T.V n x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · refine nval_mul_unit n (by simp) ?_ x
    simp [vV]

theorem wedgeOrd_eq_of_unique (n : ℕ) {φ : CoefHom c io K₀} {y : IntFr Xo c T io} {s : ι → RulK Xo c K₀}
    {o : ι ≃ TIx Dw Φ} (h : letI := io.toAlgebra; ∃! d, IsWedgeVal Φ o φ y.1 s d) {d : T.Fr}
    (hd : letI := io.toAlgebra; IsWedgeVal Φ o φ y.1 s d) : wedgeOrd Φ n φ y s = nval T.V n d := by
  letI := io.toAlgebra
  refine wedgeOrd_eq (wedgeOrd_ne_bot_iff.2 ⟨_, ⟨o, d, hd, rfl⟩, ?_⟩) ⟨o, d, hd, rfl⟩
  rintro _ ⟨o', d', hd', rfl⟩
  rw [← h.unique (hd'.reorder o) hd, nval_sign_mul]

theorem KSIso.wedgeOrd_eq {y : IntFr Xo c T io} (h : letI := io.toAlgebra; KSIso Φ y.1) (n : ℕ)
    {φ : CoefHom c io K₀} {e : Ix Dw → ℤ} {s : ι → RulK Xo c K₀} (hs : ∀ i, s i ∈ secK Xo c K₀ e)
    {o : ι ≃ TIx Dw Φ} {d : T.Fr} (hd : letI := io.toAlgebra; IsWedgeVal Φ o φ y.1 s d) :
    wedgeOrd Φ n φ y s = nval T.V n d :=
  letI := io.toAlgebra
  wedgeOrd_eq_of_unique n (h.existsUnique_isWedgeVal o φ hs hd.1) hd

end Norm

end GlobalTheory.FlagTan
