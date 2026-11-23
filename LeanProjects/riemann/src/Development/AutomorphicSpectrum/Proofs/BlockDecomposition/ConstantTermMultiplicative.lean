import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMulSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermConvolutionHeckeStatement

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtMulSplit

theorem hint_comp_equiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (K : Subgroup H) (K' : Subgroup H')
    (hK : ∀ x, x ∈ K ↔ e x ∈ K') (u : H' → ℂ) : hint K (fun x => u (e x)) = hint K' u := by
  set S : Subgroup H := rStab (fun x => u (e x)) ⊓ K with hSdef
  set S' : Subgroup H' := rStab u ⊓ K' with hS'def
  have hr : ∀ x, x ∈ rStab (fun x => u (e x)) ↔ e x ∈ rStab u := by
    intro x
    constructor
    · intro hx y
      have := hx (e.symm y)
      simpa using this
    · intro hx y
      show u (e (y * x)) = u (e y)
      rw [map_mul]
      exact hx (e y)
  have hS : ∀ x, x ∈ S ↔ e x ∈ S' := by
    intro x
    rw [hSdef, hS'def, Subgroup.mem_inf, Subgroup.mem_inf, hr, hK]
  have hKm : K.map e.toMonoidHom = K' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hK x).1 hx
    · intro hy
      exact ⟨e.symm y, (hK _).2 (by simpa using hy), by simp⟩
  have hSc : S = S'.comap e.toMonoidHom := by
    ext x
    exact hS x
  have hidx : S.relIndex K = S'.relIndex K' := by
    rw [hSc, Subgroup.relIndex_comap, hKm]
  let φ : H ⧸ S ≃ H' ⧸ S' := Quotient.congr e.toEquiv (by
    intro x y
    show QuotientGroup.leftRel S x y ↔ QuotientGroup.leftRel S' (e x) (e y)
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hS]
    simp)
  have hφ : ∀ x : H, φ (x : H ⧸ S) = ((e x : H') : H' ⧸ S') := fun x => rfl
  have hsum : ∑ᶠ q : H ⧸ S, u (e q.out) = ∑ᶠ q : H' ⧸ S', u q.out := by
    rw [← finsum_comp_equiv φ]
    refine finsum_congr fun q => ?_
    have h1 : φ q = ((e q.out : H') : H' ⧸ S') := by
      rw [← hφ, QuotientGroup.out_eq']
    rw [h1]
    have hk : (((e q.out : H') : H' ⧸ S').out)⁻¹ * e q.out ∈ S' :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' ((e q.out : H') : H' ⧸ S'))
    have := (Subgroup.mem_inf.1 hk).1 (((e q.out : H') : H' ⧸ S').out)
    simpa using this
  show ((S.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ S, u (e q.out) = ((S'.relIndex K' : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H' ⧸ S', u q.out
  rw [hidx, hsum]

theorem hint_const_mul {H : Type} [Group H] (K : Subgroup H) (c : ℂ) (hc : c ≠ 0) (u : H → ℂ) :
    hint K (fun z => c * u z) = c * hint K u := by
  have hr : rStab (fun z => c * u z) = rStab u := by
    ext k
    constructor
    · intro hk x
      exact mul_left_cancel₀ hc (hk x)
    · intro hk x
      show c * u (x * k) = c * u x
      rw [hk x]
  unfold hint
  rw [hr, mul_left_comm]
  congr 1
  simpa [smul_eq_mul] using (smul_finsum c (fun q : H ⧸ (rStab u ⊓ K) => u q.out)).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ordL_neg_one (w : Pl E) : ordL ((-1 : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 0 := by
  have h1 : Valued.v ((-1 : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    simp
  unfold ordL
  rw [dif_neg (by rw [h1]; exact one_ne_zero)]
  simp [h1]
  rfl

theorem twist_mul (a b : ℕ) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) (x y : GLw a w × GLw b w) :
    μ ((-1) ^ (a * b) * GeneralLinearGroup.det (x * y).1 ^ b * GeneralLinearGroup.det (x * y).2 ^ a) =
      μ ((-1) ^ (a * b) * GeneralLinearGroup.det x.1 ^ b * GeneralLinearGroup.det x.2 ^ a) *
        μ ((-1) ^ (a * b) * GeneralLinearGroup.det y.1 ^ b * GeneralLinearGroup.det y.2 ^ a) := by
  have h1 : μ (-1) = 1 := hμ _ (ordL_neg_one w)
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, map_pow, h1, one_pow, one_mul, mul_pow]
  exact mul_mul_mul_comm _ _ _ _

theorem mconv_twist {a b : ℕ} {w : Pl E} (c : GLw a w × GLw b w → ℂ) (hc : ∀ m, c m ≠ 0)
    (hm : ∀ x y, c (x * y) = c x * c y) (u v : GLw a w × GLw b w → ℂ) (m : GLw a w × GLw b w) :
    mconv (fun m => c m * u m) (fun m => c m * v m) m = c m * mconv u v m := by
  unfold mconv
  rw [← hint_const_mul _ _ (hc m)]
  congr 1
  funext z
  have e : c m = c z * c (z⁻¹ * m) := by rw [← hm, mul_inv_cancel_left]
  rw [e]
  ring

theorem toSub_val {n : ℕ} {w : Pl E} (hU : UL n w = ⊤) (x : UL n w) : toSub (UL n w) x.1 = x := by
  unfold toSub
  rw [dif_pos x.2]

theorem toSub_mul {n : ℕ} {w : Pl E} (hU : UL n w = ⊤) (x y : GLw n w) :
    toSub (UL n w) (x * y) = toSub (UL n w) x * toSub (UL n w) y := by
  have hm : ∀ z : GLw n w, z ∈ UL n w := fun z => hU ▸ Subgroup.mem_top z
  unfold toSub
  rw [dif_pos (hm _), dif_pos (hm _), dif_pos (hm _)]
  rfl

theorem val_toSub {n : ℕ} {w : Pl E} (hU : UL n w = ⊤) (y : GLw n w) : (toSub (UL n w) y).1 = y := by
  have hm : ∀ z : GLw n w, z ∈ UL n w := fun z => hU ▸ Subgroup.mem_top z
  unfold toSub
  rw [dif_pos (hm _)]

def ulEquiv {n : ℕ} {w : Pl E} (hU : UL n w = ⊤) : UL n w ≃* GLw n w where
  toFun x := x.1
  invFun y := toSub (UL n w) y
  left_inv x := toSub_val hU x
  right_inv y := val_toSub hU y
  map_mul' _ _ := rfl

theorem isHk_of_isHecke {n : ℕ} {w : Pl E} (hU : UL n w = ⊤) {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) :
    IsHk (GlobalTheory.LFun.KGL w n) (fun y => f (toSub (UL n w) y)) := by
  refine ⟨?_, GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w n, ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]
    exact GlobalTheory.SplitFlip.isOpen_KO
  · refine HasCompactSupport.intro (hf.1.isCompact.image continuous_subtype_val) fun y hy => ?_
    by_contra h0
    exact hy ⟨toSub (UL n w) y, subset_tsupport _ h0, val_toSub hU y⟩
  · intro k₁ hk₁ k₂ hk₂ g
    have hm : ∀ k ∈ GlobalTheory.LFun.KGL w n, toSub (UL n w) k ∈ KL n w := fun k hk => by
      rw [KL, Subgroup.mem_subgroupOf, val_toSub hU]
      exact hk
    show f (toSub _ (k₁ * g * k₂)) = f (toSub _ g)
    rw [toSub_mul hU, toSub_mul hU, (hf.2 _ (hm _ hk₂) _).2, (hf.2 _ (hm _ hk₁) _).1]

theorem lconv_eq_gconv {n : ℕ} {w : Pl E} (hU : UL n w = ⊤) (f g : UL n w → ℂ) :
    (fun y => PositivityTheory.Rg.BcB.F.Eig.lconv f g (toSub (UL n w) y)) =
      gconv (fun y => f (toSub (UL n w) y)) (fun y => g (toSub (UL n w) y)) := by
  funext y
  unfold PositivityTheory.Rg.BcB.F.Eig.lconv gconv
  rw [← hint_comp_equiv (ulEquiv hU) (KL n w) (GlobalTheory.LFun.KGL w n) (fun x => Subgroup.mem_subgroupOf)]
  congr 1
  funext z
  show _ = f (toSub _ z.1) * g (toSub _ (z.1⁻¹ * y))
  rw [toSub_val hU, toSub_mul hU]
  congr 2
  congr 1
  exact (toSub_val hU z⁻¹).symm

theorem hint_left {H : Type} [Group H] (K : Subgroup H) (k : H) (u : H → ℂ) :
    hint K (fun z => u (k * z)) = hint K u := by
  have hr : rStab (fun z => u (k * z)) = rStab u := by
    ext l
    constructor
    · intro hl x
      have := hl (k⁻¹ * x)
      simpa [mul_assoc] using this
    · intro hl x
      show u (k * (x * l)) = u (k * x)
      rw [← mul_assoc, hl]
  unfold hint
  rw [hr]
  congr 1
  set S := rStab u ⊓ K with hS
  refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (H ⧸ S)) (f := fun q : H ⧸ S => u q.out))
  refine finsum_congr fun q => ?_
  have h1 : (MulAction.toPerm k : Equiv.Perm (H ⧸ S)) q = ((k * q.out : H) : H ⧸ S) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [h1]
  have hk : (((k * q.out : H) : H ⧸ S).out)⁻¹ * (k * q.out) ∈ S :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' ((k * q.out : H) : H ⧸ S))
  have := (Subgroup.mem_inf.1 hk).1 (((k * q.out : H) : H ⧸ S).out)
  simpa using this

theorem gconv_bi {n : ℕ} {w : Pl E} {f₁ f₂ : GLw n w → ℂ}
    (h₁ : ∀ u ∈ GlobalTheory.LFun.KGL w n, ∀ g, f₁ (u * g) = f₁ g ∧ f₁ (g * u) = f₁ g)
    (h₂ : ∀ u ∈ GlobalTheory.LFun.KGL w n, ∀ g, f₂ (u * g) = f₂ g ∧ f₂ (g * u) = f₂ g) :
    ∀ u ∈ GlobalTheory.LFun.KGL w n, ∀ g, gconv f₁ f₂ (u * g) = gconv f₁ f₂ g ∧ gconv f₁ f₂ (g * u) = gconv f₁ f₂ g := by
  intro u hu g
  constructor
  · unfold gconv
    rw [← hint_left _ u]
    congr 1
    funext z
    rw [(h₁ u hu z).1]
    congr 2
    group
  · unfold gconv
    congr 1
    funext z
    rw [← mul_assoc, (h₂ u hu _).2]

theorem constant_term_eq_mackey_entry {n a b : ℕ} (h : a + b = n) (w : Pl E) {f : GLw n w → ℂ}
    (hf : ∀ u ∈ GlobalTheory.LFun.KGL w n, ∀ g, f (u * g) = f g ∧ f (g * u) = f g) :
    ct h w f = phi3 h w f 1 1 := by
  funext m
  unfold ct phi3
  congr 2
  funext Z
  have hX1 : ∀ x ∈ ({1} : Finset (GLw n w)), x ∈ GlobalTheory.LFun.KGL w n := by
    intro x hx
    rw [Finset.mem_singleton.1 hx]
    exact Subgroup.one_mem _
  have hX2 : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ ({1} : Finset (GLw n w)), x⁻¹ * k ∈ GlobalTheory.LFun.KGL w n := by
    intro k hk
    refine ⟨1, ⟨Finset.mem_singleton_self _, by simpa using hk⟩, ?_⟩
    rintro y ⟨hy, -⟩
    exact Finset.mem_singleton.1 hy
  rw [GlobalTheory.CompanionTheory.DiagAvg.avg_conj _ _ {1} hX1 hX2 f hf]
  simp

theorem ct_gconv {n a b : ℕ} (h : a + b = n) (w : Pl E) {f₁ f₂ : GLw n w → ℂ}
    (h₁ : IsHk (GlobalTheory.LFun.KGL w n) f₁) (h₂ : IsHk (GlobalTheory.LFun.KGL w n) f₂) (m : GLw a w × GLw b w) :
    ct h w (gconv f₁ f₂) m = mconv (ct h w f₁) (ct h w f₂) m := by
  have hbi : ∀ {f : GLw n w → ℂ}, IsHk (GlobalTheory.LFun.KGL w n) f →
      ∀ u ∈ GlobalTheory.LFun.KGL w n, ∀ g, f (u * g) = f g ∧ f (g * u) = f g := fun hf u hu g =>
    ⟨by simpa using hf.2.2.2 u hu 1 (Subgroup.one_mem _) g, by simpa using hf.2.2.2 1 (Subgroup.one_mem _) u hu g⟩
  have hnorm : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ GlobalTheory.LFun.KGL w n, k * k' * k⁻¹ ∈ GlobalTheory.LFun.KGL w n :=
    fun k hk k' hk' => mul_mem (mul_mem hk hk') (inv_mem hk)
  have hX1 : ∀ x ∈ ({1} : Finset (GLw n w)), x ∈ GlobalTheory.LFun.KGL w n := by
    intro x hx
    rw [Finset.mem_singleton.1 hx]
    exact Subgroup.one_mem _
  have hX2 : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ ({1} : Finset (GLw n w)), x⁻¹ * k ∈ GlobalTheory.LFun.KGL w n := by
    intro k hk
    refine ⟨1, ⟨Finset.mem_singleton_self _, by simpa using hk⟩, ?_⟩
    rintro y ⟨hy, -⟩
    exact Finset.mem_singleton.1 hy
  have hmul := GlobalTheory.T.constant_term_convolution_hecke E n a b h w (GlobalTheory.LFun.KGL w n) h₁.1 le_rfl hnorm {1} hX1 hX2 f₁ f₂ h₁ h₂ 1
    (Finset.mem_singleton_self _) 1 (Finset.mem_singleton_self _) m
  rw [constant_term_eq_mackey_entry h w (gconv_bi (hbi h₁) (hbi h₂)), constant_term_eq_mackey_entry h w (hbi h₁), constant_term_eq_mackey_entry h w (hbi h₂), hmul]
  simp

theorem ctMul : CtMul := by
  intro E _ _ _ n a ha w hw μ hμ f g hf hg
  have hU : UL n w = ⊤ := if_pos hw
  funext m
  set h := Nat.add_sub_cancel' ha with hh
  let c : GLw a w × GLw (n - a) w → ℂ := fun m =>
    (μ ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) : ℂ)
  have hc0 : ∀ m, c m ≠ 0 := fun m => Units.ne_zero _
  have hcm : ∀ x y, c (x * y) = c x * c y := fun x y => by
    show ((μ _ : ℂˣ) : ℂ) = _
    rw [twist_mul a (n - a) w μ hμ x y]
    rfl
  have hfun : ∀ F : UL n w → ℂ, ctMu h w μ F = fun m => c m * ct h w (fun y => F (toSub (UL n w) y)) m :=
    fun F => rfl
  rw [hfun f, hfun g, mconv_twist c hc0 hcm, hfun, lconv_eq_gconv hU]
  show c m * _ = _
  rw [ct_gconv h w (isHk_of_isHecke hU hf) (isHk_of_isHecke hU hg)]

end GlobalTheory.CompanionTheory.CtMulSplit
