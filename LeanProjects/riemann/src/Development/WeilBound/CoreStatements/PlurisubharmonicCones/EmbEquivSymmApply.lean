import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexConjugate

noncomputable section

namespace LevelTowerAlt

section Emb

variable {E : Type} [Field E] [NumberField E]

theorem exists_mul_eq_nat {a : 𝓞 E} (h : a ≠ 0) : ∃ (n : ℕ) (c : 𝓞 E), n ≠ 0 ∧ c * a = n := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  refine ⟨_, c, ?_, hc⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact h

theorem emb_inj (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  obtain ⟨n, c, hn, hc⟩ := exists_mul_eq_nat h
  have h1 := congrArg s hc
  rw [map_mul, ha, mul_zero, map_natCast] at h1
  exact hn (by exact_mod_cast h1.symm)

def extE (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_inj s)

theorem extE_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extE s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_inj s) a

theorem extE_comp (s : 𝓞 E →+* ℂ) : (extE s).comp (algebraMap (𝓞 E) E) = s := RingHom.ext (extE_apply s)

variable (E) in

def embEquiv : (E →+* ℂ) ≃ (𝓞 E →+* ℂ) where
  toFun t := t.comp (algebraMap (𝓞 E) E)
  invFun := extE
  left_inv t := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (extE_comp (t.comp (algebraMap (𝓞 E) E)))
  right_inv := extE_comp

instance fintypeEmb : Fintype (𝓞 E →+* ℂ) := Fintype.ofEquiv _ (embEquiv E)

omit [NumberField E] in
theorem cj_cj (s : 𝓞 E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s :=
  RingHom.ext fun _ => Complex.conj_conj _

variable (E) in

def cjEquiv : (𝓞 E →+* ℂ) ≃ (𝓞 E →+* ℂ) where
  toFun s := (starRingEnd ℂ).comp s
  invFun s := (starRingEnd ℂ).comp s
  left_inv := cj_cj
  right_inv := cj_cj

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem emb_uniq {w : (𝓞 E →+* ℂ) → W} (h : ∀ a, ∑ s : 𝓞 E →+* ℂ, s a • w s = 0) (s : 𝓞 E →+* ℂ) :
    w s = 0 := by
  have hli : LinearIndependent ℂ (fun t : 𝓞 E →+* ℂ => ((t : 𝓞 E →* ℂ) : 𝓞 E → ℂ)) :=
    (linearIndependent_monoidHom (𝓞 E) ℂ).comp (fun t : 𝓞 E →+* ℂ => (t : 𝓞 E →* ℂ))
      (fun t t' htt => RingHom.ext fun a => DFunLike.congr_fun htt a)
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  refine Fintype.linearIndependent_iff.mp hli (fun t => φ (w t)) ?_ s
  funext a
  have h1 := congrArg φ (h a)
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, MonoidHom.coe_coe]
  rw [← h1]
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

theorem emb_uniq₂ {w w' : (𝓞 E →+* ℂ) → W}
    (h : ∀ a, ∑ s : 𝓞 E →+* ℂ, s a • w s = ∑ s : 𝓞 E →+* ℂ, s a • w' s) (s : 𝓞 E →+* ℂ) : w s = w' s := by
  rw [← sub_eq_zero]
  refine emb_uniq (w := fun s => w s - w' s) (fun a => ?_) s
  simp only [smul_sub, Finset.sum_sub_distrib, h a, sub_self]

theorem conj_of_real {h : (𝓞 E →+* ℂ) → ℂ} (hr : ∀ a, (∑ s : 𝓞 E →+* ℂ, s a * h s).im = 0)
    (s : 𝓞 E →+* ℂ) : h ((starRingEnd ℂ).comp s) = conj (h s) := by
  have key : ∀ t, h t = conj (h ((starRingEnd ℂ).comp t)) := by
    refine emb_uniq₂ (W := ℂ) (fun a => ?_)
    have hc : conj (∑ t : 𝓞 E →+* ℂ, t a * h t) = ∑ t : 𝓞 E →+* ℂ, t a * h t :=
      Complex.conj_eq_iff_im.mpr (hr a)
    simp only [smul_eq_mul]
    rw [← hc, map_sum]
    simp only [map_mul]
    exact Fintype.sum_equiv (cjEquiv E) _ _ (fun t => by simp [cjEquiv, cj_cj])
  rw [key ((starRingEnd ℂ).comp s), cj_cj]

variable (E) in
theorem exists_coef : ∃ d : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (𝓞 E →+* ℂ) → ℂ, ∀ a j,
    (((RingOfIntegers.basis E).repr a j : ℤ) : ℂ) = ∑ s : 𝓞 E →+* ℂ, s a * d j s := by
  classical
  let b := RingOfIntegers.basis E
  let M : Matrix (𝓞 E →+* ℂ) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℂ := fun s j => s (b j)
  have hs : ∀ (s : 𝓞 E →+* ℂ) (a : 𝓞 E), s a = ∑ j, ((b.repr a j : ℤ) : ℂ) * s (b j) := by
    intro s a
    conv_lhs => rw [← b.sum_repr a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zsmul_eq_mul, map_mul, map_intCast]
  have hexp : ∀ (w : (𝓞 E →+* ℂ) → ℂ) (a : 𝓞 E),
      ∑ t : 𝓞 E →+* ℂ, t a * w t = ∑ j, ((b.repr a j : ℤ) : ℂ) * (w ᵥ* M) j := by
    intro w a
    simp only [Matrix.vecMul, dotProduct, M, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hs t a, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hinj : Function.Injective (Matrix.vecMulLinear M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : w ᵥ* M = 0 := hw
    funext t
    refine emb_uniq (W := ℂ) (w := w) (fun a => ?_) t
    simp only [smul_eq_mul]
    rw [hexp, hw']
    simp
  have hcard : Module.finrank ℂ ((𝓞 E →+* ℂ) → ℂ) =
      Module.finrank ℂ (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      ← Module.finrank_eq_card_basis b, RingOfIntegers.rank, ← NumberField.Embeddings.card E ℂ]
    convert (Fintype.card_congr (embEquiv E)).symm
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hcard).mp hinj
  refine ⟨fun j => (hsurj (Pi.single j 1)).choose, fun a j => ?_⟩
  have hd : (hsurj (Pi.single j 1)).choose ᵥ* M = Pi.single j 1 := (hsurj (Pi.single j 1)).choose_spec
  rw [hexp, hd]
  simp [Pi.single_apply, b]

def coef (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (s : 𝓞 E →+* ℂ) : ℂ := (exists_coef E).choose j s

theorem coef_spec (a : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (((RingOfIntegers.basis E).repr a j : ℤ) : ℂ) = ∑ s : 𝓞 E →+* ℂ, s a * coef j s :=
  (exists_coef E).choose_spec a j

theorem coef_conj (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (s : 𝓞 E →+* ℂ) :
    coef j ((starRingEnd ℂ).comp s) = conj (coef j s) :=
  conj_of_real (h := coef j) (fun a => by rw [← coef_spec, Complex.intCast_im]) s

theorem dec_spec (f : 𝓞 E →+ W) (a : 𝓞 E) :
    f a = ∑ s : 𝓞 E →+* ℂ, s a • ∑ j, coef j s • f (RingOfIntegers.basis E j) := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← coef_spec]
  conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr a]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem sum_coef (s : 𝓞 E →+* ℂ) : ∑ j, coef j s * s (RingOfIntegers.basis E j) = 1 := by
  classical
  have h0 := emb_uniq₂ (W := ℂ) (w := fun t => ∑ j, coef j t * s (RingOfIntegers.basis E j))
    (w' := fun t => if t = s then 1 else 0) (fun a => by
      have h1 := dec_spec (W := ℂ) (RingHom.toAddMonoidHom s) a
      simp only [smul_eq_mul] at h1
      simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact h1.symm) s
  simpa using h0

theorem mem_eig {k V O : Type} [CommRing k] [AddCommGroup V] [Module k V] [CommRing O]
    {ρ : O →+* Module.End k V} {s : O →+* k} {x : V} : x ∈ eigSp ρ s ↔ ∀ a, ρ a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

variable (ρ : 𝓞 E →+* Module.End ℂ W)

def proj (s : 𝓞 E →+* ℂ) : Module.End ℂ W := ∑ j, coef j s • ρ (RingOfIntegers.basis E j)

theorem proj_apply (s : 𝓞 E →+* ℂ) (x : W) :
    proj ρ s x = ∑ j, coef j s • ρ (RingOfIntegers.basis E j) x := by
  simp only [proj, LinearMap.sum_apply, LinearMap.smul_apply]

theorem act_apply (a : 𝓞 E) (x : W) : ρ a x = ∑ s : 𝓞 E →+* ℂ, s a • proj ρ s x := by
  have h0 := dec_spec (AddMonoidHom.mk' (fun b => ρ b x) (fun b c => by rw [map_add, LinearMap.add_apply])) a
  simpa only [AddMonoidHom.mk'_apply, proj_apply] using h0

theorem sum_proj (x : W) : ∑ s : 𝓞 E →+* ℂ, proj ρ s x = x := by
  have h := act_apply ρ 1 x
  simp only [map_one, one_smul, Module.End.one_apply] at h
  exact h.symm

theorem act_proj (s : 𝓞 E →+* ℂ) (a : 𝓞 E) (x : W) : ρ a (proj ρ s x) = s a • proj ρ s x := by
  refine emb_uniq₂ (w := fun t => ρ a (proj ρ t x)) (w' := fun t => t a • proj ρ t x) (fun c => ?_) s
  calc ∑ t : 𝓞 E →+* ℂ, t c • ρ a (proj ρ t x) = ρ a (∑ t : 𝓞 E →+* ℂ, t c • proj ρ t x) := by
        simp [map_sum, map_smul]
    _ = ρ (c * a) x := by
        rw [← act_apply, mul_comm, map_mul]
        rfl
    _ = ∑ t : 𝓞 E →+* ℂ, t c • t a • proj ρ t x := by
        rw [act_apply]
        exact Finset.sum_congr rfl fun t _ => by rw [map_mul, mul_smul]

theorem proj_act (s : 𝓞 E →+* ℂ) (a : 𝓞 E) (x : W) : proj ρ s (ρ a x) = s a • proj ρ s x := by
  rw [← act_proj, proj_apply, proj_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  congr 1
  show (ρ _ * ρ a) x = (ρ a * ρ _) x
  rw [← map_mul, ← map_mul, mul_comm]

theorem proj_mem (s : 𝓞 E →+* ℂ) (x : W) : proj ρ s x ∈ eigSp ρ s := mem_eig.2 fun a => act_proj ρ s a x

variable {ρ}

open Classical in
theorem proj_eig {s : 𝓞 E →+* ℂ} {x : W} (hx : x ∈ eigSp ρ s) (t : 𝓞 E →+* ℂ) :
    proj ρ t x = if t = s then x else 0 := by
  refine emb_uniq₂ (w := fun t => proj ρ t x) (w' := fun t => if t = s then x else 0) (fun a => ?_) t
  rw [← act_apply, mem_eig.1 hx a]
  simp

theorem proj_eig_self {s : 𝓞 E →+* ℂ} {x : W} (hx : x ∈ eigSp ρ s) : proj ρ s x = x := by
  simpa using proj_eig hx s

theorem proj_eig_ne {s t : 𝓞 E →+* ℂ} {x : W} (hx : x ∈ eigSp ρ s) (h : t ≠ s) : proj ρ t x = 0 := by
  rw [proj_eig hx, if_neg h]

variable (ρ)

theorem eigComp_eq (s : 𝓞 E →+* ℂ) (x : W) : eigComp ρ s x = proj ρ s x := by
  classical
  have hsup : (⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s}, eigSp ρ σ') ≤ LinearMap.ker (proj ρ s) := by
    refine iSup₂_le fun t ht => ?_
    intro y hy
    exact LinearMap.mem_ker.mpr (proj_eig_ne hy (Ne.symm ht))
  have hex : ∃ p ∈ eigSp ρ s, x - p ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s}, eigSp ρ σ' := by
    refine ⟨proj ρ s x, proj_mem ρ s x, ?_⟩
    have h1 := sum_proj ρ x
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at h1
    rw [sub_eq_iff_eq_add'.mpr h1.symm]
    refine Submodule.sum_mem _ fun t ht => ?_
    have hts : t ≠ s := Finset.ne_of_mem_erase ht
    exact Submodule.mem_iSup_of_mem t (Submodule.mem_iSup_of_mem hts (proj_mem ρ t x))
  unfold eigComp
  rw [dif_pos hex]
  have h2 := hsup hex.choose_spec.2
  rw [LinearMap.mem_ker, map_sub, proj_eig_self hex.choose_spec.1, sub_eq_zero] at h2
  exact h2.symm

end Emb

section Riem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  (R : RiemLat E g Λ)

theorem ip_add_right (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' :=
  add_dotProduct _ _ _

theorem ip_smul_right (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y :=
  smul_dotProduct _ _ _

theorem ip_conj (x y : Fin g → ℂ) : conj (R.ip x y) = R.ip y x := by
  simp only [RiemLat.ip, dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, RCLike.star_def,
    Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hh : conj (R.Hm i j) = R.Hm j i := by simpa [RCLike.star_def] using R.herm.apply j i
  rw [hh]
  ring

theorem ip_add_left (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  simp only [RiemLat.ip, star_add, Matrix.mulVec_add, dotProduct_add]

theorem ip_smul_left (c : ℂ) (x y : Fin g → ℂ) : R.ip (c • x) y = conj c * R.ip x y := by
  simp only [RiemLat.ip, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, RCLike.star_def]

def ipR (x : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun := R.ip x
  map_add' := ip_add_right R x
  map_smul' c y := ip_smul_right R c x y

theorem ip_sum_right {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (x : Fin g → ℂ) :
    R.ip x (∑ i ∈ t, f i) = ∑ i ∈ t, R.ip x (f i) := map_sum (ipR R x) f t

theorem ip_sum_left {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (y : Fin g → ℂ) :
    R.ip (∑ i ∈ t, f i) y = ∑ i ∈ t, R.ip (f i) y := by
  rw [← ip_conj R y, ip_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => ip_conj R y (f i)

theorem ip_zero_right (x : Fin g → ℂ) : R.ip x 0 = 0 := map_zero (ipR R x)

theorem ip_zero_left (x : Fin g → ℂ) : R.ip 0 x = 0 := by
  rw [← ip_conj, ip_zero_right, map_zero]

theorem eq_zero_of_re {x : Fin g → ℂ} (h : (R.ip x x).re = 0) : x = 0 := by
  by_contra hx
  exact (R.pos x hx).ne' h

def imB : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (R.ip x y).im)
    (fun x x' y => by rw [ip_add_left, Complex.add_im])
    (fun c x y => by rw [← Complex.coe_smul, ip_smul_left, Complex.conj_ofReal, Complex.im_ofReal_mul, smul_eq_mul])
    (fun x y y' => by rw [ip_add_right, Complex.add_im])
    (fun c x y => by rw [← Complex.coe_smul, ip_smul_right, Complex.im_ofReal_mul, smul_eq_mul])

theorem imB_apply (x y : Fin g → ℂ) : imB R x y = (R.ip x y).im := rfl

theorem imB_P (x y : Λ) : imB R (R.P y) (R.P x) = R.form x y := R.im x y

theorem precomp_injective : Function.Injective R.P := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply R.unimod.1
  refine LinearMap.ext fun y => ?_
  have h := R.im x y
  rw [hx, zero_dotProduct, Complex.zero_im] at h
  rw [map_zero, LinearMap.zero_apply]
  exact_mod_cast h.symm

theorem basis_indep {ι : Type} [Fintype ι] (e : Module.Basis ι ℤ Λ) :
    LinearIndependent ℝ fun i => R.P (e i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro r hr j
  obtain ⟨f, hf⟩ := R.unimod.2 (e.coord j)
  have h := congrArg (fun z => imB R z (R.P f)) hr
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, imB_P, hf, map_zero,
    LinearMap.zero_apply] at h
  simpa [Finsupp.single_apply] using h

theorem span_top : Submodule.span ℝ (Set.range R.P) = ⊤ := by
  haveI := R.free
  haveI := R.fin
  let e := Module.Free.chooseBasis ℤ Λ
  have hli := basis_indep R e
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [← Module.finrank_eq_card_basis e, R.rank, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have htop := hli.span_eq_top_of_card_eq_finrank' hcard
  rw [eq_top_iff, ← htop]
  exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨e i, rfl⟩)

theorem real_indep {ι : Type} {v : ι → Λ} (h : LinearIndependent ℤ v) :
    LinearIndependent ℝ fun i => R.P (v i) := by
  haveI := R.free
  haveI := R.fin
  let e := Module.Free.chooseBasis ℤ Λ
  let bR := Algebra.TensorProduct.basis ℝ e
  let L : TensorProduct ℤ ℝ Λ →ₗ[ℝ] (Fin g → ℂ) := LinearMap.liftBaseChange ℝ R.P.toIntLinearMap
  have hL : ∀ (r : ℝ) (y : Λ), L (TensorProduct.tmul ℤ r y) = r • R.P y := fun r y => by
    simp [L, LinearMap.liftBaseChange_tmul]
  have hli := basis_indep R e
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    rw [← bR.sum_repr z] at hz
    rw [map_sum] at hz
    simp only [map_smul, bR, Algebra.TensorProduct.basis_apply, hL, one_smul] at hz
    have h0 := Fintype.linearIndependent_iff.mp hli _ hz
    rw [← bR.sum_repr z]
    simp [bR, h0]
  have h2 := (Module.Flat.linearIndependent_one_tmul (S := ℝ) h).map' L hker
  have h3 : (fun i => R.P (v i)) = (L ∘ fun x => TensorProduct.tmul ℤ (1 : ℝ) (v x)) := by
    funext i
    simp [hL]
  rw [h3]
  exact h2

theorem emb_conj (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : s (IsCMField.ringOfIntegersComplexConj E a) = conj (s a) := by
  rw [← extE_apply s, ← extE_apply s a]
  exact IsCMField.complexEmbedding_complexConj (K := E) (extE s) _

theorem ip_adj (a : 𝓞 E) (x y : Fin g → ℂ) :
    R.ip y (R.B a x) = R.ip (R.B (IsCMField.ringOfIntegersComplexConj E a) y) x := by
  set a' := IsCMField.ringOfIntegersComplexConj E a with ha'
  have hadj : ∀ u v : Λ, R.form (a • v) u = R.form v (a' • u) := fun u v => R.adj a a' rfl v u
  have hlat : ∀ u v : Λ, (R.ip (R.P u) (R.B a (R.P v))).im = (R.ip (R.B a' (R.P u)) (R.P v)).im := by
    intro u v
    rw [← R.act, ← R.act, ← imB_apply, ← imB_apply, imB_P, imB_P, hadj]
  have hIm : ∀ u v : Fin g → ℂ, (R.ip u (R.B a v)).im = (R.ip (R.B a' u) v).im := by
    let F := (imB R).compl₂ ((R.B a).restrictScalars ℝ)
    let G := (imB R).comp ((R.B a').restrictScalars ℝ)
    have hFG : F = G := by
      refine LinearMap.ext_on_range (span_top R) fun u => ?_
      refine LinearMap.ext_on_range (span_top R) fun v => ?_
      simp only [F, G, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply, imB_apply]
      exact hlat u v
    intro u v
    have h0 := congrArg (fun f => f u v) hFG
    simpa [F, G, imB_apply] using h0
  apply Complex.ext
  · have h1 := hIm y (Complex.I • x)
    rw [map_smul, ip_smul_right, ip_smul_right] at h1
    simpa using h1
  · exact hIm y x

theorem ip_orth {s s' : 𝓞 E →+* ℂ} (h : s ≠ s') {x y : Fin g → ℂ} (hx : x ∈ eigSp R.B s)
    (hy : y ∈ eigSp R.B s') : R.ip x y = 0 := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h
  have h1 := ip_adj R a y x
  rw [mem_eig.1 hy, mem_eig.1 hx, ip_smul_right, ip_smul_left, emb_conj, Complex.conj_conj] at h1
  have h2 : (s a - s' a) * R.ip x y = 0 := by rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)

theorem ip_act (a : 𝓞 E) (x y : Fin g → ℂ) :
    R.ip x (R.B a y) = ∑ s : 𝓞 E →+* ℂ, s a * R.ip (proj R.B s x) (proj R.B s y) := by
  conv_lhs => rw [← sum_proj R.B x, act_apply R.B a y]
  rw [ip_sum_left]
  simp_rw [ip_sum_right, ip_smul_right]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single t]
  · intro u _ hut
    rw [ip_orth R (Ne.symm hut) (proj_mem _ t x) (proj_mem _ u y), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem gram_conj {I : Submodule (𝓞 E) Λ} (hI : IsIsoSub R.form I) (s : 𝓞 E →+* ℂ) {v w : Λ} (hv : v ∈ I)
    (hw : w ∈ I) :
    R.ip (proj R.B ((starRingEnd ℂ).comp s) (R.P v)) (proj R.B ((starRingEnd ℂ).comp s) (R.P w)) =
      conj (R.ip (proj R.B s (R.P v)) (proj R.B s (R.P w))) := by
  refine conj_of_real (h := fun t => R.ip (proj R.B t (R.P v)) (proj R.B t (R.P w))) (fun a => ?_) s
  rw [← ip_act, ← R.act, ← imB_apply, imB_P, hI _ (I.smul_mem a hw) _ hv, Int.cast_zero]

private theorem coef_ne_lemma {u t : 𝓞 E →+* ℂ} (h : u ≠ t) :
    ∑ j, coef j u * t (RingOfIntegers.basis E j) = 0 := by
  classical
  have h0 := emb_uniq₂ (W := ℂ) (w := fun u => ∑ j, coef j u * t (RingOfIntegers.basis E j))
    (w' := fun u => if u = t then 1 else 0) (fun a => by
      have h1 := dec_spec (W := ℂ) (RingHom.toAddMonoidHom t) a
      simp only [smul_eq_mul] at h1
      simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact h1.symm) u
  simpa [h] using h0

private theorem ker_conj_lemma_2 {I : Submodule (𝓞 E) Λ} (hI : IsIsoSub R.form I) (s : 𝓞 E →+* ℂ) {r : ℕ}
    {v : Fin r → Λ} (hv : ∀ a, v a ∈ I) (c : Fin r → ℂ)
    (hc : ∑ a, c a • proj R.B s (R.P (v a)) = 0) :
    ∑ a, conj (c a) • proj R.B ((starRingEnd ℂ).comp s) (R.P (v a)) = 0 := by
  apply eq_zero_of_re R
  have hG : ∀ a b, R.ip (proj R.B ((starRingEnd ℂ).comp s) (R.P (v a)))
      (proj R.B ((starRingEnd ℂ).comp s) (R.P (v b))) =
      conj (R.ip (proj R.B s (R.P (v a))) (proj R.B s (R.P (v b)))) :=
    fun a b => gram_conj R hI s (hv a) (hv b)
  have h1 : conj (R.ip (∑ a, c a • proj R.B s (R.P (v a))) (∑ a, c a • proj R.B s (R.P (v a)))) = 0 := by
    rw [hc, ip_zero_left, map_zero]
  simp only [ip_sum_left, ip_sum_right, ip_smul_left, ip_smul_right, map_sum, map_mul,
    Complex.conj_conj] at h1
  simp only [ip_sum_left, ip_sum_right, ip_smul_left, ip_smul_right, hG, Complex.conj_conj]
  rw [h1, Complex.zero_re]

theorem proj_indep {I : Submodule (𝓞 E) Λ} (hI : IsIsoSub R.form I) (s : 𝓞 E →+* ℂ) {r : ℕ} {v : Fin r → Λ}
    (hv : ∀ a, v a ∈ I) (hli : LinearIndependent (𝓞 E) v) :
    LinearIndependent ℂ fun a => proj R.B s (R.P (v a)) := by
  classical
  have hZ : LinearIndependent ℤ
      (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin r => RingOfIntegers.basis E p.1 • v p.2) :=
    linearIndependent_smul (RingOfIntegers.basis E).linearIndependent hli
  have hRl := real_indep R hZ
  have key : ∀ γ : Fin r → (𝓞 E →+* ℂ) → ℂ, (∀ a t, γ a ((starRingEnd ℂ).comp t) = conj (γ a t)) →
      ∑ a, ∑ t, γ a t • proj R.B t (R.P (v a)) = 0 → ∀ a t, γ a t = 0 := by
    intro γ hγ h0
    let x : Fin r → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ := fun a j => ∑ t, γ a t * coef j t
    have hxreal : ∀ a j, conj (x a j) = x a j := by
      intro a j
      simp only [x, map_sum, map_mul]
      exact Fintype.sum_equiv (cjEquiv E) _ _ (fun t => by simp [cjEquiv, hγ, coef_conj])
    have hop : ∀ a (y : Fin g → ℂ), ∑ t, γ a t • proj R.B t y =
        ∑ j, x a j • R.B (RingOfIntegers.basis E j) y := by
      intro a y
      simp only [x, proj_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
    have hsum : ∑ p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin r,
        (x p.2 p.1).re • R.P (RingOfIntegers.basis E p.1 • v p.2) = 0 := by
      rw [← h0, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hop]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [R.act]
      have hx : x a j = ((x a j).re : ℂ) := (Complex.conj_eq_iff_re.mp (hxreal a j)).symm
      conv_rhs => rw [hx]
      rw [Complex.coe_smul]
    have hre : ∀ a j, (x a j).re = 0 := fun a j => Fintype.linearIndependent_iff.mp hRl _ hsum (j, a)
    have hx0 : ∀ a j, x a j = 0 := fun a j => by
      rw [← Complex.conj_eq_iff_re.mp (hxreal a j), hre, Complex.ofReal_zero]
    intro a t
    calc γ a t = ∑ u, γ a u * (if u = t then 1 else 0) := by simp
      _ = ∑ u, γ a u * ∑ j, coef j u * t (RingOfIntegers.basis E j) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          by_cases hu : u = t
          · subst hu
            rw [if_pos rfl, sum_coef]
          · rw [if_neg hu, coef_ne_lemma hu]
      _ = ∑ j, x a j * t (RingOfIntegers.basis E j) := by
          simp only [x, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => by ring
      _ = 0 := by simp [hx0]
  have main : ∀ c : Fin r → ℂ, ∑ a, c a • proj R.B s (R.P (v a)) = 0 →
      ∀ a, c a + (if s = (starRingEnd ℂ).comp s then conj (c a) else 0) = 0 := by
    intro c hc a
    have hc' := ker_conj_lemma_2 R hI s hv c hc
    let γ : Fin r → (𝓞 E →+* ℂ) → ℂ := fun a t =>
      (if t = s then c a else 0) + (if t = (starRingEnd ℂ).comp s then conj (c a) else 0)
    have hγ : ∀ a t, γ a ((starRingEnd ℂ).comp t) = conj (γ a t) := by
      intro a t
      have e1 : ((starRingEnd ℂ).comp t = s) ↔ (t = (starRingEnd ℂ).comp s) :=
        ⟨fun h => by rw [← h, cj_cj], fun h => by rw [h, cj_cj]⟩
      have e2 : ((starRingEnd ℂ).comp t = (starRingEnd ℂ).comp s) ↔ (t = s) :=
        ⟨fun h => by rw [← cj_cj t, h, cj_cj], fun h => by rw [h]⟩
      simp only [γ]
      rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl, map_add, apply_ite (starRingEnd ℂ),
        apply_ite (starRingEnd ℂ), map_zero, Complex.conj_conj, add_comm]
    have hzero : ∑ a, ∑ t, γ a t • proj R.B t (R.P (v a)) = 0 := by
      simp only [γ, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [hc, hc', add_zero]
    have h3 := key γ hγ hzero a s
    simpa [γ] using h3
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have h1 := main c hc a
  have h2 : Complex.I * c a + (if s = (starRingEnd ℂ).comp s then conj (Complex.I * c a) else 0) = 0 :=
    main (fun a => Complex.I * c a) (by
      simp only [mul_smul]
      rw [← Finset.smul_sum, hc, smul_zero]) a
  by_cases hs : s = (starRingEnd ℂ).comp s
  · rw [if_pos hs] at h1 h2
    rw [map_mul, Complex.conj_I] at h2
    have h4 : (2 : ℂ) * Complex.I * c a = 0 := by linear_combination Complex.I * h1 + h2
    simpa [Complex.I_ne_zero] using h4
  · rw [if_neg hs, add_zero] at h1
    exact h1

end Riem

end LevelTowerAlt
