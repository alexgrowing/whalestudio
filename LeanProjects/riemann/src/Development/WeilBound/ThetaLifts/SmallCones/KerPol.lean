import Development.WeilBound.ThetaLifts.SmallCones.KerGeo
import Development.WeilBound.ThetaLifts.LeviDeterminants.MCSpan

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open GlobalTheory.Doubling (absE)
open Matrix (vecMulVec)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem vv0 {S : Type} [CommRing S] (a : Fin n → S) : vecMulVec a (0 : Fin d → S) = 0 := by
  ext i j
  simp [Matrix.vecMulVec_apply]

def vL (n : ℕ) (b : Fin d → E) : (Fin n → E) →ₗ[E] Matrix (Fin n) (Fin d) E where
  toFun x := vecMulVec x b
  map_add' x y := Matrix.add_vecMulVec _ _ _
  map_smul' a x := Matrix.smul_vecMulVec _ _ _

def vR (d : ℕ) (a : Fin n → E) : (Fin d → E) →ₗ[E] Matrix (Fin n) (Fin d) E where
  toFun y := vecMulVec a y
  map_add' x y := Matrix.vecMulVec_add _ _ _
  map_smul' c x := Matrix.vecMulVec_smul _ _ _

@[simp] theorem vL_apply (b : Fin d → E) (x : Fin n → E) : vL n b x = vecMulVec x b := rfl
@[simp] theorem vR_apply (a : Fin n → E) (y : Fin d → E) : vR d a y = vecMulVec a y := rfl

def vA (a : Fin n → E) (b : Fin d → E) (ι' : Matrix (Fin d) (Fin d₁) E) : ((Fin n → E) × (Fin d₁ → E)) →ₗ[E] Matrix (Fin n) (Fin d) E :=
  (vL n b).coprod ((vR d a).comp ι'.mulVecLin)

def vB (a : Fin n → E) (b : Fin d → E) (ι : Matrix (Fin n) (Fin n₁) E) : ((Fin d → E) × (Fin n₁ → E)) →ₗ[E] Matrix (Fin n) (Fin d) E :=
  (vR d a).coprod ((vL n b).comp ι.mulVecLin)

theorem vA_apply (a : Fin n → E) (b : Fin d → E) (ι' : Matrix (Fin d) (Fin d₁) E) (t) :
    vA a b ι' t = vecMulVec t.1 b + vecMulVec a (ι' *ᵥ t.2) := rfl

theorem vB_apply (a : Fin n → E) (b : Fin d → E) (ι : Matrix (Fin n) (Fin n₁) E) (t) :
    vB a b ι t = vecMulVec a t.1 + vecMulVec (ι *ᵥ t.2) b := rfl

def isoX (d : ℕ) (H : Plane E n n₁) : Set (Ten F E n d) := {u | ∃ z, u = vecMulVec (incV F H.x) z}

def sumA (H : Plane E n n₁) (H' : Plane E d d₁) : Set (Ten F E n d) :=
  {u | ∃ y z, u = vecMulVec y (incV F H'.x) + vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z)}

def sumB (H : Plane E n n₁) (H' : Plane E d d₁) : Set (Ten F E n d) :=
  {u | ∃ z y, u = vecMulVec (incV F H.x) z + vecMulVec (incM F H.ι *ᵥ y) (incV F H'.x)}

variable (σ X W X₁ W₁) in

def PolT {T : Type} [AddCommGroup T] [Module E T] [Module F T] (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Ten F E n d)) (U : T →ₗ[E] Matrix (Fin n) (Fin d) E) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) F T) (z : Fin m → Matrix (Fin n) (Fin d) E), Polar σ X W X₁ W₁ ι ι' I (fun j => U (b j)) z

variable {H : Plane E n n₁} {H' : Plane E d d₁} {ε ε' : ℤ}

theorem one_gram (J : Matrix (Fin n) (Fin n) E) : (1 : Matrix (Fin n) (Fin n) E)ᵀ * J * (1 : Matrix (Fin n) (Fin n) E).map σ = J := by
  rw [Matrix.map_one _ (map_zero _) (map_one _)]; simp

theorem PG.nd_low (h : PG σ X X₁ H ε) (u) (hu : ∀ z, bf σ.toRingHom X.J (H.ι *ᵥ z) (H.ι *ᵥ u) = 0) : u = 0 := by
  refine h.inj u (h.rat.nd _ fun w => ?_)
  obtain ⟨s, t, z, rfl⟩ := h.rat.span w
  simp only [bf_add_r, bf_smul_r, h.rat.ix, h.rat.iy, h.rat.symm (H.ι *ᵥ z), hu, map_zero, mul_zero, add_zero]

theorem PG.nd_r (h : PG σ X X₁ H ε) (u) (hu : ∀ z, bf σ.toRingHom X.J z u = 0) : u = 0 :=
  h.rat.nd _ fun w => by rw [h.rat.symm, hu, map_zero, mul_zero]

theorem pol0 (hX : X.J.det ≠ 0) (h' : PG σ W W₁ H' ε') : PolT σ X W X W₁ 1 H'.ι (iso0 n H') (vL n H'.y) := by
  refine polar_of (vL n H'.y) (vL n H'.x) (fun t a => ⟨a • incV F t, by rw [vL_apply, incM_vv, Matrix.smul_vecMulVec]⟩)
    (fun t ht => nd_of_det hX t fun w => by simpa only [vL_apply, hT_vv, h'.rat.xy, mul_one] using ht w)
    (fun t t' => by simp only [vL_apply, hT_vv, h'.rat.yy, mul_zero]) (fun t t' => by simp only [vL_apply, hT_vv, h'.rat.xx, mul_zero])
    (fun t w => by rw [vL_apply, incM_vv, hT_vm (Or.inr h'.ad.yi)]) (fun t w => by rw [vL_apply, incM_vv, hT_vm (Or.inr h'.ad.xi)])
    (one_gram _) h'.gram fun x => ?_
  obtain ⟨s, t, z, e⟩ := span_r h'.rat x
  exact ⟨t, s, z, by rw [e, Matrix.one_mul, vL_apply, vL_apply]; abel⟩

theorem polX (h : PG σ X X₁ H ε) (hW : W.J.det ≠ 0) : PolT σ X W X₁ W H.ι 1 (isoX d H) (vR d H.y) := by
  refine polar_of (vR d H.y) (vR d H.x) (fun t a => ⟨a • incV F t, by rw [vR_apply, incM_vv, Matrix.vecMulVec_smul]⟩)
    (fun t ht => nd_of_det hW t fun w => by simpa only [vR_apply, hT_vv, h.rat.xy, one_mul] using ht w)
    (fun t t' => by simp only [vR_apply, hT_vv, h.rat.yy, zero_mul]) (fun t t' => by simp only [vR_apply, hT_vv, h.rat.xx, zero_mul])
    (fun t w => by rw [vR_apply, incM_vv, hT_vm (Or.inl h.ad.yi)]) (fun t w => by rw [vR_apply, incM_vv, hT_vm (Or.inl h.ad.xi)])
    h.gram (one_gram _) fun x => ?_
  obtain ⟨s, t, z, e⟩ := span_l h.rat x
  exact ⟨t, s, z, by rw [e, Matrix.transpose_one, Matrix.mul_one, vR_apply, vR_apply]; abel⟩

theorem polA (h : PG σ X X₁ H ε) (h' : PG σ W W₁ H' ε') : PolT σ X W X₁ W₁ H.ι H'.ι (sumA H H') (vA H.y H'.y H'.ι) := by
  refine polar_of (vA H.y H'.y H'.ι) (vA H.x H'.x H'.ι) (fun t a => ⟨a • incV F t.1, a • incV F t.2, by
      rw [vA_apply, incM_add, incM_vv, incM_vv, Matrix.smul_vecMulVec, Matrix.mulVec_smul, Matrix.vecMulVec_smul, inc_mulVec, smul_add]⟩)
    (fun t ht => Prod.ext (h.nd_r _ fun w => ?_) (h'.nd_low _ fun w => ?_))
    (fun t t' => by
      simp only [vA_apply, hT_add_l, hT_add_r, hT_vv, h'.rat.yy, h'.rat.yi, h'.rat.iy, h.rat.yy, mul_zero, zero_mul, add_zero])
    (fun t t' => by
      simp only [vA_apply, hT_add_l, hT_add_r, hT_vv, h'.rat.xx, h'.rat.xi, h'.rat.ix, h.rat.xx, mul_zero, zero_mul, add_zero])
    (fun t w => by rw [vA_apply, incM_add, incM_vv, incM_vv, hT_add_l, hT_vm (Or.inr h'.ad.yi), hT_vm (Or.inl h.ad.yi), add_zero])
    (fun t w => by rw [vA_apply, incM_add, incM_vv, incM_vv, hT_add_l, hT_vm (Or.inr h'.ad.xi), hT_vm (Or.inl h.ad.xi), add_zero])
    h.gram h'.gram fun x => ?_
  · have := ht (w, 0)
    simpa only [vA_apply, Matrix.mulVec_zero, vv0, add_zero, hT_add_r, hT_vv, h'.rat.xy, h'.rat.xi, mul_one,
      mul_zero] using this
  · have := ht (0, w)
    simpa only [vA_apply, Matrix.zero_vecMulVec, zero_add, hT_add_r, hT_vv, h.rat.xy, h'.rat.iy, one_mul, mul_zero] using this
  obtain ⟨s, t, z, e⟩ := span_r h'.rat x
  obtain ⟨s', t', z', rfl⟩ := span_l h.rat z
  refine ⟨(t, t'), (s, s'), z', ?_⟩
  rw [e, vA_apply, vA_apply, Matrix.add_mul, Matrix.add_mul, vv_mul_r, vv_mul_r]
  abel

theorem polB (h : PG σ X X₁ H ε) (h' : PG σ W W₁ H' ε') : PolT σ X W X₁ W₁ H.ι H'.ι (sumB H H') (vB H.y H'.y H.ι) := by
  refine polar_of (vB H.y H'.y H.ι) (vB H.x H'.x H.ι) (fun t a => ⟨a • incV F t.1, a • incV F t.2, by
      rw [vB_apply, incM_add, incM_vv, incM_vv, Matrix.vecMulVec_smul, Matrix.mulVec_smul, Matrix.smul_vecMulVec, inc_mulVec, smul_add]⟩)
    (fun t ht => Prod.ext (h'.nd_r _ fun w => ?_) (h.nd_low _ fun w => ?_))
    (fun t t' => by
      simp only [vB_apply, hT_add_l, hT_add_r, hT_vv, h'.rat.yy, h.rat.yi, h.rat.iy, h.rat.yy, mul_zero, zero_mul, add_zero])
    (fun t t' => by
      simp only [vB_apply, hT_add_l, hT_add_r, hT_vv, h'.rat.xx, h.rat.xi, h.rat.ix, h.rat.xx, mul_zero, zero_mul, add_zero])
    (fun t w => by rw [vB_apply, incM_add, incM_vv, incM_vv, hT_add_l, hT_vm (Or.inr h'.ad.yi), hT_vm (Or.inl h.ad.yi), add_zero])
    (fun t w => by rw [vB_apply, incM_add, incM_vv, incM_vv, hT_add_l, hT_vm (Or.inr h'.ad.xi), hT_vm (Or.inl h.ad.xi), add_zero])
    h.gram h'.gram fun x => ?_
  · have := ht (w, 0)
    simpa only [vB_apply, Matrix.mulVec_zero, Matrix.zero_vecMulVec, add_zero, hT_add_r, hT_vv, h.rat.xy, h.rat.xi, one_mul,
      zero_mul] using this
  · have := ht (0, w)
    simpa only [vB_apply, vv0, zero_add, hT_add_r, hT_vv, h'.rat.xy, h.rat.iy, mul_one, zero_mul] using this
  obtain ⟨s, t, z, e⟩ := span_l h.rat x
  obtain ⟨s', t', z', rfl⟩ := span_r h'.rat z
  refine ⟨(t, t'), (s, s'), z', ?_⟩
  rw [e, vB_apply, vB_apply, Matrix.mul_add, Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.mul_assoc]
  abel

variable {M : Model σ X W} {M₁ : Model σ X₁ W₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}

theorem isEv_sumA (hψ : IsStd B.ψ) (h' : PG σ W W₁ H' ε') (he : IsEv B M M₁ H.ι H'.ι (isoA H H') e) :
    IsEv B M M₁ H.ι H'.ι (sumA H H') e := by
  refine ⟨he.maps, he.Heisenberg₂, ?_, he.loc⟩
  rintro _ ⟨y, z, rfl⟩ Φ hΦ
  rw [← rho_rho_of _ _ _ _ (sy_of_hT (by rw [hT_vv, h'.ad.xi, mul_zero])), he.inv _ (Or.inl ⟨y, rfl⟩) _ (rho_mem M hψ _ hΦ),
    he.inv _ (Or.inr ⟨z, rfl⟩) _ hΦ]

theorem isEv_sumB (hψ : IsStd B.ψ) (h : PG σ X X₁ H ε) (he : IsEv B M M₁ H.ι H'.ι (isoB H H') e) :
    IsEv B M M₁ H.ι H'.ι (sumB H H') e := by
  refine ⟨he.maps, he.Heisenberg₂, ?_, he.loc⟩
  rintro _ ⟨y, z, rfl⟩ Φ hΦ
  rw [← rho_rho_of _ _ _ _ (sy_of_hT (by rw [hT_vv, h.ad.xi, zero_mul])), he.inv _ (Or.inl ⟨y, rfl⟩) _ (rho_mem M hψ _ hΦ),
    he.inv _ (Or.inr ⟨z, rfl⟩) _ hΦ]

section T

variable {T : Type} [AddCommGroup T] [Module E T] [Module F T] [IsScalarTower F E T] {ι : Matrix (Fin n) (Fin n₁) E}
  {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Ten F E n d)} {U : T →ₗ[E] Matrix (Fin n) (Fin d) E}

theorem lin_basis (b : Module.Basis (Fin m) F T) (t : T) :
    lin (fun j => U (b j)) (fun j => algebraMap F (AF F) (b.equivFun t j)) = incM F (U t) := by
  rw [← incM_lin]
  simp only [← LinearMap.map_smul_of_tower, ← map_sum, b.sum_equivFun]

theorem PolT.exp (hP : PolT σ X W X₁ W₁ ι ι' I U) (hE : ThetaExp) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    (he : IsEv B M M₁ ι ι' I e) : ∃ C : ℂ, C ≠ 0 ∧ ∀ Φ ∈ schA F _,
      HasSum (fun t : T => C * thetaSum F (e (M.co.rho B.ψ (incM F (U t)) Φ))) (thetaSum F Φ) := by
  obtain ⟨m, b, z, hP⟩ := hP
  obtain ⟨C, hC, h⟩ := hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m _ z hP
  refine ⟨C, hC, fun Φ hΦ => ?_⟩
  have := b.equivFun.toEquiv.hasSum_iff.2 (h Φ hΦ)
  convert this using 2 with t
  rw [← lin_basis b]
  rfl

theorem PolT.uniq (hP : PolT σ X W X₁ W₁ ι ι' I U) (hE : EvUniq) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {e'} (he : IsEv B M M₁ ι ι' I e) (he' : IsEv B M M₁ ι ι' I e') : ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F _, e' Φ = c • e Φ := by
  obtain ⟨m, b, z, hP⟩ := hP
  exact hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e e' he he' m _ z hP

theorem comp_ne {n₀ d₀ : ℕ} {X₀ : Spc F E n₀} {W₀ : Spc F E d₀} {M₀ : Model σ X₀ W₀} (hP : PolT σ X W X₁ W₁ ι ι' I U)
    (hE : ThetaExp) (hB : B.IsGood σ) (hM₀ : M₀.IsGood B.ψ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {κ κ' J}
    {e₀ : Fn F n₀ d₀ →ₗ[ℂ] Fn F n d} (he₀ : IsEv B M₀ M κ κ' J e₀) (he : IsEv B M M₁ ι ι' I e) :
    ∃ Φ ∈ schA F (Fin n₀ × Fin d₀), e (e₀ Φ) ≠ 0 := by
  by_contra h0
  push Not at h0
  obtain ⟨C, -, hC⟩ := hP.exp hE hB hM hM₁ he
  obtain ⟨Φ, hΦ, hne⟩ := ev_ne_zero hM₀ hM he₀
  have h1 : ∀ Ψ ∈ schA F (Fin n₀ × Fin d₀), thetaSum F (e₀ Ψ) = 0 := fun Ψ hΨ => by
    refine (hC _ (he₀.maps Ψ hΨ)).unique ?_
    convert hasSum_zero with t
    rw [← he₀.Heisenberg₂ _ _ hΨ, h0 _ (rho_mem M₀ hB.std _ hΨ)]
    simp [thetaSum]
  refine hne (thetaInj_of F _ B.ψ hB.std _ (he₀.maps Φ hΦ) fun w => ?_)
  obtain ⟨w, rfl⟩ := M.co.e.surjective w
  rw [← Darboux.rho, ← he₀.Heisenberg₂ _ _ hΦ, h1 _ (rho_mem M₀ hB.std _ hΦ)]

end T

theorem isEv_comp {n₂ d₂ : ℕ} {X₂ : Spc F E n₂} {W₂ : Spc F E d₂} {M₂ : Model σ X₂ W₂} (hψ : IsStd B.ψ) (hM : M.IsGood B.ψ)
    (hM₁ : M₁.IsGood B.ψ) (hM₂ : M₂.IsGood B.ψ) {ι ι' I κ κ' J} {e₂ : Fn F n₁ d₁ →ₗ[ℂ] Fn F n₂ d₂} (he : IsEv B M M₁ ι ι' I e)
    (he₂ : IsEv B M₁ M₂ κ κ' J e₂) (hne : ∃ Φ ∈ schA F (Fin n × Fin d), e₂ (e Φ) ≠ 0) {K : Set (Ten F E n d)}
    (hK : ∀ u ∈ K, u ∈ I ∨ ∃ w ∈ J, u = incM F ι * w * (incM F ι')ᵀ) : IsEv B M M₂ (ι * κ) (ι' * κ') K (e₂ ∘ₗ e) := by
  refine ⟨fun Φ hΦ => he₂.maps _ (he.maps Φ hΦ), fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_, ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← he₂.Heisenberg₂ _ _ (he.maps Φ hΦ), ← he.Heisenberg₂ _ _ hΦ]
    simp only [incM, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rcases hK u hu with h | ⟨w, hw, rfl⟩
    · rw [he.inv u h Φ hΦ]
    · rw [he.Heisenberg₂ _ _ hΦ, he₂.inv w hw _ (he.maps Φ hΦ)]
  obtain ⟨ei, ev, -, h1, h2⟩ := he.loc
  obtain ⟨ei₂, ev₂, -, k1, k2⟩ := he₂.loc
  have key : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      (e₂ ∘ₗ e) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((ei₂.comp ei) f) fun v => (ev₂ v ∘ₗ ev v) (φ v) := fun f φ a b => by
    rw [LinearMap.comp_apply, h2 f φ a b, k2 _ _ (fun v => (h1 v).2 ▸ Submodule.mem_map_of_mem (a v))
      (b.mono fun v hv => by rw [hv, (h1 v).1])]
    rfl
  refine ⟨ei₂.comp ei, fun v => ev₂ v ∘ₗ ev v, fun h0 => ?_,
    fun v => ⟨by rw [LinearMap.comp_apply, (h1 v).1, (k1 v).1], by rw [Submodule.map_comp, (h1 v).2, (k1 v).2]⟩, key⟩
  obtain ⟨Φ, hΦ, hn⟩ := hne
  refine hn ?_
  change (e₂ ∘ₗ e) Φ = 0
  clear hn
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨m, c, φ, a, b, rfl⟩ := PositivityTheory.ThKF0.Span.exists_sum_finprod hg
    have h1 : pureA F (f : _ → ℂ) (∑ k, c k • fun y => ∏ᶠ v, φ k v fun i => evalV F v (y i)) =
        ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
      funext x
      simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
      rw [mul_left_comm]
      rfl
    rw [h1, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [map_smul, key f (φ k) (a k) (((b k).and hM.std).mono fun v h => by rw [h.1, h.2]), h0]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  | zero => exact map_zero _
  | add _ _ _ _ a b => rw [map_add, a, b, add_zero]
  | smul _ _ _ a => rw [map_smul, a, smul_zero]

end PositivityTheory.ThKCT.Ker

end
