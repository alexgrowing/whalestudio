import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct

namespace GlobalTheory.SmGL.Stages

section Abstract

variable {F G M W X Y Z : Type} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] [AddCommGroup Z] [Module F Z]

def mkInd {P : Subgroup G} (σ : Representation F P W) (f : G → W)
    (h1 : ∀ (p : P) (g : G), f (p * g) = σ p (f g)) (h2 : ∀ᶠ u in 𝓝 (1 : G), ∀ x, f (x * u) = f x) :
    smoothPart (ind P σ) :=
  ⟨⟨f, h1⟩, mem_smoothPart_of_nhds (h2.mono fun _ hu => Subtype.ext (funext hu))⟩

theorem eventually_inv {P : Subgroup G} {σ : Representation F P W} (f : smoothPart (ind P σ)) :
    ∀ᶠ u in 𝓝 (1 : G), ∀ x, f.1.1 (x * u) = f.1.1 x :=
  Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun g hg x =>
    congrFun (congrArg Subtype.val (show ind P σ g f.1 = f.1 from hg)) x

theorem trans_ind {Q R : Subgroup G} (hRQ : R ≤ Q) (Θ : Representation F Q Y) (ρ : Representation F R Z)
    (ev : Y →ₗ[F] Z) (hev : ∀ (r : R) y, ev (Θ ⟨r, hRQ r.2⟩ y) = ρ r (ev y))
    (hinj : ∀ y, (∀ q, ev (Θ q y) = 0) → y = 0)
    (hsurj : ∀ φ : Q → Z, (∀ (r : R) q, φ (⟨r, hRQ r.2⟩ * q) = ρ r (φ q)) →
      (∀ᶠ u in 𝓝 (1 : Q), ∀ q, φ (q * u) = φ q) → ∃ y, ∀ q, ev (Θ q y) = φ q) :
    Nonempty ((smInd Q Θ).Equiv (smInd R ρ)) := by
  let T : smoothPart (ind Q Θ) →ₗ[F] smoothPart (ind R ρ) :=
    { toFun := fun f => mkInd ρ (fun g => ev (f.1.1 g))
        (fun r g => by rw [← hev, ← f.1.2 ⟨r, hRQ r.2⟩ g])
        ((eventually_inv f).mono fun u hu x => by rw [hu])
      map_add' := fun f g => by ext x; exact map_add ev _ _
      map_smul' := fun c f => by ext x; exact map_smul ev _ _ }
  have hext : ∀ y y', (∀ q, ev (Θ q y) = ev (Θ q y')) → y = y' := fun y y' h =>
    sub_eq_zero.1 (hinj _ fun q => by rw [map_sub, map_sub, h, sub_self])
  have h1 : Function.Injective T := by
    intro f f' h
    ext g
    refine hext _ _ fun q => ?_
    rw [← f.1.2 q g, ← f'.1.2 q g]
    exact congrFun (congrArg (fun φ => φ.1.1) h) _
  have h2 : Function.Surjective T := by
    intro h
    have key : ∀ g : G, ∃ y, ∀ q : Q, ev (Θ q y) = h.1.1 (q * g) := fun g => by
      refine hsurj (fun q => h.1.1 (q * g)) (fun r q => ?_) ?_
      · rw [← h.1.2 r, ← mul_assoc]; rfl
      · have hc : Tendsto (fun u : Q => g⁻¹ * u * g) (𝓝 1) (𝓝 1) :=
          Continuous.tendsto' (by fun_prop) _ _ (by simp)
        refine (hc.eventually (eventually_inv h)).mono fun u hu q => ?_
        rw [← hu (q * g)]
        simp [mul_assoc]
    choose y hy using key
    refine ⟨mkInd Θ y (fun p g => hext _ _ fun q => ?_)
      ((eventually_inv h).mono fun u hu x => hext _ _ fun q => ?_), ?_⟩
    · rw [← Module.End.mul_apply, ← map_mul, hy, hy, ← mul_assoc]; rfl
    · rw [hy, hy, ← mul_assoc, hu]
    · ext g
      exact (by simpa using hy g 1 : ev (y g) = h.1.1 g)
  exact ⟨.mk (LinearEquiv.ofBijective T ⟨h1, h2⟩) fun g => by ext f x; rfl⟩

def evalAt {P : Subgroup M} (σ : Representation F P W) (m : M) : smoothPart (ind P σ) →ₗ[F] W where
  toFun f := f.1.1 m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coord_rTensor {ι : Type} [DecidableEq ι] (b : Module.Basis ι F X) (f : Y →ₗ[F] W) (y : Y ⊗[F] X)
    (i : ι) : TensorProduct.equivFinsuppOfBasisRight b (f.rTensor X y) i =
      f (TensorProduct.equivFinsuppOfBasisRight b y i) := by
  induction y with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul y x => simp

theorem tensor_inj {P : Subgroup M} (σ : Representation F P W) (y : smoothPart (ind P σ) ⊗[F] X)
    (h : ∀ m, (evalAt σ m).rTensor X y = 0) : y = 0 := by
  classical
  let b := Module.Free.chooseBasis F X
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i m
  have := coord_rTensor b (evalAt σ m) y i
  rw [h] at this
  exact this.symm.trans (by simp)

theorem tensor_surj {P : Subgroup M} (σ : Representation F P W) {K : Set M} (hK : IsCompact K)
    (hPK : ∀ m, ∃ p : P, ∃ c ∈ K, m = p * c) (ψ : M → W ⊗[F] X)
    (h1 : ∀ (p : P) m, ψ (p * m) = (σ p).rTensor X (ψ m))
    (h2 : ∀ᶠ u in 𝓝 (1 : M), ∀ x, ψ (x * u) = ψ x) :
    ∃ y : smoothPart (ind P σ) ⊗[F] X, ∀ m, (evalAt σ m).rTensor X y = ψ m := by
  classical
  let b := Module.Free.chooseBasis F X
  let E := TensorProduct.equivFinsuppOfBasisRight (M := W) b
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {z | ψ z = ψ x}) fun x _ => by
    have hc : Tendsto (fun z : M => x⁻¹ * z) (𝓝 x) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact (hc.eventually h2).mono fun z hz => by simpa using hz x
  let f := fun i => mkInd σ (fun m => E (ψ m) i) (fun p m => by rw [h1, coord_rTensor])
    (h2.mono fun u hu x => by rw [hu])
  have hf : ∀ i, f i ≠ 0 → i ∈ t.biUnion fun x => (E (ψ x)).support := fun i hi => by
    by_contra hn
    apply hi
    ext m
    obtain ⟨p, c, hc, rfl⟩ := hPK m
    obtain ⟨x, hx, hcx⟩ := Set.mem_iUnion₂.1 (ht hc)
    have h0 : E (ψ x) i = 0 := by
      by_contra h0
      exact hn (Finset.mem_biUnion.2 ⟨x, hx, Finsupp.mem_support_iff.2 h0⟩)
    show E (ψ (p * c)) i = 0
    rw [h1, coord_rTensor, show ψ c = ψ x from hcx, h0, map_zero]
  refine ⟨(TensorProduct.equivFinsuppOfBasisRight b).symm (Finsupp.onFinset _ f hf), fun m => ?_⟩
  apply E.injective
  ext i
  rw [coord_rTensor, LinearEquiv.apply_symm_apply]
  rfl

theorem stage {Q R : Subgroup G} (hRQ : R ≤ Q) {P : Subgroup M} (ℓ : Q →* M) (s : M →* Q)
    (hs : Continuous s) (hls : ∀ m, ℓ (s m) = m) (hR : ∀ q : Q, (q : G) ∈ R ↔ ℓ q ∈ P)
    {K : Set M} (hK : IsCompact K) (hPK : ∀ m, ∃ p : P, ∃ c ∈ K, m = p * c)
    (σ : Representation F P W) (τ : Representation F Q X) (hτ : ∀ᶠ u in 𝓝 (1 : M), τ (s u) = 1)
    (Θ : Representation F Q Y) (j : Y ≃ₗ[F] smoothPart (ind P σ) ⊗[F] X)
    (hj : ∀ q y, j (Θ q y) = TensorProduct.map (smInd P σ (ℓ q)) (τ q) (j y))
    (ρ : Representation F R Z) (i : W ⊗[F] X ≃ₗ[F] Z)
    (hi : ∀ (q : Q) (h : (q : G) ∈ R) z,
      ρ ⟨q, h⟩ (i z) = i (TensorProduct.map (σ ⟨ℓ q, (hR q).1 h⟩) (τ q) z)) :
    Nonempty ((smInd Q Θ).Equiv (smInd R ρ)) := by
  have hval : ∀ (q : Q) (y : smoothPart (ind P σ) ⊗[F] X),
      (evalAt σ 1).rTensor X (TensorProduct.map (smInd P σ (ℓ q)) (τ q) y) =
        (τ q).lTensor W ((evalAt σ (ℓ q)).rTensor X y) := fun q y => by
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul f x =>
      simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
      congr 1
      exact congrArg f.1.1 (one_mul _)
  have hmul : ∀ (q q' : Q) (z : W ⊗[F] X),
      (τ q).lTensor W ((τ q').lTensor W z) = (τ (q * q')).lTensor W z := fun q q' z => by
    rw [map_mul, ← LinearMap.lTensor_comp_apply]; rfl
  have hone : ∀ z : W ⊗[F] X, (τ 1).lTensor W z = z := fun z => by
    rw [map_one, Module.End.one_eq_id, LinearMap.lTensor_id]; rfl
  refine trans_ind hRQ Θ ρ (i.toLinearMap ∘ₗ (evalAt σ 1).rTensor X ∘ₗ j.toLinearMap)
    (fun r y => ?_) (fun y hy => ?_) (fun φ h1 h2 => ?_)
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hj, hval, hi ⟨r, hRQ r.2⟩ r.2]
    congr 1
    generalize j y = z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul f x =>
      simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
      congr 1
      exact (congrArg f.1.1 (mul_one _).symm).trans (f.1.2 ⟨_, (hR ⟨r, hRQ r.2⟩).1 r.2⟩ 1)
  · rw [← j.map_eq_zero_iff]
    refine tensor_inj σ _ fun m => ?_
    have := hy (s m)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, i.map_eq_zero_iff] at this
    rw [hj, hval, hls] at this
    rw [← hone ((evalAt σ m).rTensor X _), ← inv_mul_cancel (s m), ← hmul, this, map_zero]
  · have h1' : ∀ (q : Q) (h : ℓ q ∈ P) (q' : Q), i.symm (φ (q * q')) =
        (σ ⟨ℓ q, h⟩).rTensor X ((τ q).lTensor W (i.symm (φ q'))) := fun q h q' => by
      rw [LinearEquiv.symm_apply_eq, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        ← hi q ((hR q).2 h), i.apply_symm_apply]
      exact h1 ⟨q, (hR q).2 h⟩ q'
    have hcomm : ∀ (A : W →ₗ[F] W) (B : X →ₗ[F] X) z,
        B.lTensor W (A.rTensor X z) = A.rTensor X (B.lTensor W z) := fun A B z => by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    obtain ⟨y, hy⟩ := tensor_surj σ hK hPK (fun m => (τ (s m)⁻¹).lTensor W (i.symm (φ (s m))))
      (fun p m => by
        rw [map_mul, h1' (s p) (by rw [hls]; exact p.2), hcomm, hmul]
        simp only [hls, mul_inv_rev, inv_mul_cancel_right])
      (by
        have hc : Tendsto s (𝓝 1) (𝓝 1) := hs.tendsto' _ _ (map_one s)
        have hc' : Tendsto (fun u : M => u⁻¹) (𝓝 1) (𝓝 1) := continuous_inv.tendsto' _ _ inv_one
        filter_upwards [hc.eventually h2, hc'.eventually hτ] with u hu hu' x
        rw [map_mul, hu, mul_inv_rev, map_mul, ← map_inv s u, hu', one_mul])
    refine ⟨j.symm y, fun q => ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hj, hval, j.apply_symm_apply, hy, hmul, ← LinearEquiv.eq_symm_apply]
    have h0 : ℓ (q * (s (ℓ q))⁻¹) = 1 := by rw [map_mul, map_inv, hls, mul_inv_cancel]
    have := h1' (q * (s (ℓ q))⁻¹) (h0 ▸ one_mem P) (s (ℓ q))
    rw [inv_mul_cancel_right, show (⟨_, h0 ▸ one_mem P⟩ : P) = 1 from Subtype.ext h0, map_one,
      Module.End.one_eq_id, LinearMap.rTensor_id] at this
    exact this.symm

end Abstract

section Blocks

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c ab bc n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype ab] [DecidableEq ab] [Fintype bc] [DecidableEq bc] [Fintype n] [DecidableEq n]
  {W V₁ V₂ V₃ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]

def pr {R : Type} [CommRing R] (e : a ⊕ b ≃ n) : parab R (two e) →* GL a R × GL b R :=
  (leviTwo R a b).symm.toMonoidHom.comp (leviProj R (two e))

def sec {R : Type} [CommRing R] (e : a ⊕ b ≃ n) : GL a R × GL b R →* parab R (two e) :=
  (emb₂ R e).codRestrict _ fun _ => leviEmb_mem_parab R _ _

theorem pr_fst {R : Type} [CommRing R] (e : a ⊕ b ≃ n) (q : parab R (two e)) (i j : a) :
    ((pr e q).1 : Matrix a a R) i j = ((q : GL n R) : Matrix n n R) (e (.inl i)) (e (.inl j)) := rfl

theorem pr_snd {R : Type} [CommRing R] (e : a ⊕ b ≃ n) (q : parab R (two e)) (i j : b) :
    ((pr e q).2 : Matrix b b R) i j = ((q : GL n R) : Matrix n n R) (e (.inr i)) (e (.inr j)) := rfl

theorem pr_sec {R : Type} [CommRing R] (e : a ⊕ b ≃ n) (g : GL a R × GL b R) : pr e (sec e g) = g :=
  congrArg (leviTwo R a b).symm (leviProj_leviEmb R (two e) (leviTwo R a b g))

theorem continuous_sec {R : Type} [CommRing R] [TopologicalSpace R] (e : a ⊕ b ≃ n) :
    Continuous (sec (R := R) e) :=
  ((continuous_leviEmb R (two e)).comp (continuous_leviTwo R)).subtype_mk _

theorem det_pr {R : Type} [CommRing R] (e : a ⊕ b ≃ n) (q : parab R (two e)) :
    GeneralLinearGroup.det (q : GL n R) =
      GeneralLinearGroup.det (pr e q).1 * GeneralLinearGroup.det (pr e q).2 := by
  rw [det_parab, Fintype.prod_bool, mul_comm]
  rfl

def dl (e : a ⊕ b ≃ n) : parab k (two e) →* ℂˣ := (deltaHalf k (Two a b)).comp (leviProj k (two e))

theorem dl_apply (e : a ⊕ b ≃ n) (q : parab k (two e)) :
    dl e q = absPow k ((Fintype.card b : ℂ) / 2) (GeneralLinearGroup.det (pr e q).1) *
      absPow k (-(Fintype.card a : ℂ) / 2) (GeneralLinearGroup.det (pr e q).2) := by
  rw [← deltaHalf_two]
  exact congrArg (deltaHalf k (Two a b)) ((leviTwo k a b).apply_symm_apply _).symm

theorem dl_sec (e : a ⊕ b ≃ n) : ∀ᶠ u in 𝓝 (1 : GL a k × GL b k), dl e (sec e u) = 1 := by
  have h := ((isSmoothChar_deltaHalf k (m := Two a b)).comp (leviTwo k a b).toMonoidHom
    (continuous_leviTwo k)).mem_nhds (one_mem _)
  refine Filter.mem_of_superset h fun u hu => ?_
  exact (congrArg (deltaHalf k (Two a b)) (leviProj_leviEmb k (two e) (leviTwo k a b u))).trans hu

def dat (e : a ⊕ b ≃ n) (ρ : Representation ℂ (GL a k × GL b k) W) :
    Representation ℂ (parab k (two e)) W :=
  (twist (ρ.comp (leviTwo k a b).symm.toMonoidHom) (deltaHalf k (Two a b))).comp (leviProj k (two e))

theorem dat_apply (e : a ⊕ b ≃ n) (ρ : Representation ℂ (GL a k × GL b k) W) (q : parab k (two e))
    (w : W) : dat e ρ q w = (dl e q : ℂ) • ρ (pr e q) w := rfl

theorem iwasawa_two (e : a ⊕ b ≃ n) (g : GL n k) :
    ∃ p : parab k (two e), ∃ c ∈ (KO k n : Set (GL n k)), g = p * c := by
  obtain ⟨p, hp, c, hc, h⟩ := iwasawa_blockTriangular k n (fun i => (blk (two e) i).toNat) g
  refine ⟨⟨p, fun i j hij => hp ?_⟩, c, hc, h⟩
  revert hij
  dsimp only
  cases blk (two e) i <;> cases blk (two e) j <;> simp

def tauSnd (e : a ⊕ b ≃ n) (π : Representation ℂ (GL b k) W) : Representation ℂ (parab k (two e)) W :=
  twist (π.comp ((MonoidHom.snd _ _).comp (pr e))) (dl e)

def tauFst (e : a ⊕ b ≃ n) (π : Representation ℂ (GL a k) W) : Representation ℂ (parab k (two e)) W :=
  twist (π.comp ((MonoidHom.fst _ _).comp (pr e))) (dl e)

theorem tauSnd_apply (e : a ⊕ b ≃ n) (π : Representation ℂ (GL b k) W) (q : parab k (two e)) (w : W) :
    tauSnd e π q w = (dl e q : ℂ) • π (pr e q).2 w := rfl

theorem tauFst_apply (e : a ⊕ b ≃ n) (π : Representation ℂ (GL a k) W) (q : parab k (two e)) (w : W) :
    tauFst e π q w = (dl e q : ℂ) • π (pr e q).1 w := rfl

theorem dat_snd (e : a ⊕ b ≃ n) (π₁ : Representation ℂ (GL a k) V₁) (π₂ : Representation ℂ (GL b k) V₂)
    (q : parab k (two e)) (y : V₁ ⊗[ℂ] V₂) :
    dat e (extTensor π₁ π₂) q y = TensorProduct.map (π₁ (pr e q).1) (tauSnd e π₂ q) y := by
  induction y with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f x =>
    rw [dat_apply, extTensor_tmul, TensorProduct.map_tmul, ← TensorProduct.tmul_smul, tauSnd_apply]

theorem dat_fst (e : a ⊕ b ≃ n) (π₁ : Representation ℂ (GL a k) V₁) (π₂ : Representation ℂ (GL b k) V₂)
    (q : parab k (two e)) (y : V₁ ⊗[ℂ] V₂) :
    TensorProduct.comm ℂ V₁ V₂ (dat e (extTensor π₁ π₂) q y) =
      TensorProduct.map (π₂ (pr e q).2) (tauFst e π₁ q) (TensorProduct.comm ℂ V₁ V₂ y) := by
  induction y with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f x =>
    rw [dat_apply, extTensor_tmul, map_smul, TensorProduct.comm_tmul, TensorProduct.comm_tmul,
      TensorProduct.map_tmul, ← TensorProduct.tmul_smul, tauFst_apply]

theorem stage_fst (e : ab ⊕ c ≃ n) (f : a ⊕ b ≃ ab) {R : Subgroup (GL n k)} (hRQ : R ≤ parab k (two e))
    (hR : ∀ q : parab k (two e), (q : GL n k) ∈ R ↔ (pr e q).1 ∈ parab k (two f))
    (σ : Representation ℂ (parab k (two f)) V₁) (π : Representation ℂ (GL c k) V₂)
    (ρ : Representation ℂ R W) (i : V₁ ⊗[ℂ] V₂ ≃ₗ[ℂ] W)
    (hi : ∀ (q : parab k (two e)) (h : (q : GL n k) ∈ R) z,
      ρ ⟨q, h⟩ (i z) = i (TensorProduct.map (σ ⟨(pr e q).1, (hR q).1 h⟩) (tauSnd e π q) z)) :
    Nonempty ((smInd _ (dat e (extTensor (smInd _ σ) π))).Equiv (smInd R ρ)) :=
  stage hRQ ((MonoidHom.fst _ _).comp (pr e)) ((sec e).comp (MonoidHom.inl _ _))
    ((continuous_sec e).comp (Continuous.prodMk_left 1))
    (fun m => congrArg Prod.fst (pr_sec e (m, 1))) hR SplitFlip.isCompact_KO (iwasawa_two f) σ (tauSnd e π)
    ((((Continuous.prodMk_left 1).tendsto 1).eventually (dl_sec e)).mono fun u hu => by
      ext v
      show tauSnd e π (sec e (u, 1)) v = v
      rw [tauSnd_apply, hu, pr_sec]; simp)
    _ (.refl _ _) (fun q y => dat_snd e _ π q y) ρ i hi

theorem stage_snd (e : a ⊕ bc ≃ n) (f : b ⊕ c ≃ bc) {R : Subgroup (GL n k)} (hRQ : R ≤ parab k (two e))
    (hR : ∀ q : parab k (two e), (q : GL n k) ∈ R ↔ (pr e q).2 ∈ parab k (two f))
    (σ : Representation ℂ (parab k (two f)) V₁) (π : Representation ℂ (GL a k) V₂)
    (ρ : Representation ℂ R W) (i : V₁ ⊗[ℂ] V₂ ≃ₗ[ℂ] W)
    (hi : ∀ (q : parab k (two e)) (h : (q : GL n k) ∈ R) z,
      ρ ⟨q, h⟩ (i z) = i (TensorProduct.map (σ ⟨(pr e q).2, (hR q).1 h⟩) (tauFst e π q) z)) :
    Nonempty ((smInd _ (dat e (extTensor π (smInd _ σ)))).Equiv (smInd R ρ)) :=
  stage hRQ ((MonoidHom.snd _ _).comp (pr e)) ((sec e).comp (MonoidHom.inr _ _))
    ((continuous_sec e).comp (Continuous.prodMk_right 1))
    (fun m => congrArg Prod.snd (pr_sec e (1, m))) hR SplitFlip.isCompact_KO (iwasawa_two f) σ (tauFst e π)
    ((((Continuous.prodMk_right 1).tendsto 1).eventually (dl_sec e)).mono fun u hu => by
      ext v
      show tauFst e π (sec e (1, u)) v = v
      rw [tauFst_apply, hu, pr_sec]; simp)
    _ (TensorProduct.comm _ _ _) (fun q y => dat_fst e π _ q y) ρ i hi

theorem action_eq (e₁ : ab ⊕ c ≃ n) (f₁ : a ⊕ b ≃ ab) (e₂ : a ⊕ bc ≃ n) (f₂ : b ⊕ c ≃ bc)
    (Ha : ∀ i, e₁ (.inl (f₁ (.inl i))) = e₂ (.inl i))
    (Hb : ∀ i, e₁ (.inl (f₁ (.inr i))) = e₂ (.inr (f₂ (.inl i))))
    (Hc : ∀ i, e₁ (.inr i) = e₂ (.inr (f₂ (.inr i))))
    (π₁ : Representation ℂ (GL a k) V₁) (π₂ : Representation ℂ (GL b k) V₂)
    (π₃ : Representation ℂ (GL c k) V₃) (q₁ : parab k (two e₁)) (q₂ : parab k (two e₂))
    (p₁ : parab k (two f₁)) (p₂ : parab k (two f₂)) (hq : (q₁ : GL n k) = q₂)
    (hp₁ : (pr e₁ q₁).1 = p₁) (hp₂ : (pr e₂ q₂).2 = p₂) (z : (V₂ ⊗[ℂ] V₃) ⊗[ℂ] V₁) :
    TensorProduct.map (dat f₁ (extTensor π₁ π₂) p₁) (tauSnd e₁ π₃ q₁)
        ((TensorProduct.assoc ℂ V₁ V₂ V₃).symm (TensorProduct.comm ℂ _ _ z)) =
      (TensorProduct.assoc ℂ V₁ V₂ V₃).symm (TensorProduct.comm ℂ _ _
        (TensorProduct.map (dat f₂ (extTensor π₂ π₃) p₂) (tauFst e₂ π₁ q₂) z)) := by
  have g₁ : (pr f₁ p₁).1 = (pr e₂ q₂).1 := by
    ext i j
    rw [pr_fst, ← hp₁, pr_fst, pr_fst, Ha, Ha, hq]
  have g₂ : (pr f₁ p₁).2 = (pr f₂ p₂).1 := by
    ext i j
    rw [pr_snd, ← hp₁, pr_fst, pr_fst, ← hp₂, pr_snd, Hb, Hb, hq]
  have g₃ : (pr e₁ q₁).2 = (pr f₂ p₂).2 := by
    ext i j
    rw [pr_snd, pr_snd, ← hp₂, pr_snd, Hc, Hc, hq]
  have hd : dl e₁ q₁ * dl f₁ p₁ = dl e₂ q₂ * dl f₂ p₂ := by
    have c₁ : (Fintype.card ab : ℂ) = Fintype.card a + Fintype.card b := by
      rw [← Fintype.card_congr f₁, Fintype.card_sum, Nat.cast_add]
    have c₂ : (Fintype.card bc : ℂ) = Fintype.card b + Fintype.card c := by
      rw [← Fintype.card_congr f₂, Fintype.card_sum, Nat.cast_add]
    rw [dl_apply, dl_apply, dl_apply, dl_apply, hp₁, hp₂, det_pr f₁ p₁, det_pr f₂ p₂, g₁, g₂, g₃, c₁, c₂]
    simp only [neg_add, add_div, absPow_add, MonoidHom.mul_apply, map_mul]
    generalize GeneralLinearGroup.det (pr e₂ q₂).1 = x
    generalize GeneralLinearGroup.det (pr f₂ p₂).1 = y
    generalize GeneralLinearGroup.det (pr f₂ p₂).2 = w
    apply Units.ext
    simp only [Units.val_mul]
    ring
  induction z with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul y x =>
    induction y with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul y z =>
      rw [TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, dat_apply, dat_apply, extTensor_tmul, extTensor_tmul, g₁, g₂,
        TensorProduct.comm_tmul, tauSnd_apply, tauFst_apply, g₃, TensorProduct.smul_tmul_smul,
        TensorProduct.smul_tmul_smul, map_smul, TensorProduct.assoc_symm_tmul, ← Units.val_mul,
        ← Units.val_mul, ← hd, mul_comm]

theorem ind₂_assoc (e₁ : ab ⊕ c ≃ n) (f₁ : a ⊕ b ≃ ab) (e₂ : a ⊕ bc ≃ n) (f₂ : b ⊕ c ≃ bc)
    (Ha : ∀ i, e₁ (.inl (f₁ (.inl i))) = e₂ (.inl i))
    (Hb : ∀ i, e₁ (.inl (f₁ (.inr i))) = e₂ (.inr (f₂ (.inl i))))
    (Hc : ∀ i, e₁ (.inr i) = e₂ (.inr (f₂ (.inr i))))
    (π₁ : Representation ℂ (GL a k) V₁) (π₂ : Representation ℂ (GL b k) V₂)
    (π₃ : Representation ℂ (GL c k) V₃) :
    Nonempty ((ind₂ e₁ (extTensor (ind₂ f₁ (extTensor π₁ π₂)) π₃)).Equiv
      (ind₂ e₂ (extTensor π₁ (ind₂ f₂ (extTensor π₂ π₃))))) := by
  let R : Subgroup (GL n k) := parab k (two e₁) ⊓ parab k (two e₂)
  have hR₁ : ∀ q : parab k (two e₁), (q : GL n k) ∈ R ↔ (pr e₁ q).1 ∈ parab k (two f₁) := fun q => by
    refine ⟨fun h => (mem_parab_two k).2 fun j i => ?_,
      fun h => ⟨q.2, (mem_parab_two k).2 fun j i => ?_⟩⟩
    · rw [pr_fst, Ha, Hb]
      exact (mem_parab_two k).1 h.2 _ _
    · obtain ⟨j | j, rfl⟩ := f₂.surjective j
      · rw [← Ha, ← Hb]
        exact (mem_parab_two k).1 h j i
      · rw [← Ha, ← Hc]
        exact (mem_parab_two k).1 q.2 _ _
  have hR₂ : ∀ q : parab k (two e₂), (q : GL n k) ∈ R ↔ (pr e₂ q).2 ∈ parab k (two f₂) := fun q => by
    refine ⟨fun h => (mem_parab_two k).2 fun j i => ?_,
      fun h => ⟨(mem_parab_two k).2 fun j i => ?_, q.2⟩⟩
    · rw [pr_snd, ← Hc, ← Hb]
      exact (mem_parab_two k).1 h.1 _ _
    · obtain ⟨i | i, rfl⟩ := f₁.surjective i
      · rw [Ha, Hc]
        exact (mem_parab_two k).1 q.2 _ _
      · rw [Hb, Hc]
        exact (mem_parab_two k).1 h j i
  let ι₁ : R →* parab k (two e₁) := Subgroup.inclusion inf_le_left
  let ρ : Representation ℂ R ((V₁ ⊗[ℂ] V₂) ⊗[ℂ] V₃) :=
    Representation.tprod ((dat f₁ (extTensor π₁ π₂)).comp
      ((((MonoidHom.fst _ _).comp (pr e₁)).comp ι₁).codRestrict _ fun r => (hR₁ (ι₁ r)).1 r.2))
      ((tauSnd e₁ π₃).comp ι₁)
  have hρ : ∀ (g : GL n k) (h : g ∈ R), ρ ⟨g, h⟩ = TensorProduct.map
      (dat f₁ (extTensor π₁ π₂) ⟨(pr e₁ ⟨g, h.1⟩).1, (hR₁ ⟨g, h.1⟩).1 h⟩) (tauSnd e₁ π₃ ⟨g, h.1⟩) :=
    fun g h => rfl
  have E₁ := stage_fst e₁ f₁ (R := R) inf_le_left hR₁ (dat f₁ (extTensor π₁ π₂)) π₃ ρ (.refl _ _)
    (fun q h z => by rw [hρ]; rfl)
  have E₂ := stage_snd e₂ f₂ (R := R) inf_le_right hR₂ (dat f₂ (extTensor π₂ π₃)) π₁ ρ
    ((TensorProduct.comm _ _ _).trans (TensorProduct.assoc _ _ _ _).symm)
    (fun q h z => by
      rw [hρ]
      exact action_eq e₁ f₁ e₂ f₂ Ha Hb Hc π₁ π₂ π₃ _ q _ _ rfl rfl rfl z)
  exact Nonempty.map2 (fun x y => x.trans y.symm) E₁ E₂

end Blocks

theorem prod₂_assoc : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r s t : ℕ) (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] (π₁ : Representation ℂ (GL (Fin r) k) V₁) (π₂ : Representation ℂ (GL (Fin s) k) V₂) (π₃ : Representation ℂ (GL (Fin t) k) V₃), IsSmooth π₁ → IsSmooth π₂ → IsSmooth π₃ → Nonempty ((prod₂ (prod₂ π₁ π₂) π₃).Equiv (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ (prod₂ π₂ π₃)))) := by
  intro k _ _ _ _ r s t V₁ V₂ V₃ _ _ _ _ _ _ π₁ π₂ π₃ _ _ _
  exact ind₂_assoc (stdSum rfl) (stdSum rfl) (stdSum (Nat.add_assoc r s t).symm) (stdSum rfl)
    (fun i => Fin.ext (by simp)) (fun i => Fin.ext (by simp)) (fun i => Fin.ext (by simp [add_assoc]))
    π₁ π₂ π₃

end GlobalTheory.SmGL.Stages
