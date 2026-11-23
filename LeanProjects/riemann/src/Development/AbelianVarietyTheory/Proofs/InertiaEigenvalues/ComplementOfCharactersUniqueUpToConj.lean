import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.CharCancel

section Cancel

variable {K Γ V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem ennreal_volume_ratio_step_cancel (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (c : Γ → K) (e : (V × K) ≃ₗ[K] (W × K))
    (h : ∀ g v x, e (a g v, c g * x) = (b g (e (v, x)).1, c g * (e (v, x)).2))
    (v₀ : V) (hv : ∀ g, a g v₀ = c g • v₀) (hd : (e (v₀, 1)).2 ≠ 0) :
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  rcases hE : e (v₀, 1) with ⟨w', δ⟩
  have hd0 : δ ≠ 0 := by rw [hE] at hd; exact hd
  have hb : ∀ g, b g w' = c g • w' := by
    intro g
    have h1 := h g v₀ 1
    have h2 : ((a g v₀, c g * 1) : V × K) = c g • ((v₀, 1) : V × K) := by
      rw [hv]; simp
    rw [h2, map_smul, hE] at h1
    have h3 := congrArg Prod.fst h1
    simp at h3
    exact h3.symm
  refine ⟨{ toFun := fun v => (e (v, 0)).1 - ((e (v, 0)).2 / δ) • w'
            invFun := fun w => (e.symm (w, 0)).1 - (e.symm (w, 0)).2 • v₀
            map_add' := ?_, map_smul' := ?_, left_inv := ?_, right_inv := ?_ }, ?_⟩
  · intro x y
    have hxy : ((x + y, (0 : K)) : V × K) = (x, 0) + (y, 0) := by simp
    rw [hxy, map_add]
    simp only [Prod.fst_add, Prod.snd_add, add_div, add_smul]
    abel
  · intro s x
    have hsx : ((s • x, (0 : K)) : V × K) = s • (x, 0) := by simp
    rw [hsx, map_smul]
    simp [smul_sub, smul_smul, mul_div_assoc]
  · intro v
    dsimp only
    have key : (((e (v, 0)).1 - ((e (v, 0)).2 / δ) • w', (0 : K)) : W × K) =
        e (v, 0) - ((e (v, 0)).2 / δ) • e (v₀, 1) := by
      rw [hE]
      ext
      · simp
      · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        rw [div_mul_cancel₀ _ hd0, sub_self]
    rw [key, map_sub, map_smul, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    simp
  · intro w
    dsimp only
    have key : (((e.symm (w, 0)).1 - (e.symm (w, 0)).2 • v₀, (0 : K)) : V × K) =
        e.symm (w, 0) - (e.symm (w, 0)).2 • (v₀, 1) := by
      ext <;> simp
    rw [key, map_sub, map_smul, LinearEquiv.apply_symm_apply, hE]
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, zero_sub]
    rw [neg_div, mul_div_cancel_right₀ _ hd0, neg_smul, sub_neg_eq_add, sub_add_cancel]
  · intro g v
    show (e (a g v, 0)).1 - ((e (a g v, 0)).2 / δ) • w' = b g ((e (v, 0)).1 - ((e (v, 0)).2 / δ) • w')
    have h1 := h g v 0
    rw [mul_zero] at h1
    rw [h1, map_sub, map_smul, hb, smul_smul]
    dsimp only
    rw [show c g * (e (v, 0)).2 / δ = (e (v, 0)).2 / δ * c g by ring]

theorem cancel_one (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (c : Γ → K) (e : (V × K) ≃ₗ[K] (W × K))
    (h : ∀ g v x, e (a g v, c g * x) = (b g (e (v, x)).1, c g * (e (v, x)).2)) :
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  by_cases hd : (e ((0 : V), (1 : K))).2 = 0
  · rcases hq : e.symm ((0 : W), (1 : K)) with ⟨v₁, d'⟩
    have hq' : e (v₁, d') = ((0 : W), (1 : K)) := by rw [← hq]; simp
    have hv1 : ∀ g, a g v₁ = c g • v₁ := by
      intro g
      have h1 := h g v₁ d'
      rw [hq'] at h1
      simp only [map_zero, mul_one] at h1
      have h2 : e (c g • v₁, c g * d') = ((0 : W), c g) := by
        have h3 : ((c g • v₁, c g * d') : V × K) = c g • (v₁, d') := by simp
        rw [h3, map_smul, hq']; simp
      have h4 := e.injective (h1.trans h2.symm)
      simpa using congrArg Prod.fst h4
    have hd1 : (e (v₁, 1)).2 ≠ 0 := by
      have h5 : ((v₁, 1) : V × K) = (v₁, d') + (1 - d') • ((0 : V), (1 : K)) := by ext <;> simp
      rw [h5, map_add, map_smul, hq']
      simp [hd]
    exact ennreal_volume_ratio_step_cancel a b c e h v₁ hv1 hd1
  · exact ennreal_volume_ratio_step_cancel a b c e h 0 (fun g => by simp) hd

def splitFirst (V : Type) [AddCommGroup V] [Module K V] (t : ℕ) :
    ((V × (Fin t → K)) × K) ≃ₗ[K] (V × (Fin (t + 1) → K)) where
  toFun p := (p.1.1, Fin.cons p.2 p.1.2)
  invFun q := ((q.1, fun j => q.2 j.succ), q.2 0)
  map_add' p q := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  map_smul' x p := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  left_inv p := by simp
  right_inv q := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem cancel_fin (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (t : ℕ) :
    ∀ (c : Fin t → Γ → K) (e : (V × (Fin t → K)) ≃ₗ[K] (W × (Fin t → K))),
    (∀ g v x, e (a g v, fun j => c j g * x j) = (b g (e (v, x)).1, fun j => c j g * (e (v, x)).2 j)) →
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  induction t with
  | zero =>
    intro c e h
    refine ⟨((LinearEquiv.prodUnique : (V × (Fin 0 → K)) ≃ₗ[K] V).symm.trans e).trans
      (LinearEquiv.prodUnique : (W × (Fin 0 → K)) ≃ₗ[K] W), fun g v => ?_⟩
    have hx : ((a g v, fun j => c j g * (default : Fin 0 → K) j) : V × (Fin 0 → K)) = (a g v, default) :=
      Prod.ext rfl (Subsingleton.elim _ _)
    have h1 := h g v default
    rw [hx] at h1
    show (e (a g v, default)).1 = b g (e (v, default)).1
    rw [h1]
  | succ t ih =>
    intro c e h
    let S := splitFirst (K := K) V t
    let T := splitFirst (K := K) W t
    let a' : Γ → (V × (Fin t → K)) →ₗ[K] (V × (Fin t → K)) := fun g =>
      (a g).prodMap (LinearMap.pi fun j => c j.succ g • LinearMap.proj j)
    let b' : Γ → (W × (Fin t → K)) →ₗ[K] (W × (Fin t → K)) := fun g =>
      (b g).prodMap (LinearMap.pi fun j => c j.succ g • LinearMap.proj j)
    refine (cancel_one a' b' (c 0) ((S.trans e).trans T.symm) ?_).elim fun f' hf' => ?_
    · intro g p y
      obtain ⟨v, x⟩ := p
      have hS : ∀ (u : V) (z : Fin t → K) (s : K), S ((u, z), s) = (u, Fin.cons s z) := fun _ _ _ => rfl
      have hT : ∀ q : W × (Fin (t + 1) → K), T.symm q = ((q.1, fun j => q.2 j.succ), q.2 0) := fun _ => rfl
      have ha : a' g (v, x) = (a g v, fun j => c j.succ g * x j) := rfl
      have hcons : (Fin.cons (c 0 g * y) (fun j => c j.succ g * x j) : Fin (t + 1) → K) =
          fun j => c j g * (Fin.cons y x : Fin (t + 1) → K) j := by
        funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp
      simp only [LinearEquiv.trans_apply]
      rw [ha, hS, hS, hcons, h g v (Fin.cons y x : Fin (t + 1) → K), hT, hT]
      rfl
    · exact ih (fun j => c j.succ) f' (fun g v x => hf' g (v, x))

end Cancel

theorem overK_apply {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {k : ℕ}
    (σ : Γ →* GL (Fin k) A) (g : Γ) (u : Fin k → FractionRing A) :
    overK σ g u = ((mat σ g).map (toFr A)).mulVec u := by
  simp [overK, mat, toFr, matRep, mapM]

theorem conj_of_isDecomp {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}
    (σ σ' : Γ →* GL (Fin n) A) (ρ ρ' : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    (hP : ∃ Pm : GL (Fin n) (FractionRing A), ∀ g,
      (Pm : Matrix (Fin n) (Fin n) (FractionRing A)) * (mat σ g).map (toFr A) =
        (mat σ' g).map (toFr A) * (Pm : Matrix (Fin n) (Fin n) (FractionRing A)))
    (h : ∃ e, IsDecomp (t := t) σ ρ χ e) (h' : ∃ e, IsDecomp (t := t) σ' ρ' χ e) :
    ∃ Pm : GL (Fin r) (FractionRing A), ∀ g,
      (Pm : Matrix (Fin r) (Fin r) (FractionRing A)) * (mat ρ g).map (toFr A) =
        (mat ρ' g).map (toFr A) * (Pm : Matrix (Fin r) (Fin r) (FractionRing A)) := by
  obtain ⟨Pm, hPm⟩ := hP
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  let L : (Fin n → FractionRing A) ≃ₗ[FractionRing A] (Fin n → FractionRing A) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' (Pm : Matrix (Fin n) (Fin n) (FractionRing A)))
      (Matrix.toLin' ((Pm⁻¹ : GL (Fin n) (FractionRing A)) : Matrix (Fin n) (Fin n) (FractionRing A)))
      (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
  have hL : ∀ g u, L (overK σ g u) = overK σ' g (L u) := by
    intro g u
    simp only [L, LinearEquiv.coe_ofLinearMap, Matrix.toLin'_apply, overK_apply, Matrix.mulVec_mulVec, hPm g]
  refine (cancel_fin (fun g => overK ρ g) (fun g => overK ρ' g) t
    (fun j g => toFr A ((χ (↑j + 1) g : Aˣ) : A)) ((e.symm.trans L).trans e') ?_).elim fun f hf => ?_
  · intro g v x
    have he1 := he g (e.symm (v, x))
    simp only [LinearEquiv.apply_symm_apply] at he1
    have h2 : e.symm (overK ρ g v, fun j => toFr A ((χ (↑j + 1) g : Aˣ) : A) * x j) = overK σ g (e.symm (v, x)) := by
      rw [← he1, LinearEquiv.symm_apply_apply]
    simp only [LinearEquiv.trans_apply]
    rw [h2, hL, he']
  · refine ⟨⟨LinearMap.toMatrix' (f : (Fin r → FractionRing A) →ₗ[FractionRing A] (Fin r → FractionRing A)),
      LinearMap.toMatrix' (f.symm : (Fin r → FractionRing A) →ₗ[FractionRing A] (Fin r → FractionRing A)), ?_, ?_⟩,
      fun g => ?_⟩
    · rw [← LinearMap.toMatrix'_comp]; simp
    · rw [← LinearMap.toMatrix'_comp]; simp
    · apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix',
        Matrix.toLin'_apply, ← overK_apply, LinearEquiv.coe_coe]
      exact hf g v

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) (r π)) → (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r π g).map (toK N i) = (rO N i r' π g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) → (∃ e, IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → (∃ e, IsDecomp (t := R.t) (r' π) (ρ' π) (N.chi i) e) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) := by
  intro R H what₂ N i r r' ρ ρ' π _ hP h h'
  exact conj_of_isDecomp (r π) (r' π) (ρ π) (ρ' π) (N.chi i) hP h h'

end GlobalTheory.CharCancel
