import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter

noncomputable section

namespace GlobalTheory.RedFun

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open scoped LaurentSeries PowerSeries

theorem card_le_of_span {k R N : Type} [Field k] [CommRing R] [Algebra k R] [AddCommGroup N] [Module k N]
    {ε : R} (hε : IsIdempotentElem ε) (h0 : ε ≠ 0) {s t : ℕ} (u : Fin s → R ⊗[k] N) (b : Fin t → N)
    (hb : LinearIndependent k b) (h : ∀ j, ε ⊗ₜ[k] b j ∈ Submodule.span R (Set.range u)) : t ≤ s := by
  classical
  let I : Ideal R := Ideal.span {1 - ε}
  have hI : I ≠ ⊤ := by
    intro hI
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((Ideal.eq_top_iff_one I).1 hI)
    apply h0
    have h1 : ε * ε = ε := hε
    linear_combination (-ε) * hc - c * h1
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  let Θ : R ⊗[k] N →ₗ[R] (R ⧸ I) ⊗[k] N := AlgebraTensorModule.map (Algebra.linearMap R (R ⧸ I)) LinearMap.id
  have h1 : algebraMap R (R ⧸ I) ε = 1 := by
    rw [eq_comm, ← map_one (algebraMap R (R ⧸ I))]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self _)
  have hli : LinearIndependent (R ⧸ I) fun j => (1 : R ⧸ I) ⊗ₜ[k] b j :=
    Module.Flat.linearIndependent_one_tmul hb
  have h2 := linearIndependent_le_span_aux' _ hli (Set.range fun j => Θ (u j)) (by
    rintro _ ⟨j, rfl⟩
    have h3 := Submodule.mem_map_of_mem (f := Θ) (h j)
    rw [Submodule.map_span, ← Set.range_comp] at h3
    have h4 : Θ (ε ⊗ₜ[k] b j) = (1 : R ⧸ I) ⊗ₜ[k] b j := by
      rw [← h1]; rfl
    rw [h4] at h3
    exact Submodule.span_le_restrictScalars R (R ⧸ I) _ h3)
  have h5 := Fintype.card_range_le fun j => Θ (u j)
  simp only [Fintype.card_fin] at h2 h5
  exact h2.trans h5

section Frames

variable {k G : Type} [Field k] [Group G] {Rk : Type} [CommRing Rk] [Algebra k Rk]

def Phi (φ : Rk →ₐ[k] Rk) (m : ℕ) : Rk ⊗[k] (Fin m → k) →ₗ[k] Rk ⊗[k] (Fin m → k) :=
  φ.toLinearMap.rTensor _

def Act (a : G → (Rk →ₐ[k] Rk)) (A : Ob k G) (g : G) : Rk ⊗[k] (Fin A.m → k) →ₗ[k] Rk ⊗[k] (Fin A.m → k) :=
  TensorProduct.map (a g).toLinearMap (A.ρ g)

@[simp] theorem Phi_tmul (φ : Rk →ₐ[k] Rk) (m : ℕ) (r : Rk) (t : Fin m → k) :
    Phi φ m (r ⊗ₜ[k] t) = φ r ⊗ₜ[k] t := rfl

@[simp] theorem Act_tmul (a : G → (Rk →ₐ[k] Rk)) (A : Ob k G) (g : G) (r : Rk) (t : Fin A.m → k) :
    Act a A g (r ⊗ₜ[k] t) = a g r ⊗ₜ[k] A.ρ g t := rfl

theorem Phi_smul (φ : Rk →ₐ[k] Rk) (m : ℕ) (r : Rk) (y : Rk ⊗[k] (Fin m → k)) :
    Phi φ m (r • y) = φ r • Phi φ m y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem Act_smul (a : G → (Rk →ₐ[k] Rk)) (A : Ob k G) (g : G) (r : Rk) (y : Rk ⊗[k] (Fin A.m → k)) :
    Act a A g (r • y) = a g r • Act a A g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem Act_mul (a : G → (Rk →ₐ[k] Rk)) (ha : ∀ g h x, a (g * h) x = a g (a h x)) (A : Ob k G) (g h : G)
    (y : Rk ⊗[k] (Fin A.m → k)) : Act a A (g * h) y = Act a A g (Act a A h y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [ha]
  | add a b ha hb => simp [ha, hb]

theorem Act_one (a : G → (Rk →ₐ[k] Rk)) (ha : ∀ x, a 1 x = x) (A : Ob k G)
    (y : Rk ⊗[k] (Fin A.m → k)) : Act a A 1 y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [ha]
  | add a b ha hb => simp [ha, hb]

def IsFrame (κ : k⸨X⸩ →+* Rk) (ε : Rk) {m : ℕ} (β : Vc k m →+ Rk ⊗[k] (Fin m → k)) : Prop :=
  Function.Injective β ∧ (∀ (c : k⸨X⸩) x, β (c • x) = κ c • β x) ∧ (∀ x, ε • β x = β x) ∧
    ∀ t, ε ⊗ₜ[k] t ∈ Submodule.span Rk (Set.range β)

structure IsFrames {l n : ℕ} [NeZero n] (R : RingPG k l) (κ : k⸨X⸩ →+* Rk) (φ : Rk →ₐ[k] Rk)
    (a : G → (Rk →ₐ[k] Rk)) (g₀ : G) (ε : ZMod n → Rk) (Obj : Ob k G → Prop)
    (β : ∀ A : Ob k G, ZMod n → (Vc k A.m →+ Rk ⊗[k] (Fin A.m → k))) : Prop where
  κ_k : ∀ c : k, κ (algebraMap k k⸨X⸩ c) = algebraMap k Rk c
  κ_φ : ∀ c, φ (κ c) = κ (R.φ c)
  κ_γ : ∀ c, a g₀ (κ c) = κ (R.γ c)
  comm : ∀ x, φ (a g₀ x) = a g₀ (φ x)
  ε_idem : ∀ i, IsIdempotentElem (ε i)
  ε_orth : ∀ i j, i ≠ j → ε i * ε j = 0
  ε_sum : ∑ i, ε i = 1
  ε_ne : ∀ i, ε i ≠ 0
  ε_φ : ∀ i, φ (ε (i - 1)) = ε i
  ε_γ : ∀ i, a g₀ (ε i) = ε i
  obj_sub : ∀ A B f, IsHom A B f → Function.Injective f → Obj B → Obj A
  obj_quot : ∀ A B f, IsHom A B f → Function.Surjective f → Obj A → Obj B
  obj_sum : ∀ A B C i j, IsHom A C i → IsHom B C j → Function.Surjective (i.coprod j) → Obj A → Obj B → Obj C
  obj_one : Obj (chr 1)
  frame : ∀ A, Obj A → ∀ i, IsFrame κ (ε i) (β A i)
  st_φ : ∀ A, Obj A → ∀ i x, ∃ y, β A i y = Phi φ A.m (β A (i - 1) x)
  st_γ : ∀ A, Obj A → ∀ i x, ∃ y, β A i y = Act a A g₀ (β A i x)
  γ_inj : ∀ A, Function.Injective (Act a A g₀)
  γ_surj : ∀ A, Obj A → ∀ i y, ∃ x, β A i y = Act a A g₀ (β A i x)
  st_map : ∀ A B f, Obj A → Obj B → IsHom A B f → ∀ i x, ∃ y, β B i y = f.baseChange Rk (β A i x)
  unit : ∀ i, ∃ x, β (chr 1) i x = ε i ⊗ₜ[k] (fun _ => 1)
  fix : ∀ A, Obj A → ∀ y, Phi φ A.m y = y → Act a A g₀ y = y → (∀ i, ∃ x, β A i x = ε i • y) →
    ∃ t, y = (1 : Rk) ⊗ₜ[k] t ∧ ∀ g, A.ρ g t = t

end Frames

section Comparison₂

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k]
    {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk)

def redT {M : Type} [AddCommGroup M] [Module O M] {m : ℕ} (q : M →ₗ[O] (Fin m → k)) :
    RW ⊗[O] M →+ Rk ⊗[k] (Fin m → k) :=
  TensorProduct.liftAddHom
    { toFun := fun w =>
        { toFun := fun t => ρ w ⊗ₜ[k] q t
          map_zero' := by simp
          map_add' := fun _ _ => by simp [tmul_add] }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_tmul] }
    (fun c w t => by
      change ρ (c • w) ⊗ₜ[k] q t = ρ w ⊗ₜ[k] q (c • t)
      rw [map_smul, map_smul, ← algebraMap_smul k c (ρ w), ← algebraMap_smul k c (q t), smul_tmul])

@[simp] theorem redT_tmul {M : Type} [AddCommGroup M] [Module O M] {m : ℕ} (q : M →ₗ[O] (Fin m → k)) (w : RW)
    (t : M) : redT ρ q (w ⊗ₜ[O] t) = ρ w ⊗ₜ[k] q t := rfl

theorem redT_smul {M : Type} [AddCommGroup M] [Module O M] {m : ℕ} (q : M →ₗ[O] (Fin m → k)) (w : RW)
    (y : RW ⊗[O] M) : redT ρ q (w • y) = ρ w • redT ρ q y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

def J (T : LocLat G Qp LL O) {m : ℕ} (q : ↥T.L.T →ₗ[O] (Fin m → k)) : W.DD T →+ Rk ⊗[k] (Fin m → k) :=
  (redT ρ q).comp (E.jD T).toAddMonoidHom

def rE : W.EE →+* Rk := (ρ : RW →+* Rk).comp (E.ioE : W.EE →+* RW)

def eps (i : ZMod n) : Rk := rE E ρ (algebraMap (LetA O n) W.EE (letE i))

theorem J_apply (T : LocLat G Qp LL O) {m : ℕ} (q : ↥T.L.T →ₗ[O] (Fin m → k)) (x : W.DD T) :
    J E ρ T q x = redT ρ q (E.jD T x) := rfl

theorem rE_apply (e : W.EE) : rE E ρ e = ρ (E.ioE e) := rfl

theorem rE_O (c : O) : rE E ρ (algebraMap O W.EE c) = algebraMap k Rk (algebraMap O k c) := by
  rw [rE_apply, AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply O k Rk]

theorem J_smul (T : LocLat G Qp LL O) {m : ℕ} (q : ↥T.L.T →ₗ[O] (Fin m → k)) (e : W.EE) (x : W.DD T) :
    J E ρ T q (e • x) = rE E ρ e • J E ρ T q x := by
  rw [J_apply, E.jD_smul, redT_smul]; rfl

theorem J_smulA (T : LocLat G Qp LL O) {m : ℕ} (q : ↥T.L.T →ₗ[O] (Fin m → k)) (c : LetA O n) (x : W.DD T) :
    J E ρ T q (c • x) = rE E ρ (algebraMap (LetA O n) W.EE c) • J E ρ T q x := by
  rw [← algebraMap_smul W.EE c x, J_smul]

theorem J_smulO (T : LocLat G Qp LL O) {m : ℕ} (q : ↥T.L.T →ₗ[O] (Fin m → k)) (c : O) (x : W.DD T) :
    J E ρ T q (c • x) = algebraMap k Rk (algebraMap O k c) • J E ρ T q x := by
  rw [← algebraMap_smul W.EE c x, J_smul, rE_O (k := k)]

theorem J_φ {φ : Rk →ₐ[k] Rk} (hφ : ∀ w, φ (ρ w) = ρ (φR w)) (T : LocLat G Qp LL O) {m : ℕ}
    (q : ↥T.L.T →ₗ[O] (Fin m → k)) (x : W.DD T) : J E ρ T q (W.φD T x) = Phi φ m (J E ρ T q x) := by
  rw [J_apply, J_apply, E.jD_φ]
  induction E.jD T x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap, hφ]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem J_act {a : G → (Rk →ₐ[k] Rk)} (ha : ∀ g w, a g (ρ w) = ρ (gR g w)) (T : LocLat G Qp LL O) (A : Ob k G)
    (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (hq : Onto T A q) (g : G) (x : W.DD T) :
    J E ρ T q (W.γD T (W.resΓ g) x) = Act a A g (J E ρ T q x) := by
  rw [J_apply, J_apply, E.jD_act]
  induction E.jD T x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have : q (T.actT g t) = A.ρ g (q t) := hq.2 g t
    simp [TWact, ha, this]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem J_map {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) {m m' : ℕ} (q : ↥T.L.T →ₗ[O] (Fin m → k))
    (q' : ↥T'.L.T →ₗ[O] (Fin m' → k)) (g : (Fin m → k) →ₗ[k] (Fin m' → k))
    (h : ∀ (x : ↥T.L.T) (x' : ↥T'.L.T), (x' : T'.V) = f.f x → q' x' = g (q x)) (x : W.DD T) :
    J E ρ T' q' (W.map f x) = g.baseChange Rk (J E ρ T q x) := by
  rw [J_apply, J_apply, E.jD_map]
  induction E.jD T x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    rw [TensorProduct.map_tmul, redT_tmul, redT_tmul, LinearMap.baseChange_tmul, h t _ rfl]; rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem J_comp (T : LocLat G Qp LL O) {m m' : ℕ} (q : ↥T.L.T →ₗ[O] (Fin m → k))
    (q' : ↥T.L.T →ₗ[O] (Fin m' → k)) (g : (Fin m → k) →ₗ[k] (Fin m' → k)) (h : ∀ x, q' x = g (q x))
    (x : W.DD T) : J E ρ T q' x = g.baseChange Rk (J E ρ T q x) := by
  rw [← J_map E ρ (latId T) q q' g (fun x x' e => by rw [← h]; exact congrArg q' (Subtype.ext e)), W.map_id]

theorem J_span (T : LocLat G Qp LL O) {m : ℕ} (q : ↥T.L.T →ₗ[O] (Fin m → k)) (t : ↥T.L.T) :
    (1 : Rk) ⊗ₜ[k] q t ∈ Submodule.span Rk (Set.range (J E ρ T q)) := by
  have key : ∀ y ∈ Submodule.span RW (Set.range (E.jD T)),
      redT ρ q y ∈ Submodule.span Rk (Set.range (J E ρ T q)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨x, rfl⟩ := hy; exact Submodule.subset_span ⟨x, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul w y _ hy => rw [redT_smul]; exact Submodule.smul_mem _ _ hy
  have := key ((1 : RW) ⊗ₜ[O] t) (by rw [E.jD_span]; trivial)
  rwa [redT_tmul, map_one] at this

theorem eps_idem (i : ZMod n) : IsIdempotentElem (eps E ρ i) := by
  rw [IsIdempotentElem, eps, ← map_mul, ← map_mul]
  congr 2
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem sum_mem_DΔ (T : LocLat G Qp LL O) (x : W.DD T) : ∑ δ ∈ W.DelF, W.γD T δ x ∈ DΔ W T := by
  have hm : ∀ g, g ∈ W.DelF ↔ IsOfFinOrder g := fun g => by rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]
  intro δ hδ
  rw [map_sum]
  refine Finset.sum_nbij' (fun d => δ * d) (fun d => δ⁻¹ * d) ?_ ?_ ?_ ?_ ?_
  · intro d hd; exact (hm _).2 (((hm _).1 hδ).mul ((hm _).1 hd))
  · intro d hd; exact (hm _).2 (((hm _).1 hδ).inv.mul ((hm _).1 hd))
  · intro d _; simp
  · intro d _; simp
  · intro d _; rw [W.γD_mul]

structure IsRed (lam : O) (κ : k⸨X⸩ →+* Rk) : Prop where
  res_surj : Function.Surjective (algebraMap O k)
  res_ker : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x
  lam_ne : algebraMap O LL lam ≠ 0
  eps_ne : ∀ i, eps E ρ i ≠ 0
  κ_of : ∀ i c, ∃ e, eps E ρ i * κ c = eps E ρ i * rE E ρ e
  of_κ : ∀ i e, ∃ c, eps E ρ i * rE E ρ e = eps E ρ i * κ c
  ker : ∀ i e, eps E ρ i * rE E ρ e = 0 →
    ∃ e', algebraMap (LetA O n) W.EE (letE i) * e = algebraMap O W.EE lam * e'
  κ_A : ∀ i (c : LetA O n), eps E ρ i * rE E ρ (algebraMap (LetA O n) W.EE c) =
    eps E ρ i * κ ((PowerSeries.map (algebraMap O k) (c i) : k⟦X⟧) : k⸨X⸩)

structure IsDel (κ : k⸨X⸩ →+* Rk) (a : G → (Rk →ₐ[k] Rk)) (ι : k⸨X⸩ →+* k⸨X⸩)
    (σ : {δ // δ ∈ W.DelF} → (k⸨X⸩ →+* k⸨X⸩)) : Prop where
  a_ρ : ∀ g w, a g (ρ w) = ρ (gR g w)
  a_eps : ∀ g i, a g (eps E ρ i) = eps E ρ i
  a_κ : ∀ g (δ : {δ // δ ∈ W.DelF}), W.resΓ g = δ.1 → ∀ c, a g (κ c) = κ (σ δ c)
  σ_inj : Function.Injective σ
  σ_fix : ∀ c, (∀ δ, σ δ c = c) ↔ ∃ c₀, ι c₀ = c
  card_ne : ((W.DelF.card : ℕ) : k) ≠ 0

end Comparison₂

end GlobalTheory.RedFun
