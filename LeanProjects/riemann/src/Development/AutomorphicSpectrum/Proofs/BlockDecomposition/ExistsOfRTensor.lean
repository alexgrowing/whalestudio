import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential

namespace GlobalTheory.CompanionTheory.HodgeAlt

section Basic

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem cupHyp_add_swap (a b : Hyp1 F) : cupHyp F a b + cupHyp F b a = 0 := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rw [cupHyp_mk, cupHyp_mk, ← map_add]
  refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ -(a.1.1 T T' φ * b.1.1 T T' φ), 0), ?_⟩
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
  · change _ = (cupTot F a.1 b.1).1 T T' T'' φ ψ + (cupTot F b.1 a.1).1 T T' T'' φ ψ
    simp only [cechDeRhamTotalDifferentialOne_functionPart, cupTot_apply, cechDeRhamTotalCocyclesOne.comp a, cechDeRhamTotalCocyclesOne.comp b, map_neg, map_mul]
    ring
  · change _ = (cupTot F a.1 b.1).2.1 T T' φ + (cupTot F b.1 a.1).2.1 T T' φ
    simp only [dTot1_a, cupTot_a]
    rw [cechDeRhamTotalCocyclesOne.conn a φ, cechDeRhamTotalCocyclesOne.conn b φ]
    simp only [Pi.zero_apply, map_zero, sub_zero, map_neg, Derivation.leibniz, smul_add]
    module
  · change _ = (cupTot F a.1 b.1).2.2 T + (cupTot F b.1 a.1).2.2 T
    simp only [dTot1_η, cupTot_η]
    rw [wedge_swap (a.1.2 T)]
    simp

variable {F}

theorem exists_lift (hs : Function.Surjective (toO F)) (f : Z1 F) :
    ∃ α : A0 F, ((f.1, α) : Tot1 F) ∈ cechDeRhamTotalCocyclesOne F := by
  obtain ⟨c, hc⟩ := hs (H1.mk F f)
  obtain ⟨c, rfl⟩ := Hyp1.mk_surjective F c
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 (show H1.mk F (cechDeRhamTotalCocyclesOne.fn F c) = H1.mk F f from hc)
  have hg' : ∀ (T T' : C) (φ : T ⟶ T'), c.1.1 T T' φ = f.1 T T' φ + (g T' - mp F φ (g T)) :=
    fun T T' φ ↦ by
      have := congrFun (congrFun (congrFun hg T) T') φ
      rw [amitsur_d0_apply] at this
      rw [this]
      change _ = _ + (c.1.1 T T' φ - f.1 T T' φ)
      abel
  refine ⟨fun T ↦ c.1.2 T - D R _ (g T), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, fun T T' φ ↦ ?_, fun T ↦ ?_⟩⟩
  · simp only [map_sub, p1_D]
    rw [cechDeRhamTotalCocyclesOne.conn c φ, hg', map_add, map_sub]
    abel
  · simp [cechDeRhamTotalCocyclesOne.closed c]

theorem exists_of_dTot1 (hs : Function.Surjective (toO F)) (e : Tot1 F) (a : A1 F) (w : W0 F 2)
    (h : dTot1 F e = ((0 : C2 F), a, w)) :
    ∃ β : A0 F, (∀ (T T' : C) (φ : T ⟶ T'), a T T' φ = β T' - p1 F φ (β T)) ∧
      ∀ T, w T = dOne R _ (β T) := by
  have he : e.1 ∈ Z1 F := by
    rw [commAlgFunctorCocyclesOne_eq_ker]
    exact congrArg Prod.fst h
  obtain ⟨α, hα⟩ := exists_lift hs ⟨e.1, he⟩
  obtain ⟨-, h2, h3⟩ := mem_cechDeRhamTotalCocyclesOne_iff.1 hα
  refine ⟨e.2 - α, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · have k : e.2 T' - p1 F φ (e.2 T) - D R _ (e.1 T T' φ) = a T T' φ :=
      congrFun (congrFun (congrFun (congrArg (·.2.1) h) T) T') φ
    have k2 : α T' = p1 F φ (α T) + D R _ (e.1 T T' φ) := h2 φ
    rw [← k, Pi.sub_apply, Pi.sub_apply, map_sub, k2]
    abel
  · have k : dOne R _ (e.2 T) = w T := congrFun (congrArg (·.2.2) h) T
    have k3 : dOne R _ (α T) = 0 := h3 T
    rw [← k, Pi.sub_apply, map_sub, k3, sub_zero]

theorem eta_eq_zero (hc : Closed1 F = ⊤) (hs : Function.Surjective (toO F)) (e : Tot1 F) (w : W0 F 2)
    (h : dTot1 F e = ((0 : C2 F), (0 : A1 F), w)) : w = 0 := by
  obtain ⟨β, h1, h2⟩ := exists_of_dTot1 hs e 0 w h
  have hβ : β ∈ Glob1 F := fun T T' φ ↦ by
    have := h1 T T' φ
    exact sub_eq_zero.1 this.symm
  have hcl : (⟨β, hβ⟩ : Glob1 F) ∈ Closed1 F := hc ▸ Submodule.mem_top
  funext T
  rw [h2 T]
  exact hcl T

end Basic

section Lin

variable {R V V' W W' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [AddCommGroup W]
  [AddCommGroup W'] [Module R V] [Module R V'] [Module R W] [Module R W']

theorem exists_proj (p q : V →ₗ[R] V') (h : Function.Bijective fun x : V × V ↦ p x.1 + q x.2) :
    ∃ P Q : V' →ₗ[R] V, (∀ v, P (p v) = v) ∧ (∀ v, P (q v) = 0) ∧ (∀ v, Q (p v) = 0) ∧
      ∀ v, Q (q v) = v := by
  let e : (V × V) ≃ₗ[R] V' := LinearEquiv.ofBijective (p.coprod q) h
  have he : ∀ x, e x = p x.1 + q x.2 := fun x ↦ rfl
  have hp : ∀ v, e.symm (p v) = (v, 0) := fun v ↦ e.symm_apply_eq.2 (by rw [he]; simp)
  have hq : ∀ v, e.symm (q v) = (0, v) := fun v ↦ e.symm_apply_eq.2 (by rw [he]; simp)
  refine ⟨LinearMap.fst R V V ∘ₗ e.symm.toLinearMap, LinearMap.snd R V V ∘ₗ e.symm.toLinearMap,
    fun v ↦ ?_, fun v ↦ ?_, fun v ↦ ?_, fun v ↦ ?_⟩ <;> simp [hp, hq]

theorem tensor_prim (p q m : V →ₗ[R] V') (p' q' m' : W →ₗ[R] W') (P : V' →ₗ[R] V) (Q : W' →ₗ[R] W)
    (hPp : ∀ v, P (p v) = v) (hPq : ∀ v, P (q v) = 0) (hQp : ∀ w, Q (p' w) = 0)
    (hQq : ∀ w, Q (q' w) = w) (hm : ∀ v, m v = p v + q v) (hm' : ∀ w, m' w = p' w + q' w)
    (t : V ⊗[R] W)
    (ht : TensorProduct.map m m' t = TensorProduct.map p p' t + TensorProduct.map q q' t) : t = 0 := by
  have h1 : ∀ t : V ⊗[R] W, TensorProduct.map P Q (TensorProduct.map m m' t) = t := fun t ↦ by
    induction t with
    | zero => simp
    | tmul v w => simp [hm, hm', hPp, hPq, hQp, hQq]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h2 : ∀ t : V ⊗[R] W, TensorProduct.map P Q (TensorProduct.map p p' t) = 0 := fun t ↦ by
    induction t with
    | zero => simp
    | tmul v w => simp [hQp]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  have h3 : ∀ t : V ⊗[R] W, TensorProduct.map P Q (TensorProduct.map q q' t) = 0 := fun t ↦ by
    induction t with
    | zero => simp
    | tmul v w => simp [hPq]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  have := congrArg (TensorProduct.map P Q) ht
  rwa [h1, map_add, h2, h3, add_zero] at this

def alt (l l' : V →ₗ[R] R) : ⋀[R]^2 V →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv
    (Matrix.detRowAlternating.compLinearMap (LinearMap.pi ![l, l']))

theorem alt_ιMulti (l l' : V →ₗ[R] R) (a b : V) :
    alt l l' (exteriorPower.ιMulti R 2 ![a, b]) = l a * l' b - l' a * l b :=
  (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans (Matrix.det_fin_two _)

theorem ext2 {N : Type} [AddCommGroup N] [Module R N] {f g : ⋀[R]^2 V →ₗ[R] N}
    (h : ∀ a b, f (exteriorPower.ιMulti R 2 ![a, b]) = g (exteriorPower.ιMulti R 2 ![a, b])) :
    f = g := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  have : v = ![v 0, v 1] := by
    funext i; fin_cases i <;> rfl
  rw [this]
  exact h _ _

theorem map2 (f : V →ₗ[R] V') (a b : V) :
    exteriorPower.map 2 f (exteriorPower.ιMulti R 2 ![a, b]) =
      exteriorPower.ιMulti R 2 ![f a, f b] := by
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i; fin_cases i <;> rfl

end Lin

section Wedge

variable {R V V' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [Module R V] [Module R V']

theorem sum_lt {M : Type} [AddCommGroup M] [Module R M] {n : ℕ} (u v : Fin n → R)
    (c : Fin n → Fin n → M) (hd : ∀ i, c i i = 0) (ha : ∀ i j, c j i = -c i j) :
    ∑ i, ∑ j, (u i * v j) • c i j =
      ∑ i, ∑ j, if i < j then (u i * v j - u j * v i) • c i j else 0 := by
  have e1 : ∀ i j, (u i * v j) • c i j = (if i < j then (u i * v j) • c i j else 0) +
      (if j < i then (u i * v j) • c i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.not_gt]
    · subst h; simp [hd]
    · simp [h, h.not_gt]
  have e2 : ∀ i j, (if i < j then (u i * v j - u j * v i) • c i j else 0) =
      (if i < j then (u i * v j) • c i j else 0) + (if i < j then (u j * v i) • c j i else 0) := by
    intro i j
    split_ifs
    · rw [ha i j, sub_smul, smul_neg, sub_eq_add_neg]
    · simp
  calc ∑ i, ∑ j, (u i * v j) • c i j
      = ∑ i, ∑ j, ((if i < j then (u i * v j) • c i j else 0) +
          (if j < i then (u i * v j) • c i j else 0)) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ e1 i j
    _ = ∑ i, ∑ j, (if i < j then (u i * v j) • c i j else 0) +
          ∑ i, ∑ j, (if j < i then (u i * v j) • c i j else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, (if i < j then (u i * v j) • c i j else 0) +
          ∑ i, ∑ j, (if i < j then (u j * v i) • c j i else 0) :=
        congrArg (_ + ·) Finset.sum_comm
    _ = _ := by simp only [e2, Finset.sum_add_distrib]

def wd : V →ₗ[R] V →ₗ[R] ⋀[R]^2 V :=
  LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, add_mul]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, mul_add]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))

theorem wd_apply (a b : V) : wd (R := R) a b = exteriorPower.ιMulti R 2 ![a, b] := rfl

theorem wd_self (a : V) : wd (R := R) a a = 0 :=
  Subtype.ext (by simp [wd_apply, ExteriorAlgebra.ιMulti_apply])

theorem wd_swap (a b : V) : wd (R := R) b a = -wd a b :=
  Subtype.ext (by
    simpa [wd_apply, ExteriorAlgebra.ιMulti_apply] using
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := R) b a))

theorem eq_zero_of_alt [Module.Finite R V] [Module.Projective R V] (τ : ⋀[R]^2 V)
    (h : ∀ l l' : V →ₗ[R] R, alt l l' τ = 0) : τ = 0 := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R V
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let x : Fin n → V := fun i ↦ π fun j ↦ if i = j then 1 else 0
  let l : Fin n → V →ₗ[R] R := fun i ↦ LinearMap.proj i ∘ₗ s
  have hx : ∀ a, a = ∑ i, l i a • x i := fun a ↦ by
    have := LinearMap.pi_apply_eq_sum_univ π (s a)
    rw [show π (s a) = a from LinearMap.congr_fun hs a] at this
    exact this
  have hw : ∀ a b, wd (R := R) a b = ∑ i, ∑ j, (l i a * l j b) • wd (R := R) (x i) (x j) := fun a b ↦ by
    refine (congrArg₂ (fun y y' ↦ wd (R := R) y y') (hx a) (hx b)).trans ?_
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [mul_comm]
  have key : (LinearMap.id : ⋀[R]^2 V →ₗ[R] ⋀[R]^2 V) = ∑ i, ∑ j, if i < j then
      (alt (l i) (l j)).smulRight (wd (R := R) (x i) (x j)) else 0 := ext2 fun a b ↦ by
    refine ((hw a b).trans (sum_lt (fun i ↦ l i a) (fun j ↦ l j b) (fun i j ↦ wd (R := R) (x i) (x j))
      (fun i ↦ wd_self _) (fun i j ↦ wd_swap _ _))).trans ?_
    simp only [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [LinearMap.smulRight_apply, alt_ιMulti]
    · rfl
  calc τ = (∑ i, ∑ j, if i < j then
        (alt (l i) (l j)).smulRight (wd (R := R) (x i) (x j)) else 0) τ := by rw [← key]; rfl
    _ = 0 := by
      simp only [LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
      split_ifs <;> simp [h]

theorem wedge_prim [Module.Finite R V] [Module.Projective R V] (p q m : V →ₗ[R] V')
    (P Q : V' →ₗ[R] V) (hPp : ∀ v, P (p v) = v) (hPq : ∀ v, P (q v) = 0) (hQp : ∀ v, Q (p v) = 0)
    (hQq : ∀ v, Q (q v) = v) (hm : ∀ v, m v = p v + q v) (τ : ⋀[R]^2 V)
    (h : exteriorPower.map 2 m τ = exteriorPower.map 2 p τ + exteriorPower.map 2 q τ) : τ = 0 := by
  refine eq_zero_of_alt τ fun l l' ↦ ?_
  have h1 : alt (l ∘ₗ P) (l' ∘ₗ Q) ∘ₗ exteriorPower.map 2 m = alt l l' := ext2 fun a b ↦ by
    simp only [LinearMap.comp_apply, map2, alt_ιMulti, hm, map_add, hPp, hPq, hQp, hQq, add_zero,
      zero_add, map_zero]
  have h2 : alt (l ∘ₗ P) (l' ∘ₗ Q) ∘ₗ exteriorPower.map 2 p = 0 := ext2 fun a b ↦ by
    simp only [LinearMap.comp_apply, map2, alt_ιMulti, hQp, LinearMap.zero_apply, map_zero]
    ring
  have h3 : alt (l ∘ₗ P) (l' ∘ₗ Q) ∘ₗ exteriorPower.map 2 q = 0 := ext2 fun a b ↦ by
    simp only [LinearMap.comp_apply, map2, alt_ιMulti, hPq, LinearMap.zero_apply, map_zero]
    ring
  have e := congrArg (alt (l ∘ₗ P) (l' ∘ₗ Q)) h
  rw [map_add, show alt (l ∘ₗ P) (l' ∘ₗ Q) (exteriorPower.map 2 m τ) = alt l l' τ from
      LinearMap.congr_fun h1 τ, show alt (l ∘ₗ P) (l' ∘ₗ Q) (exteriorPower.map 2 p τ) = 0 from
      LinearMap.congr_fun h2 τ, show alt (l ∘ₗ P) (l' ∘ₗ Q) (exteriorPower.map 2 q τ) = 0 from
      LinearMap.congr_fun h3 τ, add_zero] at e
  exact e

end Wedge

section Main

variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem mu_pull (m : CoefMap (RingHom.id R) F G) (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (muG : Z1 G ⊗[R] Glob1 G →ₗ[R] A1 G)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG : ∀ f ω T T' φ, muG (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (t : Z1 F ⊗[R] Glob1 F) {T T' : D} (φ : T ⟶ T') :
    muG (TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t) T T' φ =
      q1 m T' (muF t _ _ (m.G.map φ)) := by
  induction t with
  | zero => simp
  | tmul f ω =>
    rw [TensorProduct.map_tmul, hG, hF, prodFirstProjection_smul]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem rTensor_pull (m : CoefMap (RingHom.id R) F G) (t : Z1 F ⊗[R] Glob1 F) :
    (H1.mk G).rTensor (Glob1 G) (TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t) =
      TensorProduct.map m.pull1 (pullGlob1 m) ((H1.mk F).rTensor (Glob1 F) t) := by
  induction t with
  | zero => simp
  | tmul f ω => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_of_rTensor (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T') (t : Z1 F ⊗[R] Glob1 F)
    (ht : (H1.mk F).rTensor (Glob1 F) t = 0) :
    ∃ β : A0 F, ∀ (T T' : C) (φ : T ⟶ T'), muF t T T' φ = β T' - p1 F φ (β T) := by
  have hex : Function.Exact ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)) (H1.mk F) :=
    LinearMap.exact_map_mkQ_range _
  obtain ⟨u, rfl⟩ := (rTensor_exact (Glob1 F) hex (H1.mk_surjective F) t).1 ht
  clear ht
  induction u with
  | zero => exact ⟨0, by simp⟩
  | tmul g ω =>
    refine ⟨fun T ↦ g T • ω.1 T, fun T T' φ ↦ ?_⟩
    rw [LinearMap.rTensor_tmul, hF]
    change (g T' - mp F φ (g T)) • ω.1 T' = _
    rw [oneFormsMapOfFunctorMorphism_smul, ← ω.2 φ, sub_smul]
  | add x y hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨b', hb'⟩ := hy
    refine ⟨b + b', fun T T' φ ↦ ?_⟩
    simp only [map_add, Pi.add_apply, hb, hb']
    abel

theorem prim_cup (m p q : CoefMap (RingHom.id R) F G)
    (hm : ∀ c, pullHyp1 m c = pullHyp1 p c + pullHyp1 q c) (c : Hyp1 F) :
    pullHyp2 m (cupHyp F c c) = pullHyp2 p (cupHyp F c c) + pullHyp2 q (cupHyp F c c) := by
  have := cupHyp_add_swap G (pullHyp1 p c) (pullHyp1 q c)
  simp only [pullHyp2_cup, hm, map_add, LinearMap.add_apply]
  linear_combination (norm := abel1) this

theorem exists_rep (hcup : ∀ c, cup F c c = 0) (c : Hyp1 F) :
    ∃ z : cechDeRhamTotalCocyclesTwo F, z.1.1 = 0 ∧ Hyp2.mk F z = cupHyp F c c := by
  obtain ⟨c, rfl⟩ := Hyp1.mk_surjective F c
  have h := hcup (toO F (Hyp1.mk F c))
  rw [toO_mk, cup_mk] at h
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 h
  refine ⟨cupZZ F c c - ⟨dTot1 F (f, 0), dTot1_mem F _⟩, ?_, ?_⟩
  · funext T T' T'' φ ψ
    have := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') φ) ψ
    change (cupTot F c.1 c.1).1 T T' T'' φ ψ - d1 F f T T' T'' φ ψ = 0
    rw [this]
    exact sub_self _
  · have : Hyp2.mk F ⟨dTot1 F (f, 0), dTot1_mem F _⟩ = 0 := Hyp2.mk_eq_zero.2 ⟨_, rfl⟩
    rw [map_sub, this, sub_zero, cupHyp_mk]

theorem exists_of_prim (m p q : CoefMap (RingHom.id R) F G) (z : cechDeRhamTotalCocyclesTwo F) (hz : z.1.1 = 0)
    (h : pullHyp2 m (Hyp2.mk F z) = pullHyp2 p (Hyp2.mk F z) + pullHyp2 q (Hyp2.mk F z)) :
    ∃ e : Tot1 G, dTot1 G e = ((0 : C2 G),
      (pullTot2 m z.1 - pullTot2 p z.1 - pullTot2 q z.1).2.1,
      (pullTot2 m z.1 - pullTot2 p z.1 - pullTot2 q z.1).2.2) := by
  have h0 : Hyp2.mk G (pullZZ2 m z - pullZZ2 p z - pullZZ2 q z) = 0 := by
    rw [map_sub, map_sub, ← pullHyp2_mk, ← pullHyp2_mk, ← pullHyp2_mk, h]
    abel
  obtain ⟨e, he⟩ := Hyp2.mk_eq_zero.1 h0
  refine ⟨e, he.trans (Prod.ext ?_ rfl)⟩
  funext T T' T'' φ ψ
  change (pullTot2 m z.1).1 T T' T'' φ ψ - (pullTot2 p z.1).1 T T' T'' φ ψ -
    (pullTot2 q z.1).1 T T' T'' φ ψ = 0
  simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, hz, Pi.zero_apply, map_zero, sub_zero]

end Main

section Final

variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem closed_of_sum (p q : CoefMap (RingHom.id R) F G)
    (hb : Function.Surjective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hc : Closed1 F = ⊤) : Closed1 G = ⊤ := by
  refine eq_top_iff.2 fun ω _ ↦ ?_
  obtain ⟨⟨a, b⟩, rfl⟩ := hb ω
  have ha : a ∈ Closed1 F := hc ▸ Submodule.mem_top
  have hb' : b ∈ Closed1 F := hc ▸ Submodule.mem_top
  exact add_mem (pullClosed1 p ⟨a, ha⟩).2 (pullClosed1 q ⟨b, hb'⟩).2

theorem surj_of_sum (p q : CoefMap (RingHom.id R) F G)
    (hb : Function.Surjective fun x : H1 F × H1 F ↦ p.pull1 x.1 + q.pull1 x.2)
    (hs : Function.Surjective (toO F)) : Function.Surjective (toO G) := by
  intro c
  obtain ⟨⟨a, b⟩, rfl⟩ := hb c
  obtain ⟨a, rfl⟩ := hs a
  obtain ⟨b, rfl⟩ := hs b
  exact ⟨pullHyp1 p a + pullHyp1 q b, by rw [map_add, toO_pullHyp1, toO_pullHyp1]⟩

theorem one_cob (m p q : CoefMap (RingHom.id R) F G) (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (muG : Z1 G ⊗[R] Glob1 G →ₗ[R] A1 G)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG : ∀ f ω T T' φ, muG (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hsur : ∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, muF t = a)
    (hker : ∀ (t : Z1 G ⊗[R] Glob1 G) (β : A0 G),
      (∀ T T' φ, muG t T T' φ = β T' - p1 G φ (β T)) → (H1.mk G).rTensor (Glob1 G) t = 0)
    (hsG : Function.Surjective (toO G))
    (hb1 : Function.Bijective fun x : H1 F × H1 F ↦ p.pull1 x.1 + q.pull1 x.2)
    (hb2 : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c)
    (hm2 : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω) (z : cechDeRhamTotalCocyclesTwo F) (hz : z.1.1 = 0)
    (h : pullHyp2 m (Hyp2.mk F z) = pullHyp2 p (Hyp2.mk F z) + pullHyp2 q (Hyp2.mk F z)) :
    ∃ β : A0 F, ∀ (T T' : C) (φ : T ⟶ T'), z.1.2.1 T T' φ = β T' - p1 F φ (β T) := by
  obtain ⟨t, ht⟩ := hsur z.1.2.1 fun T T' T'' φ ψ ↦ by
    have := cechDeRhamTotalCocyclesTwo.one z φ ψ
    rw [hz] at this
    simpa using this
  obtain ⟨e, he⟩ := exists_of_prim m p q z hz h
  obtain ⟨β, hβ, -⟩ := exists_of_dTot1 hsG e _ _ he
  let s := TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t - TensorProduct.map p.pullbackOneCocycle (pullGlob1 p) t -
    TensorProduct.map q.pullbackOneCocycle (pullGlob1 q) t
  have hs : (H1.mk G).rTensor (Glob1 G) s = 0 := hker s β fun T T' φ ↦ by
    rw [← hβ T T' φ]
    simp only [s, map_sub, Pi.sub_apply]
    rw [mu_pull m muF muG hF hG, mu_pull p muF muG hF hG, mu_pull q muF muG hF hG, ht]
    rfl
  obtain ⟨P, -, hPp, hPq, -, -⟩ := exists_proj p.pull1 q.pull1 hb1
  obtain ⟨-, Q, -, -, hQp, hQq⟩ := exists_proj (pullGlob1 p) (pullGlob1 q) hb2
  have hT := tensor_prim p.pull1 q.pull1 m.pull1 (pullGlob1 p) (pullGlob1 q) (pullGlob1 m) P Q
    hPp hPq hQp hQq hm1 hm2 ((H1.mk F).rTensor (Glob1 F) t) (by
      simp only [s, map_sub, rTensor_pull] at hs
      rwa [sub_sub, sub_eq_zero] at hs)
  obtain ⟨β', hβ'⟩ := exists_of_rTensor muF hF t hT
  exact ⟨β', fun T T' φ ↦ by rw [← ht]; exact hβ' T T' φ⟩

theorem nu_pull (m : CoefMap (RingHom.id R) F G) (nuF : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (nuG : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hF : ∀ a b T, nuF (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hG : ∀ a b T, nuG (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (τ : ⋀[R]^2 (Glob1 F)) (T : D) :
    nuG (exteriorPower.map 2 (pullGlob1 m) τ) T = qOm m 2 T (nuF τ (m.G.obj T)) := by
  have e : (LinearMap.proj (φ := fun T ↦ Om R (G.obj T) 2) T ∘ₗ nuG ∘ₗ
      exteriorPower.map 2 (pullGlob1 m)) =
      ((qOm m 2 T : _ →ₗ[R] _) ∘ₗ LinearMap.proj (φ := fun T ↦ Om R (F.obj T) 2) (m.G.obj T) ∘ₗ nuF) :=
    ext2 fun a b ↦ by
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, map2, hG, hF]
      exact (qOm_wedge m (a.1 _) (b.1 _)).symm
  exact LinearMap.congr_fun e τ

theorem two_zero (m p q : CoefMap (RingHom.id R) F G) [Module.Finite R (Glob1 F)]
    [Module.Projective R (Glob1 F)] (nuF : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (nuG : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hF : ∀ a b T, nuF (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hG : ∀ a b T, nuG (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hinj : Function.Injective nuG)
    (hsur : ∀ w : W0 F 2, (∀ (T T' : C) (φ : T ⟶ T'), w T' = pOm F 2 φ (w T)) → ∃ t, nuF t = w)
    (hcG : Closed1 G = ⊤) (hsG : Function.Surjective (toO G))
    (hb2 : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm2 : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω) (z : cechDeRhamTotalCocyclesTwo F) (h1 : z.1.1 = 0)
    (h2 : z.1.2.1 = 0)
    (h : pullHyp2 m (Hyp2.mk F z) = pullHyp2 p (Hyp2.mk F z) + pullHyp2 q (Hyp2.mk F z)) :
    z.1.2.2 = 0 := by
  obtain ⟨τ, hτ⟩ := hsur z.1.2.2 fun T T' φ ↦ by
    have := cechDeRhamTotalCocyclesTwo.two z φ
    rw [h2] at this
    simpa using this
  obtain ⟨e, he⟩ := exists_of_prim m p q z h1 h
  have h0 : (pullTot2 m z.1 - pullTot2 p z.1 - pullTot2 q z.1).2.1 = 0 := by
    funext T T' φ
    change (pullTot2 m z.1).2.1 T T' φ - (pullTot2 p z.1).2.1 T T' φ -
      (pullTot2 q z.1).2.1 T T' φ = 0
    simp only [pullTot2_a, h2, Pi.zero_apply, map_zero, sub_zero]
  rw [h0] at he
  have hw := eta_eq_zero hcG hsG e _ he
  have hν : nuG (exteriorPower.map 2 (pullGlob1 m) τ - exteriorPower.map 2 (pullGlob1 p) τ -
      exteriorPower.map 2 (pullGlob1 q) τ) = 0 := by
    funext T
    have := congrFun hw T
    rw [map_sub, map_sub, Pi.sub_apply, Pi.sub_apply, nu_pull m nuF nuG hF hG,
      nu_pull p nuF nuG hF hG, nu_pull q nuF nuG hF hG, hτ]
    exact this
  have hz := hinj (hν.trans (map_zero nuG).symm)
  obtain ⟨P, Q, hPp, hPq, hQp, hQq⟩ := exists_proj (pullGlob1 p) (pullGlob1 q) hb2
  have ht : τ = 0 := wedge_prim (pullGlob1 p) (pullGlob1 q) (pullGlob1 m) P Q hPp hPq hQp hQq hm2 τ
    (by rwa [sub_sub, sub_eq_zero] at hz)
  rw [← hτ, ht, map_zero]

end Final

theorem altSt : OneFormCohSt → TwoFormCohSt → AltSt := by
  intro hOne hTwo R _ C _ F hFr hBi hCl hSurj hcup c
  obtain ⟨D, _, G, m, p, q, hSt, hPar, hb1, hb2, hm1, hm2, hm3⟩ := hBi
  let eG : (Glob1 F × Glob1 F) ≃ₗ[R] Glob1 G :=
    LinearEquiv.ofBijective ((pullGlob1 p).coprod (pullGlob1 q)) hb2
  haveI := hFr.2.2.1
  haveI := hFr.2.2.2
  have hFrG : Framed G := ⟨hSt, hPar, Module.Finite.equiv eG, Module.Projective.of_equiv eG⟩
  have hcG := closed_of_sum p q hb2.2 hCl
  have hsG := surj_of_sum p q hb1.2 hSurj
  obtain ⟨muF, hF, hsur, -⟩ := hOne R C F hFr
  obtain ⟨muG, hG, -, hker⟩ := hOne R D G hFrG
  obtain ⟨nuF, hνF, -, hνsur⟩ := hTwo R C F hFr
  obtain ⟨nuG, hνG, hνinj, -⟩ := hTwo R D G hFrG
  obtain ⟨z, hz, hzc⟩ := exists_rep hcup c
  have hprim := prim_cup m p q hm3 c
  rw [← hzc] at hprim ⊢
  obtain ⟨β, hβ⟩ := one_cob m p q muF muG hF hG hsur hker hsG hb1 hb2 hm1 hm2 z hz hprim
  let y : cechDeRhamTotalCocyclesTwo F := ⟨dTot1 F (0, β), dTot1_mem F _⟩
  have hy : Hyp2.mk F y = 0 := Hyp2.mk_eq_zero.2 ⟨_, rfl⟩
  have hzy : Hyp2.mk F (z - y) = Hyp2.mk F z := by rw [map_sub, hy, sub_zero]
  have h1 : (z - y).1.1 = 0 := by
    funext T T' T'' φ ψ
    change z.1.1 T T' T'' φ ψ - d1 F 0 T T' T'' φ ψ = 0
    rw [hz, map_zero]
    exact sub_self _
  have h2 : (z - y).1.2.1 = 0 := by
    funext T T' φ
    change z.1.2.1 T T' φ - (β T' - p1 F φ (β T) - KaehlerDifferential.D R _ ((0 : C1 F) T T' φ)) = 0
    rw [hβ]
    simp
  have h3 := two_zero m p q nuF nuG hνF hνG hνinj hνsur hcG hsG hb2 hm2 (z - y) h1 h2
    (by rw [hzy]; exact hprim)
  have h4 : z - y = 0 := Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))
  rw [← hzy, h4, map_zero]

end GlobalTheory.CompanionTheory.HodgeAlt
