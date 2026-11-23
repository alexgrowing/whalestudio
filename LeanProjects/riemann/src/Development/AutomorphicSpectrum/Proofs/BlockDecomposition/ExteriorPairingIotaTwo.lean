import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Hodge.LiftO

section Lin

variable {R V W V' W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']

theorem exists_retract (P Q : V →ₗ[R] W) (hb : Function.Bijective fun x : V × V ↦ P x.1 + Q x.2) :
    ∃ r s : W →ₗ[R] V, (∀ x, r (P x) = x) ∧ (∀ x, r (Q x) = 0) ∧ (∀ x, s (P x) = 0) ∧ ∀ x, s (Q x) = x := by
  let e : (V × V) ≃ₗ[R] W := LinearEquiv.ofBijective (P.coprod Q) hb
  have hP : ∀ x, e.symm (P x) = (x, 0) := fun x ↦ e.symm_apply_eq.2 (by
    change P x = P x + Q 0; simp)
  have hQ : ∀ x, e.symm (Q x) = (0, x) := fun x ↦ e.symm_apply_eq.2 (by
    change Q x = P 0 + Q x; simp)
  refine ⟨LinearMap.fst R V V ∘ₗ e.symm.toLinearMap, LinearMap.snd R V V ∘ₗ e.symm.toLinearMap, ?_, ?_, ?_, ?_⟩ <;>
    intro x <;> simp [hP, hQ]

theorem eq_zero_of_tprim (P₁ Q₁ : V →ₗ[R] W) (P₂ Q₂ : V' →ₗ[R] W')
    (h₁ : Function.Bijective fun x : V × V ↦ P₁ x.1 + Q₁ x.2)
    (h₂ : Function.Bijective fun x : V' × V' ↦ P₂ x.1 + Q₂ x.2) (z : V ⊗[R] V')
    (h : TensorProduct.map (P₁ + Q₁) (P₂ + Q₂) z = TensorProduct.map P₁ P₂ z + TensorProduct.map Q₁ Q₂ z) :
    z = 0 := by
  obtain ⟨r, -, a1, a2, -, -⟩ := exists_retract P₁ Q₁ h₁
  obtain ⟨-, s, -, -, b1, b2⟩ := exists_retract P₂ Q₂ h₂
  have e1 : r ∘ₗ (P₁ + Q₁) = LinearMap.id := LinearMap.ext fun x ↦ by simp [a1, a2]
  have e2 : s ∘ₗ (P₂ + Q₂) = LinearMap.id := LinearMap.ext fun x ↦ by simp [b1, b2]
  have e3 : s ∘ₗ P₂ = 0 := LinearMap.ext fun x ↦ by simp [b1]
  have e4 : r ∘ₗ Q₁ = 0 := LinearMap.ext fun x ↦ by simp [a2]
  have := congrArg (TensorProduct.map r s) h
  rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp, e1, e2, e3, e4,
    TensorProduct.map_id, TensorProduct.map_zero_right, TensorProduct.map_zero_left] at this
  simpa using this

abbrev i2 (a b : V) : ⋀[R]^2 V := exteriorPower.ιMulti R 2 ![a, b]

theorem iota_multi_two_eta (v : Fin 2 → V) : exteriorPower.ιMulti R 2 v = i2 (R := R) (v 0) (v 1) :=
  congrArg _ (by ext i; fin_cases i <;> rfl)

theorem ext2 {N : Type} [AddCommGroup N] [Module R N] {f g : ⋀[R]^2 V →ₗ[R] N}
    (h : ∀ a b, f (i2 a b) = g (i2 a b)) : f = g :=
  exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ by
    simpa [iota_multi_two_eta] using h (v 0) (v 1))

theorem exterior_map_iota_two (f : V →ₗ[R] W) (a b : V) : exteriorPower.map 2 f (i2 (R := R) a b) = i2 (f a) (f b) := by
  rw [exteriorPower.map_apply_ιMulti, iota_multi_two_eta]; rfl

theorem up0 (a b c : V) : Function.update ![a, b] 0 c = ![c, b] := by
  ext i; fin_cases i <;> rfl

theorem up1 (a b c : V) : Function.update ![a, b] 1 c = ![a, c] := by
  ext i; fin_cases i <;> rfl

def b2 : V →ₗ[R] V →ₗ[R] ⋀[R]^2 V :=
  LinearMap.mk₂ R i2
    (fun a a' b ↦ by
      have := (exteriorPower.ιMulti R 2 (M := V)).map_update_add ![a, b] 0 a a'
      rwa [up0, up0, up0] at this)
    (fun c a b ↦ by
      have := (exteriorPower.ιMulti R 2 (M := V)).map_update_smul ![a, b] 0 c a
      rwa [up0, up0] at this)
    (fun a b b' ↦ by
      have := (exteriorPower.ιMulti R 2 (M := V)).map_update_add ![a, b] 1 b b'
      rwa [up1, up1, up1] at this)
    (fun c a b ↦ by
      have := (exteriorPower.ιMulti R 2 (M := V)).map_update_smul ![a, b] 1 c b
      rwa [up1, up1] at this)

theorem wedge_basis_apply (a b : V) : b2 (R := R) a b = i2 a b := rfl

theorem wedge_basis_self_zero (a : V) : b2 (R := R) a a = 0 :=
  (exteriorPower.ιMulti R 2 (M := V)).map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) rfl (by decide)

theorem wedge_basis_swap_neg (a b : V) : b2 (R := R) b a = -b2 (R := R) a b := by
  have := wedge_basis_self_zero (R := R) (a + b)
  simp only [map_add, LinearMap.add_apply, wedge_basis_self_zero, zero_add, add_zero] at this
  exact eq_neg_of_add_eq_zero_left this

def pair2 (l u : V →ₗ[R] R) : ⋀[R]^2 V →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap (LinearMap.pi ![l, u]))

theorem exterior_pairing_iota_two (l u : V →ₗ[R] R) (a b : V) : pair2 l u (i2 a b) = l a * u b - u a * l b :=
  (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans (Matrix.det_fin_two _)

theorem eq_zero_of_pair2 [Module.Finite R V] [Module.Projective R V] (t : ⋀[R]^2 V)
    (h : ∀ l u : V →ₗ[R] R, pair2 l u t = 0) : t = 0 := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R V
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let c : Fin n → V →ₗ[R] R := fun i ↦ LinearMap.proj i ∘ₗ s
  let e : Fin n → V := fun i ↦ f (Pi.single i 1)
  have he : ∀ x, ∑ i, c i x • e i = x := fun x ↦ by
    have h1 : f (s x) = x := LinearMap.congr_fun hs x
    conv_rhs => rw [← h1, ← Finset.univ_sum_single (s x), map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← map_smul]
    congr 1
    ext j
    by_cases hij : j = i
    · subst hij; simp [c]
    · simp [c, Pi.single_eq_of_ne hij]
  let Ψ : ⋀[R]^2 V →ₗ[R] ⋀[R]^2 V :=
    ∑ i, ∑ j, if i < j then (LinearMap.toSpanSingleton R _ (b2 (e i) (e j))) ∘ₗ pair2 (c i) (c j) else 0
  have hΨ : Ψ = LinearMap.id := ext2 fun a b ↦ by
    let g : Fin n → Fin n → ⋀[R]^2 V := fun i j ↦ (c i a * c j b) • b2 (e i) (e j)
    have hg0 : ∀ i, g i i = 0 := fun i ↦ by simp [g, wedge_basis_self_zero]
    have h1 : i2 a b = ∑ i, ∑ j, g i j := by
      conv_lhs => rw [← wedge_basis_apply, ← he a, ← he b]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum, g, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_comm]
    have h2 : ∑ i, ∑ j, (if i < j then g j i else 0) = ∑ i, ∑ j, (if j < i then g i j else 0) :=
      Finset.sum_comm
    have h3 : Ψ (i2 a b) = ∑ i, ∑ j, ((if i < j then g i j else 0) + if i < j then g j i else 0) := by
      simp only [Ψ, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      split_ifs with hij
      · rw [LinearMap.comp_apply, exterior_pairing_iota_two, LinearMap.toSpanSingleton_apply]
        simp only [g]
        rw [wedge_basis_swap_neg (e i) (e j)]
        module
      · simp
    rw [h3, LinearMap.id_apply, h1]
    simp only [Finset.sum_add_distrib]
    rw [h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.not_gt]
    · subst hij; simp [hg0]
    · simp [hij, hij.not_gt]
  have := LinearMap.congr_fun hΨ t
  rw [LinearMap.id_apply] at this
  rw [← this]
  simp only [Ψ, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
  split_ifs <;> simp [h]

theorem eq_zero_of_prim [Module.Finite R V] [Module.Projective R V] (P Q : V →ₗ[R] W)
    (hb : Function.Bijective fun x : V × V ↦ P x.1 + Q x.2) (t : ⋀[R]^2 V)
    (h : exteriorPower.map 2 (P + Q) t = exteriorPower.map 2 P t + exteriorPower.map 2 Q t) : t = 0 := by
  obtain ⟨r, s, a1, a2, b1, b2'⟩ := exists_retract P Q hb
  refine eq_zero_of_pair2 t fun l u ↦ ?_
  have e1 : pair2 (l ∘ₗ r) (u ∘ₗ s) ∘ₗ exteriorPower.map 2 (P + Q) = pair2 l u := ext2 fun a b ↦ by
    rw [LinearMap.comp_apply, exterior_map_iota_two, exterior_pairing_iota_two, exterior_pairing_iota_two]
    simp [a1, a2, b1, b2']
  have e2 : pair2 (l ∘ₗ r) (u ∘ₗ s) ∘ₗ exteriorPower.map 2 P = 0 := ext2 fun a b ↦ by
    rw [LinearMap.comp_apply, exterior_map_iota_two, exterior_pairing_iota_two]
    simp [a1, a2, b1, b2']
  have e3 : pair2 (l ∘ₗ r) (u ∘ₗ s) ∘ₗ exteriorPower.map 2 Q = 0 := ext2 fun a b ↦ by
    rw [LinearMap.comp_apply, exterior_map_iota_two, exterior_pairing_iota_two]
    simp [a1, a2, b1, b2']
  have := congrArg (pair2 (l ∘ₗ r) (u ∘ₗ s)) h
  rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply, e1, e2, e3] at this
  simpa using this

end Lin

section Frame

variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}

theorem mu_pull (m : CoefMap (RingHom.id R) F G)
    (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F) (muG : Z1 G ⊗[R] Glob1 G →ₗ[R] A1 G)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG : ∀ f ω T T' φ, muG (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (t : Z1 F ⊗[R] Glob1 F) {T T' : E} (φ : T ⟶ T') :
    muG (TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t) T T' φ = q1 m T' (muF t _ _ (m.G.map φ)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f ω =>
    rw [TensorProduct.map_tmul, hG, hF, prodFirstProjection_smul]; rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem rTensor_pull (m : CoefMap (RingHom.id R) F G) (t : Z1 F ⊗[R] Glob1 F) :
    (H1.mk G).rTensor (Glob1 G) (TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t) =
      TensorProduct.map m.pull1 (pullGlob1 m) ((H1.mk F).rTensor (Glob1 F) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f ω => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_prim_cochain (m p q : CoefMap (RingHom.id R) F G)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c) (f : Z1 F) :
    ∃ g : C0 G, ∀ ⦃T T' : E⦄ (φ : T ⟶ T'), g T' - mp G φ (g T) =
      (m.pullbackOneCocycle f).1 T T' φ - ((p.pullbackOneCocycle f).1 T T' φ + (q.pullbackOneCocycle f).1 T T' φ) := by
  obtain ⟨g, hg⟩ := (H1.mk_eq_mk (F := G) (f := m.pullbackOneCocycle f) (f' := p.pullbackOneCocycle f + q.pullbackOneCocycle f)).1 (by
    have := hm1 (H1.mk F f)
    rwa [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, ← map_add] at this)
  exact ⟨g, fun T T' φ ↦ congrFun (congrFun (congrFun hg T) T') φ⟩

theorem class_zero (m p q : CoefMap (RingHom.id R) F G)
    (hH : Function.Bijective fun x : H1 F × H1 F ↦ p.pull1 x.1 + q.pull1 x.2)
    (hW : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c)
    (hmW : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω)
    (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F) (muG : Z1 G ⊗[R] Glob1 G →ₗ[R] A1 G)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG : ∀ f ω T T' φ, muG (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG3 : ∀ (t : Z1 G ⊗[R] Glob1 G) (β : A0 G), (∀ T T' φ, muG t T T' φ = β T' - p1 G φ (β T)) →
      (H1.mk G).rTensor (Glob1 G) t = 0)
    (f : Z1 F) (t : Z1 F ⊗[R] Glob1 F)
    (ht : ∀ T T' φ, muF t T T' φ = KaehlerDifferential.D R _ (f.1 T T' φ)) :
    (H1.mk F).rTensor (Glob1 F) t = 0 := by
  obtain ⟨g, hg⟩ := exists_prim_cochain m p q hm1 f
  have hz := hG3 (TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t - TensorProduct.map p.pullbackOneCocycle (pullGlob1 p) t -
      TensorProduct.map q.pullbackOneCocycle (pullGlob1 q) t) (fun T ↦ KaehlerDifferential.D R _ (g T)) (fun T T' φ ↦ by
    have e := congrArg (KaehlerDifferential.D R (G.obj T')) (hg φ)
    simp only [map_sub, map_add] at e
    simp only [map_sub, Pi.sub_apply, mu_pull _ muF muG hF hG, ht, cechDeRhamCoefMapOneForms_D, p1_D]
    rw [e]
    simp only [CoefMap.pullCocycleOne_apply]
    abel)
  rw [map_sub, map_sub, rTensor_pull, rTensor_pull, rTensor_pull] at hz
  have e1 : m.pull1 = p.pull1 + q.pull1 := LinearMap.ext hm1
  have e2 : pullGlob1 m = pullGlob1 p + pullGlob1 q := LinearMap.ext hmW
  rw [e1, e2] at hz
  refine eq_zero_of_tprim p.pull1 q.pull1 (pullGlob1 p) (pullGlob1 q) hH hW _ ?_
  rw [sub_sub, sub_eq_zero] at hz
  exact hz

def evT : C0 F ⊗[R] Glob1 F →ₗ[R] A0 F :=
  TensorProduct.lift (LinearMap.mk₂ R (fun g ω T ↦ g T • ω.1 T)
    (fun a b ω ↦ funext fun T ↦ by simp [add_smul])
    (fun r a ω ↦ funext fun T ↦ by simp)
    (fun a ω ω' ↦ funext fun T ↦ by simp)
    (fun r a ω ↦ funext fun T ↦ by simp [smul_comm r]))

theorem evT_tmul (g : C0 F) (ω : Glob1 F) (T : C) : evT (g ⊗ₜ ω) T = g T • ω.1 T := rfl

theorem exists_prim (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (t : Z1 F ⊗[R] Glob1 F) (h0 : (H1.mk F).rTensor (Glob1 F) t = 0) :
    ∃ β : A0 F, ∀ T T' φ, muF t T T' φ = β T' - p1 F φ (β T) := by
  let d' : C0 F →ₗ[R] Z1 F := (d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)
  have hex : Function.Exact d' (H1.mk F) := fun y ↦ by
    rw [H1.mk_eq_zero]
    exact ⟨fun ⟨g, hg⟩ ↦ ⟨g, Subtype.ext hg⟩, fun ⟨g, hg⟩ ↦ ⟨g, congrArg Subtype.val hg⟩⟩
  have key : ∀ (s : C0 F ⊗[R] Glob1 F) (T T' : C) (φ : T ⟶ T'),
      muF ((d').rTensor (Glob1 F) s) T T' φ = evT s T' - p1 F φ (evT s T) := fun s ↦ by
    induction s using TensorProduct.induction_on with
    | zero => intro T T' φ; simp
    | tmul g ω =>
      intro T T' φ
      rw [LinearMap.rTensor_tmul, hF, evT_tmul, evT_tmul, oneFormsMapOfFunctorMorphism_smul, ← ω.2 φ, ← sub_smul]
      rfl
    | add x y hx hy =>
      intro T T' φ
      simp only [map_add, Pi.add_apply, hx, hy]
      abel
  obtain ⟨s, rfl⟩ := (rTensor_exact (Glob1 F) hex (H1.mk_surjective F) t).1 h0
  exact ⟨evT s, key s⟩

theorem nu_pull (m : CoefMap (RingHom.id R) F G)
    (νF : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2) (νG : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hF : ∀ a b T, νF (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hG : ∀ a b T, νG (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (t : ⋀[R]^2 (Glob1 F)) (T : E) :
    νG (exteriorPower.map 2 (pullGlob1 m) t) T = qOm m 2 T (νF t _) := by
  have e : (LinearMap.proj T : W0 G 2 →ₗ[R] _) ∘ₗ νG ∘ₗ exteriorPower.map 2 (pullGlob1 m) =
      (qOm m 2 T) ∘ₗ (LinearMap.proj (m.G.obj T) : W0 F 2 →ₗ[R] _) ∘ₗ νF := ext2 fun a b ↦ by
    simp only [LinearMap.comp_apply, exterior_map_iota_two, LinearMap.proj_apply]
    rw [hG, hF, qOm_wedge]
    rfl
  exact LinearMap.congr_fun e t

theorem two_prim (m p q : CoefMap (RingHom.id R) F G)
    (hW : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c) (hC : Closed1 F = ⊤) (f : Z1 F) (β : A0 F)
    (hβ : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), β T' = p1 F φ (β T) + KaehlerDifferential.D R _ (f.1 T T' φ)) (T : E) :
    qOm m 2 T (dOne R _ (β _)) = qOm p 2 T (dOne R _ (β _)) + qOm q 2 T (dOne R _ (β _)) := by
  obtain ⟨g, hg⟩ := exists_prim_cochain m p q hm1 f
  have conn : ∀ (m' : CoefMap (RingHom.id R) F G) {T T' : E} (φ : T ⟶ T'),
      q1 m' T' (β _) = p1 G φ (q1 m' T (β _)) + KaehlerDifferential.D R _ ((m'.pullbackOneCocycle f).1 T T' φ) :=
    fun m' T T' φ ↦ by
      rw [hβ (m'.G.map φ), map_add, cechDeRhamCoefMapOneForms_naturality, cechDeRhamCoefMapOneForms_D]; rfl
  let ga : A0 G := fun T ↦ q1 m T (β _) - q1 p T (β _) - q1 q T (β _) - KaehlerDifferential.D R _ (g T)
  have hga : ga ∈ Glob1 G := fun T T' φ ↦ by
    have e := congrArg (KaehlerDifferential.D R (G.obj T')) (hg φ)
    simp only [map_sub, map_add] at e
    simp only [ga, map_sub, p1_D]
    rw [conn m φ, conn p φ, conn q φ, sub_eq_iff_eq_add.1 e]
    abel
  obtain ⟨⟨a, b⟩, hab⟩ := hW.2 ⟨ga, hga⟩
  have hcl : ∀ (a : Glob1 F) (T : C), dOne R _ (a.1 T) = 0 := fun a ↦ by
    have h : a ∈ Closed1 F := by rw [hC]; exact Submodule.mem_top
    exact h
  have e : ga T = q1 p T (a.1 _) + q1 q T (b.1 _) := (congrFun (congrArg Subtype.val hab) T).symm
  have e0 : dOne R _ (ga T) = 0 := by
    rw [e, map_add, ← qOm_dOne, ← qOm_dOne, hcl, hcl, map_zero, map_zero, add_zero]
  simp only [ga, map_sub, dOne_D, sub_zero, ← qOm_dOne] at e0
  rw [sub_sub, sub_eq_zero] at e0
  exact e0

theorem closed_of_conn (m p q : CoefMap (RingHom.id R) F G) [Module.Finite R (Glob1 F)]
    [Module.Projective R (Glob1 F)]
    (hW : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c)
    (hmW : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω)
    (hC : Closed1 F = ⊤)
    (νF : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2) (νG : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hF : ∀ a b T, νF (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hG : ∀ a b T, νG (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hinj : Function.Injective νG)
    (hsurj : ∀ w : W0 F 2, (∀ (T T' : C) (φ : T ⟶ T'), w T' = pOm F 2 φ (w T)) → ∃ t, νF t = w)
    (f : Z1 F) (β : A0 F)
    (hβ : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), β T' = p1 F φ (β T) + KaehlerDifferential.D R _ (f.1 T T' φ)) (T : C) :
    dOne R _ (β T) = 0 := by
  obtain ⟨t, ht⟩ := hsurj (fun T ↦ dOne R _ (β T)) (fun T T' φ ↦ by
    rw [hβ φ, map_add, dOne_D, add_zero, pOm_dOne])
  have h1 : exteriorPower.map 2 (pullGlob1 m) t =
      exteriorPower.map 2 (pullGlob1 p) t + exteriorPower.map 2 (pullGlob1 q) t := hinj (by
    rw [map_add]
    funext T
    rw [Pi.add_apply, nu_pull m νF νG hF hG, nu_pull p νF νG hF hG, nu_pull q νF νG hF hG, ht]
    exact two_prim m p q hW hm1 hC f β hβ T)
  have e2 : pullGlob1 m = pullGlob1 p + pullGlob1 q := LinearMap.ext hmW
  rw [e2] at h1
  have ht0 := eq_zero_of_prim (pullGlob1 p) (pullGlob1 q) hW t h1
  have := congrFun ht T
  rw [ht0, map_zero] at this
  exact this.symm

end Frame

theorem lift_of_forms : OneFormCohSt → TwoFormCohSt → LiftSt := by
  intro h1 h2 R _ C _ F hF hBi hC c
  obtain ⟨E, _, G, m, p, q, hSG, hPG, hH, hW, hm1, hmW, -⟩ := hBi
  have hFG : Framed G := by
    obtain ⟨-, -, hfin, hproj⟩ := hF
    let e : (Glob1 F × Glob1 F) ≃ₗ[R] Glob1 G :=
      LinearEquiv.ofBijective ((pullGlob1 p).coprod (pullGlob1 q)) hW
    exact ⟨hSG, hPG, Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  obtain ⟨muF, hmF, hmS, -⟩ := h1 R C F hF
  obtain ⟨muG, hmG, -, hG3⟩ := h1 R E G hFG
  obtain ⟨νF, hνF, -, hsurj⟩ := h2 R C F hF
  obtain ⟨νG, hνG, hinj, -⟩ := h2 R E G hFG
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  obtain ⟨t, ht⟩ := hmS (fun T T' φ ↦ KaehlerDifferential.D R _ (f.1 T T' φ)) (fun T T' T'' φ ψ ↦ by
    rw [Z1.comp f, map_add, p1_D])
  have hz := class_zero m p q hH hW hm1 hmW muF muG hmF hmG hG3 f t (fun T T' φ ↦ congrFun (congrFun (congrFun ht T) T') φ)
  obtain ⟨β, hβ⟩ := exists_prim muF hmF t hz
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), β T' = p1 F φ (β T) + KaehlerDifferential.D R _ (f.1 T T' φ) :=
    fun T T' φ ↦ by
      have e : KaehlerDifferential.D R _ (f.1 T T' φ) = β T' - p1 F φ (β T) :=
        (congrFun (congrFun (congrFun ht T) T') φ).symm.trans (hβ T T' φ)
      rw [e]; abel
  haveI := hF.2.2.1
  haveI := hF.2.2.2
  have hcl := closed_of_conn m p q hW hm1 hmW hC νF νG hνF hνG hinj hsurj f β hconn
  exact ⟨Hyp1.mk F ⟨(f.1, β), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hconn, hcl⟩⟩, rfl⟩

end GlobalTheory.CompanionTheory.Hodge.LiftO
