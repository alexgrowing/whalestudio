import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FormalChartOf

variable {R₀ : Type} [CommRing R₀]

theorem dual_local [IsLocalRing R₀] : IsLocalRing (DualNumber R₀) := by
  haveI : Nontrivial (DualNumber R₀) := TrivSqZeroExt.inl_injective.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

abbrev dualL (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : LAlg R₀ :=
  @LAlg.mk R₀ _ (DualNumber R₀) _ _ dual_local

abbrev baseL (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : LAlg R₀ :=
  @LAlg.mk R₀ _ R₀ _ _ _

def dualProj (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : LHom (dualL R₀) (baseL R₀) :=
  ⟨TrivSqZeroExt.fstHom R₀ R₀ R₀, ⟨fun _ h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩⟩

theorem tsze_nil {M : Type} [AddCommGroup M] [Module R₀ M] [Module R₀ᵐᵒᵖ M] [IsCentralScalar R₀ M]
    (a : TrivSqZeroExt R₀ M) (h : a.fst = 0) : IsNilpotent a := by
  refine ⟨2, ?_⟩
  have : a = TrivSqZeroExt.inr a.snd := by ext <;> simp [h]
  rw [this, pow_two, TrivSqZeroExt.inr_mul_inr]

theorem dualProj_ker [IsLocalRing R₀] :
    RingHom.ker (dualProj R₀).1 = Ideal.span {(DualNumber.eps : DualNumber R₀)} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  constructor
  · intro h
    have h' : TrivSqZeroExt.fst a = 0 := h
    refine ⟨TrivSqZeroExt.inl (TrivSqZeroExt.snd a), ?_⟩
    ext <;> simp [h']
  · rintro ⟨b, rfl⟩
    change TrivSqZeroExt.fst (b * DualNumber.eps) = 0
    simp

theorem dualProj_sqZero [IsLocalRing R₀] : (dualProj R₀).SqZero :=
  LHom.sqZero_of_span _ (DualNumber.eps : DualNumber R₀)
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) dualProj_ker DualNumber.eps_mul_eps

def epsK (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : (dualProj R₀).ker :=
  ⟨(DualNumber.eps : DualNumber R₀), (rfl : TrivSqZeroExt.fst (DualNumber.eps : DualNumber R₀) = 0)⟩

theorem tmul_eps_surj [IsLocalRing R₀] {M : Type} [AddCommGroup M] [Module R₀ M]
    (v : M ⊗[R₀] (dualProj R₀).ker) : ∃ w : M, v = w ⊗ₜ epsK R₀ := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, (TensorProduct.zero_tmul _ _).symm⟩
  | tmul w a =>
    refine ⟨TrivSqZeroExt.snd (a.1 : DualNumber R₀) • w, ?_⟩
    rw [TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    have h' : TrivSqZeroExt.fst (a.1 : DualNumber R₀) = 0 := a.2
    change (a.1 : DualNumber R₀) = TrivSqZeroExt.snd (a.1 : DualNumber R₀) • (DualNumber.eps : DualNumber R₀)
    ext <;> simp [h']
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, (TensorProduct.add_tmul _ _ _).symm⟩

theorem tmul_eps_eq_zero [IsLocalRing R₀] {M : Type} [AddCommGroup M] [Module R₀ M]
    (w : M) (h : w ⊗ₜ[R₀] epsK R₀ = 0) : w = 0 := by
  let s : (dualProj R₀).ker →ₗ[R₀] R₀ := (TrivSqZeroExt.sndHom R₀ R₀).comp (dualProj R₀).ker.subtype
  have hs : s (epsK R₀) = 1 := rfl
  have := congrArg (fun v => TensorProduct.rid R₀ M (LinearMap.lTensor M s v)) h
  simpa [hs] using this

def dualTo {S : Type} [CommRing S] [Algebra R₀ S] (i : S) (hi : i * i = 0) : DualNumber R₀ →ₐ[R₀] S :=
  DualNumber.lift ⟨(Algebra.ofId R₀ S, i), hi, fun _ => Commute.all _ _⟩

theorem dualTo_apply {S : Type} [CommRing S] [Algebra R₀ S] (i : S) (hi : i * i = 0)
    (a : DualNumber R₀) : dualTo i hi a = algebraMap R₀ S a.fst + a.snd • i := by
  rw [dualTo, DualNumber.lift_apply_apply, Algebra.smul_def]
  rfl

def dualToL [IsLocalRing R₀] (S : LAlg R₀) (hS : IsLocalHom (algebraMap R₀ (S : Type)))
    (i : (S : Type)) (hi : i * i = 0) : LHom (dualL R₀) S :=
  ⟨dualTo i hi, ⟨fun a h => by
    have h' : IsUnit (dualTo i hi a) := h
    rw [dualTo_apply] at h'
    have hn : IsNilpotent (-(TrivSqZeroExt.snd a • i)) :=
      (IsNilpotent.smul ⟨2, by rw [pow_two, hi]⟩ _).neg
    have h2 := hn.isUnit_add_left_of_commute h' (Commute.all _ _)
    rw [add_neg_cancel_right] at h2
    exact TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (hS.map_nonunit _ h2)⟩⟩

section Coord

variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G))
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S),
    (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
    (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
    ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)

include h0 hnat hinj hsurj in

theorem first_order_add (a b : Fin g → R₀) :
    x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (a k)) *
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (b k)) =
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (a k + b k)) := by
  let T := TrivSqZeroExt R₀ (R₀ × R₀)
  let a' : Fin g → T := fun k => TrivSqZeroExt.inr (a k, 0)
  let b' : Fin g → T := fun k => TrivSqZeroExt.inr (0, b k)
  have ha' : ∀ k, IsNilpotent (a' k) := fun k => tsze_nil _ rfl
  have hb' : ∀ k, IsNilpotent (b' k) := fun k => tsze_nil _ rfl
  have key : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (φ : T →ₐ[R₀] S),
      spMap φ ≫ (x T a' * x T b') = x S (fun k => φ (a' k)) * x S (fun k => φ (b' k)) := by
    intro S _ _ φ
    rw [MonObj.comp_mul, hnat _ _ φ a' ha', hnat _ _ φ b' hb']
  obtain ⟨c, hc, hxc⟩ := hsurj T R₀ (TrivSqZeroExt.fstHom R₀ R₀ (R₀ × R₀))
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) (fun u hu => tsze_nil u hu) (x T a' * x T b') (by
      rw [key]
      change x R₀ 0 * x R₀ 0 = 1
      rw [h0, _root_.mul_one])
  have hc0 : ∀ k, (c k).fst = 0 := hc
  have hcn : ∀ k, IsNilpotent (c k) := fun k => tsze_nil _ (hc0 k)
  have key2 : ∀ f : (R₀ × R₀) →ₗ[R₀] R₀,
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (a k, 0))) *
        x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (0, b k))) =
        x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (c k).snd)) := by
    intro f
    have h := key (DualNumber R₀) (TrivSqZeroExt.map f)
    rw [hxc, hnat _ _ _ c hcn] at h
    have e1 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (a' k)) =
        fun k => TrivSqZeroExt.inr (f (a k, 0)) := funext fun k => TrivSqZeroExt.map_inr _ _
    have e2 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (b' k)) =
        fun k => TrivSqZeroExt.inr (f (0, b k)) := funext fun k => TrivSqZeroExt.map_inr _ _
    have e3 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (c k)) =
        fun k => TrivSqZeroExt.inr (f (c k).snd) := funext fun k => by
      ext
      · rw [TrivSqZeroExt.fst_map, hc0]; rfl
      · rw [TrivSqZeroExt.snd_map]; rfl
    rw [e1, e2, e3] at h
    exact h.symm
  have hz : x (DualNumber R₀) (fun _ => TrivSqZeroExt.inr (0 : R₀)) = 1 := h0 _
  have k1 := key2 (LinearMap.fst R₀ R₀ R₀)
  have k2 := key2 (LinearMap.snd R₀ R₀ R₀)
  have k3 := key2 (LinearMap.fst R₀ R₀ R₀ + LinearMap.snd R₀ R₀ R₀)
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply, add_zero, zero_add] at k1 k2 k3
  rw [hz, _root_.mul_one] at k1
  rw [hz, _root_.one_mul] at k2
  have j1 := hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) k1
  have j2 := hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) k2
  rw [k3]
  congr 1
  funext k
  rw [TrivSqZeroExt.inr_injective (congrFun j1 k), TrivSqZeroExt.inr_injective (congrFun j2 k)]

variable [IsLocalRing R₀] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G))
  (he : ∀ R, Function.Bijective (e R)) (hadd : ∀ R x y, e R (x + y) = e R x * e R y)
  (hen : ∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x)

omit [IsLocalRing R₀] in
include hadd in
theorem e_zero (R : LAlg R₀) : e R 0 = 1 := by
  have h := hadd R 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

include h0 hnat hinj hsurj he hadd hen in

theorem exists_basis : ∃ gb : Module.Basis (Fin g) R₀ B.gg, ∀ w : B.gg,
    e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) =
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (gb.repr w k)) := by
  have hex : ∀ w : B.gg, ∃ t : Fin g → R₀,
      e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) =
        x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k)) := by
    intro w
    obtain ⟨c, hc, hxc⟩ := hsurj (DualNumber R₀) R₀ (dualProj R₀).1 dualProj_sqZero.1
      (fun u hu => tsze_nil u hu) (e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀))) (by
        refine (hen (dualProj R₀) _).symm.trans ?_
        rw [(B.tg_ker _ dualProj_sqZero _).2 ⟨_, rfl⟩]
        exact e_zero B e hadd _)
    have hc0 : ∀ k, (c k).fst = 0 := hc
    refine ⟨fun k => (c k).snd, hxc.trans ?_⟩
    congr 1
    funext k
    ext <;> simp [hc0]
  choose θ hθ using hex
  have huniq : ∀ s t : Fin g → R₀, x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (s k)) =
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k)) → s = t := fun s t h =>
    funext fun k => TrivSqZeroExt.inr_injective
      (congrFun (hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) h) k)
  have hθadd : ∀ v w, θ (v + w) = θ v + θ w := by
    intro v w
    apply huniq
    rw [← hθ, TensorProduct.add_tmul, map_add, hadd, hθ, hθ, first_order_add x h0 hnat hinj hsurj]
    rfl
  have hθsmul : ∀ (r : R₀) w, θ (r • w) = r • θ w := by
    intro r w
    apply huniq
    have hi : (r • DualNumber.eps : DualNumber R₀) * (r • DualNumber.eps) = 0 := by
      rw [smul_mul_smul_comm, DualNumber.eps_mul_eps, smul_zero]
    let f : LHom (dualL R₀) (dualL R₀) := dualToL (dualL R₀)
      ⟨fun a h => TrivSqZeroExt.isUnit_iff_isUnit_fst.1 h⟩ (r • DualNumber.eps) hi
    have hfa : ∀ a : DualNumber R₀, f.1 a = algebraMap R₀ _ a.fst + a.snd • r • DualNumber.eps :=
      fun a => dualTo_apply _ hi a
    have hf : ∀ a ∈ (dualProj R₀).ker, f.1.toLinearMap a ∈ (dualProj R₀).ker := by
      intro a ha
      have ha' : TrivSqZeroExt.fst a = 0 := ha
      change TrivSqZeroExt.fst (f.1 a) = 0
      rw [hfa, ha']
      simp
    have h := B.tg_nat _ _ dualProj_sqZero dualProj_sqZero f hf (w ⊗ₜ epsK R₀)
    have h2 : f.1.toLinearMap.restrict hf (epsK R₀) = r • epsK R₀ := by
      apply Subtype.ext
      change f.1 DualNumber.eps = r • DualNumber.eps
      rw [hfa]
      simp
    rw [LinearMap.lTensor_tmul, h2, ← TensorProduct.smul_tmul] at h
    rw [← hθ, h, hen, hθ]
    refine (hnat _ _ f.1 _ (fun k => tsze_nil _ rfl)).trans ?_
    congr 1
    funext k
    rw [hfa]
    ext <;> simp [mul_comm]
  let L : B.gg →ₗ[R₀] (Fin g → R₀) := ⟨⟨θ, hθadd⟩, hθsmul⟩
  have hL : Function.Bijective L := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro w hw
      have hw' : θ w = 0 := hw
      have h := hθ w
      rw [hw'] at h
      have h1 : e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) = e (dualL R₀) 0 := by
        rw [h, e_zero B e hadd]
        exact h0 (DualNumber R₀)
      have h2 := (he _).1 h1
      rw [← map_zero (B.tg (dualProj R₀) dualProj_sqZero)] at h2
      exact tmul_eps_eq_zero w (B.tg_inj _ _ h2)
    · intro t
      obtain ⟨y, hy⟩ := (he (dualL R₀)).2 (x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k)))
      have hy0 : B.map (dualProj R₀) y = 0 := by
        apply (he _).1
        rw [hen, hy, e_zero B e hadd]
        exact (hnat _ _ (dualProj R₀).1 _ (fun k => tsze_nil _ rfl)).trans (h0 R₀)
      obtain ⟨v, hv⟩ := (B.tg_ker _ dualProj_sqZero y).1 hy0
      obtain ⟨w, rfl⟩ := tmul_eps_surj v
      have h3 : θ w = t := huniq (θ w) t (by rw [← hθ, hv, hy])
      exact ⟨w, h3⟩
  refine ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective L hL), fun w => ?_⟩
  have h4 : ∀ k, (Module.Basis.ofEquivFun (LinearEquiv.ofBijective L hL)).repr w k = θ w k := fun k => by
    rw [Module.Basis.ofEquivFun_repr_apply]
    rfl
  simp only [h4]
  exact hθ w

end Coord

theorem mem_max_iff {R K : LAlg R₀} (hK : maximalIdeal (K : Type) = ⊥) (ρ : LHom R K)
    (hρ : IsNilOver ρ) (a : (R : Type)) : a ∈ maximalIdeal (R : Type) ↔ a ∈ RingHom.ker ρ.1 := by
  constructor
  · intro ha
    have : ρ.1 a ∈ maximalIdeal (K : Type) := fun h => ha (ρ.2.map_nonunit a h)
    rw [hK] at this
    exact this
  · intro ha
    exact (hρ.2 a ha).not_isUnit

theorem nil_of_mem_span {S : Type} [CommRing S] {g : ℕ} {a b : Fin g → S} (ha : ∀ i, IsNilpotent (a i))
    (hb : ∀ i, IsNilpotent (b i)) {c : S} (hc : c ∈ Ideal.span (Set.range a ∪ Set.range b)) :
    IsNilpotent c := by
  have : Ideal.span (Set.range a ∪ Set.range b) ≤ nilradical S := by
    rw [Ideal.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact mem_nilradical.2 (ha i)
    · exact mem_nilradical.2 (hb i)
  exact mem_nilradical.1 (this hc)

theorem exists_formalChart :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∃ x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G),
      (∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (g : ℕ) (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)),
    ((∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
    ∃ F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) →
      (∀ k, fAdd F a b k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ x S a * x S b = x S (fAdd F a b)) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ) (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    SmoothOfRelativeDimension g G.hom → ∀ K : LAlg R₀, maximalIdeal (K : Type) = ⊥ →
    IsLocalHom (algebraMap R₀ (K : Type)) → Nonempty (FormalChartAtZero B K g)) := by
  intro hN hL R₀ _ G _ _ _ g B e he hadd hen hsm K hK hKl
  obtain ⟨x, hx⟩ := hN G g hsm
  obtain ⟨F, hF⟩ := hL G g x hx
  obtain ⟨h0, hnat, hinj, hsurj⟩ := hx
  obtain ⟨gb, hgb⟩ := exists_basis x h0 hnat hinj hsurj B e he hadd hen
  have hFn : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → ∀ k, IsNilpotent (fAdd F a b k) :=
    fun S _ _ a b ha hb k => nil_of_mem_span ha hb ((hF S a b ha hb).1 k)
  have hχ : ∀ {R : LAlg R₀} (ρ : LHom R K), IsNilOver ρ →
      ∃ χ : {y : B.G R // B.map ρ y = 0} ≃ (Fin g → maximalIdeal (R : Type)),
        ∀ y, e R y.1 = x R (fun k => (χ y k : (R : Type))) := by
    intro R ρ hρ
    have hn : ∀ (a : Fin g → maximalIdeal (R : Type)) k, IsNilpotent (a k : (R : Type)) :=
      fun a k => hρ.2 _ ((mem_max_iff hK ρ hρ _).1 (a k).2)
    have hex : ∀ y : {y : B.G R // B.map ρ y = 0}, ∃ a : Fin g → maximalIdeal (R : Type),
        e R y.1 = x R (fun k => (a k : (R : Type))) := by
      intro y
      obtain ⟨c, hc, hxc⟩ := hsurj R K ρ.1 hρ.1 hρ.2 (e R y.1) (by
        rw [← hen, y.2, e_zero B e hadd])
      exact ⟨fun k => ⟨c k, (mem_max_iff hK ρ hρ _).2 (hc k)⟩, hxc⟩
    choose c hc using hex
    refine ⟨Equiv.ofBijective c ⟨fun y y' h => ?_, fun a => ?_⟩, hc⟩
    · exact Subtype.ext ((he R).1 (by rw [hc, hc, h]))
    · obtain ⟨y, hy⟩ := (he R).2 (x R (fun k => (a k : (R : Type))))
      have hy0 : B.map ρ y = 0 := by
        apply (he _).1
        rw [hen, hy, e_zero B e hadd, hnat _ _ ρ.1 _ (hn a), ← h0 K]
        congr 1
        funext k
        exact (mem_max_iff hK ρ hρ _).1 (a k).2
      refine ⟨⟨y, hy0⟩, funext fun k => Subtype.ext ?_⟩
      exact congrFun (hinj _ _ _ (hn _) (hn a) ((hc ⟨y, hy0⟩).symm.trans hy)) k
  choose χ hχ using @hχ
  have hn : ∀ {R : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ)
      (a : Fin g → maximalIdeal (R : Type)) k, IsNilpotent (a k : (R : Type)) :=
    fun ρ hρ a k => hρ.2 _ ((mem_max_iff hK ρ hρ _).1 (a k).2)
  refine ⟨⟨F, ?_, ?_, ?_, gb, fun {R} ρ hρ => @χ R ρ hρ, ?_, ?_, ?_⟩⟩
  · intro S _ _ a ha
    have hz : ∀ i, IsNilpotent ((0 : Fin g → S) i) := fun _ => IsNilpotent.zero
    apply hinj S _ _ (hFn S a 0 ha hz) ha
    rw [← (hF S a 0 ha hz).2, h0, _root_.mul_one]
  · intro S _ _ a b ha hb
    apply hinj S _ _ (hFn S a b ha hb) (hFn S b a hb ha)
    rw [← (hF S a b ha hb).2, ← (hF S b a hb ha).2, _root_.mul_comm]
  · intro S _ _ a b c ha hb hc
    have hab := hFn S a b ha hb
    have hbc := hFn S b c hb hc
    apply hinj S _ _ (hFn S _ c hab hc) (hFn S a _ ha hbc)
    rw [← (hF S _ c hab hc).2, ← (hF S a _ ha hbc).2, ← (hF S a b ha hb).2, ← (hF S b c hb hc).2,
      _root_.mul_assoc]
  · intro R ρ hρ y z
    apply hinj R _ _ (hn ρ hρ _) (hFn R _ _ (hn ρ hρ _) (hn ρ hρ _))
    rw [← (hF R _ _ (hn ρ hρ _) (hn ρ hρ _)).2, ← hχ, ← hχ, ← hχ, hadd]
  · intro R R' ρ ρ' hρ hρ' f hf y k
    refine congrFun (hinj R' (fun k => (χ ρ' hρ' ⟨B.map f y.1, map_nat_ker B ρ ρ' f hf y⟩ k : (R' : Type)))
      (fun k => f.1 (χ ρ hρ y k : (R : Type))) (hn ρ' hρ' _) (fun k => (hn ρ hρ _ k).map f.1) ?_) k
    rw [← hχ, ← hnat _ _ f.1 _ (hn ρ hρ _), ← hχ, hen]
  · intro R S ρ hρ π hπ ρS hfac w i k
    have hi : (i : (R : Type)) * i = 0 := by
      have h : (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul i.2 i.2
      rw [hπ.2] at h
      exact h
    have hR : IsLocalHom (algebraMap R₀ (R : Type)) := ⟨fun a h => hKl.map_nonunit a (by
      rw [← ρ.1.commutes]
      exact h.map ρ.1)⟩
    let f : LHom (dualL R₀) R := dualToL R hR i hi
    have hfa : ∀ a : DualNumber R₀, f.1 a = algebraMap R₀ _ a.fst + a.snd • (i : (R : Type)) :=
      fun a => dualTo_apply _ hi a
    have hf : ∀ a ∈ (dualProj R₀).ker, f.1.toLinearMap a ∈ π.ker := by
      intro a ha
      have ha' : TrivSqZeroExt.fst a = 0 := ha
      change f.1 a ∈ π.ker
      rw [hfa, ha', map_zero, zero_add]
      exact π.ker.smul_mem _ i.2
    have h := B.tg_nat _ _ dualProj_sqZero hπ f hf (w ⊗ₜ epsK R₀)
    have h2 : f.1.toLinearMap.restrict hf (epsK R₀) = i := by
      apply Subtype.ext
      change f.1 DualNumber.eps = i
      rw [hfa]
      simp
    rw [LinearMap.lTensor_tmul, h2] at h
    refine congrFun (hinj R
      (fun k => (χ ρ hρ ⟨B.tg π hπ (w ⊗ₜ i), map_tg_ker B ρ π hπ ρS hfac _⟩ k : (R : Type)))
      (fun k => gb.repr w k • (i : (R : Type))) (hn ρ hρ _)
      (fun k => IsNilpotent.smul ⟨2, by rw [pow_two, hi]⟩ _) ?_) k
    rw [← hχ]
    change e R (B.tg π hπ (w ⊗ₜ i)) = _
    rw [h, hen, hgb]
    refine (hnat _ _ f.1 _ (fun k => tsze_nil _ rfl)).trans ?_
    congr 1
    funext k
    rw [hfa]
    simp

end GlobalTheory.FormalChartOf
