import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLabStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSumsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMemberStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.Sep.ClassSumFun

section SumILemmas
variable {R : Type} [CommRing R] {I : Ideal R} {E Ix : Type} [AddCommGroup E] [Module R E]

theorem sumI_zero : SumI I (fun _ : Ix => (0 : E)) 0 :=
  ⟨⊥, Submodule.fg_bot, Submodule.zero_mem _, fun _ => Submodule.zero_mem _,
    fun _ => ⟨∅, fun T _ => by simp⟩⟩

theorem sumI_add {x y : Ix → E} {s t : E} (hx : SumI I x s) (hy : SumI I y t) :
    SumI I (fun i => x i + y i) (s + t) := by
  obtain ⟨N₁, f₁, hs₁, hx₁, h₁⟩ := hx
  obtain ⟨N₂, f₂, hs₂, hx₂, h₂⟩ := hy
  refine ⟨N₁ ⊔ N₂, f₁.sup f₂, Submodule.add_mem_sup hs₁ hs₂, fun i => Submodule.add_mem_sup (hx₁ i) (hx₂ i),
    fun n => ?_⟩
  obtain ⟨S₁, hS₁⟩ := h₁ n
  obtain ⟨S₂, hS₂⟩ := h₂ n
  classical
  refine ⟨S₁ ∪ S₂, fun T hT => ?_⟩
  have e : s + t - ∑ i ∈ T, (x i + y i) = (s - ∑ i ∈ T, x i) + (t - ∑ i ∈ T, y i) := by
    rw [Finset.sum_add_distrib]; abel
  rw [e]
  exact Submodule.add_mem _
    (Submodule.smul_mono le_rfl le_sup_left (hS₁ T (Finset.union_subset_left hT)))
    (Submodule.smul_mono le_rfl le_sup_right (hS₂ T (Finset.union_subset_right hT)))

theorem sumI_smul (c : R) {x : Ix → E} {s : E} (hx : SumI I x s) : SumI I (fun i => c • x i) (c • s) := by
  obtain ⟨N, f, hs, hxN, h⟩ := hx
  refine ⟨N, f, N.smul_mem c hs, fun i => N.smul_mem c (hxN i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := h n
  refine ⟨S, fun T hT => ?_⟩
  rw [← Finset.smul_sum, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ c (hS T hT)

theorem sumI_sum {κ : Type} (F : Finset κ) (x : κ → Ix → E) (s : κ → E) (h : ∀ j ∈ F, SumI I (x j) (s j)) :
    SumI I (fun i => ∑ j ∈ F, x j i) (∑ j ∈ F, s j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (sumI_zero (I := I) (E := E) (Ix := Ix))
  | insert a F ha ih =>
    simp only [Finset.sum_insert ha]
    exact sumI_add (h a (Finset.mem_insert_self a F)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem sumI_comp {Ix' : Type} {e : Ix' → Ix} (he : Function.Injective e) {x : Ix → E} {s : E}
    (h0 : ∀ i, i ∉ Set.range e → x i = 0) (hx : SumI I x s) : SumI I (fun j => x (e j)) s := by
  classical
  obtain ⟨N, f, hs, hxN, h⟩ := hx
  refine ⟨N, f, hs, fun j => hxN (e j), fun n => ?_⟩
  obtain ⟨S, hS⟩ := h n
  refine ⟨S.preimage e he.injOn, fun T hT => ?_⟩
  have hsum : ∑ j ∈ T, x (e j) = ∑ i ∈ T.map ⟨e, he⟩ ∪ S, x i := by
    rw [show ∑ j ∈ T, x (e j) = ∑ i ∈ T.map ⟨e, he⟩, x i from (Finset.sum_map T ⟨e, he⟩ x).symm]
    refine Finset.sum_subset Finset.subset_union_left fun i hi hni => ?_
    refine h0 i fun ⟨j, hj⟩ => hni ?_
    subst hj
    have hjS : e j ∈ S := by
      rcases Finset.mem_union.1 hi with h1 | h1
      · exact absurd h1 hni
      · exact h1
    exact Finset.mem_map_of_mem _ (hT (Finset.mem_preimage.2 hjS))
  rw [hsum]
  exact hS _ Finset.subset_union_right

end SumILemmas

theorem pow_val_mul_pow_val {M : Type} [Monoid M] {m : ℕ} [NeZero m] {q : M} (hq : q ^ m = 1) (x y : ZMod m) :
    q ^ x.val * q ^ y.val = q ^ (x + y).val := by
  rw [← pow_add, ZMod.val_add]
  conv_lhs => rw [← Nat.div_add_mod (x.val + y.val) m, pow_add, pow_mul, hq, one_pow, _root_.one_mul]

theorem sum_pow_val_eq_zero {V : Type} [CommRing V] [IsDomain V] {m : ℕ} [NeZero m] {q : V}
    (hq : IsPrimitiveRoot q m) {G : Type} [AddCommGroup G] [Fintype G] (k : G → ZMod m)
    (hk : ∀ x y, k (x + y) = k x + k y) (τ₀ : G) (h₀ : k τ₀ ≠ 0) : ∑ τ, q ^ (k τ).val = 0 := by
  have hsh : ∑ τ, q ^ (k τ).val = (∑ τ, q ^ (k τ).val) * q ^ (k τ₀).val := by
    rw [Finset.sum_mul]
    refine (Fintype.sum_equiv (Equiv.addRight τ₀) _ _ fun τ => ?_).symm
    rw [pow_val_mul_pow_val hq.pow_eq_one, Equiv.coe_addRight, hk]
  have hne : q ^ (k τ₀).val ≠ 1 :=
    hq.pow_ne_one_of_pos_of_lt (by rwa [Ne, ZMod.val_eq_zero]) (ZMod.val_lt _)
  have h2 : (∑ τ, q ^ (k τ).val) * (q ^ (k τ₀).val - 1) = 0 := by
    rw [mul_sub, _root_.mul_one, ← hsh, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hne)

theorem isPrimitiveRoot_map {o V : Type} [CommRing o] [IsDomain o] [CommRing V] [IsDomain V] (φ : o →+* V)
    {m : ℕ} (hm : 0 < m) {q : o} (hq : IsPrimitiveRoot q m) (hu : IsUnit (m : o)) : IsPrimitiveRoot (φ q) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_
  have hp := congrArg φ hq.prod_one_sub_pow_eq_order
  rw [map_prod] at hp
  have hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_
    rw [map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]
  rw [hz] at hp
  have hu' : IsUnit (φ ((n : o) + 1)) := by
    have := hu.map φ; simpa using this
  exact hu'.ne_zero hp.symm

theorem eStd_sub_right (g m : ℕ) (x a b : Fin g ⊕ Fin g → ZMod m) :
    eStd g m x (a - b) = eStd g m x a - eStd g m x b := by
  simp only [eStd, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem eStd_add_left (g m : ℕ) (x y a : Fin g ⊕ Fin g → ZMod m) :
    eStd g m (x + y) a = eStd g m x a + eStd g m y a := by
  simp only [eStd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.Poinc.Sep.ClassSumFun

namespace GlobalTheory.Poinc.Sep.ClassSumFun
open Classical

theorem exists_classSum_fun : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ f : X₁.S.Gam → X₁.S.Gam → X₁.Ω₁, (∀ a b, ∀ w : X₁.M.Z, X₁.M.Div X₁.S.th x₀ w → f a b ∈ X₁.M.O w) ∧ (∀ a a' b, a - a' ∈ X₁.S.HH X₁.M z₁ → f a b = f a' b) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C) (a : X₁.S.Gam) (κ : Fin 8 → X), 𝔪.YY a κ → ∀ h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ h = f a (lab c) → SumI (maximalIdeal V) (fun nu : Fin 8 → X => T (κ + (X₁.S.r * X₁.S.N) • nu) c) (ev h) := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv
  obtain ⟨sg, eps, hlink⟩ := GlobalTheory.T.theta_constants_torus_translates_twisted_sums g n F W Z i X₁ z₁ act x₀ hdiv
  have hm0 : 0 < X₁.S.r * X₁.S.N :=
    Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)
  haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨hm0.ne'⟩
  haveI := ArithBase.ded (o := X₁.o₁) X₁.Ω₁
  have hcard : IsUnit ((Nat.card (X₁.S.TT X₁.M z₁) : ℕ) : X₁.o₁) := by
    have hdvd : Nat.card (X₁.S.TT X₁.M z₁) ∣ (X₁.S.r * X₁.S.N) ^ Nat.card (Fin X₁.S.g ⊕ Fin X₁.S.g) := by
      have h1 := AddSubgroup.card_addSubgroup_dvd_card (X₁.S.TT X₁.M z₁)
      have h2 : Nat.card X₁.S.Gam = (X₁.S.r * X₁.S.N) ^ Nat.card (Fin X₁.S.g ⊕ Fin X₁.S.g) := by
        rw [Nat.card_fun, Nat.card_zmod]
      rwa [h2] at h1
    obtain ⟨k, hk⟩ := hdvd
    have hu : IsUnit ((((X₁.S.r * X₁.S.N) ^ Nat.card (Fin X₁.S.g ⊕ Fin X₁.S.g) : ℕ)) : X₁.o₁) := by
      rw [Nat.cast_pow]; exact X₁.S.unit.pow _
    rw [hk, Nat.cast_mul] at hu
    exact isUnit_of_mul_isUnit_left hu
  set u : X₁.o₁ := ↑hcard.unit⁻¹ with hu_def
  have hu1 : u * (Nat.card (X₁.S.TT X₁.M z₁) : X₁.o₁) = 1 := hcard.val_inv_mul
  set K : X₁.S.Gam → X₁.S.TT X₁.M z₁ → ZMod (X₁.S.r * X₁.S.N) :=
    fun a τ => (-(sg : ℤ)) • eStd X₁.S.g _ (τ : X₁.S.Gam) a with hK
  refine ⟨fun a b => ∑ τ : X₁.S.TT X₁.M z₁, algebraMap X₁.o₁ X₁.Ω₁ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val) *
      (algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps b τ) * X₁.S.th (b + τ) / X₁.S.th x₀), ?_, ?_, ?_⟩
  · intro a b w hw
    refine Subalgebra.sum_mem _ fun τ _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
    rw [mul_div_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hw.2 _)
  · intro a a' b hab
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h0 : eStd X₁.S.g _ (τ : X₁.S.Gam) (a - a') = 0 := τ.2 _ hab
    rw [eStd_sub_right, sub_eq_zero] at h0
    have : K a τ = K a' τ := by simp only [hK, h0]
    rw [this]
  · intro V _ _ _ ev X _ m' t δ 𝔪 C lab hlab T hT c a κ hκ h hh
    obtain ⟨hex, hsurj, hcong, hadd⟩ := GlobalTheory.T.surjective_labelHom_lattice_mod_level_thetaMember g n F W Z i X₁ z₁ act V ev X m' t δ 𝔪
    have hint := GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hdiv V ev X m' t δ 𝔪
    have hY0 : 𝔪.YY 0 0 := (hint 0).1 (AddSubgroup.zero_mem _)
    have hneg : ∀ a mu, 𝔪.YY a mu → 𝔪.YY (-a) (-mu) := by
      intro a mu ha
      obtain ⟨mu', hmu'⟩ := hex (-a)
      have h1 := hadd a (-a) mu mu' ha hmu'
      rw [add_neg_cancel] at h1
      have hc := (hcong 0 0 (mu + mu') hY0).1 h1
      refine (hcong (-a) mu' (-mu) hmu').2 fun v => ?_
      obtain ⟨w, hw⟩ := hc v
      refine ⟨-w, ?_⟩
      simp only [Pi.add_apply, Pi.zero_apply, zero_add, Pi.neg_apply] at hw ⊢
      rw [smul_neg, ← hw]
      abel
    have hsub : ∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a - a') (mu - mu') := by
      intro a a' mu mu' ha ha'
      simpa [sub_eq_add_neg] using hadd _ _ _ _ ha (hneg _ _ ha')
    choose A hA using hsurj
    have hdiff : ∀ a' mu, 𝔪.YY a' mu → ∀ τ ∈ X₁.S.TT X₁.M z₁, eStd X₁.S.g _ τ a' = eStd X₁.S.g _ τ (A mu) := by
      intro a' mu ha' τ hτ
      have h1 : a' - A mu ∈ X₁.S.HH X₁.M z₁ := (hint _).2 (by simpa using hsub _ _ _ _ ha' (hA mu))
      have h2 : eStd X₁.S.g _ τ (a' - A mu) = 0 := hτ _ h1
      rwa [eStd_sub_right, sub_eq_zero] at h2
    set ι₀ : X₁.o₁ →+* X₁.M.Z.presheaf.stalk z₁ :=
      (X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁)) with hι₀
    have hι : ∀ x, X₁.M.stalkHom z₁ (ι₀ x) = algebraMap X₁.o₁ X₁.Ω₁ x := by
      intro x
      rw [← RatModel.coe_stalkEquiv, hι₀, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply]
      rfl
    have hmemτ : ∀ τ : X₁.S.TT X₁.M z₁, algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ ∈
        X₁.M.O z₁ := by
      intro τ
      rw [mul_div_assoc]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hdiv.2 _)
    choose hτ hhτ using fun τ => (X₁.M.stalkEquiv z₁).surjective ⟨_, hmemτ τ⟩
    have hhτ' : ∀ τ, X₁.M.stalkHom z₁ (hτ τ) =
        algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ := fun τ => by
      rw [← RatModel.coe_stalkEquiv, hhτ τ]
    have hzt : X₁.M.stalkHom z₁ (ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) =
        algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) := hι _
    set wt : X₁.S.TT X₁.M z₁ → (Fin 8 → X) → ZMod (X₁.S.r * X₁.S.N) :=
      fun τ mu => (sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) (A mu) with hwt
    have hS : ∀ τ : X₁.S.TT X₁.M z₁, SumI (maximalIdeal V)
        (fun mu => ev (ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) ^ (wt τ mu).val * T mu c) (ev (hτ τ)) := fun τ =>
      hlink V ev X m' t δ 𝔪 C lab hlab T hT c τ τ.2 _ (hτ τ) hzt (hhτ' τ) (wt τ)
        (fun a' mu ha' => by simp only [hwt]; rw [hdiff a' mu ha' τ τ.2])
    have hhe : h = ∑ τ : X₁.S.TT X₁.M z₁, ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val) * hτ τ := by
      apply X₁.M.stalkHom_injective z₁
      rw [hh, map_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [(X₁.M.stalkHom z₁).map_mul, hι, hhτ']
    have hsum := sumI_sum (I := maximalIdeal V) Finset.univ
      (fun τ mu => ev (ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val)) •
        (ev (ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) ^ (wt τ mu).val * T mu c))
      (fun τ => ev (ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val)) • ev (hτ τ)) (fun τ _ => sumI_smul _ (hS τ))
    have hev : ∑ τ ∈ Finset.univ, ev (ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val)) • ev (hτ τ) = ev h := by
      rw [hhe, map_sum]
      exact Finset.sum_congr rfl fun τ _ => by simp only [smul_eq_mul, map_mul]
    rw [hev] at hsum
    set q := ev (ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) with hq_def
    have hq : IsPrimitiveRoot q (X₁.S.r * X₁.S.N) :=
      isPrimitiveRoot_map (ev.comp ι₀) hm0 (X₁.S.prim.pow (by positivity) (sq _)) X₁.S.unit
    have hpt : ∀ mu, (∑ τ ∈ Finset.univ, ev (ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val)) •
        (q ^ (wt τ mu).val * T mu c)) =
        ev (ι₀ u) * (∑ τ : X₁.S.TT X₁.M z₁, q ^ ((sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) (A mu - a)).val) * T mu c := by
      intro mu
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have e1 : K a τ + wt τ mu = (sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) (A mu - a) := by
        simp only [hK, hwt, eStd_sub_right, smul_sub, neg_smul]
        abel
      rw [← e1, ← pow_val_mul_pow_val hq.pow_eq_one, smul_eq_mul]
      rw [map_mul ι₀, map_mul ev, map_pow ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)), map_pow ev (ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))),
        ← hq_def]
      ring
    have hchar : ∀ d : X₁.S.Gam, (∑ τ : X₁.S.TT X₁.M z₁, q ^ ((sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) d).val) =
        if d ∈ X₁.S.HH X₁.M z₁ then (Nat.card (X₁.S.TT X₁.M z₁) : V) else 0 := by
      intro d
      split_ifs with hd
      · have h0 : ∀ τ : X₁.S.TT X₁.M z₁, eStd X₁.S.g _ (τ : X₁.S.Gam) d = 0 := fun τ => τ.2 d hd
        simp [h0, Nat.card_eq_fintype_card]
      · have hd' : d ∉ X₁.S.perp (X₁.S.TT X₁.M z₁) := by
          rwa [show X₁.S.TT X₁.M z₁ = X₁.S.perp (X₁.S.HH X₁.M z₁) from rfl, TestBasis.perp_perp]
        have hex' : ∃ τ ∈ X₁.S.TT X₁.M z₁, eStd X₁.S.g _ d τ ≠ 0 := by
          by_contra hc
          push_neg at hc
          exact hd' hc
        obtain ⟨τ₀, hτ₀, h₀⟩ := hex'
        have h₀' : eStd X₁.S.g _ τ₀ d ≠ 0 := by
          rw [Weights.eStd_swap]; exact neg_ne_zero.2 h₀
        refine sum_pow_val_eq_zero hq (fun τ : X₁.S.TT X₁.M z₁ => (sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) d)
          (fun x y => by simp only [AddSubgroup.coe_add, eStd_add_left, smul_add]) ⟨τ₀, hτ₀⟩ ?_
        rcases Int.units_eq_one_or sg with hs | hs <;> simpa [hs] using h₀'
    have hucard : ev (ι₀ u) * (Nat.card (X₁.S.TT X₁.M z₁) : V) = 1 := by
      rw [← map_natCast ev (Nat.card _), ← map_mul, ← map_natCast ι₀ (Nat.card _), ← map_mul, hu1, map_one, map_one]
    have hfam : ∀ mu, (∑ τ ∈ Finset.univ, ev (ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val)) •
        (q ^ (wt τ mu).val * T mu c)) = if A mu - a ∈ X₁.S.HH X₁.M z₁ then T mu c else 0 := by
      intro mu
      rw [hpt, hchar]
      split_ifs
      · rw [hucard, _root_.one_mul]
      · simp
    have hin : ∀ nu : Fin 8 → X, A (κ + (X₁.S.r * X₁.S.N) • nu) - a ∈ X₁.S.HH X₁.M z₁ := by
      intro nu
      refine (hint _).2 ((hcong _ _ 0 (hsub _ _ _ _ (hA _) hκ)).2 fun v => ⟨-nu v, ?_⟩)
      simp
    have hinj : Function.Injective fun nu : Fin 8 → X => κ + (X₁.S.r * X₁.S.N) • nu := by
      intro nu nu' he
      have h1 : (X₁.S.r * X₁.S.N) • nu = (X₁.S.r * X₁.S.N) • nu' := add_left_cancel he
      apply 𝔪.e₈.injective
      have h2 : ((X₁.S.r * X₁.S.N : ℕ) : ℤ) • (𝔪.e₈ nu - 𝔪.e₈ nu') = 0 := by
        rw [natCast_zsmul, smul_sub, ← map_nsmul, ← map_nsmul, h1, sub_self]
      rw [smul_eq_zero] at h2
      exact sub_eq_zero.1 (h2.resolve_left (by exact_mod_cast hm0.ne'))
    have key := sumI_comp hinj (fun mu hmu => ?_) hsum
    · simp only [hfam, hin, ite_true] at key
      exact key
    · rw [hfam, if_neg]
      intro hd
      apply hmu
      have h1 := (hcong _ _ 0 (hsub _ _ _ _ (hA mu) hκ)).1 ((hint _).1 hd)
      choose w hw using h1
      refine ⟨-w, funext fun v => ?_⟩
      have h2 := hw v
      simp only [Pi.zero_apply, Pi.sub_apply] at h2
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_neg]
      calc κ v + -((X₁.S.r * X₁.S.N) • w v) = κ v + -((X₁.S.r * X₁.S.N) • w v) + (mu v - κ v + (X₁.S.r * X₁.S.N) • w v) := by
            rw [← h2, add_zero]
        _ = mu v := by abel

end GlobalTheory.Poinc.Sep.ClassSumFun
