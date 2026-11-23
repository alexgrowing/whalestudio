import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitOfVal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

def GV (c : S.J → Ω) (a : Q.L.L.ι) (K : Type) [Field K] (x : Sp K ⟶ Q.G.left) (v : K) : Prop :=
  ∀ (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left)
    (jP : ρ.P.L.ι), g ≫ Q.φ = x → g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt →
    r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ →
    ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP →
    ∑ i, β (c i) * valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val ^ (S.N : ℤ) * v

variable {K : Type} [Field K] {c : S.J → Ω} {a a' : Q.L.L.ι}

theorem le_w {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀} {jP : ρ.P.L.ι}
    (h : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP) (h' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a) :
    ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U (fun _ => jP, fun _ => a) :=
  le_inf' (le_wchart _ _ _ fun _ => h) (le_wchart _ _ _ fun _ => h')

theorem val_w {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀} {jP jP' : ρ.P.L.ι}
    (h : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP) (h' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a)
    (k : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP') (k' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a') :
    valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val =
      valF (g ≫ pullback.fst ρ.P.A.hom Q.u₀) _ (ρ.P.L.g jP jP').val * (valF (g ≫ Q.φ) _ (Q.L.L.g a a').val)⁻¹ *
        valF g _ (Q.w.s (fun _ => jP', fun _ => a')).val := by
  refine (val_gen Q.w_gen g (le_w Q h h') (le_w Q k k')).trans (congrArg (· * _) ?_)
  refine (val_div_g _ _ _ _ g (le_w Q h h') (le_w Q k k')).trans ?_
  exact congrArg₂ (fun x y => x * y⁻¹) ((val_linComb_g (I := PUnit) _ _ 1 _ _ g h k).trans (zpow_one _))
    ((val_linComb_g (I := PUnit) _ _ 1 _ _ g h' k').trans (zpow_one _))

omit Q in
theorem thetaSystem_baseSection_value_chart {r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left} {jP jP' : ρ.P.L.ι}
    (h : ⊤ ≤ (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⁻¹ᵁ ρ.P.L.U jP)
    (k : ⊤ ≤ (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⁻¹ᵁ ρ.P.L.U jP') (i : S.J) :
    valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) _ (ρ.P.L.g jP jP').val ^ (S.N : ℤ) *
        valF r _ ((ρ.s i).f (fun _ => jP')) :=
  (val_sec (ρ.s i) r (j := fun _ => jP) (k := fun _ => jP') (le_wchart _ _ _ fun _ => h)
    (le_wchart _ _ _ fun _ => k)).trans (congrArg (· * _) (val_linComb_g (I := Fin 1) _ _ _ _ _ r h k))

theorem exists_data (hU : (U₀ : Set M.Z).Nonempty) {Y : Scheme.{0}} (x : Y ⟶ Q.G.left) (κ : Y ⟶ Sp Ω)
    (h : x ≫ Q.G.hom = κ ≫ M.pt) : ∃ (g : Y ⟶ pullback ρ.P.A.hom Q.u₀) (r : Y ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left),
      g ≫ Q.φ = x ∧ g ≫ pullback.snd _ _ ≫ U₀.ι = κ ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ := by
  have hr : Set.range (κ ≫ M.pt) ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := κ w) trivial
  let y : Y ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (κ ≫ M.pt) hr
  have hy : y ≫ U₀.ι = κ ≫ M.pt := IsOpenImmersion.lift_fac _ _ _
  let g : Y ⟶ pullback ρ.P.A.hom Q.u₀ := Q.cart.1.lift x y (h.trans hy.symm)
  have hg2 : g ≫ pullback.snd _ _ = y := Q.cart.1.lift_snd x y _
  refine ⟨g, pullback.lift ((g ≫ pullback.fst _ _) ≫ ρ.P.A.hom) (g ≫ pullback.fst _ _)
    (Category.comp_id _), Q.cart.1.lift_fst x y _, ?_, pullback.lift_snd _ _ _⟩
  rw [← Category.assoc, hg2, hy]

theorem exists_data' (hU : (U₀ : Set M.Z).Nonempty) (x : Sp K ⟶ Q.G.left) (β : Ω →+* K)
    (h : x ≫ Q.G.hom = spMap β ≫ M.pt) : ∃ (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀)
      (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι),
      g ≫ Q.φ = x ∧ g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ ∧
      ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP := by
  obtain ⟨g, r, h1, h2, h3⟩ := exists_data Q hU x _ h
  obtain ⟨jP, hj⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ρ.P.isLB.cover
  exact ⟨g, r, jP, h1, h2, h3, hj⟩

variable {Q} {x : Sp K ⟶ Q.G.left} {v v' : K}

theorem GV.unique (hU : (U₀ : Set M.Z).Nonempty) {β : Ω →+* K} (h : x ≫ Q.G.hom = spMap β ≫ M.pt)
    (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (H : GV Q c a K x v) (H' : GV Q c a K x v') : v = v' := by
  obtain ⟨g, r, jP, rfl, h2, h3, hj⟩ := exists_data' Q hU x β h
  exact mul_left_cancel₀ (zpow_ne_zero _ (val_unit_ne g (le_w Q hj ha) _))
    ((H β g r jP rfl h2 h3 hj).symm.trans (H' β g r jP rfl h2 h3 hj))

theorem GV.chart (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (ha' : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a') (H : GV Q c a K x v) :
    GV Q c a' K x (valF x _ (Q.L.L.g a' a).val ^ (S.N : ℤ) * v) := by
  rintro β g r jP rfl h2 h3 hj
  have h0 := zpow_ne_zero (S.N : ℤ) (val_unit_ne _ (le_inf' ha' ha) (Q.L.L.g a' a))
  rw [H β g r jP rfl h2 h3 hj, val_w Q hj ha' hj ha, val_g_self ρ.P.isLB _ hj, _root_.one_mul, mul_zpow, inv_zpow]
  field_simp

theorem GV.of_one {β : Ω →+* K} {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀}
    {r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left} {jP : ρ.P.L.ι} (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (h1 : g ≫ Q.φ = x)
    (h2 : g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt)
    (h3 : r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _)
    (hj : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP)
    (H : ∑ i, β (c i) * valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val ^ (S.N : ℤ) * v) : GV Q c a K x v := by
  intro β' g' r' jP' k1 k2 k3 kj
  have : Mono Q.φ := (MorphismProperty.monomorphisms _).of_isPullback Q.cart.1.flip
    (inferInstanceAs (Mono U₀.ι))
  have := EndoExtend.isPreimmersion_pt M
  have : Mono (snd (baseOver (Sp S.R)) ρ.P.A).left := inferInstanceAs (Mono (pullback.snd (𝟙 _) ρ.P.A.hom))
  obtain rfl : g' = g := (cancel_mono Q.φ).1 (k1.trans h1.symm)
  obtain rfl : r' = r := (cancel_mono _).1 (k3.trans h3.symm)
  obtain rfl : β' = β := congrArg (·.hom) (Spec.map_injective ((cancel_mono M.pt).1 (k2.symm.trans h2)))
  subst h1
  rw [val_w Q kj ha hj ha, val_g_self Q.L.isLB _ ha, inv_one, _root_.mul_one, mul_zpow, _root_.mul_assoc, ← H,
    Finset.mul_sum, ← h3]
  rw [← h3] at kj hj
  exact Finset.sum_congr rfl fun i _ => by rw [thetaSystem_baseSection_value_chart kj hj, mul_left_comm]

section Ratio

theorem exists_pt {X : Scheme.{0}} (y : X) : ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ X), ∀ w, g w = y :=
  ⟨X.residueField y, inferInstance, X.fromSpecResidueField _, fun _ => Scheme.fromSpecResidueField_apply _ _⟩

theorem exists_ne {P : Scheme.{0}} {O : LB P} {I : Type} {τ : I → O.Sec} (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (h : Sp K ⟶ P) {k : O.ι} (hk : ⊤ ≤ h ⁻¹ᵁ O.U k) : ∃ i, valF h _ ((τ i).f k) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top h hτ
  obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 ((le_preimage_iff h _).1 hi)
  have h1 := (le_preimage_iff h _).2 hk'
  have h2 := le_preimage_mono h (P.basicOpen_le _) h1
  refine ⟨i, ?_⟩
  rw [val_sec (τ i) h hk h2]
  exact mul_ne_zero (val_unit_ne h (le_inf' hk h2) _) ((le_preimage_basicOpen_iff h h2 _).1 h1).ne_zero

theorem exists_mem_basicOpen {P : Scheme.{0}} {O : LB P} {I : Type} {τ : I → O.Sec}
    (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (y : P) {k : O.ι} (hk : y ∈ O.U k) : ∃ i, y ∈ P.basicOpen ((τ i).f k) := by
  obtain ⟨F, _, g, hg⟩ := exists_pt y
  have h1 : ⊤ ≤ g ⁻¹ᵁ O.U k := fun w _ => show g w ∈ O.U k from Set.mem_of_eq_of_mem (hg w) hk
  obtain ⟨i, hi⟩ := exists_ne hτ g h1
  exact ⟨i, Set.mem_of_eq_of_mem (hg (IsLocalRing.closedPoint F)).symm
    ((le_preimage_basicOpen_iff g h1 _).2 hi.isUnit trivial)⟩

variable (Q) {P : Scheme.{0}} (ν : P ⟶ Q.G.left) {O : LB P} (τ : S.J → O.Sec) (b : S.J → S.J → Ω)

def Ratio (a : Q.L.L.ι) (k : O.ι) (K : Type) [Field K] (h : Sp K ⟶ P) (v : K) : Prop :=
  v ≠ 0 ∧ ∀ i, GV Q (b i) a K (h ≫ ν) (v * valF h _ ((τ i).f k))

variable {Q ν τ b} {k k' : O.ι} {h : Sp K ⟶ P}

theorem Ratio.unique (hU : (U₀ : Set M.Z).Nonempty) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) {β : Ω →+* K}
    (e : (h ≫ ν) ≫ Q.G.hom = spMap β ≫ M.pt) (ha : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hk : ⊤ ≤ h ⁻¹ᵁ O.U k)
    (H : Ratio Q ν τ b a k K h v) (H' : Ratio Q ν τ b a k K h v') : v = v' := by
  obtain ⟨i, hi⟩ := exists_ne hτ h hk
  exact mul_right_cancel₀ hi ((H.2 i).unique hU e ha (H'.2 i))

theorem Ratio.chart (ha : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hk : ⊤ ≤ h ⁻¹ᵁ O.U k)
    (ha' : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a') (hk' : ⊤ ≤ h ⁻¹ᵁ O.U k') (H : Ratio Q ν τ b a k K h v) :
    Ratio Q ν τ b a' k' K h
      (valF (h ≫ ν) _ (Q.L.L.g a' a).val ^ (S.N : ℤ) * (valF h _ (O.g k' k).val)⁻¹ * v) := by
  have h1 := val_unit_ne _ (le_inf' hk' hk) (O.g k' k)
  refine ⟨mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (val_unit_ne _ (le_inf' ha' ha) _)) (inv_ne_zero h1)) H.1,
    fun i => ?_⟩
  convert (H.2 i).chart ha ha' using 1
  rw [val_sec (τ i) h hk' hk]
  field_simp

theorem exists_unit (hU : (U₀ : Set M.Z).Nonempty) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (hp : ∀ (K : Type) [Field K] (β : Ω →+* K) (h : Sp K ⟶ P), (h ≫ ν) ≫ Q.G.hom = spMap β ≫ M.pt →
      ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a → ⊤ ≤ h ⁻¹ᵁ O.U k → ∃ v, Ratio Q ν τ b a k K h v)
    {Y : Scheme.{0}} [IsIntegral Y] (J : Y ⟶ P) (κ : Y ⟶ Sp Ω) (hJ : (J ≫ ν) ≫ Q.G.hom = κ ≫ M.pt)
    (V : Y.Opens) (hV : V ≤ (J ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hV' : V ≤ J ⁻¹ᵁ O.U k) :
    ∃ t : Γ(Y, V)ˣ, ∀ (K : Type) [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V →
      Ratio Q ν τ b a k K (h ≫ J) (valF h V t.val) := by
  have hβ : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), spMap (Spec.preimage (h ≫ κ)).hom = h ≫ κ := fun h =>
    Spec.map_preimage _
  have he : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y),
      ((h ≫ J) ≫ ν) ≫ Q.G.hom = spMap (Spec.preimage (h ≫ κ)).hom ≫ M.pt := fun h => by
    rw [hβ, Category.assoc h κ, ← hJ]; simp only [Category.assoc]
  have ha : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V → ⊤ ≤ ((h ≫ J) ≫ ν) ⁻¹ᵁ Q.L.L.U a :=
    fun h hh => le_preimage_mono h hV hh
  have hk : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V → ⊤ ≤ (h ≫ J) ⁻¹ᵁ O.U k :=
    fun h hh => le_preimage_mono h hV' hh
  obtain ⟨F, _, ξ, hξ⟩ := exists_generic Y
  obtain ⟨g, r, g1, g2, g3⟩ := exists_data Q hU _ κ hJ
  obtain ⟨f, hf⟩ := exists_glue V (fun K _ h v => Ratio Q ν τ b a k K (h ≫ J) v) ξ hξ
    (fun hh v v' H H' => H.unique hU hτ (he ξ) (ha ξ hh) (hk ξ hh) H') (fun y hy => by
      obtain ⟨jP, hj⟩ := exists_chart ρ.P.isLB ((g ≫ pullback.fst ρ.P.A.hom Q.u₀) y)
      obtain ⟨i, hi⟩ := exists_mem_basicOpen hτ (J y) (hV' hy)
      have m1 : r y ∈ (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).U (fun _ => jP) :=
        Set.mem_iInter.2 fun _ => by rw [← g3] at hj; exact hj
      have m2 : g y ∈ (pullback ρ.P.A.hom Q.u₀).basicOpen (Q.w.s (fun _ => jP, fun _ => a)).val := by
        rw [Scheme.basicOpen_of_isUnit _ (Units.isUnit _)]
        have := hV hy
        rw [← g1] at this
        exact ⟨Set.mem_iInter.2 fun _ => hj, Set.mem_iInter.2 fun _ => this⟩
      obtain ⟨W, f, hW, hf⟩ := ((Reg.sum Finset.univ fun l => (Reg.val κ (U := ⊤)
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (b i l)) trivial).mul (Reg.val r ((ρ.s l).f _) m1)).mul
        ((Reg.inv g _ m2).pow S.N)).mul (Reg.inv J _ hi)
      refine ⟨W ⊓ ((g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP ⊓ J ⁻¹ᵁ P.basicOpen ((τ i).f k)),
        resG Y inf_le_left f, ⟨hW, hj, hi⟩, fun K _ h h1 h2 => ?_⟩
      obtain ⟨v, hv⟩ := hp K _ _ (he h) (ha h h2) (hk h h2)
      have n1 : ⊤ ≤ ((h ≫ g) ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP :=
        le_preimage_mono h (inf_le_right.trans inf_le_left) h1
      have n2 : ⊤ ≤ (h ≫ J) ⁻¹ᵁ P.basicOpen ((τ i).f k) := le_preimage_mono h (inf_le_right.trans inf_le_right) h1
      have n3 : (h ≫ g) ≫ Q.φ = (h ≫ J) ≫ ν := by rw [Category.assoc, g1, Category.assoc]
      have e := hv.2 i _ (h ≫ g) (h ≫ r) jP n3 (by rw [Category.assoc, g2, hβ, Category.assoc])
        (by rw [Category.assoc, g3, Category.assoc]) n1
      have z1 : valF (h ≫ J) _ ((τ i).f k) ≠ 0 := ((le_preimage_basicOpen_iff _ (hk h h2) _).1 n2).ne_zero
      have z2 := val_unit_ne (h ≫ g) (le_w Q n1 (n3 ▸ ha h h2)) (Q.w.s (fun _ => jP, fun _ => a))
      convert hv using 1
      refine (valR_res h _ h1 _).trans ((hf K h (le_preimage_mono h inf_le_left h1)).trans ?_)
      rw [zpow_natCast] at e
      have key : ∀ (A w t : K), w ≠ 0 → t ≠ 0 → A = w ^ S.N * (v * t) → A * (w⁻¹) ^ S.N * t⁻¹ = v := by
        rintro _ w t h1 h2 rfl
        rw [inv_pow]
        field_simp
      refine key _ _ _ z2 z1 (Eq.trans (Finset.sum_congr rfl fun l _ => ?_) e)
      rw [preimage_apply (h ≫ κ) (b i l)]
      rfl)
  exact ⟨(isUnit_of_val f fun K _ h hh => (hf K h hh).1).unit, hf⟩

end Ratio

end GlobalTheory.ZH.PowSec
