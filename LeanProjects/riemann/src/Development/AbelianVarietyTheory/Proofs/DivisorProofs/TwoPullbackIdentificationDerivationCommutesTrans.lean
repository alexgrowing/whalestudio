import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section

open GlobalTheory.KS.DlogPol (gs_pbT gs_sub)

namespace GlobalTheory.HeatConn.Comm

theorem gs_stalkMap' {X X' Z : Scheme.{0}} (r : Z ⟶ X') (β : X' ⟶ X) (z : Z) (U : X.Opens) (h : β (r z) ∈ U)
    (a : Γ(X, U)) : (r.stalkMap z).hom (gs β (r z) U a) = gs (r ≫ β) z U a := by
  rw [← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]
  exact Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem cst_spMap {V V' : Type} [CommRing V] [CommRing V'] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (ψ : V' →+* V) (z : Z)
    (a : V') : cst (q ≫ spMap ψ) z a = cst q z (ψ a) := by
  rw [cst, cst, ← gs_pull _ (spMap ψ) z ⊤ trivial]
  exact congrArg (gs q z ⊤) (congrArg (fun ψ' => ψ'.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))).symm

theorem stalkMap_eq_zero {k : Type} [Field k] {A₀ B' : Scheme.{0}} (q : B' ⟶ Sp (DualNumber k)) [Flat q]
    (sc : A₀ ⟶ B') (q₀ : A₀ ⟶ Sp k) (hsc : sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (y : A₀)
    {t : B'.presheaf.stalk (sc y)} (ht : cst q (sc y) DualNumber.eps * t = 0) : (sc.stalkMap y).hom t = 0 := by
  obtain ⟨u, rfl⟩ := GlobalTheory.cst_dvd_of_cst_mul_eq_zero q (sc y) (a := DualNumber.eps) (b := DualNumber.eps)
    (fun c hc => by
      have h1 : c.fst = 0 := by simpa using congrArg TrivSqZeroExt.snd hc
      exact ⟨TrivSqZeroExt.inl c.snd, by ext <;> simp [h1]⟩) ht
  rw [map_mul, cst, gs_stalkMap' sc q y ⊤ trivial, ← cst, hsc, cst_spMap]
  have e0 : (TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps = 0 := by simp
  rw [e0, cst, map_zero, gs_eq _ y ⊤ trivial, map_zero, map_zero, zero_mul]

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

theorem spMap_fst_alg (k : Type) [Field k] :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
  rw [← spMap_comp]
  have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
    ext; simp
  rw [this, spMap]
  exact Spec.map_id _

theorem exists_sec {k : Type} [Field k] {S A A₀ B' : Scheme.{0}} (p : A ⟶ S) (s : Sp k ⟶ S) (q₀ : A₀ ⟶ Sp k)
    (q : B' ⟶ Sp (DualNumber k)) (m₀ : A₀ ⟶ A) (π₁ π₂ : B' ⟶ A) (pr : B' ⟶ A₀)
    (h₀ : IsPullback m₀ q₀ p s) (h₂ : IsPullback π₂ q p (spMap (algebraMap k (DualNumber k)) ≫ s))
    (h₃ : ∀ (Z : Scheme.{0}) (x : Z ⟶ B') (y : Z ⟶ Sp k),
      x ≫ q = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂)
    (hpr₁ : pr ≫ m₀ = π₂) (hpr₂ : pr ≫ q₀ = q ≫ spMap (algebraMap k (DualNumber k))) :
    ∃ sc : A₀ ⟶ B', sc ≫ pr = 𝟙 _ ∧ sc ≫ π₂ = m₀ ∧
      sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ∧ ∀ x : B', π₁ x = π₂ x := by
  have e1 := spMap_fst_alg k
  have w : m₀ ≫ p = (q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
      spMap (algebraMap k (DualNumber k)) ≫ s := by
    rw [Category.assoc, reassoc_of% e1, h₀.w]
  let sc := h₂.lift m₀ _ w
  have hs₂ : sc ≫ π₂ = m₀ := h₂.lift_fst _ _ _
  have hsq : sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := h₂.lift_snd _ _ _
  have hspr : sc ≫ pr = 𝟙 _ := h₀.hom_ext (by rw [Category.assoc, hpr₁, hs₂, Category.id_comp])
    (by rw [Category.assoc, hpr₂, reassoc_of% hsq, e1, Category.comp_id, Category.id_comp])
  have hR : IsPullback pr q q₀ (spMap (algebraMap k (DualNumber k))) :=
    IsPullback.of_right (h₁₂ := m₀) (v₁₃ := p) (h₂₂ := s) (by rw [hpr₁]; exact h₂) hpr₂ h₀
  have hL : IsPullback sc q₀ q (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) :=
    IsPullback.of_right (h₁₂ := pr) (v₁₃ := q₀) (h₂₂ := spMap (algebraMap k (DualNumber k)))
      (by rw [hspr, e1]; exact IsPullback.id_horiz q₀) hsq hR
  have surj := (GlobalTheory.EpsIso.isHomeomorph_of_isPullback hL).2.surjective
  refine ⟨sc, hspr, hs₂, hsq, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := surj x
  have := congrArg (fun g : A₀ ⟶ A => g y) (h₃ _ sc q₀ hsq)
  simpa using this

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

open ReciprocityTheory.ChartRestriction.G.Out.PullGtPf in
theorem const_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B]
    {π : B.left ⟶ A.left} (h : IsGrpPullback B A f π) (c : 𝟙_ (Over S) ⟶ A) (c' : 𝟙_ (Over S') ⟶ B)
    (hc : c'.left ≫ π = f ≫ c.left) : (toUnit B ≫ c').left ≫ π = π ≫ (toUnit A ≫ c).left := by
  rw [Over.comp_left, Over.comp_left, toUnit_left', toUnit_left', Category.assoc, hc, ← Category.assoc,
    ← h.1.w, Category.assoc]

theorem trans_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B]
    {π : B.left ⟶ A.left} (h : IsGrpPullback B A f π) (c : 𝟙_ (Over S) ⟶ A) (c' : 𝟙_ (Over S') ⟶ B)
    (hc : c'.left ≫ π = f ≫ c.left) :
    (padd B (𝟙 B) (toUnit B ≫ c')).left ≫ π = π ≫ (padd A (𝟙 A) (toUnit A ≫ c)).left := by
  let x₀ : Over.mk (B.hom ≫ f) ⟶ A := Over.homMk π h.1.w
  have e := h.2 B (𝟙 B) (toUnit B ≫ c') x₀ (toUnit _ ≫ c) (by simp [x₀]) (by
    rw [Over.comp_left, Over.comp_left, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left',
      ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left', Category.assoc, hc]
    rfl)
  have e2 : x₀ * (toUnit _ ≫ c) = x₀ ≫ (𝟙 A * (toUnit A ≫ c)) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  change (𝟙 B * (toUnit B ≫ c')).left ≫ π = π ≫ (𝟙 A * (toUnit A ≫ c)).left
  rw [← e, e2]
  rfl

theorem exists_lift {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {k : Type} [Field k]
    (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left)
    (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)) (h₁ : IsGrpPullback B' Q.P.A (spMap ρ) π₁)
    (h₂ : IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂)
    (hc : ∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) (α : Q.X) (j : Fin 4) :
    ∃ φ' : B'.left ⟶ B'.left, φ' ≫ B'.hom = B'.hom ∧ φ' ≫ π₁ = π₁ ≫ Q.famφB α j ∧ φ' ≫ π₂ = π₂ ≫ Q.famφB α j := by
  have hcB : ∀ y, c' y ≫ B'.hom = (𝟙_ (Over (Sp (DualNumber k)))).hom := fun y => (hc y).1
  let cB : Q.X → (𝟙_ (Over (Sp (DualNumber k))) ⟶ B') := fun y => Over.homMk (c' y) (hcB y)
  have h1 : ∀ y, (cB y).left ≫ π₁ = spMap ρ ≫ (Q.c y).left := fun y => (hc y).2.1
  have h2 : ∀ y, (cB y).left ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left := fun y => (hc y).2.2
  fin_cases j
  · exact ⟨𝟙 _, Category.id_comp _, (Category.id_comp _).trans (Category.comp_id _).symm,
      (Category.id_comp _).trans (Category.comp_id _).symm⟩
  · exact ⟨(padd B' (𝟙 B') (toUnit B' ≫ cB α)).left, Over.w _, trans_comm h₁ _ _ (h1 α),
      trans_comm h₂ _ _ (h2 α)⟩
  · exact ⟨(toUnit B' ≫ cB α).left, Over.w _, const_comm h₁ _ _ (h1 α), const_comm h₂ _ _ (h2 α)⟩
  · exact ⟨(toUnit B' ≫ η[B']).left, Over.w _,
      const_comm h₁ _ _ (ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h₁),
      const_comm h₂ _ _ (ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h₂)⟩

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

theorem commutes : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {k : Type} [Field k] (ρ : R →+* DualNumber k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsGrpPullback A₀ Q.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → (∀ (W : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → Commutes Q m₀ ed := by
  intro R _ _ Q k _ ρ A₀ _ m₀ hA₀ ed B' _ π₁ π₂ c' h₁ h₂ h₃ hc pr hpr₁ hpr₂ hD α j T hT₁ hT₂ W f Z b z hz
  have hfA : Flat Q.P.A.hom := by
    have := Q.P.smoothDim
    have : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
    infer_instance
  have hfB : Flat B'.hom := MorphismProperty.of_isPullback h₁.1 hfA
  obtain ⟨φ', hφ'0, hφ'1, hφ'2⟩ := exists_lift Q ρ B' π₁ π₂ c' h₁ h₂ hc α j
  have e2 : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫
      spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := spMap_comp _ _
  obtain ⟨sc, hspr, hs₂, hsq, hpts⟩ := exists_sec Q.P.A.hom _ A₀.hom B'.hom m₀ π₁ π₂ pr hA₀.1
    (e2 ▸ h₂.1) h₃ hpr₁ hpr₂
  have hpre : ∀ U : Q.P.A.left.Opens, π₂ ⁻¹ᵁ U ≤ π₁ ⁻¹ᵁ U := fun U x hx => by
    change π₁ x ∈ U
    rw [hpts x]
    exact hx
  have hprle : ∀ U : Q.P.A.left.Opens, π₂ ⁻¹ᵁ U ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ U) := fun U x hx => by
    change m₀ (pr x) ∈ U
    have : (pr ≫ m₀) x ∈ U := by rw [hpr₁]; exact hx
    simpa using this
  have hφpr : φ' ≫ pr = pr ≫ T := hA₀.1.hom_ext
    (by rw [Category.assoc, Category.assoc, hpr₁, hφ'2, hT₁, ← Category.assoc, hpr₁])
    (by rw [Category.assoc, Category.assoc, hpr₂, ← Category.assoc, hφ'0, hT₂, hpr₂])
  set φ := Q.famφB α j with hφdef
  have key : ∀ y : A₀.left, (T ≫ m₀) y ∈ W →
      gs (𝟙 _) y (m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W)) (ed _ ((φ.app W).hom f)) = gs T y (m₀ ⁻¹ᵁ W) (ed W f) := by
    intro y hy
    have hy' : φ (m₀ y) ∈ W := by
      have h := hy
      rw [hT₁] at h
      all_goals simpa using h
    have m₂ : sc y ∈ π₂ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
      change φ (π₂ (sc y)) ∈ W
      have : (sc ≫ π₂) y = m₀ y := by rw [hs₂]
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact hy'
    have m₃ : φ' (sc y) ∈ π₂ ⁻¹ᵁ W := by
      change π₂ (φ' (sc y)) ∈ W
      have : (φ' ≫ π₂) (sc y) = φ (π₂ (sc y)) := by rw [hφ'2]; simp
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact m₂
    have eA := congrArg (gs (𝟙 B'.left) (sc y) (π₂ ⁻¹ᵁ (φ ⁻¹ᵁ W))) (hD (φ ⁻¹ᵁ W) ((φ.app W).hom f))
    rw [gs_add (𝟙 _) (sc y) _ m₂, gs_mul (𝟙 _) (sc y) _ m₂, gs_pbT (𝟙 _) π₁ (sc y) (hpre _) m₂,
      gs_pbT (𝟙 _) π₂ (sc y) le_rfl m₂, gs_pbT (𝟙 _) pr (sc y) (hprle _) m₂, gs_constFn B'.hom _ (𝟙 _) (sc y) m₂] at eA
    have eB := congrArg (gs φ' (sc y) (π₂ ⁻¹ᵁ W)) (hD W f)
    rw [gs_add φ' (sc y) _ m₃, gs_mul φ' (sc y) _ m₃, gs_pbT φ' π₁ (sc y) (hpre _) m₃,
      gs_pbT φ' π₂ (sc y) le_rfl m₃, gs_pbT φ' pr (sc y) (hprle _) m₃, gs_constFn B'.hom _ φ' (sc y) m₃, hφ'1, hφ'2, hφ'0, hφpr] at eB
    simp only [Category.id_comp] at eA
    have m₁' : φ (π₁ (sc y)) ∈ W := by rw [hpts]; exact m₂
    rw [← gs_pull π₁ φ (sc y) W m₁', ← gs_pull π₂ φ (sc y) W m₂] at eB
    have hk : cst B'.hom (sc y) DualNumber.eps * (gs pr (sc y) (m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W)) (ed _ ((φ.app W).hom f)) -
        gs (pr ≫ T) (sc y) (m₀ ⁻¹ᵁ W) (ed W f)) = 0 := by
      linear_combination eB - eA
    have h0 := stalkMap_eq_zero B'.hom sc A₀.hom hsq y hk
    have hy0 : pr (sc y) = y := by
      have := congrArg (fun g : A₀.left ⟶ A₀.left => g y) hspr
      simpa using this
    have ma : pr (sc y) ∈ m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
      change φ (m₀ (pr (sc y))) ∈ W
      rw [hy0]; exact hy'
    have mb : (pr ≫ T) (sc y) ∈ m₀ ⁻¹ᵁ W := by
      change m₀ ((pr ≫ T) (sc y)) ∈ W
      simp only [Scheme.Hom.comp_apply]
      rw [hy0]; simpa using hy
    rw [map_sub, gs_stalkMap' sc pr y _ ma, gs_stalkMap' sc (pr ≫ T) y _ mb, hspr, reassoc_of% hspr] at h0
    exact sub_eq_zero.1 h0
  have hyz : (T ≫ m₀) (b z) ∈ W := by simpa using hz
  have mz1 : b z ∈ m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
    change φ (m₀ (b z)) ∈ W
    have h := hyz
    rw [hT₁] at h
    all_goals simpa using h
  have mz2 : T (b z) ∈ m₀ ⁻¹ᵁ W := by
    change m₀ (T (b z)) ∈ W
    simpa using hyz
  rw [gs_stalkMap b z _ mz1, key (b z) hyz, gs_stalkMap' b T z _ mz2]

end GlobalTheory.HeatConn.Comm
