import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.SqZero

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

section Der

variable {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

def addDer (φ : B →ₐ[R] A) (D : B →ₗ[R] A) (hD : ∀ b b', D (b * b') = φ b * D b' + φ b' * D b)
    (h0 : ∀ b b', D b * D b' = 0) : B →ₐ[R] A :=
  AlgHom.ofLinearMap (φ.toLinearMap + D)
    (by
      have := hD 1 1
      simp only [mul_one, map_one, one_mul, left_eq_add] at this
      simp [this])
    (fun b b' => by
      simp only [LinearMap.add_apply, AlgHom.toLinearMap_apply, map_mul, hD]
      linear_combination - h0 b b')

theorem addDer_apply (φ : B →ₐ[R] A) (D : B →ₗ[R] A) (hD) (h0) (b : B) :
    addDer φ D hD h0 b = φ b + D b := rfl

def addDers {κ : Type} [Fintype κ] (τ : κ → Derivation R B B) (φ : B →ₐ[R] A) (t : κ → A)
    (ht : ∀ i j, t i * t j = 0) : B →ₐ[R] A :=
  addDer φ
    { toFun := fun b => ∑ i, φ (τ i b) * t i
      map_add' := fun b b' => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r b => by simp [Finset.smul_sum] }
    (fun b b' => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun b b' => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul_sum]
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        rw [mul_mul_mul_comm, ht, mul_zero])

theorem addDers_apply {κ : Type} [Fintype κ] (τ : κ → Derivation R B B) (φ : B →ₐ[R] A)
    (t : κ → A) (ht : ∀ i j, t i * t j = 0) (b : B) :
    addDers τ φ t ht b = φ b + ∑ i, φ (τ i b) * t i := rfl

variable (R B) in

theorem exists_ders [Algebra.Smooth R B] :
    ∃ (κ : Type) (_ : Fintype κ) (β : κ → B) (τ : κ → Derivation R B B),
      ∀ (A : Type) [CommRing A] [Algebra R A] (φ φ' : B →ₐ[R] A),
        (∀ b b', (φ b - φ' b) * (φ b' - φ' b') = 0) →
        ∀ b, φ b - φ' b = ∑ i, φ' (τ i b) * (φ (β i) - φ' (β i)) := by
  have hfg : (Submodule.span B (Set.range (KaehlerDifferential.D R B))).FG := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Module.Finite.fg_top
  obtain ⟨s', hsub, hs'⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hex : ∀ x : s', ∃ b, KaehlerDifferential.D R B b = x := fun x => hsub x.2
  choose β hβ using hex
  have hspan : Submodule.span B (Set.range fun x : s' => KaehlerDifferential.D R B (β x)) = ⊤ := by
    rw [show (Set.range fun x : s' => KaehlerDifferential.D R B (β x)) = ↑s' by
      ext ω
      simp [hβ]]
    rw [← hs', KaehlerDifferential.span_range_derivation]
  have hsurj : Function.Surjective
      (Fintype.linearCombination B (fun x : s' => KaehlerDifferential.D R B (β x))) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  obtain ⟨h, hh⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
  let τ : s' → Derivation R B B := fun x => (LinearMap.proj x ∘ₗ h).compDer (KaehlerDifferential.D R B)
  have hD : ∀ b, KaehlerDifferential.D R B b =
      ∑ x, τ x b • KaehlerDifferential.D R B (β x) := fun b => by
    conv_lhs => rw [← LinearMap.id_apply (R := B) (KaehlerDifferential.D R B b), ← hh]
    simp [τ, Fintype.linearCombination_apply]
  refine ⟨s', inferInstance, β, τ, fun A _ _ φ φ' hprod b => ?_⟩
  let _ : Algebra B A := φ'.toRingHom.toAlgebra
  have : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq fun r => (φ'.commutes r).symm
  let δ : Derivation R B A :=
    { toFun := fun b => φ b - φ' b
      map_add' := fun b b' => by simp only [map_add]; ring
      map_smul' := fun r b => by simp [smul_sub]
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        show φ (a * b) - φ' (a * b) = φ' a * (φ b - φ' b) + φ' b * (φ a - φ' a)
        rw [map_mul, map_mul]
        linear_combination hprod a b }
  have key := congrArg δ.liftKaehlerDifferential (hD b)
  simp only [map_sum, map_smul, Derivation.liftKaehlerDifferential_comp_D] at key
  exact key

end Der

section Dual

variable {S S' S'' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S'']

abbrev fstS (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S] :
    DualNumber S →ₐ[R] S := TrivSqZeroExt.fstHom R S S

abbrev inlS (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S] :
    S →ₐ[R] DualNumber S := TrivSqZeroExt.inlAlgHom R S S

def dualMap (ρ : S →ₐ[R] S') : DualNumber S →ₐ[R] DualNumber S' :=
  dualTo ((inlS R S').comp ρ) (inr 1) (TrivSqZeroExt.inr_mul_inr _ _ _)

def dualScale (R : Type) [CommRing R] {S : Type} [CommRing S] [Algebra R S] (s : S) :
    DualNumber S →ₐ[R] DualNumber S :=
  dualTo (inlS R S) (inr s) (TrivSqZeroExt.inr_mul_inr _ _ _)

@[simp] theorem fst_dualMap (ρ : S →ₐ[R] S') (a : DualNumber S) :
    (dualMap ρ a).fst = ρ a.fst := by
  simp [dualMap, dualTo_apply]

@[simp] theorem snd_dualMap (ρ : S →ₐ[R] S') (a : DualNumber S) :
    (dualMap ρ a).snd = ρ a.snd := by
  simp [dualMap, dualTo_apply]

@[simp] theorem fst_dualScale (s : S) (a : DualNumber S) : (dualScale R s a).fst = a.fst := by
  simp [dualScale, dualTo_apply]

@[simp] theorem snd_dualScale (s : S) (a : DualNumber S) : (dualScale R s a).snd = a.snd * s := by
  simp [dualScale, dualTo_apply, mul_comm]

theorem dualMap_inr (ρ : S →ₐ[R] S') (a : S) : dualMap ρ (inr a) = inr (ρ a) := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp

theorem dualScale_inr (s a : S) : dualScale R s (inr a) = inr (a * s) := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp

theorem dualMap_comp (ρ : S →ₐ[R] S') (ρ' : S' →ₐ[R] S'') :
    (dualMap ρ').comp (dualMap ρ) = dualMap (ρ'.comp ρ) := AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp)

theorem dualScale_comp (s t : S) :
    (dualScale R s).comp (dualScale R t) = dualScale R (s * t) := AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp only [AlgHom.comp_apply, snd_dualScale]; ring)

theorem dualScale_one : dualScale R (1 : S) = AlgHom.id R _ := AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp)

theorem dualMap_comp_dualScale (ρ : S →ₐ[R] S') (s : S) :
    (dualMap ρ).comp (dualScale R s) = (dualScale R (ρ s)).comp (dualMap ρ) := AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp)

theorem fstS_comp_dualMap (ρ : S →ₐ[R] S') :
    (fstS R S').comp (dualMap ρ) = ρ.comp (fstS R S) := AlgHom.ext fun a => by simp [fstS]

theorem fstS_comp_dualScale (s : S) : (fstS R S).comp (dualScale R s) = fstS R S := AlgHom.ext fun a => by simp [fstS]

theorem IsAway.dualMap {ρ : S →ₐ[R] S'} {g : S} (h : IsAway ρ g) :
    IsAway (dualMap ρ) (inlS R S g) := by
  have hi : ∀ x : S, GlobalTheory.SqZero.dualMap ρ (inlS R S x) = inlS R S' (ρ x) := fun x =>
    TrivSqZeroExt.ext (by simp) (by simp)
  rw [isAway_iff, hi]
  refine ⟨h.unit.map (inlS R S'), fun z => ?_, fun a ha => ?_⟩
  · obtain ⟨N, a, ha⟩ := h.surj_fin ![z.fst, z.snd]
    have h0 := ha 0
    have h1 := ha 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨N, inlS R S (a 0) + inr (a 1), ?_⟩
    rw [← map_pow]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [h0]
    · simp [h1, mul_comm]
  · have e0 : ρ a.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst ha
    have e1 : ρ a.snd = 0 := by simpa using congrArg TrivSqZeroExt.snd ha
    obtain ⟨N, hN⟩ := h.ker_fin (a := ![a.fst, a.snd]) (fun i => by fin_cases i <;> simp [e0, e1])
    have h0 := hN 0
    have h1 := hN 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨N, ?_⟩
    rw [← map_pow]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [h0]
    · simp [h1]

theorem fstS_surjective : Function.Surjective (fstS R S) := fun s => ⟨inl s, by simp⟩

theorem nil_of_fstS (a : DualNumber S) (ha : fstS R S a = 0) : IsNilpotent a := by
  have h0 : a.fst = 0 := by simpa using ha
  refine ⟨2, TrivSqZeroExt.ext ?_ ?_⟩ <;> simp [pow_two, h0]

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

def IsTanOver (w : sp (R₀ := R) (DualNumber S) ⟶ G) : Prop := spMap (fstS R S) ≫ w = 1

abbrev res (ρ : S →ₐ[R] S') (w : sp (R₀ := R) (DualNumber S) ⟶ G) :
    sp (R₀ := R) (DualNumber S') ⟶ G := spMap (dualMap ρ) ≫ w

abbrev scl (s : S) (w : sp (R₀ := R) (DualNumber S) ⟶ G) :
    sp (R₀ := R) (DualNumber S) ⟶ G := spMap (dualScale R s) ≫ w

omit [GrpObj G] in
theorem res_res (ρ : S →ₐ[R] S') (ρ' : S' →ₐ[R] S'') (w : sp (R₀ := R) (DualNumber S) ⟶ G) :
    res ρ' (res ρ w) = res (ρ'.comp ρ) w := by
  dsimp only [res]
  rw [← Category.assoc, spMap_comp, dualMap_comp]

omit [GrpObj G] in
theorem scl_scl (s t : S) (w : sp (R₀ := R) (DualNumber S) ⟶ G) :
    scl s (scl t w) = scl (s * t) w := by
  dsimp only [scl]
  rw [← Category.assoc, spMap_comp, dualScale_comp]

omit [GrpObj G] in
theorem scl_one (w : sp (R₀ := R) (DualNumber S) ⟶ G) : scl (1 : S) w = w := by
  dsimp only [scl]
  rw [dualScale_one, spMap_id, Category.id_comp]

omit [GrpObj G] in
theorem res_scl (ρ : S →ₐ[R] S') (s : S) (w : sp (R₀ := R) (DualNumber S) ⟶ G) :
    res ρ (scl s w) = scl (ρ s) (res ρ w) := by
  dsimp only [res, scl]
  rw [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, dualMap_comp_dualScale]

theorem IsTanOver.res {w : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) (ρ : S →ₐ[R] S') :
    IsTanOver (res ρ w) := by
  unfold IsTanOver at hw ⊢
  dsimp only [GlobalTheory.SqZero.res]
  rw [← Category.assoc, spMap_comp, fstS_comp_dualMap, ← spMap_comp, Category.assoc, hw, comp_one']

theorem IsTanOver.scl {w : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) (s : S) :
    IsTanOver (scl s w) := by
  unfold IsTanOver at hw ⊢
  dsimp only [GlobalTheory.SqZero.scl]
  rw [← Category.assoc, spMap_comp, fstS_comp_dualScale, hw]

theorem exists_chart_of_isTanOver {B : Type} [CommRing B] [Algebra R B] (j : sp B ⟶ G)
    [IsOpenImmersion j.left] (u : B →ₐ[R] S) (hu : spMap u ≫ j = 1)
    {w : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) :
    ∃ φ : B →ₐ[R] DualNumber S, w = spMap φ ≫ j ∧ ∀ b, (φ b).fst = u b := by
  obtain ⟨φ, h1, h2⟩ := exists_chart_pt_of_nil j (fstS R S) fstS_surjective nil_of_fstS w u
    (by rw [hu]; exact hw)
  exact ⟨φ, h1, fun b => by simpa using congrArg (fun f => f b) h2⟩

theorem snd_eq_sum {B κ : Type} [CommRing B] [Algebra R B] [Fintype κ] {β : κ → B}
    {τ : κ → Derivation R B B}
    (hτ : ∀ (A : Type) [CommRing A] [Algebra R A] (φ φ' : B →ₐ[R] A),
        (∀ b b', (φ b - φ' b) * (φ b' - φ' b') = 0) →
        ∀ b, φ b - φ' b = ∑ i, φ' (τ i b) * (φ (β i) - φ' (β i)))
    (u : B →ₐ[R] S) (φ : B →ₐ[R] DualNumber S) (hφ : ∀ b, (φ b).fst = u b) (b : B) :
    (φ b).snd = ∑ i, u (τ i b) * (φ (β i)).snd := by
  have hd : ∀ b, φ b - ((inlS R S).comp u) b = inr (φ b).snd := fun b =>
    TrivSqZeroExt.ext (by simp [hφ]) (by simp)
  have key := hτ (DualNumber S) φ ((inlS R S).comp u)
    (fun b b' => by rw [hd, hd]; exact TrivSqZeroExt.inr_mul_inr _ _ _) b
  simp_rw [hd] at key
  simpa [TrivSqZeroExt.snd_sum, mul_comm] using congrArg TrivSqZeroExt.snd key

variable [Smooth G.hom] {ρ : S →ₐ[R] S'} {g : S}

theorem exists_scl_eq_of_unitInChart (hS : UnitInChart G S) (hρ : IsAway ρ g)
    {w w' : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) (hw' : IsTanOver w')
    (h : res ρ w = res ρ w') : ∃ N : ℕ, scl (g ^ N) w = scl (g ^ N) w' := by
  obtain ⟨B, _, _, j, u, hj, hu⟩ := hS
  have := smooth_of_chart j
  obtain ⟨κ, _, β, τ, hτ⟩ := exists_ders R B
  obtain ⟨φ, rfl, hφ⟩ := exists_chart_of_isTanOver j u hu hw
  obtain ⟨φ', rfl, hφ'⟩ := exists_chart_of_isTanOver j u hu hw'
  have e : (dualMap ρ).comp φ = (dualMap ρ).comp φ' := by
    apply chart_inj j
    have h' := h
    dsimp only [res] at h'
    rwa [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp] at h'
  have hz : ∀ i, ρ ((φ (β i)).snd - (φ' (β i)).snd) = 0 := fun i => by
    have := congrArg (fun f => (f (β i)).snd) e
    simpa [sub_eq_zero] using this
  obtain ⟨N, hN⟩ := hρ.ker_fin hz
  refine ⟨N, ?_⟩
  have e2 : (dualScale R (g ^ N)).comp φ = (dualScale R (g ^ N)).comp φ' := by
    refine AlgHom.ext fun b => TrivSqZeroExt.ext (by simp [hφ, hφ']) ?_
    have s1 := snd_eq_sum hτ u φ hφ b
    have s2 := snd_eq_sum hτ u φ' hφ' b
    simp only [AlgHom.comp_apply, snd_dualScale]
    rw [← sub_eq_zero, ← sub_mul, s1, s2, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← mul_sub, mul_assoc, mul_comm _ (g ^ N), hN i, mul_zero]
  dsimp only [scl]
  rw [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, e2]

theorem exists_res_eq_of_unitInChart (hS : UnitInChart G S) (hρ : IsAway ρ g)
    {w' : sp (R₀ := R) (DualNumber S') ⟶ G} (hw' : IsTanOver w') :
    ∃ (N : ℕ) (w : sp (R₀ := R) (DualNumber S) ⟶ G), IsTanOver w ∧
      res ρ w = scl (ρ g ^ N) w' := by
  obtain ⟨B, _, _, j, u, hj, hu⟩ := hS
  have := smooth_of_chart j
  obtain ⟨κ, _, β, τ, hτ⟩ := exists_ders R B
  have hu' : spMap (ρ.comp u) ≫ j = 1 := by rw [← spMap_comp, Category.assoc, hu, comp_one']
  obtain ⟨φ', rfl, hφ'⟩ := exists_chart_of_isTanOver j (ρ.comp u) hu' hw'
  obtain ⟨N, a, ha⟩ := hρ.surj_fin (fun i => (φ' (β i)).snd)
  let ψ := addDers τ ((inlS R S).comp u) (fun i => (inr (a i) : DualNumber S))
    (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have hψ : (fstS R S).comp ψ = u := AlgHom.ext fun b => by simp [ψ, addDers_apply, TrivSqZeroExt.fst_sum]
  refine ⟨N, spMap ψ ≫ j, ?_, ?_⟩
  · show spMap (fstS R S) ≫ spMap ψ ≫ j = 1
    rw [← Category.assoc, spMap_comp, hψ, hu]
  · have e : (dualMap ρ).comp ψ = (dualScale R (ρ g ^ N)).comp φ' := by
      refine AlgHom.ext fun b => TrivSqZeroExt.ext ?_ ?_
      · simp [ψ, addDers_apply, hφ', TrivSqZeroExt.fst_sum]
      · have s := snd_eq_sum hτ (ρ.comp u) φ' hφ' b
        simp only [AlgHom.comp_apply, snd_dualScale, snd_dualMap, ψ, addDers_apply]
        rw [s, Finset.sum_mul]
        simp [TrivSqZeroExt.snd_sum, map_sum, mul_assoc, ha]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    dsimp only [res, scl]
    rw [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, e]

omit [Smooth G.hom] [GrpObj G] in
theorem scl_pow_eq_of_le {w w' : sp (R₀ := R) (DualNumber S) ⟶ G} {N M : ℕ} (hNM : N ≤ M)
    (h : scl (g ^ N) w = scl (g ^ N) w') : scl (g ^ M) w = scl (g ^ M) w' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  rw [pow_add, mul_comm, ← scl_scl, h, scl_scl]

omit [Smooth G.hom] [GrpObj G] in
theorem dual_ext {κ : Type} {s : κ → S} (hs : Ideal.span (Set.range s) = ⊤) {B : κ → Type}
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (q : ∀ i, S →ₐ[R] B i)
    (hq : ∀ i, IsAway (q i) (s i)) {w w' : sp (R₀ := R) (DualNumber S) ⟶ G}
    (h : ∀ i, res (q i) w = res (q i) w') : w = w' := away_ext (span_range_map hs (inlS R S)) (fun i => dualMap (q i)) (fun i => (hq i).dualMap)
    fun i => h i

theorem exists_scl_eq (hρ : IsAway ρ g)
    {w w' : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) (hw' : IsTanOver w')
    (h : res ρ w = res ρ w') : ∃ N : ℕ, scl (g ^ N) w = scl (g ^ N) w' := by
  obtain ⟨κ, _, s, hs, hU⟩ := exists_fin_unitInChart G S
  have key : ∀ k, ∃ N : ℕ,
      res (awayHom R (s k)) (scl (g ^ N) w) = res (awayHom R (s k)) (scl (g ^ N) w') := by
    intro k
    obtain ⟨ψ, hψ⟩ := hρ.lift ((awayHom R (awayHom R (s k) g)).comp (awayHom R (s k)))
      (isAway_awayHom (R := R) (awayHom R (s k) g)).unit
    obtain ⟨N, hN⟩ := exists_scl_eq_of_unitInChart (hU k) (isAway_awayHom (awayHom R (s k) g))
      (hw.res _) (hw'.res _) (by rw [res_res, res_res, ← hψ, ← res_res, ← res_res, h])
    exact ⟨N, by rw [res_scl, res_scl, map_pow]; exact hN⟩
  choose N hN using key
  have := Fintype.ofFinite κ
  refine ⟨Finset.univ.sup N, dual_ext hs (fun k => awayHom R (s k)) (fun k => isAway_awayHom (s k))
    fun k => ?_⟩
  have h1 := hN k
  rw [res_scl, res_scl, map_pow] at h1 ⊢
  exact scl_pow_eq_of_le (Finset.le_sup (Finset.mem_univ k)) h1

theorem exists_res_eq (hρ : IsAway ρ g)
    {w' : sp (R₀ := R) (DualNumber S') ⟶ G} (hw' : IsTanOver w') :
    ∃ (N : ℕ) (w : sp (R₀ := R) (DualNumber S) ⟶ G), IsTanOver w ∧
      res ρ w = scl (ρ g ^ N) w' := by
  obtain ⟨κ, _, s, hs, hU⟩ := exists_fin_unitInChart G S
  have := Fintype.ofFinite κ
  let q : ∀ k, S →ₐ[R] Localization.Away (s k) := fun k => awayHom R (s k)
  have hq : ∀ k, IsAway (q k) (s k) := fun k => isAway_awayHom (s k)
  let p : ∀ k, Localization.Away (s k) →ₐ[R] Localization.Away (q k g) := fun k => awayHom R (q k g)
  have hp : ∀ k, IsAway (p k) (q k g) := fun k => isAway_awayHom (q k g)
  have hψ0 : ∀ k, ∃ ψ : S' →ₐ[R] Localization.Away (q k g), ψ.comp ρ = (p k).comp (q k) :=
    fun k => hρ.lift _ (hp k).unit
  choose ψ hψ using hψ0
  have hψa : ∀ k, IsAway (ψ k) (ρ (s k)) := fun k => hρ.swap (hq k) (hψ k) (hp k)
  have hgk : ∀ k, ψ k (ρ g) = p k (q k g) := fun k => by
    rw [← AlgHom.comp_apply, hψ k, AlgHom.comp_apply]
  have hk : ∀ k, ∃ (N : ℕ) (v : sp (R₀ := R) (DualNumber (Localization.Away (s k))) ⟶ G),
      IsTanOver v ∧ res (p k) v = scl (p k (q k g) ^ N) (res (ψ k) w') :=
    fun k => exists_res_eq_of_unitInChart (hU k) (hp k) (hw'.res (ψ k))
  choose N v hv hvN using hk
  obtain ⟨M, hM⟩ : ∃ M, ∀ k, N k ≤ M := ⟨Finset.univ.sup N, fun k => Finset.le_sup (Finset.mem_univ k)⟩
  let W' := scl (ρ g ^ M) w'
  let v1 : ∀ k, sp (R₀ := R) (DualNumber (Localization.Away (s k))) ⟶ G :=
    fun k => scl (q k g ^ (M - N k)) (v k)
  have H1 : ∀ k, res (p k) (v1 k) = res (ψ k) W' := fun k => by
    simp only [v1, W']
    rw [res_scl, hvN k, scl_scl, res_scl, map_pow, map_pow, hgk, ← pow_add,
      Nat.sub_add_cancel (hM k)]
  let q2 : ∀ k l, S →ₐ[R] Localization.Away (s k * s l) := fun k l => awayHom R (s k * s l)
  have hq2 : ∀ k l, IsAway (q2 k l) (s k * s l) := fun k l => isAway_awayHom _
  have hja0 : ∀ k l, ∃ ja : Localization.Away (s k) →ₐ[R] Localization.Away (s k * s l),
      ja.comp (q k) = q2 k l := fun k l => (hq k).lift _
    (isUnit_of_mul_isUnit_left (y := q2 k l (s l)) (by rw [← map_mul]; exact (hq2 k l).unit))
  have hjb0 : ∀ k l, ∃ ja : Localization.Away (s l) →ₐ[R] Localization.Away (s k * s l),
      ja.comp (q l) = q2 k l := fun k l => (hq l).lift _
    (isUnit_of_mul_isUnit_right (x := q2 k l (s k)) (by rw [← map_mul]; exact (hq2 k l).unit))
  choose ja hja using hja0
  choose jb hjb using hjb0
  have hP : ∀ k l, ∃ P : ℕ,
      scl (q2 k l g ^ P) (res (ja k l) (v1 k)) = scl (q2 k l g ^ P) (res (jb k l) (v1 l)) := by
    intro k l
    have hp2 := isAway_awayHom (R := R) (q2 k l g)
    obtain ⟨χ, hχ⟩ := (hp k).lift ((awayHom R (q2 k l g)).comp (ja k l)) (by
      rw [AlgHom.comp_apply, ← AlgHom.comp_apply (ja k l), hja]
      exact hp2.unit)
    obtain ⟨χ', hχ'⟩ := (hp l).lift ((awayHom R (q2 k l g)).comp (jb k l)) (by
      rw [AlgHom.comp_apply, ← AlgHom.comp_apply (jb k l), hjb]
      exact hp2.unit)
    have e : χ.comp (ψ k) = χ'.comp (ψ l) := hρ.ext (by
      rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hψ, hψ, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
        hχ, hχ', AlgHom.comp_assoc, AlgHom.comp_assoc, hja, hjb])
    refine exists_scl_eq hp2 (((hv k).scl _).res _) (((hv l).scl _).res _) ?_
    rw [res_res, res_res, ← hχ, ← hχ', ← res_res, ← res_res, H1, H1, res_res, res_res, e]
  choose Q hQ using hP
  obtain ⟨P, hPQ⟩ : ∃ P, ∀ k l, Q k l ≤ P :=
    ⟨Finset.univ.sup fun k => Finset.univ.sup (Q k), fun k l =>
      (Finset.le_sup (f := Q k) (Finset.mem_univ l)).trans
        (Finset.le_sup (f := fun k => Finset.univ.sup (Q k)) (Finset.mem_univ k))⟩
  let v2 : ∀ k, sp (R₀ := R) (DualNumber (Localization.Away (s k))) ⟶ G :=
    fun k => scl (q k g ^ P) (v1 k)
  have H2 : ∀ k l, res (ja k l) (v2 k) = res (jb k l) (v2 l) := fun k l => by
    show res (ja k l) (scl (q k g ^ P) (v1 k)) = res (jb k l) (scl (q l g ^ P) (v1 l))
    rw [res_scl (ja k l) (q k g ^ P) (v1 k), res_scl (jb k l) (q l g ^ P) (v1 l), map_pow, map_pow, ← AlgHom.comp_apply (ja k l), hja,
      ← AlgHom.comp_apply (jb k l), hjb]
    exact scl_pow_eq_of_le (hPQ k l) (hQ k l)
  obtain ⟨z, hz⟩ := away_glue (X := G) (span_range_map hs (inlS R S)) (fun k => dualMap (q k))
    (fun k => (hq k).dualMap) v2 (fun k l T _ _ a b e =>
      agree_of_isAway ((hq k).dualMap) ((hq l).dualMap) (a₀ := dualMap (ja k l))
        (b₀ := dualMap (jb k l)) (by rw [dualMap_comp, dualMap_comp, hja, hjb])
        (by rw [dualMap_comp, hja, ← map_mul]; exact (hq2 k l).dualMap) (H2 k l) T a b e)
  refine ⟨M + P, z, ?_, ?_⟩
  · show spMap (fstS R S) ≫ z = 1
    refine away_ext hs q hq fun k => ?_
    rw [comp_one', ← Category.assoc, spMap_comp, ← fstS_comp_dualMap, ← spMap_comp, Category.assoc,
      hz k]
    exact ((hv k).scl _).scl _
  · refine dual_ext (span_range_map hs ρ) ψ hψa fun k => ?_
    rw [res_res, hψ k, ← res_res]
    show res (p k) (spMap (dualMap (q k)) ≫ z) = _
    rw [hz k]
    show res (p k) (scl (q k g ^ P) (v1 k)) = _
    rw [res_scl (p k) (q k g ^ P) (v1 k), H1 k]
    simp only [W']
    rw [res_scl, res_scl, scl_scl]
    simp only [map_pow, hgk]
    rw [← pow_add, add_comm]

end Dual

end GlobalTheory.SqZero
