import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists

theorem mem_span_basis_iff {J A C X : Type} [Fintype J] [CommRing A] [Field C] [Algebra A C]
    [AddCommGroup X] [Module C X] [Module A X] [IsScalarTower A C X] (F : Module.Basis J C X) (y : X) :
    y ∈ Submodule.span A (Set.range F) ↔ ∀ j, F.repr y j ∈ (algebraMap A C).range := by
  classical
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      intro j
      rw [F.repr_self, Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => intro j; simp
    | add x z _ _ hx hz => intro j; simpa using add_mem (hx j) (hz j)
    | smul a x _ hx =>
      intro j
      rw [← algebraMap_smul C a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem ⟨a, rfl⟩ (hx j)
  · intro h
    rw [← F.sum_repr y]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨a, ha⟩ := h j
    rw [← ha, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_transport {E : Type} [Field E] [NumberField E] {Ω W J C X : Type} [Field Ω] [AddCommGroup W]
    [Module Ω W] [Fintype J] [DecidableEq J] (B : Module.Basis J Ω W) (ρ : 𝓞 E →+* Module.End Ω W)
    (R : Subring Ω) (L : Submodule R W) (hL : L = Submodule.span R (Set.range B))
    (hst : ∀ a, ∀ h ∈ L, ρ a h ∈ L) [Field C] [AddCommGroup X] [Module C X]
    (F : Module.Basis J C X) (ψ : R →+* C) :
    ∃ (ρX : 𝓞 E →+* Module.End C X) (ev : L →ₛₗ[ψ] X),
      (∀ (h : L) (i : J) (r : R), B.repr (h : W) i = r → F.repr (ev h) i = ψ r) ∧
      (∀ (j : J) (hj : B j ∈ L), ev ⟨B j, hj⟩ = F j) ∧
      (∀ (a : 𝓞 E) (h : L) (h' : ρ a (h : W) ∈ L), ev ⟨_, h'⟩ = ρX a (ev h)) := by
  have hc : ∀ h ∈ L, ∀ i, B.repr h i ∈ R := by
    intro h hh i
    rw [hL, mem_span_basis_iff (A := R) B h] at hh
    obtain ⟨r, hr⟩ := hh i
    rw [← hr]
    exact r.2
  have hB : ∀ j, B j ∈ L := fun j => hL ▸ Submodule.subset_span ⟨j, rfl⟩
  let cd : L → J → R := fun h i => ⟨B.repr (h : W) i, hc _ h.2 i⟩
  let m : 𝓞 E → Matrix J J R := fun a i j => cd ⟨ρ a (B j), hst a _ (hB j)⟩ i
  have hm : ∀ a, R.subtype.mapMatrix (m a) = LinearMap.toMatrixAlgEquiv B (ρ a) := by
    intro a
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrixAlgEquiv_apply]
    rfl
  have hinj : Function.Injective (R.subtype.mapMatrix (m := J)) := by
    intro x y hxy
    ext i j
    have := congrFun (congrFun hxy i) j
    simpa using this
  let mr : 𝓞 E →+* Matrix J J R :=
    { toFun := m
      map_one' := hinj (by rw [hm, map_one, map_one, map_one])
      map_zero' := hinj (by rw [hm, map_zero, map_zero, map_zero])
      map_mul' := fun a b => hinj (by rw [map_mul, hm, hm, hm, map_mul, map_mul])
      map_add' := fun a b => hinj (by rw [map_add, hm, hm, hm, map_add, map_add]) }
  let ρX : 𝓞 E →+* Module.End C X :=
    ((Matrix.toLinAlgEquiv F).toRingEquiv.toRingHom.comp ψ.mapMatrix).comp mr
  have hρX : ∀ a j, ρX a (F j) = ∑ i, ψ (m a i j) • F i := by
    intro a j
    simp [ρX, mr, Matrix.toLinAlgEquiv_self]
  let ev : L →ₛₗ[ψ] X :=
    { toFun := fun h => ∑ i, ψ (cd h i) • F i
      map_add' := fun x y => by
        have : ∀ i, cd (x + y) i = cd x i + cd y i := fun i => Subtype.ext (by simp [cd])
        simp [this, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        have : ∀ i, cd (r • x) i = r * cd x i := fun i => Subtype.ext (by
          simp only [cd, Submodule.coe_smul]
          rw [← algebraMap_smul Ω r (x : W), map_smul]
          simp [Subring.coe_mul]
          rfl)
        simp [this, mul_smul, Finset.smul_sum] }
  have hev : ∀ h, ev h = ∑ i, ψ (cd h i) • F i := fun _ => rfl
  have hco : ∀ (h : L) (i : J) (r : R), B.repr (h : W) i = r → F.repr (ev h) i = ψ r := by
    intro h i r hr
    have : cd h i = r := Subtype.ext hr
    simp [hev, this, Finsupp.single_apply]
  refine ⟨ρX, ev, hco, ?_, ?_⟩
  · intro j hj
    apply F.repr.injective
    ext i
    by_cases hij : i = j
    · subst hij
      rw [hco _ i 1 (by simp), F.repr_self]
      simp
    · rw [hco _ i 0 (by simp [Finsupp.single_apply, Ne.symm hij]), F.repr_self]
      simp [Finsupp.single_apply, Ne.symm hij]
  · intro a h h'
    have key : ∀ i, cd ⟨_, h'⟩ i = ∑ j, m a i j * cd h j := by
      intro i
      apply Subtype.ext
      have := congrFun (LinearMap.toMatrix_mulVec_repr B B (ρ a) (h : W)) i
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [cd, m, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul]
      simpa [LinearMap.toMatrix_apply] using this.symm
    rw [hev, hev, map_sum]
    simp only [map_smul, hρX, key, map_sum, map_mul, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]

theorem ev_mem_span {Ω W J K C X A : Type} [Field Ω] [AddCommGroup W] [Module Ω W] [Fintype J]
    (R R' : Subring Ω) (hR : R ≤ R') (L : Submodule R' W) (u : J → L) (v : K → L)
    (huv : ∀ q, (v q : W) ∈ Submodule.span R (Set.range fun j => (u j : W)))
    [Field C] [AddCommGroup X] [Module C X] [CommRing A] [Algebra A C] [Module A X] [IsScalarTower A C X]
    (ψ : R' →+* C) (ev : L →ₛₗ[ψ] X) (hψ : ∀ r : R, ψ ⟨r, hR r.2⟩ ∈ (algebraMap A C).range) (q : K) :
    ev (v q) ∈ Submodule.span A (Set.range fun j => ev (u j)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (huv q)
  have : v q = ∑ j, (⟨c j, hR (c j).2⟩ : R') • u j := by
    apply Subtype.ext
    rw [← hc]
    simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul]
    rfl
  rw [this, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smulₛₗ]
  obtain ⟨a, ha⟩ := hψ (c j)
  rw [← ha, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem free_transport {Ω W J K C X A : Type} [Field Ω] [AddCommGroup W] [Module Ω W] [Fintype J] [Fintype K]
    (B : Module.Basis J Ω W) (T : Module.Basis K Ω W) (R R' : Subring Ω) (hR : R ≤ R')
    (hBT : Submodule.span R (Set.range B) = Submodule.span R (Set.range T))
    (L : Submodule R' W) (hB : ∀ j, B j ∈ L) (hT : ∀ q, T q ∈ L)
    [Field C] [AddCommGroup X] [Module C X] [CommRing A] [Algebra A C] [Module A X] [IsScalarTower A C X]
    (F : Module.Basis J C X) (ψ : R' →+* C) (ev : L →ₛₗ[ψ] X) (hF : ∀ j, ev ⟨B j, hB j⟩ = F j)
    (hψ : ∀ r : R, ψ ⟨r, hR r.2⟩ ∈ (algebraMap A C).range) :
    LinearIndependent C (fun q => ev ⟨T q, hT q⟩) ∧
      Submodule.span A (Set.range F) = Submodule.span A (Set.range fun q => ev ⟨T q, hT q⟩) := by
  have h1 : ∀ j, F j ∈ Submodule.span A (Set.range fun q => ev ⟨T q, hT q⟩) := fun j => by
    rw [← hF j]
    refine ev_mem_span R R' hR L (fun q => ⟨T q, hT q⟩) (fun j => ⟨B j, hB j⟩) (fun j => ?_) ψ ev hψ j
    show B j ∈ Submodule.span R (Set.range T)
    rw [← hBT]
    exact Submodule.subset_span ⟨j, rfl⟩
  have h2 : ∀ q, ev ⟨T q, hT q⟩ ∈ Submodule.span A (Set.range F) := fun q => by
    have := ev_mem_span (A := A) R R' hR L (fun j => ⟨B j, hB j⟩) (fun q => ⟨T q, hT q⟩) (fun q => ?_) ψ ev hψ q
    · simpa only [hF] using this
    · show T q ∈ Submodule.span R (Set.range B)
      rw [hBT]
      exact Submodule.subset_span ⟨q, rfl⟩
  have hspan : Submodule.span A (Set.range F) = Submodule.span A (Set.range fun q => ev ⟨T q, hT q⟩) :=
    le_antisymm (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h1 j))
      (Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact h2 q))
  refine ⟨?_, hspan⟩
  have htop : (⊤ : Submodule C X) ≤ Submodule.span C (Set.range fun q => ev ⟨T q, hT q⟩) := by
    rw [← F.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.span_subset_span A C _ (h1 j)
  refine linearIndependent_of_top_le_span_of_card_eq_finrank htop ?_
  rw [Module.finrank_eq_card_basis F, ← Module.finrank_eq_card_basis B, Module.finrank_eq_card_basis T]

theorem stable_of_isFreeOn {E K V A : Type} [Field E] [NumberField E] [CommRing A] [Field K] [Algebra A K]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] {ρ : 𝓞 E →+* Module.End K V}
    {X : Submodule A V} {N : ℕ} {t : Fin N → V} (h : HT.IsFreeOn ρ X t) (a : 𝓞 E) :
    ∀ x ∈ X, ρ a x ∈ X := by
  intro x hx
  rw [h.2.2] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    have e : ρ a (ρ (RingOfIntegers.basis E q.2) (t q.1)) =
        ∑ j, ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E q.2) j) •
          ρ (RingOfIntegers.basis E j) (t q.1) := by
      have := congrArg (fun y => ρ y (t q.1)) ((RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E q.2))
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, map_mul, Module.End.mul_apply] at this
      exact this.symm
    rw [e]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(q.1, j), rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ _ hx

theorem repr_mem {Ω W J : Type} [Field Ω] [AddCommGroup W] [Module Ω W] [Fintype J] (B : Module.Basis J Ω W)
    (R : Subring Ω) {h : W} (hh : h ∈ Submodule.span R (Set.range B)) (i : J) : B.repr h i ∈ R := by
  rw [mem_span_basis_iff (A := R) B h] at hh
  obtain ⟨r, hr⟩ := hh i
  rw [← hr]
  exact r.2

variable {Ω Vs : Type} [Field Ω] [AddCommGroup Vs] [Module Ω Vs] {g : ℕ}

theorem exists_basis (ℓ : Fin g → Vs) (hli : LinearIndependent Ω ℓ) (hsp : Submodule.span Ω (Set.range ℓ) = ⊤)
    (R : Subring Ω) (HL : Submodule R (Vs × Module.Dual Ω Vs))
    (hfst : HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) = Submodule.span R (Set.range ℓ)) :
    ∃ (b : Module.Basis (Fin g) Ω Vs) (B : Module.Basis (Fin g ⊕ Fin g) Ω (Vs × Module.Dual Ω Vs)),
      (⇑b = ℓ) ∧ (∀ i, B (Sum.inl i) ∈ HL ∧ (B (Sum.inl i)).1 = ℓ i) ∧
      (∀ i, B (Sum.inr i) = (0, b.coord i)) ∧
      (∀ h i, B.repr h (Sum.inl i) = b.repr h.1 i) ∧
      (∀ f i, B.repr ((0 : Vs), f) (Sum.inr i) = f (ℓ i)) := by
  let b : Module.Basis (Fin g) Ω Vs := Module.Basis.mk hli hsp.ge
  have hb : ⇑b = ℓ := Module.Basis.coe_mk hli hsp.ge
  have hl : ∀ i, ∃ y ∈ HL, y.1 = ℓ i := fun i => by
    have : ℓ i ∈ HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) := by
      rw [hfst]; exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy, e⟩ := this
    exact ⟨y, hy, e⟩
  choose y hy hy1 using hl
  let Λ : Vs →ₗ[Ω] Module.Dual Ω Vs := b.constr Ω (fun i => (y i).2)
  let S : (Vs × Module.Dual Ω Vs) ≃ₗ[Ω] (Vs × Module.Dual Ω Vs) :=
    LinearEquiv.skewProd (LinearEquiv.refl Ω Vs) (LinearEquiv.refl Ω (Module.Dual Ω Vs)) Λ
  have hS : ∀ p, S p = (p.1, p.2 + Λ p.1) := fun p => rfl
  have hSs : ∀ p, S.symm p = (p.1, p.2 - Λ p.1) := fun p => by
    apply S.injective
    rw [S.apply_symm_apply, hS]
    simp
  have hΛ : ∀ i, Λ (b i) = (y i).2 := fun i => b.constr_basis Ω _ i
  let B := (b.prod b.dualBasis).map S
  have hBl : ∀ i, B (Sum.inl i) = y i := fun i => by
    simp only [B, Module.Basis.map_apply, hS, Module.Basis.prod_apply, Sum.elim_inl]
    have h' : Λ (ℓ i) = (y i).2 := hb ▸ hΛ i
    simp [h', hb, hy1, Prod.ext_iff]
  refine ⟨b, B, hb, fun i => ?_, fun i => ?_, fun h i => ?_, fun f i => ?_⟩
  · rw [hBl]; exact ⟨hy i, hy1 i⟩
  · simp only [B, Module.Basis.map_apply, hS, Module.Basis.prod_apply, Sum.elim_inr]
    simp
  · simp only [B, Module.Basis.map_repr, LinearEquiv.trans_apply, hSs]
    simp
  · simp only [B, Module.Basis.map_repr, LinearEquiv.trans_apply, hSs]
    simp [hb]

theorem eq_span_basis {ℓ : Fin g → Vs} {b : Module.Basis (Fin g) Ω Vs}
    {B : Module.Basis (Fin g ⊕ Fin g) Ω (Vs × Module.Dual Ω Vs)} (hb : ⇑b = ℓ)
    (hl : ∀ i, (B (Sum.inl i)).1 = ℓ i) (hr : ∀ i, B (Sum.inr i) = (0, b.coord i))
    (R : Subring Ω) (HL : Submodule R (Vs × Module.Dual Ω Vs)) (hB : ∀ j, B j ∈ HL)
    (hfst : HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) = Submodule.span R (Set.range ℓ))
    (hd : ∀ f : Module.Dual Ω Vs, ((0 : Vs), f) ∈ HL ↔ ∀ e ∈ Submodule.span R (Set.range ℓ), f e ∈ R) :
    HL = Submodule.span R (Set.range B) := by
  refine le_antisymm (fun h hh => ?_) (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hB j))
  have h1 : h.1 ∈ Submodule.span R (Set.range ℓ) := by
    rw [← hfst]; exact ⟨h, hh, rfl⟩
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h1
  set s : Vs × Module.Dual Ω Vs := ∑ i, x i • B (Sum.inl i) with hs
  have hsm : s ∈ Submodule.span R (Set.range B) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hsH : s ∈ HL := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hB _)
  have hs1 : s.1 = h.1 := by
    rw [← hx, hs, Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Prod.smul_fst, hl]
  obtain ⟨f, hf⟩ : ∃ f, h - s = ((0 : Vs), f) := ⟨(h - s).2, Prod.ext (by simp [hs1]) rfl⟩
  have hfH : ((0 : Vs), f) ∈ HL := hf ▸ sub_mem hh hsH
  have hfR : ∀ j, f (ℓ j) ∈ R := fun j => (hd f).1 hfH _ (Submodule.subset_span ⟨j, rfl⟩)
  have hfs : ((0 : Vs), f) = ∑ j, (⟨f (ℓ j), hfR j⟩ : R) • B (Sum.inr j) := by
    have := b.sum_dual_apply_smul_coord f
    apply Prod.ext
    · simp [Prod.fst_sum, hr]
    · simp only [Prod.snd_sum, Prod.smul_snd, hr]
      conv_lhs => rw [← this]
      simp only [hb]
      rfl
  have : h = s + ((0 : Vs), f) := by rw [← hf]; abel
  rw [this, hfs]
  exact add_mem hsm (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem repr_comb {R : Subring Ω} {ℓ : Fin g → Vs} {b : Module.Basis (Fin g) Ω Vs} (hb : ⇑b = ℓ)
    (x : Fin g → R) (i : Fin g) : b.repr (comb ℓ x) i = x i := by
  subst hb
  simp [comb, Finsupp.single_apply]

theorem exists_eval : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs)) (bar : 𝓞 E ≃+* 𝓞 E)
    (R R' : Subring Ω) (hR : R ≤ R') (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HLx : Submodule R (Vs × Module.Dual Ω Vs)) (HLy : Submodule R' (Vs × Module.Dual Ω Vs))
    (C A : Type) [Field C] [CommRing A] [Algebra A C] (ψ : R' →+* C),
    (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) →
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    HodgeAt ρH HLx ℓ t → HodgeAt ρH HLy ℓ t →
    (∀ r : R, ψ ⟨r, hR r.2⟩ ∈ (algebraMap A C).range) →
    ∃ (ρC : 𝓞 E →+* Module.End C (Fin g → C))
      (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
      (ev : HLy →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
      (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C))),
      (∀ a y, (ρHC a y).1 = ρC a y.1) ∧ (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) ∧
      Tied ℓ ψ ρ ρC ∧ IsEval ℓ ψ ρH ρHC HLy ev ∧
      HV.map ((LinearMap.fst C (Fin g → C) (Module.Dual C (Fin g → C))).restrictScalars A) = stdLat A C g ∧
      (∀ f : Module.Dual C (Fin g → C), ((0 : Fin g → C), f) ∈ HV ↔
        ∀ e ∈ stdLat A C g, f e ∈ (algebraMap A C).range) ∧
      ∀ ht : ∀ i, t i ∈ HLy, HT.IsFreeOn ρHC HV (fun i => ev ⟨t i, ht i⟩) := by
  intro E _ _ Ω Vs _ _ _ ρ ρH bar R R' hR g N ℓ t HLx HLy C A _ _ _ ψ h1 h2 hli hsp hx hy hψ
  classical
  obtain ⟨b, B, hb, hinl, hinr, hrl, hrr⟩ := exists_basis ℓ hli hsp R HLx hx.2.1
  have hxy : ∀ w ∈ HLx, w ∈ HLy := by
    intro w hw
    rw [hx.1.2.2] at hw
    induction hw using Submodule.span_induction with
    | mem x hx' =>
      rw [hy.1.2.2]
      exact Submodule.subset_span hx'
    | zero => exact zero_mem _
    | add x z _ _ h h' => exact add_mem h h'
    | smul r x _ h => exact HLy.smul_mem (⟨r, hR r.2⟩ : R') h
  have hBx : ∀ j, B j ∈ HLx := by
    rintro (i | i)
    · exact (hinl i).1
    · rw [hinr, hx.2.2]
      intro e he
      rw [← hb] at he
      have := repr_mem b R he i
      simpa using this
  have hBy : ∀ j, B j ∈ HLy := fun j => hxy _ (hBx j)
  have eqx : HLx = Submodule.span R (Set.range B) :=
    eq_span_basis hb (fun i => (hinl i).2) hinr R HLx hBx hx.2.1 hx.2.2
  have eqy : HLy = Submodule.span R' (Set.range B) :=
    eq_span_basis hb (fun i => (hinl i).2) hinr R' HLy hBy hy.2.1 hy.2.2
  have sty := stable_of_isFreeOn hy.1
  have hfm : ∀ h ∈ HLy, h.1 ∈ Submodule.span R' (Set.range ℓ) := fun h hh => by
    rw [← hy.2.1]; exact ⟨h, hh, rfl⟩
  have stL : ∀ a, ∀ v ∈ Submodule.span R' (Set.range ℓ), ρ a v ∈ Submodule.span R' (Set.range ℓ) := by
    intro a v hv
    rw [← hy.2.1] at hv
    obtain ⟨h, hh, rfl⟩ := hv
    have := hfm _ (sty a h hh)
    rwa [h1] at this
  let F : Module.Basis (Fin g) C (Fin g → C) := Pi.basisFun C (Fin g)
  let EE : Module.Basis (Fin g ⊕ Fin g) C ((Fin g → C) × Module.Dual C (Fin g → C)) := F.prod F.dualBasis
  have hspanb : Submodule.span R' (Set.range ℓ) = Submodule.span R' (Set.range b) := by rw [hb]
  obtain ⟨ρC, evC, hC1, hC1', hC2⟩ := exists_transport b ρ R' (Submodule.span R' (Set.range ℓ)) hspanb stL F ψ
  obtain ⟨ρHC, ev, hH1, hH1', hH2⟩ := exists_transport B ρH R' HLy eqy sty EE ψ
  have hFr : ∀ (v : Fin g → C) i, F.repr v i = v i := fun v i => by simp [F]
  have fc1 : ∀ (h : Submodule.span R' (Set.range ℓ)) i (r : R'), b.repr (h : Vs) i = r → evC h i = ψ r :=
    fun h i r e => by
      have := hC1 h i r e
      rwa [hFr] at this
  have fe1 : ∀ (h : HLy) i (r : R'), b.repr (h : Vs × Module.Dual Ω Vs).1 i = r → (ev h).1 i = ψ r :=
    fun h i r e => by
      have := hH1 h (Sum.inl i) r (by rw [hrl]; exact e)
      simpa [EE, F] using this
  have fe2 : ∀ (h : HLy) i (r : R'), B.repr (h : Vs × Module.Dual Ω Vs) (Sum.inr i) = r →
      (ev h).2 (F i) = ψ r := fun h i r e => by
    have := hH1 h (Sum.inr i) r e
    simpa [EE] using this
  have hcomb : ∀ x : Fin g → R', comb ℓ x ∈ Submodule.span R' (Set.range ℓ) := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (x i) (Submodule.subset_span ⟨i, rfl⟩)
  have hevC : ∀ (x : Fin g → R') (hm), evC ⟨comb ℓ x, hm⟩ = fun i => ψ (x i) := fun x hm =>
    funext fun i => fc1 _ i (x i) (repr_comb hb x i)
  have hEv1 : ∀ (h : HLy), (ev h).1 = evC ⟨(h : Vs × Module.Dual Ω Vs).1, hfm _ h.2⟩ := fun h => by
    funext i
    have hm : b.repr (h : Vs × Module.Dual Ω Vs).1 i ∈ R' := by
      refine repr_mem b R' ?_ i
      rw [← hspanb]
      exact hfm _ h.2
    rw [fe1 h i ⟨_, hm⟩ rfl, fc1 _ i ⟨_, hm⟩ rfl]
  have c1 : ∀ a y, (ρHC a y).1 = ρC a y.1 := by
    intro a y
    have : (LinearMap.fst C _ _) ∘ₗ ρHC a = ρC a ∘ₗ LinearMap.fst C (Fin g → C) (Module.Dual C (Fin g → C)) := by
      refine EE.ext fun j => ?_
      show (ρHC a (EE j)).1 = ρC a (EE j).1
      rw [← hH1' j (hBy j), ← hH2 a _ (sty a _ (hBy j)), hEv1, hEv1, ← hC2 a _ (stL a _ (hfm _ (hBy j)))]
      congr 2
      exact h1 a _
    exact LinearMap.congr_fun this y
  have fe3 : ∀ (h : HLy) (x : Fin g → R') (r : R'), (h : Vs × Module.Dual Ω Vs).1 = 0 →
      (h : Vs × Module.Dual Ω Vs).2 (comb ℓ x) = r → (ev h).2 (fun i => ψ (x i)) = ψ r := by
    intro h x r h0 hr
    obtain ⟨w, hw⟩ := h
    obtain ⟨v, f⟩ := w
    obtain rfl : v = 0 := h0
    have hs : ∀ i, B.repr ((0 : Vs), f) (Sum.inr i) ∈ R' := fun i => repr_mem B R' (eqy ▸ hw) _
    have e1 : (fun i => ψ (x i)) = ∑ i, ψ (x i) • F i := by
      ext k
      simp [F, Finset.sum_apply, Pi.single_apply]
    rw [e1, map_sum]
    simp only [map_smul, smul_eq_mul]
    have e2 : ∀ i, (ev ⟨(0, f), hw⟩).2 (F i) = ψ ⟨_, hs i⟩ := fun i => fe2 _ i _ rfl
    simp only [e2]
    have hr' : r = ∑ i, x i * ⟨_, hs i⟩ := by
      apply Subtype.ext
      have hr2 : f (comb ℓ x) = r := hr
      rw [← hr2, AddSubmonoidClass.coe_finset_sum]
      simp only [comb, map_sum, map_smul, smul_eq_mul, Subring.coe_mul, hrr]
    rw [hr', map_sum]
    simp only [map_mul]
  have c2 : ∀ a f, ρHC a ((0 : Fin g → C), f) = (0, f ∘ₗ ρC (bar a)) := by
    intro a f
    have : ρHC a ∘ₗ LinearMap.inr C (Fin g → C) (Module.Dual C (Fin g → C)) =
        LinearMap.inr C (Fin g → C) (Module.Dual C (Fin g → C)) ∘ₗ (ρC (bar a)).dualMap := by
      refine F.dualBasis.ext fun j => ?_
      have hE : ((0 : Fin g → C), F.dualBasis j) = EE (Sum.inr j) := by simp [EE]
      show ρHC a ((0 : Fin g → C), F.dualBasis j) = ((0 : Fin g → C), (ρC (bar a)).dualMap (F.dualBasis j))
      have hB' : ρH a (B (Sum.inr j)) = (0, b.coord j ∘ₗ ρ (bar a)) := by rw [hinr]; exact h2 _ _
      rw [hE, ← hH1' _ (hBy _), ← hH2 a _ (sty a _ (hBy _))]
      apply Prod.ext
      · funext i
        exact (fe1 _ i 0 (by simp [hB'])).trans (by simp)
      · refine F.ext fun i => ?_
        have hl : ℓ i ∈ Submodule.span R' (Set.range ℓ) := Submodule.subset_span ⟨i, rfl⟩
        have hcoef : b.repr (ρ (bar a) (ℓ i)) j ∈ R' := by
          refine repr_mem b R' ?_ j
          rw [← hspanb]
          exact stL _ _ hl
        have hFi : F i = evC ⟨ℓ i, hl⟩ := by
          have := hC1' i (by rw [hb]; exact hl)
          rw [← this]
          congr 2
          exact congrFun hb i
        have e1 := fe2 ⟨_, sty a _ (hBy (Sum.inr j))⟩ i ⟨_, hcoef⟩ (by
          show B.repr (ρH a (B (Sum.inr j))) (Sum.inr i) = _
          rw [hB', hrr]
          simp)
        refine e1.trans ?_
        have e2 : (ρC (bar a)).dualMap (F.dualBasis j) (F i) = (ρC (bar a) (F i)) j := by
          simp [F]
        show _ = (ρC (bar a)).dualMap (F.dualBasis j) (F i)
        rw [e2, hFi, ← hC2 _ _ (stL _ _ hl)]
        exact (fc1 _ j ⟨_, hcoef⟩ rfl).symm
    exact LinearMap.congr_fun this f
  have tied : Tied ℓ ψ ρ ρC := by
    intro a x x' e
    rw [← hevC x (hcomb x), ← hC2 _ _ (stL _ _ (hcomb x))]
    simp only [e]
    exact hevC x' _
  have isEv : IsEval ℓ ψ ρH ρHC HLy ev := by
    refine ⟨hH2, ?_, ?_⟩
    · intro h x e
      funext i
      exact fe1 h i (x i) (by rw [e]; exact repr_comb hb x i)
    · exact fun h x r h0 hr => fe3 h x r h0 hr
  have hHV : ∀ y : (Fin g → C) × Module.Dual C (Fin g → C), y ∈ Submodule.span A (Set.range EE) ↔
      (∀ i, y.1 i ∈ (algebraMap A C).range) ∧ (∀ i, y.2 (F i) ∈ (algebraMap A C).range) := by
    intro y
    rw [mem_span_basis_iff EE y, Sum.forall]
    simp [EE, F]
  refine ⟨ρC, ρHC, ev, Submodule.span A (Set.range EE), c1, c2, tied, isEv, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hyV, rfl⟩
      exact ((hHV y).1 hyV).1
    · intro hx'
      exact ⟨(x, 0), (hHV _).2 ⟨hx', fun i => by simp⟩, rfl⟩
  · intro f
    rw [hHV]
    constructor
    · rintro ⟨-, hf⟩ e he
      have : e = ∑ i, e i • F i := by
        ext k
        simp [F, Finset.sum_apply, Pi.single_apply]
      rw [this, map_sum]
      refine sum_mem fun i _ => ?_
      rw [map_smul, smul_eq_mul]
      exact mul_mem (he i) (hf i)
    · intro hf
      refine ⟨fun i => by simp, fun i => hf _ fun k => ?_⟩
      by_cases hk : k = i
      · subst hk
        simpa [F] using one_mem (algebraMap A C).range
      · simpa [F, Pi.single_apply, hk] using zero_mem (algebraMap A C).range
  · intro ht
    have hspan : Submodule.span Ω (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        ρH (RingOfIntegers.basis E q.2) (t q.1)) = ⊤ := by
      have := hx.1.2.1
      rw [hx.1.2.2, Submodule.span_span_of_tower] at this
      exact this
    let T : Module.Basis (Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)) Ω (Vs × Module.Dual Ω Vs) :=
      Module.Basis.mk hx.1.1 hspan.ge
    have hTc : ∀ q, T q = ρH (RingOfIntegers.basis E q.2) (t q.1) := fun q => by simp [T]
    have hT : ∀ q, T q ∈ HLy := fun q => by
      rw [hTc]
      exact sty _ _ (ht q.1)
    have hBT : Submodule.span R (Set.range B) = Submodule.span R (Set.range T) := by
      rw [← eqx, hx.1.2.2]
      congr 2
      exact (Module.Basis.coe_mk hx.1.1 hspan.ge).symm
    obtain ⟨f1, f2⟩ := free_transport (A := A) B T R R' hR hBT HLy hBy hT EE ψ ev (fun j => hH1' j _) hψ
    have hfam : (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        ρHC (RingOfIntegers.basis E q.2) (ev ⟨t q.1, ht q.1⟩)) = fun q => ev ⟨T q, hT q⟩ := by
      funext q
      rw [← hH2 _ _ (sty _ _ (ht q.1))]
      congr 2
      exact (hTc q).symm
    refine ⟨?_, ?_, ?_⟩
    · rw [hfam]; exact f1
    · rw [Submodule.span_span_of_tower]
      exact EE.span_eq
    · rw [hfam]; exact f2

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists
