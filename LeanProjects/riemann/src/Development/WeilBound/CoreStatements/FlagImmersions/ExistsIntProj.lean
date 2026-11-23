import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.WeilBound.CoreStatements.HodgeTatePoints.GhModel
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.LieTangent

namespace RootFieldNumerics.RF.Fib

theorem mem_eigSp {R W O : Type} [CommRing R] [AddCommGroup W] [Module R W] [CommRing O]
    {ρ : O →+* Module.End R W} {σ : O →+* R} {w : W} : w ∈ eigSp ρ σ ↔ ∀ a, ρ a w = σ a • w := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

private theorem exists_trace_dual_integral_projector {E : Type} [Field E] [NumberField E] {Ix : Type} [Fintype Ix] [DecidableEq Ix]
    (B : Module.Basis Ix ℤ (𝓞 E)) (A : Matrix Ix Ix ℤ) (d : ℤ) (hd : d ≠ 0)
    (hA : A * Algebra.traceMatrix ℤ B = d • 1) :
    ∃ z : Ix → 𝓞 E, (∀ a j, a * z j = ∑ k, B.repr (a * B k) j • z k) ∧ ∑ k, z k * B k = (d : 𝓞 E) := by
  obtain ⟨z, hz⟩ : ∃ z : Ix → 𝓞 E, ∀ j, z j = ∑ i, A j i • B i := ⟨_, fun _ => rfl⟩
  have hF0 : ∀ j l, Algebra.trace ℤ (𝓞 E) (z j * B l) = if j = l then d else 0 := by
    intro j l
    have h1 := congr_fun (congr_fun hA j) l
    rw [Matrix.mul_apply] at h1
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply] at h1
    rw [hz, Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_zsmul, smul_eq_mul]
    rw [h1]
    simp [Matrix.one_apply]
  have hF : ∀ j y, Algebra.trace ℤ (𝓞 E) (z j * y) = d * B.repr y j := by
    intro j y
    conv_lhs => rw [← B.sum_repr y]
    simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_zsmul, hF0, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have hN : ∀ x x' : 𝓞 E, (∀ y, Algebra.trace ℤ (𝓞 E) (x * y) = Algebra.trace ℤ (𝓞 E) (x' * y)) → x = x' := by
    intro x x' h
    apply B.ext_elem
    intro j
    have h2 := h (z j)
    rw [mul_comm x, mul_comm x', hF, hF] at h2
    exact mul_left_cancel₀ hd h2
  refine ⟨z, fun a j => hN _ _ fun y => ?_, hN _ _ fun y => ?_⟩
  · rw [mul_comm a, _root_.mul_assoc, hF, Finset.sum_mul]
    simp only [smul_mul_assoc, map_sum, map_zsmul, hF, smul_eq_mul]
    conv_lhs => rw [← B.sum_repr y]
    simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_zsmul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [Finset.sum_mul, map_sum]
    simp only [_root_.mul_assoc, hF]
    rw [← zsmul_eq_mul, map_zsmul, smul_eq_mul, Algebra.trace_eq_matrix_trace B, Matrix.trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, mul_comm]

private theorem exists_eigSp_projector_sum_mem_and_discr_smul (E : Type) [Field E] [NumberField E] :
    ∃ (I : Type) (_ : Fintype I) (z b : I → 𝓞 E), ∀ (K W : Type) [Field K] [AddCommGroup W] [Module K W]
      (χ : 𝓞 E →+* K) (ρ : 𝓞 E →+* Module.End K W) (w : W),
      (∑ k, χ (z k) • ρ (b k) w) ∈ eigSp ρ χ ∧ (w ∈ eigSp ρ χ → ∑ k, χ (z k) • ρ (b k) w = ((discr E : ℤ) : K) • w) := by
  classical
  obtain ⟨z, hza, hzd⟩ := exists_trace_dual_integral_projector (RingOfIntegers.basis E)
    (Algebra.traceMatrix ℤ (RingOfIntegers.basis E)).adjugate (discr E) (discr_ne_zero E)
    (by rw [Matrix.adjugate_mul]; rfl)
  set B := RingOfIntegers.basis E
  refine ⟨_, inferInstance, z, B, ?_⟩
  intro K W _ _ _ χ ρ w
  have hB : ∀ a k, a * B k = ∑ j, B.repr (a * B k) j • B j := fun a k => (B.sum_repr (a * B k)).symm
  constructor
  · rw [mem_eigSp]
    intro a
    calc ρ a (∑ k, χ (z k) • ρ (B k) w) = ∑ k, χ (z k) • ρ (a * B k) w := by
          simp [map_sum, map_smul, map_mul, Module.End.mul_apply]
      _ = ∑ k, χ (z k) • ∑ j, ((B.repr (a * B k) j : ℤ) : K) • ρ (B j) w := by
          refine Finset.sum_congr rfl fun k _ => ?_
          conv_lhs => rw [hB a k]
          simp [map_sum, Int.cast_smul_eq_zsmul]
      _ = ∑ j, ∑ k, (((B.repr (a * B k) j : ℤ) : K) * χ (z k)) • ρ (B j) w := by
          simp only [Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          simp only [mul_comm]
      _ = ∑ j, χ (a * z j) • ρ (B j) w := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hza a j, map_sum, Finset.sum_smul]
          simp only [map_zsmul, zsmul_eq_mul, map_mul, map_intCast]
      _ = χ a • ∑ k, χ (z k) • ρ (B k) w := by
          simp [Finset.smul_sum, smul_smul, map_mul]
  · intro hw
    rw [mem_eigSp] at hw
    simp only [hw, smul_smul]
    rw [← Finset.sum_smul]
    simp only [← map_mul]
    rw [← map_sum, hzd, map_intCast]

section Val

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E] {M : LieModel G ξ E} {V L : Type} [CommRing V] [IsLocalRing V] [Field L]
  [Algebra V L] {z : Spec (CommRingCat.of V) ⟶ X} {EC : Type} [AddCommGroup EC] [Module L EC] [Module V EC]
  [IsScalarTower V L EC] {MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) EC}

theorem lat_act (M : LieModel G ξ E) (f : G ⟶ G) [IsMonHom f] (T : E →ₗ[Ω] E) (hT : M.IsDiffOf f T) {p : Cpt ξ} {e : E}
    (he : e ∈ M.lat p) : T e ∈ M.lat p := by
  have key : ∀ (e : E) (v : epsAt (X.fromSpecStalk p.1) ⟶ G), M.Extends p e v → M.Extends p (T e) (v ≫ f) := by
    intro e v hv
    obtain ⟨h1, h2⟩ := hv
    refine ⟨?_, ?_⟩
    · unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left]
      simp
    · rw [hT e, Over.comp_left, h2, Category.assoc, Over.comp_left]
  unfold LieModel.lat at he ⊢
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv⟩ := hx
    exact Submodule.subset_span ⟨v ≫ f, key _ _ hv⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ a hx

theorem val_smul (hξ : IsCptGen ξ) {e : E} {w : EC} {a : Ω} {r : V} (ha : ValAt ξ z a r)
    (h : M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) e (MC.pt w)) :
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (a • e) (MC.pt (r • w)) := by
  obtain ⟨hc, -⟩ := id h
  obtain ⟨h1, s, hs1, hs2⟩ := ProjectiveLinePlaces.valAt_restrict (algebraMap V L) rfl hc ha
  have key := LieModel.ValAt.smul h h1 s
  rw [hs1, hs2] at key
  convert key using 1
  apply Over.OverMorphism.ext
  rw [← algebraMap_smul L r w, MC.smul, Over.comp_left]
  rfl

theorem val_add {e e' : E} {w w' : EC}
    (h : M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) e (MC.pt w))
    (h' : M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) e' (MC.pt w')) :
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (e + e') (MC.pt (w + w')) := by
  rw [MC.add]
  exact h.add h'

theorem val_zero (h : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z)) :
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) 0 (MC.pt 0) := by
  rw [MC.pt_zero]
  exact M.valAt_zero h

theorem val_sum (h : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z)) {I : Type} (s : Finset I)
    (e : I → E) (w : I → EC)
    (hw : ∀ k, M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (e k) (MC.pt (w k))) :
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (∑ k ∈ s, e k) (MC.pt (∑ k ∈ s, w k)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact val_zero h
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    exact val_add (hw k) ih

theorem val_mem_span (hξ : IsCptGen ξ) (h : genPt ξ ⤳ centre z)
    (h' : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z)) {n : ℕ} {b : Fin n → E}
    {x : Fin n → EC} (hx : ∀ k, M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (b k) (MC.pt (x k)))
    {e : E} (he : e ∈ Submodule.span (regAt ξ ⟨centre z, h⟩) (Set.range b)) {w : EC}
    (hw : M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) e (MC.pt w)) :
    w ∈ Submodule.span V (Set.range x) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  have hs : ∀ k, ∃ s, genMap ξ ⟨centre z, h⟩ s = (c k : Ω) := fun k => RingHom.mem_range.1 (c k).2
  choose s hs using hs
  have hval : ∀ k, M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) ((c k : Ω) • b k)
      (MC.pt ((CommRingCat.Hom.hom (Scheme.stalkClosedPointTo z)) (s k) • x k)) :=
    fun k => val_smul hξ ⟨h, s k, hs k, rfl⟩ (hx k)
  have hsum := val_sum h' Finset.univ _ _ hval
  have he' : ∑ k, (c k : Ω) • b k = e := by
    rw [← hc]
    rfl
  rw [he'] at hsum
  have hweq := MC.inj (LieModel.ValAt.unique hξ hw hsum)
  rw [hweq]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem val_eig (hξ : IsCptGen ξ) {O : Type} [CommRing O] {act : O → (G ⟶ G)} (hact : ∀ a, IsMonHom (act a))
    {ρ : O →+* Module.End Ω E} {ρC : O →+* Module.End L EC} (h1 : M.IsActOf act ρ) (h2 : MC.IsActOf act ρC)
    {χ : O →+* Ω} {σ : O →+* V} (hσ : ∀ a, ValAt ξ z (χ a) (σ a)) {e : E} (he : e ∈ eigSp ρ χ) {w : EC}
    (hw : M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) e (MC.pt w)) :
    w ∈ eigSp ρC ((algebraMap V L).comp σ) := by
  rw [mem_eigSp] at he ⊢
  intro a
  have hA : M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (ρ a e) (MC.pt (ρC a w)) := by
    obtain ⟨hc, v, ⟨hv1, hv2⟩, hv3⟩ := id hw
    haveI := hact a
    refine ⟨hc, v ≫ act a, ⟨?_, ?_⟩, ?_⟩
    · unfold IsTanAt at hv1 ⊢
      rw [Over.comp_left, ← Category.assoc, hv1, ← Over.comp_left]
      simp
    · rw [h1 a e, Over.comp_left, hv2, Category.assoc, Over.comp_left]
    · rw [h2 a w, Over.comp_left, hv3, Category.assoc, Over.comp_left]
  have hB := val_smul hξ (hσ a) hw
  rw [← he a] at hB
  have heq := MC.inj (LieModel.ValAt.unique hξ hA hB)
  rw [heq, RingHom.comp_apply, algebraMap_smul]

end Val

end RootFieldNumerics.RF.Fib

namespace RootFieldNumerics.RF

open Fib PositivityTheory.HtPt.Gh

private theorem mem_lat_of_specializes {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E)
    (q q' : Cpt ξ) (hs : q'.1 ⤳ q.1) {e : E} (he : e ∈ M.lat q) : e ∈ M.lat q' := by
  have hreg : ∀ a ∈ regAt ξ q, a ∈ regAt ξ q' := by
    rintro a ⟨s, rfl⟩
    exact ⟨_, ProjectiveLinePlaces.genMap_specializes hs q'.2 q.2 s⟩
  have hψ : Spec.map (X.presheaf.stalkSpecializes hs) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk q'.1 :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hs
  have hgen : ∀ (v : epsAt (X.fromSpecStalk q.1) ⟶ G) (x : E), M.Extends q x v →
      ∃ v' : epsAt (X.fromSpecStalk q'.1) ⟶ G, M.Extends q' x v' := by
    intro v x hv
    obtain ⟨hv1, hv2⟩ := hv
    have hφ : Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes hs).hom)) ≫
        (epsAt (X.fromSpecStalk q.1)).hom = (epsAt (X.fromSpecStalk q'.1)).hom := by
      simp only [epsAt, Over.mk_hom]
      rw [← hψ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext a <;> simp [dualMap] <;> first | rfl | exact map_zero _
    let φ : epsAt (X.fromSpecStalk q'.1) ⟶ epsAt (X.fromSpecStalk q.1) := Over.homMk _ hφ
    have hφl : φ.left = Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes hs).hom)) := rfl
    refine ⟨φ ≫ v, ?_, ?_⟩
    · unfold IsTanAt at hv1 ⊢
      have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk q'.1)
          (X.presheaf.stalk q'.1) (X.presheaf.stalk q'.1)).toRingHom) ≫ φ.left =
          Spec.map (X.presheaf.stalkSpecializes hs) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom
          (X.presheaf.stalk q.1) (X.presheaf.stalk q.1) (X.presheaf.stalk q.1)).toRingHom) := by
        rw [hφl, ← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext a <;> simp [dualMap] <;> first | rfl | exact map_zero _
      rw [Over.comp_left, ← Category.assoc, key, Category.assoc, hv1]
      let ψ : Over.mk (X.fromSpecStalk q'.1) ⟶ Over.mk (X.fromSpecStalk q.1) := Over.homMk _ hψ
      have h1 : ψ ≫ (1 : Over.mk (X.fromSpecStalk q.1) ⟶ G) = 1 := by
        exact MonObj.comp_one ψ
      have h2 := congrArg Over.Hom.left h1
      rw [Over.comp_left] at h2
      exact h2
    · rw [Over.comp_left, hφl, ← Category.assoc, ← Spec.map_comp, hv2]
      congr 2
      have hg : ∀ s, genMap ξ q' ((X.presheaf.stalkSpecializes hs).hom s) = genMap ξ q s :=
        fun s => ProjectiveLinePlaces.genMap_specializes hs q'.2 q.2 s
      ext a <;> simp [dualMap, hg] <;> first | rfl | exact (hg _).symm
  unfold LieModel.lat at he ⊢
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨v', hv'⟩ := hgen v x hv
    exact Submodule.subset_span ⟨v', hv'⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    exact Submodule.smul_mem _ (⟨a, hreg a a.2⟩ : regAt ξ q') hx

private theorem fibAt_mono' {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E)
    {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) {C : Type} [Field C] [Algebra R C]
    {EC : Type} [AddCommGroup EC] [Module C EC] [Module R EC]
    (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC) (L1 L2 : Lat ξ E)
    (hL : ∀ h : genPt ξ ⤳ centre z, ∀ e ∈ L1 ⟨centre z, h⟩, e ∈ L2 ⟨centre z, h⟩) :
    M.fibAt L1 z MC ≤ M.fibAt L2 z MC := by
  apply Submodule.span_mono
  rintro w ⟨h, e, he, hw⟩
  exact ⟨h, e, hL h e he, hw⟩

theorem fibSandwich : FibSandwich := by
  intro E _ _ _ H D l Xo c _ Y S Ω _ K _ J _ y 𝔐 V L _ _ _ _ _ _ _ p j z g MC ρC s σ b hj hact hσ hb
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  have hc : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hc' : genPt 𝔐.ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) := 𝔐.all _
  have hspec : centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) ⤳ centre z :=
    ProjectiveLinePlaces.centre_specializes z (algebraMap V L)
  have hemb : ∀ a, 𝔐.emb s a ∈ regAt 𝔐.ξ ⟨centre z, hc⟩ := by
    intro a
    obtain ⟨h, st, h1, -⟩ := hσ a
    exact ⟨st, h1⟩
  have hreg : ∀ a ∈ regAt 𝔐.ξ ⟨centre z, hc⟩, a ∈ regAt 𝔐.ξ ⟨_, hc'⟩ := by
    rintro a ⟨st, rfl⟩
    exact ⟨_, ProjectiveLinePlaces.genMap_specializes hspec hc' hc st⟩
  have hunit' : ∀ n : ℕ, n ≠ 0 → unitAt 𝔐.ξ ⟨_, hc'⟩ (n : Ω) := by
    intro n hn
    rw [unitAt_centre_iff hξ _ hc' n]
    exact isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn)
  have hnorm : ∀ n : ℤ, ‖j (n : L)‖ = ‖(n : ℚ_[(p : ℕ)])‖ := by
    intro n
    rw [map_intCast, ← map_intCast (algebraMap ℚ_[(p : ℕ)] ℂ_[(p : ℕ)]), norm_algebraMap']
  have hpnorm : ‖j ((p : ℕ) : L)‖ < 1 := by
    have := hnorm ((p : ℕ) : ℤ)
    push_cast at this
    rw [this]
    exact Padic.norm_p_lt_one
  have hpnu : ¬ IsUnit (((p : ℕ) : V)) := by
    rintro ⟨u, hu⟩
    have h1 : algebraMap V L ((u⁻¹ : Vˣ) : V) * ((p : ℕ) : L) = 1 := by
      rw [← map_natCast (algebraMap V L), ← map_mul, ← hu, Units.inv_mul, map_one]
    have h2 : ‖j (algebraMap V L ((u⁻¹ : Vˣ) : V))‖ ≤ 1 := (hj _).2 ⟨_, rfl⟩
    have h4 := congrArg (fun x => ‖j x‖) h1
    simp only [map_mul, norm_mul, map_one, norm_one] at h4
    nlinarith [norm_nonneg (j (algebraMap V L ((u⁻¹ : Vˣ) : V))), norm_nonneg (j ((p : ℕ) : L))]
  have hfib : InFibre 𝔐.ξ (p : ℕ) ⟨centre z, hc⟩ := by
    unfold InFibre
    rw [unitAt_centre_iff hξ z hc]
    exact hpnu
  have honly : ∀ p' ∈ S, InFibre 𝔐.ξ p' ⟨centre z, hc⟩ → p' = (p : ℕ) := by
    intro p' hp' hf
    by_contra hne
    exact Lat.not_inFibre_of_coprime _ ((Nat.coprime_primes p.2 (𝔐.S_prime p' hp')).2 (Ne.symm hne)) hfib hf
  have hnot' : ∀ p' ∈ S, ¬ InFibre 𝔐.ξ p' ⟨_, hc'⟩ := fun p' hp' hf => hf (hunit' p' (𝔐.S_prime p' hp').ne_zero)
  have hbq : 𝔐.V s ⟨centre z, hc⟩ = Submodule.span (regAt 𝔐.ξ ⟨centre z, hc⟩) (Set.range b) := hb.2
  have hbk : ∀ k, b k ∈ 𝔐.V s ⟨centre z, hc⟩ := fun k => by
    rw [hbq]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hVS : (p : ℕ) ∈ S → 𝔐.V s ⟨centre z, hc⟩ = 𝔐.HT p s ⟨centre z, hc⟩ := by
    intro hpS
    unfold HodgeCpt.V Lat.patch
    rw [if_pos ⟨_, hpS, hfib⟩]
    apply le_antisymm
    · exact iInf_le_of_le (p : ℕ) (iInf_le_of_le hpS (iInf_le _ hfib))
    · exact le_iInf fun p' => le_iInf fun hp' => le_iInf fun hf => by rw [honly p' hp' hf]
  have hVnS : (p : ℕ) ∉ S → 𝔐.V s ⟨centre z, hc⟩ =
      𝔐.M.lat ⟨centre z, hc⟩ ⊓ (eigSp 𝔐.ρ (𝔐.emb s)).restrictScalars (regAt 𝔐.ξ ⟨centre z, hc⟩) := by
    intro hpS
    unfold HodgeCpt.V Lat.patch
    rw [if_neg]
    · rfl
    · rintro ⟨p', hp', hf⟩
      exact hpS (honly p' hp' hf ▸ hp')
  have hdiff : ∃ N : ℕ, N ≠ 0 ∧ (N : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) :=
    ⟨Ideal.absNorm (differentIdeal ℤ (𝓞 E)), by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact differentIdeal_ne_bot, Ideal.absNorm_mem _⟩
  have hD : (p : ℕ) ∈ S → ∀ e ∈ 𝔐.M.htDual 𝔐.t.PP.L ((p : ℕ) ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) ⟨centre z, hc⟩,
      e ∈ 𝔐.M.lat ⟨_, hc'⟩ := fun hpS =>
    PositivityTheory.HtPt.Gh.htDual_le_lat 𝔐 hpS s ⟨centre z, hc⟩ ⟨_, hc'⟩ hspec hfib honly hnot' hemb
  have hVlat : ∀ e ∈ 𝔐.V s ⟨centre z, hc⟩, e ∈ 𝔐.M.lat ⟨_, hc'⟩ := by
    intro e he
    by_cases hpS : (p : ℕ) ∈ S
    · rw [hVS hpS] at he
      rcases s with τ | τ
      · obtain ⟨N, hN0, hNd⟩ := hdiff
        change e ∈ 𝔐.M.htW _ _ _ _ (differentIdeal ℤ (𝓞 E)) _ at he
        unfold LieModel.htW at he
        induction he using Submodule.span_induction with
        | mem x hx =>
          have h1 := hD hpS _ (hx.2 _ hNd)
          rw [map_natCast] at h1
          obtain ⟨hne, -, hinv⟩ := hunit' N hN0
          have h2 := Submodule.smul_mem _ (⟨_, hinv⟩ : regAt 𝔐.ξ ⟨_, hc'⟩) h1
          have h3 : ((N : Ω)⁻¹ * N) • x ∈ 𝔐.M.lat ⟨_, hc'⟩ := by
            rw [mul_smul]
            exact h2
          rwa [inv_mul_cancel₀ hne, one_smul] at h3
        | zero => exact zero_mem _
        | add x y _ _ hx hy => exact add_mem hx hy
        | smul a x _ hx => exact Submodule.smul_mem _ (⟨a, hreg a a.2⟩ : regAt 𝔐.ξ ⟨_, hc'⟩) hx
      · exact hD hpS e he
    · rw [hVnS hpS] at he
      exact mem_lat_of_specializes 𝔐.M ⟨centre z, hc⟩ ⟨_, hc'⟩ hspec he.1
  have hx0 : ∀ k, ∃ x : Fin g → L,
      𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (b k) (MC.pt x) := by
    intro k
    obtain ⟨w, hw⟩ := (𝔐.M.exists_valAt_iff _ (b k)).2 ⟨hc', hVlat _ (hbk k)⟩
    obtain ⟨x, hx⟩ := MC.onto w hw.isTanAt
    exact ⟨x, hx ▸ hw⟩
  choose x hx using hx0
  have hspan : Submodule.span V (Set.range x) = 𝔐.M.fibAt (𝔐.V s) z MC := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨hc, b k, hbk k, hx k⟩
    · apply Submodule.span_le.2
      rintro w ⟨h, e, he, hw⟩
      have hbq' : 𝔐.V s ⟨centre z, h⟩ = Submodule.span (regAt 𝔐.ξ ⟨centre z, h⟩) (Set.range b) := hb.2
      rw [hbq'] at he
      exact val_mem_span hξ h hc' hx he hw
  refine ⟨x, hx, ?_, ?_⟩
  · intro hpS hpd
    have hVq := hVnS hpS
    obtain ⟨I, _, zz, bb, hP⟩ := exists_eigSp_projector_sum_mem_and_discr_smul E
    have hdisc : IsUnit ((discr E : ℤ) : V) := by
      have hn : ‖j ((discr E : ℤ) : L)‖ = 1 := by
        rw [hnorm]
        refine le_antisymm (Padic.norm_int_le_one _) (not_lt.1 fun h => hpd ?_)
        exact_mod_cast Padic.norm_intCast_lt_one_iff.1 h
      have hne : ((discr E : ℤ) : L) ≠ 0 := by
        intro h0
        rw [h0, map_zero, norm_zero] at hn
        exact zero_ne_one hn
      obtain ⟨u, hu⟩ := RingHom.mem_range.1 ((hj (((discr E : ℤ) : L)⁻¹)).1 (by rw [map_inv₀, norm_inv, hn, inv_one]))
      have hmul : ((discr E : ℤ) : V) * u = 1 := by
        apply IsFractionRing.injective V L
        rw [map_mul, hu, map_intCast, map_one, mul_inv_cancel₀ hne]
      exact ⟨⟨_, u, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hbk' := hbk k
      rw [hVq] at hbk'
      refine Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨hc, b k, (Submodule.mem_inf.1 hbk').1, hx k⟩, ?_⟩
      exact val_eig hξ 𝔐.t.act.hom 𝔐.act hact hσ (Submodule.mem_inf.1 hbk').2 (hx k)
    · intro w hw
      obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hw
      have key : ∀ w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC,
          (∑ k, ((algebraMap V L).comp σ) (zz k) • ρC (bb k) w) ∈ Submodule.span V (Set.range x) := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w' hw' =>
          obtain ⟨h, e, he, hwe⟩ := hw'
          have hact2 : ∀ k, 𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (𝔐.ρ (bb k) e)
              (MC.pt (ρC (bb k) w')) := by
            intro k
            haveI := 𝔐.t.act.hom (bb k)
            exact PositivityTheory.HtPt.Gh.valAt_act 𝔐.M MC (𝔐.t.act.act (bb k)) (𝔐.ρ (bb k)) (ρC (bb k)) (𝔐.act (bb k))
              (hact (bb k)) hwe
          have hsum := val_sum hc' Finset.univ (fun k => 𝔐.emb s (zz k) • 𝔐.ρ (bb k) e)
            (fun k => σ (zz k) • ρC (bb k) w') (fun k => val_smul hξ (hσ (zz k)) (hact2 k))
          have hmem : (∑ k, 𝔐.emb s (zz k) • 𝔐.ρ (bb k) e) ∈
              Submodule.span (regAt 𝔐.ξ ⟨centre z, hc⟩) (Set.range b) := by
            rw [← hbq, hVq]
            refine Submodule.mem_inf.2 ⟨?_, (hP Ω 𝔐.Li (𝔐.emb s) 𝔐.ρ e).1⟩
            refine Submodule.sum_mem _ fun k _ => ?_
            have h1 : 𝔐.ρ (bb k) e ∈ 𝔐.M.lat ⟨centre z, hc⟩ := by
              haveI := 𝔐.t.act.hom (bb k)
              exact lat_act 𝔐.M (𝔐.t.act.act (bb k)) (𝔐.ρ (bb k)) (𝔐.act (bb k)) he
            exact Submodule.smul_mem _ (⟨_, hemb (zz k)⟩ : regAt 𝔐.ξ ⟨centre z, hc⟩) h1
          have h5 := val_mem_span hξ hc hc' hx hmem hsum
          simpa [RingHom.comp_apply, algebraMap_smul] using h5
        | zero => simp
        | add w1 w2 _ _ h1 h2 =>
          simp only [map_add, smul_add, Finset.sum_add_distrib]
          exact add_mem h1 h2
        | smul a w _ h1 =>
          have h3 : ∀ k, ((algebraMap V L).comp σ) (zz k) • ρC (bb k) (a • w) =
              a • (((algebraMap V L).comp σ) (zz k) • ρC (bb k) w) := by
            intro k
            rw [LinearMap.map_smul_of_tower, smul_comm]
          simp only [h3, ← Finset.smul_sum]
          exact Submodule.smul_mem _ a h1
      have h1 := key w hw1
      rw [(hP L (Fin g → L) ((algebraMap V L).comp σ) ρC w).2 hw2] at h1
      rw [← map_intCast (algebraMap V L), algebraMap_smul] at h1
      obtain ⟨u, hu⟩ := hdisc.exists_left_inv
      have h2 := Submodule.smul_mem _ u h1
      rwa [smul_smul, hu, one_smul] at h2
  · intro hpS hfree κ κz hsand hκ
    let v : Valuation L NNReal := (NormedField.valuation (K := ℂ_[(p : ℕ)])).comap j
    have hv : v.Integers V := by
      refine ⟨IsFractionRing.injective V L, fun r => ?_, fun a ha => ?_⟩
      · show ‖j (algebraMap V L r)‖₊ ≤ 1
        rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
        exact (hj _).2 ⟨r, rfl⟩
      · have ha' : ‖j a‖ ≤ 1 := by
          have h0 : ‖j a‖₊ ≤ 1 := ha
          rwa [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one] at h0
        exact RingHom.mem_range.1 ((hj a).1 ha')
    have hvp : v ((p : ℕ) : L) < 1 := by
      show ‖j ((p : ℕ) : L)‖₊ < 1
      rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
      exact hpnorm
    obtain ⟨t1, t2, -⟩ := PositivityTheory.HtPt.Gh.hodge_tate_free_sandwich E H D l Xo c _ _ Y S Ω K J y 𝔐 (p : ℕ) hpS κ hfree hsand
      L v V hv hvp z (Fin g → L) MC ρC s σ κz hact hσ hκ
    have hVq := hVS hpS
    have hDV : ∀ h : genPt 𝔐.ξ ⤳ centre z,
        ∀ e ∈ 𝔐.M.htDual 𝔐.t.PP.L ((p : ℕ) ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) ⟨centre z, h⟩, e ∈ 𝔐.V s ⟨centre z, h⟩ := by
      intro h e he
      change e ∈ 𝔐.V s ⟨centre z, hc⟩
      rw [hVq]
      rcases s with τ | τ
      · change e ∈ 𝔐.M.htW _ _ _ _ (differentIdeal ℤ (𝓞 E)) _
        unfold LieModel.htW
        change e ∈ Submodule.span _ _ at he
        refine Submodule.span_le.2 ?_ he
        intro e0 he0
        exact Submodule.subset_span ⟨he0.1, fun d _ =>
          Submodule.smul_mem _ (⟨_, hemb d⟩ : regAt 𝔐.ξ ⟨centre z, hc⟩) (Submodule.subset_span he0)⟩
      · exact he
    refine ⟨?_, fun d hd w hw => ?_⟩
    · rw [hspan]
      exact t1.trans (fibAt_mono' 𝔐.M z MC _ _ hDV)
    rw [hspan] at hw
    have hsd : σ d • w ∈ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L ((p : ℕ) ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC := by
      rcases s with τ | τ
      · have hd' := hd rfl
        have hW2 : ∀ e ∈ 𝔐.M.htW 𝔐.t.PP.L ((p : ℕ) ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (Sum.inl τ)) (differentIdeal ℤ (𝓞 E))
            ⟨centre z, hc⟩, 𝔐.emb (Sum.inl τ) d • e ∈
              𝔐.M.htDual 𝔐.t.PP.L ((p : ℕ) ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (Sum.inl τ)) ⟨centre z, hc⟩ := by
          intro e he
          unfold LieModel.htW at he
          induction he using Submodule.span_induction with
          | mem e0 he0 => exact he0.2 d hd'
          | zero => simp
          | add e1 e2 _ _ h1 h2 =>
            rw [smul_add]
            exact add_mem h1 h2
          | smul a e1 _ h1 =>
            rw [Subring.smul_def, smul_comm]
            exact Submodule.smul_mem _ a h1
        induction hw using Submodule.span_induction with
        | mem w' hw' =>
          obtain ⟨h, e, he, hwe⟩ := hw'
          change e ∈ 𝔐.V (Sum.inl τ) ⟨centre z, hc⟩ at he
          rw [hVq] at he
          change e ∈ 𝔐.M.htW _ _ _ _ (differentIdeal ℤ (𝓞 E)) _ at he
          have he2 := hW2 e he
          exact Submodule.subset_span ⟨hc, _, he2, val_smul hξ (hσ d) hwe⟩
        | zero => simp
        | add w1 w2 _ _ h1 h2 =>
          rw [smul_add]
          exact add_mem h1 h2
        | smul a w1 _ h1 =>
          rw [smul_comm]
          exact Submodule.smul_mem _ a h1
      · have hw' : w ∈ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L ((p : ℕ) ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (Sum.inr τ))) z MC := by
          refine (fibAt_mono' 𝔐.M z MC _ _ (fun h e he => ?_)) hw
          change e ∈ 𝔐.V (Sum.inr τ) ⟨centre z, hc⟩ at he
          rw [hVq] at he
          exact he
        exact Submodule.smul_mem _ (σ d) hw'
    have h6 := t2 _ hsd
    rw [mul_smul]
    exact h6

end RootFieldNumerics.RF
