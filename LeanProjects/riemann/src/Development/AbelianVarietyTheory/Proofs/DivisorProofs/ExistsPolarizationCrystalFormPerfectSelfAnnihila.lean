import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolExists

theorem exists_sum_wedge {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (w : ⋀[R]^2 M) :
    ∃ (n : ℕ) (a b : Fin n → M), ∑ k, exteriorPower.ιMulti R 2 ![a k, b k] = w := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, fun _ ↦ v 0, fun _ ↦ v 1, ?_⟩
    rw [Fin.sum_univ_one]
    congr 1
    ext i; fin_cases i <;> rfl
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, a, b, rfl⟩ := hx
    obtain ⟨m, c, d, rfl⟩ := hy
    refine ⟨n + m, Fin.append a c, Fin.append b d, ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r x _ hx =>
    obtain ⟨n, a, b, rfl⟩ := hx
    refine ⟨n, fun k ↦ r • a k, b, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have e : (![r • a k, b k] : Fin 2 → M) = Function.update ![a k, b k] 0 (r • ![a k, b k] 0) := by
      ext i; fin_cases i <;> simp
    rw [e, AlternatingMap.map_update_smul, Function.update_eq_self]

theorem mem_of_annihilates {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ψ : LinearMap.BilinForm K V) [hψ : ψ.IsPerfPair] (F : Submodule K V)
    (hiso : ∀ f ∈ F, ∀ g ∈ F, ψ f g = 0) (hdim : 2 * Module.finrank K F = Module.finrank K V) (f : V)
    (hf : ∀ g ∈ F, ψ f g = 0) : f ∈ F := by
  let Φ : V →ₗ[K] Module.Dual K F := F.subtype.dualMap ∘ₗ ψ
  have hΦ : Function.Surjective Φ :=
    (LinearMap.dualMap_surjective_of_injective F.injective_subtype).comp hψ.bijective_left.2
  have hker : F ≤ LinearMap.ker Φ := fun f hf' ↦ LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ hiso f hf' g g.2)
  have hr := LinearMap.finrank_range_add_finrank_ker Φ
  rw [LinearMap.range_eq_top.2 hΦ, finrank_top, Subspace.dual_finrank_eq] at hr
  have heq : F = LinearMap.ker Φ := Submodule.eq_of_le_of_finrank_eq hker (by omega)
  rw [heq]
  exact LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ hf g g.2)

theorem isGen_self {X : Scheme.{0}} {L : Semi.LB X} (hL : L.IsLB) :
    Semi.LB.Gen.IsGen (⟨fun p => L.g p.1 p.2⟩ : Semi.LB.Iso L L) := by
  refine fun p q => unit_ext fun y hy => ?_
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

end GlobalTheory.PolExists

namespace GlobalTheory.PolExists

open GlobalTheory.Published GlobalTheory.CatCoh

theorem polForm_exists : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X}
    {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π →
    ∃ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
      (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧
      ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  intro P E _ _ _ H Dw l Xo K _ x A _ π hπ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨h0, -, -, -, e, he⟩ := P.1 K A _ hA gA
  have hLB : (Xo.univ.t.PP.L.pull π).IsLB := pull_isLB Xo.univ.t.PP.isLB π
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso K ⊥ (dp0 K) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := exists_sum_wedge (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 K) (𝟙 _) A
    rw [show prim (dp0 K) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 K) (A.hom ≫ 𝟙 _) (Xo.univ.t.PP.L.pull π) (∑ k, cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, cup _ (a k) (b k) := by
      rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  have hpol : IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) (wedgeForm (dp0 K) (𝟙 _) A a' b') :=
    ⟨n, a', b', hz', rfl⟩
  have hK : Out.KTriv A (Xo.univ.t.PP.L.pull π) :=
    kTriv_pull hπ Xo.univ.t.PP.isLB hLB ((isGen_iff _).1 (isGen_self hLB)) Xo.univ.ktriv
  obtain ⟨hiso, hperf⟩ := P.2.2.2.2 K A _ hA gA _ hLB _ hpol
  have hperf' := hperf hK
  refine ⟨_, hpol, hiso, hperf', fun f hf ↦ ?_⟩

  obtain ⟨hfin, -, hrk⟩ := AbelianDeRham.Free.prim P.1 hA gA
  obtain ⟨-, -, hFfin, -, hFrk⟩ := P.2.1 K A _ hA gA
  let p : PrimeSpectrum K := IsLocalRing.closedPoint K
  have d1 : Module.finrank K (primDR A) = 2 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
    have := hrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have d2 : Module.finrank K (PrimitiveSubmodule A) = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
    have := hFrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have d3 := Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)
  have d4 : Module.finrank K (HdR A) = Module.finrank K (primDR A) := Subspace.dual_finrank_eq
  exact mem_of_annihilates _ (Fil A) hiso (by
    change 2 * Module.finrank K (PrimitiveSubmodule A).dualAnnihilator = _
    omega) f hf

end GlobalTheory.PolExists
