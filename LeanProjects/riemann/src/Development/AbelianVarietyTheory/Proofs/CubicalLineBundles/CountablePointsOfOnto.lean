import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CMCount

theorem eq_top_of_countable {V L : Type} [AddCommGroup V] [Module ℂ V] [Countable L] (W : Submodule ℂ V) (P : L → V)
    (h : ∀ z, ∃ a, z - P a ∈ W) : W = ⊤ := by
  by_contra hW
  obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hW)
  choose a ha using h
  have : Function.Injective fun c : ℂ => a (c • v) := fun c d e => by
    by_contra hne
    have h1 := W.sub_mem (ha (c • v)) (ha (d • v))
    simp only at e
    rw [e, sub_sub_sub_cancel_right, ← sub_smul] at h1
    exact hv ((W.smul_mem_iff (sub_ne_zero.2 hne)).1 h1)
  have : Countable ℂ := this.countable
  exact not_countable (Complex.ofReal_injective.countable)

theorem exists_basis {V L J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddCommGroup L]
    (b : Module.Basis J ℤ L) (P : L →+ V) (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) : ∃ B : Module.Basis J ℝ V, ∀ i, B i = P (b i) := by
  let Λ : Submodule ℤ V := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology Λ := hd
  have : IsZLattice ℝ Λ := ⟨hs⟩
  refine ⟨(b.map (LinearEquiv.ofInjective P.toIntLinearMap hi)).ofZLatticeBasis ℝ Λ, fun i => ?_⟩
  rw [Module.Basis.ofZLatticeBasis_apply]
  rfl

theorem exists_real_equiv {V L : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddCommGroup L]
    (P P' : L →+ V) (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (hi' : Function.Injective P') (hd' : DiscreteTopology P'.range)
    (hs' : Submodule.span ℝ (Set.range P') = ⊤) : ∃ h : V ≃ₗ[ℝ] V, ∀ a, P' a = h (P a) := by
  let Λ : Submodule ℤ V := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology Λ := hd
  have : IsZLattice ℝ Λ := ⟨hs⟩
  have : Module.Free ℤ L := Module.Free.of_equiv (LinearEquiv.ofInjective P.toIntLinearMap hi).symm
  let b := Module.Free.chooseBasis ℤ L
  obtain ⟨B, hB⟩ := exists_basis b P hi hd hs
  obtain ⟨B', hB'⟩ := exists_basis b P' hi' hd' hs'
  refine ⟨B.equiv B' (Equiv.refl _), fun a => ?_⟩
  have : P'.toIntLinearMap = ((B.equiv B' (Equiv.refl _)).toLinearMap.restrictScalars ℤ).comp P.toIntLinearMap :=
    b.ext fun i => by simp [← hB, ← hB']
  exact LinearMap.congr_fun this a

theorem exists_complex_equiv {U V I : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [Module ℝ U] [Module ℝ V] [IsScalarTower ℝ ℂ U] [IsScalarTower ℝ ℂ V]
    (h : V ≃ₗ[ℝ] V) (F F' : I → (U →ₗ[ℂ] V)) (s : Set U) (hs : Submodule.span ℝ s = ⊤)
    (hF : ⨆ j, LinearMap.range (F j) = ⊤) (e : ∀ j, ∀ x ∈ s, F' j x = h (F j x)) :
    ∃ h' : V ≃ₗ[ℂ] V, ∀ v, h' v = h v := by
  have e' : ∀ j x, F' j x = h (F j x) := fun j x =>
    LinearMap.congr_fun (LinearMap.ext_on (f := (F' j).restrictScalars ℝ)
      (g := h.toLinearMap.comp ((F j).restrictScalars ℝ)) hs (e j)) x
  have hc : ∀ (c : ℂ) v, h (c • v) = c • h v := fun c v => by
    have hv : v ∈ ⨆ j, LinearMap.range (F j) := hF ▸ Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem j x hx =>
      obtain ⟨x, rfl⟩ := hx
      rw [← map_smul, ← e', ← e', map_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  exact ⟨{ h.toAddEquiv with map_smul' := hc }, fun _ => rfl⟩

theorem exists_compare {S S' : Scheme.{0}} {G : Over S} {A B : Over S'} [GrpObj G] [GrpObj A] [GrpObj B] {f : S' ⟶ S}
    {α : A.left ⟶ G.left} {β : B.left ⟶ G.left} (hA : IsGrpPullback A G f α) (hB : IsGrpPullback B G f β) :
    ∃ κ : A ⟶ B, IsMonHom κ ∧ ∀ (T : Over S') (z : T ⟶ B), ∃ y : T ⟶ A, y ≫ κ = z := by
  let κ : A ⟶ B := Over.homMk (hB.1.lift α A.hom hA.1.w) (hB.1.lift_snd ..)
  have hκ : κ.left ≫ β = α := hB.1.lift_fst ..
  refine ⟨κ, isMonHom_of_mul κ fun T x y => ?_, fun T z => ?_⟩
  · let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (x.left ≫ α) (by
      rw [Category.assoc, hA.1.w, Over.w_assoc]; rfl)
    let y₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (y.left ≫ α) (by
      rw [Category.assoc, hA.1.w, Over.w_assoc]; rfl)
    refine Over.OverMorphism.ext (hB.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [← hB.2 T (x ≫ κ) (y ≫ κ) x₀ y₀ (by simp [x₀, hκ]) (by simp [y₀, hκ]), hA.2 T x y x₀ y₀ rfl rfl,
      Over.comp_left, Category.assoc, hκ]
  · refine ⟨Over.homMk (hA.1.lift (z.left ≫ β) T.hom (by rw [Category.assoc, hB.1.w, Over.w_assoc]))
      (hA.1.lift_snd ..), Over.OverMorphism.ext (hB.1.hom_ext ?_ ?_)⟩
    · simp [hκ]
    · rw [Over.w, Over.w]

theorem exists_linear_onto {A B : Over (Sp ℂ)} [GrpObj A] [GrpObj B] {A₀ : Over (Sp ℂ)} [GrpObj A₀]
    (h₀ : IsAbelianScheme A₀) (hB : IsAbelianScheme B) {L₀ : LB A₀.left} {L : LB B.left} {g₀ g : ℕ}
    (u₀ : HolUnif A₀ L₀ g₀) (u : HolUnif B L g)
    (d₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (d₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (κ : A ⟶ B) [IsMonHom κ] (hκ : ∀ (T : Over (Sp ℂ)) (z : T ⟶ B), ∃ y : T ⟶ A, y ≫ κ = z)
    {I : Type} (ψ : I → (A₀ ⟶ A)) (hψ : ∀ i, IsMonHom (ψ i)) (ho : OntoAt ψ (𝟙 (Sp ℂ))) :
    ∃ F : I → ((Fin g₀ → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ j, ∀ x ∈ u₀.Λ, F j x ∈ u.Λ) ∧
      ∀ z, ∃ w ∈ ⨆ j, LinearMap.range (F j), z - w ∈ u.Λ := by
  choose F hF hΛ _ using fun j => HomLinear.exists_linear_of_isMonHom A₀ B h₀ hB L₀ L g₀ g u₀ u d₁ d₂ (ψ j ≫ κ) (by have := hψ j; infer_instance)
  refine ⟨F, hΛ, fun z => ?_⟩
  have key : ∀ l : List (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ y ∈ l, ∃ w ∈ ⨆ j, LinearMap.range (F j), y ≫ κ = u.ex w) →
      ∃ w ∈ ⨆ j, LinearMap.range (F j), l.prod ≫ κ = u.ex w := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨0, Submodule.zero_mem _, by rw [(u.ker 0).2 u.Λ.zero_mem, List.prod_nil, MonObj.one_comp]⟩
    | cons y l ih =>
      intro h
      obtain ⟨w, hw, e⟩ := h y (by simp)
      obtain ⟨w', hw', e'⟩ := ih fun y hy => h y (by simp [hy])
      exact ⟨w + w', Submodule.add_mem _ hw hw', by rw [List.prod_cons, MonObj.mul_comp, e, e', u.ex_add]⟩
  obtain ⟨y, hy⟩ := hκ _ (u.ex z)
  obtain ⟨n, i, x, e⟩ := ho y
  obtain ⟨w, hw, e'⟩ := key (List.ofFn fun m => x m ≫ ψ (i m)) fun y hy => by
    obtain ⟨m, rfl⟩ := (List.mem_ofFn' _ _).1 hy
    obtain ⟨a, ha⟩ := u₀.ex_onto (x m)
    refine ⟨F (i m) a, Submodule.mem_iSup_of_mem (i m) ⟨a, rfl⟩, ?_⟩
    rw [hF, ha]
    exact Category.assoc ..
  refine ⟨w, hw, (u.ker _).1 ?_⟩
  have h1 : u.ex z = u.ex w := by rw [← hy, ← e', e]
  have h2 := u.ex_add (z - w) w
  rw [sub_add_cancel, h1] at h2
  exact mul_eq_right.1 h2.symm

end GlobalTheory.CMCount

namespace GlobalTheory

open CMCount

theorem countable_points_of_onto : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (P₀ : Out.PolAV (Sp ℂ)), Set.Countable {y : Sp ℂ ⟶ Xo.X | y ≫ Xo.s = spMap (algebraMap (KA l) ℂ) ∧ ∃ (t : SAB H (Sp ℂ)) (_ : SABMap t Xo.univ.t y) (n : ℕ) (ψ : Fin n → (P₀.A ⟶ t.G)), (∀ i, IsMonHom (ψ i)) ∧ OntoAt ψ (𝟙 (Sp ℂ))} := by
  intro hU hL E _ _ _ H D l Xo g ty FU P₀
  obtain ⟨rig, hrig⟩ := P₀.rigid
  obtain ⟨u₀, -⟩ := hU P₀ rig hrig
  obtain ⟨s, hsΛ, hs, hli⟩ := exists_linearIndependent ℝ (u₀.Λ : Set (Fin P₀.g → ℂ))
  rw [u₀.full] at hs
  have : Finite s := hli.finite
  have : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  have : ∀ i, Countable (FU.Di i).La := fun i =>
    have := (FU.Di i).fin
    Finsupp.Countable.of_moduleFinite (R := 𝓞 E)
  let R : (Sp ℂ ⟶ Xo.X) → (Σ i : Fin FU.n, Σ n : ℕ, Fin n → s → (FU.Di i).La) → Prop := fun y c =>
    ∃ P, IsPeriod (FU.Di c.1) ty P ∧ FU.u c.1 P = y ∧ ∃ F : Fin c.2.1 → ((Fin P₀.g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      ⨆ j, LinearMap.range (F j) = ⊤ ∧ ∀ j (x : s), F j x = P (c.2.2 j x)
  have huniq : ∀ c, {y | R y c}.Subsingleton := by
    rintro ⟨i, n, c⟩ _ ⟨P, hP, rfl, F, hF, e⟩ _ ⟨P', hP', rfl, F', -, e'⟩
    obtain ⟨h, hh⟩ := exists_real_equiv P P' hP.2.1 hP.2.2.1 hP.2.2.2.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2.1
    obtain ⟨h', hh'⟩ := exists_complex_equiv h F F' s hs hF fun j x hx => by
      rw [e j ⟨x, hx⟩, e' j ⟨x, hx⟩, hh]
    exact (FU.fibre i P P' hP hP').2 ⟨LinearEquiv.refl _ _, h', fun _ _ => rfl, fun a _ => ⟨0, by simp⟩,
      fun a => ⟨0, by simp⟩, fun a => by rw [hh']; exact hh a⟩
  refine (Set.countable_iUnion fun c => (huniq c).countable).mono ?_
  rintro y ⟨hy, t, m, n, ψ, hψ, ho⟩
  obtain ⟨i, P, hP, rfl⟩ := FU.onto y hy
  obtain ⟨Q, φ, -, hQ, hQL, -⟩ := exists_polAV_pullback_of_isLocalRing E H _ Xo.univ.t Xo.univ.proper Xo.univ.ample
    Xo.univ.ktriv ℂ (FU.u i P)
  obtain ⟨u, -, -, Φ, -, d₁, d₂, -, -, hΦ, -⟩ := familyUnif_fibre_theta hU hL.weil E H D l Xo _ g ty FU i P hP Q φ hQ hQL
  obtain ⟨κ, hκ, hκ'⟩ := exists_compare m.cart hQ
  obtain ⟨F, hF, hF'⟩ := exists_linear_onto P₀.isAb Q.isAb u₀ u d₁ d₂ κ hκ' ψ hψ ho
  have hm : ∀ j (x : s), ∃ a, P a = Φ.symm (F j x) := fun j x =>
    (hΦ _).1 (by rw [Φ.apply_symm_apply]; exact hF j x (hsΛ x.2))
  choose c hc using hm
  refine Set.mem_iUnion.2 ⟨⟨i, n, c⟩, P, hP, rfl, fun j => Φ.symm.toLinearMap ∘ₗ F j, ?_, fun j x => (hc j x).symm⟩
  refine eq_top_of_countable _ P fun z => ?_
  obtain ⟨w, hw, hz⟩ := hF' (Φ z)
  obtain ⟨a, ha⟩ := (hΦ (z - Φ.symm w)).1 (by rwa [map_sub, Φ.apply_symm_apply])
  refine ⟨a, ?_⟩
  rw [ha, sub_sub_cancel]
  simp only [LinearMap.range_comp, ← Submodule.map_iSup]
  exact Submodule.mem_map_of_mem hw

end GlobalTheory
