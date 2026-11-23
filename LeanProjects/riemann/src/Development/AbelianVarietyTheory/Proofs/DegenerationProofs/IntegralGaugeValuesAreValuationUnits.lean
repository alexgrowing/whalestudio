import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.UnitVal

section Values
variable {C : Type} [Field C] {X Y : Scheme.{0}}

theorem valF_appLE' {F : Type} [Field F] {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_res' {F : Type} [Field F] {x : Sp F ⟶ X} {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem exists_valHom (S : ValuationSubring C) (t : Sp S ⟶ X) (U : X.Opens) (ht : ⊤ ≤ t ⁻¹ᵁ U) :
    ∃ g : Γ(X, U) →+* S, ∀ a, valF (spMap S.subtype ≫ t) U a = g a := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (t.appLE U ⊤ ht).hom, fun a => ?_⟩
  have h' : ⊤ ≤ (spMap S.subtype ≫ t) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap S.subtype q))
  rw [valF, dif_pos h']
  have e : (spMap S.subtype ≫ t).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      t.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom S.subtype := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap S.subtype) t U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  exact congrArg (fun g => g.hom a) e

theorem val_valF_le {S : ValuationSubring C} (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) : valF (spMap S.subtype ≫ t) U a ∈ S := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  rw [hg]
  exact (g a).2

theorem val_valF_unit {S : ValuationSubring C} (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) (ha : IsUnit a) : S.valuation (valF (spMap S.subtype ≫ t) U a) = 1 := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  rw [hg]
  exact (S.valuation_eq_one_iff (g a)).1 (ha.map g)
end Values

section Geo
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C] [Algebra (FractionRing R) C]
  {N : NumD C} {ν : NumOf D C N} {S : ValuationSubring C} {s : Sp S ⟶ Sp R}

theorem exists_base (h : ∀ r : R, algebraMap (FractionRing R) C (algebraMap R _ r) ∈ S) :
    ∃ s : Sp S ⟶ Sp R, spMap S.subtype ≫ s = (TF (R := R) C).hom := by
  refine ⟨spMap (((algebraMap (FractionRing R) C).comp (algebraMap R _)).codRestrict S.toSubring h), ?_⟩
  change _ = jFK (R := R) C ≫ jK R
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem base_ext {a b : Sp S ⟶ Sp R} (h : spMap S.subtype ≫ a = spMap S.subtype ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have := Spec.map_injective h
  congr 1
  ext r
  exact congrArg (fun g => g.hom r) this

theorem isDominant_sub : IsDominant (spMap S.subtype) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 S.subtype_injective]; exact bot_le)⟩

theorem chart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (y : Sp S ⟶ D.P.A.left)
    (hy : y ≫ D.P.A.hom = s) : ⊤ ≤ y ⁻¹ᵁ D.P.L.U (ν.J (spMap S.subtype ≫ y)) := by
  obtain ⟨x₀, e, h⟩ := hν (Over.homMk (spMap S.subtype ≫ y) (by rw [Category.assoc, hy, hs]))
  have := D.P.isAb.proper
  have := isDominant_sub (S := S)
  have e' : spMap S.subtype ≫ x₀ = spMap S.subtype ≫ y := e
  obtain rfl : x₀ = y := ext_of_isDominant_of_isSeparated D.P.A.hom
    (base_ext (by rw [← Category.assoc, e', Category.assoc])) _ e'
  exact h

theorem wchart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) {Y : Scheme.{0}} {K : Type}
    [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((spMap S.subtype ≫ r) ≫ φ k) := fun q hq =>
  Set.mem_iInter.2 fun k => by
    beta_reduce
    rw [Category.assoc]
    exact chart_int hν hs (r ≫ φ k) (by rw [Category.assoc, h]) hq

theorem val_vF (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    S.valuation (vF t r' ν.J) = 1 := by
  subst e
  exact val_valF_unit r _ (wchart_int hν hs φ r h) _ (Units.isUnit _)

theorem val_sF (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Sec (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    sF t r' ν.J ∈ S := by
  subst e
  exact val_valF_le r _ (wchart_int hν hs φ r h) _

theorem exists_ext (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (x : TF (R := R) C ⟶ D.P.A) :
    ∃ x₀ : Over.mk s ⟶ D.P.A, (Over.homMk (spMap S.subtype) hs : TF (R := R) C ⟶ Over.mk s) ≫ x₀ = x := by
  obtain ⟨x₀, e, -⟩ := hν x
  refine ⟨Over.homMk x₀ (base_ext ?_), Over.OverMorphism.ext e⟩
  rw [← Category.assoc, e, Over.w x]
  exact hs.symm

theorem val_rig (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) :
    S.valuation (vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) C).hom ν.J) = 1 :=
  val_vF hν hs _ s (fun _ => by
    have : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
    exact (congrArg (s ≫ ·) this).trans (Category.comp_id _)) hs

theorem val_θ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x y u : N.A) : S.valuation ((N.θ x y u : C)) = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  obtain ⟨y₀, hy⟩ := exists_ext hν hs (ν.eA y)
  obtain ⟨u₀, hu⟩ := exists_ext hν hs (ν.eA u)
  rw [ν.θ_eq]
  refine val_vF hν hs _ (lift x₀ (lift y₀ u₀)).left (fun k => ?_) ?_
  · exact (congrArg (_ ≫ ·) (Over.w (psum D.P.A (x3 D.P.A) k.down))).trans (Over.w (lift x₀ (lift y₀ u₀)))
  · rw [← hx, ← hy, ← hu, ← comp_lift, ← comp_lift]
    rfl

theorem val_σ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : S.valuation ((N.σ x : C)) = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  rw [ν.σ_eq]
  refine val_vF hν hs _ x₀.left (fun k => ?_) (congrArg (·.left) hx)
  fin_cases k
  · exact (congrArg (_ ≫ ·) (Over.w ι[D.P.A])).trans (Over.w x₀)
  · exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀)

theorem val_th (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : N.th x ∈ S := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  have h := congrArg S.valuation (ν.th_eq x)
  rw [map_mul, val_rig hν hs, _root_.mul_one] at h
  rw [← S.valuation_le_one_iff, h, S.valuation_le_one_iff]
  exact val_sF hν hs _ x₀.left (fun _ => (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀))
    (congrArg (·.left) hx)

theorem val_psi (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : D.X) (hχ : PsiUnitOn D χ Set.univ) : S.valuation (vF (D.psi χ) (jFK (R := R) C) ν.J) = 1 := by
  have e : jFK (R := R) C ≫ D.xK χ = spMap S.subtype ≫ s ≫ (D.c χ).left := by
    rw [← Category.assoc, hs]
    exact (Category.assoc _ _ _).symm
  have h1 := chart_int hν hs (s ≫ (D.c χ).left)
    ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (Over.w (D.c χ))).trans (Category.comp_id _)))
  rw [← e] at h1
  have h2 : s (IsLocalRing.closedPoint S) ∈ ((D.c χ).left ⁻¹ᵁ D.P.L.U (ν.J (jFK (R := R) C ≫ D.xK χ)) : (Sp R).Opens) :=
    h1 (Set.mem_univ _)
  obtain ⟨_, ⟨V, hV, rfl⟩, hy, hle⟩ := (Sp R).isBasis_affineOpens.exists_subset_of_mem_open h2 (TopologicalSpace.Opens.isOpen _)
  have h3 : ⊤ ≤ s ⁻¹ᵁ V := ((IsLocalRing.closedPoint_mem_iff (s ⁻¹ᵁ V)).1 hy).ge
  have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U
      (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) := fun y hy => Set.mem_iInter.2 fun _ => hle hy
  obtain ⟨r, hr, er⟩ := hχ (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) V hV (Set.subset_univ _) hle h
  have hs' : jFK (R := R) C ≫ jK R = spMap S.subtype ≫ s := hs.symm
  have h4 : ⊤ ≤ jFK (R := R) C ⁻¹ᵁ (jK R ⁻¹ᵁ V) := by
    change ⊤ ≤ (jFK (R := R) C ≫ jK R) ⁻¹ᵁ V
    rw [hs']
    exact fun q _ => h3 (Set.mem_univ (spMap S.subtype q))
  have a := valF_res' h h4 ((D.psi χ).s _).val
  rw [Scheme.Hom.app_eq_appLE] at er
  refine (congrArg S.valuation (a.symm.trans ((congrArg (valF _ _) er.symm).trans
    (valF_appLE' (jK R) V le_rfl h4 r)))).trans ?_
  exact (congrArg (fun q => S.valuation (valF q V r)) hs').trans (val_valF_unit s V h3 r hr)

theorem val_ψ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : N.X) (hχ : PsiUnitOn D (ν.eX χ) Set.univ) : S.valuation ((N.ψ χ : C)) = 1 := by
  rw [ν.ψ_eq, map_mul, val_rig hν hs, val_psi hν hs _ hχ, _root_.mul_one]
end Geo

theorem integral_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∀ (N : NumD F) (ν : NumOf D F N), ν.Integral S → (∀ x y u, S.valuation (N.θ x y u : F) = 1) ∧ (∀ x, S.valuation (N.σ x : F) = 1) ∧ (∀ x, N.th x ∈ S) ∧ ((∀ y, PsiUnitOn D y Set.univ) → ∀ χ, S.valuation (N.ψ χ : F) = 1) := by
  intro R _ _ D F _ _ S hR N ν hν
  obtain ⟨s, hs⟩ := exists_base (R := R) (S := S) hR
  exact ⟨val_θ hν hs, val_σ hν hs, val_th hν hs, fun h χ => val_ψ hν hs χ (h _)⟩

end GlobalTheory.Ex.UnitVal
end
