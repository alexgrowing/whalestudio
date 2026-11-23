import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.FinPart

theorem thick_apply (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ)
    (q : Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)))) :
    thick R (IsLocalRing.maximalIdeal R) e q = IsLocalRing.closedPoint R := by
  apply PrimeSpectrum.ext
  show Ideal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) q.asIdeal =
    IsLocalRing.maximalIdeal R
  have hp : (Ideal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) q.asIdeal).IsPrime :=
    q.isPrime.comap _
  have hle : IsLocalRing.maximalIdeal R ≤
      Ideal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) q.asIdeal := by
    intro a ha
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1)) (a ^ (e + 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow ha _)
    have h1 : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1)) a) ^ (e + 1) ∈ q.asIdeal := by
      rw [← map_pow, h0]
      exact zero_mem _
    exact q.isPrime.mem_of_pow_mem _ h1
  exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hp.ne_top hle).symm

section Points
variable {R : Type} [CommRing R] [IsDomain R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {N : ℕ} {T : Type} [CommGroup T] {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left}

def unitIso (Y : Over (Spec (CommRingCat.of R))) : Over.mk (Y.hom ≫ 𝟙 _) ≅ Y :=
  Over.isoMk (Iso.refl _) (by simp)

theorem mul_left_eq (ht : Γ.IsTorsionAlong G (𝟙 _) N i) {Y : Over (Spec (CommRingCat.of R))}
    (y z : Y ⟶ Γ.G) (a b : Y ⟶ G) (ha : a.left = y.left ≫ i) (hb : b.left = z.left ≫ i) :
    (a * b).left = (y * z).left ≫ i := by
  have h := ht.mul Y y z ((unitIso Y).hom ≫ a) ((unitIso Y).hom ≫ b)
    (by simpa [unitIso] using ha) (by simpa [unitIso] using hb)
  rw [← MonObj.comp_mul] at h
  simpa [unitIso] using h

theorem pow_eq_one_iff (ht : Γ.IsTorsionAlong G (𝟙 _) N i) {Y : Over (Spec (CommRingCat.of R))}
    (g : Y ⟶ G) : g ^ N = 1 ↔ ∃ y : Y ⟶ Γ.G, y.left ≫ i = g.left := by
  have h := ht.kernel Y ((unitIso Y).hom ≫ g)
  have e : ((unitIso Y).hom ≫ g) ^ N = (unitIso Y).hom ≫ g ^ N := by
    rw [← GlobalTheory.CompanionTheory.Ar.BT.Tors.comp_pow_id, Category.assoc, GlobalTheory.CompanionTheory.Ar.BT.Tors.comp_pow_id]
  have e1 : (unitIso Y).hom ≫ g ^ N = 1 ↔ g ^ N = 1 := by
    constructor
    · intro h1
      have := congrArg (fun w => (unitIso Y).inv ≫ w) h1
      simpa [MonObj.comp_one] using this
    · intro h1
      rw [h1, MonObj.comp_one]
  rw [e, e1] at h
  rw [h]
  simp [unitIso]

end Points

section Pow
universe v₁ u₁
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

theorem comp_pow_id' {B Y : C} [MonObj B] (y : Y ⟶ B) (n : ℕ) : y ≫ (𝟙 B) ^ n = y ^ n := by
  induction n with
  | zero => simp [Hom.one_def]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

end Pow

section Main
variable {R : Type} [CommRing R] [IsDomain R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {N : ℕ} {T : Type} [CommGroup T] {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left}
  {H : Type} [CommGroup H] {Γf : QFGroup R H} {u : Γf.G ⟶ Γ.G} [IsMonHom u]

def finMap (ht : Γ.IsTorsionAlong G (𝟙 _) N i) (u : Γf.G ⟶ Γ.G) : Γf.G ⟶ G :=
  Over.homMk (u.left ≫ i) (by
    have h := ht.isOver
    have hu := Over.w u
    simp only [Category.comp_id] at h
    simp [h, hu])

theorem finMap_left (ht : Γ.IsTorsionAlong G (𝟙 _) N i) : (finMap ht u).left = u.left ≫ i := rfl

theorem comp_finMap_mul (ht : Γ.IsTorsionAlong G (𝟙 _) N i) {Y : Over (Spec (CommRingCat.of R))}
    (a b : Y ⟶ Γf.G) : (a * b) ≫ finMap ht u = (a ≫ finMap ht u) * (b ≫ finMap ht u) := by
  ext1
  have h := mul_left_eq ht (a ≫ u) (b ≫ u) (a ≫ finMap ht u) (b ≫ finMap ht u)
    (by simp [finMap_left]) (by simp [finMap_left])
  rw [h, ← MonObj.mul_comp]
  simp [finMap_left]

instance isMonHom_finMap (ht : Γ.IsTorsionAlong G (𝟙 _) N i) : IsMonHom (finMap ht u) := by
  have hone : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γf.G) ≫ finMap ht u = 1 := by
    have h := comp_finMap_mul (u := u) ht (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γf.G) 1
    rw [_root_.mul_one] at h
    exact left_eq_mul.1 h
  refine ⟨?_, ?_⟩
  · simpa [Hom.one_def] using hone
  · have h := comp_finMap_mul (u := u) ht (fst Γf.G Γf.G) (snd Γf.G Γf.G)
    rw [Hom.mul_def, Hom.mul_def] at h
    simpa using h

theorem mono_finMap (ht : Γ.IsTorsionAlong G (𝟙 _) N i) [IsOpenImmersion u.left] : Mono (finMap ht u) := by
  have hu : Mono u := by
    constructor
    intro Z a b h
    ext1
    rw [← cancel_mono u.left]
    simpa using congrArg (fun w => w.left) h
  constructor
  intro Z a b h
  rw [← cancel_mono u]
  apply ht.inj
  simpa [finMap_left] using congrArg (fun w => w.left) h

theorem finMap_pow (ht : Γ.IsTorsionAlong G (𝟙 _) N i) : finMap ht u ^ N = 1 :=
  (pow_eq_one_iff ht _).2 ⟨u, rfl⟩

theorem isPullback_thick (ht : Γ.IsTorsionAlong G (𝟙 _) N i) [IsLocalRing R] [IsOpenImmersion u.left]
    (hcl : ∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) (e : ℕ) :
    IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map (finMap ht u)) (toUnit _)
      ((𝟙 (thickObj R (IsLocalRing.maximalIdeal R) e G)) ^ N)
      η[thickObj R (IsLocalRing.maximalIdeal R) e G] := by
  set x := thick R (IsLocalRing.maximalIdeal R) e with hx
  have := mono_finMap (u := u) ht
  have hF : (𝟙 (thickObj R (IsLocalRing.maximalIdeal R) e G)) ^ N = (Over.pullback x).map ((𝟙 G) ^ N) :=
    (GlobalTheory.CompanionTheory.Ar.BT.Tors.map_pow_id (Over.pullback x) G N).symm
  refine GlobalTheory.Diag.isPullback_toUnit_of_lift _ ?_ ?_ ?_
  · rw [hF, ← Functor.map_comp, GlobalTheory.CompanionTheory.Ar.BT.Tors.comp_pow_id, finMap_pow, Functor.map_one, ← Hom.one_def]
  · intro Z a b h
    exact (cancel_mono _).1 h
  · intro Z t h
    have htN : t ^ N = 1 := by
      rw [← Hom.one_def] at h
      rw [← comp_pow_id', h]
    let g := GlobalTheory.CompanionTheory.Ar.BT.Tors.ofPull x G t
    have hg : GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull x G g = t := GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull_ofPull x G t
    have hgN : g ^ N = 1 := by
      apply (GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull_inj (x := x) (G := G))
      have h1 := map_pow (GlobalTheory.CompanionTheory.Ar.BT.Tors.toPullHom x G Z) g N
      have h2 : GlobalTheory.CompanionTheory.Ar.BT.Tors.toPullHom x G Z g = GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull x G g := rfl
      have h3 := map_one (GlobalTheory.CompanionTheory.Ar.BT.Tors.toPullHom x G Z)
      exact h1.trans ((by rw [h2, hg, htN]; exact h3.symm))
    obtain ⟨y, hy⟩ := (pow_eq_one_iff ht g).1 hgN
    have hrange : Set.range y.left ⊆ Set.range u.left := by
      rintro _ ⟨z, rfl⟩
      apply hcl
      rw [← Scheme.Hom.comp_apply, Over.w y]
      show x (Z.hom z) = _
      exact thick_apply R e _
    let l := IsOpenImmersion.lift u.left y.left hrange
    have hl : l ≫ u.left = y.left := IsOpenImmersion.lift_fac _ _ _
    let w : Over.mk (Z.hom ≫ x) ⟶ Γf.G := Over.homMk l (by
      have hu := Over.w u
      have hyw := Over.w y
      rw [← hu, ← Category.assoc, hl, hyw])
    refine ⟨GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull x Γf.G w, ?_⟩
    apply GlobalTheory.CompanionTheory.Ar.BT.Tors.hom_ext_pull
    have h1 : ((Over.pullback x).map (finMap ht u)).left ≫ pullback.fst G.hom x =
        pullback.fst _ x ≫ (finMap ht u).left := pullback.lift_fst _ _ _
    rw [Over.comp_left, Category.assoc, h1, ← Category.assoc, GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull_fst]
    show l ≫ u.left ≫ i = g.left
    rw [← Category.assoc, hl, hy]

end Main

theorem finite_part_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (N : ℕ) (T : Type) [CommGroup T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G (𝟙 _) N i → ∀ (H : Type) [CommGroup H] (Γf : QFGroup R H) (u : Γf.G ⟶ Γ.G) [IsMonHom u], IsOpenImmersion u.left → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) → ∃ v : Γf.G ⟶ G, v.left = u.left ≫ i ∧ IsMonHom v ∧ Mono v ∧ ∀ e, IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map v) (toUnit _) ((𝟙 (thickObj R (IsLocalRing.maximalIdeal R) e G)) ^ N) η[thickObj R (IsLocalRing.maximalIdeal R) e G] := by
  intro R _ _ _ G _ _ N T _ Γ i ht H _ Γf u _ hu hcl
  have := hu
  exact ⟨finMap ht u, rfl, inferInstance, mono_finMap ht, isPullback_thick ht hcl⟩

end GlobalTheory.CompanionTheory.Ar.BT.FinPart
