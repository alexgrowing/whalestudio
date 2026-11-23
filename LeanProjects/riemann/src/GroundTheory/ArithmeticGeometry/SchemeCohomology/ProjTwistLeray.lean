import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistAway
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjCechModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

universe w w' u

noncomputable section

instance isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf))
    (inferInstanceAs (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}).IsQuasicoherent)

section Transfer

variable {X : TopCat.{u}} {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {D : Opens X}

lemma cechAcyclic_of_bijective_le (φ : ∀ W : Opens X, W ≤ D → Q.obj (op W) →+ P.obj (op W))
    (hφ : ∀ W hW, Function.Bijective (φ W hW))
    (hnat : ∀ {W W' : Opens X} (h : W' ≤ W) (hW : W ≤ D) (x : Q.obj (op W)),
      φ W' (h.trans hW) (res Q h x) = res P h (φ W hW x))
    {ι : Type w} (U : ι → Opens X) (hU : ∀ a, U a ≤ D) (hQ : CechAcyclic Q U) :
    CechAcyclic P U := by
  have hI : ∀ {m : ℕ} (i : Fin (m + 1) → ι), inter U i ≤ D := fun i =>
    (inter_le U i 0).trans (hU _)
  let push' (m : ℕ) : Cochain Q U m →+ Cochain P U m :=
    { toFun σ i := φ _ (hI i) (σ i)
      map_zero' := by funext i; exact map_zero _
      map_add' σ τ := by funext i; exact map_add _ _ _ }
  have hd : ∀ m σ, d P U m (push' m σ) = push' (m + 1) (d Q U m σ) := by
    intro m σ
    funext i
    rw [d_apply]
    change _ = φ _ (hI i) (d Q U m σ i)
    rw [d_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_zsmul]
    congr 1
    exact (hnat _ (hI (i ∘ a.succAbove)) _).symm
  have hinj : ∀ m, Function.Injective (push' m) := fun m σ τ h => by
    funext i
    exact (hφ _ (hI i)).1 (congrFun h i)
  have hsurj : ∀ m, Function.Surjective (push' m) := fun m σ =>
    ⟨fun i => ((hφ _ (hI i)).2 (σ i)).choose, funext fun i => ((hφ _ (hI i)).2 (σ i)).choose_spec⟩
  intro m σ hσ
  obtain ⟨σQ, rfl⟩ := hsurj _ σ
  have h0 : d Q U (m + 1) σQ = 0 := hinj _ (by rw [← hd, hσ, map_zero])
  obtain ⟨τ, hτ⟩ := hQ m σQ h0
  exact ⟨push' m τ, by rw [hd, hτ]⟩

end Transfer

namespace ProjTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

lemma pow_mem_of_mem_one {u : A} (hu : u ∈ 𝒜 1) (m : ℕ) : u ^ m ∈ 𝒜 m := by
  have := SetLike.pow_mem_graded m hu
  rwa [smul_eq_mul, mul_one] at this

lemma pow_nmem {u : A} {x : ProjectiveSpectrum 𝒜} (hx : u ∉ x.asHomogeneousIdeal) (m : ℕ) :
    u ^ m ∉ x.asHomogeneousIdeal := fun h => hx (x.isPrime.mem_of_pow_mem m h)

def twistFrac (u : A) (k : ℤ) (x : ProjectiveSpectrum 𝒜) (hx : u ∉ x.asHomogeneousIdeal) :
    Loc 𝒜 x :=
  Localization.mk (u ^ k.toNat) ⟨u ^ (-k).toNat, pow_nmem hx _⟩

lemma twistFrac_mul_twistFrac_neg (u : A) (k : ℤ) (x : ProjectiveSpectrum 𝒜)
    (hx : u ∉ x.asHomogeneousIdeal) : twistFrac u k x hx * twistFrac u (-k) x hx = 1 := by
  rw [twistFrac, twistFrac, Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [neg_neg, Submonoid.coe_mul, Submonoid.coe_one, one_mul, mul_one]
  ring

lemma isLocallyFraction_twistFrac {u : A} (hu : u ∈ 𝒜 1) (k : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒜)} (hW : ∀ x : W, u ∉ x.1.asHomogeneousIdeal) :
    (isLocallyFraction 𝒜 k).pred (fun x : W => twistFrac u k x.1 (hW x)) := fun x =>
  ⟨W, x.2, 𝟙 W, (-k).toNat, k.toNat, by omega, u ^ k.toNat, u ^ (-k).toNat,
    pow_mem_of_mem_one hu _, pow_mem_of_mem_one hu _, fun y => pow_nmem (hW y) _, fun _ => rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma isLocallyFraction_val_section {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (t : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op W)) :
    (isLocallyFraction 𝒜 0).pred (fun x : W => (t.1 x).val) := fun x => by
  obtain ⟨V, hxV, iV, j, ⟨r, hr⟩, ⟨s, hs⟩, hsn, w⟩ := t.2 x
  refine ⟨V, hxV, iV, j, j, by simp, r, s, hr, hs, hsn, fun y => ?_⟩
  exact (congrArg HomogeneousLocalization.val (w y)).trans (HomogeneousLocalization.val_mk _)

def twistMap {u : A} (hu : u ∈ 𝒜 1) (k : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : ∀ x : W, u ∉ x.1.asHomogeneousIdeal) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op W) →+
      (twistPresheafAb 𝒜 k).obj (op W) where
  toFun t := ⟨fun x => twistFrac u k x.1 (hW x) * (t.1 x).val,
    isLocallyFraction_mul (add_zero k) (isLocallyFraction_twistFrac hu k hW)
      (isLocallyFraction_val_section t)⟩
  map_zero' := Subtype.ext (funext fun x => by
    change twistFrac u k x.1 (hW x) * HomogeneousLocalization.val 0 = 0
    rw [HomogeneousLocalization.val_zero, mul_zero])
  map_add' t t' := Subtype.ext (funext fun x => by
    change twistFrac u k x.1 (hW x) * HomogeneousLocalization.val (t.1 x + t'.1 x) =
      twistFrac u k x.1 (hW x) * (t.1 x).val + twistFrac u k x.1 (hW x) * (t'.1 x).val
    rw [HomogeneousLocalization.val_add, mul_add])

lemma twistMap_apply {u : A} (hu : u ∈ 𝒜 1) (k : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : ∀ x : W, u ∉ x.1.asHomogeneousIdeal)
    (t : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op W)) (x : W) :
    (twistMap hu k hW t).1 x = twistFrac u k x.1 (hW x) * (t.1 x).val := rfl

lemma twistMap_bijective {u : A} (hu : u ∈ 𝒜 1) (k : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : ∀ x : W, u ∉ x.1.asHomogeneousIdeal) : Function.Bijective (twistMap hu k hW) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    apply Subtype.ext
    funext x
    apply HomogeneousLocalization.val_injective
    have h1 : twistFrac u k x.1 (hW x) * (t.1 x).val = 0 := congrFun (congrArg Subtype.val ht) x
    have h2 := twistFrac_mul_twistFrac_neg u k x.1 (hW x)
    refine (show (t.1 x).val = 0 from ?_).trans HomogeneousLocalization.val_zero.symm
    calc (t.1 x).val = twistFrac u (-k) x.1 (hW x) * (twistFrac u k x.1 (hW x) * (t.1 x).val) := by
          linear_combination (-(t.1 x).val) * h2
      _ = 0 := by rw [h1, mul_zero]
  · intro s
    have hf := isLocallyFraction_mul (neg_add_cancel k) (isLocallyFraction_twistFrac hu (-k) hW) s.2
    obtain ⟨t, ht⟩ := exists_section_of_isLocallyFraction_zero _ hf
    refine ⟨t, Subtype.ext (funext fun x => ?_)⟩
    rw [twistMap_apply, ht x]
    change twistFrac u k x.1 (hW x) * (twistFrac u (-k) x.1 (hW x) * s.1 x) = s.1 x
    linear_combination (s.1 x) * twistFrac_mul_twistFrac_neg u k x.1 (hW x)

end ProjTwist

section Leray

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

open ProjTwist

def AffineUnder {ι : Type w} (v : ι → A) (V : (Proj 𝒜).Opens) : Prop :=
  IsAffineOpen V ∧ ∃ j, V ≤ Proj.basicOpen 𝒜 (v j)

lemma isCoverSystem_affineUnder {ι : Type w} (v : ι → A) :
    IsCoverSystem (X := (Proj 𝒜).toTopCat) (AffineUnder v)
      (fun {κ} V U => IsBasicCover (κ := κ) V U ∧ AffineUnder v V) where
  iSup_eq V κ U hU := isCoverSystem_isBasicCover.iSup_eq V U hU.1
  inter_mem V κ U hU n i := by
    refine ⟨isCoverSystem_isBasicCover.inter_mem V U hU.1 i, ?_⟩
    obtain ⟨j, hj⟩ := hU.2.2
    refine ⟨j, (inter_le U i 0).trans ((le_iSup U (i 0)).trans ?_)⟩
    exact (isCoverSystem_isBasicCover.iSup_eq V U hU.1).le.trans hj
  exists_refinement V hV O hO := by
    obtain ⟨κ, hκ, U, hU, hsub⟩ := isCoverSystem_isBasicCover.exists_refinement V hV.1 O hO
    exact ⟨κ, hκ, U, ⟨hU, hV⟩, hsub⟩

lemma goodAcyclic_twist {ι : Type w} (v : ι → A) (hv : ∀ j, v j ∈ 𝒜 1) (k : ℤ) :
    GoodAcyclic (X := (Proj 𝒜).toTopCat) (AffineUnder v)
      (fun {κ} V U => IsBasicCover (κ := κ) V U ∧ AffineUnder v V)
      (modulesAb (twistingSheaf 𝒜 k)) := by
  intro V hV κ _ U hU
  obtain ⟨j, hj⟩ := hV.2
  have hUV : ∀ a, U a ≤ V := fun a =>
    (le_iSup U a).trans (isCoverSystem_isBasicCover.iSup_eq V U hU.1).le
  refine cechAcyclic_of_bijective_le
    (Q := (modulesAb (SheafOfModules.unit (Proj 𝒜).ringCatSheaf)).obj)
    (D := Proj.basicOpen 𝒜 (v j))
    (fun W hW => twistMap (hv j) k (W := W) (fun x => hW x.2))
    (fun W hW => twistMap_bijective _ _ _) ?_ U (fun a => (hUV a).trans hj)
    (cechAcyclic_of_isBasicCover _ hU.1)
  intro W W' h hW x
  rfl

lemma inter_basicOpen_eq {ι : Type w} (v : ι → A) {m : ℕ} (i : Fin (m + 1) → ι) :
    inter (X := (Proj 𝒜).toTopCat) (fun j => Proj.basicOpen 𝒜 (v j)) i =
      Proj.basicOpen 𝒜 (∏ a, v (i a)) := by
  ext x
  change x ∈ inter (X := (Proj 𝒜).toTopCat) (fun j => Proj.basicOpen 𝒜 (v j)) i ↔ _
  rw [mem_inter_iff]
  change (∀ a, v (i a) ∉ x.asHomogeneousIdeal.toIdeal) ↔
    (∏ a, v (i a)) ∉ x.asHomogeneousIdeal.toIdeal
  have := x.isPrime
  rw [Ideal.IsPrime.prod_mem_iff]
  simp

theorem nonempty_cechH_equiv_H_twist {ι : Type w} (v : ι → A) (hv : ∀ j, v j ∈ 𝒜 1)
    (hcov : ⨆ j, Proj.basicOpen 𝒜 (v j) = ⊤) (k : ℤ) (p : ℕ)
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (Proj 𝒜).toTopCat) AddCommGrpCat.{u})] :
    Nonempty (cechH (modulesAb (twistingSheaf 𝒜 k)).obj
      (X := (Proj 𝒜).toTopCat) (fun j => Proj.basicOpen 𝒜 (v j)) p ≃+
        Sheaf.H.{w'} (modulesAb (twistingSheaf 𝒜 k)) p) := by
  refine nonempty_cechH_equiv (isCoverSystem_affineUnder v) _ hcov (fun {m} i => ⟨?_, ⟨i 0,
    inter_le _ i 0⟩⟩) p _ (goodAcyclic_twist v hv k)
  rw [inter_basicOpen_eq]
  have hmem : ∏ a, v (i a) ∈ 𝒜 (m + 1) := by
    have := SetLike.prod_mem_graded 𝒜 (fun _ => 1) (fun a => v (i a))
      (F := (Finset.univ : Finset (Fin (m + 1)))) (fun a _ => hv (i a))
    simpa using this
  exact Proj.isAffineOpen_basicOpen 𝒜 _ hmem (Nat.succ_pos m)

end Leray

namespace ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {n : ℕ}

theorem nonempty_cechH_equiv_H (k : ℤ) (p : ℕ)
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat)
      AddCommGrpCat.{u})] :
    Nonempty (cechH (twistAb A n k) (cover A n) p ≃+
      Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) p) :=
  nonempty_cechH_equiv_H_twist (fun j => MvPolynomial.X j) (fun j => X_mem j) iSup_stdOpen k p

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
