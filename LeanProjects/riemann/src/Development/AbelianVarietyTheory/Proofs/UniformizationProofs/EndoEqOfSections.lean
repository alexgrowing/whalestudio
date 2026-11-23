import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.AutUniq

theorem hom_eq_of_sval {X X' Y B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (X ⟶ Y)} {ε : K → ℤ}
    {M : ℕ} (s : Fin (M + 1) → LB.Sec (LB.LinComb L φ ε)) (f : X ⟶ B) (p q : X' ⟶ X) (hf : p ≫ f = q ≫ f)
    (hcov : ⨆ i, nonzeroLocus (s i) = ⊤) (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (M + 1) → Γ(X, nonzeroLocus (s i))) (hr : ∀ i j, AmpleSpan.IsRatio (s j) (s i) (r i j))
    (hsurj : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus (s i)) le_top).hom (r i)))
    (h : ∀ z : X', ∃ J, Good L z J ∧ ∃ u : (X'.presheaf.stalk z)ˣ, ∀ j, sval (s j) q z J = u.val * sval (s j) p z J) :
    p = q := by
  have mem : ∀ (χ : X' ⟶ X) i z J, Good L z J → (χ z ∈ nonzeroLocus (s i) ↔ IsUnit (sval (s i) χ z J)) :=
    fun χ i z J hJ => AmpleSpan.mem_nonzeroLocus_iff_gs (s i) χ z (hJ.mem φ χ)
  have rat : ∀ (χ : X' ⟶ X) i j z J, Good L z J → χ z ∈ nonzeroLocus (s i) →
      sval (s j) χ z J = gs χ z _ (r i j) * sval (s i) χ z J :=
    fun χ i j z J hJ hz => (hr i j).gs χ z hz (hJ.mem φ χ)
  have hm : ∀ i z, p z ∈ nonzeroLocus (s i) → q z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨J, hJ, u, hu⟩ := h z
    rw [mem q i z J hJ, hu]
    exact u.isUnit.mul ((mem p i z J hJ).1 hz)
  refine MapUniq.hom_ext_of_gs (fun i => nonzeroLocus (s i)) haff hcov p q hm fun i z hz a => ?_
  have hz' := hm i z hz
  obtain ⟨J, hJ, u, hu⟩ := h z
  have hrr : ∀ j, gs p z _ (r i j) = gs q z _ (r i j) := fun j => by
    have e := rat q i j z J hJ hz'
    rw [hu, hu, rat p i j z J hJ hz, mul_left_comm] at e
    have e' := (Units.mul_right_inj _).1 ((mul_left_comm _ _ _).trans e |>.trans (mul_left_comm _ _ _))
    exact ((mem p i z J hJ).1 hz).mul_right_cancel e'
  have cst : ∀ (χ : X' ⟶ X), χ z ∈ nonzeroLocus (s i) → ∀ c : Γ(B, ⊤),
      gs χ z _ ((f.appLE ⊤ (nonzeroLocus (s i)) le_top).hom c) = gs (χ ≫ f) z ⊤ c := fun χ hχ c =>
    (gs_res χ z le_top hχ _).trans (gs_pull χ f z ⊤ trivial _)
  obtain ⟨P, rfl⟩ := hsurj i a
  induction P using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, cst p hz, cst q hz', hf]
  | add P Q hP hQ => rw [map_add, gs_add p z _ hz, gs_add q z _ hz', hP, hQ]
  | mul_X P j hP => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul p z _ hz, gs_mul q z _ hz', hP, hrr]

theorem eq_of_twistPull {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (hS : IsAffineOpen (⊤ : S.Opens)) {n : ℕ} (hV : VeryAmpleAt A L n) {T : Over S} (ψ ψ' : T ⊗ A ⟶ T ⊗ A)
    (h₁ : ψ ≫ fst _ _ = fst _ _) (h₂ : ψ' ≫ fst _ _ = fst _ _)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![(n : ℤ), -(n : ℤ)]))
    (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ' ≫ snd _ _).left] ![(n : ℤ), -(n : ℤ)]))
    (hα : α.IsGen) (hα' : α'.IsGen) (c : Γ(T.left, ⊤)ˣ)
    (H : ∀ t t₁ t₂ : LB.Sec (LPow A L n T), IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t t₁ →
      IsTwistPull A L ψ' (ψ' ≫ snd _ _) rfl n n α' t t₂ → ∀ j, t₂.f j = liftFun A _ c.val * t₁.f j) : ψ = ψ' := by
  obtain ⟨M, s, hcov, haff⟩ := hV ⊤ hS
  choose r hr hsurj using fun i => (haff i).2
  obtain ⟨i', hi⟩ : ∃ i' : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.left.topIso.inv, A.left.topIso.inv_hom_id⟩
  have sec : ∀ j, ∃ v : LB.Sec (LPow A L n T), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → VVRank.sv A v r z J =
        sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
          (r ≫ (snd T A).left ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ := fun _ : Fin n => (snd T A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => (n : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd T A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
    exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (VVRank.sval_pullTo _ _ _ r z hJ)⟩
  choose v hv using sec
  have key : ψ.left ≫ (snd T A).left ≫ i' = ψ'.left ≫ (snd T A).left ≫ i' := by
    refine hom_eq_of_sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s (A.hom ∣_ ⊤) _ _ ?_
      hcov (fun i => (haff i).1) r hr hsurj fun y => ?_
    · rw [← cancel_mono (⊤ : S.Opens).ι]
      simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hi, Over.w]
    · choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
      refine ⟨J, hJ, (val α' (𝟙 _) y J)⁻¹ * gm (𝟙 _ ≫ (fst T A).left) y ⊤ c * val α (𝟙 _) y J, fun j => ?_⟩
      obtain ⟨t₁, ht₁⟩ := VVRank.exists_isTwistPull A (hm := rfl) hL hα (v j)
      obtain ⟨t₂, ht₂⟩ := VVRank.exists_isTwistPull A (hm := rfl) hL hα' (v j)
      have e₁ := VVRank.sv_of_isTwistPull A ht₁ (𝟙 _) y hJ
      have e₂ := VVRank.sv_of_isTwistPull A ht₂ (𝟙 _) y hJ
      have hy := Good.mem hJ (fun _ : Fin 1 => (snd T A).left) (𝟙 (T ⊗ A).left)
      have e₃ : VVRank.sv A t₂ (𝟙 _) y J =
          (gm (𝟙 _ ≫ (fst T A).left) y ⊤ c).val * VVRank.sv A t₁ (𝟙 _) y J :=
        (congrArg (gs (𝟙 _) y _) (H _ _ _ ht₁ ht₂ _)).trans ((gs_mul _ y _ hy _ _).trans
          (congrArg (· * _) ((gs_res _ y le_top hy _).trans ((gs_pull _ _ y ⊤ trivial _).trans
            (gs_unit _ y ⊤ trivial c)))))
      rw [hv _ _ _ _ _ hJ, Category.id_comp] at e₁ e₂
      rw [Units.val_mul, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← e₁, ← e₃, e₂, Units.inv_mul_cancel_left]
  refine CartesianMonoidalCategory.hom_ext _ _ (h₁.trans h₂.symm) (Over.OverMorphism.ext ?_)
  have := congrArg (fun q => q ≫ (A.hom ⁻¹ᵁ ⊤).ι) key
  simpa only [Category.assoc, hi, Category.comp_id, Over.comp_left] using this

theorem endo_eq_of_sections : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ), 4 ≤ N → ∀ (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), ψ ≫ fst _ _ = fst _ _ → ψ' ≫ fst _ _ = fst _ _ → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (ψ ≫ snd _ _).left] ![(N : ℤ), -(N : ℤ)])) (α' : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (ψ' ≫ snd _ _).left] ![(N : ℤ), -(N : ℤ)])), α.IsGen → α'.IsGen → ∀ c : Γ((TFK (R := R) F).left, ⊤)ˣ, (∀ t t₁ t₂ : SecA A F N, IsTwistPull A.A A.L ψ (ψ ≫ snd _ _) rfl N N α t t₁ → IsTwistPull A.A A.L ψ' (ψ' ≫ snd _ _) rfl N N α' t t₂ → ∀ j, t₂.f j = liftFun A.A _ c.val * t₁.f j) → ψ = ψ' := by
  intro hL R _ _ A F _ _ N hN ψ ψ' h₁ h₂ α α' hα hα' c H
  exact eq_of_twistPull A.isLB (isAffineOpen_top _) (hL.1.ample _ A N hN).2 ψ ψ' h₁ h₂ α α' hα hα' c H

end GlobalTheory.AutUniq
