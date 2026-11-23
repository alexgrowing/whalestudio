import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifAfterFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8invTranspose

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.UnitValuedLeadingSection

variable (R : Type) [CommRing R] [IsDomain R]

def thK (z : (TK R).left) : FractionRing R →+* (TK R).left.presheaf.stalk z :=
  ((TK R).left.presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

def uK (z : (TK R).left) : Rˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
  Units.map ((thK R z).comp (algebraMap R (FractionRing R))).toMonoidHom

variable {R}

def TopGood (P : PolAV (Spec (CommRingCat.of R))) (z : (TK R).left) (J : ((TK R).left ⟶ P.A.left) → P.L.ι) : Prop :=
  Good P.L z J ∧ ∀ x : Spec (CommRingCat.of R) ⟶ P.A.left, x ≫ P.A.hom = 𝟙 _ → x ⁻¹ᵁ P.L.U (J (jK R ≫ x)) = ⊤

theorem gm_top_unit {R : Type} [CommRing R] [IsDomain R] (V : (Spec (CommRingCat.of R)).Opens) (hV : V = ⊤)
    (v : Γ(Spec (CommRingCat.of R), V)ˣ) (z : (TK R).left) : ∃ u : Rˣ, gm (jK R) z V v = uK R z u := by
  subst hV
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom v, Units.ext ?_⟩
  have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
  simp only [gm, dif_pos hz]
  have e := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (v : Γ(Spec (CommRingCat.of R), ⊤))))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp [uK, thK, pullU]
  rw [CommRingCat.hom_ofHom] at e
  have hv : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (v : Γ(Spec (CommRingCat.of R), ⊤))) = v := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  rw [e, hv]
  rfl

theorem val_section_unit {R : Type} [CommRing R] [IsDomain R] (P : PolAV (Spec (CommRingCat.of R)))
    (z : (TK R).left) (J : ((TK R).left ⟶ P.A.left) → P.L.ι) (hJ : TopGood P z J) {Y : Scheme.{0}} {K : Type}
    [Fintype K] {φ : K → (Y ⟶ P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb P.L φ ε))
    (q : Spec (CommRingCat.of R) ⟶ Y) (hq : ∀ k, (q ≫ φ k) ≫ P.A.hom = 𝟙 _) :
    ∃ u : Rˣ, val t (jK R ≫ q) z J = uK R z u := by
  have htop : q ⁻¹ᵁ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) = ⊤ := by
    refine eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => ?_
    have h := hJ.2 (q ≫ φ k) (hq k)
    have : p ∈ (q ≫ φ k) ⁻¹ᵁ P.L.U (J (jK R ≫ q ≫ φ k)) := by rw [h]; trivial
    show q p ∈ (φ k) ⁻¹ᵁ P.L.U (J ((jK R ≫ q) ≫ φ k))
    rw [Category.assoc]
    exact this
  have hz : q (jK R z) ∈ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) := by
    have : jK R z ∈ q ⁻¹ᵁ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) := by rw [htop]; trivial
    exact this
  obtain ⟨u, hu⟩ := gm_top_unit _ htop (pullU q _ (t.s (fun k => J ((jK R ≫ q) ≫ φ k)))) z
  exact ⟨u, (gm_pull (jK R) q z _ hz _).symm.trans hu⟩

theorem exists_topGood (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (P : PolAV (Spec (CommRingCat.of R)))
    (z : (TK R).left) : ∃ J, TopGood P z J := by
  classical
  haveI : IsProper P.A.hom := P.isAb.proper
  haveI : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)⟩
  have hext : ∀ x x' : Spec (CommRingCat.of R) ⟶ P.A.left, x ≫ P.A.hom = 𝟙 _ → x' ≫ P.A.hom = 𝟙 _ →
      jK R ≫ x = jK R ≫ x' → x = x' := fun x x' hx hx' h =>
    ext_of_isDominant_of_isSeparated P.A.hom (hx.trans hx'.symm) (jK R) h
  choose top htop using fun x : Spec (CommRingCat.of R) ⟶ P.A.left =>
    ReciprocityTheory.ChartRestriction.G.DVR.GC.exists_chart_top P.L P.isLB x
  choose d hd using fun φ : (TK R).left ⟶ P.A.left => exists_chart P.isLB (φ z)
  refine ⟨fun φ => if h : ∃ x, x ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x = φ then top h.choose else d φ,
    fun φ => ?_, fun x hx => ?_⟩
  · by_cases h : ∃ x, x ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x = φ
    · simp only [dif_pos h]
      have m : jK R z ∈ h.choose ⁻¹ᵁ P.L.U (top h.choose) := by rw [htop]; trivial
      have m' : (jK R ≫ h.choose) z ∈ P.L.U (top h.choose) := m
      rwa [h.choose_spec.2] at m'
    · simp only [dif_neg h]; exact hd φ
  · have h : ∃ x', x' ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x' = jK R ≫ x := ⟨x, hx, rfl⟩
    simp only [dif_pos h]
    rw [hext _ _ h.choose_spec.1 hx h.choose_spec.2]
    exact htop x

end GlobalTheory.Mum.UnitValuedLeadingSection
