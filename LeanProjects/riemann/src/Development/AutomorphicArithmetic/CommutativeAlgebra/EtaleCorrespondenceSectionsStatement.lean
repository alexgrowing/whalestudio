import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsSeparatedOfProj
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFunctionFieldStatementOne
import Development.AutomorphicArithmetic.CommutativeAlgebra.ComplexPointsBijectiveAlgHomAffineOpen
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

private theorem germ_ex {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (e : V = W) (hV : genericPoint X ∈ V)
    (hW : genericPoint X ∈ W) (y : X.functionField) :
    (∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hV).hom f = y) ↔
      ∃ f : Γ(X, W), (X.presheaf.germ W (genericPoint X) hW).hom f = y := by
  subst e; rfl

private theorem ring_single {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type}
    {U : ι → X.Opens} {B : Finset ι → Subalgebra ℂ X.functionField} (h : IsAffCover p U B) (i : ι)
    (hg : genericPoint X ∈ U i) (y : X.functionField) :
    y ∈ B {i} ↔ ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = y :=
  (h.ring {i} ⟨i, by simp⟩ y).trans (germ_ex (Finset.inf_singleton ..) _ _ y)

private theorem clear_denom {Y : Scheme.{0}} [IsIntegral Y] (s' : Y ⟶ Sp ℂ) [Algebra ℂ Y.functionField] {A W : Y.Opens}
    (hA : IsAffineOpen A) (gA : genericPoint Y ∈ A) (gW : genericPoint Y ∈ W) (B : Subalgebra ℂ Y.functionField)
    (hB : ∀ y, y ∈ B ↔ ∃ f : Γ(Y, A), (Y.presheaf.germ A (genericPoint Y) gA).hom f = y) (e : B →ₐ[ℂ] ℂ)
    (y : CxPts s' (RingHom.id ℂ)) (hM : UpperTheory.A.Mt s' A gA B e y) (hyW : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) W)
    (f : Γ(Y, W)) :
    ∃ (b : Y.functionField) (hb : b ∈ B), e ⟨b, hb⟩ ≠ 0 ∧
      b * (Y.presheaf.germ W (genericPoint Y) gW).hom f ∈ B := by
  obtain ⟨hyA, hev⟩ := hM
  obtain ⟨h, hhW, hh⟩ := hA.exists_basicOpen_le (V := W) ⟨_, CxPts.mem_ptsIn.1 hyW⟩ (CxPts.mem_ptsIn.1 hyA)
  have hD : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (Y.basicOpen h) := CxPts.mem_ptsIn.2 hh
  have hne := (CxPts.mem_ptsIn_basicOpen hyA h).1 hD
  have gD : genericPoint Y ∈ Y.basicOpen h :=
    ((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen h).isOpen).2 ⟨_, trivial, hh⟩
  have := hA.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h ((Y.presheaf.map (homOfLE hhW).op).hom f)
  have hb : (Y.presheaf.germ A (genericPoint Y) gA).hom (h ^ n) ∈ B := (hB _).2 ⟨_, rfl⟩
  refine ⟨_, hb, ?_, (hB _).2 ⟨a, ?_⟩⟩
  · rw [hev (h ^ n) hb, CxPts.ev_eq hyA, map_pow, ← CxPts.ev_eq hyA]
    exact pow_ne_zero n hne
  · have e1 := congrArg (Y.presheaf.germ (Y.basicOpen h) (genericPoint Y) gD).hom ha
    have e2 : ∀ g : Γ(Y, A), (Y.presheaf.germ (Y.basicOpen h) (genericPoint Y) gD).hom (algebraMap Γ(Y, A) Γ(Y, Y.basicOpen h) g)
        = (Y.presheaf.germ A (genericPoint Y) gA).hom g := fun g =>
      Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le h)) (genericPoint Y) gD g
    have e3 : (Y.presheaf.germ (Y.basicOpen h) (genericPoint Y) gD).hom ((Y.presheaf.map (homOfLE hhW).op).hom f)
        = (Y.presheaf.germ W (genericPoint Y) gW).hom f :=
      Y.presheaf.germ_res_apply (homOfLE hhW) (genericPoint Y) gD f
    rw [map_mul, map_pow, e2, e2, e3] at e1
    rw [map_pow, mul_comm]
    exact e1.symm

theorem UpperTheory.etaleCorrespondence_sections_statement :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)) (i : Fin (d + 1)) (e : rB ℂ Y.functionField x {i} →ₐ[ℂ] ℂ), ∃ j : Fin (d + 1), ∀ v ∈ R2 x j2 {j}, ∃ (b : Y.functionField) (hb : b ∈ rB ℂ Y.functionField x {i}), e ⟨b, hb⟩ ≠ 0 ∧ b * v ∈ rB ℂ Y.functionField x {i} := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU i e
  obtain ⟨-, hU1⟩ := UpperTheory.A.isFinCover_pull h1 hK hL g1 hx hU
  have hU2 := UpperTheory.etaleCorrespondence_functionField_statement_one d Z Y s s' hP c1 c2 h1 h2 hK hL g1 j2 g2 F x U hx hU
  have gen : ∀ (c : Y ⟶ Z) [Etale c] (k : Fin (d + 1)), genericPoint Y ∈ c ⁻¹ᵁ U k := fun c _ k => by
    change c (genericPoint Y) ∈ U k
    rw [UpperTheory.A.generic_map c]
    simpa using hU.ne {k}
  have hA : IsAffineOpen (c1 ⁻¹ᵁ U i) := by simpa using hU1.affine {i} ⟨i, by simp⟩
  have hB := ring_single hU1 i (gen c1 i)
  obtain ⟨y, hy, -⟩ := (UpperTheory.complexPoints_bijective_algHom_affineOpen Y s' hL _ hA (gen c1 i) _ hB).1 e
  obtain ⟨j, hj⟩ := CxPts.exists_mem_ptsIn hU.cover (UpperTheory.A.zpt c2 h2 y)
  have hyW : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c2 ⁻¹ᵁ U j) := by
    refine CxPts.mem_ptsIn.2 ?_
    exact CxPts.mem_ptsIn.1 hj
  refine ⟨j, fun v hv => ?_⟩
  obtain ⟨f, rfl⟩ := (ring_single hU2 j (gen c2 j) v).1 hv
  exact clear_denom s' hA (gen c1 i) (gen c2 j) _ hB e y hy hyW f
