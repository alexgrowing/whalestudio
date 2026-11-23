import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitAnalyticFunction
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsSeparatedOfProj
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

set_option autoImplicit false

namespace UpperTheory.FixIff

section Local

variable {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp ℂ}

private theorem germ_resG {W W' : Y.Opens} (h : W ≤ W') (hW : genericPoint Y ∈ W) (hW' : genericPoint Y ∈ W')
    (f : Γ(Y, W')) :
    (Y.presheaf.germ W (genericPoint Y) hW).hom (resG Y h f) = (Y.presheaf.germ W' (genericPoint Y) hW').hom f :=
  Y.presheaf.germ_res_apply (homOfLE h) (genericPoint Y) hW f

private theorem generic_mem_of_pt {W : Y.Opens} {y : CxPts p (RingHom.id ℂ)}
    (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) W) : genericPoint Y ∈ W :=
  ((genericPoint_spec Y).mem_open_set_iff W.isOpen).2 ⟨_, trivial, CxPts.mem_ptsIn.1 hy⟩

private theorem ev_germ_mul {W1 W2 W3 : Y.Opens} (g1 : genericPoint Y ∈ W1) (g2 : genericPoint Y ∈ W2)
    (g3 : genericPoint Y ∈ W3) (a : Γ(Y, W1)) (b : Γ(Y, W2)) (c : Γ(Y, W3)) (y : CxPts p (RingHom.id ℂ))
    (y1 : y ∈ CxPts.ptsIn p (RingHom.id ℂ) W1) (y2 : y ∈ CxPts.ptsIn p (RingHom.id ℂ) W2)
    (y3 : y ∈ CxPts.ptsIn p (RingHom.id ℂ) W3)
    (e : (Y.presheaf.germ W1 (genericPoint Y) g1).hom a * (Y.presheaf.germ W2 (genericPoint Y) g2).hom b =
      (Y.presheaf.germ W3 (genericPoint Y) g3).hom c) :
    CxPts.ev p (RingHom.id ℂ) W1 a y * CxPts.ev p (RingHom.id ℂ) W2 b y = CxPts.ev p (RingHom.id ℂ) W3 c y := by
  have hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (W1 ⊓ W2 ⊓ W3) :=
    CxPts.mem_ptsIn_inf.2 ⟨CxPts.mem_ptsIn_inf.2 ⟨y1, y2⟩, y3⟩
  have hg : genericPoint Y ∈ W1 ⊓ W2 ⊓ W3 := generic_mem_of_pt hy
  have l1 : W1 ⊓ W2 ⊓ W3 ≤ W1 := inf_le_left.trans inf_le_left
  have l2 : W1 ⊓ W2 ⊓ W3 ≤ W2 := inf_le_left.trans inf_le_right
  have l3 : W1 ⊓ W2 ⊓ W3 ≤ W3 := inf_le_right
  have h : resG Y l1 a * resG Y l2 b = resG Y l3 c := by
    apply germ_injective_of_isIntegral Y (genericPoint Y) hg
    rw [map_mul, germ_resG l1 hg g1, germ_resG l2 hg g2, germ_resG l3 hg g3, e]
  have := congrArg (CxPts.evHom hy) h
  rw [map_mul, ← CxPts.ev_eq, ← CxPts.ev_eq, ← CxPts.ev_eq, CxPts.ev_res _ hy, CxPts.ev_res _ hy, CxPts.ev_res _ hy] at this
  exact this

variable [Algebra ℂ Y.functionField] {V W : Y.Opens} {hg : genericPoint Y ∈ V} {B : Subalgebra ℂ Y.functionField}
  {e : B →ₐ[ℂ] ℂ} {y : CxPts p (RingHom.id ℂ)}

private theorem val_of_regular (hV : IsAffineOpen V)
    (hB : ∀ v, v ∈ B ↔ ∃ f : Γ(Y, V), (Y.presheaf.germ V (genericPoint Y) hg).hom f = v)
    (hM : UpperTheory.A.Mt p V hg B e y) (g : Γ(Y, W)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) W) (hW : genericPoint Y ∈ W) :
    Val B e ((Y.presheaf.germ W (genericPoint Y) hW).hom g) (CxPts.ev p (RingHom.id ℂ) W g y) := by
  obtain ⟨β, hβW, hβy⟩ := hV.exists_basicOpen_le (V := W) ⟨_, CxPts.mem_ptsIn.1 hy⟩ (CxPts.mem_ptsIn.1 hM.1)
  have hyD : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (Y.basicOpen β) := CxPts.mem_ptsIn.2 hβy
  have hgD : genericPoint Y ∈ Y.basicOpen β := generic_mem_of_pt hyD
  have := hV.isLocalization_basicOpen β
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj β (resG Y hβW g)
  have ha' : resG Y hβW g * resG Y (Y.basicOpen_le β) β ^ n = resG Y (Y.basicOpen_le β) a := ha
  set G := (Y.presheaf.germ V (genericPoint Y) hg).hom with hG
  have e1 : G (β ^ n) * (Y.presheaf.germ W (genericPoint Y) hW).hom g = G a := by
    have := congrArg (Y.presheaf.germ _ (genericPoint Y) hgD).hom ha'
    rw [map_mul, map_pow, germ_resG hβW hgD hW, germ_resG _ hgD hg, germ_resG _ hgD hg] at this
    rw [← this, map_pow]
    exact mul_comm _ _
  have hb : G (β ^ n) ∈ B := (hB _).2 ⟨_, rfl⟩
  have hbv : G (β ^ n) * (Y.presheaf.germ W (genericPoint Y) hW).hom g ∈ B := e1 ▸ (hB _).2 ⟨a, rfl⟩
  have hne : CxPts.ev p (RingHom.id ℂ) V (β ^ n) y ≠ 0 := by
    rw [CxPts.ev_eq hM.1, map_pow, ← CxPts.ev_eq hM.1]
    exact pow_ne_zero n ((CxPts.mem_ptsIn_basicOpen hM.1 β).1 hyD)
  refine ⟨_, hb, hbv, ?_, ?_⟩
  · rw [hM.2 (β ^ n) hb]; exact hne
  · rw [hM.2 (β ^ n) hb]
    have h2 : e ⟨_, hbv⟩ = CxPts.ev p (RingHom.id ℂ) V a y := by
      rw [← hM.2 a ((hB _).2 ⟨a, rfl⟩)]
      exact congrArg e (Subtype.ext e1)
    rw [h2]
    exact (ev_germ_mul hg hW hg _ _ _ y hM.1 hy hM.1 e1).symm

private theorem val_unique
    (hB : ∀ v, v ∈ B ↔ ∃ f : Γ(Y, V), (Y.presheaf.germ V (genericPoint Y) hg).hom f = v)
    (hM : UpperTheory.A.Mt p V hg B e y) (g : Γ(Y, W)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) W) (hW : genericPoint Y ∈ W)
    {c : ℂ} (hc : Val B e ((Y.presheaf.germ W (genericPoint Y) hW).hom g) c) :
    c = CxPts.ev p (RingHom.id ℂ) W g y := by
  obtain ⟨b, hb, hbv, hne, hv⟩ := hc
  obtain ⟨f1, rfl⟩ := (hB b).1 hb
  obtain ⟨f2, h2⟩ := (hB _).1 hbv
  have m := ev_germ_mul hg hW hg f1 g f2 y hM.1 hy hM.1 h2.symm
  have v1 := hM.2 f1 hb
  have v2 : e ⟨_, hbv⟩ = CxPts.ev p (RingHom.id ℂ) V f2 y := by
    rw [← hM.2 f2 ((hB _).2 ⟨f2, rfl⟩)]
    exact congrArg e (Subtype.ext h2.symm)
  rw [v2, v1, ← m] at hv
  rw [v1] at hne
  exact (mul_left_cancel₀ hne hv).symm

private theorem ne_zero_of_val
    (hB : ∀ v, v ∈ B ↔ ∃ f : Γ(Y, V), (Y.presheaf.germ V (genericPoint Y) hg).hom f = v)
    (hM : UpperTheory.A.Mt p V hg B e y) (g : Γ(Y, W)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) W) (hW : genericPoint Y ∈ W)
    {v : Y.functionField} {c : ℂ} (hc : Val B e v c)
    (hv : (Y.presheaf.germ W (genericPoint Y) hW).hom g * v = 1) :
    CxPts.ev p (RingHom.id ℂ) W g y ≠ 0 := by
  obtain ⟨b, hb, hbv, hne, -⟩ := hc
  obtain ⟨f1, rfl⟩ := (hB b).1 hb
  obtain ⟨f2, h2⟩ := (hB _).1 hbv
  have e1 : (Y.presheaf.germ W (genericPoint Y) hW).hom g * (Y.presheaf.germ V (genericPoint Y) hg).hom f2 =
      (Y.presheaf.germ V (genericPoint Y) hg).hom f1 := by
    rw [h2, mul_left_comm, hv, mul_one]
  have m := ev_germ_mul hW hg hg g f2 f1 y hy hM.1 hM.1 e1
  rw [hM.2 f1 hb, ← m] at hne
  exact left_ne_zero_of_mul hne

end Local

section Chart

variable {Z : Scheme.{0}} [IsIntegral Z] {s : Z ⟶ Sp ℂ} [Algebra ℂ Z.functionField] {F : Type} [Field F] [Algebra ℂ F]
  [Algebra F Z.functionField] [IsScalarTower ℂ F Z.functionField] {d : ℕ} {x : Fin (d + 1) → F}
  {U : Fin (d + 1) → Z.Opens}

private theorem ring_of_eq (hU : IsAffCover s U (rB ℂ Z.functionField x)) (I : Finset (Fin (d + 1))) (hI : I.Nonempty)
    (V' : Z.Opens) (e : V' = I.inf U) (hV' : genericPoint Z ∈ V') (b : Z.functionField) :
    b ∈ rB ℂ Z.functionField x I ↔ ∃ f : Γ(Z, V'), (Z.presheaf.germ V' (genericPoint Z) hV').hom f = b := by
  subst e
  exact hU.ring I hI b

private theorem ratio_mem (I : Finset (Fin (d + 1))) (i j : Fin (d + 1)) (hi : i ∈ I) :
    algebraMap F Z.functionField (x j / x i) ∈ rB ℂ Z.functionField x I :=
  (integralClosure (rA ℂ x I) Z.functionField).algebraMap_mem ⟨x j / x i, Algebra.subset_adjoin ⟨i, hi, j, rfl⟩⟩

private theorem mem_chart_of_ne_zero (hx : IsFinCover ℂ Z.functionField x)
    (hU : IsAffCover s U (rB ℂ Z.functionField x)) (l i : Fin (d + 1)) (P : CxPts s (RingHom.id ℂ))
    (hP : P ∈ CxPts.ptsIn s (RingHom.id ℂ) (U l)) (wf : Γ(Z, U l)) (hgl : genericPoint Z ∈ U l)
    (hw : (Z.presheaf.germ (U l) (genericPoint Z) hgl).hom wf = algebraMap F Z.functionField (x i / x l))
    (hne : CxPts.ev s (RingHom.id ℂ) (U l) wf P ≠ 0) : P ∈ CxPts.ptsIn s (RingHom.id ℂ) (U i) := by
  by_cases hli : l = i
  · subst hli; exact hP
  have eW : U l ⊓ U i = ({l, i} : Finset (Fin (d + 1))).inf U := by simp
  have hW : IsAffineOpen (U l ⊓ U i) := eW ▸ hU.affine {l, i} ⟨l, by simp⟩
  have hUl : IsAffineOpen (U l) := by simpa using hU.affine {l} ⟨l, by simp⟩
  have hgW : genericPoint Z ∈ U l ⊓ U i := eW ▸ hU.ne {l, i}
  have ringW := ring_of_eq hU {l, i} ⟨l, by simp⟩ (U l ⊓ U i) eW hgW
  have ringl := ring_of_eq hU {l} ⟨l, by simp⟩ (U l) (by simp) hgl
  have hloc := (GlobalTheory.PD.rB_mono_loc ℂ F Z.functionField d x hx {l, i} l (by simp)).2
  have hprod : ∏ j ∈ ({l, i} : Finset (Fin (d + 1))), x j / x l = x i / x l := by
    rw [Finset.prod_pair hli, div_self (hx.pd.ne l), one_mul]
  rw [hprod] at hloc
  have hle : U l ⊓ U i ≤ U l := inf_le_left
  obtain ⟨vf, hvf⟩ := (ringW _).1 (ratio_mem (x := x) {l, i} i l (by simp))
  have hwv : resG Z hle wf * vf = 1 := by
    apply germ_injective_of_isIntegral Z (genericPoint Z) hgW
    rw [map_mul, map_one, germ_resG hle hgW hgl, hw, hvf, ← map_mul,
      div_mul_div_comm, mul_comm (x i), div_self (mul_ne_zero (hx.pd.ne _) (hx.pd.ne _)), map_one]
  letI : Algebra Γ(Z, U l) Γ(Z, U l ⊓ U i) := (resG Z hle).toAlgebra
  have hres : ∀ f, algebraMap Γ(Z, U l) Γ(Z, U l ⊓ U i) f = resG Z hle f := fun _ => rfl
  haveI : IsLocalization.Away wf Γ(Z, U l ⊓ U i) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, n, rfl⟩
      rw [hres, map_pow]
      exact (IsUnit.of_mul_eq_one _ hwv).pow n
    · intro t
      obtain ⟨N, hN⟩ := (hloc _).1 ((ringW _).2 ⟨t, rfl⟩)
      obtain ⟨a, ha⟩ := (ringl _).1 hN
      refine ⟨⟨a, ⟨wf ^ N, N, rfl⟩⟩, ?_⟩
      apply germ_injective_of_isIntegral Z (genericPoint Z) hgW
      simp only [hres]
      rw [map_mul, germ_resG hle hgW hgl, germ_resG hle hgW hgl, ha, map_pow, hw]
    · intro a b hab
      refine ⟨1, ?_⟩
      have : a = b := by
        apply germ_injective_of_isIntegral Z (genericPoint Z) hgl
        rw [← germ_resG hle hgW hgl, ← germ_resG hle hgW hgl]
        exact congrArg _ hab
      rw [this]
  have hunit : IsUnit (CxPts.evHom hP wf) := by
    rw [← CxPts.ev_eq hP]
    exact isUnit_iff_ne_zero.2 hne
  let φ : Γ(Z, U l ⊓ U i) →+* ℂ := IsLocalization.Away.lift wf hunit
  have hφ : ∀ f, φ (resG Z hle f) = CxPts.evHom hP f := fun f => IsLocalization.Away.lift_eq wf hunit f
  have hC : ∀ a : ℂ, φ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX s (U l ⊓ U i) a) = RingHom.id ℂ a := fun a => by
    have h1 := RingHom.congr_fun (GlobalTheory.TopForm.resG_comp_algX s hle) a
    rw [RingHom.comp_apply] at h1
    rw [← h1, hφ, ← CxPts.ev_eq hP, CxPts.ev_algX hP]
  have hq := CxPts.ofHom_mem hW φ hC
  have hPq : P = CxPts.ofHom hW φ hC := by
    refine Subtype.ext (GlobalTheory.Points.ext_of_valR hUl hP (CxPts.ptsIn_mono hle hq) fun f => ?_)
    change CxPts.ev s (RingHom.id ℂ) (U l) f P = CxPts.ev s (RingHom.id ℂ) (U l) f _
    rw [← CxPts.ev_res hle hq f, CxPts.ev_ofHom, hφ, CxPts.ev_eq hP]
  rw [hPq]
  exact CxPts.ptsIn_mono inf_le_right hq

end Chart

end UpperTheory.FixIff

open UpperTheory.FixIff in
theorem UpperTheory.etaleCorrespondence_complexPoints_statement :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)) (i : Fin (d + 1)) (hg : genericPoint Y ∈ c1 ⁻¹ᵁ U i) (e : rB ℂ Y.functionField x {i} →ₐ[ℂ] ℂ) (y : CxPts s' (RingHom.id ℂ)), UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U i) hg _ e y → (IsFix (rB ℂ Y.functionField x {i}) e j2 (rB ℂ Z.functionField x {i}) ↔ y.1 ≫ c1 = y.1 ≫ c2) := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU i hg e y hM
  have hgZ : ∀ j, genericPoint Z ∈ U j := fun j => by simpa using hU.ne {j}
  have hg2 : ∀ j, genericPoint Y ∈ c2 ⁻¹ᵁ U j := fun j => by
    change c2 (genericPoint Y) ∈ U j
    rw [UpperTheory.A.generic_map c2]
    exact hgZ j
  have affU : ∀ j, IsAffineOpen (U j) := fun j => by simpa using hU.affine {j} ⟨j, by simp⟩
  have hV : IsAffineOpen (c1 ⁻¹ᵁ U i) := (affU i).preimage c1
  have hB : ∀ v, v ∈ rB ℂ Y.functionField x {i} ↔
      ∃ f : Γ(Y, c1 ⁻¹ᵁ U i), (Y.presheaf.germ (c1 ⁻¹ᵁ U i) (genericPoint Y) hg).hom f = v := fun v =>
    UpperTheory.A.mem_rB_pull h1 hK hL g1 hU {i} ⟨i, by simp⟩ (c1 ⁻¹ᵁ U i) (by simp) hg v
  have ringZ : ∀ j b, b ∈ rB ℂ Z.functionField x {j} ↔
      ∃ f : Γ(Z, U j), (Z.presheaf.germ (U j) (genericPoint Z) (hgZ j)).hom f = b := fun j b =>
    ring_of_eq hU {j} ⟨j, by simp⟩ (U j) (by simp) (hgZ j) b
  have hz1 : UpperTheory.A.zpt c1 h1 y ∈ CxPts.ptsIn s (RingHom.id ℂ) (U i) := hM.1

  have hval1 : ∀ (f : Γ(Z, U i))
      (hb1 : algebraMap Z.functionField Y.functionField
        ((Z.presheaf.germ (U i) (genericPoint Z) (hgZ i)).hom f) ∈ rB ℂ Y.functionField x {i}),
      e ⟨_, hb1⟩ = CxPts.ev s (RingHom.id ℂ) (U i) f (UpperTheory.A.zpt c1 h1 y) := by
    intro f hb1
    have hf : (Y.presheaf.germ (c1 ⁻¹ᵁ U i) (genericPoint Y) hg).hom ((c1.app (U i)).hom f) ∈
        rB ℂ Y.functionField x {i} := (hB _).2 ⟨_, rfl⟩
    have h := hM.2 _ hf
    have e1 : (⟨_, hb1⟩ : rB ℂ Y.functionField x {i}) = ⟨_, hf⟩ := Subtype.ext (g1 _ (hgZ i) hg f).symm
    rw [e1, h]
    exact (GlobalTheory.Points.valR_comp y.1 c1 (U i) f).symm
  have hev2 : ∀ (j : Fin (d + 1)) (f : Γ(Z, U j)),
      CxPts.ev s' (RingHom.id ℂ) (c2 ⁻¹ᵁ U j) ((c2.app (U j)).hom f) y =
        CxPts.ev s (RingHom.id ℂ) (U j) f (UpperTheory.A.zpt c2 h2 y) := fun j f =>
    (GlobalTheory.Points.valR_comp y.1 c2 (U j) f).symm
  constructor
  · intro hF
    obtain ⟨l, hl⟩ := CxPts.exists_mem_ptsIn hU.cover (UpperTheory.A.zpt c2 h2 y)
    have hyl : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c2 ⁻¹ᵁ U l) := hl
    obtain ⟨wf, hwf⟩ := (ringZ l _).1 (ratio_mem (x := x) {l} l i (by simp))
    obtain ⟨bf, hbf⟩ := (ringZ i _).1 (ratio_mem (x := x) {i} i l (by simp))
    have hb1 : algebraMap Z.functionField Y.functionField
        ((Z.presheaf.germ (U i) (genericPoint Z) (hgZ i)).hom bf) ∈ rB ℂ Y.functionField x {i} := by
      rw [← g1 _ (hgZ i) hg bf]
      exact (hB _).2 ⟨_, rfl⟩
    have hVal := hF _ ((ringZ i _).2 ⟨bf, rfl⟩) hb1
    have hmul : (Y.presheaf.germ (c2 ⁻¹ᵁ U l) (genericPoint Y) (hg2 l)).hom ((c2.app (U l)).hom wf) *
        j2 ((Z.presheaf.germ (U i) (genericPoint Z) (hgZ i)).hom bf) = 1 := by
      rw [← g2 _ (hgZ l) (hg2 l) wf, ← map_mul, hwf, hbf, ← map_mul,
        div_mul_div_comm, mul_comm (x i), div_self (mul_ne_zero (hx.pd.ne _) (hx.pd.ne _)), map_one, map_one]
    have hne := ne_zero_of_val hB hM _ hyl (hg2 l) hVal hmul
    rw [hev2] at hne
    have hz2 := mem_chart_of_ne_zero hx hU l i _ hl wf (hgZ l) hwf hne
    have hyi : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c2 ⁻¹ᵁ U i) := hz2
    refine GlobalTheory.Points.ext_of_valR (affU i) hz1 hz2 fun f => ?_
    have hf1 : algebraMap Z.functionField Y.functionField
        ((Z.presheaf.germ (U i) (genericPoint Z) (hgZ i)).hom f) ∈ rB ℂ Y.functionField x {i} := by
      rw [← g1 _ (hgZ i) hg f]
      exact (hB _).2 ⟨_, rfl⟩
    have hVf := hF _ ((ringZ i _).2 ⟨f, rfl⟩) hf1
    rw [g2 _ (hgZ i) (hg2 i) f] at hVf
    have := val_unique hB hM _ hyi (hg2 i) hVf
    rw [hval1 f hf1, hev2] at this
    exact this
  · intro hfix b hb hb1
    obtain ⟨f, rfl⟩ := (ringZ i b).1 hb
    have hzz : UpperTheory.A.zpt c1 h1 y = UpperTheory.A.zpt c2 h2 y := Subtype.ext hfix
    have hyi : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c2 ⁻¹ᵁ U i) := by
      have : UpperTheory.A.zpt c2 h2 y ∈ CxPts.ptsIn s (RingHom.id ℂ) (U i) := hzz ▸ hz1
      exact this
    rw [hval1 f hb1, g2 _ (hgZ i) (hg2 i) f, hzz, ← hev2]
    exact val_of_regular hV hB hM _ hyi (hg2 i)
