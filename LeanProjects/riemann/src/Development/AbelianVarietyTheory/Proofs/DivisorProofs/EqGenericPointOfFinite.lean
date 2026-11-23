import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagBundleFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagBundleFamilyDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagFamilyChernLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagFamilyHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationValuativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationUnfoldingFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationGenericLiftStatement
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.FlagCls
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCovDeg

theorem card_points {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) (hx : f.residueDegree x ≠ 0) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [CharZero Ω] (p : Sp Ω ⟶ Y) (hp : p (IsLocalRing.closedPoint Ω) = f x) :
    Nat.card {z : Sp Ω ⟶ X // z ≫ f = p ∧ z (IsLocalRing.closedPoint Ω) = x} = f.residueDegree x := by
  obtain ⟨⟨y, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω Y).symm.surjective p
  obtain rfl : y = f x := (Scheme.fromSpecResidueField_apply y _).symm.trans hp
  letI : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  letI : Algebra (Y.residueField (f x)) Ω := ψ.hom.toAlgebra
  haveI : Module.Finite (Y.residueField (f x)) (X.residueField x) := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hx)
  haveI : CharZero (Y.residueField (f x)) := ψ.hom.charZero
  have hc : Nat.card (X.residueField x →ₐ[Y.residueField (f x)] Ω) = f.residueDegree x := by
    rw [Nat.card_eq_fintype_card]
    exact AlgHom.card _ _ _
  rw [← hc]
  have key (σ : X.residueField x ⟶ CommRingCat.of Ω) : (Spec.map σ ≫ X.fromSpecResidueField x) ≫ f =
      Spec.map (f.residueFieldMap x ≫ σ) ≫ Y.fromSpecResidueField (f x) := by
    rw [Spec.map_comp, Category.assoc, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  symm
  refine Nat.card_eq_of_bijective (fun σ => ⟨Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ X.fromSpecResidueField x, ?_,
    Scheme.fromSpecResidueField_apply x _⟩) ⟨fun σ σ' h => ?_, fun ⟨z, h1, h2⟩ => ?_⟩
  · refine (key _).trans ?_
    have : f.residueFieldMap x ≫ CommRingCat.ofHom σ.toRingHom = ψ := by
      ext a; exact σ.commutes a
    exact congrArg (fun s => Spec.map s ≫ Y.fromSpecResidueField (f x)) this
  · have := Spec.map_injective ((cancel_mono _).1 (congrArg Subtype.val h))
    exact AlgHom.ext fun a => congr($this a)
  · obtain ⟨⟨w, σ⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective z
    obtain rfl : w = x := (Scheme.fromSpecResidueField_apply w _).symm.trans h2
    have := Spec.map_injective ((cancel_mono _).1 ((key σ).symm.trans h1))
    exact ⟨⟨σ.hom, fun a => congr($this a)⟩, rfl⟩

theorem residueDegree_eq_mul {G C Y Bg S : Scheme.{0}} (f : G ⟶ C) (r : G ⟶ Y) (jG : G ⟶ Bg) (πB : Bg ⟶ S) (πC : C ⟶ S)
    (w : jG ≫ πB = f ≫ πC) (η : G) (hf : f.residueDegree η ≠ 0) (hr : r.residueDegree η ≠ 0)
    (hB : πB.residueDegree (jG η) ≠ 0) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (p : Sp Ω ⟶ C)
    (hp : p (IsLocalRing.closedPoint Ω) = f η)
    (h : ∀ xb : Sp Ω ⟶ Bg, xb ≫ πB = p ≫ πC → ∃ y : Sp Ω ⟶ Y, y (IsLocalRing.closedPoint Ω) = r η ∧
      ∀ z : Sp Ω ⟶ G, (z ≫ f = p ∧ z ≫ jG = xb) ↔ z ≫ r = y) :
    f.residueDegree η = r.residueDegree η * πB.residueDegree (jG η) := by
  have hS : (p ≫ πC) (IsLocalRing.closedPoint Ω) = πB (jG η) := by
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply, ← hp]
    rfl
  rw [← card_points f η hf Ω p hp, ← card_points πB (jG η) hB Ω (p ≫ πC) hS]
  let T := {xb : Sp Ω ⟶ Bg // xb ≫ πB = p ≫ πC ∧ xb (IsLocalRing.closedPoint Ω) = jG η}
  let m : {z : Sp Ω ⟶ G // z ≫ f = p ∧ z (IsLocalRing.closedPoint Ω) = η} → T := fun z =>
    ⟨z.1 ≫ jG, by rw [Category.assoc, w, ← Category.assoc, z.2.1], congrArg jG z.2.2⟩
  have hT : Finite T := Nat.finite_of_card_ne_zero ((card_points πB (jG η) hB Ω (p ≫ πC) hS).trans_ne hB)
  have hm (t : T) : Nat.card {z // m z = t} = r.residueDegree η := by
    obtain ⟨y, hy, hz⟩ := h t.1 t.2.1
    rw [← card_points r η hr Ω y hy]
    exact Nat.card_congr ⟨fun z => ⟨z.1.1, (hz _).1 ⟨z.1.2.1, congrArg Subtype.val z.2⟩, z.1.2.2⟩,
      fun z => ⟨⟨z.1, ((hz _).2 z.2.1).1, z.2.2⟩, Subtype.ext ((hz _).2 z.2.1).2⟩, fun _ => rfl, fun _ => rfl⟩
  have hm' (t : T) : Finite {z // m z = t} := Nat.finite_of_card_ne_zero ((hm t).trans_ne hr)
  have := Fintype.ofFinite T
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv m), Nat.card_sigma, Finset.sum_congr rfl fun t _ => hm t]
  simp [mul_comm, T]

theorem residueDegree_ne_zero {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (x : X) : f.residueDegree x ≠ 0 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) := residueFieldMap_finite_of_locallyQuasiFinite f _
  exact Module.finrank_pos.ne'

theorem eq_genericPoint_of_finite {X Y : Scheme.{0}} [IsIntegral X] (f : X ⟶ Y) [IsFinite f] (x : X)
    (h : f x = f (genericPoint X)) : x = genericPoint X := by
  have hd := f.isDiscrete_preimage_singleton (f (genericPoint X))
  obtain ⟨U, hU, e⟩ := (isDiscrete_iff_forall_mem_exists_isOpen.1 hd) x h
  have : genericPoint X ∈ U ∩ f ⁻¹' {f (genericPoint X)} :=
    ⟨(genericPoint_specializes x).mem_open hU (e.ge rfl).1, rfl⟩
  exact (e.le this).symm

variable {D : D7} (O : Setup D) (c : O.s.Comp)

set_option maxHeartbeats 1000000 in

theorem deg_eq_mul {B Bg Y : Scheme.{0}} [IsIntegral Y] {q : B ⟶ Sp (𝓞 D.what₂.LL)}
    {E : (D.host.E →+* ℂ) → B.Modules} (hE : ∀ σ, IsVB (E σ) (O.S.Dw.mult σ)) {jB : Bg ⟶ B} {πB : Bg ⟶ gen O.s.T.Z}
    (pb : IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    [IsFinite πB] {t : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB}
    (hLF : ∀ σ, IsLieFrames O.s.T.Z O.κ.e jB πB (E σ) _ σ false (t σ)) {π : Y ⟶ B}
    {fl : ∀ σ, Vert.Flag ((Scheme.Modules.pullback π).obj (E σ)) (O.S.Dw.mult σ)} (hfb : IsFlagBundle π E O.S.Dw.mult fl)
    (arY : IsArithVar (π ≫ q) (O.var c).dim) (V : Cover (O.var c)) (ρ : V.X ⟶ Y) (w : ρ ≫ π ≫ q = V.p)
    (hρ : FlagChain.IsCov (π ≫ q) (O.var c).dim ρ) (jG : V.G ⟶ Bg) (hjG : jG ≫ jB = V.j ≫ ρ ≫ π)
    (hγ : jG ≫ πB = V.π ≫ (O.Φ.C c).π) {χ : O.κ.c.F →+* V.G.functionField} {x : Sp V.G.functionField ⟶ O.s.T.Z.X}
    (g : EigFrame O.s.T.Z χ x)
    (hb : Bears O.s.T.Z id (fun _ => false) (fun _ => rfl) hE jB πB t π fl (GlobalTheory.FlagCov.genPt V.G ≫ V.j ≫ ρ)
      (GlobalTheory.FlagCov.genPt V.G ≫ jG) g)
    (hc : (O.Φ.C c).Carries (GlobalTheory.FlagCov.genPt V.G ≫ V.π) g) :
    V.deg = ρ.residueDegree (genericPoint V.X) * πB.residueDegree (jG (genericPoint V.G)) := by
  obtain ⟨γ, hγ'⟩ : ∃ γ : V.G ⟶ gen O.s.T.Z, γ = jG ≫ πB := ⟨_, rfl⟩
  have hπ : V.π ≫ (O.Φ.C c).π = γ := hγ.symm.trans hγ'.symm
  obtain rfl : x = GlobalTheory.FlagCov.genPt V.G ≫ γ ≫ genι O.s.T.Z := by rw [hb.2.1]; simp only [hγ', Category.assoc]
  let Br : ∀ (K : Type) [CommRing K], (Sp K ⟶ V.G) → ∀ (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X),
      EigFrame O.s.T.Z χ x → Prop := fun K _ z χ x g =>
    Bears O.s.T.Z id (fun _ => false) (fun _ => rfl) hE jB πB t π fl (z ≫ V.j ≫ ρ) (z ≫ jG) g
  have P0 : ∀ (K : Type) [CommRing K] (z : Sp K ⟶ V.G) (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X)
      (g : EigFrame O.s.T.Z χ x), Br K z χ x g → x = z ≫ γ ≫ genι O.s.T.Z ∧ z ≫ γ ≫ genStr O.s.T.Z = spMap χ := by
    intro K _ z χ x g hb
    refine ⟨?_, ?_⟩
    · rw [hb.2.1]; simp only [hγ', Category.assoc]
    · rw [← hb.2.2.1]; simp only [hγ', Category.assoc]
  have P1 : ∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ V.G) (χ : O.κ.c.F →+* K),
      z ≫ γ ≫ genStr O.s.T.Z = spMap χ → ∃ g : EigFrame O.s.T.Z χ (z ≫ γ ≫ genι O.s.T.Z), Br K z χ _ g := by
    intro K _ _ z χ hz
    exact GlobalTheory.T.toroidal_flag_bundle_family _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) (fun _ => rfl) _ _ _ _ hE jB πB t π fl
      hLF Function.bijective_id K (z ≫ V.j ≫ ρ) (z ≫ jG) χ (by simp only [Category.assoc, hjG])
      (by simpa only [hγ', Category.assoc] using hz) _ (by simp only [hγ', Category.assoc])
  have bmap := GlobalTheory.T.toroidal_flag_bundle_family_dual _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) (fun _ => rfl) _ _ _ _ hE jB πB t π fl
    hLF
  have P2 : ∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ V.G) (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X)
      (g : EigFrame O.s.T.Z χ x) (K' : Type) [CommRing K'] (ψ : K →+* K') (χ' : O.κ.c.F →+* K')
      (x' : Sp K' ⟶ O.s.T.Z.X) (g' : EigFrame O.s.T.Z χ' x') (t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → K'ˣ),
      Br K z χ x g → g.Tri ψ g' t → Br K' (spMap ψ ≫ z) χ' x' g' := by
    intro K _ _ z χ x g K' _ ψ χ' x' g' t hb ht
    simpa only [Br, Category.assoc] using bmap K _ _ χ x g K' ψ χ' x' g' t hb ht
  have P3 : ∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ V.G) (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X)
      (g g' : EigFrame O.s.T.Z χ x), Br K z χ x g → Br K z χ x g' →
      ∃ t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → Kˣ, g.Tri (RingHom.id K) g' t := by
    intro K _ _ z χ x g g' hb hb'
    exact GlobalTheory.T.toroidal_flag_family_chern_limit _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) (fun _ => rfl) _ _ _ _ hE jB πB t π fl
      hLF Function.surjective_id K _ _ χ x g g' hb hb'
  have hcar := GlobalTheory.T.flag_compactification_generic_lift _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) V.G γ Br P0 P1 P2 P3 V.π χ g hb hπ hc
  have huniq (K : Type) [Field K] (χ : O.κ.c.F →+* K) (x : Sp K ⟶ O.s.T.Z.X) (g : EigFrame O.s.T.Z χ x)
      (p p' : Sp K ⟶ (O.Φ.C c).Y.X) (h1 : x = p ≫ (O.Φ.C c).π ≫ genι O.s.T.Z)
      (h2 : p ≫ (O.Φ.C c).π ≫ genStr O.s.T.Z = spMap χ) (h3 : p' ≫ (O.Φ.C c).π = p ≫ (O.Φ.C c).π)
      (c1 : (O.Φ.C c).Carries p g) (c2 : (O.Φ.C c).Carries p' g) : p' = p := by
    rw [← Category.assoc] at h1 h2
    subst h1
    exact (GlobalTheory.T.uniformization_unfolding_free _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ _ O.Φ c K χ _ h2
      (by rintro _ ⟨w, rfl⟩; exact ⟨p w, rfl⟩) g).unique ⟨h3, c2⟩ ⟨rfl, c1⟩
  have hstr : jG ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom = V.π ≫ (O.var c).str := by
    rw [← Category.assoc, hγ, Category.assoc]
    exact congrArg _ (O.Φ.C c).π_str

  have hbase (K : Type) [Field K] (z : Sp K ⟶ V.G) (xb : Sp K ⟶ Bg) (h1 : (z ≫ V.j ≫ ρ) ≫ π = xb ≫ jB) :
      z ≫ jG = xb := by
    haveI : IsPreimmersion (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 D.what₂.LL)) (S := D.what₂.LL)
    haveI : IsPreimmersion jB := MorphismProperty.of_isPullback (P := @IsPreimmersion) pb.flip inferInstance
    rw [← cancel_mono jB, ← h1, Category.assoc, hjG]
    simp only [Category.assoc]
  let Ω := AlgebraicClosure V.G.functionField
  let ι : V.G.functionField →+* Ω := algebraMap _ _
  haveI : CharZero Ω := charZero_of_injective_ringHom (ι.comp χ).injective
  let z₀ : Sp Ω ⟶ V.G := spMap ι ≫ GlobalTheory.FlagCov.genPt V.G
  have hz₀ : z₀ (IsLocalRing.closedPoint Ω) = genericPoint V.G := by
    change V.G.fromSpecStalk _ (spMap ι _) = _
    rw [show spMap ι (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint _ from Subsingleton.elim (α := PrimeSpectrum V.G.functionField) _ _]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨g₀, hg₀⟩ := g.exists_isMap ι (φ' := ι.comp χ) (x' := z₀ ≫ γ ≫ genι O.s.T.Z) rfl (Category.assoc _ _ _)
  have hb₀ : Br Ω z₀ _ _ g₀ := P2 _ _ _ _ g _ ι _ _ g₀ 1 hb (hg₀.tri rfl (Category.assoc _ _ _))
  have hc₀ := hcar _ _ _ _ _ hb₀
  have hχ₀ := (P0 _ _ _ _ _ hb₀).2
  have hdeg : (V.j ≫ ρ).residueDegree (genericPoint V.G) = ρ.residueDegree (genericPoint V.X) := by
    rw [CurveDegreesCompare.residueDegree_comp, CoverDeg.j_residueDegree, mul_one, CoverDeg.j_genericPoint]
  rw [← hdeg]
  refine residueDegree_eq_mul V.π (V.j ≫ ρ) jG πB (O.Φ.C c).π hγ _ (residueDegree_ne_zero _ _) (hdeg.trans_ne hρ.2.2)
    (residueDegree_ne_zero _ _) Ω (z₀ ≫ V.π) (congrArg V.π hz₀) fun xb hxb => ?_
  have hxb' : xb ≫ πB = z₀ ≫ γ := by rw [hxb, Category.assoc, hπ]
  obtain ⟨y, hy, hyu⟩ := GlobalTheory.T.toroidal_flag_family_height _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) (fun _ => rfl) _ _ _ _ hE
    jB πB t π fl hLF hfb Ω xb _ _ g₀ (by rw [← Category.assoc xb, hxb']; exact (Category.assoc _ _ _).symm)
    (by rw [← Category.assoc xb, hxb', Category.assoc, hχ₀])

  have hover (K : Type) [Field K] (ψ : Ω →+* K) (z : Sp K ⟶ V.G) (hz : z ≫ V.j ≫ ρ = spMap ψ ≫ y) :
      z ≫ V.π = spMap ψ ≫ z₀ ≫ V.π ∧ z ≫ jG = spMap ψ ≫ xb := by
    have e1 : z ≫ jG = spMap ψ ≫ xb := hbase K z _ (by rw [hz, Category.assoc, hy.1, Category.assoc])
    obtain ⟨g₁, hg₁⟩ := g₀.exists_isMap ψ (φ' := ψ.comp (ι.comp χ)) (x' := spMap ψ ≫ z₀ ≫ γ ≫ genι O.s.T.Z) rfl rfl
    have ht := hg₁.tri rfl rfl
    have b1 : Br K z _ _ g₁ := by
      simp only [Br, hz, e1]
      exact bmap _ _ _ _ _ g₀ K ψ _ _ g₁ 1 hy ht
    have b2 := P2 _ _ _ _ g₀ _ ψ _ _ g₁ 1 hb₀ ht
    refine ⟨(huniq K _ _ g₁ ((spMap ψ ≫ z₀) ≫ V.π) _ ?_ ?_ ?_ (hcar _ _ _ _ _ b2) (hcar _ _ _ _ _ b1)).trans
      (Category.assoc _ _ _), e1⟩
    · simp only [← hπ, Category.assoc]
    · rw [← (P0 _ _ _ _ _ b2).2]; simp only [← hπ, Category.assoc]
    · rw [Category.assoc, Category.assoc, hπ, Category.assoc, ← hxb', hγ', ← Category.assoc, e1, Category.assoc]
  refine ⟨y, ?_, fun z => ⟨fun ⟨h1, h2⟩ => ?_, fun hz => ?_⟩⟩
  · haveI : IsProper (π ≫ q) := GlobalTheory.CommonModel.isProper_of_isProjOver arY.isProjOver
    haveI : IsProper (ρ ≫ π ≫ q) := GlobalTheory.CommonModel.isProper_of_isProjOver hρ.1.isProjOver
    haveI : IsProper ρ := IsProper.of_comp ρ (π ≫ q)
    have hs : y (IsLocalRing.closedPoint Ω) ∈ Set.range ρ :=
      (genericPoint_specializes _).mem_closed ρ.isClosedMap.isClosed_range ⟨_, hρ.2.1⟩
    obtain ⟨v, hv⟩ := hs
    obtain ⟨u, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := ρ) (g := y) v _ hv
    let K := (Limits.pullback ρ y).residueField u
    let a : Sp K ⟶ Limits.pullback ρ y := (Limits.pullback ρ y).fromSpecResidueField u
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Ω →+* K, a ≫ Limits.pullback.snd ρ y = spMap ψ := ⟨_, (Spec.map_preimage _).symm⟩
    have e0 : (a ≫ Limits.pullback.fst ρ y) ≫ ρ = spMap ψ ≫ y := by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hψ]
    have e1 : (a ≫ Limits.pullback.fst ρ y) ≫ V.p = (spMap ψ ≫ xb ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) ≫
        spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) := by
      rw [← w, ← Category.assoc, e0, Category.assoc, ← Category.assoc y, hy.1, Category.assoc, pb.w]
      simp only [Category.assoc]
    have e2 : V.pb.lift _ _ e1 ≫ V.j ≫ ρ = spMap ψ ≫ y := by rw [← Category.assoc, V.pb.lift_fst, e0]
    have e3 := congrArg (fun s => s (IsLocalRing.closedPoint K)) (hover K ψ _ e2).1
    have e4 : spMap ψ (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint Ω :=
      Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    have e5 := eq_genericPoint_of_finite V.π (V.pb.lift _ _ e1 (IsLocalRing.closedPoint K))
      (e3.trans (congrArg V.π ((congrArg z₀ e4).trans hz₀)))
    rw [← e5, ← e4]
    exact (congrArg (fun s => s (IsLocalRing.closedPoint K)) e2).symm
  · refine hyu _ ?_
    obtain ⟨g', hg'⟩ := GlobalTheory.T.toroidal_flag_bundle_family _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ id (fun _ => false) (fun _ => rfl) _ _ _ _ hE
      jB πB t π fl hLF Function.bijective_id Ω (z ≫ V.j ≫ ρ) (z ≫ jG) (ι.comp χ) (by simp only [Category.assoc, hjG])
      (by rw [h2, ← Category.assoc xb, hxb', Category.assoc, hχ₀]) (z₀ ≫ γ ≫ genι O.s.T.Z)
      (by rw [h2, ← Category.assoc xb, hxb']; exact (Category.assoc _ _ _).symm)
    have c2 := hcar Ω z _ _ g' hg'
    rw [h1] at c2
    obtain ⟨s, hs⟩ := GlobalTheory.T.flag_compactification_valuative _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) Ω _ _ g' g₀ _ c2 hc₀
    have := bmap Ω _ _ _ _ g' Ω (RingHom.id Ω) _ _ g₀ s hg' hs
    rwa [show spMap (RingHom.id Ω) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.id_comp, h2] at this
  · have := hover Ω (RingHom.id Ω) z (by rw [hz, show spMap (RingHom.id Ω) = 𝟙 _ from Spec.map_id _, Category.id_comp])
    rwa [show spMap (RingHom.id Ω) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.id_comp] at this

variable {O c} in

theorem residueDegree_base (M : DRBase O c) {B Bg : Scheme.{0}} {q : B ⟶ Sp (𝓞 D.what₂.LL)} {jB : Bg ⟶ B}
    {πB : Bg ⟶ gen O.s.T.Z} {s : Bg ⟶ Sp D.what₂.LL}
    (pb : IsPullback jB s q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) (β : B ⟶ M.B)
    (h : jB ≫ β ≫ M.b = πB ≫ genι O.s.T.Z) (x : Bg) : πB.residueDegree x = β.residueDegree (jB x) := by
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 D.what₂.LL)) (S := D.what₂.LL)
  haveI : IsPreimmersion jB := MorphismProperty.of_isPullback (P := @IsPreimmersion) pb.flip inferInstance
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 O.κ.c.F) O.κ.c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 O.κ.c.F)) (S := O.κ.c.F)
  haveI : IsPreimmersion (genι O.s.T.Z) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have e := congrArg (fun f => Scheme.Hom.residueDegree f x) h
  simpa only [CurveDegreesCompare.residueDegree_comp, CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks jB,
    CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks M.b,
    CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks (genι O.s.T.Z), mul_one, one_mul] using e.symm

set_option maxHeartbeats 1000000 in

theorem deg_eq_mul_base (M : DRBase O c) {B Bg Y : Scheme.{0}} [IsIntegral B] [IsIntegral Y] {q : B ⟶ Sp (𝓞 D.what₂.LL)}
    {E : (D.host.E →+* ℂ) → B.Modules} (hE : ∀ σ, IsVB (E σ) (O.S.Dw.mult σ)) {jB : Bg ⟶ B} {πB : Bg ⟶ gen O.s.T.Z}
    (pb : IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    [IsFinite πB] {t : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB}
    (hLF : ∀ σ, IsLieFrames O.s.T.Z O.κ.e jB πB (E σ) _ σ false (t σ)) {π : Y ⟶ B}
    {fl : ∀ σ, Vert.Flag ((Scheme.Modules.pullback π).obj (E σ)) (O.S.Dw.mult σ)} (hfb : IsFlagBundle π E O.S.Dw.mult fl)
    (arY : IsArithVar (π ≫ q) (O.var c).dim) (V : Cover (O.var c)) (ρ : V.X ⟶ Y) (w : ρ ≫ π ≫ q = V.p)
    (hρ : FlagChain.IsCov (π ≫ q) (O.var c).dim ρ) (jG : V.G ⟶ Bg) (hjG : jG ≫ jB = V.j ≫ ρ ≫ π)
    (hγ : jG ≫ πB = V.π ≫ (O.Φ.C c).π) {χ : O.κ.c.F →+* V.G.functionField} {x : Sp V.G.functionField ⟶ O.s.T.Z.X}
    (g : EigFrame O.s.T.Z χ x)
    (hb : Bears O.s.T.Z id (fun _ => false) (fun _ => rfl) hE jB πB t π fl (GlobalTheory.FlagCov.genPt V.G ≫ V.j ≫ ρ)
      (GlobalTheory.FlagCov.genPt V.G ≫ jG) g)
    (hc : (O.Φ.C c).Carries (GlobalTheory.FlagCov.genPt V.G ≫ V.π) g) (β : B ⟶ M.B)
    (h : jB ≫ β ≫ M.b = πB ≫ genι O.s.T.Z) :
    V.deg = ρ.residueDegree (genericPoint V.X) * β.residueDegree (genericPoint B) := by
  rw [deg_eq_mul O c hE pb hLF hfb arY V ρ w hρ jG hjG hγ g hb hc, residueDegree_base M pb β h]
  congr 2
  obtain ⟨y, hy⟩ := GlobalTheory.FlagSurj.isFlagBundle_surjective B Y π _ E _ fl hE hfb (genericPoint B)
  have h1 : π (genericPoint Y) ⤳ genericPoint B := hy ▸ (genericPoint_specializes y).map π.continuous
  rw [← Scheme.Hom.comp_apply, hjG, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, CoverDeg.j_genericPoint, hρ.2.1]
  exact (h1.antisymm (genericPoint_specializes _)).eq

end GlobalTheory.FlagCovDeg

end
