import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRham

open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct

theorem eq_of_le_of_le_add_eps {R : Type} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module (DualNumber R) M] {F G : Submodule (DualNumber R) M} (hF : ∃ N, IsCompl F N) (h1 : G ≤ F)
    (h2 : ∀ x ∈ F, ∃ y ∈ G, ∃ z : M, x = y + (DualNumber.eps : DualNumber R) • z) : F = G := by
  refine le_antisymm (fun x hx => ?_) h1
  obtain ⟨N, hN⟩ := hF
  have ee : ∀ z : M, (DualNumber.eps : DualNumber R) • (DualNumber.eps : DualNumber R) • z = 0 :=
    fun z => by rw [smul_smul, DualNumber.eps_mul_eps, zero_smul]
  have step : ∀ x ∈ F, ∃ y ∈ G, ∃ w ∈ F, x = y + (DualNumber.eps : DualNumber R) • w := fun x hx => by
    obtain ⟨y, hy, z, rfl⟩ := h2 x hx
    have hz : z ∈ F ⊔ N := hN.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨zF, hzF, zN, hzN, rfl⟩ := Submodule.mem_sup.1 hz
    have hmem : (DualNumber.eps : DualNumber R) • zN ∈ F := by
      have e : (DualNumber.eps : DualNumber R) • zN =
          (y + (DualNumber.eps : DualNumber R) • (zF + zN)) - y - (DualNumber.eps : DualNumber R) • zF := by
        rw [smul_add]; abel
      rw [e]; exact sub_mem (sub_mem hx (h1 hy)) (F.smul_mem _ hzF)
    have h0 : (DualNumber.eps : DualNumber R) • zN = 0 :=
      (Submodule.disjoint_def.1 hN.disjoint) _ hmem (N.smul_mem _ hzN)
    exact ⟨y, hy, zF, hzF, by rw [smul_add, h0, add_zero]⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := step x hx
  obtain ⟨y', hy', w', -, rfl⟩ := step w hw
  rw [smul_add, ee, add_zero]
  exact G.add_mem hy (G.smul_mem _ hy')

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

def crysLo (d : Crys (epsDP R) (epsRed R) A) : HdR A where
  toFun c := (d ((constMor A).pull c)).fst
  map_add' x y := by simp only [map_add, TrivSqZeroExt.fst_add]
  map_smul' r c := by
    rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_mul]
    simp

def crysHi (d : Crys (epsDP R) (epsRed R) A) : HdR A where
  toFun c := (d ((constMor A).pull c)).snd
  map_add' x y := by simp only [map_add, TrivSqZeroExt.snd_add]
  map_smul' r c := by
    rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]
    simp

theorem crys_constMor (d : Crys (epsDP R) (epsRed R) A) (c : primDR A) :
    d ((constMor A).pull c) = TrivSqZeroExt.inl (crysLo d c) + TrivSqZeroExt.inr (crysHi d c) := by
  ext <;> simp [crysLo, crysHi]

theorem crys_ext (P : AbelianDeRham) {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {d d' : Crys (epsDP R) (epsRed R) A}
    (e : ∀ c, d ((constMor A).pull c) = d' ((constMor A).pull c)) : d = d' := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨z, rfl⟩ := constMor_surjective P hA hg w
  induction z with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r c => rw [liftSemi_tmul, map_smul, map_smul, e]

theorem fst_eq_crysLo (P : AbelianDeRham) {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (d : Crys (epsDP R) (epsRed R) A)
    (w : prim (epsDP R) (epsRed R) A) : (d w).fst = crysLo d ((redMor A).pull w) := by
  obtain ⟨z, rfl⟩ := constMor_surjective P hA hg w
  induction z with
  | zero => simp only [map_zero, TrivSqZeroExt.fst_zero]
  | add x y hx hy => simp only [map_add, TrivSqZeroExt.fst_add, hx, hy]
  | tmul r c =>
    rw [liftSemi_tmul, map_smul, LinearMap.map_smulₛₗ, redMor_constMor, map_smul]
    simp [crysLo]

end GlobalTheory.DeRham

namespace GlobalTheory.DeRham

open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

theorem exists_const (A : Over (Sp R)) [GrpObj A] :
    ∃ (C : Over (Sp (DualNumber R))) (_ : GrpObj C) (φ : C.left ⟶ A.left) (j : A.left ⟶ C.left),
      IsGrpPullback C A (spMap (algebraMap R (DualNumber R))) φ ∧ IsGrpPullback A C (epsRed R) j ∧
        j ≫ φ = 𝟙 _ := by
  obtain ⟨C, _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A (spMap (algebraMap R (DualNumber R)))
  have eid : epsRed R ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    have e0 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [epsRed, spMap_comp_spMap, e0]
    exact Spec.map_id _
  have w : 𝟙 A.left ≫ A.hom = (A.hom ≫ epsRed R) ≫ spMap (algebraMap R (DualNumber R)) := by
    rw [Category.assoc, eid, Category.comp_id, Category.id_comp]
  have e1 : hφ.1.lift _ _ w ≫ φ = 𝟙 _ := hφ.1.lift_fst _ _ _
  have e2 : hφ.1.lift _ _ w ≫ C.hom = A.hom ≫ epsRed R := hφ.1.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  have hic : IsGrpPullback A C (epsRed R) (hφ.1.lift _ _ w) :=
    hφ.cancel ((isGrpPullback_of_iso (Iso.refl A)).congr eid.symm e1.symm) e2
  exact ⟨C, inferInstance, φ, _, hφ, hic, e1⟩

variable {C : Over (Sp (DualNumber R))} [GrpObj C] {φ : C.left ⟶ A.left} {j : A.left ⟶ C.left}

theorem constMor_isBC (P : AbelianDeRham) {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (hφ : IsGrpPullback C A (spMap (algebraMap R (DualNumber R))) φ)
    (hic : IsGrpPullback A C (epsRed R) j) (e1 : j ≫ φ = 𝟙 _) : (constMor A).IsBC := by
  obtain ⟨-, -, PB, PR, -⟩ := P
  have hC := PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hg
  obtain ⟨bc, -⟩ := PB R A g hA hg (DualNumber R) C φ hφ
  have su : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rg := PR _ C g hC gC _ (epsDP R) (isDPNilpotent_squareZero _) R _ su rfl A _ hic
  have e : ∀ z, liftSemi (constMor A).pull z = (liftMor (epsDP R) hic).pull (liftSemi (bcMor hφ).pull z) :=
    fun z => by
      induction z with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul r c =>
        rw [liftSemi_tmul, liftSemi_tmul, map_smul,
          ← GrpMor.pull_pull (bcMor hφ) (liftMor (epsDP R) hic) (constMor A) (fun _ => rfl) (by simpa using e1) c]
  have : ⇑(liftSemi (constMor A).pull) = (liftMor (epsDP R) hic).pull ∘ liftSemi (bcMor hφ).pull := funext e
  unfold GrpMor.IsBC
  rw [this]
  exact rg.comp bc

theorem mem_liftFil_const_iff (P : AbelianDeRham) {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (hφ : IsGrpPullback C A (spMap (algebraMap R (DualNumber R))) φ)
    (hic : IsGrpPullback A C (epsRed R) j) (e1 : j ≫ φ = 𝟙 _) {d : Crys (epsDP R) (epsRed R) A} :
    d ∈ liftFil (epsDP R) hic ↔ ∀ c ∈ PrimitiveSubmodule A, d ((constMor A).pull c) = 0 := by
  obtain ⟨-, hF⟩ := P.2.2.1 R A g hA hg (DualNumber R) C φ hφ
  have key : ∀ c, crysToDR (epsDP R) hic d ((bcMor hφ).pull c) = d ((constMor A).pull c) := fun c => by
    rw [crysToDR_apply,
      GrpMor.pull_pull (bcMor hφ) (liftMor (epsDP R) hic) (constMor A) (fun _ => rfl) (by simpa using e1) c]
  rw [liftFil, Submodule.mem_comap, Fil, hF, Submodule.mem_dualAnnihilator]
  constructor
  · intro H c hc
    rw [← key]
    exact H _ (Submodule.subset_span ⟨c, hc, rfl⟩)
  · intro H c hc
    refine (Submodule.span_le (p := LinearMap.ker (crysToDR (epsDP R) hic d))).2 (fun c hc => ?_) hc
    obtain ⟨c, hc, rfl⟩ := hc
    change _ = 0
    rw [key]
    exact H c hc

theorem crysLo_mem_Fil (P : AbelianDeRham) {A' : Over (Sp (DualNumber R))} [GrpObj A'] {g : ℕ}
    (hA : IsAbelianScheme A') (hg : SmoothOfRelativeDimension g A'.hom) {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (epsRed R) i) {d : Crys (epsDP R) (epsRed R) A} (hd : d ∈ liftFil (epsDP R) h) :
    crysLo d ∈ Fil A := by
  have a₀ := PolPull.isAbelianScheme_of_isGrpPullback hA h
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  letI : Algebra (DualNumber R) R := (TrivSqZeroExt.fstHom R R R).toRingHom.toAlgebra
  obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber R) A' g hA hg R A i h
  rw [Fil, hF, Submodule.mem_dualAnnihilator]
  intro c hc
  refine (Submodule.span_le (p := LinearMap.ker (crysLo d))).2 (fun c hc => ?_) hc
  obtain ⟨c', hc', rfl⟩ := hc
  have z0 : d ((liftMor (epsDP R) h).pull c') = 0 := (Submodule.mem_dualAnnihilator _).1 hd c' hc'
  have red : (redMor A).pull ((liftMor (epsDP R) h).pull c') = (bcMor h).pull c' :=
    GrpMor.pull_pull (liftMor (epsDP R) h) (redMor A) (bcMor h) (fun _ => rfl) (by simp) c'
  change crysLo d _ = 0
  rw [← red, ← fst_eq_crysLo P a₀ g₀, z0, TrivSqZeroExt.fst_zero]

end GlobalTheory.DeRham

namespace GlobalTheory.DeRham

open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

set_option maxHeartbeats 1000000 in

theorem exists_retraction_of_isKSValue_one (P : AbelianDeRham) (GD : GrothendieckDeformation)
    {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (epsRed R) i)
    {g : ℕ} (hA' : IsAbelianScheme A') (hg : SmoothOfRelativeDimension g A'.hom)
    (hKS : ∀ f ∈ Fil A, IsKSValue h f 1) :
    ∃ q : A'.left ⟶ A.left, i ≫ q = 𝟙 _ ∧ IsGrpPullback A' A (spMap (algebraMap R (DualNumber R))) q := by
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hA' h
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  obtain ⟨C, _, φ, j, hφ, hic, e1⟩ := exists_const A
  have hC := PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 gA
  have hBC := constMor_isBC P hA gA hφ hic e1
  have GM := GD.at_dualNumber R
  have hEq : liftFil (epsDP R) hic = liftFil (epsDP R) h := by
    symm
    refine eq_of_le_of_le_add_eps ?_ (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨N, hN⟩ := (GM.1 g A A' i h hA' hg).2.1
      have c := GM.1.crysToDR_bijective h hA' hg
      exact ⟨_, (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ c)).symm.isCompl hN⟩
    ·
      have H := (mem_liftFil_const_iff P hA gA hφ hic e1).1 hx
      have hlo : crysLo x ∈ Fil A := (Submodule.mem_dualAnnihilator _).2 fun c hc => by
        change (x _).fst = 0
        rw [H c hc, TrivSqZeroExt.fst_zero]
      have hhi : crysHi x ∈ Fil A := (Submodule.mem_dualAnnihilator _).2 fun c hc => by
        change (x _).snd = 0
        rw [H c hc, TrivSqZeroExt.snd_zero]
      obtain ⟨k, ⟨d₁, hd₁, e₁⟩, hk⟩ := hKS _ hlo
      have hk' : k ∈ Fil A := isLieImage_one_iff.1 hk
      obtain ⟨k₂, ⟨d₂, hd₂, e₂⟩, -⟩ := hKS _ (sub_mem hhi hk')
      have ex : x = d₁ + (DualNumber.eps : DualNumber R) • d₂ := crys_ext P hA gA fun c => by
        rw [LinearMap.add_apply, LinearMap.smul_apply, e₁, e₂, crys_constMor]
        ext <;> simp only [smul_eq_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_mul,
          TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr,
          TrivSqZeroExt.snd_inr, DualNumber.fst_eps, DualNumber.snd_eps, LinearMap.sub_apply] <;> simp
      rw [ex]
      exact add_mem hd₁ (Submodule.smul_mem _ _ hd₂)
    ·
      have hlo := crysLo_mem_Fil P hA' hg h hx
      obtain ⟨y₀, hy₀⟩ := hBC.exists (crysLo x)
      obtain ⟨y₁, hy₁⟩ := hBC.exists (crysHi x)
      refine ⟨y₀, (mem_liftFil_const_iff P hA gA hφ hic e1).2 fun c hc => ?_, y₁, ?_⟩
      · rw [hy₀ c, (Submodule.mem_dualAnnihilator _).1 hlo c hc, map_zero]
      · refine crys_ext P hA gA fun c => ?_
        rw [LinearMap.add_apply, LinearMap.smul_apply, hy₀ c, hy₁ c, crys_constMor]
        ext <;> simp only [smul_eq_mul, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, DualNumber.fst_eps,
          DualNumber.snd_eps] <;> simp
  obtain ⟨e, _, he⟩ := (GM.2.2.exists_iso_iff hic hC gC h hA' hg).2 hEq
  have hi : i ≫ e.inv.left = j := by
    rw [← he, Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.comp_id]
  refine ⟨e.inv.left ≫ φ, by rw [← Category.assoc, hi, e1], ?_⟩
  haveI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact ((isGrpPullback_of_iso e.symm).comp hφ).congr (Category.id_comp _) rfl

end GlobalTheory.DeRham

namespace GlobalTheory.FlagTan

theorem exists_retraction_of_ks_zero : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
      (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' →
      ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left)
        (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i),
        IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π →
        (∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1) →
        ∃ q : A'.left ⟶ A.left, i ≫ q = 𝟙 _ ∧ IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q := by
  intro Pr GD E _ _ _ H Dw l Xo c K _ _ y x' _ _ A _ A' _ π π' i h _ hπ' _ hKS
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  exact GlobalTheory.DeRham.exists_retraction_of_isKSValue_one Pr.p5 GD h hA' gA' hKS

end GlobalTheory.FlagTan
