import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEntireMulEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TangentVectorExistsUniqueUniformisingVector
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValIsoChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValIso
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPointOverOriginLiftsTangentVectorUniformisedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicUniformizationComplexBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFunctionValuesClassicalUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFibreFrameAtOriginEqRigidificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
noncomputable section

namespace GlobalTheory.MBLow.Cl.GeoOne

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

def frW {x : KeyIn ℂ} {Y : Scheme.{0}} {M : LB Y} {φ : x.P.A.left ⟶ Y} (w : LB.Iso x.P.L (M.pull φ)) {g : ℕ}
    (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u.ex z).left _ (w.s (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z).left)).val *
    u.fr (FrameValue.chartAt x.P.isLB (u.ex z).left) z

variable {x : KeyIn ℂ} {Y : Scheme.{0}} {M : LB Y} {φ : x.P.A.left ⟶ Y} {w : LB.Iso x.P.L (M.pull φ)} {g : ℕ}

theorem frW_eq (hM : M.IsLB) (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) (k : x.P.L.ι)
    (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U k) :
    frW w u j z = valAt' (u.ex z).left _ (w.s (fun _ => j, k)).val * u.fr k z := by
  unfold frW
  have hi := le_chartAt x.P.isLB (u.ex z).left
  rw [u.fr_compat _ k z ((le_preimage_inf _ _ _).2 ⟨hi, hk⟩), ← _root_.mul_assoc]
  exact congrArg (· * u.fr k z) (GlobalTheory.Ex.Arch.FibEx.val_iso _ (pull_isLB hM φ) hw _ _ _
    ((le_preimage_wchart _ _ _ _).2 fun _ => hj) hi hk)

theorem frW_ne (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) :
    frW w u j z ≠ 0 := by
  have hi := le_chartAt x.P.isLB (u.ex z).left
  exact mul_ne_zero (val_unit_ne_zero _ valueRules
    ((le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hi⟩) _) (u.fr_ne _ _ hi)

theorem frW_compat (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (i j : M.ι) (z : Fin g → ℂ)
    (hi : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U i) (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) :
    frW w u i z = valAt' ((u.ex z).left ≫ φ) (M.U i ⊓ M.U j) (M.g i j).val * frW w u j z := by
  unfold frW
  rw [← _root_.mul_assoc]
  exact congrArg (· * _) (GlobalTheory.Ex.Arch.val_iso_chart x.P.isLB hw _ i j _ hi hj (le_chartAt x.P.isLB (u.ex z).left))

theorem frW_hol (hM : M.IsLB) (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (j : M.ι) :
    DifferentiableOn ℂ (frW w u j) {z | ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j} := by
  intro z₀ hz₀
  have hk := le_chartAt x.P.isLB (u.ex z₀).left
  have a : ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ (((M.pull φ).div x.P.L).U (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z₀).left)) :=
    (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hz₀, hk⟩
  obtain ⟨o₂, d₂⟩ := u.hol _ (w.s (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z₀).left)).val
  have n₂ := o₂.mem_nhds a
  have d := (d₂.differentiableAt n₂).fun_mul ((u.fr_hol _).differentiableAt ((u.hol _ 0).1.mem_nhds hk))
  refine (d.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [n₂] with z hz
  obtain ⟨h₁, h₂⟩ := (le_preimage_inf _ _ _).1 hz
  exact frW_eq hM hw u j z _ ((le_preimage_wchart _ _ _ _).1 h₁ PUnit.unit) h₂

theorem valAt'_appLE_comp {X X' : Scheme.{0}} (p : Sp ℂ ⟶ X) (f : X ⟶ X') (U : X'.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (hV : ⊤ ≤ p ⁻¹ᵁ V) (s : Γ(X', U)) : valAt' p V ((f.appLE U V h).hom s) = valAt' (p ≫ f) U s := by
  show valAt' p V (resG X h ((f.app U).hom s)) = _
  rw [valAt'_res _ h _ hV, valAt'_comp]

end GlobalTheory.MBLow.Cl.GeoOne

namespace GlobalTheory.MBLow.Cl.GeoOne

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem tf_hom (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] :
    (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
  simp only [TF, jFK, jK, spMap, Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem eq_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (F : DualNumber A →+* DualNumber B)
    (h1 : ∀ a, F (algebraMap A _ a) = algebraMap B _ (f a)) (h2 : F DualNumber.eps = DualNumber.eps) : F = dualMap f := by
  refine RingHom.ext fun z => ?_
  have hz : z = algebraMap A _ z.fst + algebraMap A _ z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hz, map_add, map_mul, h1, h1, h2]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl, dualMap]

theorem eu_gen (x : KeyIn ℂ) (g : ℕ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) :
    ∀ w, IsTangent w → ∃! W, u.IsDiff W w := by
  subst hg
  exact (GlobalTheory.LamT.existsUnique_isDiff_and_linear x u).1

theorem one_left {S : Scheme.{0}} (X : Over S) [GrpObj X] : (1 : 𝟙_ (Over S) ⟶ X).left = eSec X := by
  have : (1 : 𝟙_ (Over S) ⟶ X) = η[X] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [this]; rfl

end GlobalTheory.MBLow.Cl.GeoOne

namespace GlobalTheory.MBLow.Cl

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue GlobalTheory.MBLow.Cl.GeoOne

theorem exists_ab_geo_of_nf : AllC fun {R} _ _ {D} _ {N} ν => ∀ (y : KeyIn R) (_ : y.P = D.P), HEq y.rig D.rig → (∃ th : D.P.L.Sec, HEq y.th th ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i)) → ∀ (x : KeyIn ℂ) (hg : x.P.g = D.P.g) (hy : y.P.g = D.P.g) (u : HolUnif x.P.A x.P.L D.P.g) (τ : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (a b : Fin D.P.g → ℂ) (c : ℂ) (W : Fin D.P.g → Fin D.P.g → ℂ), KeyPB x y ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) → NF x hg u τ a b c W → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), d.c = c ∧ ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ i, HEq (y.v (i.cast hy.symm)) (vB i)) → ∀ i (bb : TE R ℂ ⟶ D.P.A), bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left → ∀ W', IsD ν d W' bb ↔ W' = W i := by
  intro R _ _ _ _ D hψ hτ _ N ν y hyP hrig hth x hg hy u τ a b c W hpb hnf
  obtain ⟨P, gpos, rig, rig_gen, th, th_ne, v, basis⟩ := y
  subst hyP
  cases hrig
  obtain ⟨th', hth', hνth⟩ := hth
  cases hth'
  obtain ⟨φ, he, w, hg', F, hφ, hw, hrigm, hthm, hF1, hF2, hv⟩ := hpb
  have hnf' := hnf
  obtain ⟨hs, hp, ha, hb, hc, hΛ, hrigu, hfn, hdiff⟩ := hnf'
  obtain ⟨e, he'⟩ := LiePull.exists_pushEquiv hφ (𝟙_ (Over (Sp ℂ))) (TF (R := R) ℂ).hom
    (by rw [tf_hom]; exact (Category.id_comp _).symm)
  have hJ := ν.good
  have hex0 : u.ex 0 = 1 := by
    have := u.ex_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have h0 : (u.ex 0).left ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A := by rw [hex0, one_left]; exact he
  have hrg0 : frW w u (ν.J (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A)) 0 = ν.rg := by
    unfold NumOf.rg vF
    rw [tf_hom]
    exact GlobalTheory.T.uniformisedFibre_frame_at_origin_eq_rigidification R D x φ he w hw hrigm _ u hrigu _ _ (le_chartAt _ _) (hJ _)
  have hrgne : ν.rg ≠ 0 := by
    rw [← hrg0]
    refine frW_ne u _ 0 ?_
    rw [h0]; exact hJ _
  have hthz : ∀ z, sF ν.th ((u.ex z).left ≫ φ) ν.J =
      c * thetaChar τ a b z * frW w u (ν.J ((u.ex z).left ≫ φ)) z := by
    intro z
    have hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := hJ _
    have hle : (D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) fun _ => ν.J ((u.ex z).left ≫ φ)) ≤
        D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := fun q hq => Set.mem_iInter.1 hq 0
    have e0 : sF ν.th ((u.ex z).left ≫ φ) ν.J = valAt' ((u.ex z).left ≫ φ) _ (resG _ hle (th.f (ν.J ((u.ex z).left ≫ φ)))) := by
      rw [← hνth _ hle]; rfl
    rw [e0, valAt'_res _ hle _ ((le_preimage_wchart _ _ _ _).2 fun _ => by rw [Category.comp_id]; exact hj)]
    have hk := le_chartAt x.P.isLB (u.ex z).left
    have hV : ((D.P.L.pull φ).U (fun _ => ν.J ((u.ex z).left ≫ φ))) ⊓ x.P.L.U (FrameValue.chartAt x.P.isLB (u.ex z).left) ≤
        φ ⁻¹ᵁ D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := inf_le_left.trans (LB.wchart_le _ _ _ PUnit.unit)
    have hpV : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((D.P.L.pull φ).U (fun _ => ν.J ((u.ex z).left ≫ φ))) ⊓
        x.P.L.U (FrameValue.chartAt x.P.isLB (u.ex z).left)) :=
      (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hk⟩
    have hm := congrArg (valAt' (u.ex z).left _) (hthm (fun _ => ν.J ((u.ex z).left ≫ φ)) _ hV)
    rw [valAt'_appLE_comp _ _ _ _ hV hpV, valAt'_mul, valAt'_res _ _ _ hpV, hfn _ z hk] at hm
    dsimp only at hm
    rw [hm]
    unfold frW
    have key : ∀ A B C E : ℂ, A = B → A * (C * E) = C * (B * E) := by intros; subst_vars; ring
    exact key _ _ _ _ rfl
  let d : AB N.toNumB D.P.g :=
    { τ := τ, a := a, b := b, c := c, symm := hs, pos := hp, ha := ha, hb := hb, hc := hc
      ex := fun z => ν.eA.symm (e (u.ex z))
      ex_add := fun z w => by simp only [u.ex_add, map_mul]
      onto := fun q => by
        obtain ⟨p, hp⟩ := e.surjective (ν.eA q)
        obtain ⟨z, rfl⟩ := u.ex_onto p
        exact ⟨z, show ν.eA.symm (e (u.ex z)) = q by rw [hp, MulEquiv.symm_apply_apply]⟩
      ker := fun z => by
        rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, u.ker, hΛ]
      fr := fun z => Units.mk0 (frW w u (ν.J ((u.ex z).left ≫ φ)) z / ν.rg) (div_ne_zero (frW_ne u _ z (hJ _)) hrgne)
      fr_zero := by
        ext
        rw [Units.val_mk0, Units.val_one, h0, hrg0, div_self hrgne]
      fr_per := fun M N z => by
        simp only [Units.val_mk0]
        have hl : u.ex (z + perV τ M N) = u.ex z := by
          rw [u.ex_add, (u.ker _).2 ((hΛ _).2 ⟨M, N, rfl⟩), _root_.mul_one]
        unfold frW
        rw [hl, frame_eq_autV_mul _ x hg u τ a b c W hnf M N _ z (le_chartAt _ _)]
        ring
      th := fun z => by
        have h1 := ν.th_eq (ν.eA.symm (e (u.ex z)))
        rw [MulEquiv.apply_symm_apply, he'] at h1
        change N.th _ * ν.rg = _ at h1
        rw [hthz z] at h1
        rw [Units.val_mk0]
        field_simp
        exact h1 }
  have hE : ∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ := fun z => by
    show (ν.eA (ν.eA.symm (e (u.ex z)))).left = _
    rw [MulEquiv.apply_symm_apply, he']
  refine ⟨d, ⟨fun i z => frW w u i z, GlobalTheory.T.holomorphic_functionValues_classicalUniformisation R D N ν _ d x u φ hφ hE, fun i => ?_, fun i j z h => ?_, fun z => ?_,
    fun bb hbb => ?_⟩, rfl, ?_⟩
  · simp only [hE]
    exact frW_hol D.P.isLB hw u i
  · rw [hE] at h ⊢
    exact frW_compat hw u i j z ((le_preimage_inf _ _ _).1 h).1 ((le_preimage_inf _ _ _).1 h).2
  · rw [hE]
    show (frW w u (ν.J ((u.ex z).left ≫ φ)) z / ν.rg) * ν.rg = _
    exact div_mul_cancel₀ _ hrgne
  · obtain ⟨b', hb't, hb'⟩ := GlobalTheory.T.dualPointOverOrigin_lifts_tangentVector_uniformised R D x φ hφ he bb hbb
    obtain ⟨W', hW', -⟩ := eu_gen x _ hg u b' hb't
    exact ⟨W', (GlobalTheory.T.holomorphic_uniformization_complex_base_change R D N ν _ d x u φ hφ hE b' bb hb't hb' W').2 hW'⟩
  · intro vB hvB i bb hbb W'
    have hvi : v i = vB i := by
      have := eq_of_heq (hvB i)
      rwa [Fin.cast_eq_self] at this
    have hF : F = dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := eq_dualMap _ F hF1 hF2
    have hb' : (x.v (i.cast hg.symm)).left ≫ φ = bb.left := by
      rw [hv, hbb, hF, ← hvi]
      rfl
    rw [GlobalTheory.T.holomorphic_uniformization_complex_base_change R D N ν _ d x u φ hφ hE _ bb (x.basis.1 _) hb' W']
    obtain ⟨W0, -, huniq⟩ := eu_gen x _ hg u _ (x.basis.1 (i.cast hg.symm))
    constructor
    · intro h
      exact (huniq _ h).trans (huniq _ (hdiff i)).symm
    · rintro rfl
      exact hdiff i

end GlobalTheory.MBLow.Cl
