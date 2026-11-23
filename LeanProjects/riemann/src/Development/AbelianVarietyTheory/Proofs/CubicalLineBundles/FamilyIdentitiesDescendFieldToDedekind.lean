import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPicardGroup
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LineBundleIsoDescendsFieldToDedekindDomainStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FamDescent

theorem lamEq_descend {R k : Type} [CommRing R] [IsDedekindDomain R] [Field k] (f : R →+* k)
    (hf : Function.Injective f) {X Y A B : Over (Sp R)} {X' Y' A' B' : Over (Sp k)} [GrpObj X] [GrpObj Y]
    [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj A'] [IsCommMonObj A'] [GrpObj B'] [IsCommMonObj B']
    (hX : IsAbelianScheme X) (hY : IsAbelianScheme Y)
    {x : X'.left ⟶ X.left} {y : Y'.left ⟶ Y.left} {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}
    (hx : IsPullback x X'.hom X.hom (spMap f)) (hy : IsPullback y Y'.hom Y.hom (spMap f))
    (hA : IsGrpPullback A' A (spMap f) a) (hB : IsGrpPullback B' B (spMap f) b)
    {L : LB A.left} {M : LB B.left} {L' : LB A'.left} {M' : LB B'.left}
    (hL : L.IsLB) (hM : M.IsLB) (hL' : L'.IsLB) (hM' : M'.IsLB) (iL : LBIso (L.pull a) L') (iM : LBIso (M.pull b) M')
    {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B} [IsMonHom f₁] [IsMonHom f₂] [IsMonHom g₁] [IsMonHom g₂]
    {f₁' : X' ⟶ A'} {f₂' : Y' ⟶ A'} {g₁' : X' ⟶ B'} {g₂' : Y' ⟶ B'}
    (e₁ : f₁'.left ≫ a = x ≫ f₁.left) (e₂ : f₂'.left ≫ a = y ≫ f₂.left)
    (e₃ : g₁'.left ≫ b = x ≫ g₁.left) (e₄ : g₂'.left ≫ b = y ≫ g₂.left)
    (H : LamEq L' f₁' f₂' M' g₁' g₂') : LamEq L f₁ f₂ M g₁ g₂ := by
  obtain ⟨Pic, _, cl, pl, hiso, -, -, hcomp, hlin, -⟩ := CechPicMul.exists_picardGroup
  have hpull : ∀ {U V : Scheme.{0}} (N : LB U), N.IsLB → ∀ g : V ⟶ U, (N.pull g).IsLB ∧ cl (N.pull g) = pl g (cl N) :=
    fun N hN g => ⟨(hlin _ _ N hN _ _ _).1, (hlin _ _ N hN _ _ _).2.trans (by simp)⟩
  let π := pullback.fst (X ⊗ Y).hom (spMap f)
  let p := pullback.snd (X ⊗ Y).hom (spMap f)
  have hπ : π ≫ (X ⊗ Y).hom = p ≫ spMap f := pullback.condition
  let u : Over.mk p ⟶ X' := Over.homMk (hx.lift (π ≫ (fst X Y).left) p (by rw [Category.assoc, Over.w, hπ]))
    (hx.lift_snd _ _ _)
  let v : Over.mk p ⟶ Y' := Over.homMk (hy.lift (π ≫ (snd X Y).left) p (by rw [Category.assoc, Over.w, hπ]))
    (hy.lift_snd _ _ _)
  have hu : u.left ≫ x = π ≫ (fst X Y).left := hx.lift_fst _ _ _
  have hv : v.left ≫ y = π ≫ (snd X Y).left := hy.lift_fst _ _ _
  let U : Over.mk ((Over.mk p).hom ≫ spMap f) ⟶ X ⊗ Y := Over.homMk π hπ
  have gen : ∀ {C : Over (Sp R)} {C' : Over (Sp k)} [GrpObj C] [GrpObj C'] {c : C'.left ⟶ C.left}
      (hC : IsGrpPullback C' C (spMap f) c) {N : LB C.left} {N' : LB C'.left}, N.IsLB → N'.IsLB →
      LBIso (N.pull c) N' → ∀ (s : X ⟶ C) (t : Y ⟶ C) (s' : X' ⟶ C') (t' : Y' ⟶ C'),
      s'.left ≫ c = x ≫ s.left → t'.left ≫ c = y ≫ t.left →
      cl ((cubeLB C ![fst X Y ≫ s, snd X Y ≫ t] N).pull π) = cl (cubeLB C' ![u ≫ s', v ≫ t'] N') := by
    intro C C' _ _ c hC N N' hN hN' iN s t s' t' hs ht
    have e : pl c (cl N) = cl N' := (hpull N hN c).2.symm.trans ((hiso _ _ _ (hpull N hN c).1 hN').2 iN)
    refine (hpull _ (LamCalc.cubeLB_isLB hN _) π).2.trans ?_
    refine (congrArg (pl π) (hlin _ _ N hN _ _ _).2).trans (Eq.trans ?_ (hlin _ _ N' hN' _ _ _).2.symm)
    rw [map_prod]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [map_zpow, ← hcomp, ← e, ← hcomp]
    refine congrArg (fun z => pl z (cl N) ^ _) (Eq.symm ?_)
    refine lamBC_psum_push hC _ _ U (fun i => ?_) I.down
    fin_cases i
    · refine Over.OverMorphism.ext ?_
      show (u.left ≫ s'.left) ≫ c = π ≫ (fst X Y).left ≫ s.left
      rw [Category.assoc, hs, ← Category.assoc, hu, Category.assoc]
    · refine Over.OverMorphism.ext ?_
      show (v.left ≫ t'.left) ≫ c = π ≫ (snd X Y).left ≫ t.left
      rw [Category.assoc, ht, ← Category.assoc, hv, Category.assoc]
  have zero : ∀ {C : Over (Sp R)} [GrpObj C] [IsCommMonObj C] {N : LB C.left}, N.IsLB →
      ∀ (s : X ⟶ C) (t : Y ⟶ C), IsMonHom s → IsMonHom t →
      cl ((cubeLB C ![fst X Y ≫ s, snd X Y ≫ t] N).pull (eSec (X ⊗ Y))) = 1 := by
    intro C _ _ N hN s t _ _
    refine (hpull _ (LamCalc.cubeLB_isLB hN _) _).2.trans ?_
    rw [LamCalc.class_cubeLB cl (fun z => pl z (cl N)) (fun I _ φ ε => (hlin _ _ N hN I φ ε).2)]
    have w : ∀ z : X ⊗ Y ⟶ C, η[X ⊗ Y] ≫ z = 1 →
        pl (eSec (X ⊗ Y)) (pl z.left (cl N)) = pl (1 : 𝟙_ (Over (Sp R)) ⟶ C).left (cl N) := fun z hz => by
      rw [← hcomp, ← hz]; rfl
    have o : (1 : 𝟙_ (Over (Sp R)) ⟶ C) = η[C] := by simp [Hom.one_def]
    have h₁ : η[X ⊗ Y] ≫ fst X Y ≫ s = 1 := by rw [o]; exact IsMonHom.one_hom _
    have h₂ : η[X ⊗ Y] ≫ snd X Y ≫ t = 1 := by rw [o]; exact IsMonHom.one_hom _
    simp only [map_mul, map_inv]
    rw [w _ h₁, w _ h₂, w 1 (MonObj.comp_one _), w _ (by rw [MonObj.comp_mul, h₁, h₂, _root_.mul_one])]
    simp
  have cL := LamCalc.cubeLB_isLB hL ![fst X Y ≫ f₁, snd X Y ≫ f₂]
  have cM := LamCalc.cubeLB_isLB hM ![fst X Y ≫ g₁, snd X Y ≫ g₂]
  refine GlobalTheory.T.lineBundleIso_descends_field_to_dedekindDomain R k f hf (X ⊗ Y) (AbelianSchemeGerms.isAbelianScheme_tensor X Y hX hY) _ π p (IsPullback.of_hasPullback _ _)
    _ _ cL cM ?_ ?_
  · exact (hiso _ _ _ (hpull _ cL _).1 (hpull _ cM _).1).1
      ((zero hL f₁ f₂ ‹_› ‹_›).trans (zero hM g₁ g₂ ‹_› ‹_›).symm)
  · refine (hiso _ _ _ (hpull _ cL _).1 (hpull _ cM _).1).1
      ((gen hA hL hL' iL _ _ _ _ e₁ e₂).trans (Eq.trans ?_ (gen hB hM hM' iM _ _ _ _ e₃ e₄).symm))
    exact (hiso _ _ _ (LamCalc.cubeLB_isLB hL' _) (LamCalc.cubeLB_isLB hM' _)).2 (LamCalc.lbIso_of_lamEq H u v)

theorem isFam_descend : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (k : Type) [Field k] (ω' : k) (C' : Ell H k ω') (f : R →+* k) (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp k)) (m : SABMap T'.t T.t (spMap f)) (ψ' : L → (C'.P.A ⟶ T'.t.G)), Function.Injective f → EllMap C' C f φ → (∀ a, (ψ' a).left ≫ m.φ = φ ≫ (ψ a).left) → IsFam C' T' h L ψ' → IsFam C T h L ψ := by
  intro _ E _ _ _ H R _ _ ω C D h T L ψ k _ ω' C' f φ T' m ψ' hf hE hψ hF
  obtain ⟨-, ⟨-, hC, iC⟩, -, hact⟩ := hE
  obtain ⟨hlin, hadd, hsm, hlam⟩ := hF
  have : IsSchemeTheoreticallyDominant (spMap f) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom f) hf
  have : QuasiCompact (spMap f) := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom f)))
  have := C.P.isAb.smooth
  have : Flat C.P.A.hom := inferInstance
  have : IsSeparated T.t.G.hom := T.t.semi.separated
  have hm : ∀ a, IsMonHom (ψ a) := fun a =>
    have := (hlin a).isMonHom
    ExtUnique.isMonHom_of_isGrpPullback hC m.cart (ψ' a) (ψ a) (hψ a)
  refine ⟨fun a => ⟨hm a, fun c => ?_⟩, fun a b => ?_, fun s a => ?_, fun a b => ?_⟩
  · refine ExtUnique.over_hom_ext_of_isPullback hC.1 ?_
    have e := congrArg (fun z => z.left ≫ m.φ) ((hlin a).comm c)
    simp only [Over.comp_left, Category.assoc, Serre.comapAct_act] at e ⊢
    rw [hψ, m.act, ← Category.assoc, ← Category.assoc, hact, hψ, Category.assoc, Category.assoc] at e
    exact e
  · refine ExtUnique.over_hom_ext_of_isPullback hC.1 ?_
    let φ₀ : Over.mk (C'.P.A.hom ≫ spMap f) ⟶ C.P.A := Over.homMk φ hC.1.w
    have e := m.cart.2 C'.P.A (ψ' a) (ψ' b) (φ₀ ≫ ψ a) (φ₀ ≫ ψ b) (hψ a).symm (hψ b).symm
    rw [← MonObj.comp_mul] at e
    rw [← hψ, hadd, ← e]
    rfl
  · refine ExtUnique.over_hom_ext_of_isPullback hC.1 ?_
    rw [← hψ, hsm, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hψ, Category.assoc]
  · have := hm a
    have := hm b
    have := C.act.hom (h a b)
    exact lamEq_descend f hf C.P.isAb C.P.isAb hC.1 hC.1 m.cart hC T.t.PP.isLB C.P.isLB T'.t.PP.isLB C'.P.isLB
      (LBIso.symm (show LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) from m.lin.imp fun _ h => h.1))
      iC (hψ a) (hψ b) (hact _) (by simp) (hlam a b)

end GlobalTheory.FamDescent

end
