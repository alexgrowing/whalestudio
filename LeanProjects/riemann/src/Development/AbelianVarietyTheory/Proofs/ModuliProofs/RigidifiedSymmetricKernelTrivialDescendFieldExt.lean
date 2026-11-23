import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendFieldStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolDescent

theorem exists_gen_of_unique {Y : Scheme.{0}} [Subsingleton Y] (y₀ : Y) {M : LB Y} (hM : M.IsLB) :
    ∃ t : LB.Gen M, t.IsGen := by
  obtain ⟨i₀, hi₀⟩ := exists_chart hM y₀
  have h : ∀ y, y ∈ M.U i₀ := fun y => by rwa [Subsingleton.elim y y₀]
  have le : ∀ i, M.U i ≤ M.U i ⊓ M.U i₀ := fun i => le_inf le_rfl fun y _ => h y
  refine ⟨⟨fun i => res (le i) (M.g i i₀)⟩, fun i j => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (Eq.symm ((map_mul _ _ _).trans ?_))
  refine (congrArg _ ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _))).trans ?_
  exact gm_cocycle hM _ y hy.1 hy.2 (h y)

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

theorem inv_left_comp (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h A') (𝟙 A'))
  simp only [Hom.inv_def, Category.id_comp] at e
  exact e.trans (congrArg (· ≫ _) (Category.id_comp φ))

theorem kTriv_of_pullback [Flat f] [Surjective f] [IsAffineHom f] (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : Out.KTriv A' L') : Out.KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let R' : Type := Γ(pullback t f, ⊤)
  let e : Spec (CommRingCat.of R') ⟶ pullback t f := (pullback t f).isoSpec.inv
  have : IsIso e := inferInstanceAs (IsIso (pullback t f).isoSpec.inv)
  have : Epi (pullback.fst t f) := Flat.epi_of_flat_of_surjective _
  obtain ⟨q, t', hq, sq⟩ : ∃ (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
      (t' : Spec (CommRingCat.of R') ⟶ S'), Epi q ∧ q ≫ t = t' ≫ f :=
    ⟨e ≫ pullback.fst t f, e ≫ pullback.snd t f, inferInstance, by
      rw [Category.assoc, Category.assoc, pullback.condition]⟩
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have sx : (q ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ sx) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = q ≫ x.left := h.1.lift_fst _ _ _
  have main : x' = toUnit _ ≫ η[A'] := by
    refine hK R' t' x' fun p => ?_
    obtain ⟨V, hV, c, hc⟩ := hx (q p)
    refine ⟨q ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ q)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ q :=
      congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (snd T' A').left ≫ φ = (lift a b).left ≫ (snd T A).left :=
      (congrArg (fun q => q.left) (lift_snd a b)).symm
    have k₃ : ((fst T' A' ≫ x') * snd T' A').left ≫ φ = (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left := by
      have e₀ : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₁ := h.2 (T' ⊗ A') (fst T' A' ≫ x') (snd T' A') (a ≫ x) b
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)) rfl
      rw [← e₀] at e₁
      exact e₁.symm
    obtain ⟨n, hn⟩ : ∃ n : ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ ((fst T A).left ⁻¹ᵁ V).toScheme,
        n ≫ ((fst T A).left ⁻¹ᵁ V).ι = ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫ (lift a b).left :=
      ⟨IsOpenImmersion.lift _ (((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫ (lift a b).left) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    let ψ : Fin 2 → (((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ A'.left) := fun k =>
      ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫
        ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k => ψ k ≫ φ) _ _ n fun k => by
      rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
      fin_cases k
      exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ ψ fun _ => rfl) c₃ h₃
  let a : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk q sq
  have e₁ : pushPt h.1.w x' = 1 := (congrArg _ main).trans (map_one (pushHom h T'))
  have e₂ : a ≫ x = a ≫ (1 : T ⟶ A) :=
    (Over.OverMorphism.ext hx'.symm : a ≫ x = pushPt h.1.w x').trans (e₁.trans (MonObj.comp_one a).symm)
  exact Over.OverMorphism.ext ((cancel_epi q).1 (congrArg (fun z => z.left) e₂))

theorem sym_of_pullback [Subsingleton S'] (s' : S') (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    (desc : ∀ M : LB A.left, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen)
    (hS : Out.Sym A' L') : Out.Sym A L := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨U, hU, c, hc⟩ := hS s'
  obtain ⟨e, he⟩ : ∃ e : A'.left ⟶ (A'.hom ⁻¹ᵁ U).toScheme, e ≫ (A'.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      show A'.hom y ∈ U
      rwa [Subsingleton.elim (A'.hom y) s']), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullSame L' ![(GrpObj.inv : A' ⟶ A').left, 𝟙 _] _ _ e fun k => by
    fin_cases k
    · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) he).trans (Category.id_comp _))).symm
    · exact he.symm) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' c₁ h₁
  obtain ⟨c₃, h₃⟩ := desc _ (DVR.linComb_isLB L hL ![(GrpObj.inv : A ⟶ A).left, 𝟙 _] ![1, -1])
    (gen_chartPull (chartPullOut L _ _ φ _ fun k => by
      fin_cases k
      · exact inv_left_comp h
      · exact (Category.id_comp φ).trans (Category.comp_id φ).symm) c₂ h₂)
  intro s
  refine ⟨⊤, trivial, gen_chartPull (chartPullSame L _ _ _ (A.hom ⁻¹ᵁ ⊤).ι fun k => ?_) c₃ h₃⟩
  fin_cases k
  · rfl
  · exact (Category.comp_id _).symm

theorem rigidified_sym_kTriv_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left) (L₀ : LB A₀.left) (L : LB A.left), IsAbelianScheme A₀ → IsGrpPullback A A₀ (spMap i) φ → L₀.IsLB → L.IsLB → LBIso L (L₀.pull φ) → (Out.Rigidified A L → Out.Rigidified A₀ L₀) ∧ (Out.Sym A L → Out.Sym A₀ L₀) ∧ (Out.KTriv A L → Out.KTriv A₀ L₀) := by
  intro K₀ K _ _ i A₀ A _ _ φ L₀ L hA h hL₀ hL hw
  refine ⟨fun _ => ?_, fun hS => ?_, fun hK => ?_⟩
  · have : Subsingleton (𝟙_ (Over (Sp K₀))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
    exact exists_gen_of_unique (default : PrimeSpectrum K₀) (pull_isLB hL₀ _)
  · have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    exact sym_of_pullback (default : PrimeSpectrum K) h hL₀ hL hw
      (GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ A₀.hom A.hom φ hA.smooth hA.proper hA.geomConnected h.1).1 hS
  · have := GlobalTheory.FieldBaseChange.flat_spMap i
    have := GlobalTheory.FieldBaseChange.surjective_spMap i
    exact kTriv_of_pullback h hL₀ hL hw hK

end GlobalTheory.PolDescent
