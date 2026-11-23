import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.FibreCmp

theorem isDerivAt0_comp_linear {g g' : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g' → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g' → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem valAt'_comp_app {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [Scheme.Hom.app_eq_appLE]
    exact valAt'_appLE _ _ _ _ _ _ h
  · have h' : ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := h
    unfold valAt'
    rw [dif_neg h, dif_neg h']

theorem isDerivAt0_of_isDiff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {Y : Scheme.{0}}
    (φ : A.left ⟶ Y) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)}
    (he : ∀ z, (u.ex z).left ≫ φ = e z) (hv : IsTangent v) (hd : u.IsDiff w v) :
    IsDerivAt0 e w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ) := by
  obtain rfl : (fun z => (show Sp ℂ ⟶ _ from (u.ex z).left) ≫ φ) = e := funext he
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [← Category.assoc]
    refine congrArg (· ≫ φ) (hv.trans ?_)
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp
  · have := hd (φ ⁻¹ᵁ U) hU ((φ.app U).hom f)
    simp only [valAt'_comp_app] at this
    rw [← this, Scheme.Hom.comp_appLE]
    rfl

open FibreUnif in

theorem exists_equiv_of_polAV {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty)
    (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (FU.Di i) ty Pe) (P : Out.PolAV (Sp ℂ))
    (φ : P.A.left ⟶ Xo.univ.t.G.left) (hp : IsGrpPullback P.A Xo.univ.t.G (FU.u i Pe) φ)
    (hL : LBIso P.L (Xo.univ.t.PP.L.pull φ)) {g : ℕ} (u : HolUnif P.A P.L g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {κ : u.Λ → ℂ} (hAH : u.IsAH Hm κ) :
    ∃ F : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left) ∧
      (∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range) ∧
      (∀ a b, (hermForm Hm (F (Pe a)) (F (Pe b))).im = (FU.Di i).EF a b) ∧
      ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ P.A), IsTangent v → (u.IsDiff (F w) v ↔
        IsDerivAt0 (fun z => (FU.ex i Pe z).left) w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ)) := by
  obtain ⟨w, hw⟩ := hL
  obtain ⟨Ef, hEf, -, -, ht₁, ht₂, hweil⟩ := AHWeil.tangent_and_weil_of_isAH thetaUnifAV_all P g u Hm κ hAH
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = y.left ≫ φ → x = y := fun x y h =>
    Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w y]))
  have lift : ∀ x₀ : Over.mk (FU.u i Pe) ⟶ Xo.univ.t.G, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = x₀.left := fun x₀ =>
    ⟨Over.homMk (hp.1.lift x₀.left (𝟙 _) ((Over.w x₀).trans (Category.id_comp _).symm)) (hp.1.lift_snd _ _ _),
      hp.1.lift_fst _ _ _⟩
  choose Φ hΦ using lift
  have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y => inj _ _ (by
    rw [hΦ, ← hp.2 _ (Φ x) (Φ y) (pushPt hp.1.w (Φ x)) (pushPt hp.1.w (Φ y)) rfl rfl]
    exact mul_left_congr (Category.id_comp _).symm _ _ _ _ (hΦ x).symm (hΦ y).symm)
  have Φinj : Function.Injective Φ := fun x y h => Over.OverMorphism.ext (by rw [← hΦ, ← hΦ, h])
  have Φsurj : Function.Surjective Φ := fun x =>
    ⟨Over.homMk (x.left ≫ φ) ((Over.w (pushPt hp.1.w x)).trans (Category.id_comp _)), inj _ _ (hΦ _)⟩
  have Φone : Φ 1 = 1 := by
    have := Φmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have holG : IsHolTo (Set.univ : Set (Fin g₀ → ℂ)) (fun z => (FU.ex i Pe z).left) := by
    have h := (FU.hol i 0 Set.univ (fun _ => Pe) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
    exact isHolTo_slice h 0
  have hol : IsHolTo (Set.univ : Set (Fin g₀ → ℂ)) (fun z => (Φ (FU.ex i Pe z)).left) :=
    isHolTo_of_isPullback hp.1 (e := fun z => (Φ (FU.ex i Pe z)).left) (fun z => Over.w (Φ (FU.ex i Pe z)))
      (by simpa only [hΦ] using holG)
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L g g₀ u ht₁ ht₂ (fun z => Φ (FU.ex i Pe z))
    (fun z z' => by rw [FU.ex_add i Pe hP, Φmul]) hol
  have hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range := fun z => by
    rw [← u.ker, hF, ← FU.ex_ker i Pe hP, ← Φone, Φinj.eq_iff]
  have cΛ : (u.Λ : Set (Fin g → ℂ)).Countable := by
    have := u.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u.Λ)
  have cP : (Pe.range : Set (Fin g₀ → ℂ)).Countable := by
    have := hP.2.2.1
    exact (countable_of_Lindelof_of_discrete : Countable Pe.range)
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz =>
    eq_zero_of_smul_mem_countable cP fun t => (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)
  have Fsurj : Function.Surjective F := surjective_of_countable F cΛ fun v => by
    obtain ⟨x₀, hx₀⟩ := Φsurj (u.ex v)
    obtain ⟨z, rfl⟩ := FU.ex_onto i Pe hP x₀
    refine ⟨z, (u.ker _).1 ?_⟩
    have := u.ex_add (v - F z) (F z)
    rw [sub_add_cancel, hF, hx₀] at this
    exact right_eq_mul.1 this
  have hex : ∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left := fun z => by rw [hF, hΦ]
  let F' := LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩
  have fwd : ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ P.A), IsTangent v → u.IsDiff (F' w) v →
      IsDerivAt0 (fun z => (FU.ex i Pe z).left) w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ) := fun w v hv hd => by
    have h1 := isDerivAt0_of_isDiff u φ (e := fun z => (FU.ex i Pe (F'.symm.toLinearMap z)).left)
      (fun z => by rw [← hex]; exact congrArg (fun t => (u.ex t).left ≫ φ) (F'.apply_symm_apply z).symm) hv hd
    have h2 := (isDerivAt0_comp_linear _ holG F'.symm.toLinearMap _ _).1 h1
    rwa [LinearEquiv.coe_coe, F'.symm_apply_apply] at h2
  refine ⟨F', hex, hΛ, fun a b => ?_, fun w v hv => ⟨fwd w v hv, fun hd => ?_⟩⟩
  · let a' : u.Λ := ⟨F (Pe a), (hΛ _).2 ⟨a, rfl⟩⟩
    let b' : u.Λ := ⟨F (Pe b), (hΛ _).2 ⟨b, rfl⟩⟩
    refine (hEf a' b').symm.trans (congrArg _ (int_eq_of_exp_eq fun k hk => ?_))
    have h₁ := hweil k a' b' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have h₂ := FU.ex_weil i Pe hP k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    have h₃ := weil_eq_of_grpPullback hp Xo.univ.t.PP.isLB P.isLB w hw (Z := Sp ℂ) (t := FU.u i Pe) (t' := 𝟙 _)
      (Category.id_comp _).symm k (u.ex ((k : ℂ)⁻¹ • F (Pe a))) (u.ex ((k : ℂ)⁻¹ • F (Pe b))) _ _
      (by rw [← hex, map_smul]) (by rw [← hex, map_smul]) _ _ h₁ h₂
    exact congrArg Units.val (unitOn_injective h₃)
  · obtain ⟨w', hw', -⟩ := ht₁ v hv
    obtain ⟨w₁, rfl⟩ := F'.surjective w'
    have h1 := fwd w₁ v hv hw'
    let a : epsPt (FU.u i Pe) ⟶ Xo.univ.t.G := Over.homMk ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ)
      (by rw [Category.assoc, hp.1.w, ← Category.assoc]; exact congrArg (· ≫ FU.u i Pe) (Over.w v))
    have e : w = w₁ := ((FU.ex_diff i Pe hP).2 a hd.1).unique hd h1
    rwa [e]

theorem exists_equiv_of_isAH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ' : KA l →+* ℂ) (g₀ : ℕ) (ty : Fin g₀ → (E →+* ℂ)) (Fu : FamilyUnif Xo σ' ty) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g₀ → ℂ)) (y₀ : Sp ℂ ⟶ Xo.X) (s' : Sp ℂ ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s') (m : ObjMap o Xo.univ y₀) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ), IsPeriod (Fu.Di i) ty P → y₀ = Fu.u i P → u.IsAH Hm κ → ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) ∧ (∀ z, h z ∈ u.Λ ↔ z ∈ P.range) ∧ (∀ a b, (herm Hm (h (P a)) (h (P b))).im = (Fu.Di i).EF a b) ∧ ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ o.t.G), IsTangent v → (u.IsDiff (h w) v ↔ IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v.left ≫ m.toSABMap.φ)) := by
  intro E _ _ _ H D l Xo σ' g₀ ty Fu i P y₀ s' o m g u Hm κ hP hy hAH
  subst hy
  obtain ⟨w, hw, -⟩ := m.lin
  exact exists_equiv_of_polAV Fu i hP (GlobalTheory.Obj.toPolAV o) m.toSABMap.φ m.cart ⟨w, hw⟩ u hAH

end GlobalTheory.DetLine.FibreCmp
