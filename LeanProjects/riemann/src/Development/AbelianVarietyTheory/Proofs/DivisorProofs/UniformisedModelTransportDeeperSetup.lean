import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonBaseChangePolarizedAbelianSchemeOfGe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrValuesUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelBaseChangeCompleteDvrExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.Transport

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

open GlobalTheory.Poinc.Extend in

theorem extend {O Ω Γ : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω]
    [IsFractionRing O Ω] {S₁ S₂ T₁ T₂ U K : Scheme.{0}} [U.IsSeparated] {A₁ : Over S₁} {A₂ : Over S₂} {G₁ : Over T₁}
    {G₂ : Over T₂} [GrpObj G₁] [GrpObj G₂] (ab₁ : IsAbelianScheme G₁) (ab₂ : IsAbelianScheme G₂) {σ₁ : T₁ ⟶ S₁}
    {σ₂ : T₂ ⟶ S₂} {α₁ : G₁.left ⟶ A₁.left} {α₂ : G₂.left ⟶ A₂.left} (hα₁ : IsPullback α₁ G₁.hom A₁.hom σ₁)
    (hα₂ : IsPullback α₂ G₂.hom A₂.hom σ₂) (k₁ : Sp O ⟶ T₁) (k₂ : Sp O ⟶ T₂) (β₁ : G₁.left ⟶ U) (β₂ : G₂.left ⟶ U)
    (t₁ : Γ → (S₁ ⟶ A₁.left)) (t₂ : Γ → (S₂ ⟶ A₂.left)) (ht₁ : ∀ x, t₁ x ≫ A₁.hom = 𝟙 _) (ht₂ : ∀ x, t₂ x ≫ A₂.hom = 𝟙 _)
    {P : Over (Sp Ω)} [GrpObj P] {a₁ : P.left ⟶ G₁.left} {a₂ : P.left ⟶ G₂.left}
    (h₁ : IsGrpPullback P G₁ (spMap (algebraMap O Ω) ≫ k₁) a₁) (h₂ : IsGrpPullback P G₂ (spMap (algebraMap O Ω) ≫ k₂) a₂)
    (hβ : a₁ ≫ β₁ = a₂ ≫ β₂)
    (hx : ∀ x, ∃ w : Sp Ω ⟶ P.left, w ≫ a₁ ≫ α₁ = (spMap (algebraMap O Ω) ≫ k₁ ≫ σ₁) ≫ t₁ x ∧
      w ≫ a₂ ≫ α₂ = (spMap (algebraMap O Ω) ≫ k₂ ≫ σ₂) ≫ t₂ x)
    (v : K ⟶ Sp O) {A : Over K} [GrpObj A] {e₁ : A.left ⟶ G₁.left} (he : IsGrpPullback A G₁ (v ≫ k₁) e₁) :
    ∃ e₂ : A.left ⟶ G₂.left, IsGrpPullback A G₂ (v ≫ k₂) e₂ ∧ e₁ ≫ β₁ = e₂ ≫ β₂ ∧
      ∀ x, ∃ w : K ⟶ A.left, w ≫ A.hom = 𝟙 _ ∧ w ≫ e₁ ≫ α₁ = (v ≫ k₁ ≫ σ₁) ≫ t₁ x ∧
        w ≫ e₂ ≫ α₂ = (v ≫ k₂ ≫ σ₂) ≫ t₂ x := by
  obtain ⟨Q₁, _, b₁, g₁⟩ : ∃ (Q : Over (Sp O)) (_ : GrpObj Q) (b : Q.left ⟶ G₁.left), IsGrpPullback Q G₁ k₁ b :=
    ⟨_, _, _, isGrpPullback_pullback G₁ k₁⟩
  obtain ⟨Q₂, _, b₂, g₂⟩ : ∃ (Q : Over (Sp O)) (_ : GrpObj Q) (b : Q.left ⟶ G₂.left), IsGrpPullback Q G₂ k₂ b :=
    ⟨_, _, _, isGrpPullback_pullback G₂ k₂⟩
  obtain ⟨c₁, l₁, rfl⟩ := exists_factor g₁ h₁
  obtain ⟨c₂, l₂, rfl⟩ := exists_factor g₂ h₂
  obtain ⟨d, ld, rfl⟩ := exists_factor g₁ he
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp O) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have hj : IsGenericPointHom (spMap (algebraMap O Ω)) := IsGenericPointHom.fractionField O Ω
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  have s₁ := isSemiAbelian_of_isAbelianScheme Q₁ (PolPull.isAbelianScheme_of_isGrpPullback ab₁ g₁)
  have s₂ := isSemiAbelian_of_isAbelianScheme Q₂ (PolPull.isAbelianScheme_of_isGrpPullback ab₂ g₂)
  have := s₁.smooth
  have := s₂.smooth
  have := s₁.separated
  have := s₂.separated
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₁ s₂ l₁ l₂ (𝟙 P)
  obtain ⟨F', ⟨-, eF'⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₂ s₁ l₂ l₁ (𝟙 P)
  rw [Over.id_left, Category.id_comp] at eF eF'
  let I : Q₁ ≅ Q₂ :=
    ⟨F, F', ExtUnique.over_hom_ext_of_isPullback l₁.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF, ← eF', Over.id_left, Category.comp_id]),
      ExtUnique.over_hom_ext_of_isPullback l₂.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF', ← eF, Over.id_left, Category.comp_id])⟩
  have : IsMonHom I.hom := hF
  have g₂' : IsGrpPullback Q₁ G₂ k₂ (F.left ≫ b₂) :=
    ((isGrpPullback_of_iso I).comp g₂).congr (Category.id_comp _) rfl
  have : IsSchemeTheoreticallyDominant c₁ := .of_isPullback l₁.1.flip
  have hb : b₁ ≫ β₁ = F.left ≫ b₂ ≫ β₂ :=
    ExtUnique.hom_ext_of_dominant (terminal.from U) (terminal.hom_ext _ _) c₁ (by
      rw [← Category.assoc, hβ, eF, Category.assoc, Category.assoc])
  refine ⟨d ≫ F.left ≫ b₂, ld.comp g₂', by rw [Category.assoc, hb, Category.assoc, Category.assoc], fun x => ?_⟩
  obtain ⟨w, u₁, u₂⟩ := hx x
  obtain ⟨d₁, v₁, z₁, w₁⟩ := exists_sec (g₁.1.paste_horiz hα₁) l₁.1.w (t₁ x) (ht₁ x) w (by
    simpa only [Category.assoc] using u₁)
  obtain ⟨d₂, v₂, z₂, w₂⟩ := exists_sec (g₂.1.paste_horiz hα₂) l₂.1.w (t₂ x) (ht₂ x) w (by
    simpa only [Category.assoc] using u₂)
  have : Surjective (w ≫ P.hom) := ⟨fun y => ⟨y, Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
  have hd : d₁ ≫ F.left = d₂ := ext_of_isDominant_of_isSeparated Q₂.hom
    (by rw [Category.assoc, Over.w, z₁, z₂]) ((w ≫ P.hom) ≫ spMap (algebraMap O Ω))
    (by rw [← Category.assoc, w₁, w₂, eF, Category.assoc])
  have sq : (v ≫ d₁) ≫ Q₁.hom = 𝟙 K ≫ v := by rw [Category.assoc, z₁, Category.comp_id, Category.id_comp]
  have e := ld.1.lift_fst _ _ sq
  refine ⟨ld.1.lift _ _ sq, ld.1.lift_snd _ _ sq, ?_, ?_⟩
  · rw [Category.assoc, reassoc_of% e, v₁]; simp only [Category.assoc]
  · rw [Category.assoc, Category.assoc, reassoc_of% e, reassoc_of% hd, v₂]; simp only [Category.assoc]

section Model

variable {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
  [Algebra Ω Ω'] {M : RatModel o Ω} {M' : RatModel o' Ω'} {f : M'.Z ⟶ M.Z}

theorem valF_app (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {U : M.Z.Opens}
    (hU : (U : Set M.Z).Nonempty) (a : Γ(M.Z, U)) :
    valF M'.pt (f ⁻¹ᵁ U) (f.app U a) = algebraMap Ω Ω' (valF M.pt U a) := by
  refine (GlobalTheory.Points.valR_comp M'.pt f U a).symm.trans ?_
  rw [hf]
  exact GlobalTheory.Points.valR_spMap_comp _ M.pt U (M.top_le_preimage_pt hU) a

theorem map_mem_O (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {z : M'.Z} {x : Ω}
    (hx : x ∈ M.O (f z)) : algebraMap Ω Ω' x ∈ M'.O z := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  exact ⟨f ⁻¹ᵁ U, f.app U a, hz, valF_app hf ⟨_, hz⟩ a⟩

theorem val_comp (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {K : Type} [Field K] (y : Sp K ⟶ M'.Z)
    (w : Sp K) {x : Ω} (hx : x ∈ M.O (f (y w))) : M.val (y ≫ f) x = M'.val y (algebraMap Ω Ω' x) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ (f ⁻¹ᵁ U : M'.Z.Opens) := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [RatModel.val_eq h1 (valF_app hf ⟨_, hz⟩ a), RatModel.val_valF (U := U) (by rintro _ ⟨w', rfl⟩; exact h1 ⟨w', rfl⟩)]
  exact GlobalTheory.Points.valR_comp y f U a

end Model

theorem pt_iff {K C R : Type} [CommRing K] [CommRing C] [CommRing R] {A : Over (Sp K)} {G : Over (Sp R)} {h : R →+* K}
    {a : A.left ⟶ G.left} (c : IsPullback a A.hom G.hom (spMap h)) (j : K →+* C) {s : Sp R ⟶ G.left} {w : Sp K ⟶ A.left}
    (hw : w ≫ A.hom = 𝟙 _) (hs : w ≫ a = spMap h ≫ s) (x : Sp C ⟶ A.left) (hx : x ≫ A.hom = spMap j) :
    x ≫ a = spMap (j.comp h) ≫ s ↔ x = spMap j ≫ w := by
  rw [spMap_comp₂, Category.assoc, ← hs]
  constructor
  · intro e
    exact c.hom_ext (by rw [e, Category.assoc]) (by rw [hx, Category.assoc, hw, Category.comp_id])
  · intro e
    rw [e, Category.assoc]

theorem isSeparated_univ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) : Xo.univ.t.G.left.IsSeparated := by
  have := Xo.univ.t.semi.separated
  have : IsSeparated Xo.s := by
    obtain ⟨N, i, hi, -, e⟩ := Xo.qproj
    have : IsSeparated (PSpace.str (KA l) N) := by
      unfold PSpace.str
      infer_instance
    rw [← e]
    infer_instance
  refine ⟨?_⟩
  rw [← terminal.comp_from (Xo.univ.t.G.hom ≫ Xo.s)]
  infer_instance

end GlobalTheory.UPoinc.Transport

open GlobalTheory.UPoinc.Transport in

theorem GlobalTheory.UPoinc.uTest_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame X₁.ρ ρ' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → spMap (ratHull R').val.toRingHom ≫ u' = X₁.uΩ → R' ≤ X₁.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀) (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (u₂' : Sp (ratHull R₂) ⟶ Xo.XF cf), USame D.X.ρ ρ₂ (fun x => x) (RingHom.id _) → ρ₂.i₀ = D.X.ρ.i₀ → spMap (ratHull R₂).val.toRingHom ≫ u₂' = D.X.uΩ → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₂ ρ₂.P.A (spMap (toRat R₂)) α₂ → IsGrpPullback G₂ Xo.univ.t.G (u₂' ≫ pullback.fst _ _) β₂ → LBIso (ρ₂.P.L.pull α₂) (Xo.univ.t.PP.L.pull β₂) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) → (∀ a : D.X.o₁, ‖y₂ (algebraMap D.X.o₁ R₂ a)‖ ≤ 1) → (∃ (P₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj P₀) (a : P₀.left ⟶ G.left) (a₂ : P₀.left ⟶ G₂.left), IsGrpPullback P₀ G (spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom)) a ∧ IsGrpPullback P₀ G₂ (spMap (ratHull R₂).val.toRingHom) a₂ ∧ a ≫ β = a₂ ≫ β₂ ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ P₀.left, w ≫ a ≫ α = spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) ≫ (ρ'.pt x).left ∧ w ≫ a₂ ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt (D.lab x)).left) → ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧ (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧ (∀ x₂ (w₂ : Sp (PadicAlgCl p) ⟶ G₂.left), w₂ ≫ α₂ = x₂.left ≫ u₂.φ → ∃ w : Sp (PadicAlgCl p) ⟶ G.left, w ≫ α = (T x₂).left ≫ u.φ ∧ w ≫ β = w₂ ≫ β₂) ∧ (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧ (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  intro E _ _ _ H Dw l Xo cf C X₁ D p _ z₁ ct y h c₀ hc R' fg frac hth hev ρ' u' _ _ _ hR' G _ α β hα hβ hL y₀ hy₀ u
    c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ u₂' _ _ _ hR₂ G₂ _ α₂ β₂ hα₂ hβ₂ hL₂ y₂ hy₂ _ ⟨P₀, _, a, a₂, ha, ha₂, hab, hpt⟩
  obtain ⟨V₂, _, _, _, _, hV₂c, hV₂n, σ, hσ, hval⟩ :=
    GlobalTheory.UPoinc.exists_complete_dvr_values_unitary E H Dw l Xo cf C X₁ D p z₁ ct y h u.V u.complete u.norm_le
  obtain ⟨u₁, τ, e, T, hτ, hpsi, hT, hfw, hbw⟩ :=
    GlobalTheory.Poinc.UTestBaseChange.baseChange _ _ _ ρ' p y₀ u V₂ hV₂c hV₂n σ hσ
  let j : FractionRing u₁.V →+* PadicAlgCl p := algebraMap _ _
  have hf' : j.comp u₁.yK = y₀ := u₁.fac
  haveI := X₁.ar.char
  haveI := D.X.ar.char
  haveI := isSeparated_univ Xo

  set x₂ := (gPt p ≫ y) (closedPoint (PadicAlgCl p)) with hx₂
  have hx₁ : (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) = D.q x₂ := by
    rw [← h, ← Category.assoc]; rfl
  haveI : IsDedekindDomain D.X.o₁ := ArithBase.ded (Ω := D.X.Ω₁)
  haveI : IsNoetherianRing (D.X.M.O x₂) := D.X.M.isNoetherianRing_O x₂
  haveI : IsIntegrallyClosed (D.X.M.O x₂) := haveI := D.X.normal; RatModel.isIntegrallyClosed_O (GlobalTheory.IsNormalScheme.pred _) x₂
  have hmem : ∀ a : R', algebraMap X₁.Ω₁ D.X.Ω₁ a ∈ D.X.M.O x₂ := fun a =>
    map_mem_O D.gen (hx₁ ▸ hR' a.2)
  let g₁ : R' →+* D.X.M.O x₂ := ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom).codRestrict _ hmem
  let g₂ : R₂ →+* D.X.M.O x₂ := (Subalgebra.inclusion hR₂).toRingHom

  have hrg : Set.range (gPt p ≫ y) = {x₂} := RatModel.range_eq_singleton _ _
  let vO : D.X.M.O x₂ →+* PadicAlgCl p := D.X.M.valHom (gPt p ≫ y) x₂ hrg
  have hvr : ∀ a, vO a ∈ j.range := fun a => by
    obtain ⟨b, hb⟩ := hval a a.2
    exact ⟨τ b, (RingHom.congr_fun hτ b).trans hb⟩
  let jE : FractionRing u₁.V ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict ⟨fun a b hab => j.injective
    (congrArg Subtype.val hab), j.rangeRestrict_surjective⟩
  let v : D.X.M.O x₂ →+* FractionRing u₁.V := jE.symm.toRingHom.comp (vO.codRestrict j.range hvr)
  have hjv : ∀ a, j (v a) = vO a := fun a => congrArg Subtype.val (jE.apply_symm_apply (vO.codRestrict j.range hvr a))
  have hf₂ : j.comp (v.comp g₂) = y₂ := RingHom.ext fun a => (hjv _).trans (hy₂ a).symm
  have hf'v : u₁.yK = v.comp g₁ := RingHom.ext fun a => j.injective <| by
    rw [← RingHom.comp_apply j u₁.yK, hf', hy₀ a, RingHom.comp_apply, hjv]
    show X₁.M.val (gPt p ≫ ct.y) a = D.X.M.val (gPt p ≫ y) (algebraMap X₁.Ω₁ D.X.Ω₁ a)
    rw [← h, ← Category.assoc]
    have hm : (a : X₁.Ω₁) ∈ X₁.M.O (D.q ((gPt p ≫ y) (closedPoint (PadicAlgCl p)))) := hx₁ ▸ hR' a.2
    exact val_comp D.gen (gPt p ≫ y) (closedPoint (PadicAlgCl p)) hm

  have hun : ∀ n : ℤ, n ≠ 0 → IsUnit (n : D.X.M.O x₂) := fun n hn =>
    (RatModel.val_ne_zero_iff hrg _).1 (by
      show vO n ≠ 0
      rw [map_intCast]
      exact Int.cast_ne_zero.2 hn)
  have hunΩ : ∀ n : ℤ, n ≠ 0 → IsUnit (n : D.X.Ω₁) := fun n hn => IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)
  obtain ⟨k₁, hk₁, -⟩ := existsUnique_ratLift R' hun g₁
  obtain ⟨k₂, hk₂, -⟩ := existsUnique_ratLift R₂ hun g₂
  have ek₁ : (algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom = (algebraMap (D.X.M.O x₂) D.X.Ω₁).comp k₁ :=
    (existsUnique_ratLift R' hunΩ ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom)).unique rfl
      (by rw [RingHom.comp_assoc, hk₁]; rfl)
  have ek₂ : (ratHull R₂).val.toRingHom = (algebraMap (D.X.M.O x₂) D.X.Ω₁).comp k₂ :=
    (existsUnique_ratLift R₂ hunΩ R₂.val.toRingHom).unique rfl (by rw [RingHom.comp_assoc, hk₂]; rfl)
  have sk₁ : spMap k₁ ≫ spMap (toRat R') = spMap g₁ := by rw [← spMap_comp₂, hk₁]
  have sk₂ : spMap k₂ ≫ spMap (toRat R₂) = spMap g₂ := by rw [← spMap_comp₂, hk₂]
  have sg₁ : spMap (algebraMap (D.X.M.O x₂) D.X.Ω₁) ≫ spMap k₁ ≫ spMap (toRat R') =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) := by rw [sk₁, ← spMap_comp₂]; rfl
  have sg₂ : spMap (algebraMap (D.X.M.O x₂) D.X.Ω₁) ≫ spMap k₂ ≫ spMap (toRat R₂) = spMap R₂.val.toRingHom := by
    rw [sk₂, ← spMap_comp₂]; rfl
  have sv₁ : spMap v ≫ spMap k₁ ≫ spMap (toRat R') = spMap u₁.yK := by rw [sk₁, ← spMap_comp₂, hf'v]
  have sv₂ : spMap v ≫ spMap k₂ ≫ spMap (toRat R₂) = spMap (v.comp g₂) := by rw [sk₂, ← spMap_comp₂]
  obtain ⟨e₁, he₁, ee₁⟩ := GlobalTheory.Poinc.Extend.exists_factor (j := spMap v ≫ spMap k₁) hα
    (u₁.cart.congr (by rw [Category.assoc, sv₁]) rfl)
  obtain ⟨e₂, he₂, hee, hw⟩ := extend (Γ := X₁.S.Gam) (PolPull.isAbelianScheme_of_isGrpPullback ρ'.P.isAb hα)
    (PolPull.isAbelianScheme_of_isGrpPullback ρ₂.P.isAb hα₂) hα.1 hα₂.1 (spMap k₁) (spMap k₂) β β₂
    (fun x => (ρ'.pt x).left) (fun x => (ρ₂.pt (D.lab x)).left) (fun x => Over.w (ρ'.pt x))
    (fun x => Over.w (ρ₂.pt (D.lab x))) (ha.congr (by rw [ek₁, spMap_comp₂]) rfl)
    (ha₂.congr (by rw [ek₂, spMap_comp₂]) rfl) hab (by rw [sg₁, sg₂]; exact hpt) (spMap v) he₁
  have hcart : IsGrpPullback u₁.A.A ρ₂.P.A (spMap (v.comp g₂)) (e₂ ≫ α₂) :=
    (he₂.comp hα₂).congr (by rw [Category.assoc, sv₂]) rfl
  have hU := Xo.univ.t.PP.isLB
  have hlb : LBIso u₁.A.L (ρ₂.P.L.pull (e₂ ≫ α₂)) :=
    LBIso.trans u₁.A.isLB (pull_isLB ρ'.P.isLB _) (pull_isLB ρ₂.P.isLB _) u₁.lb
      (LBIso.trans (pull_isLB ρ'.P.isLB _) (pull_isLB hU _) (pull_isLB ρ₂.P.isLB _)
        (GenSpread.lbIso_pull_comp e₁ ee₁.symm rfl hL) (GenSpread.lbIso_pull_comp e₂ rfl hee hL₂).symm)
  let u₂ : ρ₂.UTest p y₂ :=
    { V := u₁.V, complete := u₁.complete, norm_le := u₁.norm_le, yK := v.comp g₂, fac := hf₂, A := u₁.A, φ := e₂ ≫ α₂,
      cart := hcart, lb := hlb, G := u₁.G, semi := u₁.semi, D := u₁.D, U := u₁.U }
  refine ⟨u₂, e, T, hpsi, fun x a => ?_, fun x w₂ hw₂ => ⟨x.left ≫ e₁, ?_, ?_⟩, hfw, hbw⟩
  · obtain ⟨w, w₀, w₁, w₂⟩ := hw a
    rw [sv₁, ee₁] at w₁
    rw [sv₂] at w₂
    rw [hT]
    have i₁ := pt_iff u₁.cart.1 j w₀ w₁ x.left (Over.w x)
    have i₂ := pt_iff hcart.1 j w₀ w₂ x.left (Over.w x)
    rw [hf'] at i₁
    rw [hf₂] at i₂
    exact i₂.trans i₁.symm
  · rw [hT, Category.assoc, ee₁]
  · have hw₂' : w₂ ≫ α₂ = (x.left ≫ e₂) ≫ α₂ := hw₂.trans (Category.assoc _ _ _).symm
    have : w₂ = x.left ≫ e₂ := hα₂.1.hom_ext hw₂'
      ((existsUnique_ratPoint R₂ (w₂ ≫ α₂ ≫ ρ₂.P.A.hom)).unique (by rw [Category.assoc, hα₂.1.w])
        (by rw [Category.assoc, ← hα₂.1.w, ← Category.assoc, ← hw₂', Category.assoc]))
    rw [this, Category.assoc, hee, Category.assoc]
