import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FV
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedRestrictPullBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsRestrictOpenBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictGradedPullNaturalStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.HodgeAffineIsoType
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace CrystallineSemistableComparison.Om.Nt2.TermAff

theorem mOm_four {K A B₁ B₂ B₃ B₄ C₁ C₂ C₃ : Type} [CommRing K] [CommRing A] [Algebra K A]
    [CommRing B₁] [Algebra K B₁] [CommRing B₂] [Algebra K B₂] [CommRing B₃] [Algebra K B₃] [CommRing B₄] [Algebra K B₄]
    [CommRing C₁] [Algebra K C₁] [CommRing C₂] [Algebra K C₂] [CommRing C₃] [Algebra K C₃]
    {α₁ : A →+* B₁} {α₂ : B₁ →+* B₂} {α₃ : B₂ →+* B₃} {α₄ : B₃ →+* B₄}
    {β₁ : A →+* C₁} {β₂ : C₁ →+* C₂} {β₃ : C₂ →+* C₃} {β₄ : C₃ →+* B₄}
    (h₁ : SemiHom (RingHom.id K) α₁) (h₂ : SemiHom (RingHom.id K) α₂) (h₃ : SemiHom (RingHom.id K) α₃) (h₄ : SemiHom (RingHom.id K) α₄)
    (k₁ : SemiHom (RingHom.id K) β₁) (k₂ : SemiHom (RingHom.id K) β₂) (k₃ : SemiHom (RingHom.id K) β₃) (k₄ : SemiHom (RingHom.id K) β₄)
    (e : ∀ b, α₄ (α₃ (α₂ (α₁ b))) = β₄ (β₃ (β₂ (β₁ b)))) {j : ℕ} (x : Om K A j) :
    h₄.mOm j (h₃.mOm j (h₂.mOm j (h₁.mOm j x))) = k₄.mOm j (k₃.mOm j (k₂.mOm j (k₁.mOm j x))) := by
  have a₂ : SemiHom (RingHom.id K) (α₂.comp α₁) := h₁.comp h₂
  have a₃ : SemiHom (RingHom.id K) (α₃.comp (α₂.comp α₁)) := a₂.comp h₃
  have a₄ : SemiHom (RingHom.id K) (α₄.comp (α₃.comp (α₂.comp α₁))) := a₃.comp h₄
  have b₂ : SemiHom (RingHom.id K) (β₂.comp β₁) := k₁.comp k₂
  have b₃ : SemiHom (RingHom.id K) (β₃.comp (β₂.comp β₁)) := b₂.comp k₃
  have b₄ : SemiHom (RingHom.id K) (β₄.comp (β₃.comp (β₂.comp β₁))) := b₃.comp k₄
  have e' : α₄.comp (α₃.comp (α₂.comp α₁)) = β₄.comp (β₃.comp (β₂.comp β₁)) := RingHom.ext e
  rw [SemiHom.mOm_mOm h₁ h₂ a₂ (fun _ => rfl), SemiHom.mOm_mOm a₂ h₃ a₃ (fun _ => rfl), SemiHom.mOm_mOm a₃ h₄ a₄ (fun _ => rfl),
    SemiHom.mOm_mOm k₁ k₂ b₂ (fun _ => rfl), SemiHom.mOm_mOm b₂ k₃ b₃ (fun _ => rfl), SemiHom.mOm_mOm b₃ k₄ b₄ (fun _ => rfl)]
  have key : ∀ (γ δ : A →+* B₄) (hγ : SemiHom (RingHom.id K) γ) (hδ : SemiHom (RingHom.id K) δ), γ = δ → hγ.mOm j x = hδ.mOm j x := by
    intro γ δ hγ hδ h
    subst h
    rfl
  exact key _ _ a₄ b₄ e'

section Forms

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def fb (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ) : OmU q V a →ₗ[K] OmU (V.ι ≫ q) ⊤ a :=
  (formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V by simp) a).comp (formPull (f := V.ι) rfl V a)

theorem fb_bij (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ) : Function.Bijective (fb q V a) :=
  GlobalTheory.T.forms_restrict_open_bijective q V a

theorem over_res {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q)
    {V : X.Opens} {W : Y.Opens} (h : V ≤ u ⁻¹ᵁ W) : u.resLE W V h ≫ (W.ι ≫ p) = V.ι ≫ q := by
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hu]

theorem fb_nat {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q)
    {V : X.Opens} {W : Y.Opens} (h : V ≤ u ⁻¹ᵁ W) (a : ℕ) (ω : OmU p W a) :
    fb q V a (formRes q h a (formPull hu W a ω)) =
      formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ (u.resLE W V h) ⁻¹ᵁ ⊤ by simp) a
        (formPull (over_res hu h) ⊤ a (fb p W a ω)) := by
  refine mOm_four (semiHom_appSec hu W) (SemiHom.of_algHom (Sec.res q h)) (semiHom_appSec rfl V)
    (SemiHom.of_algHom (Sec.res (V.ι ≫ q) _))
    (semiHom_appSec rfl W) (SemiHom.of_algHom (Sec.res (W.ι ≫ p) _)) (semiHom_appSec (over_res hu h) ⊤)
    (SemiHom.of_algHom (Sec.res (V.ι ≫ q) _)) (fun b => ?_) ω
  have hT1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have hT2 : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := by simp
  have hT3 : (⊤ : V.toScheme.Opens) ≤ (u.resLE W V h) ⁻¹ᵁ ⊤ := by simp
  have key : ∀ (f g : V.toScheme ⟶ Y) (hfg : f = g) (e : ⊤ ≤ f ⁻¹ᵁ W) (e' : ⊤ ≤ g ⁻¹ᵁ W), f.appLE W ⊤ e = g.appLE W ⊤ e' := by
    intro f g hfg e e'
    subst hfg
    rfl
  have e1 := Scheme.Hom.appLE_comp_appLE V.ι u W V ⊤ h hT1
  have e2 := Scheme.Hom.appLE_comp_appLE (u.resLE W V h) W.ι W ⊤ ⊤ hT2 hT3
  have e3 := key _ _ (Scheme.Hom.resLE_comp_ι u h).symm
    (hT1.trans (V.ι.preimage_mono h)) ((hT3.trans ((u.resLE W V h).preimage_mono hT2)))
  exact congrArg (fun φ => φ.hom b) (e1.trans (e3.trans e2.symm))

end Forms

section Main

variable {K : Type} [Field K] {X Y : Scheme.{0}}

abbrev trM (q : X ⟶ Spec (CommRingCat.of K)) (s a : ℕ) :
    CH.Mor (HT.grT (smFun X q) a) ((KS q s {⊤}).ι ⋙ HT.grT (smFun X q) a) (RingHom.id K) :=
  CH.Mor.restrict (HT.grT (smFun X q) a) (KS q s {⊤}).ι

theorem trM_bij (q : X ⟶ Spec (CommRingCat.of K)) (s a : ℕ) (h : a < s) (n : ℕ) : Function.Bijective ((trM q s a).pull n) :=
  GlobalTheory.T.graded_restrict_pull_bijective q {⊤} (by simp) a s h n

theorem ks_top {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} (r : X ⟶ Y) (hr : r ≫ p = q) (s a : ℕ)
    (T) (hT : KS q s {⊤} T) : KS p s {⊤} ((pullM r hr a).G.obj T) :=
  ⟨hT.1, ⊤, rfl, le_of_eq rfl⟩

theorem trM_nat {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} (r : X ⟶ Y) (hr : r ≫ p = q) (s a n : ℕ)
    (hG : ∀ T, KS q s {⊤} T → KS p s {⊤} ((pullM r hr a).G.obj T)) (z : CH.H (HT.grT (smFun Y p) a) n) :
    (morU (pullM r hr a) (U := KS p s {⊤}) (U' := KS q s {⊤}) hG).pull n ((trM p s a).pull n z) =
      (trM q s a).pull n ((pullM r hr a).pull n z) := by
  have h1 := (P.pull_comp (σ'' := RingHom.id K) (trM p s a) (morU (pullM r hr a) (U := KS p s {⊤}) (U' := KS q s {⊤}) hG) n z).1
  have h2 := (P.pull_comp (σ'' := RingHom.id K) (pullM r hr a) (trM q s a) n z).1
  rw [← h1, ← h2]
  rfl

def tq (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ), HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a)
    (m : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a : ℕ),
      CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a) ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a)
        (RingHom.id K))
    (hm : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a n : ℕ), Function.Bijective ((m q V s a).pull n))
    (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) :
    CH.H (FV q V a) a ≃ₗ[K] OmU q V a :=
  haveI : IsAffine V.toScheme := hV
  (LinearEquiv.ofBijective ((m q V (a + 1) a).pull a) (hm q V (a + 1) a a)).symm ≪≫ₗ
    (LinearEquiv.ofBijective ((trM (V.ι ≫ q) (a + 1) a).pull a) (trM_bij _ _ _ (Nat.lt_succ_self a) a)).symm ≪≫ₗ
      e (V.ι ≫ q) a ≪≫ₗ (LinearEquiv.ofBijective (fb q V a) (fb_bij q V a)).symm

theorem tq_spec (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ), HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a)
    (m : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a : ℕ),
      CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a) ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a)
        (RingHom.id K))
    (hm : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a n : ℕ), Function.Bijective ((m q V s a).pull n))
    (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) (z : HT.Hdg (V.ι ≫ q) a a) :
    haveI : IsAffine V.toScheme := hV
    fb q V a (tq e m hm q V hV a ((m q V (a + 1) a).pull a ((trM (V.ι ≫ q) (a + 1) a).pull a z))) = e (V.ι ≫ q) a z := by
  haveI : IsAffine V.toScheme := hV
  have h1 := (LinearEquiv.ofBijective ((m q V (a + 1) a).pull a) (hm q V (a + 1) a a)).symm_apply_apply
    ((trM (V.ι ≫ q) (a + 1) a).pull a z)
  have h2 := (LinearEquiv.ofBijective ((trM (V.ι ≫ q) (a + 1) a).pull a) (trM_bij _ _ _ (Nat.lt_succ_self a) a)).symm_apply_apply z
  have h4 : tq e m hm q V hV a ((m q V (a + 1) a).pull a ((trM (V.ι ≫ q) (a + 1) a).pull a z)) =
      (LinearEquiv.ofBijective (fb q V a) (fb_bij q V a)).symm (e (V.ι ≫ q) a z) := by
    refine congrArg (fun w => (LinearEquiv.ofBijective (fb q V a) (fb_bij q V a)).symm (e (V.ι ≫ q) a w)) ?_
    exact (congrArg (LinearEquiv.ofBijective ((trM (V.ι ≫ q) (a + 1) a).pull a) (trM_bij _ _ _ (Nat.lt_succ_self a) a)).symm h1).trans h2
  rw [h4]
  exact (LinearEquiv.ofBijective (fb q V a) (fb_bij q V a)).apply_symm_apply _

end Main

set_option maxHeartbeats 400000 in

theorem term_aff : ∀ (K : Type) [Field K] [CharZero K],
    ∃ t : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (V : X.Opens), IsAffineOpen V → ∀ a : ℕ,
      CH.H (FV q V a) a ≃ₗ[K] OmU q V a,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (V : X.Opens) (W : Y.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ u ⁻¹ᵁ W)
      (a : ℕ) (hG : ∀ T, KS q (a + 1) {V} T → KS p (a + 1) {W} ((pullM u hu a).G.obj T)) (x : CH.H (FV p W a) a),
      t q V hV a ((morU (pullM u hu a) (U := KS p (a + 1) {W}) (U' := KS q (a + 1) {V}) hG).pull a x) =
        formRes q h a (formPull hu W a (t p W hW a x)) := by
  intro K _ _
  obtain ⟨e, ε, -, he, -, -⟩ := CrystallineSemistableComparison.Om.L2.hodge_affine_iso_sign K
  obtain ⟨m, hm, hn⟩ := GlobalTheory.T.restrict_graded_pull_natural K
  refine ⟨fun q _ V hV a => tq (@e) (@m) (@hm) q V hV a, ?_⟩
  intro X Y q p _ _ u hu V W hV hW h a hG x
  haveI : IsAffine V.toScheme := hV
  haveI : IsAffine W.toScheme := hW
  obtain ⟨y, rfl⟩ := (hm p W (a + 1) a a).2 x
  obtain ⟨z, rfl⟩ := (trM_bij (W.ι ≫ p) (a + 1) a (Nat.lt_succ_self a) a).2 y
  have hh := over_res hu h
  have hG' := ks_top (u.resLE W V h) hh (a + 1) a
  refine (fb_bij q V a).1 ?_
  have s1 := hn q p u hu V W h hh (a + 1) a hG hG' a ((trM (W.ι ≫ p) (a + 1) a).pull a z)
  have s2 := trM_nat (u.resLE W V h) hh (a + 1) a a hG' z
  have s3 := tq_spec (@e) (@m) (@hm) q V hV a ((pullM (u.resLE W V h) hh a).pull a z)
  have s4 := tq_spec (@e) (@m) (@hm) p W hW a z
  have s5 := fb_nat hu h a (tq (@e) (@m) (@hm) p W hW a ((m p W (a + 1) a).pull a ((trM (W.ι ≫ p) (a + 1) a).pull a z)))
  have s6 := he _ _ (u.resLE W V h) hh a z
  have s7 := s1.symm.trans (congrArg ((m q V (a + 1) a).pull a) s2)
  have s8 := (congrArg (fun w => fb q V a (tq (@e) (@m) (@hm) q V hV a w)) s7).trans s3
  have s9 := s5.trans (congrArg (fun w => formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ (u.resLE W V h) ⁻¹ᵁ ⊤ by simp) a
        (formPull (over_res hu h) ⊤ a w)) s4)
  exact s8.trans (s6.trans s9.symm)

end CrystallineSemistableComparison.Om.Nt2.TermAff

example : type_of% CrystallineSemistableComparison.Om.Nt2.TermAff.term_aff := CrystallineSemistableComparison.Om.Nt2.TermAff.term_aff
