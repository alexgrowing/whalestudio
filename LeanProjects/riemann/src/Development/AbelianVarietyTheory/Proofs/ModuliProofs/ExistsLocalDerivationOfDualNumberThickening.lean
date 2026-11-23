import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructureStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.EpsDer

variable {X Y Z : Scheme.{0}}

theorem pull_pull (f : Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (e : f ≫ g = h) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ h ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom a) = (h.appLE U W e₃).hom a := by
  subst e
  exact congrArg (fun φ => φ.hom a) (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)

theorem pull_congr {f g : Y ⟶ X} (e : f = g) {U : X.Opens} {V : Y.Opens}
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE U V e₁).hom a = (g.appLE U V e₂).hom a := by
  subst e
  rfl

theorem res_pull (φ : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((φ.appLE U V h).hom a) = (φ.appLE U W (h'.trans h)).hom a := congrArg (fun ψ => ψ.hom a) (φ.appLE_map h (homOfLE h').op)

theorem pull_res (φ : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U') (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.appLE U' V h).hom (resG X h' a) = (φ.appLE U V (h.trans fun _ hy => h' hy)).hom a := congrArg (fun ψ => ψ.hom a) (φ.map_appLE h (homOfLE h').op)

theorem app_res (φ : Y ⟶ X) {U U' : X.Opens} (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.app U').hom (resG X h' a) = resG Y (fun _ hy => h' hy) ((φ.app U).hom a) := congrArg (fun ψ => ψ.hom a) (φ.naturality (homOfLE h').op)

theorem id_pull {U : X.Opens} (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (a : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom a = a := by
  have key : (𝟙 X : X ⟶ X).appLE U ((𝟙 X : X ⟶ X) ⁻¹ᵁ U) le_rfl = 𝟙 _ :=
    (Scheme.Hom.app_eq_appLE (f := 𝟙 X) (U := U)).symm.trans (Scheme.Hom.id_app U)
  exact congrArg (fun ψ => ψ.hom a) key

theorem spec_pull {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (e : ⊤ ≤ spMap f ⁻¹ᵁ ⊤)
    (a : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (((spMap f).appLE ⊤ ⊤ e).hom a) =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
  have key : (spMap f).appLE ⊤ ⊤ e = (spMap f).appTop :=
    (Scheme.Hom.app_eq_appLE (f := spMap f) (U := ⊤)).symm
  rw [key]
  exact congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem spec_pull_inv {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (e : ⊤ ≤ spMap f ⁻¹ᵁ ⊤)
    (r : R) :
    ((spMap f).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f r) := by
  have key : (spMap f).appLE ⊤ ⊤ e = (spMap f).appTop :=
    (Scheme.Hom.app_eq_appLE (f := spMap f) (U := ⊤)).symm
  rw [key]
  exact (congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem pull_const {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (φ : Y ⟶ X) (p : X ⟶ Sp R)
    (p' : Y ⟶ Sp R') (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (r : R) :
    (φ.appLE U V h).hom (constFn p U r) = constFn p' V (f r) := by
  unfold constFn
  rw [pull_pull φ p (φ ≫ p) rfl (U := ⊤) (V := U) (W := V) (by simp) h (by simp),
    pull_congr hφ (U := ⊤) (V := V) (by simp) (by simp),
    ← pull_pull p' (spMap f) (p' ≫ spMap f) rfl (U := ⊤) (V := ⊤) (W := V) (by simp) (by simp) (by simp),
    spec_pull_inv f (by simp)]

theorem res_const {R : Type} [CommRing R] (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    resG X h (constFn q U a) = constFn q V a := by
  unfold constFn
  exact res_pull q (U := ⊤) (by simp) h _

def constHom {R : Type} [CommRing R] (q : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (q.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem const_eq {R : Type} [CommRing R] (q : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn q U a = constHom q U a := rfl

theorem dual_decomp (x : DualNumber ℂ) :
    x = algebraMap ℂ (DualNumber ℂ) x.fst + DualNumber.eps * algebraMap ℂ (DualNumber ℂ) x.snd := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
private theorem appLE_app_of_comp_eq {A B C : Scheme.{0}} (f : C ⟶ B) (g : B ⟶ A) (k : C ⟶ A) (e : f ≫ g = k)
    {O : A.Opens} {V : C.Opens} (e₁ : V ≤ f ⁻¹ᵁ (g ⁻¹ᵁ O)) (e₂ : V ≤ k ⁻¹ᵁ O) (a : Γ(A, O)) :
    (f.appLE (g ⁻¹ᵁ O) V e₁).hom ((g.app O).hom a) = (k.appLE O V e₂).hom a := by
  rw [Scheme.Hom.app_eq_appLE]
  exact pull_pull f g k e le_rfl e₁ e₂ a
private theorem constFn_eps_mul_self {A : Scheme.{0}} (π : A ⟶ Sp (DualNumber ℂ)) (V : A.Opens) :
    constFn π V DualNumber.eps * constFn π V DualNumber.eps = 0 := by
  rw [const_eq, ← map_mul, DualNumber.eps_mul_eps, map_zero]
private theorem appLE_app_of_section' {A B : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ A) (e : f ≫ g = 𝟙 A) {O : A.Opens}
    (e₁ : O ≤ f ⁻¹ᵁ (g ⁻¹ᵁ O)) (a : Γ(A, O)) : (f.appLE (g ⁻¹ᵁ O) O e₁).hom ((g.app O).hom a) = a := by
  rw [appLE_app_of_comp_eq f g (𝟙 A) e e₁ le_rfl]
  exact id_pull _ a

theorem exists_locDer : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (Φ : Y' ⟶ X), j ≫ Φ = m → Φ ≫ p = π ≫ spMap xD → ∃ d, LocDer q p m (fun r => (xD r).snd) ⊤ d ∧ ∀ (y : Sp ℂ ⟶ Y) (yt : Sp (DualNumber ℂ) ⟶ Y'), yt ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y → yt ≫ π = 𝟙 _ → ∀ (W : X.Opens) (h : ⊤ ≤ (yt ≫ Φ) ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom (((yt ≫ Φ).appLE W ⊤ h).hom f)) = valAt' y (m ⁻¹ᵁ W) (d W f) := by
  intro Y Y' q π ρ j hpb hjρ hjπ R _ xD X p m Φ hm hΦ
  obtain ⟨hO, -, hdec⟩ := GlobalTheory.T.const_thickening_complex_functions_structure Y Y' q π ρ j hpb hjρ hjπ

  have hW : ∀ W : X.Opens, ρ ⁻¹ᵁ (m ⁻¹ᵁ W) = Φ ⁻¹ᵁ W := fun W => by
    subst hm
    exact hO (Φ ⁻¹ᵁ W)
  have hjO : ∀ O : Y.Opens, j ⁻¹ᵁ (ρ ⁻¹ᵁ O) = O := fun O => by
    show (j ≫ ρ) ⁻¹ᵁ O = O
    rw [hjρ]
    rfl

  have uniq : ∀ (O : Y.Opens) (a b a' b' : Γ(Y, O)),
      (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b =
        (ρ.app O).hom a' + constFn π _ DualNumber.eps * (ρ.app O).hom b' → a = a' ∧ b = b' := by
    intro O a b a' b' e
    have := (hdec O ((ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b)).unique
      (y₁ := (a, b)) (y₂ := (a', b')) rfl e
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hex : ∀ (W : X.Opens) (f : Γ(X, W)), ∃ ab : Γ(Y, m ⁻¹ᵁ W) × Γ(Y, m ⁻¹ᵁ W),
      (Φ.appLE W (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (hW W).le).hom f =
        (ρ.app _).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app _).hom ab.2 :=
    fun W f => (hdec (m ⁻¹ᵁ W) _).exists
  choose AB hAB using hex

  have Aeq : ∀ (W : X.Opens) (f : Γ(X, W)), (AB W f).1 = (m.app W).hom f := by
    intro W f
    have e := congrArg (j.appLE (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (m ⁻¹ᵁ W) (hjO _).ge).hom (hAB W f)
    rw [map_add, map_mul, pull_pull j Φ m hm (hW W).le (hjO _).ge le_rfl f,
      appLE_app_of_section' j ρ hjρ (hjO _).ge, appLE_app_of_section' j ρ hjρ (hjO _).ge, pull_const (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom j π q hjπ] at e
    have h0 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom DualNumber.eps = 0 := by simp
    rw [h0, const_eq, map_zero, zero_mul, add_zero] at e
    rw [← e, Scheme.Hom.app_eq_appLE]
  refine ⟨fun W f => (AB W f).2, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro W _ f f'
    refine (uniq _ (AB W (f + f')).1 _ ((AB W f).1 + (AB W f').1) ((AB W f).2 + (AB W f').2) ?_).2
    rw [← hAB W (f + f')]
    simp only [map_add]
    rw [hAB W f, hAB W f']
    ring
  · intro W _ f f'
    rw [← Aeq W f, ← Aeq W f']
    refine (uniq _ (AB W (f * f')).1 _ ((AB W f).1 * (AB W f').1) ((AB W f).1 * (AB W f').2 + (AB W f').1 * (AB W f).2) ?_).2
    rw [← hAB W (f * f')]
    simp only [map_mul, map_add]
    rw [hAB W f, hAB W f']
    linear_combination ((ρ.app _).hom (AB W f).2 * (ρ.app _).hom (AB W f').2) * constFn_eps_mul_self π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W))
  · intro W W' h _ f
    have hOO : m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ W := fun _ hy => h hy
    have hV : ρ ⁻¹ᵁ (m ⁻¹ᵁ W') ≤ ρ ⁻¹ᵁ (m ⁻¹ᵁ W) := fun _ hy => hOO hy
    refine (uniq _ (AB W' (resG X h f)).1 _ (resG Y hOO (AB W f).1) (resG Y hOO (AB W f).2) ?_).2
    rw [← hAB W' (resG X h f), pull_res Φ (hW W').le h f, ← res_pull Φ (hW W).le hV f, hAB W f,
      map_add, map_mul, res_const, ← app_res ρ hOO (AB W f).1, ← app_res ρ hOO (AB W f).2]
  · intro W _ r
    have hc : ∀ c : ℂ, (ρ.app (m ⁻¹ᵁ W)).hom (constFn q (m ⁻¹ᵁ W) c) =
        constFn π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (algebraMap ℂ (DualNumber ℂ) c) := fun c => by
      rw [Scheme.Hom.app_eq_appLE]
      exact pull_const (algebraMap ℂ (DualNumber ℂ)) ρ q π hpb.w le_rfl c
    have e1 : constFn π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (xD r) =
        constFn π _ (algebraMap ℂ (DualNumber ℂ) (xD r).fst) +
          constFn π _ DualNumber.eps * constFn π _ (algebraMap ℂ (DualNumber ℂ) (xD r).snd) := by
      simp only [const_eq]
      rw [← map_mul, ← map_add, ← dual_decomp]
    refine (uniq _ (AB W (constFn p W r)).1 _ (constFn q _ (xD r).fst) (constFn q _ (xD r).snd) ?_).2
    rw [← hAB W (constFn p W r), pull_const xD Φ p π hΦ, e1, hc, hc]
  · intro y yt hy1 hy2 W h f
    have h2 : ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) := by
      intro s _
      have ht : yt ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s) ∈ ρ ⁻¹ᵁ (m ⁻¹ᵁ W) := by
        rw [hW W]
        exact h trivial
      have e : ρ (yt ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s)) =
          y ((spMap (algebraMap ℂ (DualNumber ℂ))) ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s)) :=
        congrArg (fun g : Sp (DualNumber ℂ) ⟶ Y => g ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s)) hy1
      have hs : (spMap (algebraMap ℂ (DualNumber ℂ))) ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s) = s :=
        Subsingleton.elim _ _
      show y s ∈ m ⁻¹ᵁ W
      rw [← hs, ← e]
      exact ht
    have h' : ⊤ ≤ yt ⁻¹ᵁ (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) := by
      rw [hW W]
      exact h
    have e1 : ((yt ≫ Φ).appLE W ⊤ h).hom f = (yt.appLE _ ⊤ h').hom ((Φ.appLE W _ (hW W).le).hom f) :=
      (pull_pull yt Φ (yt ≫ Φ) rfl (hW W).le h' h f).symm
    have e2 : ∀ a : Γ(Y, m ⁻¹ᵁ W), (yt.appLE _ ⊤ h').hom ((ρ.app (m ⁻¹ᵁ W)).hom a) =
        ((spMap (algebraMap ℂ (DualNumber ℂ))).appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((y.appLE _ ⊤ h2).hom a) := by
      intro a
      rw [appLE_app_of_comp_eq yt ρ _ hy1 h' (fun x _ => h2 trivial),
        pull_pull (spMap (algebraMap ℂ (DualNumber ℂ))) y _ rfl h2 (fun _ _ => trivial) (fun x _ => h2 trivial)]
    have e3 : (yt.appLE _ ⊤ h').hom (constFn π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) DualNumber.eps) =
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps := by
      unfold constFn
      rw [pull_pull yt π (𝟙 _) hy2 (U := ⊤) (V := ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (W := ⊤) (fun _ _ => trivial) h'
        (fun _ _ => trivial)]
      exact id_pull _ _
    have e4 : (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps) = DualNumber.eps :=
      congrArg (fun g => CommRingCat.Hom.hom g DualNumber.eps)
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv_hom_id
    show TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom
      (((yt ≫ Φ).appLE W ⊤ h).hom f)) = valAt' y (m ⁻¹ᵁ W) (AB W f).2
    unfold valAt' valAt
    rw [dif_pos h2, e1, hAB W f, map_add, map_mul, e2, e2, e3, map_add, map_mul, e4]
    clear e1 e2 e3 e4 uniq hdec Aeq hAB hO hjO hpb hjρ hjπ hΦ hm
    have s1 := spec_pull (algebraMap ℂ (DualNumber ℂ)) (fun _ _ => trivial) ((y.appLE _ ⊤ h2).hom (AB W f).1)
    have s2 := spec_pull (algebraMap ℂ (DualNumber ℂ)) (fun _ _ => trivial) ((y.appLE _ ⊤ h2).hom (AB W f).2)
    rw [s1, s2]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KS.EpsDer
end
