import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueCommaOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocOAff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def extMap {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R] →ₐ[R] TrivSqZeroExt (F.obj T') Ω[F.obj T'⁄R] :=
  { semiDiag (semiHom_mp F φ) with
    commutes' := fun r ↦ by
      change semiDiag (semiHom_mp F φ) (algebraMap R _ r) = algebraMap R _ r
      ext
      · rw [fst_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl', (semiHom_mp F φ).map_algebraMap]
      · rw [snd_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl'] }

theorem fst_extMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) :
    (extMap F φ c).fst = mp F φ c.fst := fst_semiDiag _ c

theorem snd_extMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) :
    (extMap F φ c).snd = p1 F φ c.snd := snd_semiDiag _ c

def omExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R])
  map φ := CommAlgCat.ofHom (extMap F φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMap F _ c).trans (mp_id F T _)) ((snd_extMap F _ c).trans (oneFormsMapOfFunctorMorphism_id F _)))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMap F _ c).trans ((mp_comp F φ ψ _).trans (by
      change _ = ((extMap F ψ) (extMap F φ c)).fst
      rw [fst_extMap, fst_extMap])))
    ((snd_extMap F _ c).trans ((oneFormsMapOfFunctorMorphism_comp F φ ψ _).trans (by
      change _ = ((extMap F ψ) (extMap F φ c)).snd
      rw [snd_extMap, snd_extMap]))))

end GlobalTheory.CechDR.FormExt

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem isLocalization_of_data {T T' : C} (l : T ⟶ T') (b : F.obj T) (h1 : IsUnit (mp F l b))
    (h2 : ∀ y : F.obj T', ∃ (n : ℕ) (x : F.obj T), y * mp F l b ^ n = mp F l x)
    (h3 : ∀ x : F.obj T, mp F l x = 0 → ∃ n : ℕ, b ^ n * x = 0) :
    letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
    IsLocalization.Away b (F.obj T') := by
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  refine ⟨?_, fun z ↦ ?_, fun {x y} e ↦ ?_⟩
  · rintro ⟨_, n, rfl⟩
    change IsUnit (mp F l (b ^ n))
    rw [map_pow]; exact h1.pow n
  · obtain ⟨n, x, e⟩ := h2 z
    refine ⟨(x, ⟨b ^ n, n, rfl⟩), ?_⟩
    change z * mp F l (b ^ n) = mp F l x
    rw [map_pow]; exact e
  · obtain ⟨n, hn⟩ := h3 (x - y) (by rw [map_sub]; exact sub_eq_zero.2 e)
    exact ⟨⟨b ^ n, n, rfl⟩, sub_eq_zero.1 (by rw [← mul_sub]; exact hn)⟩

theorem isUnit_mp_omExt_iff {T S : C} (u : T ⟶ S) (c : (omExt F).obj T) :
    IsUnit (mp (omExt F) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_extMap F u c)))

theorem surj_key {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R])
    (y : TrivSqZeroExt (F.obj T') Ω[F.obj T'⁄R]) (a₀ : F.obj T) (η₀ : Ω[F.obj T⁄R]) (k₁ k₂ : ℕ)
    (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀) (hη : mp F l (c.fst ^ k₂) • y.snd = p1 F l η₀) :
    y * extMap F l c ^ (k₁ + k₂ + 1) = extMap F l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_extMap, fst_extMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_extMap, fst_extMap, snd_extMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      oneFormsMapOfFunctorMorphism_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module

theorem ker_key {T : C} (c x : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]
    linear_combination c.fst ^ (m₂ + 1) * h₁
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]
    linear_combination (norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)

theorem hasLoc_omExt (H : Desc.HasLoc F) : Desc.HasLoc (omExt F) := by
  intro T c
  obtain ⟨T', l, h1, h2, h3, h4⟩ := H T c.fst
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  haveI : IsScalarTower R (F.obj T) (F.obj T') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm
  haveI := isLocalization_of_data F l c.fst h1 h2 h3
  have hp : ∀ ω, p1 F l ω = KaehlerDifferential.map R R (F.obj T) (F.obj T') ω :=
    SemiHom.oneFormMap_eq_kaehlerDifferential_map _ fun _ ↦ rfl
  have hs : ∀ (a : F.obj T) (η : Ω[F.obj T'⁄R]), a • η = mp F l a • η := fun a η ↦
    (algebraMap_smul (F.obj T') a η).symm
  refine ⟨T', l, (isUnit_mp_omExt_iff F l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_,
    fun S u hu ↦ h4 S u ((isUnit_mp_omExt_iff F u c).1 hu)⟩
  · obtain ⟨⟨a₀, _, k₁, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers c.fst) y.fst
    obtain ⟨⟨η₀, _, k₂, rfl⟩, hη⟩ := IsLocalizedModule.surj (Submonoid.powers c.fst)
      (KaehlerDifferential.map R R (F.obj T) (F.obj T')) y.snd
    change y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha
    change (c.fst ^ k₂) • y.snd = _ at hη
    rw [hs, ← hp] at hη
    refine ⟨k₁ + k₂ + 1, TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀), ?_⟩
    exact surj_key F l c y a₀ η₀ k₁ k₂ ha hη
  · have e1 : mp F l x.fst = 0 := (fst_extMap F l x).symm.trans (congrArg TrivSqZeroExt.fst hx)
    have e2 : KaehlerDifferential.map R R (F.obj T) (F.obj T') x.snd = 0 :=
      (hp _).symm.trans ((snd_extMap F l x).symm.trans (congrArg TrivSqZeroExt.snd hx))
    obtain ⟨m₁, h₁⟩ := h3 _ e1
    obtain ⟨⟨_, m₂, rfl⟩, h₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst)
      (f := KaehlerDifferential.map R R (F.obj T) (F.obj T')) (x₁ := x.snd) (x₂ := 0)
      (by rw [e2, map_zero])
    rw [smul_zero, Submonoid.smul_def] at h₂
    exact ⟨m₁ + m₂ + 1, ker_key F c x m₁ m₂ h₁ h₂⟩

end GlobalTheory.CechDR.FormExt

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem span_inl_eq_top {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (omExt F).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) Ω[F.obj S⁄R])) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

theorem glue_one_forms : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], [Quiver.IsThin C'] → ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : AffOp X') (s : ∀ t, (T ⟶ G.obj t) → Ω[(OAff s').obj (G.obj t)⁄R']), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 (OAff s') (G.map a) (s t u)) → ∃ ω : Ω[(OAff s').obj T⁄R'], ∀ t u, p1 (OAff s') u ω = s t u) := by
  intro R' _ X' s' C' _ _ G hcov hdir T s hs
  have unit : ∀ {S S' : AffOp X'} (u : S ⟶ S') (b : (OAff s').obj S),
      IsUnit (mp (omExt (OAff s')) u (TrivSqZeroExt.inl b)) → IsUnit (mp (OAff s') u b) :=
    fun u b h ↦ ((isUnit_mp_omExt_iff (OAff s') u _).1 h)
  obtain ⟨x, hx⟩ := GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omExt (OAff s')) G (hasLoc_omExt (OAff s') (hasLoc_OAff s'))
    (fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S u hu ↦ h i S u (unit u _ hu)⟩)
    (fun t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S' u hu ↦ h i S' u (unit u _ hu)⟩)
    T (fun t u ↦ TrivSqZeroExt.inr (s t u)) (fun t t' u a ↦ by
      apply TrivSqZeroExt.ext
      · exact (TrivSqZeroExt.fst_inr _ _).trans (((fst_extMap (OAff s') (G.map a) _).trans
          (by rw [TrivSqZeroExt.fst_inr, map_zero])).symm)
      · exact ((TrivSqZeroExt.snd_inr _ _).trans (hs t t' u a)).trans
          ((snd_extMap (OAff s') (G.map a) _).trans (by rw [TrivSqZeroExt.snd_inr])).symm)
  exact ⟨x.snd, fun t u ↦ (snd_extMap (OAff s') u x).symm.trans
    ((congrArg TrivSqZeroExt.snd (hx t u)).trans (TrivSqZeroExt.snd_inr _ _))⟩

end GlobalTheory.CechDR.FormExt
