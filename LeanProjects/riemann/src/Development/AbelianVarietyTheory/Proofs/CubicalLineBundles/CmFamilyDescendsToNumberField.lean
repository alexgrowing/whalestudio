import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyIdentitiesDescendFieldToDedekindStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.FamDesc

theorem exists_field (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt) (k : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ k] (P Q : Out.PolAV (Sp k)) {G H : Over (Sp ℂ)} [GrpObj G] [GrpObj H]
    {φ : G.left ⟶ P.A.left} {m : H.left ⟶ Q.A.left} (hP : IsGrpPullback G P.A (spMap (algebraMap k ℂ)) φ)
    (hQ : IsGrpPullback H Q.A (spMap (algebraMap k ℂ)) m) (f : G ⟶ H) [IsMonHom f] :
    ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ →
      ∀ (G₂ H₂ : Over (Sp k₂)) (φ₂ : G₂.left ⟶ P.A.left) (m₂ : H₂.left ⟶ Q.A.left) (φ₃ : G.left ⟶ G₂.left)
        (m₃ : H.left ⟶ H₂.left), φ₂ ≫ P.A.hom = G₂.hom ≫ spMap (IntermediateField.inclusion h₂).toRingHom →
        IsPullback m₂ H₂.hom Q.A.hom (spMap (IntermediateField.inclusion h₂).toRingHom) →
        φ₃ ≫ G₂.hom = G.hom ≫ spMap (algebraMap k₂ ℂ) → m₃ ≫ H₂.hom = H.hom ≫ spMap (algebraMap k₂ ℂ) →
        φ₃ ≫ φ₂ = φ → m₃ ≫ m₂ = m → ∃ f₂ : G₂ ⟶ H₂, f.left ≫ m₃ = φ₃ ≫ f₂.left := by
  obtain ⟨e, he, he'⟩ := grpPullback_iso hP (isGrpPullback_pullback P.A _)
  obtain ⟨d, hd, hd'⟩ := grpPullback_iso hQ (isGrpPullback_pullback Q.A _)
  obtain ⟨K, f₁, j, hK, -, j₁, j₂, j₃⟩ := hom_descends_to_numberField hT hB k P Q (e.inv ≫ f ≫ d.hom) inferInstance
  have : IsScalarTower ℚ k K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hfin : FiniteDimensional ℚ K := Module.Finite.trans k K
  refine ⟨K.restrictScalars ℚ, hfin, fun k₂ h₂ h₁ G₂ H₂ φ₂ m₂ φ₃ m₃ w₂ c₂ w₃ v₃ e₃ d₃ => ?_⟩
  let q : K →+* k₂ := (IntermediateField.inclusion h₁).toRingHom
  have s₁ : spMap q ≫ spMap (algebraMap k K) = spMap (IntermediateField.inclusion h₂).toRingHom :=
    (spMap_comp_spMap _ _).trans (congrArg spMap (RingHom.ext fun _ => rfl))
  have s₂ : spMap (algebraMap k₂ ℂ) ≫ spMap q = spMap K.val.toRingHom :=
    (spMap_comp_spMap _ _).trans (congrArg spMap (RingHom.ext fun _ => rfl))
  obtain ⟨i, i₁, i₂⟩ : ∃ i : G₂.left ⟶ pullback P.A.hom (spMap (algebraMap k K)),
      i ≫ pullback.fst _ _ = φ₂ ∧ i ≫ pullback.snd _ _ = G₂.hom ≫ spMap q :=
    ⟨pullback.lift φ₂ (G₂.hom ≫ spMap q) (by rw [w₂, Category.assoc, s₁]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have fw : f₁.left ≫ pullback.snd Q.A.hom (spMap (algebraMap k K)) = pullback.snd _ _ := Over.w f₁
  have ew : e.hom.left ≫ pullback.snd P.A.hom (spMap (algebraMap k ℂ)) = G.hom := Over.w e.hom
  have w : (i ≫ f₁.left ≫ pullback.fst _ _) ≫ Q.A.hom =
      G₂.hom ≫ spMap (IntermediateField.inclusion h₂).toRingHom := by
    have h : f₁.left ≫ pullback.fst Q.A.hom (spMap (algebraMap k K)) ≫ Q.A.hom =
        pullback.snd _ _ ≫ spMap (algebraMap k K) :=
      (congrArg (f₁.left ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) fw))
    refine (Category.assoc _ _ _).trans ((congrArg (i ≫ ·) ((Category.assoc _ _ _).trans h)).trans ?_)
    rw [← Category.assoc, i₂, Category.assoc, s₁]
  have key : φ₃ ≫ i = e.hom.left ≫ j := by
    apply pullback.hom_ext
    · exact ((Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) i₁).trans e₃)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₁).trans he')).symm
    · refine ((Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) i₂).trans ?_)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₂).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) ew)))).symm
      rw [← Category.assoc, w₃, Category.assoc, s₂]
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : G₂ ⟶ H₂, f₂.left ≫ m₂ = i ≫ f₁.left ≫ pullback.fst _ _ :=
    ⟨Over.homMk (c₂.lift _ G₂.hom w) (c₂.lift_snd _ _ _), c₂.lift_fst _ _ _⟩
  refine ⟨f₂, c₂.hom_ext ?_ ?_⟩
  · have r : e.hom.left ≫ (e.inv ≫ f ≫ d.hom).left = f.left ≫ d.hom.left := by
      rw [← Over.comp_left, e.hom_inv_id_assoc, Over.comp_left]
    have a₁ : (φ₃ ≫ f₂.left) ≫ m₂ = e.hom.left ≫ j ≫ f₁.left ≫ pullback.fst _ _ :=
      (Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) hf₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) key).trans (Category.assoc _ _ _))))
    rw [a₁, Category.assoc, d₃, ← hd', ← Category.assoc, ← r, Category.assoc]
    exact congrArg (e.hom.left ≫ ·) j₃.symm
  · rw [Category.assoc, Category.assoc, Over.w, v₃, w₃, ← Category.assoc, Over.w]

theorem exists_mul {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj H] {G' H' : Over S'} [GrpObj H']
    {φ : G'.left ⟶ G.left} {m : H'.left ⟶ H.left} (w : φ ≫ G.hom = G'.hom ≫ j) (hm : IsGrpPullback H' H j m)
    {x' y' : G' ⟶ H'} {x y : G ⟶ H} (hx : x'.left ≫ m = φ ≫ x.left) (hy : y'.left ≫ m = φ ≫ y.left) :
    (x' * y').left ≫ m = φ ≫ (x * y).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ w
  have h := hm.2 G' x' y' (φ₀ ≫ x) (φ₀ ≫ y) hx.symm hy.symm
  rw [← MonObj.comp_mul] at h
  rw [← h]
  rfl

end GlobalTheory.CM.FamDesc

namespace GlobalTheory.CM
open FamDesc in

theorem isFam_descends_to_numberField : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (ω : k) (C : Ell H k ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp k)) (L : Submodule (𝓞 E) D.La) (ω' : ℂ) (C' : Ell H ℂ ω') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp ℂ)) (m : SABMap T'.t T.t (spMap (algebraMap k ℂ))) (ψ' : L → (C'.P.A ⟶ T'.t.G)), EllMap C' C (algebraMap k ℂ) φ → IsFam C' T' h L ψ' →
  ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ (ω₂ : k₂) (C₂ : Ell H k₂ ω₂) (φ₂ : C₂.P.A.left ⟶ C.P.A.left) (φ₃ : C'.P.A.left ⟶ C₂.P.A.left) (T₂ : PAT H (Sp k₂)) (m₂ : SABMap T₂.t T.t (spMap (IntermediateField.inclusion h₂).toRingHom)) (m₃ : SABMap T'.t T₂.t (spMap (algebraMap k₂ ℂ))),
    EllMap C₂ C (IntermediateField.inclusion h₂).toRingHom φ₂ → EllMap C' C₂ (algebraMap k₂ ℂ) φ₃ → φ₃ ≫ φ₂ = φ → m₃.φ ≫ m₂.φ = m.φ → ∃ ψ : L → (C₂.P.A ⟶ T₂.t.G), IsFam C₂ T₂ h L ψ ∧ ∀ a, (ψ' a).left ≫ m₃.φ = φ₃ ≫ (ψ a).left := by
  intro hT hL E _ _ _ H k _ ω C D h T L ω' C' φ T' m ψ' hC hF
  have hfin := D.fin
  have : Module.Finite (𝓞 E) L := inferInstance
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have hg : AddMonoid.FG L := AddGroup.fg_iff_addMonoid_fg.1 (Module.Finite.iff_addGroup_fg.1 inferInstance)
  obtain ⟨S, hS⟩ := hg.fg_top
  choose K hK hK' using fun a : L => @exists_field hT hL.polBaseChange k _ C.P T.pol _ _ _ _ _ _ hC.2.1.2.1 m.cart
    (ψ' a) (hF.1 a).isMonHom
  refine ⟨k ⊔ (K 0 ⊔ ⨆ a : S, K a), ?_, le_sup_left, ?_⟩
  · have := hK
    have : FiniteDimensional ℚ (⨆ a : S, K a : IntermediateField ℚ ℂ) := IntermediateField.finiteDimensional_iSup_of_finite
    infer_instance
  intro k₂ h₂ h₁ ω₂ C₂ φ₂ φ₃ T₂ m₂ m₃ e₂ e₃ eφ em
  have gen : ∀ a : L, K a ≤ k₂ → ∃ f₂ : C₂.P.A ⟶ T₂.t.G, (ψ' a).left ≫ m₃.φ = φ₃ ≫ f₂.left := fun a ha =>
    hK' a k₂ h₂ ha C₂.P.A T₂.t.G φ₂ m₂.φ φ₃ m₃.φ e₂.2.1.2.1.1.w m₂.cart.1 e₃.2.1.2.1.1.w m₃.cart.1.w eφ em
  have all : ∀ a : L, ∃ f₂ : C₂.P.A ⟶ T₂.t.G, (ψ' a).left ≫ m₃.φ = φ₃ ≫ f₂.left := by
    intro a
    have ha : a ∈ AddSubmonoid.closure (S : Set L) := hS ▸ AddSubmonoid.mem_top a
    induction ha using AddSubmonoid.closure_induction with
    | mem a ha => exact gen a (((le_iSup (fun a : S => K a) ⟨a, ha⟩).trans (le_sup_right.trans le_sup_right)).trans h₁)
    | zero => exact gen 0 ((le_sup_left.trans le_sup_right).trans h₁)
    | add a b _ _ ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x * y, by rw [hF.2.1]; exact exists_mul e₃.2.1.2.1.1.w m₃.cart hx hy⟩
  choose ψ hψ using all
  exact ⟨ψ, GlobalTheory.T.family_identities_descend_field_to_dedekind hL E H k₂ ω₂ C₂ D h T₂ L ψ ℂ ω' C' (algebraMap k₂ ℂ) φ₃ T' m₃ ψ'
    (algebraMap k₂ ℂ).injective e₃ hψ hF, hψ⟩

end GlobalTheory.CM
end
