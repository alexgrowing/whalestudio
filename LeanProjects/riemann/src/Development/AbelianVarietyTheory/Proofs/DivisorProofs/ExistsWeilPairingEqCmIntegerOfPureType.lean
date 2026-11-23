import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulOfRankOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEndomorphismOfConjugateAdjointFormStatement

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.PureHom

section Lift

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}

theorem linear_lift_unique (u : HolUnif A L g) (u' : HolUnif A' L' g')
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) (h₁ : ∀ v, IsTangent v → ∃! w, u'.IsDiff w v)
    (f : A ⟶ A') [IsMonHom f] {F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)}
    (hF : ∀ z, u'.ex (F z) = u.ex z ≫ f) (hF' : ∀ z, u'.ex (F' z) = u.ex z ≫ f) : F = F' := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
  exact (h₁ _ (HomLinear.isTangent_comp f hv)).unique (HomLinear.isDiff_comp u u' f F hF hv hd)
    (HomLinear.isDiff_comp u u' f F' hF' hv hd)

end Lift

def diagMul {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (s : E) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z k := ty k s * z k
  map_add' z w := by funext k; simp [mul_add]
  map_smul' c z := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

open PureTriple in

theorem exists_weilEq_smul_of_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (A B : PAT H (Sp ℂ)) (p q : ℕ), p + q = 1 → (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ q)) → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ → Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ g : 𝓞 E, WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) := by
  intro E _ _ _ H A B p q hpq hdet f₁ f₂ hf₁ hf₂
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  obtain ⟨gA, ty, hty⟩ := AllClasses.exists_isTypeFn H p q
  obtain ⟨uA, HA, χA, -, hA, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨uB, HB, χB, -, hB, -⟩ := PureType.exists_isThetaUnif hT B.pol
  obtain ⟨D, Pe, F, hp, hq, hP, hF, hE, hact⟩ := exists_datum_period hT hL A hty hdet uA hA
  obtain ⟨-, -, -, -, -, hA2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A.pol _ uA HA χA hA
  obtain ⟨EfB, hEB, -, -, hB1, hB2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT B.pol _ uB HB χB hB
  obtain ⟨F₁, hF₁, hF₁Λ, -⟩ := HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2
    f₁ hf₁.isMonHom
  obtain ⟨F₂, hF₂, hF₂Λ, -⟩ := HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2
    f₂ hf₂.isMonHom
  choose ρB hρB using fun s : 𝓞 E => (HomLinear.exists_linear_of_isMonHom B.t.G B.t.G B.ab B.ab _ _ _ _ uB uB hB1 hB2
    (B.t.act.act s) (B.t.act.hom s)).imp fun _ h => h.1
  let G : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ) := fun s =>
    F.toLinearMap ∘ₗ diagMul ty (s : E) ∘ₗ F.symm.toLinearMap
  have hG : ∀ s z, uA.ex (G s z) = uA.ex z ≫ A.t.act.act s := fun s z => by
    have e := hact s (F.symm z)
    rw [F.apply_symm_apply] at e
    exact e
  have hGP : ∀ s a, G s (F (Pe a)) = F (Pe (s • a)) := fun s a => by
    simp only [G, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    funext k
    simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, hP.1]
  have hcomm : ∀ (f : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f →
      ∀ Fl : (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ), (∀ z, uB.ex (Fl z) = uA.ex z ≫ f) →
      ∀ s z, Fl (G s z) = ρB s (Fl z) := by
    intro f hf Fl hFl s z
    haveI := hf.isMonHom
    haveI := A.t.act.hom s
    have e := linear_lift_unique uA uB hA2 hB1 (A.t.act.act s ≫ f) (F := Fl ∘ₗ G s) (F' := ρB s ∘ₗ Fl)
      (fun z => by rw [LinearMap.comp_apply, hFl, hG, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, hρB, hFl, hf.comm, Category.assoc])
    exact LinearMap.congr_fun e z
  have hadj : ∀ s z w, hermForm HB (ρB s z) w = hermForm HB z (ρB (H.bar s) w) := fun a =>
    (weilEq_iff_hermForm_eq hT hL B.pol B.pol B.pol B.pol uB uB uB uB HB HB χB χB hB hB (B.t.act.act a) (𝟙 _) (𝟙 _)
      (B.t.act.act (H.bar a)) (ρB a) LinearMap.id LinearMap.id (ρB (H.bar a)) (hρB a)
      (fun _ => (Category.comp_id _).symm) (fun _ => (Category.comp_id _).symm) (hρB _)).1
      (weilEq_of_lamEq hL ℂ B.pol B.pol B.pol B.pol _ _ _ _ (B.t.act.hom a) inferInstance inferInstance
        (B.t.act.hom _) (by
          unfold LamEq
          rw [Category.comp_id, Category.comp_id]
          exact B.t.adj a))
  have mem₁ : ∀ a, F₁ (F (Pe a)) ∈ uB.Λ := fun a => hF₁Λ _ ((hF _).2 ⟨a, rfl⟩)
  have mem₂ : ∀ a, F₂ (F (Pe a)) ∈ uB.Λ := fun a => hF₂Λ _ ((hF _).2 ⟨a, rfl⟩)
  let β : D.La → D.La → ℤ := fun a b => EfB ⟨_, mem₁ a⟩ ⟨_, mem₂ b⟩
  have hβ : ∀ a b, (β a b : ℝ) = (hermForm HB (F₁ (F (Pe a))) (F₂ (F (Pe b)))).im := fun a b => hEB _ _
  have hadd₁ : ∀ x y z, β (x + y) z = β x z + β y z := fun x y z => by
    have e : (⟨_, mem₁ (x + y)⟩ : uB.Λ) = ⟨_, mem₁ x⟩ + ⟨_, mem₁ y⟩ := Subtype.ext (by simp)
    show EfB _ _ = EfB _ _ + EfB _ _
    rw [e, map_add, LinearMap.add_apply]
  have hadd₂ : ∀ x y z, β x (y + z) = β x y + β x z := fun x y z => by
    have e : (⟨_, mem₂ (y + z)⟩ : uB.Λ) = ⟨_, mem₂ y⟩ + ⟨_, mem₂ z⟩ := Subtype.ext (by simp)
    show EfB _ _ = EfB _ _ + EfB _ _
    rw [e, map_add]
  have hadjβ : ∀ (s : 𝓞 E) x y, β (s • x) y = β x (H.bar s • y) := fun s x y => by
    have e : (β (s • x) y : ℝ) = β x (H.bar s • y) := by
      rw [hβ, hβ, ← hGP, ← hGP, hcomm f₁ hf₁ F₁ hF₁, hcomm f₂ hf₂ F₂ hF₂, hadj]
    exact_mod_cast e
  obtain ⟨γ, hγ, hβγ⟩ := GlobalTheory.T.exists_linear_endomorphism_of_conjugate_adjoint_form E H D β hadd₁ hadd₂ hadjβ
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_smul_of_rank_one' E H D (by rw [hp, hq]; exact hpq) γ hγ
  refine ⟨c, (weilEq_iff_hermForm_eq hT hL A.pol A.pol B.pol A.pol uA uA uB uA HB HA χB χA hB hA f₁ f₂
    (A.t.act.act c) (𝟙 _) F₁ F₂ (G c) LinearMap.id hF₁ hF₂ (hG c) (fun _ => (Category.comp_id _).symm)).2 ?_⟩
  refine HermWeil.hermForm_eq_of_im HB HA F₁ F₂ (G c) LinearMap.id uA.full uA.full fun z hz w hw => ?_
  obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.1 ((hF (F.symm z)).1 (by rwa [F.apply_symm_apply]))
  obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 ((hF (F.symm w)).1 (by rwa [F.apply_symm_apply]))
  have ez : z = F (Pe a) := by rw [ha, F.apply_symm_apply]
  have ew : w = F (Pe b) := by rw [hb, F.apply_symm_apply]
  subst ez ew
  rw [← hβ, hβγ, hc, ← hE, LinearMap.id_apply, hGP]

end GlobalTheory.CM.PureHom
end
