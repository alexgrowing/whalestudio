import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsEmbedFunctionFieldRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanIInterSubmodulesOfFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbedsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SecFlatBC

section Helpers

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁]

theorem zero_mem_spanBy (c : R₁ →+* F₁) (T : Set F₁) : (0 : F₁) ∈ spanBy c T :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩

theorem add_mem_spanBy (c : R₁ →+* F₁) (T : Set F₁) {a b : F₁} (ha : a ∈ spanBy c T) (hb : b ∈ spanBy c T) :
    a + b ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := ha
  obtain ⟨m, r', t', ht', rfl⟩ := hb
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using ht i
    · simpa using ht' i
  · rw [Fin.sum_univ_add]; simp

theorem spanBy_mul (c : R₁ →+* F₁) (T : Set F₁) (w : F₁) :
    spanBy c ((w * ·) '' T) = (w * ·) '' spanBy c T := by
  ext v; constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    choose s hs e using ht
    refine ⟨∑ i, c (r i) * s i, ⟨n, r, s, hs, rfl⟩, ?_⟩
    dsimp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← e i]; ring
  · rintro ⟨_, ⟨n, r, t, ht, rfl⟩, rfl⟩
    refine ⟨n, r, fun i => w * t i, fun i => ⟨_, ht i, rfl⟩, ?_⟩
    dsimp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

end Helpers

theorem fnOf_algX {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (U : X.Opens)
    (hg : genericPoint X ∈ U) (a : R) :
    GlobalTheory.Cartier.fnOf U hg (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U a) = GlobalTheory.Desc.cst p a := by
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, GlobalTheory.Desc.cst, RingHom.comp_apply]
  have := X.presheaf.germ_res_apply (homOfLE (show U ≤ p ⁻¹ᵁ ⊤ from le_top)) (genericPoint X) hg
    ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  exact this

theorem span_chart {R R₁ : Type} [CommRing R] [CommRing R₁] {ρ : R →+* R₁} {X Y V : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {p : X ⟶ Sp R} {q : Y ⟶ Sp R₁} {i : V ⟶ Y} [IsOpenImmersion i] {φ : V ⟶ X}
    {θ : X.functionField →+* Y.functionField} (H : IsPullback φ (i ≫ q) p (spMap ρ)) (hP : PFF i φ θ)
    {U : X.Opens} (hU : IsAffineOpen U) (hg : genericPoint X ∈ U) :
    spanBy (GlobalTheory.Desc.cst q) (θ '' Set.range (GlobalTheory.Cartier.fnOf U hg)) =
      {v | ∀ z : V, φ z ∈ U → GlobalTheory.Cartier.RegAt (i z) v} := by
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  letI := ρ.toAlgebra
  obtain ⟨β, -, hβ, hr⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U hU hg
  rw [← hr]
  ext v; constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    choose a ha e using ht
    choose b hb using ha
    refine ⟨∑ j, b j ⊗ₜ[R] r j, ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hβ, hb, e, _root_.mul_comm]
  · rintro ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem_spanBy _ _
    | tmul b r =>
      refine ⟨1, fun _ => r, fun _ => θ (GlobalTheory.Cartier.fnOf U hg b), fun _ => ⟨_, ⟨b, rfl⟩, rfl⟩, ?_⟩
      rw [hβ, Fin.sum_univ_one, _root_.mul_comm]
    | add x y hx hy => rw [map_add]; exact add_mem_spanBy _ _ hx hy

theorem sections_linDisj_flatBaseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), ρ.Flat → ∀ (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), QuasiCompact p → QuasiSeparated p → IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (D : CartierDiv X) (D₁ : CartierDiv Y), PPull i φ θ D D₁ → LinDisj (GlobalTheory.Desc.cst p) (GlobalTheory.Desc.cst q) θ ∧ ∀ k : ℕ, {v | ∀ z : V, (k • D₁).RegularAt (i z) v} = spanBy (GlobalTheory.Desc.cst q) (θ '' Sec D k) := by
  intro R R₁ _ _ ρ hρ X Y V _ _ p q i _ φ θ _ _ H hP D D₁ hD
  letI : Algebra R X.functionField := (GlobalTheory.Desc.cst p).toAlgebra
  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Flat R R₁ := hρ
  obtain ⟨U₀, hU₀, hg₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  have hc : ∀ a : R, θ (algebraMap R X.functionField a) = GlobalTheory.Desc.cst q (algebraMap R R₁ a) := by
    intro a
    letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₀).toAlgebra
    obtain ⟨β, -, hβ, -⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U₀ hU₀ hg₀
    have e : (algebraMap R Γ(X, U₀) a) ⊗ₜ[R] (1 : R₁) = (1 : Γ(X, U₀)) ⊗ₜ[R] (algebraMap R R₁ a) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one a, TensorProduct.smul_tmul]
    have e' := congrArg β e
    simp only [hβ, _root_.map_one, _root_.mul_one, _root_.one_mul] at e'
    rw [← e']
    exact congrArg θ (fnOf_algX p U₀ hg₀ a).symm
  have hinj : ∀ (n : ℕ) (u : Fin n → X.functionField) (r : Fin n → R₁),
      ∑ j, GlobalTheory.Desc.cst q (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0 := by
    letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₀).toAlgebra
    haveI : Nonempty U₀ := ⟨⟨_, hg₀⟩⟩
    haveI : IsFractionRing Γ(X, U₀) X.functionField := functionField_isFractionRing_of_isAffineOpen X U₀ hU₀
    have hal : ∀ b, algebraMap Γ(X, U₀) X.functionField b = GlobalTheory.Cartier.fnOf U₀ hg₀ b := fun b => rfl
    haveI : IsScalarTower R Γ(X, U₀) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun a => ((hal _).trans (fnOf_algX p U₀ hg₀ a)).symm
    obtain ⟨β, hβi, hβ, -⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U₀ hU₀ hg₀
    exact GlobalTheory.T.tensor_fraction_injective_of_tensor_injective R R₁ Γ(X, U₀) X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) β hβi
      (fun b r => (hβ b r).trans (by rw [hal]))
  refine ⟨GlobalTheory.T.linearlyDisjoint_of_flat_baseChange_embeds R R₁ X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) hinj, fun k => ?_⟩
  have hloc : ∀ x : X, ∃ (U : X.Opens) (g : X.functionFieldˣ), IsAffineOpen U ∧ x ∈ U ∧ ∀ y ∈ U, D.IsEqn y g := by
    intro x
    obtain ⟨W, hxW, g, hg⟩ := D.exists_isEqn_nhds x
    obtain ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hxW
    exact ⟨U, g, hU, hxU, fun y hy => hg y (hUW hy)⟩
  choose U g hUa hxU hUg using hloc
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  have cov : ∀ y : X, ∃ j : t, y ∈ U j.1 := fun y => by
    obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨⟨a, ha⟩, h⟩
  haveI : Nonempty t := ⟨(cov (genericPoint X)).choose⟩
  have hgen : ∀ j : t, genericPoint X ∈ U j.1 := fun j => GlobalTheory.Cartier.gen_mem (hxU j.1)
  let N : t → Submodule R X.functionField := fun j =>
    { carrier := {u | ∀ y ∈ U j.1, (k • D).RegularAt y u}
      add_mem' := fun ha hb y hy => (ha y hy).add (hb y hy)
      zero_mem' := fun y _ => ((k • D).vanishesAt_zero y).regularAt
      smul_mem' := fun a u hu y hy => by
        rw [Algebra.smul_def]
        exact (hu y hy).regAt_mul (GlobalTheory.Cartier.regAt_fnOf (U := ⊤) trivial trivial _) }
  have hSec : Sec D k = ⋂ j, (N j : Set X.functionField) := by
    ext u; rw [Set.mem_iInter]
    exact ⟨fun h j y _ => h y, fun h y => let ⟨j, hj⟩ := cov y; h j y hj⟩
  have hG : ∀ j : t, ∀ z : V, φ z ∈ U j.1 →
      (k • D₁).IsEqn (i z) (Units.map θ.toMonoidHom (g j.1 ^ k)) := by
    intro j z hz
    rw [map_pow]
    exact (hD z _ (hUg j.1 _ hz)).nsmul k
  have hN : ∀ j : t, (N j : Set X.functionField) =
      ((((g j.1 ^ k : X.functionFieldˣ) : X.functionField)⁻¹ * ·) '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) := by
    intro j; ext u; constructor
    · intro hu
      have hreg : ∀ y ∈ U j.1, GlobalTheory.Cartier.RegAt y (u * ((g j.1 ^ k : X.functionFieldˣ) : X.functionField)) :=
        fun y hy => ((hUg j.1 y hy).nsmul k).regularAt_iff.1 (hu y hy)
      obtain ⟨b, hb⟩ := GlobalTheory.Cartier.exists_fnOf_eq (hgen j) hreg
      exact ⟨_, ⟨b, rfl⟩, by dsimp only; rw [hb, _root_.mul_comm u, ← _root_.mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), _root_.one_mul]⟩
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩ y hy
      dsimp only
      rw [((hUg j.1 y hy).nsmul k).regularAt_iff, _root_.mul_comm _ ((g j.1 ^ k : X.functionFieldˣ) : X.functionField),
        ← _root_.mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), _root_.one_mul]
      exact GlobalTheory.Cartier.regAt_fnOf hy (hgen j) b
  have hspan : ∀ j : t, spanBy (GlobalTheory.Desc.cst q) (θ '' (N j : Set X.functionField)) =
      {v | ∀ z : V, φ z ∈ U j.1 → (k • D₁).RegularAt (i z) v} := by
    intro j
    set G : X.functionField := ((g j.1 ^ k : X.functionFieldˣ) : X.functionField) with hGdef
    have himg : θ '' ((G⁻¹ * ·) '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) =
        (θ G⁻¹ * ·) '' (θ '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) := by
      rw [Set.image_image, Set.image_image]; simp only [map_mul]
    rw [hN j, himg, spanBy_mul, span_chart H hP (hUa j.1) (hgen j)]
    have hGne : G ≠ 0 := Units.ne_zero _
    have hθG : θ G ≠ 0 := (map_ne_zero θ).2 hGne
    have hval : ∀ z : V, (((Units.map θ.toMonoidHom (g j.1 ^ k)) : Y.functionFieldˣ) : Y.functionField) = θ G :=
      fun _ => rfl
    ext v; constructor
    · rintro ⟨w, hw, rfl⟩ z hz
      rw [(hG j z hz).regularAt_iff, hval z, map_inv₀, _root_.mul_comm, ← _root_.mul_assoc, mul_inv_cancel₀ hθG, _root_.one_mul]
      exact hw z hz
    · intro hv
      refine ⟨v * θ G, fun z hz => ?_, ?_⟩
      · have := (hG j z hz).regularAt_iff.1 (hv z hz)
        rwa [hval z] at this
      · show θ G⁻¹ * (v * θ G) = v
        rw [map_inv₀, _root_.mul_comm, _root_.mul_assoc, mul_inv_cancel₀ hθG, _root_.mul_one]
  have hT : {v | ∀ z : V, (k • D₁).RegularAt (i z) v} =
      ⋂ j : t, {v | ∀ z : V, φ z ∈ U j.1 → (k • D₁).RegularAt (i z) v} := by
    ext v; rw [Set.mem_iInter]
    exact ⟨fun h j z _ => h z, fun h z => let ⟨j, hj⟩ := cov (φ z); h j z hj⟩
  rw [hT, hSec, GlobalTheory.T.span_iInter_submodules_of_flat_baseChange R R₁ X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) hc hinj t N]
  exact Set.iInter_congr fun j => (hspan j).symm

end GlobalTheory.SecFlatBC
