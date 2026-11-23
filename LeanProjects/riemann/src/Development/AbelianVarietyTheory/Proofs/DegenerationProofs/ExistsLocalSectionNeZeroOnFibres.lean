import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RegularOfBoundedAtPadicAlgClPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfNormOneGenerators
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory
namespace ThetaLocal
open NormGlue

theorem isUnit_gs_iff_mem {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f y U a) ↔ f y ∈ X.basicOpen a := by
  rw [gs_eq f y U h, ← Scheme.mem_basicOpen Y _ y h, ← Scheme.preimage_basicOpen]
  rfl

theorem fn_eq_of_generic {X : Scheme.{0}} [IsIntegral X] (ξ : X)
    (hξ : ∀ O : X.Opens, (O : Set X).Nonempty → ξ ∈ O) {U : X.Opens} {a b : Γ(X, U)}
    (h : ξ ∈ U → gs (𝟙 X) ξ U a = gs (𝟙 X) ξ U b) : a = b := by
  by_cases hU : (U : Set X).Nonempty
  · have hm : ξ ∈ U := hξ _ hU
    have e := h hm
    rw [gs_eq _ ξ U hm, gs_eq _ ξ U hm] at e
    exact germ_injective_of_isIntegral X (U := U) ξ hm e
  · exact fn_ext fun x hx => (hU ⟨x, hx⟩).elim

theorem exists_push {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (V : Y.Opens) (u : Γ(Y, V)ˣ) :
    ∃ t : Γ(X, f ''ᵁ V)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V → gm (r ≫ f) z _ t = gm r z V u := by
  have h : V ≤ f ⁻¹ᵁ (f ''ᵁ V) := (f.preimage_image_eq V).ge
  let t : Γ(X, f ''ᵁ V)ˣ := Units.map (f.appIso V).inv.hom.toMonoidHom u
  have e' : Semi.res h (pullU f _ t) = u := by
    apply Units.ext
    rw [val_res_pullU, ← Scheme.Hom.appIso_hom']
    exact Iso.inv_hom_id_apply _ _
  refine ⟨t, fun Z r z hz => ?_⟩
  rw [← e', gm_res r z h hz, gm_pull r f z _ (h hz)]

theorem exists_ratio {X G : Scheme.{0}} (p₁ p₂ : X ⟶ G) {E E' : G.Opens} (t : Γ(G, E)ˣ) (t' : Γ(G, E')ˣ)
    (V : X.Opens) (h₁ : V ≤ p₁ ⁻¹ᵁ E) (h₂ : V ≤ p₂ ⁻¹ᵁ E') :
    ∃ u : Γ(X, V)ˣ, (∀ (Y : Scheme.{0}) (r : Y ⟶ X) (y : Y), r y ∈ V →
      gm r y V u = gm (r ≫ p₁) y E t * (gm (r ≫ p₂) y E' t')⁻¹) ∧
      ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ X), Set.range x ⊆ V →
        ‖valF x V u.val‖ * ‖valF (x ≫ p₂) E' t'.val‖ = ‖valF (x ≫ p₁) E t.val‖ := by
  have k : ∀ (Y : Scheme.{0}) (r : Y ⟶ X) (y : Y), r y ∈ V →
      gm r y V (Semi.res h₁ (pullU p₁ E t) * (Semi.res h₂ (pullU p₂ E' t'))⁻¹) =
        gm (r ≫ p₁) y E t * (gm (r ≫ p₂) y E' t')⁻¹ := fun Y r y hy => by
    rw [map_mul, map_inv, gm_res r y h₁ hy, gm_res r y h₂ hy, gm_pull r p₁ y _ (h₁ hy), gm_pull r p₂ y _ (h₂ hy)]
  refine ⟨_, k, fun p _ x hx => ?_⟩
  let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hz := mem_of_range hx z
  rw [← norm_mul]
  congr 1
  apply (toStk z).injective
  rw [map_mul, toStk_valF x _ z hz, toStk_valF (x ≫ p₁) _ z (h₁ hz), toStk_valF (x ≫ p₂) _ z (h₂ hz), k _ x z hz,
    ← Units.val_mul, inv_mul_cancel_right]

theorem exists_local_section {G Z X : Scheme.{0}} (p₁ p₂ : X ⟶ G) [IsIntegral X] (π : X ⟶ Sp ℤ)
    [Flat π] [LocallyOfFiniteType π] (hX : Geo.Tor.IsNormalScheme X) (h : G ⟶ Z) (hp : IsPullback p₁ p₂ h h)
    (M : LB G) (E : M.ι → G.Opens) (hE : ∀ i, E i ≤ M.U i)
    (hne : ∀ i, (M.U i : Set G).Nonempty → (E i : Set G).Nonempty) (t : ∀ i, Γ(G, E i)ˣ)
    (ht : ∀ i k (Y : Scheme.{0}) (r : Y ⟶ G) (y : Y), r y ∈ E i → r y ∈ E k →
      gm r y _ (t i) = gm r y _ (M.g i k) * gm r y _ (t k))
    (Om : Set G) (hδ : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ Z), ∃ δ : ℝ, 0 < δ ∧
      ∀ (b : Sp (OO p) ⟶ G) (i : M.ι), (gPt p ≫ b) ≫ h = y → b (cPt p) ∈ M.U i → Set.range (gPt p ≫ b) ⊆ E i →
        ‖valF (gPt p ≫ b) _ (t i).val‖ ≤ δ ∧ (b (cPt p) ∈ Om → ‖valF (gPt p ≫ b) _ (t i).val‖ = δ))
    (W : G.Opens) (i₀ : M.ι) (hW : W ≤ M.U i₀) (hWO : (W : Set G) ⊆ Om) (hWne : (W : Set G).Nonempty)
    (N : Z.Opens) (b : N.toScheme ⟶ G) (hb : b ≫ h = N.ι) (hbW : ∀ z, b z ∈ W) :
    ∃ σ : LB.Sec (M.pull (h ⁻¹ᵁ N).ι), ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, h ((h ⁻¹ᵁ N).ι x) = z' := by
  obtain ⟨ξ, hξ⟩ := exists_generic X
  let Δ : G ⟶ X := hp.lift (𝟙 G) (𝟙 G) rfl
  have g₁ : ∀ O : G.Opens, (O : Set G).Nonempty → p₁ ξ ∈ O := fun O ⟨y, hy⟩ =>
    hξ (p₁ ⁻¹ᵁ O) ⟨Δ y, by
      change (Δ ≫ p₁) y ∈ O
      rw [hp.lift_fst]; exact hy⟩
  have g₂ : ∀ O : G.Opens, (O : Set G).Nonempty → p₂ ξ ∈ O := fun O ⟨y, hy⟩ =>
    hξ (p₂ ⁻¹ᵁ O) ⟨Δ y, by
      change (Δ ≫ p₂) y ∈ O
      rw [hp.lift_snd]; exact hy⟩
  have hW₁ := g₁ W hWne
  have hW₂ := g₂ W hWne
  have hE₂ := g₂ (E i₀) (hne _ ⟨_, hW hW₂⟩)
  have hE₁ : ∀ k, p₁ ξ ∈ M.U k → p₁ ξ ∈ E k := fun k hk => g₁ _ (hne _ ⟨_, hk⟩)
  have ll := GlobalTheory.regular_of_bounded_at_padicAlgCl_points.2 X π hX
  have nrm : ∀ k (V : X.Opens) (h₁ : V ≤ p₁ ⁻¹ᵁ E k) (h₂ : V ≤ p₂ ⁻¹ᵁ E i₀), ∃ u : Γ(X, V)ˣ,
      (ξ ∈ V → gm (𝟙 X) ξ V u = gm p₁ ξ _ (t k) * (gm p₂ ξ _ (t i₀))⁻¹) ∧
      ∀ (p : ℕ) [Fact p.Prime] (c : Sp (OO p) ⟶ X), p₁ (c (cPt p)) ∈ M.U k → p₂ (c (cPt p)) ∈ W →
        Set.range (gPt p ≫ c) ⊆ V → ‖valF (gPt p ≫ c) V u.val‖ ≤ 1 ∧
          (p₁ (c (cPt p)) ∈ W → ‖valF (gPt p ≫ c) V u.val‖ = 1) := by
    intro k V h₁ h₂
    obtain ⟨u, hu, hu'⟩ := exists_ratio p₁ p₂ (t k) (t i₀) V h₁ h₂
    refine ⟨u, fun hm => by simpa only [Category.id_comp] using hu _ (𝟙 X) ξ hm, fun p _ c c₁ c₂ hc => ?_⟩
    obtain ⟨δ, hδ₀, H⟩ := hδ p ((gPt p ≫ c ≫ p₁) ≫ h)
    have e := hu' p _ hc
    have a₁ := H (c ≫ p₁) k rfl c₁ (by rintro _ ⟨s, rfl⟩; exact h₁ (hc ⟨s, rfl⟩))
    have a₂ := (H (c ≫ p₂) i₀ (by simp only [Category.assoc, hp.w]) (hW c₂)
      (by rintro _ ⟨s, rfl⟩; exact h₂ (hc ⟨s, rfl⟩))).2 (hWO c₂)
    rw [Category.assoc, Category.assoc, a₂] at e
    refine ⟨?_, fun c₃ => ?_⟩
    · have := a₁.1
      rw [← e] at this
      exact le_of_mul_le_mul_right (by simpa using this) hδ₀
    · have := a₁.2 (hWO c₃)
      rw [← e] at this
      exact mul_right_cancel₀ hδ₀.ne' (by simpa using this)
  have key : ∀ k, ∃ f : Γ(X, p₁ ⁻¹ᵁ M.U k ⊓ p₂ ⁻¹ᵁ W), p₁ ξ ∈ M.U k →
      gs (𝟙 X) ξ _ f = (gm p₁ ξ _ (t k) * (gm p₂ ξ _ (t i₀))⁻¹).val := by
    intro k
    by_cases hk : p₁ ξ ∈ M.U k
    · have hm : ξ ∈ p₁ ⁻¹ᵁ E k ⊓ p₂ ⁻¹ᵁ E i₀ ⊓ p₂ ⁻¹ᵁ W := ⟨⟨hE₁ k hk, hE₂⟩, hW₂⟩
      obtain ⟨u, hu, hu'⟩ := nrm k (p₁ ⁻¹ᵁ E k ⊓ p₂ ⁻¹ᵁ E i₀ ⊓ p₂ ⁻¹ᵁ W) (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right)
      have le : p₁ ⁻¹ᵁ E k ⊓ p₂ ⁻¹ᵁ E i₀ ⊓ p₂ ⁻¹ᵁ W ≤ p₁ ⁻¹ᵁ M.U k ⊓ p₂ ⁻¹ᵁ W :=
        fun x hx => ⟨hE k hx.1.1, hx.2⟩
      obtain ⟨f, hf, -⟩ := (ll _ _ le u.val ⟨ξ, hm⟩).1 fun p _ c hc hr => (hu' p c hc.1 hc.2 hr).1
      refine ⟨f, fun _ => ?_⟩
      rw [← hu hm, ← gs_unit _ ξ _ hm, ← hf, gs_res _ ξ le hm]
    · exact ⟨0, fun hk' => (hk hk').elim⟩
  choose f hf using key
  have compat : ∀ k k' (Y : Scheme.{0}) (r : Y ⟶ X) (y : Y), p₁ (r y) ∈ M.U k → p₁ (r y) ∈ M.U k' → p₂ (r y) ∈ W →
      gs r y _ (f k) = (gm (r ≫ p₁) y _ (M.g k k')).val * gs r y _ (f k') := by
    intro k k'
    let O : X.Opens := p₁ ⁻¹ᵁ (M.U k ⊓ M.U k') ⊓ p₂ ⁻¹ᵁ W
    have l₁ : O ≤ p₁ ⁻¹ᵁ M.U k ⊓ p₂ ⁻¹ᵁ W := fun x hx => ⟨hx.1.1, hx.2⟩
    have l₂ : O ≤ p₁ ⁻¹ᵁ M.U k' ⊓ p₂ ⁻¹ᵁ W := fun x hx => ⟨hx.1.2, hx.2⟩
    have l₃ : O ≤ p₁ ⁻¹ᵁ (M.U k ⊓ M.U k') := inf_le_left
    have ev : ∀ (Y : Scheme.{0}) (r : Y ⟶ X) (y : Y), r y ∈ O →
        gs r y O (resG X l₁ (f k)) = gs r y _ (f k) ∧
        gs r y O ((Semi.res l₃ (pullU p₁ _ (M.g k k'))).val * resG X l₂ (f k')) =
          (gm (r ≫ p₁) y _ (M.g k k')).val * gs r y _ (f k') := fun Y r y hy =>
      ⟨gs_res r y l₁ hy _, by
        rw [gs_mul r y _ hy, gs_unit r y _ hy, gm_res r y l₃ hy, gm_pull r p₁ y _ (l₃ hy), gs_res r y l₂ hy]⟩
    have e : resG X l₁ (f k) = (Semi.res l₃ (pullU p₁ _ (M.g k k'))).val * resG X l₂ (f k') := by
      refine fn_eq_of_generic ξ hξ fun hm => ?_
      obtain ⟨e₁, e₂⟩ := ev _ (𝟙 X) ξ hm
      rw [e₁, e₂, hf k hm.1.1, hf k' hm.1.2, Category.id_comp, ht k k' _ p₁ ξ (hE₁ k hm.1.1) (hE₁ k' hm.1.2),
        ← Units.val_mul, _root_.mul_assoc]
    intro Y r y a₁ a₂ a₃
    obtain ⟨e₁, e₂⟩ := ev _ r y ⟨⟨a₁, a₂⟩, a₃⟩
    rw [← e₁, ← e₂, e]
  have unit : ∀ (Y : Scheme.{0}) (r : Y ⟶ X) (y : Y), p₁ (r y) ∈ W → p₂ (r y) ∈ W → IsUnit (gs r y _ (f i₀)) := by
    have hm : ξ ∈ p₁ ⁻¹ᵁ E i₀ ⊓ p₂ ⁻¹ᵁ E i₀ ⊓ (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ W) := ⟨⟨hE₁ _ (hW hW₁), hE₂⟩, hW₁, hW₂⟩
    obtain ⟨u, hu, hu'⟩ := nrm i₀ (p₁ ⁻¹ᵁ E i₀ ⊓ p₂ ⁻¹ᵁ E i₀ ⊓ (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ W)) (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)
    obtain ⟨ψ, hψ, e⟩ := (ll _ _ inf_le_right u.val ⟨ξ, hm⟩).2 u.isUnit fun p _ c hc hr =>
      (hu' p c (hW hc.1) hc.2 hr).2 hc.1
    have le : p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ W ≤ p₁ ⁻¹ᵁ M.U i₀ ⊓ p₂ ⁻¹ᵁ W := fun x hx => ⟨hW hx.1, hx.2⟩
    have e' : resG X le (f i₀) = ψ := by
      refine fn_eq_of_generic ξ hξ fun hm' => ?_
      rw [gs_res _ ξ le hm', hf i₀ (hW hW₁), ← hu hm, ← gs_unit _ ξ _ hm, ← e, gs_res _ ξ inf_le_right hm]
    intro Y r y a₁ a₂
    have hy : r y ∈ p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ W := ⟨a₁, a₂⟩
    rw [← gs_res r y le hy, e', gs_eq r y _ hy]
    exact (hψ.map _).map _
  let q : (h ⁻¹ᵁ N).toScheme ⟶ X := hp.lift (h ⁻¹ᵁ N).ι (h ∣_ N ≫ b) (by rw [Category.assoc, hb, morphismRestrict_ι])
  have q₁ : q ≫ p₁ = (h ⁻¹ᵁ N).ι := hp.lift_fst _ _ _
  have q₂ : q ≫ p₂ = h ∣_ N ≫ b := hp.lift_snd _ _ _
  have r₁ : ∀ x, p₁ (q x) = (h ⁻¹ᵁ N).ι x := fun x => by rw [← q₁]; rfl
  have r₂ : ∀ x, p₂ (q x) = b ((h ∣_ N) x) := fun x => congrArg (fun s : (h ⁻¹ᵁ N).toScheme ⟶ G => s x) q₂
  have le : ∀ J, (M.pull (h ⁻¹ᵁ N).ι).U J ≤ q ⁻¹ᵁ (p₁ ⁻¹ᵁ M.U (J PUnit.unit) ⊓ p₂ ⁻¹ᵁ W) := fun J x hx =>
    ⟨show p₁ (q x) ∈ M.U _ from (r₁ x).symm ▸ mem_pull.1 hx, show p₂ (q x) ∈ W from (r₂ x).symm ▸ hbW _⟩
  have ev : ∀ J x, x ∈ (M.pull (h ⁻¹ᵁ N).ι).U J →
      gs (𝟙 _) x _ (resG _ (le J) ((q.app _).hom (f (J PUnit.unit)))) = gs q x _ (f (J PUnit.unit)) := fun J x hx => by
    rw [gs_res _ x (le J) hx, gs_pull _ q x _ (le J hx), Category.id_comp]
  refine ⟨⟨fun J => resG _ (le J) ((q.app _).hom (f (J PUnit.unit))), fun J J' => fn_ext fun x hx => ?_⟩,
    fun z' hz' => ?_⟩
  · rw [gs_res _ x inf_le_left hx, gs_mul _ x _ hx, gs_res _ x inf_le_right hx, ev J x hx.1, ev J' x hx.2,
      gs_unit _ x _ hx, gm_pull_g M _ _ x J J' hx.1 hx.2, Category.id_comp,
      compat _ _ _ q x (le J hx.1).1 (le J' hx.2).1 (le J hx.1).2, q₁]
  · have e₀ : h (b ⟨z', hz'⟩) = z' := congrArg (fun s : N.toScheme ⟶ Z => s ⟨z', hz'⟩) hb
    let x : (h ⁻¹ᵁ N).toScheme := ⟨b ⟨z', hz'⟩, show h (b ⟨z', hz'⟩) ∈ N from e₀.symm ▸ hz'⟩
    have hx : x ∈ (M.pull (h ⁻¹ᵁ N).ι).U (fun _ => i₀) := mem_pull.2 (hW (hbW _))
    refine ⟨x, TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i₀, ?_⟩, e₀⟩
    refine (isUnit_gs_iff_mem (𝟙 _) x _ hx _).1 ?_
    rw [ev _ x hx]
    exact unit _ q x ((r₁ x).symm ▸ hbW _) ((r₂ x).symm ▸ hbW _)

theorem exists_basicOpen_theta {C : Core} (T : C.Theta) :
    ∃ j, ((C.A.left.basicOpen (T.θ.f j) : C.A.left.Opens) : Set C.A.left).Nonempty := by
  have := C.lft
  have := C.isIntegral_G
  have := C.isOpenImmersion_a
  obtain ⟨-, -, -, hcl, -⟩ := GlobalTheory.jacobson_closedPoints_tools_int C.Z C.π
  obtain ⟨z, hz, -⟩ := hcl (genericPoint C.Z) PEmpty (fun k => k.elim) ⊤ trivial
  obtain ⟨x, hx, -⟩ := T.s_ne z hz
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨y₀⟩ := C.nonempty_A
  obtain ⟨y, hy⟩ := preimage_nonempty C.a y₀ ⟨x, hi⟩
  obtain ⟨j, hj⟩ := exists_chart T.L.isLB ((mulN C.A T.m).left y)
  have hyi : C.a y ∈ T.O₁.U i := C.G.toScheme.basicOpen_le _ hy
  have hu := (isUnit_gs_iff_mem C.a y _ hyi _).2 hy
  rw [T.w_sec y i j hyi hj] at hu
  exact ⟨j, _, (isUnit_gs_iff_mem _ y _ hj _).1 (isUnit_of_mul_isUnit_right hu)⟩

theorem exists_rational_section {C : Core} (T : C.Theta) (Om : Set C.G.toScheme) (ν) (hν : T.Norms Om ν)
    (M : LB C.G.toScheme) (w : LB.Iso (M.pull C.a) T.L.L) (D : M.ι → C.A.left.Opens) (hw : w.IsGen)
    (hD : ∀ i, (D i : Set C.A.left).Nonempty)
    (hn : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.A.left) (i : M.ι) (j : T.L.L.ι),
      IntAt C.a (M.U i) x → Set.range x ⊆ T.L.L.U j → Set.range x ⊆ D i →
      ‖valF x _ (w.s (j, fun _ => i)).val‖ * ν p x j = 1) :
    ∃ (E : M.ι → C.G.toScheme.Opens) (t : ∀ i, Γ(C.G.toScheme, E i)ˣ), (∀ i, E i ≤ M.U i) ∧
      (∀ i, (M.U i : Set C.G.toScheme).Nonempty → (E i : Set C.G.toScheme).Nonempty) ∧
      (∀ i k (Y : Scheme.{0}) (r : Y ⟶ C.G.toScheme) (y : Y), r y ∈ E i → r y ∈ E k →
        gm r y _ (t i) = gm r y _ (M.g i k) * gm r y _ (t k)) ∧
      ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ C.Z), ∃ δ : ℝ, 0 < δ ∧
        ∀ (b : Sp (OO p) ⟶ C.G.toScheme) (i : M.ι), (gPt p ≫ b) ≫ C.GG.hom = y → b (cPt p) ∈ M.U i →
          Set.range (gPt p ≫ b) ⊆ E i →
          ‖valF (gPt p ≫ b) _ (t i).val‖ ≤ δ ∧ (b (cPt p) ∈ Om → ‖valF (gPt p ≫ b) _ (t i).val‖ = δ) := by
  have := C.isIntegral_G
  have := C.isOpenImmersion_a
  have := C.nonempty_A
  have hA := C.isPullback_a
  haveI : IsIntegral C.A.left := isIntegral_of_isOpenImmersion C.a
  obtain ⟨ξ, hξ⟩ := exists_generic C.A.left
  obtain ⟨j, hj⟩ := exists_basicOpen_theta T
  have lθ : C.A.left.basicOpen (T.θ.f j) ≤ T.L.L.U j := C.A.left.basicOpen_le _
  obtain ⟨θ₀, hθ₀⟩ : IsUnit (resG _ lθ (T.θ.f j)) := C.A.left.toRingedSpace.isUnit_res_basicOpen (T.θ.f j)
  let V : M.ι → C.A.left.Opens := fun i => C.A.left.basicOpen (T.θ.f j) ⊓ C.a ⁻¹ᵁ M.U i ⊓ D i
  have l₁ : ∀ i, V i ≤ C.A.left.basicOpen (T.θ.f j) := fun i => inf_le_left.trans inf_le_left
  have l₂ : ∀ i, V i ≤ (LB.div T.L.L (M.pull C.a)).U (j, fun _ => i) := fun i x hx =>
    ⟨lθ hx.1.1, mem_pull.2 hx.1.2⟩
  choose t ht using fun i => exists_push C.a (V i)
    (Semi.res (l₁ i) θ₀ * (Semi.res (l₂ i) (w.s (j, fun _ => i)))⁻¹)
  have ht' : ∀ i (Y : Scheme.{0}) (r : Y ⟶ C.A.left) (y : Y), r y ∈ V i →
      gm (r ≫ C.a) y _ (t i) = gm r y _ θ₀ * (gm r y _ (w.s (j, fun _ => i)))⁻¹ := fun i Y r y hy => by
    rw [ht i Y r y hy, map_mul, map_inv, gm_res r y _ hy, gm_res r y _ hy]
  have hE : ∀ i, C.a ''ᵁ V i ≤ M.U i := fun i => image_le C.a (inf_le_left.trans inf_le_right)
  have back : ∀ i (x : C.A.left), C.a x ∈ C.a ''ᵁ V i → x ∈ V i := fun i x hx =>
    (C.a.preimage_image_eq (V i)).le hx
  refine ⟨fun i => C.a ''ᵁ V i, t, hE, fun i hi => ⟨C.a ξ, ξ, ⟨⟨hξ _ hj, hξ _ (preimage_nonempty C.a ξ hi)⟩,
    hξ _ (hD i)⟩, rfl⟩, fun i k => ?_, fun p _ y => ?_⟩
  · have l : C.a ''ᵁ V i ⊓ C.a ''ᵁ V k ≤ M.U i ⊓ M.U k := inf_le_inf (hE i) (hE k)
    have e : Semi.res inf_le_left (t i) = Semi.res l (M.g i k) * Semi.res inf_le_right (t k) := by
      refine unit_eq_of_gm C.a ξ hξ fun hm => ?_
      rw [map_mul, gm_res _ ξ _ hm, gm_res _ ξ _ hm, gm_res _ ξ _ hm]
      have m₁ := back i ξ hm.1
      have m₂ := back k ξ hm.2
      have e₁ := ht' i _ (𝟙 _) ξ m₁
      have e₂ := ht' k _ (𝟙 _) ξ m₂
      have e₃ := gm_isGen hw (𝟙 _) ξ j j (fun _ => i) (fun _ => k) (l₂ i m₁).1 (l₂ i m₁).1 (l₂ i m₁).2 (l₂ k m₂).2
      have e₄ := gm_pull_g M C.a (𝟙 _) ξ (fun _ => i) (fun _ => k) (l₂ i m₁).2 (l₂ k m₂).2
      rw [gm_self T.L.isLB (𝟙 _) ξ (l₂ i m₁).1, e₄, _root_.one_mul] at e₃
      unfold gv at e₃
      rw [Category.id_comp] at e₁ e₂ e₃
      rw [e₁, e₂, e₃, mul_inv, inv_inv, mul_left_comm]
    intro Y r y a₁ a₂
    have hm : r y ∈ C.a ''ᵁ V i ⊓ C.a ''ᵁ V k := ⟨a₁, a₂⟩
    have := congrArg (gm r y _) e
    rwa [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_res _ y _ hm] at this
  · have lift : ∀ (b : Sp (OO p) ⟶ C.G.toScheme) (i : M.ι), Set.range (gPt p ≫ b) ⊆ (C.a ''ᵁ V i : C.G.toScheme.Opens) →
        ∃ x : Sp (PadicAlgCl p) ⟶ C.A.left, x ≫ C.a = gPt p ≫ b := fun b i hr =>
      ⟨IsOpenImmersion.lift C.a (gPt p ≫ b) (fun s hs => by
        obtain ⟨s', -, rfl⟩ := hr hs
        exact ⟨s', rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
    by_cases hy : ∃ y' : Sp (PadicAlgCl p) ⟶ C.U.toScheme, y' ≫ C.U.ι = y
    · obtain ⟨y', rfl⟩ := hy
      obtain ⟨δ, hδ, H⟩ := hν.theta p y'
      refine ⟨δ, hδ, fun b i hb hc hr => ?_⟩
      obtain ⟨x, hx⟩ := lift b i hr
      let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
      have hz' : (x ≫ C.a) z ∈ C.a ''ᵁ V i := hx ▸ mem_of_range hr z
      have hz : x z ∈ V i := back i _ hz'
      have hxy : x ≫ C.A.hom = y' := by
        rw [← cancel_mono C.U.ι, Category.assoc, ← hA.w, reassoc_of% hx, ← hb, Category.assoc]
      obtain ⟨H₁, H₂⟩ := H x j hxy (range_sub z (l₂ i hz).1) ⟨b, hx.symm, trivial⟩
      have H₃ := hn p x i j ⟨b, hx.symm, hc⟩ (range_sub z (l₂ i hz).1) (range_sub z hz.2)
      have e₁ : valF (x ≫ C.a) _ (t i).val * valF x _ (w.s (j, fun _ => i)).val = valF x _ θ₀.val := by
        apply (toStk z).injective
        rw [map_mul, toStk_valF _ _ z hz', toStk_valF x _ z (l₂ i hz), toStk_valF x _ z (l₁ i hz), ht' i _ x z hz,
          ← Units.val_mul, inv_mul_cancel_right]
      have e₂ : valF x _ θ₀.val = valF x _ (T.θ.f j) := by
        rw [hθ₀, valF, valF, dif_pos ((top_le_iff_mem x _ z).2 (l₁ i hz)),
          dif_pos ((top_le_iff_mem x _ z).2 (lθ (l₁ i hz)))]
        congr 1
        change (C.A.left.presheaf.map (homOfLE lθ).op ≫ x.appLE _ _ _).hom _ = _
        rw [Scheme.Hom.map_appLE]
      have e₃ : ‖valF (gPt p ≫ b) _ (t i).val‖ = ‖valF x _ (T.θ.f j)‖ * ν p x j := by
        rw [← e₂, ← e₁, norm_mul, _root_.mul_assoc, H₃, _root_.mul_one, hx]
      rw [e₃]
      exact ⟨H₁, fun ho => H₂.2 ⟨b, hx.symm, ho⟩⟩
    · refine ⟨1, one_pos, fun b i hb _ hr => (hy ?_).elim⟩
      obtain ⟨x, hx⟩ := lift b i hr
      exact ⟨x ≫ C.A.hom, by rw [Category.assoc, ← hA.w, reassoc_of% hx, ← hb, Category.assoc]⟩

end ThetaLocal

open ThetaLocal NormGlue in

theorem exists_local_section_ne_zero_on_fibres : ∀ (C : Core) (L : C.Law) (T : C.Theta) (Om : Set C.G.toScheme) (ν), IsOpen Om → T.Norms Om ν → L.CompanionTheory Om → (∃ (M : LB C.G.toScheme) (w : LB.Iso (M.pull C.a) T.L.L) (D : M.ι → C.A.left.Opens), M.IsLB ∧ w.IsGen ∧ (∀ i, (D i : Set C.A.left).Nonempty) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.A.left) (i : M.ι) (j : T.L.L.ι), IntAt C.a (M.U i) x → Set.range x ⊆ T.L.L.U j → Set.range x ⊆ D i → ‖valF x _ (w.s (j, fun _ => i)).val‖ * ν p x j = 1) → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  rintro C L T Om ν hOm hν hS ⟨M, w, D, hM, hw, hD, hn⟩
  refine ⟨M, hM, ⟨w, hw⟩, fun z => ?_⟩
  obtain ⟨E, t, hE, hne, ht, hδ⟩ := exists_rational_section T Om ν hν M w D hw hD hn
  have hA := C.isPullback_a
  have := L.smooth
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  obtain ⟨hI, hN, -⟩ := AddExt.isIntegral_and_normal C
    (pullback.map C.A.hom C.A.hom C.GG.hom C.GG.hom C.a C.a C.U.ι hA.w.symm hA.w.symm)
    ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hI' : IsIntegral (pullback C.GG.hom C.GG.hom) := hI
  have := C.lft
  have := C.flat
  obtain ⟨-, -, -, hcl, -⟩ := GlobalTheory.jacobson_closedPoints_tools_int C.G.toScheme (C.GG.hom ≫ C.π)
  obtain ⟨x₀, hx₀, hsp, -⟩ := hcl (C.e z) PEmpty (fun k => k.elim) ⊤ trivial
  have hz : z ⤳ C.GG.hom x₀ := by
    have e : C.GG.hom (C.e z) = z := congrArg (fun s : C.Z ⟶ C.Z => s z) C.e_sec
    exact e ▸ hsp.map C.GG.hom.continuous
  obtain ⟨N, b, c, K, _, s, x, b', c', hx, hb, -, H⟩ := hS x₀ hx₀
  let k : Sp K := IsLocalRing.closedPoint K
  have h₁ : x.left k = x₀ := by
    have : x.left k ∈ Set.range x.left := ⟨k, rfl⟩
    rwa [hx] at this
  have h₂ : N.ι (s k) = C.GG.hom x₀ := by
    rw [← h₁]
    exact (congrArg (fun q : Sp K ⟶ C.Z => q k) (Over.w x)).symm
  have h₃ : b.left (s k) ∈ Om := by
    have := H b' (by simp) ⟨k, rfl⟩
    rw [hb] at this
    exact this
  obtain ⟨i₀, hi₀⟩ := exists_chart hM (b.left (s k))
  let W : C.G.toScheme.Opens := ⟨Om, hOm⟩ ⊓ M.U i₀
  let b₀ : N.toScheme ⟶ C.G.toScheme := b.left
  have hb₀ : b₀ ≫ C.GG.hom = N.ι := Over.w b
  let N' : C.Z.Opens := N.ι ''ᵁ (b₀ ⁻¹ᵁ W)
  have le : N' ≤ N := N.ι_image_le _
  obtain ⟨σ, hσ⟩ := exists_local_section (pullback.fst C.GG.hom C.GG.hom) (pullback.snd C.GG.hom C.GG.hom)
    (pullback.fst C.GG.hom C.GG.hom ≫ C.GG.hom ≫ C.π) hN C.GG.hom (IsPullback.of_hasPullback _ _) M E hE hne t ht
    Om hδ W i₀ inf_le_right (fun _ h => h.1) ⟨_, h₃, hi₀⟩ N' (C.Z.homOfLE le ≫ b₀)
    (by rw [Category.assoc, hb₀, Scheme.homOfLE_ι]) (by
      intro v
      have e : N.ι (C.Z.homOfLE le v) = N'.ι v :=
        congrArg (fun q : N'.toScheme ⟶ C.Z => q v) (Scheme.homOfLE_ι _ le)
      exact (N.ι.preimage_image_eq (b₀ ⁻¹ᵁ W)).le (show N.ι (C.Z.homOfLE le v) ∈ N' from e ▸ v.2))
  exact ⟨N', σ, hz.mem_open N'.isOpen ⟨s k, ⟨h₃, hi₀⟩, h₂⟩, hσ⟩

end GlobalTheory
