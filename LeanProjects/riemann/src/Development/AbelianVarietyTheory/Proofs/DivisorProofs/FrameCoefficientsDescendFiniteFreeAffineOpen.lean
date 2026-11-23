import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁]

theorem exists_basis (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) :
    letI := ρ₁.toAlgebra; ∃ B : Module.Basis (Fin d) R R₁, ⇑B = b := by
  letI := ρ₁.toAlgebra
  have hs : ∀ (c : R) (x : R₁), c • x = ρ₁ c * x := fun c x => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hli : LinearIndependent R b := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    have h1 : (0 : R₁) = ∑ l, ρ₁ (g l) * b l := by
      rw [← hg]; simp only [hs]
    have h2 : (0 : R₁) = ∑ l, ρ₁ ((0 : Fin d → R) l) * b l := by simp
    exact congrFun ((hb 0).unique h1 h2) i
  refine ⟨Module.Basis.mk hli ?_, Module.Basis.coe_mk _ _⟩
  intro r _
  obtain ⟨c, hc, -⟩ := hb r
  rw [hc]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [← hs]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem gs_zero0 {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

variable {X Z : Scheme.{0}}

theorem aff_coeff (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    {V : X.Opens} (hV : IsAffineOpen V) :
    (∀ t : Γ(Z, q ⁻¹ᵁ V), ∃ a : Fin d → Γ(X, V),
      t = ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l)) ∧
    (∀ a : Fin d → Γ(X, V), ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l) = 0 → a = 0) := by
  classical
  letI := ρ₁.toAlgebra
  obtain ⟨B, hB⟩ := exists_basis ρ₁ b hb
  have hg : ρ₁.Flat := by
    have : Module.Free R R₁ := Module.Free.of_basis B
    exact (inferInstance : Module.Flat R R₁)
  letI : Algebra R Γ(X, V) := (GlobalTheory.AbLaw.cst f V).toAlgebra
  obtain ⟨e, he⟩ := GlobalTheory.FlatSec.exists_equiv_of_isPushout (R := R) (q.app V) (GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V))
    (GlobalTheory.FlatSec.isPushout_app hg H hV.isCompact hV.isQuasiSeparated)
  have hsum : ∀ a : Fin d → Γ(X, V), e (∑ l, B l ⊗ₜ[R] a l) =
      ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l) := by
    intro a; rw [map_sum]; simp only [he, hB]
  constructor
  · intro t
    refine ⟨fun l => TensorProduct.equivFinsuppOfBasisLeft B (e.symm t) l, ?_⟩
    rw [← hsum]
    have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply B (TensorProduct.equivFinsuppOfBasisLeft B (e.symm t))
    rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    rw [← h, AddEquiv.apply_symm_apply]
  · intro a ha
    rw [← hsum] at ha
    have h0 : ∑ l, B l ⊗ₜ[R] a l = 0 := e.injective (ha.trans (map_zero e).symm)
    funext k
    have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisLeft B w k) h0
    simpa [map_sum, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self,
      Finsupp.single_apply] using this

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem gs_cst_top (p : Z ⟶ Sp R₁) (z : Z) (c : R₁) :
    gs (𝟙 Z) z ⊤ (GlobalTheory.AbLaw.cst p ⊤ c) = gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c) := by
  have h1 := gs_res (𝟙 Z) z (le_top : (⊤ : Z.Opens) ≤ p ⁻¹ᵁ ⊤) trivial ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c))
  have h2 := gs_pull (𝟙 Z) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c)
  rw [Category.id_comp] at h2
  exact h1.trans h2

theorem gs_comb_pt {d : ℕ} (b : Fin d → R₁) (p : Z ⟶ Sp R₁) (q : Z ⟶ X) (V : X.Opens) (z : Z) (hz : q z ∈ V)
    (a : Fin d → Γ(X, V)) :
    gs (𝟙 Z) z (q ⁻¹ᵁ V) (∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l)) =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z V (a l) := by
  rw [GlobalTheory.FlatSec.gs_comb p q V z hz b a]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [gs_cst_top]

theorem exists_aff (U : X.Opens) (x : X) (hx : x ∈ U) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U := by
  obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  exact ⟨V, hV, hxV, hVU⟩

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem inj_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (U : X.Opens) (a : Fin d → Γ(X, U))
    (h : ∀ z : Z, q z ∈ U →
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z U (a l) = 0) :
    ∀ l, a l = 0 := by
  intro l
  apply fn_ext
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := exists_aff U x hx
  have h0 := (aff_coeff ρ₁ b hb H hV).2 (fun l => GlobalTheory.AbLaw.rs X hVU (a l)) (fn_ext fun z hz => by
    rw [gs_comb_pt b p q V z hz, gs_zero0]
    refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) (h z (hVU hz))
    rw [gs_res q z hVU hz])
  have e := congrFun h0 l
  have e2 := gs_res (𝟙 X) x hVU hxV (a l)
  simp only [Pi.zero_apply] at e
  rw [← e2]
  erw [e]
  rw [gs_zero0, gs_zero0]

theorem surj_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (U : X.Opens) (t : Γ(Z, q ⁻¹ᵁ U)) :
    ∃ a : Fin d → Γ(X, U), ∀ z : Z, q z ∈ U →
      gs (𝟙 Z) z (q ⁻¹ᵁ U) t =
        ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z U (a l) := by
  classical
  choose V hV hxV hVU using fun x : U => exists_aff U x.1 x.2
  have hle : ∀ x, q ⁻¹ᵁ V x ≤ q ⁻¹ᵁ U := fun x z hz => hVU x hz
  choose c hc using fun x : U => (aff_coeff ρ₁ b hb H (hV x)).1 (GlobalTheory.AbLaw.rs Z (hle x) t)
  have hcg : ∀ x z, q z ∈ V x → gs (𝟙 Z) z (q ⁻¹ᵁ U) t =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (V x) (c x l) := by
    intro x z hz
    rw [← gs_res (𝟙 Z) z (hle x) hz t, ← gs_comb_pt b p q (V x) z hz]
    exact congrArg _ (hc x)
  have hcomp : ∀ l x y, GlobalTheory.AbLaw.rs X (inf_le_left : V x ⊓ V y ≤ V x) (c x l) =
      GlobalTheory.AbLaw.rs X (inf_le_right : V x ⊓ V y ≤ V y) (c y l) := by
    intro l x y
    refine sub_eq_zero.1 (inj_gen ρ₁ b hb H (V x ⊓ V y)
      (fun l => GlobalTheory.AbLaw.rs X inf_le_left (c x l) - GlobalTheory.AbLaw.rs X inf_le_right (c y l)) (fun z hz => ?_) l)
    have e : ∀ l, gs q z (V x ⊓ V y) (GlobalTheory.AbLaw.rs X inf_le_left (c x l) - GlobalTheory.AbLaw.rs X inf_le_right (c y l)) =
        gs q z (V x) (c x l) - gs q z (V y) (c y l) := fun l => by
      rw [gs_eq q z _ hz, map_sub, map_sub, ← gs_eq q z _ hz, ← gs_eq q z _ hz, gs_res q z _ hz, gs_res q z _ hz]
    simp only [e, mul_sub, Finset.sum_sub_distrib]
    rw [← hcg x z hz.1, ← hcg y z hz.2, sub_self]
  have hcov : U ≤ iSup V := fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  choose s hs using fun l => X.sheaf.existsUnique_gluing' V U (fun x => homOfLE (hVU x)) hcov
    (fun x => c x l) (fun x y => hcomp l x y)
  refine ⟨s, fun z hz => ?_⟩
  rw [hcg ⟨q z, hz⟩ z (hxV ⟨q z, hz⟩)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← (hs l).1 ⟨q z, hz⟩]
  exact congrArg _ (gs_res q z (hVU ⟨q z, hz⟩) (hxV ⟨q z, hz⟩) (s l))

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem main_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (L : LB X) (W O : X.Opens) (hOW : O ≤ W)
    (τ : ∀ k : L.ι, Γ(Z, q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k)ˣ) (hτ : FrameAlong L q (q ⁻¹ᵁ W) τ) :
    ∃ s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k), (∀ l, IsSecOver L O (s l)) ∧
      ∀ (z : Z) (k : L.ι), q z ∈ O → q z ∈ L.U k →
        gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val =
          ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (O ⊓ L.U k) (s l k) := by
  have hle : ∀ k, q ⁻¹ᵁ (O ⊓ L.U k) ≤ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k := fun k z hz => ⟨hOW hz.1, hz.2⟩
  choose a ha using fun k => surj_gen ρ₁ b hb H (O ⊓ L.U k) (GlobalTheory.AbLaw.rs Z (hle k) (τ k).val)
  have hτg : ∀ k z, q z ∈ O ⊓ L.U k → gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (O ⊓ L.U k) (a k l) := by
    intro k z hz
    rw [← gs_res (𝟙 Z) z (hle k) hz]
    exact ha k z hz
  refine ⟨fun l k => a k l, fun l => ?_, fun z k hO hk => hτg k z ⟨hO, hk⟩⟩
  intro x k k' hx hk hk'
  have hV : O ⊓ L.U k ≤ L.U k := inf_le_right
  have hW : O ⊓ L.U k' ≤ L.U k' := inf_le_right
  have h0 := inj_gen ρ₁ b hb H ((O ⊓ L.U k) ⊓ (O ⊓ L.U k'))
    (fun l => GlobalTheory.AbLaw.rs X inf_le_left (a k l) -
      GlobalTheory.AbLaw.rs X (inf_le_inf hV hW) (L.g k k').val * GlobalTheory.AbLaw.rs X inf_le_right (a k' l)) (fun z hz => ?_) l
  · have e := congrArg (gs (𝟙 X) x _) h0
    rw [GlobalTheory.FlatSec.gs_diff hV hW (a k l) (a k' l) (𝟙 X) x ⟨⟨hx, hk⟩, ⟨hx, hk'⟩⟩, gs_zero0] at e
    exact sub_eq_zero.1 e
  · have e1 : ∀ l, gs q z _ (GlobalTheory.AbLaw.rs X inf_le_left (a k l) -
        GlobalTheory.AbLaw.rs X (inf_le_inf hV hW) (L.g k k').val * GlobalTheory.AbLaw.rs X inf_le_right (a k' l)) =
        gs q z _ (a k l) - (gm q z (L.U k ⊓ L.U k') (L.g k k')).val * gs q z _ (a k' l) :=
      fun l => GlobalTheory.FlatSec.gs_diff hV hW _ _ q z hz
    simp only [e1, mul_sub, Finset.sum_sub_distrib]
    have hfr := congrArg Units.val (hτ z k k' (hOW hz.1.1) hz.1.2 hz.2.2)
    rw [Units.val_mul, ← gs_unit (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) ⟨hOW hz.1.1, hz.1.2⟩ (τ k),
      ← gs_unit (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k') ⟨hOW hz.1.1, hz.2.2⟩ (τ k'),
      hτg k z hz.1, hτg k' z hz.2] at hfr
    rw [hfr, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.FrameCoeff

theorem GlobalTheory.FrameCoeff.frame_coeff : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → IsAffineOpen O → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ), FrameAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ → ∃ s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k), (∀ l, IsSecOver L O (s l)) ∧ ∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k) := by
  intro R R₁ _ _ ρ₁ d b hb X f L hL W O hOW hO τ hτ
  exact GlobalTheory.FrameCoeff.main_gen ρ₁ b hb (IsPullback.of_hasPullback f (spMap ρ₁)) L W O hOW τ hτ
