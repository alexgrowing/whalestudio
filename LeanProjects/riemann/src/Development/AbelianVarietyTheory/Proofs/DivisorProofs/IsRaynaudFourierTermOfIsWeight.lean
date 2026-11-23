import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionPullbackThetaValue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeUnitStalkDataGerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDescentFlatSurjectiveQuasiCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveQuasiCompactQStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Heat.TermDescent

theorem gs_top_appLE {Y X : Scheme.{0}} (φ : Y ⟶ X) (y : Y) (U : X.Opens) (h : ⊤ ≤ φ ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs (𝟙 Y) y ⊤ ((φ.appLE U ⊤ h).hom a) = gs φ y U a := by
  have e := gs_appLE φ U ⊤ h (𝟙 Y) y trivial a
  rwa [Category.id_comp] at e

theorem gs_of_valR {S : Type} [CommRing S] {X : Scheme.{0}} (x x' : Sp S ⟶ X) (V : X.Opens) (f : Γ(X, V))
    (c : Sˣ) (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ x' ⁻¹ᵁ V) (e : valR x' V f = c * valR x V f) (y : Sp S) :
    gs x' y V f = (gm (𝟙 (Sp S)) y ⊤ (unitOn c)).val * gs x y V f := by
  rw [valR, valR, dif_pos h, dif_pos h'] at e
  have e' : (x'.appLE V ⊤ h').hom f = (unitOn c).val * (x.appLE V ⊤ h).hom f := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom e
    rw [map_mul] at this
    simpa [unitOn] using this
  rw [← gs_top_appLE x' y V h', ← gs_top_appLE x y V h, e', gs_mul _ y ⊤ trivial, gs_unit _ y ⊤ trivial]

theorem gen_ratio {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {S : Type} [CommRing S] {K : Type} [Fintype K]
    {φ φ' : K → (Sp S ⟶ X)} (ε : K → ℤ) (e : φ = φ') (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen) (ht' : t'.IsGen) : ∃ c : Sˣ, ∀ y J, Good L y J →
      val t' (𝟙 _) y J = gm (𝟙 (Sp S)) y ⊤ (unitOn c) * val t (𝟙 _) y J := by
  subst e
  let u := LB.mulGen L φ ε φ (fun k => - ε k) t' (LB.invGen L φ ε t)
  have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ ht' (DVR.invGen_isGen _ _ _ _ ht)
  have hF : FormEq (Sum.elim φ φ) (Sum.elim ε fun k => - ε k) (K' := PEmpty.{1}) PEmpty.elim PEmpty.elim := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib,
      mul_inv_cancel, Fintype.prod_empty]
  obtain ⟨t₀, -, h₀⟩ := exists_gen hL hF u hu
  have le : (⊤ : (Sp S).Opens) ≤ LB.wchart L (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  let v : Γ(Sp S, ⊤)ˣ := res le (t₀.s PEmpty.elim)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom v, fun y J hJ => ?_⟩
  have hv : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom v) = v := by
    ext; simp [unitOn]
  have e₀ : gm (𝟙 (Sp S)) y ⊤ v = val t₀ (𝟙 _) y J :=
    (gm_res _ y le trivial _).trans (val_of t₀ _ y J PEmpty.elim fun k => k.elim).symm
  rw [hv, e₀, h₀ _ _ y J hJ, val_mul hJ, val_inv, inv_mul_cancel_right]

end GlobalTheory.Heat.TermDescent

namespace GlobalTheory.Heat
open GlobalTheory.Heat.TermDescent

theorem isTerm_of_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (τ : SecM Y.q.left Q.P.L k) (J : Type) (V : J → Q.P.A.left.Opens) (j : J → Fin 1 → Q.P.L.ι), ⨆ i, Y.q.left ⁻¹ᵁ V i = ⊤ → (∀ i, Y.q.left ⁻¹ᵁ V i ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (j i)) → (∀ i, IsWt Y α (Y.q.left ⁻¹ᵁ V i) (rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i))) → ∃ σ' : Q.SecB k α, IsTerm Y k α σ' τ := by
  intro R _ _ Q O _ _ _ oa Y k α τ Jt V j hcov hle hwt
  have hL := Q.P.isLB
  obtain ⟨hs, hqc⟩ := GlobalTheory.T.ray_q_surjective_and_quasiCompact Y
  have := Ray.smooth_q Y
  let t := (Y.Φ Y.H (𝟙 _)).s α
  have ht : t.IsGen := (Y.Φ Y.H (𝟙 _)).isGen α
  have hF : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 _ ≫ Y.q.left) (DegPre.gtφT Q Y.H Y.q α))
      (Sum.elim (fun _ => (k : ℤ)) (fun a => - DegPre.gtε a)) (fun i => Y.q.left ≫ DegPre.famφB Q α i)
      (DegPre.famε k) := by
    intro U _ h
    have e := GlobalTheory.RayEv.formEq_term Y k α U h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp, zpow_neg,
      Finset.prod_inv_distrib] at e ⊢
    rw [← e, mul_inv_cancel_right]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF (pullMulSec τ (𝟙 _) (LB.invGen Q.P.L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have vσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) J, Good Q.P.L z J →
      sval σ r z J = sval τ r z J * ((val t r z J)⁻¹).val := by
    intro Z r z J hJ
    rw [hσ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, Category.comp_id]
    exact congrArg (fun u => sval τ r z J * u.val) (val_inv (z := z) (J := J) t r)
  have vt : ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) (y : T.left) J, Good Q.P.L y J →
      val t x.left y J = val ((Y.Φ T x).s α) (𝟙 _) y J := by
    intro T x y J hJ
    obtain ⟨-, h₂⟩ := (GlobalTheory.TorusModel.isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))
    have e := h₂ α y J hJ
    rw [Category.comp_id] at e
    exact e.symm
  have hdesc : ∀ (S : Type) [CommRing S] [IsLocalRing S] (g₁ g₂ : Sp S ⟶ Y.H.left), g₁ ≫ Y.q.left = g₂ ≫ Y.q.left →
      ∀ J, Good Q.P.L (closedPoint S) J → sval σ g₁ (closedPoint S) J = sval σ g₂ (closedPoint S) J := by
    intro S _ _ g₁ g₂ hg J hJ
    have hA : g₂ ≫ Y.H.hom = g₁ ≫ Y.H.hom := by
      rw [← Over.w Y.q, ← Category.assoc, ← Category.assoc, hg]
    obtain ⟨φ, hφ⟩ : ∃ φ : R →+* S, g₁ ≫ Y.H.hom = spMap φ :=
      ⟨(Spec.preimage (g₁ ≫ Y.H.hom)).hom, (Spec.map_preimage _).symm⟩
    let x₁ : Over.mk (spMap φ) ⟶ Y.H := Over.homMk g₁ hφ
    let x₂ : Over.mk (spMap φ) ⟶ Y.H := Over.homMk g₂ (hA.trans hφ)
    have hx : x₂ ≫ Y.q = x₁ ≫ Y.q := Over.OverMorphism.ext hg.symm
    have hc : ∀ χ, ∃ c : Sˣ, ∀ y J, Good Q.P.L y J → val ((Y.Φ _ x₂).s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn c) * val ((Y.Φ _ x₁).s χ) (𝟙 _) y J := fun χ =>
      gen_ratio Q.P.L hL DegPre.gtε (by rw [Ray.Φ_b, Ray.Φ_b, hx]) _ _ ((Y.Φ _ x₁).isGen χ) ((Y.Φ _ x₂).isGen χ)
    choose c hc using hc
    obtain ⟨i, hi⟩ : ∃ i, g₁ (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i := by
      have : g₁ (closedPoint S) ∈ (⨆ i, Y.q.left ⁻¹ᵁ V i : Y.H.left.Opens) := by rw [hcov]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    have hi₂ : g₂ (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i := by
      show (g₂ ≫ Y.q.left) (closedPoint S) ∈ V i
      rw [← hg]; exact hi
    have h₁ : ⊤ ≤ g₁ ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V i) :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of S) g₁ hi).ge
    have h₂ : ⊤ ≤ g₂ ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V i) :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of S) g₂ hi₂).ge
    have hw := hwt i S φ x₁ x₂ c g₁ g₂ rfl rfl h₁ h₂ hx hc
    have hg' := gs_of_valR g₁ g₂ _ _ (c α) h₁ h₂ hw (closedPoint S)
    have s_i : ∀ g : Sp S ⟶ Y.H.left, g (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i →
        gs g (closedPoint S) (Y.q.left ⁻¹ᵁ V i) (rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i)) =
          (trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g (closedPoint S) (j i)
            (fun _ => J (g ≫ Y.q.left))).val * sval τ g (closedPoint S) J := by
      intro g hm
      have er : rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i) = resG _ (hle i) (τ.f (j i)) := dif_pos (hle i)
      rw [er]
      exact (gs_res g _ (hle i) hm _).trans (sec_trans τ g _ (hle i hm) (hJ.mem _ g))
    have htr : trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g₂ (closedPoint S) (j i)
        (fun _ => J (g₂ ≫ Y.q.left)) = trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g₁ (closedPoint S) (j i)
        (fun _ => J (g₁ ≫ Y.q.left)) := by
      simp only [trF]
      rw [hg]
    set C : ((Sp S).presheaf.stalk (closedPoint S))ˣ := gm (𝟙 (Sp S)) (closedPoint S) ⊤ (unitOn (c α)) with hC
    have sv : sval τ g₂ (closedPoint S) J = C.val * sval τ g₁ (closedPoint S) J := by
      have e := hg'
      rw [s_i g₂ hi₂, s_i g₁ hi, htr, mul_left_comm] at e
      exact (Units.mul_right_inj _).1 e
    have vv : val t g₂ (closedPoint S) J = C * val t g₁ (closedPoint S) J :=
      (vt _ x₂ _ J hJ).trans ((hc α _ J hJ).trans (congrArg (C * ·) (vt _ x₁ _ J hJ).symm))
    rw [vσ _ g₁ _ J hJ, vσ _ g₂ _ J hJ, sv, vv, mul_inv_rev, Units.val_mul]
    linear_combination (-(sval τ g₁ (closedPoint S) J * ((val t g₁ (closedPoint S) J)⁻¹).val)) * C.mul_inv

  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_section_descent_flat_surjective_quasiCompact Q.P.L hL Y.q.left inferInstance hs hqc (DegPre.famφB Q α) (DegPre.famε k) σ hdesc
  refine ⟨b, fun T x y J hJ => ?_⟩
  have e1 := hb _ x.left y J hJ
  rw [vσ _ _ y J hJ, vt T x y J hJ] at e1
  show sval τ x.left y J = sval b (x.left ≫ Y.q.left) y J * _
  rw [← e1, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]

end GlobalTheory.Heat
