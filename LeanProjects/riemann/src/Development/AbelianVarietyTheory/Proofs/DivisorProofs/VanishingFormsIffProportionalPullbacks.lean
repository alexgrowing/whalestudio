import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.HomFixUniv.MapIff

theorem eval₂_mul_of_isHomogeneous' {R S σ : Type} [CommRing R] [CommRing S] [Fintype σ] (g : R →+* S)
    (x : σ → S) (u : S) {F : MvPolynomial σ R} {d : ℕ} (hF : F.IsHomogeneous d) :
    MvPolynomial.eval₂ g (fun j => u * x j) F = u ^ d * MvPolynomial.eval₂ g x F := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply]
    simp [Finsupp.sum_fintype]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

section
variable {X Z : Scheme.{0}}

def gsH (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : Γ(X, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem gsH_apply (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    gsH r z U h a = gs r z U a := (gs_eq r z U h a).symm

theorem gs_eval₂Hom {R σ : Type} [CommRing R] (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (g : R →+* Γ(X, U)) (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (MvPolynomial.eval₂Hom g x F) =
      MvPolynomial.eval₂Hom ((gsH r z U h).comp g) (fun j => gs r z U (x j)) F := by
  rw [← gsH_apply r z U h, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  congr 2
  funext j
  exact gsH_apply r z U h _

theorem gs_cst_gc {R : Type} [CommRing R] (f : X ⟶ Sp R) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (GlobalTheory.AbLaw.cst f U c) = gc (r ≫ f) z c := by
  rw [GlobalTheory.MapToProj.gs_cst f r z U h c, gs_eq _ z ⊤ trivial]
  rfl

theorem gs_eval_cst {R σ : Type} [CommRing R] (f : X ⟶ Sp R) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst f U) x F) =
      MvPolynomial.eval₂Hom (gc (r ≫ f) z) (fun j => gs r z U (x j)) F := by
  rw [gs_eval₂Hom r z U h, show (gsH r z U h).comp (GlobalTheory.AbLaw.cst f U) = gc (r ≫ f) z from
    RingHom.ext fun c => (gsH_apply r z U h _).trans (gs_cst_gc f r z U h c)]

end

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem exists_combSec (hN : N.IsLB) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) : ∃ s : Fin mB → LB.Sec (N.pull φ), ∀ j z q, φ z ∈ N.U q →
      gs (𝟙 X) z ((N.pull φ).U (fun _ => q)) ((s j).f (fun _ => q)) = comb a φ p c z q j := by
  have le : ∀ J : PUnit → N.ι, (N.pull φ).U J ≤ φ ⁻¹ᵁ N.U (J PUnit.unit) := fun J _ hy => mem_pull.1 hy
  let F : Fin mB → ∀ J : PUnit → N.ι, Γ(X, (N.pull φ).U J) := fun j J =>
    ∑ i, (p.appLE ⊤ ((N.pull φ).U J) le_top).hom (c i j) *
      (φ.appLE (N.U (J PUnit.unit)) ((N.pull φ).U J) (le J)).hom ((a i).f (J PUnit.unit))
  have hF : ∀ j (J : PUnit → N.ι) z, z ∈ (N.pull φ).U J →
      gs (𝟙 X) z ((N.pull φ).U J) (F j J) = comb a φ p c z (J PUnit.unit) j := by
    intro j J z hz
    simp only [F, comb]
    rw [GlobalTheory.AmpleSpan.gs_sum' (𝟙 X) z _ hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul (𝟙 X) z _ hz]
    exact congrArg₂ (· * ·) ((gs_appLE p ⊤ _ _ (𝟙 X) z hz _).trans (by rw [Category.id_comp]))
      ((gs_appLE φ _ _ _ (𝟙 X) z hz _).trans (by rw [Category.id_comp]))
  refine ⟨fun j => ⟨F j, fun J J' => fn_ext fun y hy => ?_⟩, fun j z q hz => hF j _ z (mem_pull.2 hz)⟩
  have hJ : φ y ∈ N.U (J PUnit.unit) := mem_pull.1 hy.1
  have hJ' : φ y ∈ N.U (J' PUnit.unit) := mem_pull.1 hy.2
  rw [gs_res (𝟙 X) y _ hy, gs_mul (𝟙 X) y _ hy, gs_res (𝟙 X) y _ hy, gs_unit (𝟙 X) y _ hy,
    gm_pull_g N φ (𝟙 X) y J J' hy.1 hy.2, hF j J y hy.1, hF j J' y hy.2, Category.id_comp]
  simp only [comb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_compat (a i) φ y hJ hJ']
  ring

end GlobalTheory.HomFixUniv.MapIff

namespace GlobalTheory.HomFixUniv

open MapIff

theorem formsOK_iff_exists_proport : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (f : A₀ ⟶ Sp Rg)
    (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H)
    (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)),
    GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → φ ≫ f = p ≫ t → GlobalTheory.HomFixUniv.Generates a φ p c →
    (GlobalTheory.HomFixUniv.FormsOK a fB b φ p t c ↔
      ∃ Ψ : X ⟶ B₀, Ψ ≫ fB = p ≫ t ∧ GlobalTheory.HomFixUniv.Proport a b φ p Ψ c) := by
  intro Rg _ A₀ B₀ X T f fB N H mA mB a b φ p t c hE hH hN _ hG
  constructor
  · intro hF
    cases mB with
    | zero =>
      have : IsEmpty X := ⟨fun z => by
        obtain ⟨q, hq⟩ := exists_chart hN (φ z)
        obtain ⟨j, -⟩ := hG z q hq
        exact j.elim0⟩
      exact ⟨isInitialOfIsEmpty.to B₀, isInitialOfIsEmpty.hom_ext _ _, fun z => (IsEmpty.false z).elim⟩
    | succ n =>
      obtain ⟨s, hs⟩ := exists_combSec (mB := n + 1) hN a φ p c
      have hva : GlobalTheory.AbLaw.VeryAmpleBy fB H b := (GlobalTheory.AmpleSpan.embedsBy_spec_iff fB b).1 hE
      have hcov : ⨆ j, nonzeroLocus (s j) = ⊤ := by
        refine eq_top_iff.2 fun z _ => ?_
        obtain ⟨q, hq⟩ := exists_chart hN (φ z)
        obtain ⟨j, hj⟩ := hG z q hq
        have hk : (𝟙 X : X ⟶ X) z ∈ (N.pull φ).U (fun _ => q) := mem_pull.2 hq
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (s j) (𝟙 X) z hk).2
          (by rw [hs j z q hq]; exact hj)⟩
      have hforms : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) Rg), F.IsHomogeneous d →
          (∀ k : H.ι, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst fB (H.U k)) (fun j => (b j).f k) F = 0) →
          ∀ k : (N.pull φ).ι,
            MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst (p ≫ t) ((N.pull φ).U k)) (fun j => (s j).f k) F = 0 := by
        intro d F hFd hK k
        obtain ⟨q, rfl⟩ : ∃ q, k = fun _ => q := ⟨k PUnit.unit, rfl⟩
        refine fn_ext fun z hz => ?_
        have hq : φ z ∈ N.U q := mem_pull.1 hz
        have e : (fun j => gs (𝟙 X) z ((N.pull φ).U (fun _ => q)) ((s j).f (fun _ => q))) = comb a φ p c z q :=
          funext fun j => hs j z q hq
        rw [gs_eval_cst (p ≫ t) (𝟙 X) z _ hz, Category.id_comp, e, gs_eq (𝟙 X) z _ hz 0, map_zero, map_zero]
        exact hF d F hFd hK z q hq
      obtain ⟨Ψ, w, hΨ, -, hrel⟩ := GlobalTheory.exists_hom_of_veryAmpleBy Rg B₀ fB H n b hH hva X (p ≫ t) (N.pull φ) s
        (LB.isLB_linComb hN _ _) hcov hforms
      refine ⟨Ψ, hΨ, fun z q k hq hk j j' => ?_⟩
      have hz : z ∈ (N.pull φ).U (fun _ => q) := mem_pull.2 hq
      rw [hrel j z k (fun _ => q) hk hz, hrel j' z k (fun _ => q) hk hz, hs j z q hq, hs j' z q hq]
      ring
  · rintro ⟨Ψ, hΨ, hP⟩ d F hFd hK z q hq
    obtain ⟨j₀, hj₀⟩ := hG z q hq
    obtain ⟨j', hj'⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show Ψ z ∈ ⨆ j, nonzeroLocus (b j) by rw [hE.1]; trivial)
    obtain ⟨k, hk⟩ := GlobalTheory.AmpleSpan.exists_chart_of_mem (b j') hj'
    have hu' : IsUnit (gs Ψ z _ ((b j').f k)) := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b j') Ψ z hk).1 hj'
    have hPr := hP z q k hq hk
    have hB0 : IsUnit (gs Ψ z (H.U k) ((b j₀).f k)) := by
      have hu : IsUnit (gs Ψ z (H.U k) ((b j₀).f k) * comb a φ p c z q j') := hPr j' j₀ ▸ hu'.mul hj₀
      exact isUnit_of_mul_isUnit_left hu
    obtain ⟨u, hu⟩ := hj₀
    have hBC : ∀ j, gs Ψ z (H.U k) ((b j).f k) =
        (gs Ψ z (H.U k) ((b j₀).f k) * ↑u⁻¹) * comb a φ p c z q j := fun j => by
      have h1 := hPr j j₀
      rw [← hu] at h1
      calc gs Ψ z (H.U k) ((b j).f k) = gs Ψ z (H.U k) ((b j).f k) * ↑u * ↑u⁻¹ := by simp
        _ = gs Ψ z (H.U k) ((b j₀).f k) * comb a φ p c z q j * ↑u⁻¹ := by rw [h1]
        _ = _ := by ring
    have hK' := congrArg (gs Ψ z (H.U k)) (hK k)
    rw [gs_eval_cst fB Ψ z _ hk, hΨ, gs_eq Ψ z _ hk 0, map_zero, map_zero, funext hBC,
      MvPolynomial.coe_eval₂Hom, eval₂_mul_of_isHomogeneous' _ _ _ hFd] at hK'
    have hl : IsUnit ((gs Ψ z (H.U k) ((b j₀).f k) * ↑u⁻¹) ^ d) := (hB0.mul u⁻¹.isUnit).pow d
    rw [MvPolynomial.coe_eval₂Hom]
    exact hl.mul_right_eq_zero.1 hK'

end GlobalTheory.HomFixUniv
