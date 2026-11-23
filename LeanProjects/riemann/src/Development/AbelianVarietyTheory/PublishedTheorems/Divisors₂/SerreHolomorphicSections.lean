import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Vanishing

namespace GlobalTheory.Published

def SerreHolomorphicSections : Prop :=
  ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → IsProjOver p →
    ∀ (R : AnRead p (RingHom.id ℂ) D) (B : LB Y), B.IsLB →
      Function.Bijective fun s : B.Sec =>
        (⟨secVal p (RingHom.id ℂ) s, R.secVal_mem_holSec s⟩ : R.holSec B)

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k} {q : Y' ⟶ Sp k'}
  {r : Y' ⟶ Y} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D D' : ℕ} {m : CxPts q τ → CxPts p σ} {B : LB Y}

variable (r m B) in

def pullVal : (B.ι → CxPts p σ → ℂ) →ₗ[ℂ] ((B.pull r).ι → CxPts q τ → ℂ) where
  toFun s J z := s (J PUnit.unit) (m z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullVal_injective (hb : Function.Surjective m) : Function.Injective (pullVal r m B) :=
  fun _ _ h => funext₂ fun i y => by
    obtain ⟨z, rfl⟩ := hb y
    exact congrFun₂ h (fun _ => i) z

theorem mem_ptsIn_pull (hm : ∀ z, (m z).1 = z.1 ≫ r) {J : (B.pull r).ι} {z : CxPts q τ} :
    z ∈ ptsIn q τ ((B.pull r).U J) ↔ m z ∈ ptsIn p σ (B.U (J PUnit.unit)) := by
  rw [← mem_ptsIn_preimage hm, mem_ptsIn, mem_ptsIn]
  exact mem_pull

theorem pullVal_mem_holSec (hm : ∀ z, (m z).1 = z.1 ≫ r) {R : AnRead p σ D} (R' : AnRead q τ D')
    {s : B.ι → CxPts p σ → ℂ} (hs : s ∈ R.holSec B) : pullVal r m B s ∈ R'.holSec (B.pull r) := by
  refine ⟨⟨fun J J' z h h' => ?_, fun J z h => hs.1.2 _ _ (mt (mem_ptsIn_pull hm).2 h)⟩, fun J =>
    ((hs.2 _).comp_map (isOpen_ptsIn _) hm R').mono fun _ hz => (mem_ptsIn_pull hm).1 hz⟩
  rw [gv_linComb (m := fun _ => m z) (fun _ => hm z) h h', Fintype.prod_unique, zpow_one]
  exact hs.1.1 _ _ _ ((mem_ptsIn_pull hm).1 h) ((mem_ptsIn_pull hm).1 h')

theorem cval_pullChart_ofSec {ρ : k →+* k'} (hm : ∀ z, (m z).1 = z.1 ≫ r) (w : r ≫ p = q ≫ spMap ρ)
    (s : B.Sec) : cval τ (pullChart (W := ⊤) (GlobalTheory.chartPullPull B r) w le_top (H0.ofSec p ⊤ s)) =
      pullVal r m B (secVal p σ s) := funext₂ fun J z => by
  by_cases h : z ∈ ptsIn q τ ((B.pull r).U J)
  · rw [cval_pullChart hm _ _ _ h, cval_ofSec]
    rfl
  · exact ((cval_mem _ _).2 _ _ h).trans ((secVal_mem s).2 _ _ (mt (mem_ptsIn_pull hm).2 h)).symm

end BaseChange

theorem SerreHolomorphicSections.bijective_valC (h : SerreHolomorphicSections) {F : Type} [Field F]
    {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ} [SmoothOfRelativeDimension D p] (hp : IsProjOver p)
    (R : AnRead p σ D) {B : LB Y} (hB : B.IsLB) : Function.Bijective (R.valC B) := by
  let := σ.toAlgebra
  have H := IsPullback.of_hasPullback p (spMap σ)
  generalize Limits.pullback.fst p (spMap σ) = r at H
  generalize Limits.pullback.snd p (spMap σ) = q at H
  have hq := ProjSpace.isProjOver_of_isPullback_spMap σ H hp
  have hs : SmoothOfRelativeDimension D q :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange D
    MorphismProperty.of_isPullback H ‹SmoothOfRelativeDimension D p›
  obtain ⟨m, hm, hb⟩ : ∃ m : CxPts q (RingHom.id ℂ) → CxPts p σ, (∀ z, (m z).1 = z.1 ≫ r) ∧
      Function.Surjective m := ⟨bcMap H.w (RingHom.id ℂ), fun _ => rfl, (bijective_bcMap H _).2⟩
  have hB' := LB.isLB_pull hB r
  have hS := h _ q D hs hq (AnRead.all _ _ D) _ hB'
  have hE := isExtension_pullChart_top (k := F) (E := ℂ) H hB hB' (GlobalTheory.chartPullPull B r) hp hq
  set ι := pullChart (O := ⊤) (W := ⊤) (GlobalTheory.chartPullPull B r) H.w le_top
  let L : SecC p σ B →ₗ[ℂ] H0 q (B.pull r) ⊤ :=
    SecC.lift (ι.toAddMonoidHom.comp (H0.ofSec p ⊤)) fun a s =>
      (congrArg ι (H0.ofSec_smul a s)).trans (map_smulₛₗ ι a _)
  have hL (s) : L (SecC.of p σ s) = ι (H0.ofSec p ⊤ s) := SecC.lift_of _ _ s
  have hc (x) : cval (RingHom.id ℂ) (L x) = pullVal r m B (SecC.val x) := by
    refine LinearMap.eqOn_span' (f := cval (RingHom.id ℂ) ∘ₗ L) (g := pullVal r m B ∘ₗ SecC.val)
      (s := range (SecC.of p σ)) ?_ (SecC.span_range_of.ge Submodule.mem_top)
    rintro _ ⟨s, rfl⟩
    simp only [LinearMap.comp_apply, hL, SecC.val_of]
    exact cval_pullChart_ofSec hm H.w s
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun s => ?_⟩
  · have h₀ : L x = 0 := by
      obtain ⟨t, ht⟩ := H0.bijective_ofSec_top.2 (L x)
      have e := hc x
      rw [← ht, cval_ofSec, show SecC.val x = 0 from congrArg Subtype.val hx, map_zero] at e
      rw [← ht, hS.1 (a₁ := t) (a₂ := 0) (Subtype.ext (e.trans (map_zero _).symm)), map_zero]
    have := finite_top hp hB
    let b := Module.finBasis F (H0 p B ⊤)
    choose v hv using fun i => H0.bijective_ofSec_top.2 (b i)
    have hx' : x ∈ Submodule.span ℂ (range fun i => SecC.of p σ (v i)) := by
      refine (SecC.span_range_of.ge.trans (Submodule.span_le.2 ?_)) Submodule.mem_top
      rintro _ ⟨s, rfl⟩
      have e : s = ∑ i, DVR.FlatBC.algX p ⊤ (b.repr (H0.ofSec p ⊤ s) i) • v i :=
        (H0.bijective_ofSec_top (p := p)).1 (by simp only [map_sum, H0.ofSec_smul, hv, b.sum_repr])
      rw [e, map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        rw [SecC.of_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx'
    simp only [map_sum, map_smul, hL, hv] at h₀
    simp [Fintype.linearIndependent_iff.1 (hE.indep _ b b.linearIndependent) c h₀]
  · obtain ⟨t, ht⟩ := hS.2 ⟨_, pullVal_mem_holSec hm (AnRead.all _ _ D) s.2⟩
    have hr : H0.ofSec q ⊤ t ∈ LinearMap.range L := by
      refine (hE.span.ge.trans (Submodule.span_le.2 ?_)) Submodule.mem_top
      rintro _ ⟨f, rfl⟩
      obtain ⟨u, rfl⟩ := H0.bijective_ofSec_top.2 f
      exact ⟨_, hL u⟩
    obtain ⟨x, hx⟩ := hr
    refine ⟨x, Subtype.ext (pullVal_injective (r := r) hb ((hc x).symm.trans ?_))⟩
    rw [hx, cval_ofSec]
    exact congrArg Subtype.val ht

end GlobalTheory.Published
