import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDominantSpMapOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SInfMulNormPlk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartGluing

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.LineNorm

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ β : A →+* B, f = spMap β :=
  ⟨(Spec.preimage f).hom, (Spec.map_preimage f).symm⟩

theorem exists_fromSpec {A : Type} [CommRing A] {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : Sp A ⟶ X)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ∃ φ : Γ(X, U) →+* A, spMap φ ≫ hU.fromSpec = x := by
  have hr : Set.range x ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact h (Set.mem_univ y)
  obtain ⟨φ, hφ⟩ := exists_spMap' (A := Γ(X, U)) (IsOpenImmersion.lift hU.fromSpec x hr)
  exact ⟨φ, hφ ▸ IsOpenImmersion.lift_fac _ _ hr⟩

theorem max_of_chart {R : Type} [CommRing R] {N : ℕ} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (f : Sp ↥(intO C) ⟶ PSpace R N) (q : Fin (N + 1)) (hq : ⊤ ≤ f ⁻¹ᵁ chart R N q) (c : R →+* C)
    (w : Fin (N + 1) → C) (hw : Ideal.span (Set.range w) = ⊤) (h : spMap (intO C).subtype ≫ f = pt c w hw) :
    (∀ q', ‖w q'‖ ≤ ‖w q‖) ∧ w q ≠ 0 := by
  have := GlobalTheory.LatDRFree.intO_isLocalRing C
  obtain ⟨b, hb⟩ := exists_spMap' (f ≫ PSpace.str R N)
  obtain ⟨v, hv, rfl⟩ := exists_eq_pt b f hb
  rw [pt_preimage_chart] at hq
  have hu : IsUnit (v q) := by
    have h1 : IsLocalRing.closedPoint ↥(intO C) ∈ spOpen (v q) := hq (Set.mem_univ _)
    by_contra hn
    exact mem_spOpen.1 h1 hn
  rw [GlobalTheory.ProjSpace.spMap_pt] at h
  have hc : (intO C).subtype.comp b = c := by
    have h1 := congrArg (· ≫ PSpace.str R N) h
    simp only [pt_str] at h1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hc
  obtain ⟨s, rfl⟩ := (pt_eq_pt_iff _ _ _).1 h
  have h1 : ‖(v q : C)‖ = 1 := by
    obtain ⟨a, ha⟩ := hu.exists_right_inv
    have h2 : ‖(v q : C)‖ * ‖(a : C)‖ = 1 := by
      rw [← norm_mul, ← norm_one (α := C)]
      exact congrArg (fun x : ↥(intO C) => ‖(x : C)‖) ha
    have h3 : ‖(v q : C)‖ ≤ 1 := (v q).2
    have h4 : ‖(a : C)‖ ≤ 1 := a.2
    nlinarith [norm_nonneg (v q : C), norm_nonneg (a : C)]
  have e : ∀ q', (s • ((intO C).subtype ∘ v)) q' = s.val * (v q' : C) := fun _ => rfl
  refine ⟨fun q' => ?_, ?_⟩
  · rw [e, e, norm_mul, norm_mul, h1]
    exact mul_le_mul_of_nonneg_left (v q').2 (norm_nonneg _)
  · rw [e]
    exact mul_ne_zero s.ne_zero (fun h0 => by simp [h0] at h1)

theorem log_norm_add_log_grNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (n : ℕ) (u : Fin n → Let Dw.mult) (kk : Fin n) (h₀ : Down (u ∘ Fin.castLE kk.2.le)) (h₁ : Down (u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2))) (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M kk + 1)) (q₁ : Fin L'.n → Fin (plN M (kk + 1) + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g ⟨kk, _, h₀⟩ ⟨kk + 1, _, h₁⟩ L' ix q₀ q₁ r → Down u → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (z : Sp ↥(intO C) ⟶ Z.X) a i (φ : Γ(Z.X, (Z.U a).1) →+* C), spMap φ ≫ Z.chart a = spMap (intO C).subtype ≫ z → ⊤ ≤ z ⁻¹ᵁ L'.U i → Real.log ‖valF (spMap (intO C).subtype ≫ z) _ (r a i).val‖ + Real.log (grNorm (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π) (latDR (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π)) (fun j => (Z.fr a).bc φ (u j).1 (u j).2) kk) = 0 := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T n u kk h₀ h₁ L' ix q₀ q₁ r hL hu C _ _ z a i φ hφ hz
  have : (Y Z.i).X.IsSeparated := by
    have hp : IsProper (Y Z.i).s := projProper _ _ _ (Y Z.i).proj
    constructor
    rw [← terminal.comp_from (Y Z.i).s]
    infer_instance
  have hle := hz.trans (z.preimage_mono (hL.le i))
  have hU : ⊤ ≤ (z ≫ Z.π) ⁻¹ᵁ L.U (ix i) := fun y hy => (hle hy).1
  have hq₀ : ⊤ ≤ (z ≫ g ⟨kk, _, h₀⟩) ⁻¹ᵁ chart _ _ (q₀ i) := fun y hy => (hle hy).2.1
  have hq₁ : ⊤ ≤ (z ≫ g ⟨kk + 1, _, h₁⟩) ⁻¹ᵁ chart _ _ (q₁ i) := fun y hy => (hle hy).2.2
  obtain ⟨φO, hO⟩ := exists_fromSpec (aff (ix i)) _ hU
  have hx : spMap ((intO C).subtype.comp φO) ≫ (aff (ix i)).fromSpec = (spMap (intO C).subtype ≫ z) ≫ Z.π := by
    rw [Category.assoc, ← hO, ← Category.assoc]
    congr 1
    exact Spec.map_comp (CommRingCat.ofHom φO) (CommRingCat.ofHom (intO C).subtype)
  have hx' : spMap φ ≫ Z.chart a ≫ Z.π = (spMap (intO C).subtype ≫ z) ≫ Z.π := by rw [← hφ, Category.assoc]
  have P := GlobalTheory.FlagEmb.PlkPt.plk_pt E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T C a (ix i) φ _ (hx.trans hx'.symm)
  have hg : ∀ en, spMap (intO C).subtype ≫ z ≫ g en = spMap φ ≫ Z.chart a ≫ g en := fun en => by
    rw [← Category.assoc, ← hφ, Category.assoc]
  obtain ⟨hu₀, e₀⟩ := P ⟨kk, _, h₀⟩
  obtain ⟨hu₁, e₁⟩ := P ⟨kk + 1, _, h₁⟩
  obtain ⟨hun, -⟩ := P ⟨n, u, hu⟩
  obtain ⟨m₀, n₀⟩ := max_of_chart _ _ hq₀ _ _ _ ((hg _).trans e₀)
  obtain ⟨m₁, n₁⟩ := max_of_chart _ _ hq₁ _ _ _ ((hg _).trans e₁)
  have hv := hL.val C a i φ _ (hx.trans hx'.symm) (by
    rw [hφ]
    exact (spMap (intO C).subtype).preimage_mono hz)
  have key := GlobalTheory.FlagEmb.GradedNorm.sInf_mul_norm_plk C M n
    (fun j => crd (ix i) C ((intO C).subtype.comp φO) ((Z.fr a).bc φ (u j).1 (u j).2)) kk (q₀ i) (q₁ i)
    (span_range_eq_top_iff_ne_zero.1 hun) m₀ m₁
  have tan : ∀ j, IsTanAtG (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π) ((Z.fr a).bc φ (u j).1 (u j).2) :=
    fun j => hx' ▸ ((T.frame a C φ).1 (u j).1 (u j).2).1
  have lat := fun w => GlobalTheory.LatDRCrd.mem_latDR_iff_crd E H _ (Y Z.i).t L aff M crd T.emb (ix i) C φO _ w hx
  have hS : grNorm (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π)
      (latDR (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π)) (fun j => (Z.fr a).bc φ (u j).1 (u j).2) kk =
      sInf {s : ℝ | ∃ cf : Fin n → C, cf kk ≠ 0 ∧ (∀ k, kk < k → cf k = 0) ∧ (∀ s, ‖(∑ j, cf j •
        crd (ix i) C ((intO C).subtype.comp φO) ((Z.fr a).bc φ (u j).1 (u j).2)) s‖ ≤ 1) ∧ s = ‖cf kk‖⁻¹} := by
    refine congrArg sInf (Set.ext fun s => exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_left fun _ => ⟨?_, fun hb => ?_⟩)
    · rintro ⟨w, hw, hc⟩
      have ht := comb_tan _ tan hc
      rw [← (T.emb.comb_iff _ _ hx tan ht cf).1 hc]
      exact (lat w ht).1 hw
    · obtain ⟨w, ht, hc⟩ := exists_comb _ tan cf
      refine ⟨w, (lat w ht).2 ?_, hc⟩
      rw [(T.emb.comb_iff _ _ hx tan ht cf).1 hc]
      exact hb
  rw [hS, ← hφ]
  have aux : ∀ (x A B : C) (s : ℝ), x * B = A → s * ‖A‖ = ‖B‖ → B ≠ 0 → Real.log ‖x‖ + Real.log s = 0 := by
    intro x A B s h1 h2 h3
    have h4 : ‖x‖ * s = 1 := by
      refine mul_right_cancel₀ (norm_ne_zero_iff.2 h3) ?_
      rw [← h1, norm_mul] at h2
      rw [one_mul]
      linear_combination h2
    rw [← Real.log_mul (left_ne_zero_of_mul_eq_one h4) (right_ne_zero_of_mul_eq_one h4), h4, Real.log_one]
  exact aux _ _ _ _ hv key n₁

end GlobalTheory.FlagEmb.LineNorm
