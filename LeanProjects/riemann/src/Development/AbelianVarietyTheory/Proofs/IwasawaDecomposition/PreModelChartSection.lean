import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartGluingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesAgreeOnLieEmbeddingChartStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.LChart

theorem diag_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V] {n : ℕ} (c : Fin n → V)
    (hc : LinearIndependent k c) (j : Fin n) (cf : Fin n → k) (d : k) (hcf : ∀ m, j < m → cf m = 0)
    (h : (∑ m, cf m • c m) - d • c j ∈ Submodule.span k (c '' {m | m < j})) : d = cf j := by
  have h1 : (∑ m, cf m • c m) - cf j • c j ∈ Submodule.span k (c '' {m | m < j}) := by
    rw [← Finset.sum_erase_eq_sub (Finset.mem_univ j)]
    refine Submodule.sum_mem _ fun m hm => ?_
    rcases lt_trichotomy m j with hlt | heq | hgt
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hlt, rfl⟩)
    · exact absurd heq (Finset.ne_of_mem_erase hm)
    · rw [hcf m hgt, zero_smul]
      exact Submodule.zero_mem _
  have h2 := Submodule.sub_mem _ h1 h
  rw [sub_sub_sub_cancel_left, ← sub_smul] at h2
  by_contra hne
  have h3 := (Submodule.smul_mem_iff _ (sub_ne_zero.2 hne)).1 h2
  exact hc.notMem_span_image (s := {m | m < j}) (x := j) (lt_irrefl j) h3

theorem exists_ringHom {k : Type} [Field k] {X : Scheme.{0}} (f : Sp k ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ f ⁻¹ᵁ U) : ∃ ψ : Γ(X, U) →+* k, spMap ψ ≫ hU.fromSpec = f := by
  have hr : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact h (Set.mem_univ x)
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hU.fromSpec f hr)).hom, ?_⟩
  have : spMap (Spec.preimage (IsOpenImmersion.lift hU.fromSpec f hr)).hom =
      IsOpenImmersion.lift hU.fromSpec f hr := Spec.map_preimage _
  rw [this, IsOpenImmersion.lift_fac]

theorem ne_zero_of_chart {R k : Type} [CommRing R] [Field k] {N : ℕ} (c : R →+* k) (v : Fin (N + 1) → k)
    (hv : Ideal.span (Set.range v) = ⊤) (i : Fin (N + 1)) (h : ⊤ ≤ pt c v hv ⁻¹ᵁ chart R N i) : v i ≠ 0 := by
  intro h0
  rw [pt_preimage_chart, h0] at h
  have h1 := h (Set.mem_univ (IsLocalRing.closedPoint k))
  exact h1 (Ideal.zero_mem _)

theorem gen_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (n : ℕ) (u : Fin n → Let Dw.mult) (kk : Fin n) (h₀ : Down (u ∘ Fin.castLE kk.2.le)) (h₁ : Down (u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2))) (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M kk + 1)) (q₁ : Fin L'.n → Fin (plN M (kk + 1) + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g ⟨kk, _, h₀⟩ ⟨kk + 1, _, h₁⟩ L' ix q₀ q₁ r → ∀ (k : Type) [Field k] a a' i (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k) (cf : Fin (Dw.mult (u kk).1) → k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' → ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ L'.U i → (∀ m, (u kk).2 < m → cf m = 0) → IsCombAtG (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ (u kk).1) cf ((Z.fr a').bc φ' (u kk).1 (u kk).2) → valF (spMap φ ≫ Z.chart a) _ (r a i).val = valF (spMap φ ≫ Z.chart a) _ (r a' i).val * cf (u kk).2 := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T n u kk h₀ h₁ L' ix q₀ q₁ r hL k _ a a' i φ φ' cf hφ hi hcf hcomb
  have hle := (spMap φ ≫ Z.chart a).preimage_mono (hL.le i)
  have hle1 := hi.trans hle
  have hU : ⊤ ≤ (spMap φ ≫ Z.chart a ≫ Z.π) ⁻¹ᵁ L.U (ix i) := fun x hx => (hle1 hx).1
  have hφπ : spMap φ ≫ Z.chart a ≫ Z.π = spMap φ' ≫ Z.chart a' ≫ Z.π := by
    rw [← Category.assoc, hφ, Category.assoc]
  obtain ⟨ψ, hψ⟩ := exists_ringHom _ (aff (ix i)) hU
  have fa := T.frame a k φ
  have fa' := T.frame a' k φ'
  rw [← hφπ] at fa'
  have sf := GlobalTheory.T.pre_model_chart_compatible E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a a' φ φ' hφ
  rw [T.ty] at sf
  obtain ⟨t1, t2, -⟩ := GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd T.emb (ix i) k ψ _ _ _ _ _ hψ fa fa'
  obtain ⟨d, hd⟩ := t1.1 sf
  have hc := (T.emb.comb_iff (ix i) ψ hψ (fun j => (fa.1 (u kk).1 j).1) (fa'.1 (u kk).1 (u kk).2).1 cf).1 hcomb
  have hdc : d (u kk) = cf (u kk).2 := by
    refine diag_eq _ (t2 (u kk).1) (u kk).2 cf _ hcf ?_
    have := hd (u kk)
    simp only [hc] at this
    exact this
  have P0 := congrFun (plk_tri _ _ _ _ _ _ d _ _ hd h₀) (q₀ i)
  have P1 := congrFun (plk_tri _ _ _ _ _ _ d _ _ hd h₁) (q₁ i)
  have v := hL.val k a i φ ψ hψ hi
  have v' := hL.val k a' i φ' ψ (hψ.trans hφπ) (hφ ▸ hi)
  obtain ⟨hu, hp⟩ := GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a' (ix i) φ' ψ (hψ.trans hφπ)
    ⟨kk + 1, _, h₁⟩
  have hne := ne_zero_of_chart _ _ hu (q₁ i) (by
    rw [← hp, ← Category.assoc, ← hφ]
    exact fun x hx => (hle1 hx).2.2)
  rw [← hφ] at v'
  have hprod : ∏ l : Fin (kk + 1), d ((u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2)) l) =
      (∏ l : Fin kk, d ((u ∘ Fin.castLE kk.2.le) l)) * d (u kk) := by
    rw [Fin.prod_univ_castSucc]
    rfl
  rw [hprod, hdc] at P1
  simp only [Pi.smul_apply, smul_eq_mul] at P0 P1
  dsimp only at v v' hne
  rw [P1] at hne
  rw [P0, P1, ← v] at v'
  have hD := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hP := right_ne_zero_of_mul hne
  apply mul_right_cancel₀ (mul_ne_zero hD hP)
  linear_combination -v'

end GlobalTheory.FlagEmb.LChart
