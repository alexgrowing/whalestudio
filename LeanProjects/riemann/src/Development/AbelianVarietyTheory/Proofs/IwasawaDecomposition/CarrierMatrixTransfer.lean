import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierIndependentSpanIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.IntPt

section Lin

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem span_cols {n k : ℕ} (hk : k ≤ n) (a a' : Matrix (Fin n) (Fin n) R) (h2 : a' * a = 1)
    (ξ : Fin k → Fin n → K) (hξ : LinearIndependent K ξ)
    (h0 : ∀ (l : Fin k) (j : Fin n), k ≤ (j : ℕ) → ∑ i, algebraMap R K (a j i) * ξ l i = 0) :
    LinearIndependent K (fun (l : Fin k) => algebraMap R K ∘ fun i => a' i (Fin.castLE hk l)) ∧
      Submodule.span K (Set.range fun (l : Fin k) => algebraMap R K ∘ fun i => a' i (Fin.castLE hk l)) =
        Submodule.span K (Set.range ξ) := by
  set φ := algebraMap R K with hφ
  set c : Fin k → Fin n → K := fun l => φ ∘ fun i => a' i (Fin.castLE hk l) with hc
  have hmap : a'.map φ * a.map φ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hmem : ∀ l, ξ l ∈ Submodule.span K (Set.range c) := fun l => by
    have e : ξ l = ∑ j : Fin n, (∑ i, φ (a j i) * ξ l i) • (fun r => φ (a' r j)) := by
      have := Matrix.mulVec_mulVec (ξ l) (a'.map φ) (a.map φ)
      rw [hmap, Matrix.one_mulVec] at this
      refine this.symm.trans ?_
      funext r
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : k ≤ (j : ℕ)
    · rw [h0 l j hj, zero_smul]
      exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, not_le.1 hj⟩, ?_⟩)
      rfl
  have hle : Submodule.span K (Set.range ξ) ≤ Submodule.span K (Set.range c) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hmem)
  have hf : Module.finrank K (Submodule.span K (Set.range ξ)) = k := by
    simpa using finrank_span_eq_card hξ
  have hc' : Module.finrank K (Submodule.span K (Set.range c)) ≤ k := by
    simpa [Set.finrank] using finrank_range_le_card (R := K) c
  have heq : Submodule.span K (Set.range ξ) = Submodule.span K (Set.range c) :=
    Submodule.eq_of_le_of_finrank_le hle (hc'.trans hf.ge)
  refine ⟨linearIndependent_iff_card_eq_finrank_span.2 ?_, heq.symm⟩
  rw [Set.finrank, ← heq, hf]
  simp

theorem unimod {M k n : ℕ} (hk : k ≤ n) (A : Matrix (Fin (M + 1)) (Fin n) R) (A' : Matrix (Fin n) (Fin (M + 1)) R)
    (hA : A' * A = 1) (a a' : Matrix (Fin n) (Fin n) R) (h1 : a * a' = 1) :
    Ideal.span (Set.range (plk (fun l : Fin k => A.mulVec fun i => a' i (Fin.castLE hk l)) id)) = ⊤ := by
  have h := GlobalTheory.FlagEmb.CauchyBinet.lform_plk R M k (Fin k) (Fin n) (fun j r => (a * A') j r)
    (fun l : Fin k => A.mulVec fun i => a' i (Fin.castLE hk l)) (Fin.castLE hk) id
  have hm : (Matrix.of fun l l' : Fin k => ∑ r, (a * A') (Fin.castLE hk l') r *
      (A.mulVec fun i => a' i (Fin.castLE hk (id l))) r) = 1 := by
    ext l l'
    have e : ∑ r, (a * A') (Fin.castLE hk l') r * (A.mulVec fun i => a' i (Fin.castLE hk (id l))) r =
        (a * a') (Fin.castLE hk l') (Fin.castLE hk l) := by
      have : (a * A').mulVec (A.mulVec fun i => a' i (Fin.castLE hk (id l))) =
          a.mulVec fun i => a' i (Fin.castLE hk (id l)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hA, Matrix.mul_one]
      exact congrFun this (Fin.castLE hk l')
    rw [Matrix.of_apply, e, h1, Matrix.one_apply, Matrix.one_apply]
    by_cases hl : l = l'
    · simp [hl]
    · rw [if_neg (fun e => hl (Fin.castLE_injective hk e).symm), if_neg hl]
  rw [hm, Matrix.det_one] at h
  rw [Ideal.eq_top_iff_one, ← h]
  exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)

end Lin

theorem main : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (s : Z ⟶ Sp O) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)), q ≫ PSpace.str O _ = f ≫ s → ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z) (α : C.A) (_ : ⊤ ≤ z ⁻¹ᵁ C.B α) (n' : ℕ) (a : Matrix (Fin n') (Fin (C.n α)) R) (a' : Matrix (Fin (C.n α)) (Fin n') R) (y : Sp K ⟶ Z') (hy : ⊤ ≤ (y ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin k → Fin (C.n α) → K), a * a' = 1 → a' * a = 1 → y ≫ f = spMap (algebraMap R K) ≫ z → Car Em f q y α hy ξ → (∀ (l : Fin k) (j : Fin n'), k ≤ (j : ℕ) → ∑ i, algebraMap R K (a j i) * ξ l i = 0) → ∃ y₀ : Sp R ⟶ PSpace O (plN N k), y₀ ≫ PSpace.str O _ = z ≫ s ∧ y ≫ q = spMap (algebraMap R K) ≫ y₀ := by
  intro O _ Z Z' s C N k Em f q hq R K _ _ _ z α hz n' a a' y hy ξ h1 h2 hyz hcar h0
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  obtain rfl : n' = C.n α := by simpa using Matrix.square_of_invertible a a' h1 h2
  obtain ⟨hli, hiff, -⟩ := GlobalTheory.T.carrier_independent_span_iff O Z Z' C N k Em f q K y α hy ξ hcar
  have hk : k ≤ C.n α := by simpa using hli.fintype_card_le_finrank
  obtain ⟨l1, l2⟩ := span_cols hk a a' h2 ξ hli h0
  obtain ⟨g, hv, e⟩ := (hiff _).2 ⟨l1, l2⟩
  obtain ⟨A', hA'⟩ := Em.linv α
  set φ := algebraMap R K with hφ
  let g₀ : O →+* R := (Spec.preimage (z ≫ s)).hom
  have hg₀ : spMap g₀ = z ≫ s := Spec.map_preimage (z ≫ s)
  have hAz : A'.map (ev z _ hz) * (Em.A α).map (ev z _ hz) = 1 := by
    rw [← Matrix.map_mul, hA', Matrix.map_one _ (map_zero _) (map_one _)]
  have hu := unimod hk _ _ hAz a a' h1
  refine ⟨pt g₀ _ hu, by rw [GlobalTheory.ProjSpace.pt_str, hg₀], ?_⟩
  have hg : g = φ.comp g₀ := by
    have h5 : spMap (φ.comp g₀) = spMap φ ≫ spMap g₀ := by
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    have h3 : spMap g = spMap (φ.comp g₀) := by
      have h4 := congrArg (· ≫ PSpace.str O _) e
      simp only [Category.assoc, GlobalTheory.ProjSpace.pt_str, hq] at h4
      rw [← h4, ← Category.assoc, hyz, Category.assoc, h5, hg₀]
    exact congrArg (·.hom) (Spec.map_injective h3)
  have hev : ev (y ≫ f) _ hy = φ.comp (ev z _ hz) :=
    (GlobalTheory.FlagMod.ev_congr hyz _ hy (hyz ▸ hy)).trans (GlobalTheory.FlagMod.ev_spMap φ z _ hz _)
  have hp : plk (fun l : Fin k => ((Em.A α).map (ev (y ≫ f) _ hy)).mulVec (φ ∘ fun i => a' i (Fin.castLE hk l))) id =
      φ ∘ plk (fun l : Fin k => ((Em.A α).map (ev z _ hz)).mulVec fun i => a' i (Fin.castLE hk l)) id := by
    rw [GlobalTheory.FlagEmb.map_plk]
    congr 1
    funext l
    funext r
    have hm : (Em.A α).map (φ.comp (ev z _ hz)) = ((Em.A α).map (ev z _ hz)).map φ := by
      rw [Matrix.map_map]
      rfl
    rw [hev, hm]
    exact (RingHom.map_mulVec φ ((Em.A α).map (ev z _ hz)) _ r).symm
  have hpt : ∀ (c : O →+* K) (v w : Fin (plN N k + 1) → K) (hv : Ideal.span (Set.range v) = ⊤)
      (hw : Ideal.span (Set.range w) = ⊤), v = w → pt c v hv = pt c w hw := by
    rintro c v w hv hw rfl
    rfl
  rw [e, GlobalTheory.ProjSpace.spMap_pt]
  subst hg
  exact hpt _ _ _ _ _ hp

end GlobalTheory.GrCl.IntPt
