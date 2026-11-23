import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependentStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

open GlobalTheory.ProjSpace (pt_eq_pt_iff pt_str span_range_eq_top_iff_ne_zero)

theorem plk_smul_all {S : Type} [CommRing S] {M k : ℕ} (u : S) (v : Fin k → Fin (M + 1) → S) :
    plk (fun l => u • v l) id = u ^ k • plk v id := by
  funext q
  have h : (Matrix.of fun l l' => (u • v l) (GlobalTheory.FlagEmb.plE M k q l')) =
      u • Matrix.of fun l l' => v l (GlobalTheory.FlagEmb.plE M k q l') := by
    ext; simp
  change (Matrix.of fun l l' => (u • v l) (GlobalTheory.FlagEmb.plE M k q l')).det =
    u ^ k * (Matrix.of fun l l' => v l (GlobalTheory.FlagEmb.plE M k q l')).det
  rw [h, Matrix.det_smul, Fintype.card_fin]

theorem exists_pt_eq_of_smul {O K : Type} [CommRing O] [Field K] {N : ℕ} (g : O →+* K) {v v' : Fin (N + 1) → K}
    (hv : Ideal.span (Set.range v) = ⊤) (r : Kˣ) (h : v' = (r : K) • v) : ∃ hv', pt g v hv = pt g v' hv' := by
  have h0 : v' ≠ 0 := h ▸ smul_ne_zero r.ne_zero (span_range_eq_top_iff_ne_zero.1 hv)
  exact ⟨span_range_eq_top_iff_ne_zero.2 h0, (pt_eq_pt_iff g _ _).2 ⟨r, h⟩⟩

theorem plk_point_iff {O K : Type} [CommRing O] [Field K] {N n k : ℕ} (A : Matrix (Fin (N + 1)) (Fin n) K)
    (A' : Matrix (Fin n) (Fin (N + 1)) K) (h1 : A' * A = 1) (y : Sp K ⟶ PSpace O (plN N k)) (ξ : Fin k → Fin n → K)
    (hξ : ∃ (g : O →+* K) (hv : _), y = pt g (plk (fun l => A.mulVec (ξ l)) id) hv) :
    LinearIndependent K ξ ∧ ∀ ξ' : Fin k → Fin n → K,
      (∃ (g : O →+* K) (hv : _), y = pt g (plk (fun l => A.mulVec (ξ' l)) id) hv) ↔
        LinearIndependent K ξ' ∧ Submodule.span K (Set.range ξ') = Submodule.span K (Set.range ξ) := by
  obtain ⟨g, hv, hg⟩ := hξ
  have hinj : Function.Injective A.mulVecLin := by
    intro x y hxy
    have := congrArg A'.mulVec hxy
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
  have hli : ∀ ξ' : Fin k → Fin n → K, LinearIndependent K (fun l => A.mulVec (ξ' l)) ↔ LinearIndependent K ξ' :=
    fun ξ' => LinearMap.linearIndependent_iff (v := ξ') A.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  have hsp : ∀ ξ' : Fin k → Fin n → K, Submodule.span K (Set.range fun l => A.mulVec (ξ' l)) =
      (Submodule.span K (Set.range ξ')).map A.mulVecLin := fun ξ' => by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hI := (GlobalTheory.T.plucker_nonzero_iff_independent K N k (fun l => A.mulVec (ξ l)) fun l => A.mulVec (ξ l)).1.1
    (span_range_eq_top_iff_ne_zero.1 hv)
  refine ⟨(hli ξ).1 hI, fun ξ' => ?_⟩
  have hk := (GlobalTheory.T.plucker_nonzero_iff_independent K N k (fun l => A.mulVec (ξ l)) fun l => A.mulVec (ξ' l)).2 hI
  rw [hli, hsp, hsp, (Submodule.map_injective_of_injective hinj).eq_iff] at hk
  rw [hk]
  constructor
  · rintro ⟨g', hv', hg'⟩
    have e := hg.symm.trans hg'
    have e1 : spMap g = spMap g' := by rw [← pt_str g _ hv, e, pt_str]
    obtain rfl : g = g' := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    exact (pt_eq_pt_iff g _ _).1 e
  · rintro ⟨r, hr⟩
    obtain ⟨hv', e⟩ := exists_pt_eq_of_smul g hv r hr
    exact ⟨g, hv', hg.trans e⟩

theorem plk_point_change {O K : Type} [CommRing O] [Field K] {N n n' k : ℕ} (A : Matrix (Fin (N + 1)) (Fin n) K)
    (B : Matrix (Fin (N + 1)) (Fin n') K) (T : Matrix (Fin n') (Fin n) K) (u : Kˣ) (hu : B * T = (u : K) • A)
    (y : Sp K ⟶ PSpace O (plN N k)) (ξ : Fin k → Fin n → K)
    (hξ : ∃ (g : O →+* K) (hv : _), y = pt g (plk (fun l => A.mulVec (ξ l)) id) hv) :
    ∃ (g : O →+* K) (hv : _), y = pt g (plk (fun l => B.mulVec (T.mulVec (ξ l))) id) hv := by
  obtain ⟨g, hv, hg⟩ := hξ
  have hr : plk (fun l => B.mulVec (T.mulVec (ξ l))) id = ((u ^ k : Kˣ) : K) • plk (fun l => A.mulVec (ξ l)) id := by
    simp only [Matrix.mulVec_mulVec, hu, Matrix.smul_mulVec]
    rw [plk_smul_all, Units.val_pow_eq_pow_val]
  obtain ⟨hv', e⟩ := exists_pt_eq_of_smul g hv _ hr
  exact ⟨g, hv', hg.trans e⟩

theorem car_span : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) (K : Type) [Field K] (w : Sp K ⟶ Z') (β : C.A) (hβ : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B β) (ξ : Fin k → Fin (C.n β) → K), Car Em f q w β hβ ξ → LinearIndependent K ξ ∧ (∀ ξ' : Fin k → Fin (C.n β) → K, Car Em f q w β hβ ξ' ↔ LinearIndependent K ξ' ∧ Submodule.span K (Set.range ξ') = Submodule.span K (Set.range ξ)) ∧ ∀ (α : C.A) (hα : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), Car Em f q w α hα fun l => (C.tr α β (w ≫ f) hα hβ).mulVec (ξ l) := by
  intro O _ Z Z' C N k Em f q K _ w β hβ ξ hξ
  obtain ⟨A', hA'⟩ := Em.linv β
  have h1 : A'.map (ev (w ≫ f) _ hβ) * (Em.A β).map (ev (w ≫ f) _ hβ) = 1 := by
    rw [← Matrix.map_mul, hA', Matrix.map_one _ (map_zero _) (map_one _)]
  have h := plk_point_iff _ _ h1 (w ≫ q) ξ hξ
  refine ⟨h.1, h.2, fun α hα => ?_⟩
  obtain ⟨u, hu⟩ := Em.compat α β K (w ≫ f) hα hβ
  exact plk_point_change _ _ _ u hu (w ≫ q) ξ hξ

end GlobalTheory.GrCl
