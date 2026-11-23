import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.HilbertRowConditions.RowPin

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Ker NumberField

namespace Formalism.MainNotions.DIV.HookProducts.AdmPtTw

def PtT (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) :
    ((D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ) →ₗ[ℂ] (D.PTw u μ).Wrow :=
  (D.PTw u μ).lowerMap ∘ₗ (D.PTw u μ).evz

structure PendTw (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) where
  br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ)
  coM : D.what₂.places.Pl → (T.fm u μ).clsP → (((D.chTw u μ).Y D.R.m → ℂ) →ₗ[ℂ]
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)
  coP : D.what₂.places.Pl → ((D.PTw u μ).Wrow →ₗ[ℂ] ((T.fm u μ).clsP →
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))
  Pt_eq : ∀ w, ∀ φ ∈ (T.fm u μ).Fi D.R.m, ∀ c,
    coP w (PtT D u μ φ) c = blk (fun τ => br τ) (coM w c (φ ((T.fm u μ).til c)))
  lat_co : ∀ w, ∀ x ∈ (T.fm u μ).S D.R.m w, ∀ c,
    coM w c ((T.fm u μ).emb D.R.m x ((T.fm u μ).til c)) ∈ IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (T.fm u μ).ptC,
    (∃ y ∈ (T.fm u μ).SP w, (T.fm u μ).ptEmb y = z) ↔ ∀ c, coP w z c ∈ IntSpan D w (D.fm u).sg

def LowerTieTwAt (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  (∀ φ ∈ (T.fm u μ).Fi D.R.m, PtT D u μ φ ∈ (T.fm u μ).ptC) ∧ (D.fm u).SgInterlace ∧
    ∃ P : PendTw D T u μ, ∀ τ, P.br τ = brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)

lemma blk_IntSpan_of {D : D7} {u : D.what₂.Word}
    (br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
      MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))
    (h4 : ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.IsBr (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) (br τ)) (w : D.what₂.places.Pl)
    (p : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)
    (hp : p ∈ IntSpan D w ((D.fm u).lam D.R.m)) : blk (fun τ => br τ) p ∈ IntSpan D w (D.fm u).sg := by
  unfold IntSpan at hp
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hx
    have hg : ∀ τ, ∃ g ∈ delSq ℤ _ ((D.fm u).sg τ),
        br τ (MvPolynomial.map (Int.castRingHom ℂ) (f τ)) = MvPolynomial.map (Int.castRingHom ℂ) g :=
      fun τ => by
        have h := (h4 τ).1 (f τ) (by unfold lamTr; rw [delSq_wSh]; exact hf τ)
        unfold sgTr at h
        rwa [delSq_wSh] at h
    choose g hg1 hg2 using hg
    refine AddSubgroup.subset_closure ⟨r, g, hr, hg1, ?_⟩
    rw [map_smul, blk_ten]
    congr 2
    funext τ
    exact hg2 τ
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

variable {D : D7} {T : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup}

lemma emb_memT (i : ℕ) (x : ((T.fm u μ).lat i).V) : (T.fm u μ).emb i x ∈ (T.fm u μ).Fi i := by
  rw [← ((T.fm u μ).emb_basis i).2, ← ((T.fm u μ).lat i).b.sum_repr x, map_sum]
  exact Submodule.sum_mem _ (fun a _ => by
    rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

lemma S_spanT (i : ℕ) (w : D.what₂.places.Pl) :
    Submodule.span D.what₂.LL ((T.fm u μ).S i w : Set ((T.fm u μ).lat i).V) = ⊤ := by
  rw [eq_top_iff, ← ((T.fm u μ).lat_good i).2.2]
  exact Submodule.span_mono (fun x hx => Submodule.subset_span hx)

theorem Pt_locT (P : PendTw D T u μ) (h4 : ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.IsBr (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) (P.br τ))
    (hPF : ∀ φ ∈ (T.fm u μ).Fi D.R.m, PtT D u μ φ ∈ (T.fm u μ).ptC) (w : D.what₂.places.Pl) :
    ∀ x ∈ (T.fm u μ).S D.R.m w,
      ∃ y ∈ (T.fm u μ).SP w, (T.fm u μ).ptEmb y = PtT D u μ ((T.fm u μ).emb D.R.m x) := by
  intro x hx
  refine (P.pt_co w _ (hPF _ (emb_memT _ x))).mpr (fun c => ?_)
  rw [P.Pt_eq w _ (emb_memT _ x) c]
  exact blk_IntSpan_of P.br h4 w _ (P.lat_co w x hx c)

theorem PRat_ofT (P : PendTw D T u μ) (h4 : ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.IsBr (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) (P.br τ))
    (hPF : ∀ φ ∈ (T.fm u μ).Fi D.R.m, PtT D u μ φ ∈ (T.fm u μ).ptC) : (T.fm u μ).PRat := by
  obtain ⟨w, _⟩ := exists_offT D u
  intro x
  show ∃ y, (T.fm u μ).ptEmb y = PtT D u μ ((T.fm u μ).emb D.R.m x)
  have hx : x ∈ Submodule.span D.what₂.LL ((T.fm u μ).S D.R.m w : Set ((T.fm u μ).lat D.R.m).V) := by
    rw [S_spanT]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨y, _, hy⟩ := Pt_locT P h4 hPF w x hx; exact ⟨y, hy⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, h1⟩ := hx; obtain ⟨a2, h2⟩ := hy
    exact ⟨a1 + a2, by rw [map_add, map_add, map_add, h1, h2]⟩
  | smul r x _ hx =>
    obtain ⟨a1, h1⟩ := hx
    exact ⟨r • a1, by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1, LinearMap.map_smul]⟩

theorem Pt_integralT (P : PendTw D T u μ) (h4 : ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.IsBr (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) (P.br τ))
    (hPF : ∀ φ ∈ (T.fm u μ).Fi D.R.m, PtT D u μ φ ∈ (T.fm u μ).ptC) (h : (T.fm u μ).PRat) :
    (T.fm u μ).PtilIntegral h := by
  intro x hx
  refine mem_of_forall_inLoc _ _ (fun p => ?_)
  obtain ⟨y, hy, hy'⟩ := Pt_locT P h4 hPF (D.plEq.symm p) x (Submodule.subset_span hx)
  have e : y = (T.fm u μ).PtL h x := (T.fm u μ).ptEmb_inj (by rw [hy', (T.fm u μ).PtL_spec h x]; rfl)
  have := D.inLoc_of_mem_locW (D.plEq.symm p) (T.fm u μ).ptLat.L y hy
  rwa [Equiv.apply_symm_apply, e] at this

theorem lowerTieTwAt_integral (h : LowerTieTwAt D T u μ) : ∃ hr : (T.fm u μ).PRat, (T.fm u μ).PtilIntegral hr := by
  obtain ⟨hz, hI, P, hP⟩ := h
  have h4 : ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.IsBr (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) (P.br τ) := fun τ => by
    rw [hP τ]; exact brOneIsBr D u τ (interlaceTr D u hI τ)
  exact ⟨PRat_ofT P h4 hz, Pt_integralT P h4 hz _⟩

theorem twisted_chain_integral_of_lowerTieTwAt (h : ∀ u μ, μ ≠ D.what₂.mu0 → LowerTieTwAt D T u μ) : Formalism.MainNotions.WeightDegreeSizes.TwistedChainIntegral D T :=
  fun u μ hμ => lowerTieTwAt_integral (h u μ hμ)

end Formalism.MainNotions.DIV.HookProducts.AdmPtTw
