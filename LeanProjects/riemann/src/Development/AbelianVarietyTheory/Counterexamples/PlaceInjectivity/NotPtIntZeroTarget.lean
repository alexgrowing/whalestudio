import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty

noncomputable section

namespace GlobalTheory.LvT.PtIntTest

open Formalism.BasicNotions Classical NumberField

variable {D : D7} {u : D.what₂.Word}

theorem ptInt_iff (X : Ch D u) : PtInt X ↔
    ∀ x ∈ (X.fm.lat D.R.m).L, ∃ y ∈ X.fm.ptLat.L, X.fm.ptEmb y = Pt X (X.fm.emb D.R.m x) := by
  constructor
  · rintro ⟨-, h, hI⟩ x hx
    exact ⟨_, hI x hx, X.fm.PtL_spec h x⟩
  · intro H
    have hR : X.fm.PRat := by
      intro x
      have hx : x ∈ Submodule.span D.what₂.LL ((X.fm.lat D.R.m).L : Set (X.fm.lat D.R.m).V) := by
        rw [(X.fm.lat_good D.R.m).2.2]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨y, -, hy⟩ := H x hx; exact ⟨y, hy⟩
      | zero => exact ⟨0, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨y, hy⟩ := ha
        obtain ⟨z, hz⟩ := hb
        exact ⟨y + z, by simp [hy, hz]⟩
      | smul c a _ ha =>
        obtain ⟨y, hy⟩ := ha
        exact ⟨c • y, by simp only [LinearMap.map_smulₛₗ, hy, RingHom.id_apply]⟩
    refine ⟨fun φ hφ => ?_, hR, fun x hx => ?_⟩
    · rw [← (X.fm.emb_basis D.R.m).2] at hφ
      refine (Submodule.span_le (p := X.fm.ptC.comap (Pt X))).2 ?_ hφ
      rintro _ ⟨a, rfl⟩
      obtain ⟨y, hy⟩ := hR ((X.fm.lat D.R.m).b a)
      show Pt X _ ∈ X.fm.ptC
      have : Pt X (X.fm.emb D.R.m ((X.fm.lat D.R.m).b a)) = X.fm.ptEmb y := hy.symm
      rw [this, ← X.fm.ptEmb_basis.2, ← X.fm.ptLat.b.sum_repr y, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · obtain ⟨y, hy, e⟩ := H x hx
      have : X.fm.PtL hR x = y := X.fm.ptEmb_inj ((X.fm.PtL_spec hR x).trans e.symm)
      rw [this]; exact hy

def zeroTarget (Tw : TwForms D) : TwForms D where
  A := Tw.A
  A_T := Tw.A_T
  fm u μ := { Tw.fm u μ with
    ptC := ⊥
    ipP := 0
    ptLat := Examples₂.fmZeroHLat D.what₂.LL
    ptLat_good := Examples₂.fmZeroHLat_good _
    ptEmb := 0
    ptEmb_basis := ⟨linearIndependent_empty_type, by rw [Set.range_eq_empty, Submodule.span_empty]⟩
    ptEmb_norm := fun x => by rw [Examples₂.fmZeroHLat_maj]; simp }
  e0 := Tw.e0
  twist_preserves_base_lattice := Tw.twist_preserves_base_lattice
  embed_mul_block_embedding := Tw.embed_mul_block_embedding
  eMu0 := Tw.eMu0
  eMu0_lat := Tw.eMu0_lat
  eMu0_emb := Tw.eMu0_emb

def scaleTarget (Tw : TwForms D) (c : D.what₂.LL) (hc : c ≠ 0) : TwForms D where
  A := Tw.A
  A_T := Tw.A_T
  fm u μ := { Tw.fm u μ with
    ptLat := { (Tw.fm u μ).ptLat with
      L := (Tw.fm u μ).ptLat.L.map ((c • LinearMap.id : _ →ₗ[D.what₂.LL] _).restrictScalars (𝓞 D.what₂.LL)) }
    ptLat_good := by
      obtain ⟨h1, h2, h3⟩ := (Tw.fm u μ).ptLat_good
      refine ⟨h1, h2.map _, ?_⟩
      rw [eq_top_iff, ← h3, Submodule.span_le]
      intro x hx
      have : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
    ptEmb := (Tw.fm u μ).ptEmb
    ptEmb_basis := (Tw.fm u μ).ptEmb_basis
    ptEmb_norm := (Tw.fm u μ).ptEmb_norm }
  e0 := Tw.e0
  twist_preserves_base_lattice := Tw.twist_preserves_base_lattice
  embed_mul_block_embedding := Tw.embed_mul_block_embedding
  eMu0 := Tw.eMu0
  eMu0_lat := Tw.eMu0_lat
  eMu0_emb := Tw.eMu0_emb

end GlobalTheory.LvT.PtIntTest
