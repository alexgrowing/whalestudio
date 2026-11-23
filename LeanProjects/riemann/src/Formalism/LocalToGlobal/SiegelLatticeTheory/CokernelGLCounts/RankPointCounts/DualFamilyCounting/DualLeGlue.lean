import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormMemOfDual

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
  {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)}

theorem memW (hG : Good hc M T 𝔭 Λ) {b : V} (hb : b ∈ locF 𝔭 (dualIn h (orthK h U) T)) :
    b ∈ orthK h U := by
  obtain ⟨x, -, rfl⟩ := hG.oW b hb
  first
  | exact Submodule.projection_apply_mem _ _ _ _
  | exact Submodule.projection_apply_mem _ _ _
  | exact Submodule.projection_apply_mem _ _
  | exact (orthK h U).projection_apply_mem _ _ _
  | (unfold prO; simp)

theorem mem_glue_of (hG₀ : Good hc M T 𝔭 Λ₀) {y : V} (hy : y ∈ Λ₀)
    (x' : ↥(locF 𝔭 (dualIn h (orthK h U) T)))
    (hx' : Submodule.Quotient.mk x' = P (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩)) :
    prO hc y + x' ∈ glue hc T 𝔭 Λ₀ P := by
  have hx'W : (x' : V) ∈ orthK h U := memW hG₀ x'.2
  have hyU : prO hc y ∈ U := by
    first
    | exact Submodule.projection_apply_mem _ _ _ _
    | exact Submodule.projection_apply_mem _ _ _
    | exact Submodule.projection_apply_mem _ _
    | (unfold prO; simp)
  have h0 : prO hc.symm (prO hc y) = 0 := by
    first
    | exact prO_symm_of_mem_U hyU
    | (rw [prO_apply]; simp [hyU])
    | (unfold prO; simp [hyU])
  refine ⟨x', ?_, y, hy, ⟨prO hc.symm y, hG₀.iW y hy⟩, rfl, ?_, hx'⟩
  · rw [map_add, orth_projection_symm_of_mem (hc' := hc) hx'W, h0, zero_add]
  · rw [map_add, prO_of_mem_U (hc' := hc) hyU, orth_projection_of_mem_compl (hc' := hc) hx'W, add_zero]

theorem glue_inf_U (hG₀ : Good hc M T 𝔭 Λ₀) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hP : FP P) :
    glue hc T 𝔭 Λ₀ P ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M := by
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨b, hb, y, hy, c, hcy, hU, hPb⟩, hxU⟩
    have hb0 : b = 0 :=
      Subtype.ext (hb.trans ((prO_symm_of_mem_U (hc' := hc) hxU).trans Submodule.coe_zero.symm))
    rw [hb0, Submodule.Quotient.mk_zero] at hPb
    have hxy : prO hc y = x := by rw [hU, prO_of_mem_U (hc' := hc) hxU]
    have hcW : (c : V) ∈ orthK h U := by
      rw [hcy]
      first
      | exact Submodule.projection_apply_mem _ _ _ _
      | exact Submodule.projection_apply_mem _ _ _
      | exact Submodule.projection_apply_mem _ _
      | (unfold prO; simp)
    have hcO : ∀ u ∈ U, h u (c : V) = 0 := by
      intro u hu
      simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hcW
      exact hcW u hu
    have hcΛ : (c : V) ∈ Λ₀ := by
      rw [← hd₀]
      intro z hz
      have hzW := hG₀.iW z hz
      obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _
        (P (Submodule.Quotient.mk (⟨prO hc.symm z, hzW⟩ : ↥(locF 𝔭 (dualIn h (orthK h U) T)))))
      have h2 := hP ⟨prO hc.symm z, hzW⟩ c d 0 hd (by rw [Submodule.Quotient.mk_zero]; exact hPb)
      have e : h z (c : V) =
          -(h (d : V) (((0 : ↥(locF 𝔭 (dualIn h (orthK h U) T))) : V)) - h (prO hc.symm z) (c : V)) := by
        have e1 : h z (c : V) = h (prO hc z) (c : V) + h (prO hc.symm z) (c : V) := by
          conv_lhs => rw [← prO_add hc z]
          rw [map_add, LinearMap.add_apply]
        rw [e1, hcO (prO hc z) ?_]
        · simp
        · first
      | exact Submodule.projection_apply_mem _ _ _ _
      | exact Submodule.projection_apply_mem _ _ _
      | exact Submodule.projection_apply_mem _ _
      | (unfold prO; simp)
      rw [e]
      exact Submodule.neg_mem _ h2
    have hxΛ : x ∈ Λ₀ := by
      have e := prO_add hc y
      rw [hxy, ← hcy] at e
      have ex : x = y - (c : V) := eq_sub_of_add_eq e
      rw [ex]
      exact Λ₀.sub_mem hy hcΛ
    rw [← hG₀.cU]
    exact Submodule.mem_inf.2 ⟨hxΛ, hxU⟩
  · intro hx
    have hxΛU : x ∈ Λ₀ ⊓ U.restrictScalars (𝓞 K) := by
      rw [hG₀.cU]
      exact hx
    obtain ⟨hxΛ, hxU⟩ := Submodule.mem_inf.1 hxΛU
    have hxU' : x ∈ U := hxU
    have hps : prO hc.symm x = 0 := prO_symm_of_mem_U (hc' := hc) hxU'
    have hmem : prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T) := hG₀.iW x hxΛ
    refine ⟨⟨0, Submodule.coe_zero.trans hps.symm, x, hxΛ, ⟨prO hc.symm x, hmem⟩, rfl, rfl, ?_⟩, hxU'⟩
    have hz : (⟨prO hc.symm x, hmem⟩ : ↥(locF 𝔭 (dualIn h (orthK h U) T))) = 0 := Subtype.ext hps
    rw [hz, Submodule.Quotient.mk_zero, map_zero]

theorem glue_inf_orthK_eq_locF (hG₀ : Good hc M T 𝔭 Λ₀) :
    glue hc T 𝔭 Λ₀ P ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T := by
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨b, hb, y, hy, c, hcy, hU, hP⟩, hxW⟩
    have hx0 : prO hc x = 0 := orth_projection_of_mem_compl (hc' := hc) hxW
    have hxb : (b : V) = x := by rw [hb, orth_projection_symm_of_mem (hc' := hc) hxW]
    have hyc : (c : V) = y := by
      rw [hcy]
      have e := prO_add hc y
      rw [hU, hx0, zero_add] at e
      exact e
    have hyW : y ∈ orthK h U := by
      rw [← hyc, hcy]
      first
      | exact Submodule.projection_apply_mem _ _ _ _
      | exact Submodule.projection_apply_mem _ _ _
      | exact Submodule.projection_apply_mem _ _
      | (unfold prO; simp)
    have hyT : y ∈ locF 𝔭 T := by
      rw [← hG₀.cW]
      exact Submodule.mem_inf.2 ⟨hy, hyW⟩
    have hc0 : (Submodule.Quotient.mk c : DiscMod h (orthK h U) T 𝔭) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.mem_comap.2 (by rw [Submodule.subtype_apply, hyc]; exact hyT))
    rw [hc0, map_zero] at hP
    have hb' := Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 hP)
    rw [Submodule.subtype_apply, hxb] at hb'
    exact hb'
  · intro hx
    have hxΛW : x ∈ Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) := by
      rw [hG₀.cW]
      exact hx
    obtain ⟨hxΛ, hxW⟩ := Submodule.mem_inf.1 hxΛW
    have hxW' : x ∈ orthK h U := hxW
    have hps : prO hc.symm x = x := orth_projection_symm_of_mem (hc' := hc) hxW'
    have hmem : prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T) := hG₀.iW x hxΛ
    refine ⟨⟨⟨prO hc.symm x, hmem⟩, rfl, x, hxΛ, ⟨prO hc.symm x, hmem⟩, rfl, rfl, ?_⟩, hxW'⟩
    have hc0 : (Submodule.Quotient.mk (⟨prO hc.symm x, hmem⟩ : ↥(locF 𝔭 (dualIn h (orthK h U) T))) :
        DiscMod h (orthK h U) T 𝔭) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.mem_comap.2 (by rw [hps] at hmem ⊢; exact hx : prO hc.symm x ∈ locF 𝔭 T))
    rw [hc0, map_zero]

theorem glue_int (hs : h.IsSymm) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hP : FP P) {a b : V}
    (ha : a ∈ glue hc T 𝔭 Λ₀ P) (hb : b ∈ glue hc T 𝔭 Λ₀ P) :
    h a b ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  obtain ⟨ba, hba, ya, hya, ca, hca, hUa, hPa⟩ := ha
  obtain ⟨bb, hbb, yb, hyb, cb, hcb, hUb, hPb⟩ := hb
  rw [split hs hc a b, ← hUa, ← hUb, ← hba, ← hbb]
  have hy : h (prO hc ya) (prO hc yb) = h ya yb - h ca cb := by
    rw [split hs hc ya yb, ← hca, ← hcb]
    ring
  rw [hy]
  have h1 : h ya yb ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    have hmemd : yb ∈ dualF h 𝔭 Λ₀ := by
      rw [hd₀]
      exact hyb
    exact hmemd ya hya
  have h2 := hP ca cb ba bb hPa hPb
  have e : h ya yb - h ca cb + h ba bb = h ya yb + (h ba bb - h ca cb) := by ring
  rw [e]
  exact Submodule.add_mem _ h1 h2

theorem glue_le_dual (hs : h.IsSymm) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hP : FP P) :
    glue hc T 𝔭 Λ₀ P ≤ dualF h 𝔭 (glue hc T 𝔭 Λ₀ P) := by
  intro x hx y hy
  exact glue_int hs hd₀ hP hy hx

theorem dual_le_glue (hs : h.IsSymm) (hG₀ : Good hc M T 𝔭 Λ₀) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀)
    (hM : IsLatIn U M) (hT : IsLatIn (orthK h U) T) (hP : FP P) (hsurj : Function.Surjective P) :
    dualF h 𝔭 (glue hc T 𝔭 Λ₀ P) ≤ glue hc T 𝔭 Λ₀ P := by
  intro x hx
  have hx' : ∀ z ∈ glue hc T 𝔭 Λ₀ P, h z x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := hx
  have hLM : locF 𝔭 M ≤ glue hc T 𝔭 Λ₀ P := by
    intro m hm
    rw [← glue_inf_U hG₀ hd₀ hP] at hm
    exact hm.1
  have hLT : locF 𝔭 T ≤ glue hc T 𝔭 Λ₀ P := by
    intro m hm
    rw [← glue_inf_orthK_eq_locF (P := P) hG₀] at hm
    exact hm.1
  have hxU : prO hc x ∈ locF 𝔭 (dualIn h U M) := by
    apply mem_locF_dualIn hM.1 𝔭 (prO_mem hc x)
    intro m hm
    have hmU := le_of_isLatIn hM m hm
    have e : h m x = h m (prO hc x) + h m (prO hc.symm x) := by rw [← map_add, prO_add]
    rw [h_UW hmU (prO_symm_mem hc x), add_zero] at e
    rw [← e]
    exact hx' m (hLM (LocF.le_locF 𝔭 M hm))
  have hxW : prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T) := by
    apply mem_locF_dualIn hT.1 𝔭 (prO_symm_mem hc x)
    intro m hm
    have hmW := le_of_isLatIn hT m hm
    have e : h m x = h m (prO hc x) + h m (prO hc.symm x) := by rw [← map_add, prO_add]
    rw [h_WU hs hmW (prO_mem hc x), zero_add] at e
    rw [← e]
    exact hx' m (hLT (LocF.le_locF 𝔭 T hm))
  obtain ⟨y, hy, hyU⟩ := hG₀.oU _ hxU
  obtain ⟨x'', hx''⟩ := Submodule.Quotient.mk_surjective _
    (P (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩))
  have hz := mem_glue_of hG₀ hy x'' hx''
  have hx''W := memW hG₀ x''.2
  have hdW : prO hc.symm x - (x'' : V) ∈ orthK h U := (orthK h U).sub_mem (prO_symm_mem hc x) hx''W
  have hdx : prO hc.symm x - (x'' : V) = x - (prO hc y + x'') := by
    calc prO hc.symm x - (x'' : V) = (prO hc x + prO hc.symm x) - (prO hc x + x'') := by abel
      _ = _ := by rw [prO_add, hyU]
  have hdT : prO hc.symm x - (x'' : V) ∈ locF 𝔭 T := by
    apply mem_T_of hG₀ hd₀ hdW
    intro b' hb'
    obtain ⟨e, he⟩ := hsurj (Submodule.Quotient.mk ⟨b', hb'⟩)
    induction e using Submodule.Quotient.induction_on with
    | H e₀ =>
      obtain ⟨y₁, hy₁, he₀⟩ := hG₀.oW e₀ e₀.2
      have hz₁ : prO hc y₁ + b' ∈ glue hc T 𝔭 Λ₀ P := by
        refine mem_glue_of hG₀ hy₁ ⟨b', hb'⟩ ?_
        rw [← he]
        congr 2
        exact Subtype.ext he₀.symm
      have h1 := hx' _ hz₁
      have h2 := glue_int hs hd₀ hP hz₁ hz
      have := sub_mem h1 h2
      rw [← map_sub, ← hdx, map_add, LinearMap.add_apply, h_UW (prO_mem hc y₁) hdW, zero_add] at this
      exact this
  refine ⟨⟨prO hc.symm x, hxW⟩, rfl, y, hy, ⟨prO hc.symm y, hG₀.iW y hy⟩, rfl, hyU, ?_⟩
  rw [← hx'']
  exact (mk_eq_iff _ _).2 hdT

end Formalism.L2.SG.Pf.OrthogonalProjections
