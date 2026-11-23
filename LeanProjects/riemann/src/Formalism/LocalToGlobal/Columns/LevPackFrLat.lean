import Formalism.LocalToGlobal.Columns.JointLevelFrameZero
import Formalism.LocalToGlobal.Columns.RecLevelLocF

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

theorem th_fLoc_pi (h : BasePi ST π) (a : Formalism.BasicNotions.intV E v)
    (ha : (a : E ⊗[F] v.adicCompletion F) = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π)) (m : fMod hc n ST v) :
    a • m = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
  show a • fLoc hc n ST v x = 0
  rw [← map_smul, rll_fLoc_eq_zero, rll_baseKer_eq n h, rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)]
  have hx : x.1 ∈ Formalism.L2.Herm.locL v (rll_dLat n (star (algebraMap (𝓞 E) E π))) := by
    rw [← rll_dualV_eq hc n v h]; exact x.2
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hx
  refine ⟨fun i hi => mul_mem a.2 (hx.1 i hi), ?_⟩
  show inclE (F := F) (v.adicCompletion F) (star (algebraMap (𝓞 E) E π) / algebraMap (𝓞 E) E π) *
    ((a : E ⊗[F] v.adicCompletion F) * x.1 (lastIdx n)) ∈ Formalism.BasicNotions.intV E v
  rw [ha, rll_cp_mul v h]
  exact hx.2

end Loc

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) (hK : LocalLevelIsKOneAtT hc u Λ)

theorem levPack_fM_pi (H : HCrd Pr n fun c => (s c).1.L) (v : HeightOneSpectrum (𝓞 X.F)) (hv : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal)
    (a : intV X.E v) (ha : (a : X.E ⊗[X.F] v.adicCompletion X.F) = inclE (F := X.F) (v.adicCompletion X.F) (Pr.piT u : X.E))
    (m : (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.fM v hv) : a • m = 0 := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact th_fLoc_pi hc _ v (basePi_of_ok hX hPr u) a ha m

theorem levPack_frLat (S : GSplit (Pr := Pr) hc) (H : HCrd Pr n fun c => (s c).1.L) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F))
    (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) (t : Fin H.n' → v.adicCompletion X.F) :
    (∃ x ∈ Formalism.L2.Herm.locL v (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb, ∀ b, (S.sp i v h (x b)).1 = t b) ↔
      ∀ b, (((1 : GL (Fin H.n') (v.adicCompletion X.F))⁻¹ : GL (Fin H.n') (v.adicCompletion X.F)) :
        Matrix (Fin H.n') (Fin H.n') (v.adicCompletion X.F)).mulVec t b ∈ v.adicCompletionIntegers X.F := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  refine gco_fr_lat _ (Pr.vT u) v (S.sp i v h) (S.sp_alg i v h) ?_ t
  intro hT
  have h1 : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal :=
    (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).1 hT
  exact rls_T_notUnder hPr u v h1 ((th_plUnder_vGs hc hPr v).2 (by fin_cases i; exact Or.inl h; exact Or.inr h))

end Gen

end Formalism.L2.Col
