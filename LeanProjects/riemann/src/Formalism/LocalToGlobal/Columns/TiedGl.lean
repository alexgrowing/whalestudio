import Formalism.LocalToGlobal.Columns.TiedGlPl
import Formalism.LocalToGlobal.Columns.TiedGlLev

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM InJ)

section Prod

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)

include hc hPr in
theorem glk_under_mem (i : Fin 2) {w : Pl X.E} (hw : w ∈ Pr.vG i) : (Pr.g i : 𝓞 X.F) ∈ (underPl X.F w).asIdeal :=
  (glk_under hc hPr i _).1 ⟨w, hw, rfl⟩

theorem glk_gwOf_under (i : Fin 2) {w : Pl X.E} (hw : w ∈ Pr.vG i) :
    gwOf hc hPr i (underPl X.F w) (glk_under_mem hc hPr i hw) = ⟨w, glk_vG_le i hw⟩ :=
  (gwOf_uniq hc hPr i (underPl X.F w) (glk_under_mem hc hPr i hw) ⟨w, glk_vG_le i hw⟩
    (show (underPl X.F w).asIdeal = _ from rfl)).symm

open Classical in
theorem glk_prod_i (A : Pr.vGs → ℂ) (i : Fin 2) :
    ∏ w ∈ Pr.vG i, (if h : w ∈ Pr.vGs then A ⟨w, h⟩ else 1) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal), A (gwOf hc hPr i v h) := by
  have h1 : ∀ v : HeightOneSpectrum (𝓞 X.F), (∏ᶠ (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal), A (gwOf hc hPr i v h)) =
      if h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal then A (gwOf hc hPr i v h) else 1 := fun v => finprod_eq_dif _
  rw [finprod_congr h1]
  rw [finprod_eq_prod_of_mulSupport_subset (s := (Pr.vG i).image (underPl X.F))]
  · rw [Finset.prod_image]
    · refine Finset.prod_congr rfl fun w hw => ?_
      rw [dif_pos (glk_vG_le i hw), dif_pos (glk_under_mem hc hPr i hw), glk_gwOf_under hc hPr i hw]
    · intro w hw w' hw' e
      have e1 := glk_gwOf_under hc hPr i hw
      have e2 := glk_gwOf_under hc hPr i hw'
      have e3 : gwOf hc hPr i (underPl X.F w) (glk_under_mem hc hPr i hw) =
          gwOf hc hPr i (underPl X.F w') (glk_under_mem hc hPr i hw') := by
        congr 1
      rw [e1, e2] at e3
      exact congrArg Subtype.val e3
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    have hp : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := by
      by_contra hn
      exact hv (dif_neg hn)
    rw [Finset.coe_image]
    refine ⟨(gwOf hc hPr i v hp).1, gwOf_mem hc hPr i v hp, ?_⟩
    exact HeightOneSpectrum.ext (gwOf_over hc hPr i v hp).symm

theorem glk_prod (A : Pr.vGs → ℂ) :
    ∏ w : Pr.vGs, A w =
      ∏ i : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal), A (gwOf hc hPr i v h) := by
  classical
  have h0 : ∏ w : Pr.vGs, A w = ∏ w ∈ Pr.vGs, (if h : w ∈ Pr.vGs then A ⟨w, h⟩ else 1) := by
    rw [← Finset.prod_coe_sort Pr.vGs]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [dif_pos w.2]
  have hd : Disjoint (Pr.vG 0) (Pr.vG 1) := by
    rw [Finset.disjoint_left]
    intro w h0 h1
    exact hPr.g_ne ((hPr.vG_norm 0 w h0).symm.trans (hPr.vG_norm 1 w h1))
  rw [h0, Fin.prod_univ_two, ← glk_prod_i hc hPr A 0, ← glk_prod_i hc hPr A 1]
  unfold Primes.vGs
  convert Finset.prod_union hd using 2

end Prod

section GLc

variable {X : Fields} {Pr : Primes X} {hc : Formalism.BasicNotions.CMData X.F X.E} (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ)

def tieGLoc (hCh : Ch.Ok) : Formalism.L2.Forms.GLoc X.F X.E hc.sig Pr.g where
  sp := S.sp
  sp_sig := S.sp_sig
  sp_alg := S.sp_alg
  piG := Pr.piG
  piG_norm i := by
    have := congrArg (algebraMap (𝓞 X.E) X.E) (hPr.piG_norm i)
    rw [map_mul, map_natCast] at this
    exact this
  sp_pi := S.sp_pi
  psi0 i v h := glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h))
  psi_zero_nontrivial_character i v h := by
    intro h1
    apply hCh.psi_zero_nontrivial_character (gwOf hc hPr i v h)
    ext x
    have h2 := DFunLike.congr_fun h1 (S.eK hPr i v h x)
    rw [glmPsi_apply, AddChar.one_apply] at h2
    rw [AddChar.one_apply]
    exact σ₀.injective (h2.trans (map_one σ₀).symm)
  chiB i v h s := glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)

end GLc

end Formalism.L2.Col
