import Formalism.LocalToGlobal.Columns.TiedUpDnA

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG
open Formalism.L2.DIV (Pl)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

theorem tud_lat_move (γ : URat hc n) (g₀ : UF E n × H) (hγ : ratHom hc n γ = g₀.1) (d' d₁ : DecoSet E n ST SG)
    (hg₀ : g₀ • d' = d₁) (P : ST) :
    Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.L = d₁.1.L ∧
      Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.Lsh = d₁.1.Lsh ∧
      ∀ y, d'.1.f P y = d₁.1.f P (((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y) := by
  subst hg₀
  have hm : ∀ L : Submodule (𝓞 E) (Sp E n), Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) L =
      gmap ((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n) L := by
    intro L
    unfold Formalism.L2.Forms.mulLat gmap
    congr 1
    apply LinearMap.ext
    intro y
    show _ = ((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n) y
    rw [← hγ]
    exact (rlc_ratHom_apply hc n γ y).symm
  refine ⟨by rw [hm, rlc_smul_val, Deco.L_act], by rw [hm, rlc_smul_val, Deco.Lsh_act _ g₀.1.2], fun y => ?_⟩
  show d'.1.f P y = d'.1.f P (((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n).symm (((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y))
  rw [← hγ, ← rlc_ratHom_apply, LinearEquiv.symm_apply_apply]

omit [Algebra F E] in
theorem tud_f_rep (d : DecoSet E n ST SG) (P : ST) {x : d.lv P} (hx : d.fv P x = 1) : d.1.f P (modP.rep x) = 1 := by
  rw [← d.fv_mk P ⟨modP.rep x, modP.rep_mem x⟩, modP.mk_rep, hx]

theorem tud_up_core (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG E ST) {v : HeightOneSpectrum (𝓞 F)} (d d' : DecoSet E n ST SG)
    (P : ST) (hov : IsOver v P.1) (hP : MoveHyp ST SG P) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2)
    {a : 𝓞 E} (ha : SepElt ST a) (x : d.lv P) (hx : d.fv P x = 1) (g₀ : UF E n × H) (hg₀ : g₀ • d' = d.upL P q x) :
    ∃ (γ : URat hc n) (η : UAd hc n) (κ : levU hc n ST SG H), ratHom hc n γ = g₀.1 ∧ levRed hc n ST SG H κ = g₀.2 ∧
      (∀ v', v' ≠ v → bc (prV (E := E) v') (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
      bc (iA F E) (γ : GL (Fin n) E) * (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (ptOfD hc n ST SG c₀ d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * η * κ ∧
      localization₂ P.1.asIdeal (Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.L) = localization₂ P.1.asIdeal d.1.Lsh ∧
      (∀ {w : Sp E n} {t : 𝓞 E}, t ∉ P.1.asIdeal → w ∈ d.1.Lsh → modP.rep x - t • w ∈ P.1.asIdeal • d.1.N →
        localization₂ P.1.asIdeal (Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.Lsh) =
          localization₂ P.1.asIdeal (d.1.Lsh ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • w})) ∧
      ∀ y ∈ d'.1.Lsh, d'.1.f P y = d.1.f P (q • (((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y)) := by
  have hfr := tud_f_rep n ST SG d P hx
  have hd₁ : (d.upL P q x).1 = d.1.up P q (modP.rep x) := d.up_val P hP hq hq2 (modP.rep_mem x) hfr
  have hSO := tud_sameOff_up hc d P hP hq hq2 hov (modP.rep_mem x) hfr
  obtain ⟨γ, η, κ, hγ, hκ, hη, e⟩ := updn_move hc n ST SG H hS c₀ v d (d.upL P q x) d' hSO g₀ hg₀
  obtain ⟨hL, hLs, hf⟩ := tud_lat_move hc n ST SG H γ g₀ hγ d' _ hg₀ P
  refine ⟨γ, η, κ, hγ, hκ, hη, e, ?_, ?_, ?_⟩
  · rw [hL, tud_locP_L ha, DecoSet.locP_LshKer_up hP hq hq2 ha (d.upL_mem P hP hq hq2 hx) P]
  · intro w t ht hw hrw
    rw [hLs, (d.upL P q x).2.locP_Lsh ha P, show (d.upL P q x).1.N = upN P.1.asIdeal d.1.N (modP.rep x) from
      congrArg Deco.N hd₁, localizationAt_upN d.2.lat d.2.uni P.1 hP.ne (modP.rep_mem x)]
    exact localizationAt_upA hq hq2 d.2.N_le_Lsh (by rw [← d.2.locP_Lsh ha P]; exact le_locP _ _) hw ht hrw
  · intro y hy
    have hy1 : ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y ∈ (d.upL P q x).1.Lsh := by
      rw [← hLs]; exact Submodule.mem_map_of_mem hy
    have hy2 := (d.upL P q x).2.Lsh_le_at ha P hy1
    rw [hf y, hd₁, Deco.up_f, if_pos]
    rw [hd₁] at hy2
    exact hy2

theorem tud_dn_core (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG E ST) {v : HeightOneSpectrum (𝓞 F)} (d d' : DecoSet E n ST SG)
    (P : ST) (hov : IsOver v P.1) (hP : MoveHyp ST SG P) {a : 𝓞 E} (ha : SepElt ST a)
    (g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (d.lk P)) (hg : g ≠ 0) (g₀ : UF E n × H) (hg₀ : g₀ • d' = d.dnL P g) :
    ∃ (γ : URat hc n) (η : UAd hc n) (κ : levU hc n ST SG H), ratHom hc n γ = g₀.1 ∧ levRed hc n ST SG H κ = g₀.2 ∧
      (∀ v', v' ≠ v → bc (prV (E := E) v') (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
      bc (iA F E) (γ : GL (Fin n) E) * (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (ptOfD hc n ST SG c₀ d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * η * κ ∧
      localization₂ P.1.asIdeal (Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.Lsh) = localization₂ P.1.asIdeal d.1.L ∧
      ∀ y, d'.1.f P y = modP.ext P.1 (d.1.kerAt P) g (((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y) := by
  classical
  have hd₁ := d.dnL_val P hP hg
  have hSO := tud_sameOff_dn hc d P hP hg hov
  obtain ⟨γ, η, κ, hγ, hκ, hη, e⟩ := updn_move hc n ST SG H hS c₀ v d (d.dnL P g) d' hSO g₀ hg₀
  obtain ⟨-, hLs, hf⟩ := tud_lat_move hc n ST SG H γ g₀ hγ d' _ hg₀ P
  refine ⟨γ, η, κ, hγ, hκ, hη, e, ?_, fun y => ?_⟩
  · rw [hLs, (d.dnL P g).2.locP_Lsh ha P, show (d.dnL P g).1.N = d.1.dnN P from congrArg Deco.N hd₁,
      (d.2.dnN_spec P hP.ne).2.2.2, ← d.2.locP_LshKer_self ha P, tud_locP_L ha]
  · rw [hf y, hd₁]
    show Function.update d.1.f P _ P _ = _
    rw [Function.update_self]

end Formalism.L2.Col
