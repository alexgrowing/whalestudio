import Formalism.LocalToGlobal.Columns.TiedUpDn
import Formalism.LocalToGlobal.Columns.LocalLevelIsKOneAtT
import Formalism.LocalToGlobal.Columns.TiedMvA

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem tam_locP_L_off {d : Deco E n ST SG} (hd : d.Ok) (Q : HeightOneSpectrum (𝓞 E)) (hQ : Q ∉ ST) :
    localization₂ Q.asIdeal d.L = localization₂ Q.asIdeal d.N := by
  classical
  have hex : ∀ P : ST, ∃ a ∈ P.1.asIdeal, a ∉ Q.asIdeal := fun P =>
    exists_mem_notMem (P := P.1) (Q := Q) fun e => hQ (e ▸ P.2)
  choose a ha ha' using hex
  refine le_antisymm (localizationAt_mono Q hd.L_le_N) (localization_le_of_smul_mem (a := ∏ P : ST, a P) ?_ fun x hx =>
    hd.smul_N_mem_L (fun P => Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a (Finset.mem_univ P)) (ha P)) hx)
  intro h
  obtain ⟨P, -, hP⟩ := (Ideal.IsPrime.prod_mem_iff (hp := Q.isPrime)).1 h
  exact ha' P hP

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem tam_locP_L_same {v : HeightOneSpectrum (𝓞 F)} {d d₁ : Deco E n ST SG} (hd : d.Ok) (hd₁ : d₁.Ok)
    (h : Deco.SameOff ST SG v d d₁) (Q : HeightOneSpectrum (𝓞 E)) (hQ : ¬ IsOver v Q) :
    localization₂ Q.asIdeal d.L = localization₂ Q.asIdeal d₁.L := by
  by_cases hS : Q ∈ ST
  · ext x
    rw [hd.mem_locP_L ⟨Q, hS⟩, hd₁.mem_locP_L ⟨Q, hS⟩, h.f ⟨Q, hS⟩ hQ]
    show x ∈ localization₂ Q.asIdeal d.N ∧ _ ↔ x ∈ localization₂ Q.asIdeal d₁.N ∧ _
    rw [h.N Q hQ]
  · rw [tam_locP_L_off hd Q hS, tam_locP_L_off hd₁ Q hS, h.N Q hQ]

omit [StarRing E] in
theorem localizationAt_congr (I : Ideal (𝓞 E)) [I.IsPrime] {A B : Submodule (𝓞 E) (Fin n → E)} (e : A = B) : localization₂ I A = localization₂ I B := by
  rw [e]

theorem SameOffC.congr_right {I : Ideal (𝓞 E)} {A B B' : Submodule (𝓞 E) (Fin n → E)} (h : SameOffC I A B) (e : B' = B) :
    SameOffC I A B' := e ▸ h

theorem tam_sameOffC (hc : Formalism.BasicNotions.CMData F E) {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} (hov : IsOver v P)
    {A B : Submodule (𝓞 E) (Fin n → E)} (h : ∀ Q : HeightOneSpectrum (𝓞 E), ¬ IsOver v Q → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B)
    (I : Ideal (𝓞 E)) (hI : I = P.asIdeal) : SameOffC I A B := by
  subst hI
  intro q hq h1 h2
  have hb : q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hq (RingOfIntegers.not_isField E)
  refine h ⟨q, hq.isPrime, hb⟩ fun hQ => ?_
  rcases rll_over_cases hc hov hQ with e | e
  · exact h1 (congrArg HeightOneSpectrum.asIdeal e)
  · exact h2 ((congrArg HeightOneSpectrum.asIdeal e).trans (conjIdeal_asIdeal P).symm)

end Lat

section Move

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

omit [NeZero n] in

theorem tam_ufGL_mem (g : UF E n) : ufGL E n g ∈ URat hc n := by
  obtain ⟨γ, rfl⟩ := (ratHom_bijective hc n).2 g
  rw [tud_ufGL_ratHom]
  exact γ.2

omit [NeZero n] in
theorem tam_ratHom (g : UF E n) : ratHom hc n ⟨ufGL E n g, tam_ufGL_mem hc n g⟩ = g := by
  obtain ⟨γ, rfl⟩ := (ratHom_bijective hc n).2 g
  congr 1
  exact Subtype.ext (tud_ufGL_ratHom hc n γ)

include hc in

theorem tam_lat_move (g₀ : UF E n × H) (d' d₁ : DecoSet E n ST SG) (hg₀ : g₀ • d' = d₁) :
    Formalism.L2.Forms.mulLat ((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.L = d₁.1.L ∧
      Formalism.L2.Forms.mulLat ((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.Lsh = d₁.1.Lsh ∧
      ∀ (P : ST) y, d'.1.f P y = d₁.1.f P (((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y) := by
  subst hg₀
  have hap : ∀ y, ((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y = ((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n) y := by
    intro y
    have h1 := rlc_ratHom_apply hc n ⟨ufGL E n g₀.1, tam_ufGL_mem hc n g₀.1⟩ y
    rw [tam_ratHom] at h1
    exact h1.symm
  have hm : ∀ L : Submodule (𝓞 E) (Sp E n), Formalism.L2.Forms.mulLat ((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) L =
      gmap ((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n) L := by
    intro L
    unfold Formalism.L2.Forms.mulLat gmap
    congr 1
    apply LinearMap.ext
    intro y
    exact hap y
  refine ⟨by rw [hm, rlc_smul_val, Deco.L_act], by rw [hm, rlc_smul_val, Deco.Lsh_act _ g₀.1.2], fun P y => ?_⟩
  show d'.1.f P y = d'.1.f P (((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n).symm (((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y))
  rw [hap, LinearEquiv.symm_apply_apply]

theorem tam_move (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG E ST) (v : HeightOneSpectrum (𝓞 F)) (d d₁ d' : DecoSet E n ST SG)
    (h : Deco.SameOff ST SG v d.1 d₁.1) (g₀ : UF E n × H) (hg₀ : g₀ • d' = d₁) :
    Formalism.L2.Herm.AdStep hc.sig (1 : Matrix (Fin n) (Fin n) E) (levU hc n ST SG H)
      (ptOfD hc n ST SG c₀ d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
      (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (ufGL E n g₀.1) v := by
  obtain ⟨γ, η, κ, hγ, -, hη, e⟩ := updn_move hc n ST SG H hS c₀ v d d₁ d' h g₀ hg₀
  rw [← hγ, tud_ufGL_ratHom]
  exact ⟨κ.1, κ.2, η.1, η.2, hη, e⟩

theorem tam_sameOff_dia (d : DecoSet E n ST SG) (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) {v : HeightOneSpectrum (𝓞 F)}
    (hov : IsOver v P.1) : Deco.SameOff ST SG v d.1 (d.dia1 P a).1 := by
  classical
  refine ⟨fun _ _ => rfl, fun Q hQ => ?_, fun _ _ => rfl⟩
  funext x
  show d.1.f Q x = ((Pi.mulSingle P a : DiaG E ST) Q).1 * d.1.f Q x
  rw [Pi.mulSingle_eq_of_ne (fun e => hQ (by rw [e]; exact hov)), Units.val_one, one_mul]

end Move

section Moved

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG : Finset (Pl E)}

include hc in

theorem tam_upL {v : HeightOneSpectrum (𝓞 F)} (d : DecoSet E n ST SG) (P : ST) (hov : IsOver v P.1) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {a : 𝓞 E} (ha : SepElt ST a) (x : d.lv P) (hx : d.fv P x = 1) :
    Deco.SameOff ST SG v d.1 (d.upL P q x).1 ∧
      localization₂ P.1.asIdeal (d.upL P q x).1.L = localization₂ P.1.asIdeal d.1.Lsh ∧
      (∀ {w : Sp E n} {t : 𝓞 E}, t ∉ P.1.asIdeal → w ∈ d.1.Lsh → modP.rep x - t • w ∈ P.1.asIdeal • d.1.N →
        localization₂ P.1.asIdeal (d.upL P q x).1.Lsh =
          localization₂ P.1.asIdeal (d.1.Lsh ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • w})) ∧
      (∀ y ∈ (d.upL P q x).1.Lsh, (d.upL P q x).1.f P y = d.1.f P (q • y)) ∧
      ∀ P' : ST, P' ≠ P → (d.upL P q x).1.f P' = d.1.f P' := by
  have hfr := tud_f_rep n ST SG d P hx
  have hd₁ : (d.upL P q x).1 = d.1.up P q (modP.rep x) := d.up_val P hP hq hq2 (modP.rep_mem x) hfr
  have hSO := tud_sameOff_up hc d P hP hq hq2 hov (modP.rep_mem x) hfr
  refine ⟨hSO, ?_, ?_, ?_, ?_⟩
  · rw [tud_locP_L ha, DecoSet.locP_LshKer_up hP hq hq2 ha (d.upL_mem P hP hq hq2 hx) P]
  · intro w t ht hw hrw
    rw [(d.upL P q x).2.locP_Lsh ha P, show (d.upL P q x).1.N = upN P.1.asIdeal d.1.N (modP.rep x) from
      congrArg Deco.N hd₁, localizationAt_upN d.2.lat d.2.uni P.1 hP.ne (modP.rep_mem x)]
    exact localizationAt_upA hq hq2 d.2.N_le_Lsh (by rw [← d.2.locP_Lsh ha P]; exact le_locP _ _) hw ht hrw
  · intro y hy
    have hy2 := (d.upL P q x).2.Lsh_le_at ha P hy
    rw [hd₁, Deco.up_f, if_pos]
    rw [hd₁] at hy2
    exact hy2
  · intro P' hP'
    rw [hd₁]
    exact Deco.up_f_ne d.1 P q _ hP'

include hc in

theorem tam_dnL {v : HeightOneSpectrum (𝓞 F)} (d : DecoSet E n ST SG) (P : ST) (hov : IsOver v P.1) (hP : MoveHyp ST SG P)
    {a : 𝓞 E} (ha : SepElt ST a) (g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (d.lk P)) (hg : g ≠ 0) :
    Deco.SameOff ST SG v d.1 (d.dnL P g).1 ∧
      localization₂ P.1.asIdeal (d.dnL P g).1.Lsh = localization₂ P.1.asIdeal d.1.L ∧
      (∀ y, (d.dnL P g).1.f P y = modP.ext P.1 (d.1.kerAt P) g y) ∧
      ∀ P' : ST, P' ≠ P → (d.dnL P g).1.f P' = d.1.f P' := by
  classical
  have hd₁ := d.dnL_val P hP hg
  refine ⟨tud_sameOff_dn hc d P hP hg hov, ?_, fun y => ?_, fun P' hP' => ?_⟩
  · rw [(d.dnL P g).2.locP_Lsh ha P, show (d.dnL P g).1.N = d.1.dnN P from congrArg Deco.N hd₁,
      (d.2.dnN_spec P hP.ne).2.2.2, ← d.2.locP_LshKer_self ha P, tud_locP_L ha]
  · rw [hd₁]
    show Function.update d.1.f P _ P _ = _
    rw [Function.update_self]
  · rw [hd₁]
    show Function.update d.1.f P _ P' = _
    rw [Function.update_of_ne hP']

omit [NeZero n] in

theorem tam_diaL (d : DecoSet E n ST SG) (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) :
    (d.dia1 P a).1.L = d.1.L ∧ (∀ y, (d.dia1 P a).1.f P y = a.1 * d.1.f P y) ∧
      ∀ P' : ST, P' ≠ P → (d.dia1 P a).1.f P' = d.1.f P' := by
  classical
  refine ⟨Deco.L_dia _ _, fun y => ?_, fun P' hP' => ?_⟩
  · show ((Pi.mulSingle P a : DiaG E ST) P).1 * d.1.f P y = _
    rw [Pi.mulSingle_eq_same]
  · funext y
    show ((Pi.mulSingle P a : DiaG E ST) P').1 * d.1.f P' y = _
    rw [Pi.mulSingle_eq_of_ne hP', Units.val_one, one_mul]

end Moved

section Crd

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) {σ₀ : X.K →+* ℂ} {n : ℕ} {cls : Type}
  {L : cls → Submodule (𝓞 X.E) (Fin n → X.E)}

def tamG (Q : StepCrd Pr σ₀ n L) (g : UF X.E n) : UJ (hc.sig : X.E →+* X.E) Q.J :=
  ⟨ufGL X.E n g, by rw [Q.hJ]; exact tam_ufGL_mem hc n g⟩

end Crd

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (i : ℕ)

abbrev tamDil (P : Pr.vT u) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (c : StCl W Λ u i) : StCl W Λ u i :=
  dilD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) P a c

abbrev tamMv (d₁ : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) : UF X.E (R.N i) := ((stepGSD W Λ u i).outSec.mv d₁).1

variable (Q : StepCrd Pr σ₀ (R.N i) fun c : StCl W Λ u i => (tudR W Λ u i c).1.L)

theorem tam_lat (d₁ : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) :
    Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i d₁)).1.1 (Q.lat (clsD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) d₁)) = d₁.1.L ∧
      Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i d₁)).1.1
        (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (clsD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) d₁))) = d₁.1.Lsh ∧
      ∀ (P : Pr.vT u) y, (tudR W Λ u i (clsD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) d₁)).1.f P y =
        d₁.1.f P ((tamG hc Q (tamMv W Λ u i d₁)).1.1 *ᵥ y) := by
  have hLd := tie_Ld_eq hc σ₀ u (tudR W Λ u i) Q (clsD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) d₁)
  rw [hLd, Q.hlat]
  exact tam_lat_move hc (R.N i) (Pr.vT u) Pr.vGs (Λ i).grp ((stepGSD W Λ u i).outSec.mv d₁) _ d₁ ((stepGSD W Λ u i).outSec.mv_smul d₁)

include hX in
set_option maxHeartbeats 1000000 in

theorem tam_up (P : Pr.vT u) (c : StCl W Λ u i) (z : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)))
    (hz : (tudR W Λ u i c).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z) = 1) :
    SameOffC (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
        (Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
          (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)))).1.1 (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z))) (Q.lat c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
                (Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
                  (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)))).1.1 (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z))) =
        Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)) ∧
      Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
                (Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
                  (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)))).1.1
                  (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) ⊔
          Submodule.span (𝓞 X.E) {((Pr.T u : ℕ) : X.E)⁻¹ • z.1}) ∧
      (∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z))))
        (hx : ((Pr.T u : ℕ) : 𝓞 X.E) • ((tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
          (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)))).1.1 *ᵥ x.1) ∈ dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tudUp W Λ hc hPr σ₀ u i Q P c z)).fv P
            (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P (tudUp W Λ hc hPr σ₀ u i Q P c z) x) =
          (tudR W Λ u i c).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c ⟨_, hx⟩)) ∧
      ∀ P' : Pr.vT u, P' ≠ P → ∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z))))
        (hx : (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
          (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)))).1.1 *ᵥ x.1 ∈ dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tudUp W Λ hc hPr σ₀ u i Q P c z)).fv P'
            (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' (tudUp W Λ hc hPr σ₀ u i Q P c z) x) =
          (tudR W Λ u i c).fv P' (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' c ⟨_, hx⟩) := by
  classical
  have ha := sepElt_of_ok hPr u
  have hP := moveHyp_of_ok hPr u P
  obtain ⟨hq, hq2⟩ := T_unif hX hPr u P
  have hLd := tie_Ld_eq hc σ₀ u (tudR W Λ u i) Q c
  have hLd' := tie_Ld_eq hc σ₀ u (tudR W Λ u i) Q (tudUp W Λ hc hPr σ₀ u i Q P c z)
  have hfv := tie_fv hc hPr σ₀ u (tudR W Λ u i) Q
  have hrz := tud_rep_pr hc hPr σ₀ u (tudR W Λ u i) Q P c z
  have hzL : z.1 ∈ (tudR W Λ u i c).1.Lsh := hLd ▸ z.2
  obtain ⟨hL, hLs, hf⟩ := tam_lat W Λ hc σ₀ u i Q ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
    (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z))
  obtain ⟨h1, h2, h3, h4, h5⟩ := tam_upL hc (tudR W Λ u i c) P (tieEV_over hc hX hPr u P) hP hq hq2 ha _ hz
  have h3' := h3 (tud_unit hPr u P) hzL hrz
  rw [map_natCast] at h3'
  have hlat : Q.lat c = (tudR W Λ u i c).1.L := congrFun Q.hlat c
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hL]
    exact (tam_sameOffC hc (tieEV_over hc hX hPr u P)
      (fun Q' hQ' => (tam_locP_L_same (tudR W Λ u i c).2 (Subtype.property _) h1 Q' hQ').symm) _ Ideal.mk_ker).congr_right hlat
  · simp only [Ideal.mk_ker]
    rw [hL]
    exact h2.trans (localizationAt_congr _ hLd.symm)
  · simp only [Ideal.mk_ker]
    rw [hLs]
    exact h3'.trans (localizationAt_congr _ (congrArg (· ⊔ Submodule.span (𝓞 X.E) {((Pr.T u : ℕ) : X.E)⁻¹ • z.1}) hLd.symm))
  · intro x hx
    rw [hfv, hfv, hf]
    exact h4 _ (hLs ▸ Submodule.mem_map_of_mem x.2)
  · intro P' hP' x hx
    rw [hfv, hfv, hf, h5 P' hP']

include hX in
set_option maxHeartbeats 1000000 in

theorem tam_dn (P : Pr.vT u) (c : StCl W Λ u i) (g : Module.Dual (𝓞 X.E ⧸ P.1.asIdeal) ((tudR W Λ u i c).lk P)) (hg : g ≠ 0) :
    SameOffC (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
        (Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dnL P g))).1.1 (Q.lat (tudDn W Λ u i P c g))) (Q.lat c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
                (Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dnL P g))).1.1
                  (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudDn W Λ u i P c g)))) =
        Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) (Q.lat c) ∧
      (∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudDn W Λ u i P c g))))
        (hx : (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dnL P g))).1.1 *ᵥ x.1 ∈
          Q.lat c ⊔ RingHom.ker (Ideal.Quotient.mk P.1.asIdeal) • dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tudDn W Λ u i P c g)).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P (tudDn W Λ u i P c g) x) =
          g (tiePrk hc hPr σ₀ u (tudR W Λ u i) Q P c (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) Ideal.mk_ker ⟨_, hx⟩)) ∧
      ∀ P' : Pr.vT u, P' ≠ P → ∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudDn W Λ u i P c g))))
        (hx : (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dnL P g))).1.1 *ᵥ x.1 ∈ dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tudDn W Λ u i P c g)).fv P' (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' (tudDn W Λ u i P c g) x) =
          (tudR W Λ u i c).fv P' (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' c ⟨_, hx⟩) := by
  classical
  have ha := sepElt_of_ok hPr u
  have hP := moveHyp_of_ok hPr u P
  have hfv := tie_fv hc hPr σ₀ u (tudR W Λ u i) Q
  have hprk := tud_prk hc hPr σ₀ u (tudR W Λ u i) Q P c _ Ideal.mk_ker g
  obtain ⟨hL, hLs, hf⟩ := tam_lat W Λ hc σ₀ u i Q ((tudR W Λ u i c).dnL P g)
  obtain ⟨h1, h2, h3, h5⟩ := tam_dnL hc (tudR W Λ u i c) P (tieEV_over hc hX hPr u P) hP ha g hg
  have hlat : Q.lat c = (tudR W Λ u i c).1.L := congrFun Q.hlat c
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hL]
    exact (tam_sameOffC hc (tieEV_over hc hX hPr u P)
      (fun Q' hQ' => (tam_locP_L_same (tudR W Λ u i c).2 (Subtype.property _) h1 Q' hQ').symm) _ Ideal.mk_ker).congr_right hlat
  · simp only [Ideal.mk_ker]
    rw [hLs]
    exact h2.trans (localizationAt_congr _ hlat.symm)
  · intro x hx
    rw [hfv, hprk, hf]
    exact h3 _
  · intro P' hP' x hx
    rw [hfv, hfv, hf, h5 P' hP']

theorem tam_dil (P : Pr.vT u) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (c : StCl W Λ u i) :
    Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dia1 P a))).1.1 (Q.lat (tamDil W Λ u i P a c)) = Q.lat c ∧
      (∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tamDil W Λ u i P a c))))
        (hx : (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dia1 P a))).1.1 *ᵥ x.1 ∈ dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tamDil W Λ u i P a c)).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P (tamDil W Λ u i P a c) x) =
          a.1 * (tudR W Λ u i c).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c ⟨_, hx⟩)) ∧
      ∀ P' : Pr.vT u, P' ≠ P → ∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tamDil W Λ u i P a c))))
        (hx : (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dia1 P a))).1.1 *ᵥ x.1 ∈ dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tamDil W Λ u i P a c)).fv P' (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' (tamDil W Λ u i P a c) x) =
          (tudR W Λ u i c).fv P' (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' c ⟨_, hx⟩) := by
  have hfv := tie_fv hc hPr σ₀ u (tudR W Λ u i) Q
  obtain ⟨hL, -, hf⟩ := tam_lat W Λ hc σ₀ u i Q ((tudR W Λ u i c).dia1 P a)
  obtain ⟨h1, h2, h3⟩ := tam_diaL (tudR W Λ u i c) P a
  have hlat : Q.lat c = (tudR W Λ u i c).1.L := congrFun Q.hlat c
  refine ⟨?_, ?_, ?_⟩
  · exact hL.trans (h1.trans hlat.symm)
  · intro x hx
    rw [hfv, hfv]
    exact (hf P x.1).trans (h2 _)
  · intro P' hP' x hx
    rw [hfv, hfv]
    exact (hf P' x.1).trans (congrFun (h3 P' hP') _)

include hX in

theorem tam_so_up (P : Pr.vT u) (c : StCl W Λ u i) (z : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)))
    (hz : (tudR W Λ u i c).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z) = 1) :
    Deco.SameOff (Pr.vT u) Pr.vGs (tieEV hc hX hPr u P).1 (tudR W Λ u i c).1
      ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E) (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)).1 :=
  (tam_upL hc (tudR W Λ u i c) P (tieEV_over hc hX hPr u P) (moveHyp_of_ok hPr u P) (T_unif hX hPr u P).1 (T_unif hX hPr u P).2
    (sepElt_of_ok hPr u) _ hz).1

omit Q in
include hX in

theorem tam_so_dn (P : Pr.vT u) (c : StCl W Λ u i) (g : Module.Dual (𝓞 X.E ⧸ P.1.asIdeal) ((tudR W Λ u i c).lk P)) (hg : g ≠ 0) :
    Deco.SameOff (Pr.vT u) Pr.vGs (tieEV hc hX hPr u P).1 (tudR W Λ u i c).1 ((tudR W Λ u i c).dnL P g).1 :=
  tud_sameOff_dn hc (tudR W Λ u i c) P (moveHyp_of_ok hPr u P) hg (tieEV_over hc hX hPr u P)

end Gen

section Ad

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem tam_ad (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) (v : HeightOneSpectrum (𝓞 X.F))
    (c c' : DecoCl n (Pr.vT u) Pr.vGs Λ.grp) (d₁ : DecoSet X.E n (Pr.vT u) Pr.vGs)
    (h : Deco.SameOff (Pr.vT u) Pr.vGs v (s c).1 d₁.1) (g₀ : UF X.E n × Λ.grp) (hg₀ : g₀ • s c' = d₁) :
    Formalism.L2.Herm.AdStep hc.sig H.J (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.U
      ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.y c).1 ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.y c').1
      (Formalism.L2.Forms.reGL H.hn.symm _ (ufGL X.E n g₀.1)) v := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  rw [Formalism.L2.Forms.reGL_rfl]
  exact tam_move hc _ (Pr.vT u) Pr.vGs Λ.grp hS c₀ v (s c) d₁ (s c') h g₀ hg₀

end Ad

end Formalism.L2.Col
