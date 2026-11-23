import Formalism.LocalToGlobal.Columns.TiedUpDnB
import Formalism.LocalToGlobal.Columns.TiedVal

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

instance tud_kerPrime {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    (RingHom.ker (Ideal.Quotient.mk P.asIdeal)).IsPrime :=
  RingHom.ker_isPrime _

section Comparison₂

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word) {n : ℕ} [NeZero n]
  {cls : Type} (s : cls → DecoSet X.E n (Pr.vT u) Pr.vGs) (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)

theorem tud_unit (P : Pr.vT u) : tieInv hPr u P * cO X.E (Pr.piT u) ∉ P.1.asIdeal := by
  intro h
  have h1 := tieInv_spec hPr u P
  rw [mul_comm] at h
  exact one_notMem P.1 (by simpa using Ideal.sub_mem _ h h1)

theorem tud_unit_mk (P : Pr.vT u) : Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P * cO X.E (Pr.piT u)) = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk P.1.asIdeal), ← map_sub, mul_comm]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (tieInv_spec hPr u P)

theorem tud_rep_pr (P : Pr.vT u) (c : cls) (z : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c))) :
    modP.rep (tiePr hc hPr σ₀ u s Q P c z) - (tieInv hPr u P * cO X.E (Pr.piT u)) • z.1 ∈ P.1.asIdeal • (s c).1.N := by
  have hm : tieInv hPr u P • cO X.E (Pr.piT u) • z.1 ∈ (s c).1.N :=
    (s c).1.N.smul_mem _ ((s c).2.smul_Lsh_mem_N (sepElt_of_ok hPr u).conj ((tie_Ld_eq hc σ₀ u s Q c) ▸ z.2))
  have h1 : modP.mk P.1 (s c).1.N ⟨modP.rep (tiePr hc hPr σ₀ u s Q P c z), modP.rep_mem _⟩ =
      modP.mk P.1 (s c).1.N ⟨_, hm⟩ := (modP.mk_rep _).trans rfl
  rw [mul_smul]
  exact (lv_mk_eq_iff P.1 _ _).1 h1

theorem tud_prk (P : Pr.vT u) (c : cls) (I : Ideal (𝓞 X.E)) (hI : I = P.1.asIdeal) (g : Module.Dual (𝓞 X.E ⧸ P.1.asIdeal) ((s c).lk P))
    (y : Sp X.E n) (hy : y ∈ Q.lat c ⊔ I • dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)) :
    g (tiePrk hc hPr σ₀ u s Q P c I hI ⟨y, hy⟩) = modP.ext P.1 ((s c).1.kerAt P) g y := by
  have hy' : y ∈ (s c).1.LshKer P := tie_Lk_eq hc hPr σ₀ u s Q c P I hI ▸ hy
  have hm : (tieInv hPr u P * cO X.E (Pr.piT u)) • y ∈ (s c).1.kerAt P := by
    rw [mul_smul]
    exact Submodule.smul_mem _ _ (lv_smul_LshKer_mem (s c) (sepElt_of_ok hPr u) P hy')
  have h1 := modP.ext_spec P.1 ((s c).1.kerAt P) g y (tud_unit hPr u P) hm
  rw [tud_unit_mk, one_mul] at h1
  rw [h1]
  congr 1
  show modP.mk P.1 _ ⟨tieInv hPr u P • cO X.E (Pr.piT u) • y, _⟩ = _
  congr 1
  exact Subtype.ext (mul_smul _ _ _).symm

end Comparison₂

theorem tud_ufGL_ratHom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (n : ℕ) (γ : URat hc n) : ufGL E n (ratHom hc n γ) = (γ : GL (Fin n) E) := by
  show (toGLm E n) (glEquiv (γ : GL (Fin n) E)) = _
  unfold toGLm glEquiv
  simp

theorem tud_typ_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {hc : CMData F E} {n : ℕ} [NeZero n] {ST SG : Finset (Pl E)} {H : Subgroup (GLG E n SG)} {M : Type} [CommGroup M]
    (lam : H →* M) (κ : levU hc n ST SG H) : levTyp lam κ⁻¹ = lam (levRed hc n ST SG H κ) := by
  unfold levTyp levChr
  rw [MonoidHom.inv_apply, map_inv, inv_inv]
  rfl

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ) (c₀ : DiaG X.E (Pr.vT u)) (hS : DecoPtSurj hc (R.N i) (Pr.vT u) Pr.vGs)

abbrev tudR : StCl W Λ u i → DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs := repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i)

abbrev tudK (Q : StepCrd Pr σ₀ (R.N i) fun c : StCl W Λ u i => (tudR W Λ u i c).1.L) :=
  clsG hc hX hPr σ₀ u (Λ i) c₀ (tudR W Λ u i) hS (fun c => (stepGSD W Λ u i).outSec.spec c) Q

abbrev tudUp (Q : StepCrd Pr σ₀ (R.N i) fun c : StCl W Λ u i => (tudR W Λ u i c).1.L) (P : Pr.vT u) (c : StCl W Λ u i)
    (z : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c))) : StCl W Λ u i :=
  clsD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E) (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z))

abbrev tudDn (P : Pr.vT u) (c : StCl W Λ u i) (g : Module.Dual (𝓞 X.E ⧸ P.1.asIdeal) ((tudR W Λ u i c).lk P)) : StCl W Λ u i :=
  clsD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) ((tudR W Λ u i c).dnL P g)

theorem tud_trPt (d₁ : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) (γ : URat hc (R.N i)) (κ : levU hc (R.N i) (Pr.vT u) Pr.vGs (Λ i).grp)
    (hγ : ratHom hc (R.N i) γ = ((stepGSD W Λ u i).outSec.mv d₁).1)
    (hκ : levRed hc (R.N i) (Pr.vT u) Pr.vGs (Λ i).grp κ = ((stepGSD W Λ u i).outSec.mv d₁).2)
    (h : FrS X σ₀ (R.N i) → ℂ) (s : FrS X σ₀ (R.N i)) :
    (stepEv W Λ σ₀ hσ u i).trPt d₁ h s =
      (((levTyp ((Units.map σ₀.toMonoidHom).comp (Λ i).chr) κ)⁻¹ : ℂˣ) : ℂ) * h (frMul σ₀ (γ : GL (Fin (R.N i)) X.E)⁻¹ s) := by
  show σ₀ (((Λ i).chr ((stepGSD W Λ u i).outSec.mv d₁).2 : X.Kˣ) : X.K) •
    h (frMul σ₀ (ufGL X.E (R.N i) ((stepGSD W Λ u i).outSec.mv d₁).1)⁻¹ s) = _
  rw [← hγ, ← hκ, tud_ufGL_ratHom, smul_eq_mul, ← map_inv, tud_typ_inv]
  rfl

theorem tud_frame {Q : StepCrd Pr σ₀ (R.N i) fun c : StCl W Λ u i => (tudR W Λ u i c).1.L}
    (eY : FrS X σ₀ (R.N i) ≃ Frames (gramC Q.J Q.emb)) (hW : ∀ s, (eY s).1 = s.1) (hemb : Q.emb = X.embC σ₀)
    (γ : GL (Fin (R.N i)) X.E) {s s' : FrS X σ₀ (R.N i)} (hs : IsTr (atInf Q.emb γ.1) (eY s') (eY s)) :
    frMul σ₀ γ⁻¹ s = s' := by
  have hs' : s = frMul σ₀ γ s' := by
    apply Subtype.ext
    funext τ
    have h1 := hs τ
    rw [hW, hW, hemb] at h1
    exact h1
  rw [hs', ← frMul_mul, inv_mul_cancel, frMul_one]

set_option maxHeartbeats 1000000 in

theorem tud_up (Q : StepCrd Pr σ₀ (R.N i) fun c : StCl W Λ u i => (tudR W Λ u i c).1.L)
    (eY : FrS X σ₀ (R.N i) ≃ Frames (gramC Q.J Q.emb)) (hW : ∀ s, (eY s).1 = s.1) (P : Pr.vT u) (c : StCl W Λ u i)
    (z : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)))
    (hz : (tudR W Λ u i c).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z) = 1) :
    ∃ (γ : UJ (hc.sig : X.E →+* X.E) Q.J) (η : UPts hc.sig Q.J (FiniteAdeleRing (𝓞 X.F) X.F))
      (κ : (tudK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev.U),
      (∀ v', v' ≠ (tieEV hc hX hPr u P).1 → bc (prV (E := X.E) v') η.1 = 1) ∧
      bc (inclE (F := X.F) (FiniteAdeleRing (𝓞 X.F) X.F)) γ.1 *
          ((tudK W Λ hc hX hPr σ₀ u i c₀ hS Q).y (tudUp W Λ hc hPr σ₀ u i Q P c z)).1 =
        ((tudK W Λ hc hX hPr σ₀ u i c₀ hS Q).y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) (Formalism.L2.Forms.mulLat γ.1.1 (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z))) =
        Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)) ∧
      Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
                (Formalism.L2.Forms.mulLat γ.1.1 (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) ⊔
          Submodule.span (𝓞 X.E) {((Pr.T u : ℕ) : X.E)⁻¹ • z.1}) ∧
      (∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z))))
        (hx : ((Pr.T u : ℕ) : 𝓞 X.E) • (γ.1.1 *ᵥ x.1) ∈ dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tudUp W Λ hc hPr σ₀ u i Q P c z)).fv P
            (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P (tudUp W Λ hc hPr σ₀ u i Q P c z) x) =
          (tudR W Λ u i c).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c ⟨_, hx⟩)) ∧
      ∀ (h : FrS X σ₀ (R.N i) → ℂ) s s', IsTr (atInf Q.emb γ.1.1) (eY s') (eY s) →
        (stepEv W Λ σ₀ hσ u i).trPt ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
            (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)) h s =
          ((((tudK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s' := by
  classical
  have ha := sepElt_of_ok hPr u
  have hP := moveHyp_of_ok hPr u P
  obtain ⟨hq, hq2⟩ := T_unif hX hPr u P
  have hLd := tie_Ld_eq hc σ₀ u (tudR W Λ u i) Q c
  have hLd' := tie_Ld_eq hc σ₀ u (tudR W Λ u i) Q (tudUp W Λ hc hPr σ₀ u i Q P c z)
  have hfv := tie_fv hc hPr σ₀ u (tudR W Λ u i) Q P
  have hrz := tud_rep_pr hc hPr σ₀ u (tudR W Λ u i) Q P c z
  have hzL : z.1 ∈ (tudR W Λ u i c).1.Lsh := hLd ▸ z.2
  obtain ⟨γ, η, κ, hγ, hκ, hη, e, h3, h4, h5⟩ := tud_up_core hc (R.N i) (Pr.vT u) Pr.vGs (Λ i).grp hS c₀
    (tudR W Λ u i c) (tudR W Λ u i (tudUp W Λ hc hPr σ₀ u i Q P c z)) P (tieEV_over hc hX hPr u P) hP hq hq2 ha _ hz
    ((stepGSD W Λ u i).outSec.mv _) ((stepGSD W Λ u i).outSec.mv_smul _)
  have h4' := h4 (tud_unit hPr u P) hzL hrz
  rw [map_natCast] at h4'
  have htr := tud_trPt W Λ hc σ₀ hσ u i _ γ κ hγ hκ
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  refine ⟨⟨γ.1, γ.2⟩, η, κ, hη, e, ?_, ?_, ?_, ?_⟩
  · simp only [Ideal.mk_ker]
    rw [hLd]
    exact h3
  · simp only [Ideal.mk_ker]
    rw [hLd']
    convert h4' using 3
  · intro x hx
    rw [hfv, hfv]
    exact h5 x.1 (hLd' ▸ x.2)
  · intro h s s' hs
    rw [htr h s, tud_frame W Λ σ₀ u i eY hW rfl γ.1 hs]
    rfl

set_option maxHeartbeats 1000000 in

theorem tud_dn (Q : StepCrd Pr σ₀ (R.N i) fun c : StCl W Λ u i => (tudR W Λ u i c).1.L)
    (eY : FrS X σ₀ (R.N i) ≃ Frames (gramC Q.J Q.emb)) (hW : ∀ s, (eY s).1 = s.1) (P : Pr.vT u) (c : StCl W Λ u i)
    (g : Module.Dual (𝓞 X.E ⧸ P.1.asIdeal) ((tudR W Λ u i c).lk P)) (hg : g ≠ 0) :
    ∃ (γ : UJ (hc.sig : X.E →+* X.E) Q.J) (η : UPts hc.sig Q.J (FiniteAdeleRing (𝓞 X.F) X.F))
      (κ : (tudK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev.U),
      (∀ v', v' ≠ (tieEV hc hX hPr u P).1 → bc (prV (E := X.E) v') η.1 = 1) ∧
      bc (inclE (F := X.F) (FiniteAdeleRing (𝓞 X.F) X.F)) γ.1 *
          ((tudK W Λ hc hX hPr σ₀ u i c₀ hS Q).y (tudDn W Λ u i P c g)).1 =
        ((tudK W Λ hc hX hPr σ₀ u i c₀ hS Q).y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
                (Formalism.L2.Forms.mulLat γ.1.1 (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudDn W Λ u i P c g)))) =
        Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) (Q.lat c) ∧
      (∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudDn W Λ u i P c g))))
        (hx : γ.1.1 *ᵥ x.1 ∈ Q.lat c ⊔ RingHom.ker (Ideal.Quotient.mk P.1.asIdeal) • dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tudDn W Λ u i P c g)).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P (tudDn W Λ u i P c g) x) =
          g (tiePrk hc hPr σ₀ u (tudR W Λ u i) Q P c (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) Ideal.mk_ker ⟨_, hx⟩)) ∧
      ∀ (h : FrS X σ₀ (R.N i) → ℂ) s s', IsTr (atInf Q.emb γ.1.1) (eY s') (eY s) →
        (stepEv W Λ σ₀ hσ u i).trPt ((tudR W Λ u i c).dnL P g) h s =
          ((((tudK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s' := by
  classical
  have ha := sepElt_of_ok hPr u
  have hP := moveHyp_of_ok hPr u P
  have hLd' := tie_Ld_eq hc σ₀ u (tudR W Λ u i) Q (tudDn W Λ u i P c g)
  have hfv := tie_fv hc hPr σ₀ u (tudR W Λ u i) Q P
  have hprk := tud_prk hc hPr σ₀ u (tudR W Λ u i) Q P c _ Ideal.mk_ker g
  obtain ⟨γ, η, κ, hγ, hκ, hη, e, h3, h5⟩ := tud_dn_core hc (R.N i) (Pr.vT u) Pr.vGs (Λ i).grp hS c₀
    (tudR W Λ u i c) (tudR W Λ u i (tudDn W Λ u i P c g)) P (tieEV_over hc hX hPr u P) hP ha g hg
    ((stepGSD W Λ u i).outSec.mv _) ((stepGSD W Λ u i).outSec.mv_smul _)
  have htr := tud_trPt W Λ hc σ₀ hσ u i _ γ κ hγ hκ
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  refine ⟨⟨γ.1, γ.2⟩, η, κ, hη, e, ?_, ?_, ?_⟩
  · simp only [Ideal.mk_ker]
    rw [hLd']
    exact h3
  · intro x hx
    rw [hfv, hprk]
    exact h5 x.1
  · intro h s s' hs
    rw [htr h s, tud_frame W Λ σ₀ u i eY hW rfl γ.1 hs]
    rfl

end Gen

end Formalism.L2.Col
