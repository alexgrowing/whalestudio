import Formalism.LocalToGlobal.Columns.RecLevelAsm
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG : Finset (Pl E)} (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))
  {π : 𝓞 E} {T f : ℕ}

def stepOf (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG)
    (hidx : (baseLb E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f))
    (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ) :
    Formalism.L2.Forms.StepLevel F E hc.sig (1 : Matrix (Fin n) (Fin n) E) T f (plUnder F SG) where
  Lb := baseLb E n ST
  Lb_fin := baseLb_fin n ST
  Lb_span := baseLb_span n ST
  Lb_int := baseLb_int hc n ST
  Lb_dual := baseLb_dual hc n ST (fun P hP => (hST P).1 hP) hTπ
  Lb_index := hidx
  Uloc := levLoc hc n ST SG (Subgroup.pi Set.univ Hw)
  Uloc_le := levLoc_le hc n ST SG _
  Uloc_lev := levLoc_le_levelVL hc n ST SG _
  Uloc_hyp v hv hT := levLoc_eq_levelVL hc n ST SG _ v
    (fun h => hT ((mem_plUnder_iff_norm hc hST T hTπ v).1 h)) hv
  fM v _ := fMod hc n ST v
  fT v _ := fLoc hc n ST v
  fT_ne v h := fLoc_ne hc n v hB ((mem_plUnder_iff_norm hc hST T hTπ v).2 h)
  fT_T v _ x := fLoc_natCast_smul_eq_zero_of_dvd hc n v hB T ⟨cO E π, hTπ.symm⟩ x
  fM_card v h := by
    obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc hST T hTπ v).2 h
    rw [fMod_card hc n v hB hP hov (hB.over_unique hc hP hov), hcard P hP]
  fT_L v _ x hx := fLoc_L hc n v x hx
  UlocAlt v h := levLoc_eq_stabFun hc n SG _ v hB (hSG v h)
  U := levU hc n ST SG (Subgroup.pi Set.univ Hw)
  U_eq x := levU_eq_prod hc n ST SG Hw x
  U_compact := levU_compact hc n ST SG _
  U_open := levU_open hc n ST SG _
  chi := levTyp lam
  chi_triv x h := levTyp_eq_one hc n ST SG _ lam x h

end Gen

section Col

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem rls_T_notUnder (hPr : Pr.Ok) (u : Pr.Word) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal) :
    v ∉ plUnder X.F Pr.vGs := by
  rintro ⟨w, hw, hov⟩
  apply T_notMem_vGs hPr u ⟨w, hw⟩
  have : (Pr.T u : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ h
  rwa [Ideal.mem_comap, map_natCast] at this

theorem rls_vT_iff (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (P : Pl X.E) : P ∈ Pr.vT u ↔ Pr.piT u ∈ P.asIdeal :=
  mem_divs (basePi_of_ok hX hPr u).ne_zero P

def colStep (hc : Formalism.BasicNotions.CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (Ch : Chars X Pr R.m) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (j : ℕ) :
    Formalism.L2.Forms.StepLevel X.F X.E hc.sig (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) (Pr.T u) X.f (plUnder X.F Pr.vGs) :=
  stepOf hc (R.N j) (fun w => (colLev Ch j w).H) (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = Pr.T u)) (rls_T_notUnder hPr u)
    (colBase_index hc (R.N j) hPr u) ((Units.map σ₀.toMonoidHom).comp (colLev Ch j).chr)

theorem colStep_U (hc : Formalism.BasicNotions.CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (Ch : Chars X Pr R.m) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (j : ℕ) :
    (colStep hc hX hPr Ch σ₀ u j).U = colU hc Ch u j := rfl

end Col

end Formalism.L2.Col
