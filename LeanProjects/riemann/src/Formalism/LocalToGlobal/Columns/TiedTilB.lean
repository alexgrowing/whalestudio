import Formalism.LocalToGlobal.Columns.TiedTilA
import Formalism.LocalToGlobal.Columns.TiedXpT

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem til_tmv_padL_cs (n : ℕ) {R : Type} [CommRing R] (φ : E →+* R) (a b : Fin n) :
    ((LinearMap.toMatrix' (padL E n (n + 1))).map φ) a.castSucc b = if a = b then 1 else 0 := by
  rw [Matrix.map_apply, LinearMap.toMatrix'_apply, padL_apply, dif_pos (by simp), Pi.single_apply]
  have e : (⟨(a.castSucc : ℕ), by simp⟩ : Fin n) = a := Fin.ext rfl
  rw [e]
  split_ifs
  · exact map_one φ
  · exact map_zero φ

theorem til_tmv_padL_last (n : ℕ) {R : Type} [CommRing R] (φ : E →+* R) (b : Fin n) :
    ((LinearMap.toMatrix' (padL E n (n + 1))).map φ) (Fin.last n) b = 0 := by
  rw [Matrix.map_apply, LinearMap.toMatrix'_apply, padL_apply, dif_neg (by simp), map_zero]

theorem til_tmv_move (hc : CMData F E) {N n : ℕ} (hN : N = n + 1) [NeZero N] [NeZero n] (ST SG : Finset (Pl E))
    (H : Subgroup (GLG E N SG)) (c₀ : DiaG E ST) {pi : 𝓞 E} (h0 : pi ≠ 0)
    (hcP : ∀ P : ST, ((c₀ P : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal (cO E pi))
    (hw : ∀ w : SG, pi - 1 ∈ w.1.asIdeal) (hS' : DecoPtSurj hc n (∅ : Finset (Pl E)) SG) (hS : DecoPtSurj hc N ST SG)
    (d' : DecoSet E n ∅ SG) (e : DecoSet E N ST SG) (a : UF E N × H)
    (ha : a • e = (DecoSet.tilH (ST := ST) hN pi d').res (Finset.Subset.refl _)) :
    ∃ κ : levU hc N ST SG H, levRed hc N ST SG H κ = a.2 ∧
      ∀ g : GL (Fin N) (E ⊗[F] Formalism.L2.Herm.Af F),
        g.1 * (LinearMap.toMatrix' (padL E n N)).map (iA F E) =
          (LinearMap.toMatrix' (padL E n N)).map (iA F E) * (ptOfD hc n ∅ SG 1 d').1.1 →
        g.1 *ᵥ (fun j => iA F E ((Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi) : Fin N → E) j)) =
          (fun j => iA F E ((Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi) : Fin N → E) j)) →
        bc (iA F E) ((ratEquiv hc N).symm a.1).1 * (ptOfD hc N ST SG c₀ e).1 = g * κ.1 := by
  subst hN
  have hy' : decoOf (∅ : Finset (Pl E)) SG (ptOfD hc n ∅ SG 1 d').1 = d' := by
    unfold ptOfD
    rw [decoOf_ptOf hc n ∅ SG hS', inv_one, DecoSet.dia_one]
  have hy : decoOf ST SG (ptOfD hc (n + 1) ST SG c₀ e).1 = e.dia c₀⁻¹ := by
    unfold ptOfD
    rw [decoOf_ptOf hc (n + 1) ST SG hS]
  have ha' : a • e = DecoSet.til (ST := ST) pi d' := ha
  have h1 := til_tmv_decoOfD ST SG hc (ptOfD hc n ∅ SG 1 d').2 c₀ hcP hw
  rw [hy', ← ha'] at h1
  have h2 : decoOf ST SG (padA F E n (ptOfD hc n ∅ SG 1 d').1) = a • decoOf ST SG (ptOfD hc (n + 1) ST SG c₀ e).1 := by
    rw [hy]
    have h3 := congrArg (fun t => DecoSet.dia c₀⁻¹ t) h1
    have h4 : (decoOfD (n + 1) ST SG c₀ (padA F E n (ptOfD hc n ∅ SG 1 d').1)).dia c₀⁻¹ =
        decoOf ST SG (padA F E n (ptOfD hc n ∅ SG 1 d').1) := DecoSet.dia_inv_dia c₀ _
    exact h4.symm.trans h3
  obtain ⟨γ, k, hγ, hk, hx⟩ := rlc_rel_of_orbit hc (n + 1) ST SG H
    (x := ⟨padA F E n (ptOfD hc n ∅ SG 1 d').1, padA_mem_UAd hc (ptOfD hc n ∅ SG 1 d').2⟩) (y := ptOfD hc (n + 1) ST SG c₀ e) a h2
  refine ⟨k, hk, fun g hg1 hg2 => ?_⟩
  have hγ' : (ratEquiv hc (n + 1)).symm a.1 = γ := (MulEquiv.symm_apply_eq _).2 hγ.symm
  have hp : algebraMap (𝓞 E) E pi ≠ 0 := by
    intro hz
    exact h0 (RingOfIntegers.ext (by simpa using hz))
  have hg : g = padA F E n (ptOfD hc n ∅ SG 1 d').1 := by
    apply Units.ext
    refine til_tmv_eq_padM _ (til_tmv_padL_cs n (iA F E)) (til_tmv_padL_last n (iA F E)) _ ?_ ?_ _ _ hg1 hg2
    · intro j
      rw [til_tmv_lastIdx, Pi.single_eq_of_ne (Fin.castSucc_ne_last j), map_zero]
    · rw [til_tmv_lastIdx, Pi.single_eq_same]
      exact hp.isUnit.map (iA F E)
  rw [hγ', hg]
  have hx' : padA F E n (ptOfD hc n ∅ SG 1 d').1 = bc (iA F E) (γ : GL (Fin (n + 1)) E) * (ptOfD hc (n + 1) ST SG c₀ e).1 * (k.1)⁻¹ := hx
  rw [hx', inv_mul_cancel_right]

end Gen

section Pr

variable {X : Fields} {Pr : Primes X}

theorem til_tmv_piT_sub_one (hPr : Pr.Ok) (u : Pr.Word) (w : Pr.vGs) : Pr.piT u - 1 ∈ w.1.asIdeal := by
  have hgg : ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := by
    obtain ⟨i, hi⟩ := exists_g_mem hPr w
    push_cast
    apply Ideal.mul_mem_left
    rw [sq]
    apply Ideal.mul_mem_left
    fin_cases i
    · exact Ideal.mul_mem_right _ _ hi
    · exact Ideal.mul_mem_left _ _ hi
  exact Ideal.mem_of_dvd _ (hPr.piT_cong u) hgg

theorem til_tmv_diaT (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) :
    ((diaT u P : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) : 𝓞 X.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) := by
  have := P.1.isMaximal
  let _ := Ideal.Quotient.field P.1.asIdeal
  have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (X.conjO (Pr.piT u))) :=
    (mk_ne_zero (conj_piT_notMem hPr u P)).isUnit
  unfold diaT
  rw [dif_pos hu]
  rfl

theorem til_tmv_colDia (hPr : Pr.Ok) (R : Ranks) (u : Pr.Word) (P : Pr.vT u) :
    ((colDia R u R.m P : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) : 𝓞 X.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) := by
  unfold colDia
  rw [if_neg (lt_irrefl _)]
  exact til_tmv_diaT hPr u P

end Pr

section Rec

variable {d : ColDat} (a : ColArgs d)

set_option maxHeartbeats 1000000 in

theorem til_tmv_rec (hS : SpStd d.toColBase) (hP : PtSurjP d) (hQ : PtSurj d) (u : d.what₂.Word) (c : PCl d) :
    ∃ κ : levU d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp,
    levRed d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp κ = (d.tilMv u c).2 ∧
    ∀ g : GL (Fin (d.R.N d.R.m)) (d.host.E ⊗[d.host.F] FiniteAdeleRing (𝓞 d.host.F) d.host.F),
      CF.IsExt (d.colRec a) (d.z0 u) (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F))
        (ptOfD d.sp.cm (d.R.N d.R.m - 1) ∅ d.Pr.vGs 1 (d.reprP c)).1.1 g.1 →
      bc (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F)) (d.tilGa u c).1 *
        (ptOfD d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m)
          (d.repr u d.R.m (tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c))).1 = g * κ.1 := by
  have h0 : d.Pr.piT u ≠ 0 := fun h => piT_coe_ne_zero (d := d) u (by
    show ((d.Pr.piT u : 𝓞 d.X.E) : d.X.E) = 0
    rw [h]; rfl)
  obtain ⟨κ, h1, h2⟩ := til_tmv_move (F := d.X.F) (E := d.X.E) d.sp.cm (N_m_succ d.R) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp
    (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) h0 (til_tmv_colDia d.hPr d.R u) (til_tmv_piT_sub_one d.hPr u) hP (hQ u d.R.m)
    (d.reprP c) (d.repr u d.R.m (tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c)) (d.tilMv u c) (tilMv_smul u c)
  refine ⟨κ, h1, fun g hg => h2 g ?_ hg.2⟩
  have h3 := hg.1
  unfold CF.iXm at h3
  rw [iXc_eq a hS] at h3
  exact h3

end Rec

end Formalism.L2.Col
