import Formalism.LocalToGlobal.Columns.TiedXpV
import Formalism.LocalToGlobal.Columns.TiedAtT
import Formalism.LocalToGlobal.Columns.RowFormsGood

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem xp_mulLat_L (hc : CMData F E) {n : ℕ} [NeZero n] {ST SG : Finset (Pl E)} {H : Subgroup (GLG E n SG)} (g : UF E n × H)
    (e : DecoSet E n ST SG) :
    Formalism.L2.Forms.mulLat (((ratEquiv hc n).symm g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) e.1.L = (g • e).1.L := by
  rw [rlc_smul_val, Deco.L_act]
  unfold Formalism.L2.Forms.mulLat gmap
  congr 1
  apply LinearMap.ext
  intro x
  show (((ratEquiv hc n).symm g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x = g.1.1 x
  rw [← rlc_ratHom_apply hc n]
  have : ratHom hc n ((ratEquiv hc n).symm g.1) = g.1 := (ratEquiv hc n).apply_symm_apply g.1
  rw [this]

def padL (E : Type) [Field E] (n N : ℕ) : (Fin n → E) →ₗ[E] (Fin N → E) where
  toFun x j := if h : (j : ℕ) < n then x ⟨j, h⟩ else 0
  map_add' x y := by
    funext j
    by_cases h : (j : ℕ) < n <;> simp [h]
  map_smul' c x := by
    funext j
    by_cases h : (j : ℕ) < n <;> simp [h]

theorem padL_apply (E : Type) [Field E] (n N : ℕ) (x : Fin n → E) (j : Fin N) :
    padL E n N x j = if h : (j : ℕ) < n then x ⟨j, h⟩ else 0 := rfl

theorem xp_tilH_L {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG : Finset (Pl E)} (d : DecoSet E n ∅ SG) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) (hpi : ∀ P : ST, pi ∈ P.1.asIdeal)
    (hdvd : ∀ r : 𝓞 E, (∀ P : ST, r ∈ P.1.asIdeal) → pi ∣ r)
    (iX : (Fin n → E) →ₗ[E] (Fin N → E))
    (hiX : ∀ x (j : Fin N), iX x j = if h : (j : ℕ) < n then x ⟨j, h⟩ else 0) :
    (DecoSet.tilH (ST := ST) hN pi d).1.L = d.1.N.map (iX.restrictScalars (𝓞 E)) ⊔
      Submodule.span (𝓞 E) {(Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi) : Fin N → E)} := by
  subst hN
  show (DecoSet.til (ST := ST) pi d).1.L = _
  rw [DecoSet.til_val d hT hG, d.2.til_L hT hG hpi hdvd]
  have e1 : iX = incl E n := by
    apply LinearMap.ext
    intro x
    funext j
    rw [hiX]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [incl]
    · simp [incl]
  have e2 : z0 E n (algebraMap (𝓞 E) E pi) = (Pi.single (lastIdx (n + 1)) (algebraMap (𝓞 E) E pi) : Fin (n + 1) → E) := by
    have hl : lastIdx (n + 1) = Fin.last n := Fin.ext (by simp [lastIdx])
    rw [hl]
    funext j
    simp [z0, eLast, Pi.single_apply]
  rw [e1, e2]

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem xp_crd_frame (i : ℕ) (hi : i ≤ d.R.m) (b : Fin (d.sp.X i).rank) :
    d.crd i hi ((d.sp.X i).frame b) = Pi.single (finCongr (d.sp.X_rank i hi) b) (1 : d.host.E) := by
  funext j
  show (d.sp.X i).frame.equivFun ((d.sp.X i).frame b) ((finCongr (d.sp.X_rank i hi)).symm j) = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by rw [h, Equiv.symm_apply_apply]⟩

def ColDat.z0 (d : ColDat) (u : d.what₂.Word) : Fin (d.R.N d.R.m) → d.host.E :=
  Pi.single (lastIdx (d.R.N d.R.m)) (d.piT u : d.host.E)

theorem zc_eq (hS : SpStd d.toColBase) :
    ∃ c : d.host.E, c ≠ 0 ∧ CF.zc (d.colRec a) = Pi.single (lastIdx (d.R.N d.R.m)) c := by
  obtain ⟨c, hc⟩ := hS.z
  have hr := d.sp.X_rank d.R.m le_rfl
  set b₀ : Fin (d.sp.X d.R.m).rank := (finCongr hr).symm (lastIdx (d.R.N d.R.m)) with hb₀
  have hb : (b₀ : ℕ) + 1 = (d.sp.X d.R.m).rank := by
    have h1 : (b₀ : ℕ) = d.R.N d.R.m - 1 := rfl
    have := d.R.N_pos d.R.m
    omega
  have hz := hc b₀ hb
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    apply d.sp.z_anis
    rw [hz, zero_smul, map_zero]
  · show d.crd d.R.m le_rfl d.sp.z = _
    rw [hz, map_smul, xp_crd_frame, hb₀, Equiv.apply_symm_apply]
    funext j
    simp [Pi.single_apply]

theorem piT_coe_ne_zero (u : d.what₂.Word) : (d.piT u : d.host.E) ≠ 0 :=
  (basePi_of_ok (Pr := d.Pr) d.hX d.hPr u).coe_ne_zero

theorem lastCoordinateUniformizerVector_spans_orthogonal_line (hS : SpStd d.toColBase) (u : d.what₂.Word) : ∃ c : d.host.E, d.z0 u = c • CF.zc (d.colRec a) := by
  obtain ⟨c, hc0, hc⟩ := zc_eq a hS
  refine ⟨(d.piT u : d.host.E) / c, ?_⟩
  rw [hc]
  funext j
  unfold ColDat.z0
  by_cases h : j = lastIdx (d.R.N d.R.m)
  · subst h
    simp [div_mul_cancel₀ _ hc0]
  · simp [h]

theorem hermitianForm_lastCoordinateUniformizerVector_self (hS : SpStd d.toColBase) (u : d.what₂.Word) :
    hform (CF.sigD (d.colRec a) : d.host.E →+* d.host.E) (CF.gramN (d.colRec a) d.R.m le_rfl) (d.z0 u) (d.z0 u) =
      (((d.colRec a).mem u).A.T : d.host.E) := by
  rw [gramN_eq a hS]
  have h1 := rf_hform_one (X := d.X) (d.z0 u) (d.z0 u)
  refine Eq.trans h1 ?_
  rw [hStd_apply, Finset.sum_eq_single (lastIdx (d.R.N d.R.m))]
  · unfold ColDat.z0
    rw [Pi.single_eq_same]
    have h2 := congrArg (algebraMap (𝓞 d.host.E) d.host.E) (d.hPr.piT_norm u)
    rw [map_mul, map_natCast] at h2
    rw [mul_comm]
    exact h2
  · intro j _ hj
    unfold ColDat.z0
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

def ColDat.tilPt (d : ColDat) (u : d.what₂.Word) (c : PCl d) : DecoSet d.X.E (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs :=
  tilR (Pr := d.Pr) (R := d.R) (Finset.Subset.refl _) u (d.reprP c)

def ColDat.tilMv (d : ColDat) (u : d.what₂.Word) (c : PCl d) : (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).G :=
  (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.mv (d.tilPt u c)

theorem tilMv_smul (u : d.what₂.Word) (c : PCl d) :
    d.tilMv u c • d.repr u d.R.m (tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c) = d.tilPt u c :=
  (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.mv_smul (d.tilPt u c)

def ColDat.tilGa (d : ColDat) (u : d.what₂.Word) (c : PCl d) : URat d.sp.cm (d.R.N d.R.m) :=
  (ratEquiv d.sp.cm (d.R.N d.R.m)).symm (d.tilMv u c).1

def tieGa (hS : SpStd d.toColBase) (u : d.what₂.Word) (c : PCl d) :
    UJ (CF.sigD (d.colRec a) : d.host.E →+* d.host.E) (CF.gramN (d.colRec a) d.R.m le_rfl) :=
  ⟨(d.tilGa u c).1, by rw [gramN_eq a hS]; exact (d.tilGa u c).2⟩

theorem coordinates_frame_eq_single (b : Fin d.sp.X'.rank) :
    CF.crdP (d.colRec a) (d.sp.X'.frame b) = Pi.single (finCongr (CF.rankP (d.colRec a)) b) (1 : d.host.E) := by
  funext j
  show d.sp.X'.frame.equivFun (d.sp.X'.frame b) ((finCongr (CF.rankP (d.colRec a))).symm j) = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by rw [h, Equiv.symm_apply_apply]⟩

theorem iXc_eq (hS : SpStd d.toColBase) : CF.iXc (d.colRec a) = padL d.host.E (d.R.N d.R.m - 1) (d.R.N d.R.m) := by
  apply (Pi.basisFun d.host.E (Fin (d.R.N d.R.m - 1))).ext
  intro k
  rw [Pi.basisFun_apply]
  have hk : (k : ℕ) < d.R.N d.R.m := lt_of_lt_of_le k.2 (Nat.sub_le _ _)
  have h1 : (CF.crdP (d.colRec a)).symm (Pi.single k (1 : d.host.E)) =
      d.sp.X'.frame ((finCongr (CF.rankP (d.colRec a))).symm k) := by
    rw [LinearEquiv.symm_apply_eq, coordinates_frame_eq_single, Equiv.apply_symm_apply]
  show d.crd d.R.m le_rfl (d.sp.iX' ((CF.crdP (d.colRec a)).symm (Pi.single k (1 : d.host.E)))) = _
  rw [h1, hS.iX' _ ((finCongr (d.sp.X_rank d.R.m le_rfl)).symm ⟨k, hk⟩) rfl, xp_crd_frame, Equiv.apply_symm_apply]
  funext j
  rw [padL_apply, Pi.single_apply]
  by_cases h : (j : ℕ) < d.R.N d.R.m - 1
  · rw [dif_pos h, Pi.single_apply]
    congr 1
    exact propext ⟨fun e => Fin.ext (show (j : ℕ) = k from congrArg (fun z : Fin (d.R.N d.R.m) => (z : ℕ)) e),
      fun e => Fin.ext (show (j : ℕ) = k from congrArg (fun z : Fin (d.R.N d.R.m - 1) => (z : ℕ)) e)⟩
  · rw [dif_neg h, if_neg]
    rintro rfl
    exact h k.2

theorem til_lat (hS : SpStd d.toColBase) (u : d.what₂.Word) (c : PCl d) :
    Formalism.L2.Forms.mulLat (tieGa a hS u c).1.1 (CF.clsCrd (d.colRec a) u d.R.m le_rfl
              (tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c)) =
      ((d.reprP c).1.N).map ((CF.iXc (d.colRec a)).restrictScalars (𝓞 d.host.E)) ⊔ Submodule.span (𝓞 d.host.E) {d.z0 u} := by
  rw [iXc_eq a hS]
  refine (congrArg (Formalism.L2.Forms.mulLat (tieGa a hS u c).1.1) (clsCrd_eq a u d.R.m le_rfl _)).trans ?_
  refine (xp_mulLat_L d.sp.cm (d.tilMv u c) _).trans ?_
  have h := tilMv_smul u c
  refine (congrArg (fun e : DecoSet d.X.E (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs => e.1.L) h).trans ?_
  exact xp_tilH_L (N_m_succ d.R) (d.reprP c) (fun P => conj_piT_notMem d.hPr u P) (a.piT_off u)
    (fun P => decoFin_mem_of_mem_divs P.2) (fun r hr => piT_dvd_of_mem d.hX d.hPr u r hr) _ (padL_apply _ _ _)

end Rec

end Formalism.L2.Col
