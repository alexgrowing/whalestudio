import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.RecLevelLocF

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.UG.P

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

theorem fv_rho_prV {P : Pl E} (hov : IsOver v P) (β : Formalism.L2.Herm.intAf F E) :
    rll_rho v P ⟨prV (E := E) v (β : E ⊗[F] Formalism.L2.Herm.Af F), afsplit_prV_int v _ β.2⟩ = resS F P β := by
  show resS F P ⟨afsplitIE v (prV (E := E) v (β : E ⊗[F] Formalism.L2.Herm.Af F)), _⟩ = resS F P β
  rw [← sub_eq_zero, ← map_sub]
  refine resS_eq_zero_of_prV P v hov _ ?_
  show prV (E := E) v (afsplitIE v (prV (E := E) v (β : E ⊗[F] Formalism.L2.Herm.Af F)) - (β : E ⊗[F] Formalism.L2.Herm.Af F)) = 0
  rw [map_sub, afsplit_prV_IE, sub_self]

theorem fv_prV_pullV (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (z : Fin n → E) (i : Fin n) :
    prV (E := E) v (pullV y z i) =
      (((bc (prV (E := E) v) y)⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)).1 *ᵥ
        fun a => inclE (F := F) (v.adicCompletion F) (z a)) i := by
  unfold pullV
  rw [← map_inv]
  simp only [Matrix.mulVec, dotProduct]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, afsplit_prV_inclE]
  rfl

variable (h : BasePi ST π)

theorem fv_psi_pull {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (z : Fin n → E)
    (hz : cO E π • z ∈ Formalism.UG.CS.globLat y (stdLat E n))
    (ht : (((bc (prV (E := E) v) y)⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)).1 *ᵥ
        fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ baseDualV hc n ST v) :
    rll_psi hc n v h P ⟨_, ht⟩ = Ideal.Quotient.mk P.asIdeal (cO E π) * redA P (pullV y z (lastIdx n)) := by
  have hm : iA F E (algebraMap (𝓞 E) E (cO E π)) * pullV y z (lastIdx n) ∈ Formalism.L2.Herm.intAf F E := by
    rw [← pullV_osmul]
    exact (mem_globLat y _).1 hz _
  rw [redA_spec P (h.conj_notMem hP) hm, ← fv_rho_prV v hov]
  show rll_rho v P _ = rll_rho v P _
  congr 1
  apply Subtype.ext
  show inclE (F := F) (v.adicCompletion F) (star (algebraMap (𝓞 E) E π)) * _ =
    prV (E := E) v (iA F E (algebraMap (𝓞 E) E (cO E π)) * pullV y z (lastIdx n))
  rw [map_mul, afsplit_prV_inclE, fv_prV_pullV, algebraMap_cO]

def fvPsiEquiv {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P) :
    fMod hc n ST v ≃+ kP P :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
    ext x
    rw [AddMonoidHom.mem_ker, rll_psi_ker hc n v h hP huniq]
    rfl : ((Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseKer E n ST)).comap
      (baseDualV hc n ST v).subtype).toAddSubgroup = (rll_psi hc n v h P).ker)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (rll_psi_surj hc n v h hov))

def fvMulEquiv {R : Type} [CommRing R] (a b : R) (hab : a * b = 1) : R ≃+ R where
  toFun x := a * x
  invFun x := b * x
  left_inv x := by
    show b * (a * x) = x
    rw [← mul_assoc, mul_comm b a, hab, one_mul]
  right_inv x := by
    show a * (b * x) = x
    rw [← mul_assoc, hab, one_mul]
  map_add' := mul_add _

def fvMeL {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P)
    (a b : 𝓞 E ⧸ P.asIdeal) (hab : a * b = 1) : fMod hc n ST v ≃+ (𝓞 E ⧸ P.asIdeal) :=
  (fvPsiEquiv hc n v h hP hov huniq).trans (fvMulEquiv a b hab)

theorem fvMeL_fLoc {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P)
    (a b : 𝓞 E ⧸ P.asIdeal) (hab : a * b = 1) (x : baseDualV hc n ST v) :
    fvMeL hc n v h hP hov huniq a b hab (fLoc hc n ST v x) = a * rll_psi hc n v h P x := rfl

variable (SG : Finset (Pl E)) (c₀ : DiaG E ST)

omit h in

theorem fv_f_eq (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hyU : y ∈ UAd hc n) (d : DecoSet E n ST SG)
    (hd : decoOfD n ST SG c₀ y = d) (P : ST) (z : Sp E n) (hz : z ∈ d.1.at P.1) :
    d.1.N = Formalism.UG.CS.globLat y (stdLat E n) ∧ d.1.f P z = (c₀ P).1 * redA P.1 (pullV y z (lastIdx n)) := by
  classical
  have hval : d.1 = (decoRaw ST SG y).dia c₀ := by
    rw [← hd, ← rlc_decoOf_val hc n ST SG hyU]
    rfl
  have hN : d.1.N = Formalism.UG.CS.globLat y (stdLat E n) := by rw [hval]; rfl
  refine ⟨hN, ?_⟩
  have hloc : z ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat y (stdLat E n)) := by
    rw [← hN]; exact hz
  rw [hval]
  show (c₀ P).1 * (if z ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat y (stdLat E n)) then
    redA P.1 (pullV y z (lastIdx n)) else 0) = _
  rw [if_pos hloc]

theorem fv_tieL (ha : SepElt ST (cO E π)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hyU : y ∈ UAd hc n)
    (d : DecoSet E n ST SG) (hd : decoOfD n ST SG c₀ y = d) (P : ST) (hov : IsOver v P.1) {t : 𝓞 E}
    (htt : cO E π * t - 1 ∈ P.1.asIdeal) (z : Sp E n) (hzL : z ∈ d.1.Lsh)
    (ht : (((bc (prV (E := E) v) y)⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)).1 *ᵥ
        fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ baseDualV hc n ST v) :
    d.1.f P z = (c₀ P).1 * Ideal.Quotient.mk P.1.asIdeal t * rll_psi hc n v h P.1 ⟨_, ht⟩ := by
  obtain ⟨hN, hf⟩ := fv_f_eq hc n SG c₀ y hyU d hd P z (d.2.Lsh_le_at ha P hzL)
  have hzN : cO E π • z ∈ Formalism.UG.CS.globLat y (stdLat E n) := by
    rw [← hN]
    exact d.2.smul_Lsh_mem_N ha.conj hzL
  have h1 : Ideal.Quotient.mk P.1.asIdeal t * Ideal.Quotient.mk P.1.asIdeal (cO E π) = 1 := by
    rw [← map_mul, mul_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk P.1.asIdeal), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.2 htt
  rw [hf, fv_psi_pull hc n v h P.2 hov y z hzN ht, mul_assoc, ← mul_assoc (Ideal.Quotient.mk P.1.asIdeal t), h1, one_mul]

end Loc

section Dec

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem fv_unit (P : Pr.vT u) :
    (c₀ P).1 * Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P) *
      (Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) * (c₀ P).inv) = 1 := by
  have h1 : Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P) * Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) = 1 := by
    rw [← map_mul, mul_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk P.1.asIdeal), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (tieInv_spec hPr u P)
  rw [mul_assoc, ← mul_assoc (Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P)), h1, one_mul]
  exact (c₀ P).val_inv

def fvMe (P : Pr.vT u) : fMod hc n (Pr.vT u) (tieEV hc hX hPr u P).1 ≃+ (𝓞 X.E ⧸ P.1.asIdeal) :=
  fvMeL hc n (tieEV hc hX hPr u P).1 (basePi_of_ok hX hPr u) P.2 (tieEV_over hc hX hPr u P)
    ((basePi_of_ok hX hPr u).over_unique hc P.2 (tieEV_over hc hX hPr u P)) _ _ (fv_unit hPr u c₀ P)

theorem fv_tie₁ (y : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) (hyU : y ∈ UAd hc n) (d : DecoSet X.E n (Pr.vT u) Pr.vGs)
    (hd : decoOfD n (Pr.vT u) Pr.vGs c₀ y = d) (P : Pr.vT u) (z : Sp X.E n) (hzL : z ∈ d.1.Lsh)
    (ht : (((bc (prV (E := X.E) (tieEV hc hX hPr u P).1) y)⁻¹ :
          GL (Fin n) (X.E ⊗[X.F] (tieEV hc hX hPr u P).1.adicCompletion X.F)).1 *ᵥ
        fun a => inclE (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (z a)) ∈
      baseDualV hc n (Pr.vT u) (tieEV hc hX hPr u P).1) :
    d.1.f P z = fvMe hc hX hPr u c₀ P (fLoc hc n (Pr.vT u) (tieEV hc hX hPr u P).1 ⟨_, ht⟩) :=
  fv_tieL hc n (tieEV hc hX hPr u P).1 (basePi_of_ok hX hPr u) Pr.vGs c₀ (sepElt_of_ok hPr u) y hyU d hd P
    (tieEV_over hc hX hPr u P) (tieInv_spec hPr u P) z hzL ht

variable (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
  (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)

def tieFMe (P : Pr.vT u) :
    (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.fM (tieEV hc hX hPr u P).1 (tieEV hc hX hPr u P).2 ≃+ (𝓞 X.E ⧸ P.1.asIdeal) := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact fvMe hc hX hPr u c₀ P

set_option maxHeartbeats 1000000 in

theorem tie_FvTie (P : Pr.vT u) (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp)
    (z : ↥(Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)))
    (hz : ((bc (prV (E := X.E) (tieEV hc hX hPr u P).1) ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (z.1 a)) ∈
      latS (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (intV X.E (tieEV hc hX hPr u P).1)
        (Submodule.span (𝓞 X.E) (dualSet (hc.sig : X.E →+* X.E) Q.J (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.Lb))) :
    (s c).fv P (tiePr hc hPr σ₀ u s Q P c z) =
      tieFMe hc hX hPr σ₀ u Λ c₀ s hS hs Q P
        ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.fT (tieEV hc hX hPr u P).1 (tieEV hc hX hPr u P).2 ⟨_, hz⟩) := by
  have hzL : z.1 ∈ (s c).1.Lsh := (tie_Ld_eq hc σ₀ u s Q c) ▸ z.2
  refine (tie_fv hc hPr σ₀ u s Q P c z).trans ?_
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact fv_tie₁ hc hX hPr u c₀ _ (ptOfD hc n (Pr.vT u) Pr.vGs c₀ (s c)).2 (s c)
    (decoOfD_ptOfD hc n (Pr.vT u) Pr.vGs hS c₀ (s c)) P z.1 hzL hz

end Dec

section Rec

variable {d : ColDat} (a : ColArgs d)

def formModuleEquivAtPlace (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m)
    (v : ((d.colRec a).mem u).A.vT) :
    (classAgreement a hS hH hP u i hi).lev.fM ((atTTied a hH u).eV v).1 ((atTTied a hH u).eV v).2 ≃+ ((d.colRec a).mem u).A.Fv v :=
  tieFMe d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (stepCrd a hS hH u i hi) v

set_option maxHeartbeats 1000000 in

theorem fvTied (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    CF.FvTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (formModuleEquivAtPlace a hS hH hP u i hi) :=
  fun v c z hz =>
    tie_FvTie d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
      (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (stepCrd a hS hH u i hi) v c z hz

end Rec

end Formalism.L2.Col
