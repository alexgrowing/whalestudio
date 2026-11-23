import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProof
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeCharSplitSupportedEqProdResidue

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist

open GlobalTheory.ExportSeries
open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes (pS qS aP aM dShift)

section Wt

variable (D : D7) (i : Fin D.R.m)

def liftC (τ : D.what₂.Tau) : ℤ := ⌊dShift D i τ⌋

theorem liftC_cast (τ : D.what₂.Tau) :
    (liftC D i τ : ℚ) = ((pS D i τ : ℚ) - (qS D i τ : ℚ)) / 2 - (D.hc τ).e i - 1 / 2 := by
  obtain ⟨z, hz⟩ := (GlobalTheory.PairWeightArith.arithAt D i τ).d_int
  rw [liftC, hz, Int.floor_intCast, ← hz, dShift]

def liftWeight : Weight D (Vc D i).rank where
  p := pS D i
  q := qS D i
  ap := aP D i
  am := aM D i
  c := liftC D i
  lam := lamV D i

theorem liftWeight_good : (liftWeight D i).Good where
  le τ := by
    obtain ⟨h1, h2⟩ := (GlobalTheory.PairWeightArith.arithAt D i τ).rank
    change pS D i τ + qS D i τ ≤ _
    omega
  lam_eq τ a := by
    have h := GlobalTheory.PairWeightArith.arithAt D i τ
    obtain ⟨h1, h2⟩ := h.rank
    obtain ⟨z, hz⟩ := h.d_int
    have h3 := h.coef_eq a
    have ha := a.2
    have hc : liftC D i τ = z := by rw [liftC, hz, Int.floor_intCast]
    rw [hz] at h3
    have h4 : (lamV D i τ).w a = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.thetaWt D i τ a + z := by exact_mod_cast h3
    change (lamV D i τ).w a = (if a.val < pS D i τ then (aP D i τ a : ℤ) else
      if (Vc D i).rank - qS D i τ ≤ a.val then -(aM D i τ ((Vc D i).rank - 1 - a) : ℤ) else 0) + liftC D i τ
    rw [h4, hc, GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.thetaWt]
    congr 1
    by_cases k1 : a.val < pS D i τ
    · rw [if_pos k1, if_pos k1]
    · rw [if_neg k1, if_neg k1]
      by_cases k2 : a.val < pS D i τ + D.R.t
      · rw [if_pos k2, if_neg (by omega)]
      · rw [if_neg k2, if_pos (by omega)]
        congr 3
        omega

theorem liftWeight_delta : (liftWeight D i).delta (Wc D i).rank = RealDat.Delta i := rfl

end Wt

section Res

variable {D : D7}

theorem map_loc {M N : Type} [CommRing M] [CommRing N] (f : M →+* N) (e a : M) :
    f (1 + e * (a - 1)) = 1 + f e * (f a - 1) := by
  rw [map_add, map_mul, map_sub, map_one]

structure IsLocUnit (PP : Pl D.host.E) (u : (kP PP)ˣ) (x : (AE D)ˣ) : Prop where
  off : (1 - idemAt PP) * (x : AE D) = 1 - idemAt PP
  inf : infPart D (x : AE D) = 1
  int : finPart D (x : AE D) ∈ intAE D
  int' : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D
  res : ∃ hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP ⟨_, hx⟩ = u

set_option maxHeartbeats 800000 in

theorem exists_isLocUnit {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) (u : (kP PP)ˣ) :
    ∃ x : (AE D)ˣ, IsLocUnit PP u x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP PP)
  have := PP.isPrime
  have haP : a ∉ PP.asIdeal := fun h0 => u.ne_zero (ha ▸ Ideal.Quotient.eq_zero_iff_mem.2 h0)
  have ha1 : a ≠ 0 := fun h0 => haP (h0 ▸ zero_mem _)
  have ha0 : (a : D.host.E) ≠ 0 := fun h0 => ha1 (RingOfIntegers.coe_eq_zero_iff.1 h0)
  have hinf : infPart D (idemAt PP) = 0 :=
    GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨idemAt, by simpa using h, by simp⟩, h.1.2.1⟩
  have hai : finPart D (idemAt PP * incA D ((a : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra k
    exact haP ((h.2 a ha1).2 k)
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP h
  have he : idemAt PP * idemAt PP = idemAt PP := h.1.1
  have hm : incA D (a : D.host.E) * incA D ((a : D.host.E)⁻¹) = 1 := by
    rw [← RingHom.map_mul, mul_inv_cancel₀ ha0, RingHom.map_one]
  have hb : toEAf D (incA D (a : D.host.E)) = ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  generalize incA D (a : D.host.E) = b at hm hb
  generalize incA D ((a : D.host.E)⁻¹) = b' at hm hai
  have hmul : (1 + idemAt PP * (b - 1)) * (1 + idemAt PP * (b' - 1)) = 1 := by
    linear_combination (b - 1) * (b' - 1) * he + idemAt PP * hm
  have hv : toEAf D (1 + idemAt PP * (b - 1)) =
      ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [map_loc, hb]
    rfl
  have hx : toEAf D (1 + idemAt PP * (b - 1)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hv]
    exact Subtype.property _
  refine ⟨⟨_, _, hmul, by rw [mul_comm]; exact hmul⟩, ?_, ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hx, ?_, hx, ?_⟩
  · change (1 - idemAt PP) * (1 + idemAt PP * (b - 1)) = _
    linear_combination (1 - b) * he
  · change infPart D (1 + idemAt PP * (b - 1)) = 1
    rw [map_loc, hinf, zero_mul, add_zero]
  · change finPart D (1 + idemAt PP * (b' - 1)) ∈ intAE D
    have e1 : finPart D (1 + idemAt PP * (b' - 1)) = finPart D (1 - idemAt PP) + finPart D (idemAt PP * b') := by
      rw [← RingHom.map_add]
      congr 1
      ring
    rw [e1]
    refine add_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D _ ?_) hai
    rw [← RingHom.map_mul]
    congr 1
    linear_combination he
  · have e2 : (⟨_, hx⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) :=
      Subtype.ext hv
    refine (congrArg (resS D.host.F PP) e2).trans ?_
    rw [map_loc, h1, resS_oToS, ha]
    ring

theorem IsLocUnit.eq {M : Type} [CommGroup M] {χ : (AE D)ˣ →* M} {PP : Pl D.host.E} {c : (kP PP)ˣ →* M}
    (h : IsResAt χ PP c) {u : (kP PP)ˣ} {x : (AE D)ˣ} (hx : IsLocUnit PP u x) : χ x = c u :=
  hx.res.elim fun h2 h3 => h x hx.off h2 u h3

theorem isResAt_unique {M : Type} [CommGroup M] {χ : (AE D)ˣ →* M} {PP : Pl D.host.E}
    (h : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) {c c' : (kP PP)ˣ →* M} (hc : IsResAt χ PP c) (hc' : IsResAt χ PP c') :
    c = c' := by
  ext1 u
  obtain ⟨x, hx⟩ := exists_isLocUnit h u
  rw [← hx.eq hc, hx.eq hc']

theorem IsLocUnit.eq_one {M : Type} [CommGroup M] {χ : (AE D)ˣ →* M} {Q P : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q)
    (hP : SplitSet P) (hQ : Q ⊆ P) {PP : Pl D.host.E} (hPP : PP ∈ P) (hn : PP ∉ Q) {u : (kP PP)ˣ} {x : (AE D)ˣ}
    (hx : IsLocUnit PP u x) : χ x = 1 := by
  refine hχ x hx.inf hx.int hx.int' ?_
  have h0 : idemAt PP * (idem Q + cA D (idem Q)) = 0 := by
    rw [mul_add, idem, map_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_eq_zero fun j hj => hP.mul_eq_zero hPP (hQ hj) fun e => hn (e ▸ hj),
      Finset.sum_eq_zero fun j hj => hP.mul_conj hPP (hQ hj), add_zero]
  linear_combination (idem Q + cA D (idem Q)) * hx.off + ((x : AE D) - 1) * h0

theorem eq_res_of_chrEq {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) {PP : Pl D.host.E}
    (h : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) (ht : χ.TameAt PP) {ρ : (kP PP)ˣ →* ℂˣ} (hρ : IsRes χ PP ρ) (x : (AE D)ˣ)
    (hx : (1 - idemAt PP) * (x : AE D) = 1 - idemAt PP) (hi : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (u : (kP PP)ˣ) (hu : resS D.host.F PP ⟨_, hi⟩ = u) : ((c x : Circle) : ℂ) = ((ρ u : ℂˣ) : ℂ) := by
  classical
  have := GlobalTheory.TameSplitChar.char_eq_prod_res D c χ {PP} (idemAt PP) (Function.update (fun _ => 1) PP ρ) hc
    ⟨⟨idemAt, by simpa using h, by simp⟩, h.1.2.1⟩ (by simpa using ⟨ht, hρ⟩) x x ⟨_, hi⟩ (Function.update (fun _ => 1) PP u)
    (by linear_combination hx) rfl (by simpa using hu.symm)
  simpa using this

def toCircle {M : Type} [Group M] [Finite M] (c : M →* ℂˣ) : M →* Circle where
  toFun u := ⟨((c u : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (Complex.norm_eq_one_of_pow_eq_one (n := Nat.card M)
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]) Nat.card_pos.ne')⟩
  map_one' := Circle.ext (by simp)
  map_mul' u v := Circle.ext (congrArg Units.val (map_mul c u v))

@[simp] theorem coe_toCircle {M : Type} [Group M] [Finite M] (c : M →* ℂˣ) (u : M) :
    ((toCircle c u : Circle) : ℂ) = ((c u : ℂˣ) : ℂ) := rfl

theorem toUnits_comp_toCircle {M : Type} [Group M] [Finite M] (c : M →* ℂˣ) : Circle.toUnits.comp (toCircle c) = c :=
  MonoidHom.ext fun _ => Units.ext rfl

end Res

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

structure BaseOf (B : Base (Vc D i) (Wc D i)) : Prop where
  ψ : B.F.ψ = R.ψ
  θ : B.F.θ = R.θ
  sT : B.F.sT = cart (R.MW i (sg0 D A))
  BS : ∀ τ, (B.F.BS τ).val = R.BV i τ
  BT : B.F.BT = onb (R.MW i (sg0 D A))
  ΛS : B.F.ΛS = R.ΛV i
  ΛT : B.F.ΛT = R.ΛW i
  βS : B.F.βS = R.βV i
  βT : B.F.βT = R.βW i
  vac : B.F.f₀ = R.vacP i
  Pg : B.G.Pg = R.Pg
  mu0 : B.mu0 = R.mu0 ((i : ℕ) + 1)
  eta : B.eta = R.eta
  lam : B.w.lam = lamV D i
  delta : B.w.delta (Wc D i).rank = RealDat.Delta i

  p : B.w.p = pS D i
  q : B.w.q = qS D i

  c : B.w.c = liftC D i

variable {i}

open Classical in

def IsTupOf (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle) (t : T0) : Prop :=
  R.xi t = B.de.chi * ψ.chi ∧ R.Q t = B.de.Q ∪ ψ.Q

def ConjChar (τ : ℂ ≃+* ℂ) (ψ ψ' : Twist D Circle) : Prop :=
  ψ'.Q = ψ.Q ∧ ∀ x, ((ψ'.chi x : Circle) : ℂ) = τ ((ψ.chi x : Circle) : ℂ)

def FixDat {S T : HSp D} (B : Base S T) (τ : ℂ ≃+* ℂ) : Prop :=
  (∀ x, τ ((B.de.chi x : Circle) : ℂ) = ((B.de.chi x : Circle) : ℂ)) ∧
    (∀ p, τ ((B.G.P.chi p : ℂˣ) : ℂ) = ((B.G.P.chi p : ℂˣ) : ℂ)) ∧
    ∀ PP ∈ B.G.Pg, ∀ u, τ ((B.G.mu PP u : Circle) : ℂ) = ((B.G.mu PP u : Circle) : ℂ)

theorem conjTup_of {B : Base (Vc D i) (Wc D i)} {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} {t t' : T0} (h : IsTupOf R B ψ t)
    (h' : IsTupOf R B ψ' t') (hc : ConjChar τ ψ ψ') (hf : FixDat B τ) : ConjTup R τ t t' := by
  refine ⟨by rw [h.2, h'.2, hc.1], fun x => ?_⟩
  rw [h.1, h'.1]
  simp only [MonoidHom.mul_apply, Circle.coe_mul, map_mul, hf.1, hc.2]

theorem ConjChar.symm {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (h : ConjChar τ ψ ψ') : ConjChar τ.symm ψ' ψ :=
  ⟨h.1.symm, fun x => by rw [h.2, RingEquiv.symm_apply_apply]⟩

theorem FixDat.symm {S T : HSp D} {B : Base S T} {τ : ℂ ≃+* ℂ} (h : FixDat B τ) : FixDat B τ.symm :=
  ⟨fun x => τ.symm_apply_eq.2 (h.1 x).symm, fun p => τ.symm_apply_eq.2 (h.2.1 p).symm,
    fun PP hPP u => τ.symm_apply_eq.2 (h.2.2 PP hPP u).symm⟩

theorem FixDat.conjChar {S T : HSp D} {B : Base S T} {τ : ℂ ≃+* ℂ} (h : FixDat B τ) : ConjChar τ B.de B.de :=
  ⟨rfl, fun x => (h.1 x).symm⟩

theorem ConjChar.res {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (h : ConjChar τ ψ ψ') (hψ : ψ.Good) (hψ' : ψ'.Good)
    {PP : Pl D.host.E} (hPP : PP ∈ ψ.Q) (u : (kP PP)ˣ) : ((ψ'.res PP u : Circle) : ℂ) = τ ((ψ.res PP u : Circle) : ℂ) := by
  obtain ⟨x, hx⟩ := exists_isLocUnit (hψ.split.isIdemAt hPP) u
  rw [← hx.eq (hψ.res PP hPP), ← hx.eq (hψ'.res PP (h.1 ▸ hPP)), h.2]

variable {R}

namespace BaseOf

variable {B : Base (Vc D i) (Wc D i)} (h : BaseOf R i B)
include h

theorem exponent (τ : D.what₂.Tau) : (B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2 = -(D.hc τ).e i := by
  rw [h.c, h.p, h.q, liftC_cast]
  ring

theorem fock_eq (f : WO (Vc D i) (Wc D i) → ℂ) : B.F.fock f =
    pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f := by
  rw [Frame.fock, h.ψ, h.θ, h.sT, h.BT, funext h.BS]

theorem series_eq_ser (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Vc D i))
    (w : (R.cV i).W) : series B.F (R.ωP i t) f g (R.ioP i (PiTensorProduct.tprod ℂ u) w) = ser R i t f u g w := by
  funext x
  rw [series_apply, h.fock_eq]
  rfl

theorem mu_mul {ψ : Twist D Circle} {t : T0} (ht : IsTupOf R B ψ t) : B.mu * ψ.chi = R.toLevCh.mu t ((i : ℕ) + 1) := by
  rw [Base.mu, h.mu0, mul_assoc, ← ht.1]
  rfl

theorem isWeil (hω : R.thP_ωP) {ψ : Twist D Circle} {t : T0} (ht : IsTupOf R B ψ t) : B.IsWeil ψ.chi (R.ωP i t) := by
  rw [Base.IsWeil, h.mu_mul ht, h.ψ, h.eta]
  exact hω i t

theorem muC_eq {t₀ : T0} (hL : R.toLevCh.Is t₀) (hB : B.Good) {PP : Pl D.host.E} (hPP : PP ∈ R.Pg) :
    B.G.muC PP = (R.chi ((i : ℕ) + 1) PP)⁻¹ := by
  obtain ⟨P, h1, h2, hP⟩ := hB.places.split
  have hg : PP ∈ B.G.Pg := h.Pg ▸ hPP
  refine MonoidHom.ext fun u => Units.ext ?_
  obtain ⟨x, hx⟩ := exists_isLocUnit (hP.isIdemAt (h1 hg)) u
  have e1 := hx.eq (hB.tame PP hg)
  have e2 := hx.eq_one hB.de.unram hP h2 (h1 hg) (Finset.disjoint_left.1 hB.places.disj hg)
  obtain ⟨k1, k2⟩ := hx.res
  have e3 := eq_res_of_chrEq (hL.mu0 i) (hP.isIdemAt (h1 hg)) ((R.C.isMu0 i).tame PP) (hL.chi i PP hPP) x hx.off k1 u k2
  rw [Base.mu, MonoidHom.mul_apply, e2, mul_one, h.mu0] at e1
  rw [← e3, e1]
  rfl

theorem fix_mu {t₀ : T0} (hL : R.toLevCh.Is t₀) (hB : B.Good) {τ : ℂ ≃+* ℂ}
    (hτ : ∀ PP ∈ R.Pg, ∀ u, τ ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) = ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ)) :
    ∀ PP ∈ B.G.Pg, ∀ u, τ ((B.G.mu PP u : Circle) : ℂ) = ((B.G.mu PP u : Circle) : ℂ) := by
  intro PP hPP u
  have hg : PP ∈ R.Pg := h.Pg ▸ hPP
  have e : ((B.G.mu PP u : Circle) : ℂ) = ((R.chi ((i : ℕ) + 1) PP u⁻¹ : ℂˣ) : ℂ) := by
    rw [map_inv, ← MonoidHom.inv_apply, ← h.muC_eq hL hB hg]
    rfl
  rw [e, hτ PP hg]

end BaseOf

theorem IsTupOf.xiR_eq {B : Base (Vc D i) (Wc D i)} {ψ : Twist D Circle} {t t₀ : T0} (ht : IsTupOf R B ψ t)
    (hL : R.toLevCh.Is t₀) (hB : B.Good) (hψ : ψ.Good) (hQ : B.admitted ψ.Q) {PP : Pl D.host.E} (hPP : PP ∈ R.Q t) :
    R.xiR t PP = B.de.locC PP * ψ.locC PP := by
  classical
  obtain ⟨P, -, h2, hP⟩ := hQ.1.split
  have hm : PP ∈ B.de.Q ∨ PP ∈ ψ.Q := by simpa [ht.2] using hPP
  have s1 : B.de.Q ⊆ P := fun a ha => h2 (by simp [ha])
  have s2 : ψ.Q ⊆ P := fun a ha => h2 (by simp [ha])
  have hp : PP ∈ P := hm.elim (fun k => s1 k) fun k => s2 k
  refine MonoidHom.ext fun u => Units.ext ?_
  obtain ⟨x, hx⟩ := exists_isLocUnit (hP.isIdemAt hp) u
  obtain ⟨k1, k2⟩ := hx.res
  have key : ∀ {ν : Twist D Circle}, ν.Good → ν.Q ⊆ P → ((ν.chi x : Circle) : ℂ) = ((ν.locC PP u : ℂˣ) : ℂ) := by
    intro ν hν hs
    unfold Twist.locC
    split_ifs with k
    · rw [hx.eq (hν.res PP k)]
      rfl
    · rw [hx.eq_one hν.unram hP hs hp k]
      rfl
  rw [← eq_res_of_chrEq (hL.xi t) (hP.isIdemAt hp) (hL.xi_tame t PP) (hL.xiR t PP hPP) x hx.off k1 u k2, ht.1,
    MonoidHom.mul_apply, MonoidHom.mul_apply, Circle.coe_mul, Units.val_mul, key hB.de s1, key hψ s2]

variable (R)

def tupTwist (t : T0) : Twist D Circle := ⟨R.Q t, R.xi t, fun PP => toCircle (R.xiR t PP)⟩

theorem isResAt_tupTwist {t₀ : T0} (hL : R.toLevCh.Is t₀) (t : T0) {PP : Pl D.host.E} (hPP : PP ∈ R.Q t)
    (h : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) : IsResAt (tupTwist R t).chi PP ((tupTwist R t).res PP) :=
  fun x hx hi u hu => Circle.ext (eq_res_of_chrEq (hL.xi t) h (hL.xi_tame t PP) (hL.xiR t PP hPP) x hx hi u hu)

theorem isUnit_of_isONBasis {k p : ℕ} {J s B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis J s B p) : IsUnit B := by
  obtain ⟨ε, h1, h2, -⟩ := h
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  have := congrArg Matrix.det h2
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at this
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 this.symm
  rcases h1 a with k | k <;> simp [k.1] at ha

variable (i) in

def baseAt (hB : R.models_BV) (δ : Twist D Circle) (P : LevelP R.Pg (Wc D i).rank ℂ) : Base (Vc D i) (Wc D i) where
  hr := (rank_Wc i).trans_le (r_le_V i)
  F := ⟨R.ψ, R.θ, cart (R.MW i (sg0 D A)), fun τ => (isUnit_of_isONBasis (hB i τ)).unit, onb (R.MW i (sg0 D A)),
    R.ΛV i, R.ΛW i, R.βV i, R.βW i, R.vacP i⟩
  G := ⟨R.Pg, P, fun PP => toCircle (R.chi ((i : ℕ) + 1) PP)⁻¹⟩
  de := δ
  w := liftWeight D i
  mu0 := R.mu0 ((i : ℕ) + 1)
  eta := R.eta

theorem baseOf_baseAt (hB : R.models_BV) (δ : Twist D Circle) (P : LevelP R.Pg (Wc D i).rank ℂ) :
    BaseOf R i (baseAt R i hB δ P) :=
  ⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem isTupOf_baseAt (hB : R.models_BV) (t₀ : T0) (P : LevelP R.Pg (Wc D i).rank ℂ) :
    IsTupOf R (baseAt R i hB (tupTwist R t₀) P) (Twist.triv Circle ∅) t₀ :=
  ⟨(mul_one _).symm, by classical exact (Finset.union_empty _).symm.trans (by congr)⟩

theorem isTupOf_tupTwist (hB : R.models_BV) (t : T0) (P : LevelP R.Pg (Wc D i).rank ℂ) :
    IsTupOf R (baseAt R i hB (Twist.triv Circle ∅) P) (tupTwist R t) t :=
  ⟨(one_mul _).symm, by classical exact (Finset.empty_union _).symm.trans (by congr)⟩

example (hB : R.models_BV) (hω : R.thP_ωP) (t₀ : T0) (P : LevelP R.Pg (Wc D i).rank ℂ) :
    (baseAt R i hB (tupTwist R t₀) P).IsWeil 1 (R.ωP i t₀) :=
  (baseOf_baseAt R hB _ P).isWeil hω (isTupOf_baseAt R hB t₀ P)

example (ψ : Twist D Circle) : ConjChar (starRingAut : ℂ ≃+* ℂ) ψ ⟨ψ.Q, ψ.chi⁻¹, fun PP => (ψ.res PP)⁻¹⟩ :=
  ⟨rfl, fun x => Circle.coe_inv_eq_conj (ψ.chi x)⟩

example (τ : D.what₂.Tau) (a : Fin (Vc D i).rank) (h1 : pS D i τ ≤ a.val) (h2 : a.val + qS D i τ < (Vc D i).rank) :
    (lamV D i τ).w a = liftC D i τ := by
  have h := (liftWeight_good D i).lam_eq τ a
  rw [if_neg (show ¬ a.val < (liftWeight D i).p τ from not_lt.2 h1),
    if_neg (show ¬ (Vc D i).rank - (liftWeight D i).q τ ≤ a.val from by change ¬ _ - qS D i τ ≤ _; omega), zero_add] at h
  exact h

end GlobalTheory.ConjTwist
