import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelConjBaseLatticeUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitLocalLevelFirstFactorReadsComponentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointUnitaryNormalisesLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLevelCharacterFiniteOrderStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenLevelCutByCosetStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugatedChartDataLocalLevelAtQStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExactOfIsAdelicPointOfFramedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelIffFramesOnPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartCharacterFramesOnPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartClassesBijectiveOrbitsFramedLatticesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartClassStabiliserRationalPartsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetMovesWithFrameChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepPointDeterminedByLatticeInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetsInFramesEqIffReductionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepPointGivenReductionsCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetTwistPrimeEmptyOrCosetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelAtTwistPrimesIsOpenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrimeStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)}

theorem exists_conj_level {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (b : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hbU : b ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL σ J v S.Lb)
    (hbT : ∀ v, (T : 𝓞 F) ∈ v.asIdeal → (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = S.Uloc v)
    (hbO : ∀ v, v ∉ bad → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) :
    ∃ S' : StepLevel F E σ J T f bad, S'.Lb = S.Lb ∧ S'.U = S.U.map (MulAut.conj b).toMonoidHom ∧
      ∀ (x : S'.U) (z : S.U), x.1 = b * z.1 * b⁻¹ → S'.chi x = S.chi z :=
  GlobalTheory.T.exists_stepLevel_conj_baseLatticeUnitary S b hbU hbV hbT hbO

theorem qPi_of_adAt {K : Type} [Field K] {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (P : Q) (hP : conjPrime₂ P.1 ≠ P.1)
    (a : AfE F E) (e : E) (h : adAt F P.1 a = algebraMap E _ e) : qPi q P a = q.phi P e :=
  GlobalTheory.T.splitLocalLevel_firstFactor_reads_component hc n q P hP a e h

theorem k_facts {π : 𝓞 E} (hB : BasePi ST π) (k : GL (Fin n) (AfE F E)) (c : DiaG E ST)
    (hk : ∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n)
    (hT : ∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j))
      (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) :
    k ∈ UAd hc n ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) ∧
    (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      k.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) ∧
    ∀ v, v ∈ plUnder F ST →
      (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map
        (MulAut.conj (bc (prV (E := E) v) k)).toMonoidHom =
      levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) :=
  GlobalTheory.T.admissibleBasePoint_unitary_normalisesLevel hc n hB k c hk hT

theorem qb_chr_root {K : Type} [Field K] (Θ : LevQFam E K n Q) (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ) (P : Q) :
    ∃ m : ℕ, 0 < m ∧ ∀ k, (qbLoc hc Θ hQ hΘ).chr P k ^ m = 1 :=
  GlobalTheory.T.localLevelCharacter_finiteOrder hc Θ hQ hΘ P

theorem thetaOpen_cutQ {K : Type} [Field K] (Θ : LevQFam E K n Q) (hΘ : ThetaOpen Θ) (C : ∀ P : Q, Set (Sp E n))
    (hC : ∀ P : Q, C P = ∅ ∨ ∃ (z : Sp E n) (c : E), c ≠ 0 ∧ C P = {x | c⁻¹ • (x - z) ∈ stdAt E n P.1}) : ThetaOpen (cutQ Θ C) :=
  GlobalTheory.T.openLevel_cutByCosetStabiliser Θ hΘ C hC

theorem chartQ_exists {K : Type} [Field K] (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ}
    (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T)
    (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG)
    (hidx : (baseLb E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f))
    (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ)
    {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hO : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ)
    (b : GL (Fin n) (AfE F E)) (hbU : b ∈ UAd hc n)
    (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST))
    (hbL : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      b.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST))
    (hbT : ∀ v, v ∈ plUnder F ST →
      (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map
        (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom =
      levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v))
    (hbO : ∀ v, v ∉ badQ' (F := F) SG Q → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1)
    (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = badQ' (F := F) SG Q)
    {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E))
    (s : cl → DecoF E n ST SG Q) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n) (hd : ∀ c, FrOver q (y c) (s c))
    (hs : Function.Bijective fun c => (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ))
    (hlat : ∀ c, lat c = (s c).deco.1.L)
    (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c))
    (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × ↥(Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) × ↥Θ.grp, ufGL E n g.1 = γ ∧ g • s c = s c)
    (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1) :
    ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F))
      (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J),
      Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧
      (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
        x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
        ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧
      (∀ c, Function.Injective (SI c)) ∧
      (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧
      lev.Lb = baseLb E n ST ∧ lev.U = (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj b).toMonoidHom ∧
      (∀ (x : lev.U) (z : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q), x.1 = b * z.1 * b⁻¹ →
        lev.chi x = ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q →* ℂˣ) z) ∧
      (∃ m : ℕ, 0 < m ∧ ∀ κ, lev.chi κ ^ m = 1) ∧ (∀ c, (Y c).1 = y c * b⁻¹) ∧ ∀ c a, (SI c a).1 = st c a :=
  GlobalTheory.T.exists_conjugated_chartData_localLevel_at_Q hc n Hw hB hTπ hST hcard hSG hidx lam q hO hQT σ₀ b hbU hbV hbL hbT hbO J hJ bad hb stab lat s y hy hd hs hlat st hinj hr hchr

theorem frExact_of_isPtOf {K : Type} [Field K] {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) : g ∈ UAd hc n ∧ FrExact q g p :=
  GlobalTheory.T.framesExact_of_isAdelicPointOfFramedLattice hc n q hQ h

end Gen

end GlobalTheory.Mem.Col2.ChExM

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section Mid

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

variable [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E)

theorem lev_iffQ (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) (hact : InvActs cq) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)
    (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (hC : bar r = C) (D : ∀ P : Q, Set (Sp X.E n)) (hD : cq r = D)
    (q : QLoc hc n Q (cutQ Θ D)) {g s : GL (Fin n) (AfE X.F X.E)} (hg : g ∈ UAd hc n) (hx : g * s ∈ UAd hc n) (p : DecoF X.E n ST SG Q)
    (e : FrExact q g r.1.1) (e' : FrExact q (g * s) p) :
    s ∈ levUQ hc n ST SG Q (chG Λ C) q ↔
      ∃ κ : FrmG Λ Θ, ufGL X.E n κ.1 = 1 ∧ (ya Λ Θ κ r).1.1 = p ∧ bar (ya Λ Θ κ r) = bar r ∧ cq (ya Λ Θ κ r) = cq r :=
  GlobalTheory.T.chartLevel_iff_frames_onPoints hc cq hact Λ Θ r C hC D hD q hg hx p e e'

theorem chr_eqQ (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y)
    (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (D : ∀ P : Q, Set (Sp X.E n)) (q : QLoc hc n Q (cutQ Θ D))
    {g : GL (Fin n) (AfE X.F X.E)} (z : levUQ hc n ST SG Q (chG Λ C) q) (hg : g ∈ UAd hc n) (κ : FrmG Λ Θ) (h1 : ufGL X.E n κ.1 = 1)
    (e : FrExact q g r.1.1) (e' : FrExact q (g * z.1) (ya Λ Θ κ r).1.1) :
    ((((levTyp (chLam σ Λ C)).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ)⁻¹ : levUQ hc n ST SG Q (chG Λ C) q →* ℂˣ) z : ℂˣ) : ℂ) =
      σ ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K) :=
  GlobalTheory.T.chartCharacter_frames_onPoints hc σ Λ Θ r C D q z hg κ h1 e e'

end Mid

section Orb

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β]
  (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop)
  (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n))

theorem cls_bijQ [NeZero n] (hact : InvActs cq) (hinj : PtDet cq)
    (hsur : ∀ (r : PtY ST SG Q y) (p : DecoF X.E n ST SG Q), ∃ r' : PtY ST SG Q y, r'.1.1 = p ∧ bar r' = bar r ∧ cq r' = cq r)
    (hnorm : ∀ b r r', bar r = bar r' → cq r = cq r' →
      bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')) ∧
      cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')))
    (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop)
    (hp : ∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀) ∧ cq (rp Λ Θ p₀ pref c) = cq (rp Λ Θ p₀ pref c₀)) :
    Function.Bijective fun c : {c // p c} =>
      (Quotient.mk'' (rp Λ Θ p₀ pref c.1).1.1 : DecoFCl (K := X.K) n ST SG Q (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀)))
        (cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀)))) :=
  GlobalTheory.T.chartClasses_bijective_orbits_framedLattices Λ Θ p₀ pref cq hact hinj hsur hnorm c₀ p hp

theorem stM_rangeQ (hact : InvActs cq) (hinj : PtDet cq) (c : (stR Λ Θ p₀ pref).Cl) (b : β) (hb : c.1 = b)
    (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (hC : bar (rp Λ Θ p₀ pref c) = C)
    (D : ∀ P : Q, Set (Sp X.E n)) (hD : cq (rp Λ Θ p₀ pref c) = D) (γ : GL (Fin n) X.E) :
    γ ∈ (stM Λ Θ p₀ pref c).range ↔ ∃ g : UF X.E n × ↥(chG (Λ b) C) × ↥(cutQ (Θ b) D).grp, ufGL X.E n g.1 = γ ∧
      g • (rp Λ Θ p₀ pref c).1.1 = (rp Λ Θ p₀ pref c).1.1 :=
  GlobalTheory.T.chartClassStabiliser_rationalParts Λ Θ p₀ pref cq hact hinj c b hb C hC D hD γ

end Orb

section PtL

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

theorem cqOf_acts (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) :
    InvActs (cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) :=
  GlobalTheory.T.couplingCoset_moves_with_frameChange hd

theorem cqOf_det (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hq : ∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) :
    PtDet (cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) :=
  GlobalTheory.T.stepPoint_determined_by_latticeInvariants hd hq

theorem cosetIn_iff (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hq : ∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) (r r' : PtAt R sel mu cst u j) :
    cosetIn r = cosetIn r' ↔ bar r = bar r' ∧ cqOf r = cqOf r' :=
  GlobalTheory.T.couplingCosetsInFrames_eq_iff_reductions hd hq r r'

theorem exists_pt_inv (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (r : PtAt R sel mu cst u j)
    (p : ChPt (R := R) sel mu u j) : ∃ r' : PtAt R sel mu cst u j, r'.1.1 = p ∧ bar r' = bar r ∧ cqOf r' = cqOf r :=
  GlobalTheory.T.exists_stepPoint_given_reductions_cosets hd r p

theorem cqOf_form (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)) :
    cqOf r P = ∅ ∨ ∃ (z : Sp X.E (R.N j)) (c : X.E), c ≠ 0 ∧ cqOf r P = {x | c⁻¹ • (x - z) ∈ stdAt X.E (R.N j) P.1} :=
  GlobalTheory.T.couplingCoset_twistPrime_empty_or_coset hd r P

end PtL

section Open

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem thetaOpen_levQ (hL : L.Ok Ch sel mu cst G m2) (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (j : ℕ) (b : L.β j) :
    ThetaOpen (L.levQ j b) :=
  GlobalTheory.T.levelAtTwistPrimes_isOpen hL hd j b

end Open

end GlobalTheory.Mem.Col2.ChExM

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section Main

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem trace_not_mem_twistPrime_under (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) : ∀ P : I.Q a, (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal :=
  GlobalTheory.T.memberLevelPrime_not_under_twistPrime I hI hPr u a

theorem lvQ_open (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i < B.R.m) (b : (I.stp u a i).β) : ThetaOpen (lvQ I a i b) := by
  obtain ⟨al, hal⟩ := Option.isSome_iff_exists.1 (b.2.2 hm)
  show ThetaOpen (b.1.elim _ _)
  rw [hal]
  exact thetaOpen_levQ (hI.idx_ok a) (q_disj I hI a) i al

end Main

end GlobalTheory.Mem.Col2.ChExM

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section Main2

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem inv_norm (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β)
    (q q' : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (h : bar q = bar q') (h' : cqOf q = cqOf q') :
    bar (rpT I u a i ((I.stp u a i).cl b q)) = bar (rpT I u a i ((I.stp u a i).cl b q')) ∧
    cqOf (rpT I u a i ((I.stp u a i).cl b q)) = cqOf (rpT I u a i ((I.stp u a i).cl b q')) := by
  have hd := q_disj I hI a
  rw [← cosetIn_iff hd (hqG hPr)]
  by_cases hi : i + 1 = B.R.m
  swap
  · exact cos_of_neT I hi _ _
  have hm := B.R.two_le_m
  have key := @prefRep_normal _ _ _ _ ((I.stp0 u a i).actD b) ⟨cosetIn q⟩ (fun q' => cosetIn q') (I.pref u a i b) fun p =>
    ⟨fun h => h.2.1 hi, fun h => ⟨fun h0 => by omega, fun _ => h, fun h0 => by omega⟩⟩
  refine (key q).trans (Eq.trans ?_ (key q').symm)
  congr 1
  funext r
  refine propext (exists_congr fun g => ?_)
  have : cosetIn (ya (lvG I a i b) (lvQ I a i b) g q) = cosetIn (ya (lvG I a i b) (lvQ I a i b) g q') := by
    rw [cosetIn_iff hd (hqG hPr)]
    refine ⟨?_, ?_⟩
    · funext w
      rw [bar_ya, bar_ya, h]
    · funext P
      rw [cqOf_acts hd, cqOf_acts hd, h']
  exact this ▸ Iff.rfl

end Main2

end GlobalTheory.Mem.Col2.ChExM

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section Main3

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 2000000 in

theorem chart_of (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (Q' : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (hm : i < B.R.m)
    (hQ' : ∀ v, v ∈ Q' ↔ I.UnderQ a v) (k : GA B (B.R.N i))
    (k1 : ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i))
    (k2 : ∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v →
      (a = I.mu0 ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) k = 1)
    (k3 : ∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
      HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N i)).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0))
    (g : (I.stp u a i).Cl → GA B (B.R.N i)) (hg : ∀ c, PtOf (g c) (extTo I.SQ ((I.stp u a i).rep c).1.1))
    (c₀ : (I.stp u a i).Cl) (p : (I.stp u a i).Cl → Prop)
    (hp : ∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rpT I u a i c) = bar (rpT I u a i c₀) ∧ cqOf (rpT I u a i c) = cqOf (rpT I u a i c₀)) :
    ∃ (K : LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q') i hi (fun c : {c // p c} => (I.chain l u a).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)))
      (q : QLoc B.sp.cm (B.R.N i) (I.Q a) (cutQ (lvQ I a i c₀.1) (cqOf (rpT I u a i c₀)))),
      K.lev.Lb = baseLb B.fields.E (B.R.N i) ((B.primes X).vT u) ∧
      (id K.lev.U : Subgroup (GA B (B.R.N i))) =
        (levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i c₀.1) (bar (rpT I u a i c₀))) q).map
          (MulAut.conj k).toMonoidHom ∧
      (∀ (x : K.lev.U) (z : levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i c₀.1) (bar (rpT I u a i c₀))) q),
        (id x.1 : GA B (B.R.N i)) = k * z.1 * k⁻¹ →
        K.lev.chi x = ((levTyp (chLam (X := B.fields) B.embLL (lvG I a i c₀.1) (bar (rpT I u a i c₀)))).comp (Subgroup.inclusion (levUQ_le q _)) *
          (chiQ q _ B.embLL)⁻¹ : levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i c₀.1) (bar (rpT I u a i c₀))) q →* ℂˣ) z) ∧
      (∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) ∧
      (∀ c, (K.y c).1 = g c.1 * k⁻¹) ∧ ∀ c a', (K.stabI c a').1 = (I.stp u a i).gam c.1.1 a'.1 := by
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  obtain ⟨hg1, -, hl⟩ := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z).2.2.2 i hi
  have hf : B.fields.f = B.R.f := (hPr.vT_card u).symm.trans (l.lev u a).card_ST
  have hd := q_disj I hI a
  have hq := hqG hPr
  have hact := cqOf_acts (R := B.R) (cst := I.cst a) (u := u) (j := i) hd
  have hdet := cqOf_det (R := B.R) (cst := I.cst a) (u := u) (j := i) hd hq
  have hO : ThetaOpen (cutQ (lvQ I a i c₀.1) (cqOf (rpT I u a i c₀))) :=
    thetaOpen_cutQ (B.R.N i) _ (lvQ_open I hI u a i hm c₀.1) _ (cqOf_form hd (rpT I u a i c₀))
  have hcj := q_conj I hI a
  let q := qbLoc B.sp.cm (cutQ (lvQ I a i c₀.1) (cqOf (rpT I u a i c₀))) hcj hO
  have k3' : ∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
      HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N i)).1 r j))
      (if j = r then ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) else 0) := fun P r j hr => by
    have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u))) := by
      have h0 : Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u)) ≠ 0 := fun h0 =>
        (basePi_of_ok (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u).conj_notMem P.2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      exact @Ne.isUnit (Res P.1) _ _ h0
    have e : ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) =
        Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) := by
      unfold diaT
      rw [dif_pos hu]
      rfl
    rw [e]
    exact k3 P r j hr
  obtain ⟨hkU, hkV, hkL, hkT⟩ := k_facts (F := B.host.F) (E := B.host.E) B.sp.cm (B.R.N i) (basePi_of_ok hX hPr u) k (diaT (Pr := B.primes X) u) k1 k3'
  have hbad : badQ (I.rec7 l Z) Q' = badQ' (F := B.host.F) (B.primes X).vGs (I.Q a) := by
    refine Set.ext fun v => or_congr (plUnder_vGs (X := B.fields) B.sp.cm hPr v).symm ?_
    refine (hQ' v).trans ⟨?_, ?_⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
    · rintro ⟨P, rfl⟩
      exact ⟨P.1, P.2, rfl⟩
  have hkO : ∀ v, v ∉ badQ' (F := B.host.F) (B.primes X).vGs (I.Q a) → (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1 := by
    intro v hv hT
    rw [← hbad] at hv
    refine k2 v hT (fun h => hv (Or.inr ((hQ' v).2 h))) (Or.inr fun j hj => hv (Or.inl ?_))
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr hj
  have hpt : ∀ c, g c ∈ UAd B.sp.cm (B.R.N i) ∧ FrExact q (g c) (rpT I u a i c).1.1 := fun c =>
    frExact_of_isPtOf B.sp.cm (B.R.N i) q hcj (IsPtOf.of_extTo (q_sub_SQ I a) (Finset.disjoint_right.2 fun P h => hd P h) (hg c))
  obtain ⟨lev, Y, SI, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := chartQ_exists (F := B.host.F) (E := B.host.E) B.sp.cm (B.R.N i)
    (chH (X := B.fields) (lvG I a i c₀.1) (bar (rpT I u a i c₀))) (f := B.R.f)
    (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = B.T u)) (rls_T_notUnder hPr u)
    (hf ▸ colBase_index (X := B.fields) B.sp.cm (B.R.N i) hPr u) (chLam (X := B.fields) B.embLL (lvG I a i c₀.1) (bar (rpT I u a i c₀)))
    q (qbOpen _ _ hcj hO) (trace_not_mem_twistPrime_under I hI hPr u a) B.embLL k hkU hkV hkL hkT hkO
    (gramN (I.rec7 l Z) i hi) hg1 (badQ (I.rec7 l Z) Q') hbad
    (fun c : {c // p c} => (I.stp u a i).Stab c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))
    (fun c => (rpT I u a i c.1).1.1) (fun c => g c.1) (fun c => (hpt c.1).1) (fun c => (hpt c.1).2.over)
    (cls_bijQ (lvG I a i) (lvQ I a i) _ _ _ hact hdet (exists_pt_inv hd) (inv_norm I hI hPr u a i) c₀ p hp)
    (fun c => (hl u a).1 c.1)
    (fun c => stM (lvG I a i) (lvQ I a i) _ _ c.1) (fun c => stM_inj (lvG I a i) (lvQ I a i) _ _ ((l.ch u a).step i) c.1)
    (fun c γ => stM_rangeQ (lvG I a i) (lvQ I a i) _ _ _ hact hdet c.1 c₀.1 ((hp c.1).1 c.2).1 _ ((hp c.1).1 c.2).2.1 _ ((hp c.1).1 c.2).2.2 γ)
    (qb_chr_root B.sp.cm (B.R.N i) _ hcj hO)
  exact ⟨⟨lev, Y, h1, h2, SI, h3, h4⟩, q, h5, h6, h7, h8, h9, h10⟩

end Main3

end GlobalTheory.Mem.Col2.ChExM

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section AutomorphyRankFourMain

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 1000000 in
theorem lev_at (hI : I.Ok) (hPr : (B.primes X).Ok) {u : B.Word} {a : I.ι} {i : ℕ} (c : (I.stp u a i).Cl) (b : (I.stp u a i).β) (hb : c.1 = b)
    (C : ∀ w : (B.primes X).vGs, Set (Fin (B.R.N i) → 𝓞 B.fields.E ⧸ w.1.asIdeal)) (hC : bar (rpT I u a i c) = C)
    (D : ∀ P : I.Q a, Set (Sp B.fields.E (B.R.N i))) (hD : cqOf (rpT I u a i c) = D)
    (q : QLoc B.sp.cm (B.R.N i) (I.Q a) (cutQ (lvQ I a i b) D)) {g s : GA B (B.R.N i)} (hg : g ∈ UAd B.sp.cm (B.R.N i))
    (hx : g * s ∈ UAd B.sp.cm (B.R.N i)) (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i)
    (e : FrExact q g (rpT I u a i c).1.1) (e' : FrExact q (g * s) p) :
    s ∈ levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i b) C) q ↔
      ∃ κ : (I.stp u a i).G c.1, (I.stp u a i).gam c.1 κ = 1 ∧ ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1 = p ∧
        cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) := by
  subst hb
  have hd := q_disj I hI a
  refine (lev_iffQ B.sp.cm cqOf (cqOf_acts hd) (lvG I a i c.1) (lvQ I a i c.1) (rpT I u a i c) C hC D hD q hg hx p e e').trans ?_
  exact exists_congr fun κ => and_congr Iff.rfl (and_congr Iff.rfl (cosetIn_iff hd (hqG hPr) _ _).symm)

set_option maxHeartbeats 1000000 in
theorem chr_at {u : B.Word} {a : I.ι} {i : ℕ} (c : (I.stp u a i).Cl) (b : (I.stp u a i).β) (hb : c.1 = b)
    (C : ∀ w : (B.primes X).vGs, Set (Fin (B.R.N i) → 𝓞 B.fields.E ⧸ w.1.asIdeal))
    (D : ∀ P : I.Q a, Set (Sp B.fields.E (B.R.N i)))
    (q : QLoc B.sp.cm (B.R.N i) (I.Q a) (cutQ (lvQ I a i b) D)) {g : GA B (B.R.N i)}
    (z : levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i b) C) q)
    (hg : g ∈ UAd B.sp.cm (B.R.N i)) (κ : (I.stp u a i).G c.1) (h1 : (I.stp u a i).gam c.1 κ = 1)
    (e : FrExact q g (rpT I u a i c).1.1) (e' : FrExact q (g * z.1) ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1) :
    ((((levTyp (chLam (X := B.fields) B.embLL (lvG I a i b) C)).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ B.embLL)⁻¹ :
      levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i b) C) q →* ℂˣ) z : ℂˣ) : ℂ) =
      B.embLL (((I.stp u a i).chr c.1 κ : B.LLˣ) : B.LL) := by
  subst hb
  have h := chr_eqQ (X := B.fields) B.sp.cm B.embLL (lvG I a i c.1) (lvQ I a i c.1) (rpT I u a i c) C D q z hg κ h1 e e'
  rw [h]
  rfl

set_option maxHeartbeats 2000000 in

theorem exists_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∀ k : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i), GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k → ∃ K : ∀ β : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)), I.Reads u a i (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u a Q i hi _ hm hQ k hk
  have hPr := l.pr
  have hd := q_disj I hI a
  have hq := hqG hPr
  have hcj := q_conj I hI a
  have key : ∀ c c', GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c' ↔
      c.1 = c'.1 ∧ cosetIn ((I.stp u a i).rep c) = cosetIn ((I.stp u a i).rep c') := fun c c' =>
    Subtype.ext_iff.trans Prod.ext_iff
  have onto : Function.Surjective (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) := fun β => ⟨β.2.choose, Subtype.ext β.2.choose_spec⟩
  choose s hs using onto
  have hp : ∀ β c, GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β ↔
      c.1 = (s β).1 ∧ bar (rpT I u a i c) = bar (rpT I u a i (s β)) ∧ cqOf (rpT I u a i c) = cqOf (rpT I u a i (s β)) := fun β c => by
    rw [← cosetIn_iff hd hq]
    conv_lhs => rw [← hs β]
    exact key c (s β)
  choose g hg using fun c : (I.stp u a i).Cl => GlobalTheory.T.exists_adelicPoint_decoratedLattice_allTwists I hI u _ (extTo I.SQ ((I.stp u a i).rep c).1.1)
  choose K q K1 K2 K3 K4 K5 K6 using fun β => chart_of I hI hP l Z u a Q i hi hm hQ (k β) (hk.std β) (hk.off β) (hk.T β) g hg (s β)
    (fun c => GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β) (hp β)
  have hy : ∀ c, (id ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1 : GA B (B.R.N i)) = g c * (k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c))⁻¹ := fun c => K5 _ _
  have hpt : ∀ c, PtOf (g c) ((I.stp u a i).rep c).1.1 := fun c =>
    IsPtOf.of_extTo (q_sub_SQ I a) (Finset.disjoint_right.2 fun P h => hd P h) (hg c)
  have hmove : ∀ c (x : GA B (B.R.N i)), (id ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1 : GA B (B.R.N i)) * x * k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c) =
      g c * ((k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c))⁻¹ * x * k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) := fun c x => by
    rw [hy c]
    group
  have hU : ∀ β (x : GA B (B.R.N i)), x ∈ (id (K β).lev.U : Subgroup (GA B (B.R.N i))) ↔ _ := fun β x =>
    Iff.of_eq (congrArg (fun S : Subgroup (GA B (B.R.N i)) => x ∈ S) (K2 β))
  refine ⟨K, ⟨key, fun β => ⟨_, hs β⟩, fun β x => ?_, hk.std, hk.off, hk.T, fun c => ?_, fun c x r h => ?_, fun c x κ h1 h2 => ?_, fun c a' => K6 _ _ _⟩, K4⟩
  · exact (K1 β ▸ Iff.rfl : x ∈ (K β).lev.Lb ↔ x ∈ baseLb B.fields.E (B.R.N i) ((B.primes X).vT u)).trans (mem_baseLb (B := B) (X := X) hPr u _ x)
  · show PtOf ((id ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1 : GA B (B.R.N i)) * k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) _
    rw [hy c, inv_mul_cancel_right]
    exact hg c
  · have h' : PtOf (g c * ((k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c))⁻¹ * x * k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c))) r := by
      rw [← hmove c x]; exact h
    have e := frExact_of_isPtOf B.sp.cm (B.R.N i) (q (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) hcj (hpt c)
    have e' := frExact_of_isPtOf B.sp.cm (B.R.N i) (q (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) hcj h'
    have hc := (hp (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c) c).1 rfl
    refine ((hU _ x).trans (mem_map_conj _ _ _)).trans ?_
    exact lev_at I hI hPr c _ hc.1 _ hc.2.1 _ hc.2.2 _ e.1 e'.1 r e.2 e'.2
  · have hz := (mem_map_conj _ _ _).1 ((hU _ x.1).1 x.2)
    have h2' : PtOf (g c * ((k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c))⁻¹ * x.1 * k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)))
        ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1 := by
      rw [← hmove c x.1]; exact h2
    have e := frExact_of_isPtOf B.sp.cm (B.R.N i) (q (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) hcj (hpt c)
    have e' := frExact_of_isPtOf B.sp.cm (B.R.N i) (q (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) hcj h2'
    have hc := (hp (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c) c).1 rfl
    have h3 := K3 (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c) x ⟨_, hz⟩ (by simp only [id, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one])
    refine (congrArg Units.val h3).trans ?_
    exact chr_at I c _ hc.1 _ _ _ ⟨_, hz⟩ e.1 κ h1 e.2 e'.2

end AutomorphyRankFourMain

end GlobalTheory.Mem.Col2.ChExM
