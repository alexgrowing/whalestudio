import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelDatumReferenceTupleSmallField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TranslateSumVacuumMovedByAdelicPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetIffMaximalLevelCongruentConjIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTopOfOneMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise
open scoped nonZeroDivisors

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SkewLevel

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem conj_ne_bot (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) :
    D.host.conj • modul P c ≠ ⊥ := fun h => modul_ne_bot P c (by rw [← conj_conj_smul (modul P c), h, Ideal.smul_bot])

theorem conj_conj_ne_bot (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) :
    D.host.conj • D.host.conj • modul P c ≠ ⊥ := by
  rw [conj_conj_smul]
  exact modul_ne_bot P c

theorem kill (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {I : Ideal (𝓞 D.host.E)} {y u : WO S T}
    (hy : ∀ m ∈ I, incA D (m : D.host.E) • y ∈ latO S T LS LT (fun _ => True)) (hu : u ∈ latO S T LS LT (fun _ => True))
    {b : 𝓞 D.host.E} (hb : b ∈ D.host.conj • I) : ψ (symplO S T (incA D (b : D.host.E) • u) y) = 1 := by
  rw [GlobalTheory.PlaceModel.symplO_smul, cA_incA_int]
  exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hu (hy _ (mem_conj_smul.1 hb))

theorem smul_finRat_mem (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (P : Finset (Formalism.L2.DIV.Pl D.host.E))
    (c : Formalism.L2.DIV.Pl D.host.E → ℕ) {z : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hz : z ∈ YYl D (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)) :
    ∀ m ∈ modul P c, incA D (m : D.host.E) • GlobalTheory.VacUnique.finRat S T z ∈ latO S T LS LT (fun _ => True) := fun m hm => by
  rw [smul_finRat, finRat_mem_iff hψ hcc gS hLS hLT hS hT]
  exact smul_skew_mem (conj_conj_ne_bot P c) hz (by rwa [conj_conj_smul])

theorem kill_of_inId (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P) {I : Ideal (𝓞 D.host.E)} {t y : WO S T}
    (ht : IsHalf (cA D e) t) (hI : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • I) (toEAf D (t i j)))
    (hy : ∀ m ∈ I, incA D (m : D.host.E) • y ∈ latO S T LS LT (fun _ => True)) : ψ (symplO S T t y) = 1 := by
  obtain ⟨hinf, hint, -⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props _ _ (fun _ => 0) (GlobalTheory.RefDatumLev.isIdemSum_conjPl he.1)
  have hee : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he.1]
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (D.host.conj • I))
  have hfI : ∀ k, f k ∈ D.host.conj • I := fun k => hf ▸ Submodule.subset_span ⟨k, rfl⟩
  have hc : ∀ i j, ∃ c : Fin n → Formalism.L2.Theta.AE D, (∀ k, toEAf D (c k) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      toEAf D (t i j) = ∑ k, toEAf D (incA D (f k : D.host.E)) * toEAf D (c k) := fun i j => by
    obtain ⟨h1, h2⟩ := hI i j
    have e1 : Formalism.L2.DIV.idS D.host.F (D.host.conj • I) =
        Ideal.span (Set.range fun k => Formalism.L2.DIV.oToS D.host.F D.host.E (f k)) := by
      rw [Formalism.L2.DIV.idS, ← hf]
      refine (Ideal.map_span _ _).trans ?_
      rw [← Set.range_comp]
      rfl
    rw [e1, Ideal.mem_span_range_iff_exists_fun] at h2
    obtain ⟨r, hr⟩ := h2
    choose c hc using fun k => toEAf_surj (D := D) (r k : EAf D)
    refine ⟨c, fun k => hc k ▸ (r k).2, ?_⟩
    have h3 := congrArg (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype hr
    rw [map_sum] at h3
    refine h3.symm.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, hc, mul_comm]
    rfl
  choose c hc1 hc2 using hc
  let u : Fin n → WO S T := fun k => Matrix.of fun i j => cA D e * c i j k
  have hu1 : ∀ k, IsHalf (cA D e) (u k) := fun k i j => by
    change cA D e * (cA D e * c i j k) = cA D e * c i j k
    rw [← mul_assoc, hee]
  have hu2 : ∀ k, u k ∈ latO S T LS LT (fun _ => True) := fun k =>
    (half_mem_iff hcc hLS hLT hS hT he _ (hu1 k)).2 fun i j => by
      change toEAf D (cA D e * c i j k) ∈ _
      rw [RingHom.map_mul]
      exact mul_mem hint (hc1 i j k)
  have hent : ∀ i j, (∑ k, incA D (f k : D.host.E) • u k) i j = cA D e * ∑ k, incA D (f k : D.host.E) * c i j k :=
    fun i j => by
      rw [Matrix.sum_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
  have e2 : t = ∑ k, incA D (f k : D.host.E) • u k := half_ext hinf ht
    (fun i j => by rw [hent, ← mul_assoc, hee]) fun i j => by
      rw [hent, ← ht i j, RingHom.map_mul, RingHom.map_mul, hc2, map_sum]
      simp only [RingHom.map_mul]
  rw [e2]
  exact Finset.sum_induction _ (fun t => ψ (symplO S T t y) = 1)
    (fun a b ha hb => by rw [GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, ha, hb, one_mul])
    (by rw [GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one]) fun k _ => kill hψ hS hT hy (hu2 k) (hfI k)

theorem inId_of_kill (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) {t : WO S T}
    (ht : IsHalf (cA D e) t) (htΛ : t ∈ latO S T LS LT (fun _ => True))
    (hk : ∀ z ∈ YYl D (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank),
      ψ (symplO S T t (GlobalTheory.VacUnique.finRat S T z)) = 1) (i j) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • modul P c) (toEAf D (t i j)) := by
  have hN : 0 < Ideal.absNorm (D.host.conj • D.host.conj • modul P c) :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (conj_conj_ne_bot P c))
  have h1 : ∀ s ∈ (((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      (D.host.conj • D.host.conj • modul P c : Ideal (𝓞 D.host.E))),
      toEAf D (incA D (star s) * t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun s hs => by
    have hh : IsHalf (cA D e) (incA D (star s) • t) := fun i j => by
      change cA D e * (incA D (star s) * t i j) = incA D (star s) * t i j
      rw [mul_left_comm, ht]
    refine (half_mem_iff hcc hLS hLT hS hT he _ hh).1 ?_ i j
    refine ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1 _ (Matrix.ext fun i j => ?_)).2 fun u hu => ?_
    · have : infPart D (t i j) = 0 := congrFun (congrFun (GlobalTheory.VacUnique.latO_inf S T _ _ _ htΛ) i) j
      change infPart D (incA D (star s) * t i j) = 0
      rw [RingHom.map_mul, this, mul_zero]
    · obtain ⟨γ, hγ, v, hv, rfl⟩ := approx hψ hcc gS hLS hLT hS hT hN hu
      obtain ⟨b, -, hb⟩ := mul_mem_of_skew (conj_conj_ne_bot P c) hs (Ideal.absNorm_mem _)
      have e1 : incA D s • Ideal.absNorm (D.host.conj • D.host.conj • modul P c) • v = incA D (b : D.host.E) • v := by
        rw [hb, mul_comm, RingHom.map_mul, mul_smul]
        congr 1
        rw [← Nat.cast_smul_eq_nsmul (Formalism.L2.Theta.AE D)]
        congr 1
        exact (map_natCast ((incA D).comp (algebraMap (𝓞 D.host.E) D.host.E)) _).symm
      rw [GlobalTheory.PlaceModel.symplO_smul, GlobalTheory.DualPairCheck.cA_incA, star_star, smul_add, GlobalTheory.PlaceModel.symplO_add_right,
        AddChar.map_add_eq_mul, smul_finRat, hk _ (smul_mem_skew _ hs hγ), one_mul, e1]
      exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT htΛ (GlobalTheory.VacSign.smul_mem_latO b hv)
  have h2 : ∀ r ∈ ((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • modul P c) (toEAf D (incA D (star r) * t i j)) := fun r hr => by
    rw [← div_mul_cancel₀ ((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
      (FractionalIdeal.coeIdeal_ne_zero.2 (conj_conj_ne_bot P c))] at hr
    refine FractionalIdeal.mul_induction_on hr (fun s hs m hm => ?_) fun x y hx hy => ?_
    · obtain ⟨m, hm', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
      have e1 : star (s * algebraMap (𝓞 D.host.E) D.host.E m) = ((D.host.conj • m : 𝓞 D.host.E) : D.host.E) * star s := by
        rw [star_mul, star_eq (algebraMap (𝓞 D.host.E) D.host.E m)]
        rfl
      rw [e1, RingHom.map_mul (incA D), mul_assoc]
      exact inId_mul (mem_conj_smul.1 hm') (h1 s hs)
    · rw [star_add, RingHom.map_add, add_mul, RingHom.map_add]
      exact inId_add hx hy
  obtain ⟨b, hb, a, ha, hab⟩ := Ideal.isCoprime_iff_exists.1 (isCoprime_conj he.1 c)
  have h3 := h2 _ (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.smul_mem_pointwise_smul D.host.conj _ _ ha))
  have e2 : star (algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • a)) = (a : D.host.E) := by
    change star (D.host.conj (a : D.host.E)) = _
    rw [← star_eq, star_star]
  have e3 : t i j = incA D (b : D.host.E) * t i j + incA D (a : D.host.E) * t i j := by
    have : (b : D.host.E) + (a : D.host.E) = 1 := by exact_mod_cast congrArg (algebraMap (𝓞 D.host.E) D.host.E) hab
    rw [← add_mul, ← RingHom.map_add, this, RingHom.map_one, one_mul]
  rw [e2] at h3
  rw [e3, RingHom.map_add]
  exact inId_add (inId_mul hb ((half_mem_iff hcc hLS hLT hS hT he _ ht).1 htΛ i j)) h3

theorem heisO_eq_half (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) {vac : WO S T → ℂ}
    (hvac : IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac) {z : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hz : z ∈ YYl D (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)) :
    heisO ψ S T (e • GlobalTheory.VacUnique.finRat S T (2 • z)) vac = heisO ψ S T (GlobalTheory.VacUnique.finRat S T (2 • z)) vac := by
  have hee : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hy := smul_finRat_mem hψ hcc gS hLS hLT hS hT P c (nsmul_mem hz 2)
  have hl : (1 - e) • GlobalTheory.VacUnique.finRat S T z ∈ latO S T LS LT (fun _ => True) :=
    GlobalTheory.AdTh.MovedSum.one_sub_smul_mem_latO_pow S T _ _ e P he _ fun s hs => ⟨∑ w ∈ P, c w,
      smul_finRat_mem hψ hcc gS hLS hLT hS hT P c hz _ (by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Ideal.prod_mem_prod fun w hw => Ideal.pow_mem_pow (hs w hw) _)⟩
  have e0 : cA D e • (1 - e) • GlobalTheory.VacUnique.finRat S T z = cA D e • GlobalTheory.VacUnique.finRat S T z := by
    rw [smul_smul, mul_sub, mul_comm (cA D e) e, he.2, sub_zero, mul_one]
  have hl' : cA D e • GlobalTheory.VacUnique.finRat S T z ∈ latO S T LS LT (fun _ => True) :=
    e0 ▸ GlobalTheory.PlaceModelSum.idem_smul_latO hee hl
  obtain ⟨b, hb, a, ha, hab⟩ := Ideal.isCoprime_iff_exists.1 (isCoprime_conj he c)
  have hA : ∀ w ∈ AddSubgroup.closure {w : Matrix (Fin T.rank) (Fin S.rank) D.host.E |
      ∃ s ∈ (((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
        (D.host.conj • D.host.conj • modul P c : Ideal (𝓞 D.host.E))),
        ∃ γ ∈ YYl D (stdL D S.rank) (stdL D T.rank), w = s • γ},
      ψ (symplO S T (incA D (a : D.host.E) • cA D e • GlobalTheory.VacUnique.finRat S T w) (GlobalTheory.VacUnique.finRat S T (2 • z))) = 1 := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨s, hs, γ, hγ, rfl⟩ := hw
      obtain ⟨b', hb', e1⟩ := mul_mem_of_skew (conj_conj_ne_bot P c) hs (m := a) (by rwa [conj_conj_smul])
      rw [smul_comm, smul_finRat, smul_smul, ← e1, ← smul_finRat, smul_comm]
      exact kill hψ hS hT hy (GlobalTheory.PlaceModelSum.idem_smul_latO hee ((finRat_mem_iff hψ hcc gS hLS hLT hS hT _).2 hγ)) hb'
    | zero => rw [map_zero, smul_zero, smul_zero, GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one]
    | add x y _ _ hx hy =>
      rw [map_add, smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, hx, hy, one_mul]
    | neg x _ hx =>
      have h := AddChar.map_zero_eq_one ψ
      rw [← GlobalTheory.PlaceModel.symplO_zero_left S T (GlobalTheory.VacUnique.finRat S T (2 • z)),
        ← add_neg_cancel (incA D (a : D.host.E) • cA D e • GlobalTheory.VacUnique.finRat S T x), GlobalTheory.PlaceModel.symplO_add_left,
        AddChar.map_add_eq_mul, hx, one_mul] at h
      rwa [map_neg, smul_neg, smul_neg]
  have hB : ψ (symplO S T (cA D e • GlobalTheory.VacUnique.finRat S T z) (GlobalTheory.VacUnique.finRat S T (2 • z))) = 1 := by
    have : (b : D.host.E) + (a : D.host.E) = 1 := by exact_mod_cast congrArg (algebraMap (𝓞 D.host.E) D.host.E) hab
    rw [← one_smul (Formalism.L2.Theta.AE D) (cA D e • GlobalTheory.VacUnique.finRat S T z), ← RingHom.map_one (incA D), ← this,
      RingHom.map_add, add_smul, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, kill hψ hS hT hy hl' hb,
      hA z (skew_mem_closure _ hz), one_mul]
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  have hC : symplOH S T (e • GlobalTheory.VacUnique.finRat S T (2 • z)) (2 • (1 - e) • GlobalTheory.VacUnique.finRat S T z) =
      -symplO S T (cA D e • GlobalTheory.VacUnique.finRat S T z) (GlobalTheory.VacUnique.finRat S T (2 • z)) := by
    rw [symplOH, two_nsmul ((1 - e) • GlobalTheory.VacUnique.finRat S T z), GlobalTheory.PlaceModel.symplO_add_right,
      GlobalTheory.PlaceModel.symplO_smul, e0, ← GlobalTheory.PlaceModel.symplO_skew, ← two_mul, ← mul_assoc, h2, one_mul]
  have h := GlobalTheory.LatVac.heisO_heisO ψ (e • GlobalTheory.VacUnique.finRat S T (2 • z)) (2 • (1 - e) • GlobalTheory.VacUnique.finRat S T z) vac
  rw [hvac.1 _ hl, hC, AddChar.map_neg_eq_inv, hB, inv_one, one_smul] at h
  rw [h, map_nsmul, smul_comm 2 (1 - e), ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.SkewLevel

end
