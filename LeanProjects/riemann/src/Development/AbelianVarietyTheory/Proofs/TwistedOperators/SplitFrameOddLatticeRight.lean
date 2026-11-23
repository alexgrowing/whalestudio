import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualModulusShiftHalfMemCompletedModulusHom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSmulMemHatLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitComponentIntegerResidueZeroIffMemPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeColumnsOffFiniteSet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.AscFin.FrameBarBF

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k)

theorem tmul_split (x : AF D.host.F) (b : D.host.E) :
    (x ⊗ₜ[D.host.F] b : AE D) = (x ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D b := by
  change _ = (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] b)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem pr_one_int {α : Af D.host.F} (hα : α ∈ intAf D.host.F) :
    p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ 𝒪[k] :=
  GlobalTheory.SplitCharCond.pr_int p (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩)

theorem exists_factor {α : Af D.host.F} (hα : α ∈ intAf D.host.F) : ∃ ε : AE D, cA D ε = ε ∧ p.pr ε ∈ 𝒪[k] ∧
    ∀ b : D.host.E, (pairA D.host.F 0 α ⊗ₜ[D.host.F] b : AE D) = ε * incA D b :=
  ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E), (cA_tmul _ _).trans (by rw [star_one]), pr_one_int p hα,
    fun b => tmul_split _ b⟩

theorem pr_star_int (b : 𝓞 D.host.E) : p.pr (incA D (star (b : D.host.E))) ∈ 𝒪[k] :=
  GlobalTheory.LocMod.FullLatFrame.pr_int_mem p ⟨star (b : D.host.E), Examples₂.star_isIntegral _ b.2⟩

theorem pair_rat_int {T : HSp D} {LT : Lat T} (hT : IsSelfDualC T LT) {P : GlobalTheory.FinPl.Pl D → Prop}
    {t : Fin T.rank → D.host.E} (ht : t ∈ LT) {y : Fin T.rank → AE D} (hy : y ∈ latV T LT P) :
    ∑ j, ∑ l, p.pr (incA D (star (t j))) * p.pr (incA D (T.gram j l)) * p.pr (y l) ∈ 𝒪[k] := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hy
    obtain rfl : a = 1 := ha
    obtain ⟨b, hb⟩ := (hT.2 x).1 hx t ht
    have e : ∑ j, ∑ l, p.pr (incA D (star (t j))) * p.pr (incA D (T.gram j l)) *
        p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x l)) =
        p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * p.pr (incA D (b : D.host.E)) := by
      rw [hb]
      simp only [map_sum, Finset.mul_sum, RingHom.map_mul]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      rw [one_mul, tmul_split _ (x l), RingHom.map_mul]
      ring
    rw [e]
    exact mul_mem (pr_one_int p hα) (GlobalTheory.LocMod.FullLatFrame.pr_int_mem p b)
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, RingHom.map_add, mul_add, Finset.sum_add_distrib]; exact add_mem hx hy
  | neg x _ hx =>
    simp only [Pi.neg_apply, RingHom.map_neg, mul_neg, Finset.sum_neg_distrib]; exact neg_mem hx

set_option maxHeartbeats 800000 in

theorem pair_int {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hA : ∀ a ∈ D.host.AA, p.pr (incA D (star a)) ∈ 𝒪[k]) {P : GlobalTheory.FinPl.Pl D → Prop}
    {u : WO S T} (hu : u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True)
    {x : Fin S.rank → D.host.E} (hx : x ∈ LS) {y : Fin T.rank → AE D} (hy : y ∈ latV T LT P) :
    ∑ j, ∑ l, p.pr (cA D (∑ m, u j m * incA D (x m))) * p.pr (incA D (T.gram j l)) * p.pr (y l) ∈ 𝒪[k] := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    obtain ⟨b, hb⟩ := (hS.2 x).1 hx s hs
    obtain ⟨ε, hε, hε', hs⟩ := exists_factor p hα
    have e : ∀ j, ∑ m, ε * incA D (a * t j * ∑ k, star (s k) * S.gram k m) * incA D (x m) =
        ε * incA D (a * (b : D.host.E) * t j) := fun j => by
      rw [hb, Finset.sum_comm, Finset.mul_sum, Finset.sum_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_assoc, ← RingHom.map_mul, ← Finset.sum_mul]
      congr 2
      ring
    have e2 : ∀ j, p.pr (cA D (ε * incA D (a * (b : D.host.E) * t j))) =
        p.pr ε * p.pr (incA D (star a)) *
          p.pr (incA D (star (b : D.host.E))) * p.pr (incA D (star (t j))) := fun j => by
      rw [(cA D).map_mul, hε, cA_incA, star_mul', star_mul', (incA D).map_mul, (incA D).map_mul, p.pr.map_mul,
        p.pr.map_mul, p.pr.map_mul]
      ring
    simp only [Matrix.of_apply, hs, e, e2]
    have h3 := mul_mem (mul_mem (mul_mem hε' (hA a ha)) (pr_star_int p b)) (pair_rat_int p hT ht hy)
    simp only [Finset.mul_sum] at h3
    simpa only [mul_assoc] using h3
  | zero =>
    have : ∀ j m, (0 : WO S T) j m = 0 := fun _ _ => rfl
    simp only [this, zero_mul, Finset.sum_const_zero, RingHom.map_zero]; exact zero_mem _
  | add u v _ _ hx hy =>
    have : ∀ j m, (u + v) j m = u j m + v j m := fun _ _ => rfl
    simp only [this, RingHom.map_add, add_mul, Finset.sum_add_distrib]; exact add_mem hx hy
  | neg u _ hx =>
    have : ∀ j m, (-u) j m = -u j m := fun _ _ => rfl
    simp only [this, RingHom.map_neg, neg_mul, Finset.sum_neg_distrib]; exact neg_mem hx

def Bd (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (c : k) : Prop :=
  ∀ x ∈ I, ∃ z ∈ 𝒪[k], p.pr (incA D (star x)) = c * z

variable {p}

theorem Bd.mul {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {c d : k} (h : Bd p I c) (h' : Bd p J d) :
    Bd p (I * J) (c * d) := fun x hx => by
  refine FractionalIdeal.mul_induction_on (C := fun x => ∃ z ∈ 𝒪[k], p.pr (incA D (star x)) = c * d * z) hx ?_ ?_
  · intro a ha b hb
    obtain ⟨z, hz, e⟩ := h a ha
    obtain ⟨z', hz', e'⟩ := h' b hb
    exact ⟨z * z', mul_mem hz hz', by rw [star_mul', RingHom.map_mul, RingHom.map_mul, e, e']; ring⟩
  · rintro a b ⟨z, hz, e⟩ ⟨z', hz', e'⟩
    exact ⟨z + z', add_mem hz hz', by rw [star_add, RingHom.map_add, RingHom.map_add, e, e']; ring⟩

theorem Bd.one : Bd p 1 1 := fun x hx => by
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  exact ⟨_, pr_star_int p o, (one_mul _).symm⟩

theorem Bd.pow {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {c : k} (h : Bd p I c) (n : ℕ) : Bd p (I ^ n) (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Bd.one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem exists_inv {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w) {c : 𝓞 D.host.E}
    (hc : c ∉ w.asIdeal) : ∃ z ∈ 𝒪[k], p.pr (incA D (c : D.host.E)) * z = 1 := by
  obtain ⟨h, e⟩ := GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff p w hw c
  have hu : IsUnit (⟨_, h⟩ : 𝒪[k]) := by
    by_contra hn
    exact hc (e.1 ((IsLocalRing.residue_eq_zero_iff _).2 hn))
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

theorem Bd.inv {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w)
    {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {c : 𝓞 D.host.E} (hc : c ∉ w.asIdeal) (hI : star (c : D.host.E) ∈ I) :
    Bd p I⁻¹ 1 := fun x hx => by
  obtain ⟨y, hy, e⟩ := exists_inv hw hc
  have h0 : I ≠ 0 := fun h => by
    rw [h, FractionalIdeal.mem_zero_iff, star_eq_zero] at hI
    rw [hI, RingHom.map_zero, RingHom.map_zero, zero_mul] at e
    exact zero_ne_one e
  have h1 := FractionalIdeal.mul_mem_mul hx hI
  rw [inv_mul_cancel₀ h0] at h1
  obtain ⟨z, hz, e'⟩ := Bd.one (p := p) _ h1
  rw [star_mul', star_star, RingHom.map_mul, RingHom.map_mul, one_mul] at e'
  refine ⟨z * y, mul_mem hz hy, ?_⟩
  rw [← e', one_mul, mul_assoc, e, mul_one]

theorem int_of_val {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w) {x : D.host.E}
    (hx : w.valuation D.host.E x ≤ 1) : p.pr (incA D x) ∈ 𝒪[k] := by
  obtain ⟨n, d, e⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  obtain ⟨y, hy, e'⟩ := exists_inv hw (c := d) d.2
  have h1 := GlobalTheory.LocMod.FullLatFrame.pr_int_mem p n
  have h2 : (n : D.host.E) = x * ((d : 𝓞 D.host.E) : D.host.E) := e.symm
  rw [h2, RingHom.map_mul, RingHom.map_mul] at h1
  have h3 := mul_mem h1 hy
  rwa [mul_assoc, e', mul_one] at h3

theorem pow_bd {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w) {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ)
    (n : ℕ) {c : 𝓞 D.host.E} (hc : c ∈ w.asIdeal ^ n) : ∃ z ∈ 𝒪[k], p.pr (incA D (c : D.host.E)) = (ϖ : k) ^ n * z := by
  let f : 𝓞 D.host.E →+* 𝒪[k] := ((p.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[k]
    fun o => GlobalTheory.LocMod.FullLatFrame.pr_int_mem p o
  have h1 : w.asIdeal.map f ≤ Ideal.span {ϖ} := by
    rw [← hϖ.maximalIdeal_eq, Ideal.map_le_iff_le_comap]
    intro o ho
    obtain ⟨h, e⟩ := GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff p w hw o
    exact (IsLocalRing.residue_eq_zero_iff _).1 (e.2 ho)
  have h2 : f c ∈ Ideal.span {ϖ ^ n} := by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono h1 n (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem f hc)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h2
  refine ⟨z, z.2, ?_⟩
  have := congrArg Subtype.val hz
  change (z : k) * ((ϖ ^ n : 𝒪[k]) : k) = p.pr (incA D (c : D.host.E)) at this
  rw [← this, mul_comm, SubmonoidClass.coe_pow]

theorem bd_of_mul {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (h0 : I ≠ 0) {c V : k} (h : Bd p I⁻¹ c)
    (hV : ∀ s ∈ I, p.pr (incA D (star s)) * V ∈ 𝒪[k]) : ∃ z ∈ 𝒪[k], V = c * z := by
  have h1 : (1 : D.host.E) ∈ I * I⁻¹ := by rw [mul_inv_cancel₀ h0]; exact FractionalIdeal.one_mem_one _
  have key : ∃ z ∈ 𝒪[k], p.pr (incA D (star (1 : D.host.E))) * V = c * z := by
    refine FractionalIdeal.mul_induction_on (C := fun x => ∃ z ∈ 𝒪[k], p.pr (incA D (star x)) * V = c * z) h1 ?_ ?_
    · intro a ha b hb
      obtain ⟨z, hz, e⟩ := h b hb
      exact ⟨_, mul_mem (hV a ha) hz, by rw [star_mul', (incA D).map_mul, p.pr.map_mul, e]; ring⟩
    · rintro a b ⟨z, hz, e⟩ ⟨z', hz', e'⟩
      exact ⟨z + z', add_mem hz hz', by rw [star_add, (incA D).map_add, p.pr.map_add, add_mul, e, e']; ring⟩
  rwa [star_one, RingHom.map_one, RingHom.map_one, one_mul] at key

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem star_eq (x : D.host.E) : star x = D.host.conj x := bridge_star_holds D.R D.host x

theorem aa_int (hO : OffQ D) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0)
    (hw : Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v)) {a : D.host.E} (ha : a ∈ D.host.AA ∨ a ∈ D.host.AAbar) :
    p.pr (incA D (star a)) ∈ 𝒪[k] := by
  refine int_of_val hw (GlobalTheory.FunObj.Good.valuation_le_one_of_mem
    (GlobalTheory.HalfOut.two_q_notMem hO G ((GlobalTheory.DepthFix.mem_orthogonal_frame_iff G).2 ⟨v, hv, rfl⟩)) ?_)
  rw [star_eq]
  exact ha.symm.imp (Formalism.L2.Pj.conj_mem_AA D) (Formalism.L2.Pj.conj_mem_AAbar D)

theorem stair_bd (hO : OffQ D) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0)
    (hw : Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v)) {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) (c : ℕ) (q : Fin c) :
    stairId (G.pl.stA sc) (G.pl.stAbar sc) c q ≠ 0 ∧
      Bd p (stairId (G.pl.stA sc) (G.pl.stAbar sc) c q)⁻¹ ((ϖ : k) ^ (G.pl.depth sc v * (c - q.1))) := by
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal := fun h =>
    GlobalTheory.AAUnit.absNorm_cmIdeal_not_mem_gridPlaces G.pl hv (by
      rw [← G.pl.under_w hv]
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ (G.pl.w v).asIdeal
      rwa [map_natCast])
  have hNA := GlobalTheory.HostClear.absNorm_mem_AA D
  have hN0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hA : D.host.AA ≠ 0 := fun h => by
    rw [h, FractionalIdeal.mem_zero_iff] at hNA; exact hN0 hNA
  have hAb : D.host.AAbar ≠ 0 := fun h => by
    have := Formalism.L2.Pj.conj_mem_AAbar D hNA
    rw [h, FractionalIdeal.mem_zero_iff, map_natCast] at this; exact hN0 this
  have hm : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hmb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact GlobalTheory.AscFin.PrimStd.modulBar_ne_bot G.pl sc
  refine ⟨mul_ne_zero (pow_ne_zero _ (mul_ne_zero hA (inv_ne_zero hmb)))
    (inv_ne_zero (pow_ne_zero _ (mul_ne_zero hAb (inv_ne_zero hm)))), ?_⟩
  have b1 : Bd p D.host.AA⁻¹ 1 := Bd.inv hw hN (by
    have : (((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) : D.host.E) = ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) :=
      map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _
    rw [this, star_natCast]; exact hNA)
  have hcc : ∀ o : 𝓞 D.host.E, star ((D.host.conj • o : 𝓞 D.host.E) : D.host.E) = (o : D.host.E) := fun o => by
    rw [star_eq]
    exact (congrArg D.host.conj (Formalism.L2.Pj.algebraMap_conj_smul D o)).trans (Formalism.L2.Pj.conj_conj D _)
  have hex : ∀ o ∈ G.pl.modulBar sc, ∃ o' ∈ G.pl.modul sc, D.host.conj • o' = o := fun o ho =>
    ⟨_, Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 ho, smul_inv_smul _ _⟩
  have b2 : Bd p ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
      ((ϖ : k) ^ G.pl.depth sc v) := fun x hx => by
    obtain ⟨o, ho, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    obtain ⟨o', ho', rfl⟩ := hex o ho
    have hle : G.pl.modul sc ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := by
      unfold Places.modul
      exact Ideal.prod_le_inf.trans (Finset.inf_le hv)
    obtain ⟨z, hz, e⟩ := pow_bd hw hϖ _ (hle ho')
    exact ⟨z, hz, by rw [← e, ← hcc o']⟩
  have b3 : Bd p D.host.AAbar 1 := fun x hx => ⟨_, aa_int hO G hv hw (Or.inr hx), (one_mul _).symm⟩
  have b4 : Bd p ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ 1 := by
    obtain ⟨o, ho, hw'⟩ := GlobalTheory.DepthBig.exists_modulBar_notMem G hv
    obtain ⟨o', ho', rfl⟩ := hex o ho
    refine Bd.inv hw hw' ?_
    rw [hcc]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨o', ho', rfl⟩
  have b := ((b1.mul b2).pow (c - q.1)).mul ((b3.mul b4).pow (q.1 + 1))
  rw [one_mul, one_mul, one_pow, mul_one, ← pow_mul] at b
  have e : (stairId (G.pl.stA sc) (G.pl.stAbar sc) c q)⁻¹ =
      (D.host.AA⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ^ (c - q.1) *
      (D.host.AAbar * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹) ^ (q.1 + 1) := by
    simp only [stairId, Places.stA, Places.stAbar, mul_inv, inv_inv, ← inv_pow]
  rw [e]
  exact b

theorem latO_of_latRow (G : GridData L sc) (i : ℕ) {Y : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))} (hY : Y ∈ latRow G i) :
    Y ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _)
      fun _ => True := hY.1

set_option maxHeartbeats 1600000 in

theorem bessel_step_conj_place_column_functional_bound : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v →
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  Irreducible ϖ →
  Function.Injective κ →
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) →
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) →
  ∀ t : Fin (σ + 1) → k, (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1) →
  ∀ a ∈ (pcBF W F (σ + 1) h).A₁, ∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v,
    (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i := by
  intro D hO T L μ0 hL sc G W M hM F hF σ h v hv k _ _ _ _ p β ϖ κ h1 h2 h3 h4 h5 h6 h7 t ht a ha q i
  have hq := q.2
  obtain ⟨_, eV, -⟩ := hF.hB (σ + 1) h
  obtain ⟨_, eW, -⟩ := hF.hJ (σ + 1) h
  set dV := G.colDec (2 * (σ + 1) + 2) (by omega) h with hdV
  set dW := G.colDec (2 * (σ + 1) + 1) (by omega) (by omega) with hdW
  set ξ : k := p.pr (incA D (star ((-D.host.xi0) ^ (q.1 + 1)))) with hξ
  let qV : Fin (2 * (σ + 1) + 2 - 1) := ⟨q.1, by omega⟩
  let qW : Fin (2 * (σ + 1) + 1 - 1) := ⟨q.1, by omega⟩
  let r : Fin (2 * (σ + 1) + 1 - 1) := ⟨2 * (σ + 1) - 1 - q.1, by omega⟩

  have ht1 : t q * (ξ * (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1))) = 1 := by
    have a1 := congrFun (ht q) (κ r)
    rw [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul] at a1
    rw [← a1]
    congr 1
    have g := congrFun (congrFun dW.gram qW) r
    have g1 : antiDiagonalSignGramMatrix (2 * (σ + 1) + 1 - 1) (-1 : D.host.E) qW r = 1 := by
      simp only [antiDiagonalSignGramMatrix]
      rw [if_pos (by simp only [qW, r]; omega), if_neg (fun e => by have := congrArg Fin.val e; simp only [qW, r] at this; omega)]
    rw [g1] at g
    have g2 : ∑ l, (∑ j, star (dW.a j qW) * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram j l) * dW.a l r = 1 := g
    have g3 := congrArg (fun c => p.pr (incA D c)) g2
    simp only [map_sum, RingHom.map_mul, RingHom.map_one, Finset.sum_mul] at g3
    have x1 : ∀ j, p.pr (cA D (xZero (F.dJ (σ + 1) h) j q)) = ξ * p.pr (incA D (star (dW.a j qW))) := fun j => by
      have : xZero (F.dJ (σ + 1) h) j q = incA D ((-D.host.xi0) ^ (q.1 + 1) * dW.a j qW) := by
        change incA D ((F.dJ (σ + 1) h).e j q) = _
        rw [eW]; rfl
      rw [this, cA_incA, star_mul', (incA D).map_mul, p.pr.map_mul]
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.map_apply, x1, h6, Finset.mul_sum]
    rw [← mul_one (ξ * _), ← g3, Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

  let u : WO (G.V (.grid (2 * (σ + 1) + 2) 0)) (G.V (.grid (2 * (σ + 1) + 1) 0)) := (F.dB (σ + 1) h).extX _ a
  have hu0 : u ∈ latRow G (2 * (σ + 1) + 1) := AddSubgroup.mem_comap.1 ha
  have hu1 : u ∈ latO (negSp (G.V (.grid (2 * (σ + 1) + 2) 0))) (G.V (.grid (2 * (σ + 1) + 1) 0))
      (G.Λ (.grid (2 * (σ + 1) + 2) 0) : Set _) (G.Λ (.grid (2 * (σ + 1) + 1) 0) : Set _) fun _ => True :=
    latO_of_latRow G (2 * (σ + 1) + 1) hu0
  have hcol : ∀ j, a j q = incA D ((-D.host.xi0) ^ (q.1 + 1)) * ∑ m, u j m * incA D (dV.a m qV) := fun j => by
    have a1 : HMul.hMul (HMul.hMul a (F.dB (σ + 1) h).pX) (F.dB (σ + 1) h).jX = a := by
      rw [Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
    rw [← congrFun (congrFun a1 j) q, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : (F.dB (σ + 1) h).jX m q = incA D ((-D.host.xi0) ^ (q.1 + 1) * dV.a m qV) := by
      change incA D ((F.dB (σ + 1) h).e m q) = _
      rw [eV]; rfl
    rw [this, (incA D).map_mul, mul_left_comm]
    rfl
  have hS : IsSelfDualC _ (G.Λ (.grid (2 * (σ + 1) + 2) 0)) :=
    (G.isV (X := .grid (2 * (σ + 1) + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j e => by cases e)).sd
  have hT : IsSelfDualC _ (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (G.isV (X := .grid (2 * (σ + 1) + 1) 0) ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e)).sd
  have hy := (h3 (Pi.single i 1)).1 (fun l _ => by
    by_cases e : l = i
    · subst e; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne e]; exact zero_mem _)
  have l1 : G.Λ (.grid (2 * (σ + 1) + 2) 0) = dV.lat (G.Λ (.core (2 * (σ + 1) + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 2 - 1)) := G.sp.colLat (2 * (σ + 1) + 2) (by omega) h
  set V : k := ∑ j, ∑ l, p.pr (cA D (∑ m, u j m * incA D (dV.a m qV))) *
    p.pr (incA D ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram j l)) * β.b l i with hV
  obtain ⟨s0, sb⟩ := stair_bd hO G hv h2 h4 (2 * (σ + 1) + 2 - 1) qV
  obtain ⟨z, hz, ez⟩ := bd_of_mul (V := V) s0 sb fun s hs => by
    have hx : (fun m => s * dV.a m qV) ∈ G.Λ (.grid (2 * (σ + 1) + 2) 0) := by
      rw [l1]
      refine ⟨0, zero_mem _, Pi.single qV s, fun n => ?_, ?_⟩
      · by_cases e : n = qV
        · subst e; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne e]; exact FractionalIdeal.zero_mem _
      · funext m
        rw [mulVec_zero, zero_add, GlobalTheory.StairCols.mulVec_single_apply, mul_comm]
    have a1 := pair_int p (isSelfDualC_neg hS) hT (fun a ha => aa_int hO G hv h2 (Or.inl ha)) hu1 hx hy
    convert a1 using 1
    rw [hV]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    have a2 : ∑ m, u j m * incA D (s * dV.a m qV) = incA D s * ∑ m, u j m * incA D (dV.a m qV) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [(incA D).map_mul, mul_left_comm]
    rw [a2, (cA D).map_mul, cA_incA, p.pr.map_mul, p.pr_sec, mulVec_single_one]
    simp only [Matrix.col, Matrix.transpose_apply, mul_assoc]
  have hval : ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i = ξ * V := by
    rw [hV]
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hcol j, (cA D).map_mul, cA_incA, p.pr.map_mul]
    ring
  refine ⟨ϖ ^ G.pl.depth sc v * ⟨z, hz⟩, Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow h4.not_isUnit _), ?_⟩
  have hn : 2 * (σ + 1) + 2 - 1 - qV.1 = (r.1 + 1) + 1 := by simp only [qV, r]; omega
  rw [hval, ez, hn, mul_add _ (r.1 + 1), mul_one, pow_add]
  change (ϖ : k) ^ G.pl.depth sc v * z = _
  linear_combination (-((ϖ : k) ^ G.pl.depth sc v * z)) * ht1

end GlobalTheory.AscFin.FrameBarBF
