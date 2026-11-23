import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalarReps

theorem natCast_isIntegral (n : ℕ) : IsIntegral ℤ (n : ℂ) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (n : ℤ))

theorem dvd_pow_of_primes {c N : ℕ} (hc : c ≠ 0) (hN : N ≠ 0) (h : ∀ p, p.Prime → p ∣ c → p ∣ N) :
    c ∣ N ^ c := by
  rw [← Nat.factorization_le_iff_dvd hc (pow_ne_zero _ hN)]
  intro p
  by_cases hp : p.Prime
  · by_cases hpc : p ∣ c
    · have h1 : 1 ≤ N.factorization p := (hp.dvd_iff_one_le_factorization hN).1 (h p hp hpc)
      have h2 : c.factorization p < c := Nat.factorization_lt p hc
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      nlinarith
    · rw [Nat.factorization_eq_zero_of_not_dvd hpc]; exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]; exact Nat.zero_le _

theorem unitOff_sqrt_of_dvd {c N n : ℕ} (hc : c ≠ 0) (hd : c ∣ N ^ n) :
    UnitOff N ((Real.sqrt (c : ℝ) : ℝ) : ℂ) := by
  set s : ℝ := Real.sqrt (c : ℝ) with hs
  have hpos : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hc)
  have hs2 : s ^ 2 = (c : ℝ) := Real.sq_sqrt hpos.le
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hc2 : ((s : ℂ)) ^ 2 = (c : ℂ) := by
    rw [← Complex.ofReal_pow, hs2]; push_cast; rfl
  have hint : IsIntegral ℤ (s : ℂ) :=
    IsIntegral.of_pow (n := 2) (by norm_num) (by rw [hc2]; exact natCast_isIntegral c)
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0
  obtain ⟨m, hm⟩ := hd
  refine ⟨hsc, n, ((natCast_isIntegral N).pow n).mul hint, ?_⟩
  have e : (N : ℂ) ^ n * (s : ℂ)⁻¹ = (m : ℂ) * (s : ℂ) := by
    have hN : (N : ℂ) ^ n = (s : ℂ) ^ 2 * m := by rw [hc2]; exact_mod_cast hm
    rw [hN]; field_simp
  rw [e]; exact (natCast_isIntegral m).mul hint

theorem exists_reps {G : Type} [AddCommGroup G] (H K : AddSubgroup G) (hKH : K ≤ H) (N : ℕ) (hN : N ≠ 0)
    (hinj : ∀ x y : G, N • x = N • y → x = y) (hNH : ∀ w ∈ H, N • w ∈ K)
    (R : Finset G) (hR : ∀ u ∈ K, ∃ r ∈ R, ∃ v ∈ K, u = r + N • v) :
    ∃ Rr : Finset G, (∀ u ∈ Rr, u ∈ H) ∧ (∀ w ∈ H, ∃! v, v ∈ Rr ∧ w - v ∈ K) ∧
      UnitOff N ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
  classical
  set K' : AddSubgroup H := K.addSubgroupOf H with hK'
  have hmk : ∀ a b : H, (QuotientAddGroup.mk a : H ⧸ K') = QuotientAddGroup.mk b ↔ (b : G) - a ∈ K := by
    intro a b
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simp [sub_eq_neg_add]

  have hlab : ∀ q : H ⧸ K', ∃ r ∈ R, ∃ v ∈ K, N • ((q.out : H) : G) = r + N • v :=
    fun q => hR _ (hNH _ (q.out).2)
  let f : H ⧸ K' → {r // r ∈ R} := fun q => ⟨(hlab q).choose, (hlab q).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro q1 q2 h
    obtain ⟨-, v1, hv1, e1⟩ := (hlab q1).choose_spec
    obtain ⟨-, v2, hv2, e2⟩ := (hlab q2).choose_spec
    have hr : (hlab q1).choose = (hlab q2).choose := congrArg Subtype.val h
    have hN' : N • (((q2.out : H) : G) - (q1.out : H)) = N • (v2 - v1) := by
      rw [smul_sub, smul_sub, e1, e2, hr]; abel
    have := hinj _ _ hN'
    rw [← QuotientAddGroup.out_eq' q1, ← QuotientAddGroup.out_eq' q2]
    exact (hmk _ _).2 (by rw [this]; exact K.sub_mem hv2 hv1)
  haveI : Finite (H ⧸ K') := Finite.of_injective f hf
  haveI : Fintype (H ⧸ K') := Fintype.ofFinite _
  have hout : Function.Injective (fun q : H ⧸ K' => ((q.out : H) : G)) := by
    intro q1 q2 h
    rw [← QuotientAddGroup.out_eq' q1, ← QuotientAddGroup.out_eq' q2]
    exact congrArg _ (Subtype.ext h)
  refine ⟨Finset.univ.image (fun q : H ⧸ K' => ((q.out : H) : G)), ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact (q.out).2
  · intro w hw
    refine ⟨((QuotientAddGroup.mk ⟨w, hw⟩ : H ⧸ K').out : G), ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · have := (hmk _ _).1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk ⟨w, hw⟩ : H ⧸ K'))
      simpa using this
    · rintro v ⟨hv, hwv⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hv
      congr 2
      rw [← QuotientAddGroup.out_eq' q]
      refine (hmk _ _).2 ?_
      exact hwv
  · rw [Finset.card_image_of_injective _ hout, Finset.card_univ]
    set c := Fintype.card (H ⧸ K')
    have hc : c ≠ 0 := Fintype.card_ne_zero
    refine unitOff_sqrt_of_dvd hc (dvd_pow_of_primes hc hN fun p hp hpc => ?_)
    haveI := Fact.mk hp
    obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card p hpc
    rw [← hq]
    apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf]
    simpa using hNH _ (q.out).2

end GlobalTheory.ScalarReps

namespace GlobalTheory.ScalarReps

open GlobalTheory.FinPl.FrameLat in

theorem int_at {D : D7} (P : Pl D.host.E) (ep : AE D) (hep : Formalism.L2.NTheta.IsIdemAt ep P) (N : ℕ)
    (hN : (N : 𝓞 D.host.E) ∈ P.asIdeal) (ϖ : 𝓞 D.host.E) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    finPart D (ep * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) ∈ intAE D := by
  have hv : P.valuation D.host.E ((N : D.host.E) * (ϖ : D.host.E)⁻¹) ≤ 1 := by
    have v1 : P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) :=
      (P.valuation_of_algebraMap ϖ).trans (GlobalTheory.LatIntFacts.intValuation_uniformiser P h1 h2)
    have v2 : P.valuation D.host.E (N : D.host.E) ≤ WithZero.exp (-1 : ℤ) := by
      have e : ((N : 𝓞 D.host.E) : D.host.E) = (N : D.host.E) := by push_cast; rfl
      rw [← e, P.valuation_of_algebraMap]
      have := (P.intValuation_le_pow_iff_mem (N : 𝓞 D.host.E) 1).2 (by simpa using hN)
      simpa using this
    rw [map_mul, map_inv₀, v1]
    calc P.valuation D.host.E (N : D.host.E) * (WithZero.exp (-1 : ℤ))⁻¹
        ≤ WithZero.exp (-1 : ℤ) * (WithZero.exp (-1 : ℤ))⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ (by simp)
  obtain ⟨a, b, hab⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  have hb : (b : 𝓞 D.host.E) ∉ P.asIdeal := b.2
  have hb0 : (b : 𝓞 D.host.E) ≠ 0 := fun h => hb (h ▸ zero_mem _)
  have hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hb0
  have hi : finPart D (ep * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hc
    exact hb ((hep.2 _ hb0).2 hc)
  have hq : (N : D.host.E) * (ϖ : D.host.E)⁻¹ = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hb1]
    exact hab
  have ha : finPart D (incA D (a : D.host.E)) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun v => one_mem _, a, rfl⟩
  have := mul_mem_intAE ha hi
  rw [← RingHom.map_mul, mul_left_comm, ← RingHom.map_mul] at this
  rw [hq]
  exact this

theorem int_sum {D : D7} (Q : Finset (Pl D.host.E)) (e : AE D) (he : IsIdemSum e Q) (N : ℕ)
    (hN : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) (ϖ : 𝓞 D.host.E)
    (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) :
    finPart D (cA D (e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹))) ∈ intAE D := by
  rw [GlobalTheory.FinPl.FrameLat.cA_int_iff]
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul, map_sum]
  exact AddSubgroup.sum_mem _ fun PP hP => int_at PP (es PP) (hes PP hP) N (hN PP hP) ϖ (hϖ PP hP).1 (hϖ PP hP).2

end GlobalTheory.ScalarReps

namespace GlobalTheory.ScalarReps

theorem exists_reps' {G : Type} [AddCommGroup G] (L half : AddSubgroup G) (f : G →+ G) (N : ℕ) (hN : N ≠ 0)
    (hinj : ∀ x y : G, N • x = N • y → x = y) (hfL : ∀ w ∈ L, w ∈ half → f w ∈ L)
    (hNL : ∀ w ∈ half, f w ∈ L → N • w ∈ L) (R : Finset G)
    (hR : ∀ u ∈ L, u ∈ half → ∃ r ∈ R, ∃ v ∈ L, v ∈ half ∧ u = r + N • v) :
    ∃ Rr : Finset G, (∀ u ∈ Rr, f u ∈ L ∧ u ∈ half) ∧ (∀ w, f w ∈ L → w ∈ half → ∃! v, v ∈ Rr ∧ w - v ∈ L) ∧
      UnitOff N ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
  let H : AddSubgroup G := half ⊓ L.comap f
  let K : AddSubgroup G := half ⊓ L
  have hKH : K ≤ H := fun w hw => ⟨hw.1, hfL w hw.2 hw.1⟩
  have hNH : ∀ w ∈ H, N • w ∈ K := fun w hw => ⟨half.nsmul_mem hw.1 N, hNL w hw.1 hw.2⟩
  have hR' : ∀ u ∈ K, ∃ r ∈ R, ∃ v ∈ K, u = r + N • v := by
    intro u hu
    obtain ⟨r, hr, v, hv, hvh, huv⟩ := hR u hu.2 hu.1
    exact ⟨r, hr, v, ⟨hvh, hv⟩, huv⟩
  obtain ⟨Rr, hRr1, hRr2, hRr3⟩ := exists_reps H K hKH N hN hinj hNH R hR'
  refine ⟨Rr, fun u hu => ⟨(hRr1 u hu).2, (hRr1 u hu).1⟩, fun w hw1 hw2 => ?_, hRr3⟩
  obtain ⟨v, ⟨hv, hwv⟩, huniq⟩ := hRr2 w ⟨hw2, hw1⟩
  refine ⟨v, ⟨hv, hwv.2⟩, fun v' hv' => huniq v' ⟨hv'.1, half.sub_mem hw2 (hRr1 v' hv'.1).1, hv'.2⟩⟩

def halfSub {D : D7} (S T : HSp D) (c : AE D) : AddSubgroup (WO S T) where
  carrier := {w | IsHalf c w}
  add_mem' := fun {x y} hx hy i j => by
    show c * (x i j + y i j) = x i j + y i j
    rw [mul_add, hx i j, hy i j]
  zero_mem' := fun i j => by
    show c * (0 : AE D) = 0
    rw [mul_zero]
  neg_mem' := fun {x} hx i j => by
    show c * (-x i j) = -x i j
    rw [mul_neg, hx i j]

theorem mem_halfSub {D : D7} {S T : HSp D} {c : AE D} {w : WO S T} : w ∈ halfSub S T c ↔ IsHalf c w := Iff.rfl

end GlobalTheory.ScalarReps

namespace GlobalTheory.ScalarReps

theorem actO_half {D : D7} (S T : HSp D) (Q : Finset (Pl D.host.E)) (e : AE D) (he : IsIdemSum e Q)
    (ϖ : 𝓞 D.host.E) (z : GA D S)
    (hz : mt S z = Matrix.diagonal (fun _ => e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) +
      (1 - e - cA D e)))
    (w : WO S T) (hw : IsHalf (cA D e) w) : actO S T z⁻¹ 1 w = cA D (incA D (ϖ : D.host.E)) • w := by
  have h0 : e * cA D e = 0 := he.2
  have h1 : cA D e * cA D e = cA D e := by rw [← map_mul, Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_sq he]
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.actO_eq, inv_inv, Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', Matrix.one_mul, hz]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  conv_lhs => rw [← hw i j]
  conv_rhs => rw [← hw i j]
  linear_combination (w i j * (incA D ((ϖ : D.host.E)⁻¹) - 1)) * h0 +
    (w i j * cA D (incA D (ϖ : D.host.E)) - w i j) * h1

theorem natCast_smul_cancel {D : D7} (S T : HSp D) (N : ℕ) (hN : N ≠ 0) (x y : WO S T) (h : N • x = N • y) :
    x = y := by
  have hu : IsUnit ((N : ℕ) : AE D) := by
    have h1 : IsUnit ((N : ℕ) : D.host.E) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hN)
    have h2 := h1.map (incA D)
    rwa [map_natCast] at h2
  ext i j
  have h3 : N • x i j = N • y i j := congrFun (congrFun h i) j
  rw [nsmul_eq_mul, nsmul_eq_mul] at h3
  exact hu.mul_left_cancel h3

theorem half_finite_mod {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (a : AE D) (ha : a * a = a) (k : ℕ) (hk : 0 < k) :
    ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf a u →
      ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf a v ∧ u = r + k • v := by
  obtain ⟨R, hR, h⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg (fun _ => True) k hk
  refine ⟨(hR.image fun r => a • r).toFinset, fun u hu hu' => ?_⟩
  obtain ⟨r, hr, w, hw, h'⟩ := h u hu
  refine ⟨_, (Set.Finite.mem_toFinset _).2 ⟨r, hr, rfl⟩, a • w, GlobalTheory.SplitScalar.idem_smul_mem ha w hw,
    GlobalTheory.SplitScalar.isHalf_smul ha w, ?_⟩
  rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hu', h', smul_add, smul_comm a k w]

theorem scalar_half_reps : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D S, mt S z = Matrix.diagonal (fun _ => e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) → ∃ Rr : Finset (WO S T), (∀ u ∈ Rr, actO S T z⁻¹ 1 u ∈ latAll S T ΛS ΛT ∧ IsHalf (cA D e) u) ∧ (∀ w, actO S T z⁻¹ 1 w ∈ latAll S T ΛS ΛT → IsHalf (cA D e) w → ∃! v, v ∈ Rr ∧ w - v ∈ latAll S T ΛS ΛT) ∧ (∀ w ∈ latAll S T ΛS ΛT, IsHalf (cA D e) w → actO S T z⁻¹ 1 w ∈ latAll S T ΛS ΛT) ∧ UnitOff N ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
  intro D S T ΛS ΛT hS hT Q e he N hN hNQ ϖ hϖ0 hϖ z hz
  have hact : ∀ w : WO S T, IsHalf (cA D e) w → actO S T z⁻¹ 1 w = cA D (incA D (ϖ : D.host.E)) • w :=
    fun w hw => actO_half S T Q e he ϖ z hz w hw

  have hbL : ∀ w ∈ latAll S T ΛS ΛT, cA D (incA D (ϖ : D.host.E)) • w ∈ latAll S T ΛS ΛT := by
    intro w hw
    refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ (cA D (incA D (ϖ : D.host.E))) ?_ w hw
    rw [GlobalTheory.FinPl.FrameLat.cA_int_iff]
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, ϖ, rfl⟩

  have hNL : ∀ w : WO S T, IsHalf (cA D e) w → cA D (incA D (ϖ : D.host.E)) • w ∈ latAll S T ΛS ΛT →
      N • w ∈ latAll S T ΛS ΛT := by
    intro w hw hbw
    have hint := int_sum Q e he N hNQ ϖ hϖ
    have key : cA D (e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) * cA D (incA D (ϖ : D.host.E)) =
        cA D e * (N : AE D) := by
      rw [map_mul, mul_assoc, ← map_mul (cA D), ← map_mul (incA D), mul_assoc,
        inv_mul_cancel₀ hϖ0, mul_one, map_natCast, map_natCast]
    have heq : N • w = cA D (e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) • (cA D (incA D (ϖ : D.host.E)) • w) := by
      ext i j
      show N • w i j = cA D (e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) * (cA D (incA D (ϖ : D.host.E)) * w i j)
      rw [← mul_assoc, key, mul_comm (cA D e), mul_assoc, hw i j, nsmul_eq_mul]
    rw [heq]
    exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hint _ hbw
  let f : WO S T →+ WO S T := DistribMulAction.toAddMonoidHom (WO S T) (cA D (incA D (ϖ : D.host.E)))
  have hf : ∀ w, f w = cA D (incA D (ϖ : D.host.E)) • w := fun w => rfl
  obtain ⟨R, hR⟩ := half_finite_mod S T ΛS ΛT hS hT (cA D e)
    (by rw [← map_mul, Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_sq he]) N (Nat.pos_of_ne_zero hN)
  obtain ⟨Rr, hRr1, hRr2, hRr3⟩ := exists_reps' (latAll S T ΛS ΛT) (halfSub S T (cA D e)) f N hN
    (natCast_smul_cancel S T N hN) (fun w hw hh => by rw [hf]; exact hbL w hw)
    (fun w hh hfw => hNL w hh (by rw [← hf]; exact hfw)) R
    (fun u hu hh => hR u hu hh)
  refine ⟨Rr, fun u hu => ?_, fun w hw1 hw2 => ?_, fun w hw1 hw2 => ?_, hRr3⟩
  · obtain ⟨h1, h2⟩ := hRr1 u hu
    exact ⟨by rw [hact u h2, ← hf]; exact h1, h2⟩
  · exact hRr2 w (by rw [hf, ← hact w hw2]; exact hw1) hw2
  · rw [hact w hw2]; exact hbL w hw1

end GlobalTheory.ScalarReps
