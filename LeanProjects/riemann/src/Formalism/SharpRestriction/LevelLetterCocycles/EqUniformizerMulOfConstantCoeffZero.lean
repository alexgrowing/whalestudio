import Formalism.SharpRestriction.LevelLetterCocycles.HermFlagUnipotentAnisotropicVectorSubMem
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ResiduePi0EqNegPrime
import Formalism.SharpRestriction.LevelLetterCocycles.CompleteOfPow

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open PowerSeries in

def ιS (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : PowerSeries O →ₐ[O] PowerSeries O :=
  PowerSeries.substAlgHom (R := O) (PowerSeries.HasSubst.of_constantCoeff_zero'
    (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR))

theorem ιS_apply (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (F : PowerSeries O) :
    ιS W hR F = PowerSeries.subst W.π₀₁ F := by
  rw [ιS, PowerSeries.coe_substAlgHom]

theorem ιS_X (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : ιS W hR PowerSeries.X = W.π₀₁ := by
  rw [ιS_apply]; exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero'
    (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR))

theorem rep (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {g : LetA O n} (hg : g ∈ W.AΔ) :
    ∃ F : ZMod n → PowerSeries O, ∀ i, g i = ιS W hR (F i) := by
  obtain ⟨F, hF, -⟩ := hR.2.1 g hg
  exact ⟨F, fun i => by rw [hF i, ιS_apply]; rfl⟩

theorem const_mem (o : ZMod n → O) : (fun i => PowerSeries.C (o i) : LetA O n) ∈ W.AΔ := by
  intro δ _
  funext i
  show W.γ₀ δ (PowerSeries.C (o i)) = PowerSeries.C (o i)
  exact (W.γ₀ δ).commutes (o i)

theorem eq_uniformizer_mul_of_constantCoeff_zero [IsDomain O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {a : LetA O n} (ha : a ∈ W.AΔ)
    (h0 : ∀ i, PowerSeries.constantCoeff (a i) = 0) : ∃ r ∈ W.AΔ, a = W.π₀ * r := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  obtain ⟨F, hF⟩ := rep W hR ha
  have hF0 : ∀ i, PowerSeries.constantCoeff (F i) = 0 := by
    intro i
    rw [← Formalism.MainNotions.UnusedSlot80.ToolsR.cc_subst (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR), ← ιS_apply W hR, ← hF i]
    exact h0 i
  choose F' hF' using fun i => PowerSeries.X_dvd_iff.mpr (hF0 i)
  have he : a = W.π₀ * fun i => ιS W hR (F' i) := by
    funext i
    rw [hF i, hF' i, map_mul, ιS_X]
    rfl
  refine ⟨_, Formalism.MainNotions.LiftingTheory.lifta_divΔ W _ _ hLR.πΔ hLR.πU (he ▸ ha), he⟩

theorem Gd01 : (Gd (O := O) PD.p 0 1) = PowerSeries.X + ((PD.p : ℕ) : PowerSeries O) := by
  simp [Gd]

theorem ιS_qp (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (i : ZMod n) :
    Formalism.MainNotions.LiftingTheory.qp W i = ιS W hR (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) := by
  rw [map_add, ιS_X, map_natCast]
  rfl

theorem res_decomp [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    {g : LetA O n} (hg : g ∈ W.AΔ) :
    ∃ (o : ZMod n → O) (g' : LetA O n), g' ∈ W.AΔ ∧
      g = (fun i => PowerSeries.C (o i)) + Formalism.MainNotions.LiftingTheory.qp W * g' := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  obtain ⟨F, hF⟩ := rep W hR hg
  choose Q R hQR hRd using fun i => wdiv hlm 0 1 (F i)
  have hRc : ∀ i, (R i : PowerSeries O) = PowerSeries.C ((R i).coeff 0) := by
    intro i
    have h1 : (R i).degree ≤ 0 := Nat.WithBot.lt_one_iff_le_zero.mp (by simpa using hRd i)
    conv_lhs => rw [Polynomial.eq_C_of_degree_le_zero h1]
    simp
  have he : g = (fun i => PowerSeries.C ((R i).coeff 0)) + Formalism.MainNotions.LiftingTheory.qp W * fun i => ιS W hR (Q i) := by
    funext i
    rw [Pi.add_apply, Pi.mul_apply, hF i, hQR i, Gd01, map_add, map_mul, ← ιS_qp, hRc i]
    rw [show ιS W hR (PowerSeries.C ((R i).coeff 0)) = PowerSeries.C ((R i).coeff 0) from
      (ιS W hR).commutes _]
    ring
  refine ⟨_, _, Formalism.MainNotions.LiftingTheory.lifta_divΔ W _ _ (Formalism.MainNotions.LiftingTheory.lifta_qΔ W hLR.πΔ) hLR.qU ?_, he⟩
  have : Formalism.MainNotions.LiftingTheory.qp W * (fun i => ιS W hR (Q i)) = g - fun i => PowerSeries.C ((R i).coeff 0) := by
    rw [he]; ring
  rw [this]
  exact W.AΔ.sub_mem hg (const_mem W _)

theorem res_unique [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (o : ZMod n → O) {g : LetA O n} (hg : g ∈ W.AΔ)
    (h : (fun i => PowerSeries.C (o i) : LetA O n) = Formalism.MainNotions.LiftingTheory.qp W * g) : o = 0 := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  obtain ⟨G, hG⟩ := rep W hR hg
  have ha : (fun i => PowerSeries.C (o i) : LetA O n) ∈ W.AΔ := const_mem W o
  obtain ⟨f0, -, huniq⟩ := hR.2.1 _ ha
  have h1 : ∀ i, (fun i => PowerSeries.C (o i) : LetA O n) i =
      PowerSeries.subst (W.π₀ i) (PowerSeries.C (o i)) := by
    intro i
    show PowerSeries.C (o i) = PowerSeries.subst W.π₀₁ (PowerSeries.C (o i))
    rw [← ιS_apply W hR]
    exact ((ιS W hR).commutes _).symm
  have h2 : ∀ i, (fun i => PowerSeries.C (o i) : LetA O n) i =
      PowerSeries.subst (W.π₀ i) ((PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) * G i) := by
    intro i
    show _ = PowerSeries.subst W.π₀₁ _
    rw [← ιS_apply W hR, map_mul, ← ιS_qp, ← hG i, h]
    rfl
  have e := congrFun ((huniq _ h1).trans (huniq _ h2).symm)
  funext i
  have hP := wuniq hlm 0 1 (Polynomial.C (o i)) (lt_of_le_of_lt Polynomial.degree_C_le (by simp))
    (G i) (by rw [Polynomial.coe_C, Gd01]; exact e i)
  simpa using hP

section Gam

variable {R : Type} [CommRing R] [BinomialRing R] [Algebra R O]

theorem qZ (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    ∃ w : (LetA O n)ˣ, ∀ i, (1 + PowerSeries.X : PowerSeries O) ^ (PD.p ^ 1) - 1 =
      PowerSeries.X * ((w : LetA O n) i * Formalism.MainNotions.LiftingTheory.qp W i) := by
  obtain ⟨w, hw⟩ := (Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR).qq
  refine ⟨w, fun i => ?_⟩
  rw [pow_one, ← W.q₀_def]
  congr 1
  exact congrFun hw i

theorem autW [IsDomain O] [CharZero O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (z : R)
    (hz : ((W.χΓ W.gam : Oˣ) : O) = algebraMap R O z) (hz1 : ((PD.p : ℕ) : R) ∣ z - 1) :
    (∀ f, ∃ H, W.γ₀ W.gam f - f = ((1 + PowerSeries.X) ^ (PD.p ^ 1) - 1) * H) ∧
    (∀ P Rr : PowerSeries O, P * Rr = (1 + PowerSeries.X) ^ (PD.p ^ 1) - 1 →
      ∃ H, W.γ₀ W.gam P - algebraMap O (PowerSeries O) (algebraMap R O z) * P = P ^ 2 * H) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨m, hm⟩ := hz1
  have hc : z = 1 + ((PD.p : ℕ) : R) ^ 1 * m := by rw [pow_one, ← hm]; ring
  have h1 : PowerSeries.coeff 1 (W.γ₀ W.gam PowerSeries.X) = algebraMap R O z := by
    rw [(W.γ₀_X W.gam).2, hz]
  exact Formalism.MainNotions.UnusedSlot80.LG.aut_core W.φ₀ (W.γ₀ W.gam) PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W) (W.γ₀_comm _)
    (W.γ₀_X W.gam).1 z m 1 hc h1

theorem hγg_of [IsDomain O] [CharZero O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (z : R)
    (hz : ((W.χΓ W.gam : Oˣ) : O) = algebraMap R O z) (hz1 : ((PD.p : ℕ) : R) ∣ z - 1) :
    ∀ g ∈ W.AΔ, ∃ g' ∈ W.AΔ, W.γA W.gam g - g = W.π₀ * Formalism.MainNotions.LiftingTheory.qp W * g' := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  obtain ⟨hA, -⟩ := autW W hR z hz hz1
  obtain ⟨w, hZ⟩ := qZ W hR
  intro g hg
  choose H hH using fun i => hA (g i)
  set t : LetA O n := fun i => PowerSeries.X * ((w : LetA O n) i * H i)
  have ht : W.γA W.gam g - g = Formalism.MainNotions.LiftingTheory.qp W * t := by
    funext i
    show W.γ₀ W.gam (g i) - g i = Formalism.MainNotions.LiftingTheory.qp W i * t i
    rw [hH i, hZ i]
    simp only [t]
    ring
  have htA : t ∈ W.AΔ := Formalism.MainNotions.LiftingTheory.lifta_divΔ W _ t (Formalism.MainNotions.LiftingTheory.lifta_qΔ W hLR.πΔ) hLR.qU
    (ht ▸ W.AΔ.sub_mem (Formalism.MainNotions.LiftingTheory.tr_γA_mem W W.gam hg) hg)
  obtain ⟨r, hr, hrt⟩ := eq_uniformizer_mul_of_constantCoeff_zero W hR htA (fun i => by simp [t])
  exact ⟨r, hr, by rw [ht, hrt]; ring⟩

theorem hγq_of [IsDomain O] [CharZero O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (z : R)
    (hz : ((W.χΓ W.gam : Oˣ) : O) = algebraMap R O z) (hz1 : ((PD.p : ℕ) : R) ∣ z - 1) :
    ∃ r ∈ W.AΔ, W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) =
      (algebraMap O (LetA O n) (W.χΓ W.gam : O) + Formalism.MainNotions.LiftingTheory.qp W * r) * Formalism.MainNotions.LiftingTheory.qp W := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  obtain ⟨-, hB⟩ := autW W hR z hz hz1
  obtain ⟨w, hZ⟩ := qZ W hR
  choose H hH using fun i => hB (Formalism.MainNotions.LiftingTheory.qp W i) (PowerSeries.X * (w : LetA O n) i) (by rw [hZ i]; ring)
  have hq := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hLR.πΔ
  have he : W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) =
      (algebraMap O (LetA O n) (W.χΓ W.gam : O) + Formalism.MainNotions.LiftingTheory.qp W * fun i => H i) * Formalism.MainNotions.LiftingTheory.qp W := by
    funext i
    show W.γ₀ W.gam (Formalism.MainNotions.LiftingTheory.qp W i) = _
    rw [sub_eq_iff_eq_add.mp (hH i), Pi.mul_apply, Pi.add_apply, Pi.mul_apply, Pi.algebraMap_apply, hz]
    ring
  refine ⟨fun i => H i, ?_, he⟩
  apply Formalism.MainNotions.LiftingTheory.lifta_divΔ W (Formalism.MainNotions.LiftingTheory.qp W ^ 2) _ (W.AΔ.pow_mem hq 2) (by rw [map_pow]; exact hLR.qU.pow 2)
  have : Formalism.MainNotions.LiftingTheory.qp W ^ 2 * (fun i => H i) =
      W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) - algebraMap O (LetA O n) (W.χΓ W.gam : O) * Formalism.MainNotions.LiftingTheory.qp W := by
    rw [he]; ring
  rw [this]
  exact W.AΔ.sub_mem (Formalism.MainNotions.LiftingTheory.tr_γA_mem W W.gam hq) (W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) hq)

theorem hγp_of [IsDomain O] [CharZero O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : ((PD.p : ℕ) : O) ≠ 0)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (z : R)
    (hz : ((W.χΓ W.gam : Oˣ) : O) = algebraMap R O z) (hz1 : ((PD.p : ℕ) : R) ∣ z - 1) :
    ∃ r ∈ W.AΔ, W.γA W.gam (Formalism.MainNotions.LiftingTheory.pk W 1) =
      (1 + W.π₀ * Formalism.MainNotions.LiftingTheory.qp W * r) * Formalism.MainNotions.LiftingTheory.pk W 1 := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hπ := hLR.πΔ
  have hq := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hπ
  set qp := Formalism.MainNotions.LiftingTheory.qp W
  set p1 := Formalism.MainNotions.LiftingTheory.pk W 1
  have hp1 : p1 = W.φA qp := by simp [p1, Formalism.MainNotions.LiftingTheory.pk]; rfl
  have hp1A : p1 ∈ W.AΔ := by rw [hp1]; exact Formalism.MainNotions.LiftingTheory.lifta_φΔ W _ hq
  obtain ⟨rq, hrq, hγq⟩ := hγq_of W hR z hz hz1
  set χ : LetA O n := algebraMap O (LetA O n) (W.χΓ W.gam : O)
  set u : LetA O n := χ + p1 * W.φA rq
  have huA : u ∈ W.AΔ := W.AΔ.add_mem (W.AΔ.algebraMap_mem _) (W.AΔ.mul_mem hp1A (Formalism.MainNotions.LiftingTheory.lifta_φΔ W _ hrq))
  have hγp1 : W.γA W.gam p1 = u * p1 := by
    rw [hp1, ← W.φA_γA, hγq, map_mul, map_add, map_mul]
    simp only [u, χ, AlgHom.commutes]
    rw [← hp1]
  obtain ⟨g', hg', hγg'⟩ := hγg_of W hR z hz hz1 p1 hp1A
  have hu1 : (u - 1) * p1 = W.π₀ * qp * g' := by rw [← hγg', hγp1]; ring
  obtain ⟨t, ht, hφπ⟩ := hLR.φπ
  have hp1e : p1 = ((PD.p : ℕ) : LetA O n) + W.π₀ * qp ^ (PD.p - 1) * t := by
    rw [hp1, show qp = W.π₀ + ((PD.p : ℕ) : LetA O n) from rfl, map_add, hφπ, map_natCast]
    simp only [Formalism.MainNotions.LiftingTheory.qp]
    ring
  obtain ⟨o, a, ha, hua⟩ := res_decomp W hlm hR (W.AΔ.sub_mem huA W.AΔ.one_mem)
  have hqp : qp ^ (PD.p - 1) = qp * qp ^ (PD.p - 2) := by rw [← pow_succ']; congr 1; omega

  have ho : o = 0 := by
    have hC : (fun i => PowerSeries.C (o i * ((PD.p : ℕ) : O)) : LetA O n) =
        qp * (W.π₀ * g' - a * p1 - (fun i => PowerSeries.C (o i)) * (W.π₀ * qp ^ (PD.p - 2) * t)) := by
      have e1 : (fun i => PowerSeries.C (o i * ((PD.p : ℕ) : O)) : LetA O n) =
          (fun i => PowerSeries.C (o i)) * ((PD.p : ℕ) : LetA O n) := by
        funext i; simp [map_mul]
      rw [e1]
      have e2 := hu1
      rw [hua, hp1e] at e2
      rw [hp1e, hqp] at *
      linear_combination e2
    have := res_unique W hlm hR _ (W.AΔ.sub_mem (W.AΔ.sub_mem (W.AΔ.mul_mem hπ hg') (W.AΔ.mul_mem ha hp1A))
      (W.AΔ.mul_mem (const_mem W o) (W.AΔ.mul_mem (W.AΔ.mul_mem hπ (W.AΔ.pow_mem hq _)) ht))) hC
    funext i
    have hi := congrFun this i
    simp only [Pi.zero_apply] at hi ⊢
    exact (mul_eq_zero.mp hi).resolve_right hl0
  have hua' : u - 1 = qp * a := by
    rw [hua, ho]
    have : (fun i => PowerSeries.C ((0 : ZMod n → O) i) : LetA O n) = 0 := by funext i; simp
    rw [this, zero_add]

  have hap : a * p1 = W.π₀ * g' := by
    apply Formalism.MainNotions.LiftingTheory.lifta_reg W qp _ _ hLR.qU
    rw [← mul_assoc, ← hua', hu1]; ring
  have ha0 : ∀ i, PowerSeries.constantCoeff (a i) = 0 := by
    intro i
    have e := congrArg (fun x : LetA O n => PowerSeries.constantCoeff (x i)) hap
    simp only [Pi.mul_apply, map_mul] at e
    have hcp : PowerSeries.constantCoeff (p1 i) = ((PD.p : ℕ) : O) := by
      rw [hp1e]
      simp [LocWach.π₀, Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR]
    have hcπ : PowerSeries.constantCoeff (W.π₀ i) = 0 := Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR
    rw [hcp, hcπ, zero_mul] at e
    exact (mul_eq_zero.mp e).resolve_right hl0
  obtain ⟨r, hr, har⟩ := eq_uniformizer_mul_of_constantCoeff_zero W hR ha ha0
  refine ⟨r, hr, ?_⟩
  rw [hγp1, show u = 1 + (u - 1) by ring, hua', har]
  ring

end Gam

theorem hAq'_of [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    ∀ i (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      ∃ (o : O) (g' : LetA O n), g' ∈ W.AΔ ∧
        g = algebraMap O (LetA O n) o * letE i + Formalism.MainNotions.LiftingTheory.qp W * g' := by
  intro i g hg hgi
  obtain ⟨o, g', hg', he⟩ := res_decomp W hlm hR hg
  refine ⟨o i, letE i * g', W.AΔ.mul_mem (Formalism.MainNotions.LiftingTheory.idempotent_mem_invariants W i) hg', ?_⟩
  rw [← hgi]
  conv_lhs => rw [he]
  have e : (letE i : LetA O n) * (fun j => PowerSeries.C (o j)) = algebraMap O (LetA O n) (o i) * letE i := by
    funext j
    by_cases h : j = i
    · subst h; simp [letE]
    · simp [letE, h]
  rw [mul_add, e]
  ring

theorem hqc'_of [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    ∀ i (o : O) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      algebraMap O (LetA O n) o * letE i = Formalism.MainNotions.LiftingTheory.qp W * g → o = 0 := by
  intro i o g hg _ h
  have e : algebraMap O (LetA O n) o * letE i =
      (fun j => PowerSeries.C (if j = i then o else 0) : LetA O n) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [letE]
    · simp [letE, hj]
  rw [e] at h
  have := congrFun (res_unique W hlm hR _ hg h) i
  simpa using this

theorem uniformizer_unit_of_binomial_ring [IsDomain O] [CharZero O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : ((PD.p : ℕ) : O) ≠ 0)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {R : Type} [CommRing R] [BinomialRing R] [Algebra R O] (z : R)
    (hz : ((W.χΓ W.gam : Oˣ) : O) = algebraMap R O z) (hz1 : ((PD.p : ℕ) : R) ∣ z - 1) :
    IsUnit (algebraMap (LetA O n) W.EE W.π₀) ∧
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ∧
    (∀ g ∈ W.AΔ, ∃ g' ∈ W.AΔ, W.γA W.gam g - g = W.π₀ * Formalism.MainNotions.LiftingTheory.qp W * g') ∧
    (∃ r ∈ W.AΔ, W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) =
      (algebraMap O (LetA O n) (W.χΓ W.gam : O) + Formalism.MainNotions.LiftingTheory.qp W * r) * Formalism.MainNotions.LiftingTheory.qp W) ∧
    (∃ r ∈ W.AΔ, W.γA W.gam (Formalism.MainNotions.LiftingTheory.pk W 1) =
      (1 + W.π₀ * Formalism.MainNotions.LiftingTheory.qp W * r) * Formalism.MainNotions.LiftingTheory.pk W 1) ∧
    (∀ (i : ZMod n) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      ∃ (o : O) (g' : LetA O n), g' ∈ W.AΔ ∧
        g = algebraMap O (LetA O n) o * letE i + Formalism.MainNotions.LiftingTheory.qp W * g') ∧
    (∀ (i : ZMod n) (o : O) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      algebraMap O (LetA O n) o * letE i = Formalism.MainNotions.LiftingTheory.qp W * g → o = 0) := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  exact ⟨hLR.πU, hLR.qU, hγg_of W hR z hz hz1, hγq_of W hR z hz hz1, hγp_of W hlm hl0 hR z hz hz1,
    hAq'_of W hlm hR, hqc'_of W hlm hR⟩

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

set_option maxHeartbeats 400000 in

theorem gamma_lemma_of_crystalline (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.N.Pv.LocalLengthBound.WachGammaDerivation ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  have h9W : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hg) := h9 l K 1 LL hg
  refine fun d T₁ T₂ F' b S η m hset => ?_
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hT₂ : IsCrys ((D.loc l).PD K) T₂.ρ := hset.2.2.2.2.2.1.2.1
  have hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hg) :=
    (Formalism.MainNotions.LiftingTheory.frame_p9A ((HW l).W K 1 LL hg) h9W hCA T₂ hT₂).1
  haveI : CharZero ↥(OL LL) := Formalism.MainNotions.UnusedSlot80.levg_charZero LL
  letI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) :=
    Formalism.MainNotions.CrystallineLiftingInputs.OL.OL_complete_max (D.loc l) LL
  have hlm : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.CrystallineLiftingInputs.OL.l_mem_max (D.loc l) LL
  have hl0 : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ≠ 0 := by
    rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.CrystallineLiftingInputs.OL.l_ne_zero LL
  obtain ⟨z, hz, hz1⟩ := Formalism.MainNotions.UnusedSlot80.levg_chi (D.loc l) (HW l) K LL hg
  obtain ⟨hπU, hqU, hγg, hγq, hγp, hAq, hqc⟩ := uniformizer_unit_of_binomial_ring ((HW l).W K 1 LL hg) hlm hl0 hR z hz hz1
  exact Formalism.MainNotions.N.Pv.LocalLengthBound.gamma_structure_of ((HW l).W K 1 LL hg) h9W hπU hqU hγg hγq hγp hAq hqc d T₁ T₂ F' b S η m hset

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData
