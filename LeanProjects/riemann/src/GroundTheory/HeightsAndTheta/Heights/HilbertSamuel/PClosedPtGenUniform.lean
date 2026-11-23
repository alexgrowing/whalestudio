import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtGenUniform
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubmodules
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtFibreLift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartNakayamaGen
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNearMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.Inter.AvoidRing (isMultiHomog_mul isMultiHomog_pow)

noncomputable section

namespace ClosedPtGenUniform

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {𝓜 : (K → ℤ) → Submodule S M}

theorem genNear_of_mul_eq_pow {d : K → ℤ} {a q b : MRingOver S ι} {α β δ : K → ℕ} {m : ℕ}
    (h : GenNear S ι 𝓜 d a α) (hq : IsMultiHomog q β) (hab : a * q = b ^ m) (hdeg : m • δ = α + β) :
    GenNear S ι 𝓜 d b δ := by
  intro I x hx
  obtain ⟨n, t, c, r, p, z, ht, htc, hp, hz, he⟩ := h I x hx
  refine ⟨m * n, t, c, r, fun j => q ^ n * p j, z, ht, htc, fun j => ?_, hz, ?_⟩
  · have h' := isMultiHomog_mul (isMultiHomog_pow hq n) (hp j)
    convert h' using 1
    funext k
    have hk := congrFun hdeg k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    rw [mul_comm m n, mul_assoc, hk]
    ring
  · rw [pow_mul, ← hab, mul_pow, show a ^ n * q ^ n * t = q ^ n * (a ^ n * t) by ring, mul_smul, he,
      Finset.smul_sum]
    simp_rw [mul_smul]

theorem genNear_mul_pow (hM : GenNearMul.Statement) (hgr : KH.IsMGraded S ι 𝓜) {W : Ideal (MRingOver S ι)}
    (hW : W ≤ Module.annihilator (MRingOver S ι) M) {d n : K → ℤ} {f g : MRingOver S ι} {δ γ : K → ℕ}
    (hf : IsMultiHomog f δ) (hg : IsMultiHomog g γ) (hfd : GenNear S ι 𝓜 d f δ)
    (hgn : GenNear S ι (KH.quotPart S W) n g γ) :
    ∀ a : ℕ, GenNear S ι 𝓜 (d + a • n) (f * g ^ a) (δ + a • γ) := by
  intro a
  induction a with
  | zero => simpa using hfd
  | succ a ih =>
    have h' := hM S K ι M 𝓜 W (d + a • n) n (f * g ^ a) g (δ + a • γ) γ hgr hW
      (isMultiHomog_mul hf (isMultiHomog_pow hg a)) hg ih hgn
    rw [succ_nsmul, succ_nsmul, pow_succ, ← mul_assoc, ← add_assoc, ← add_assoc]
    exact h'

end ClosedPtGenUniform

open ClosedPtGenUniform in

theorem ClosedPtGenUniform.proof (hG : GradedSubmodules.Statement) (hF : ClosedPtFibreLift.Statement)
    (hN : ChartNakayamaGen.Statement) (hM : GenNearMul.Statement) : ClosedPtGenUniform.Statement := by
  intro S _ K _ _ ι _ _ V N hS hH M _ _ _ _ 𝓜 hfin hgr hV e P hP
  classical
  obtain ⟨hPprime, hPhom, hPrel⟩ := hP.1
  choose i hi using hPrel

  let I : KH.Cell K ι 0 := ⟨fun k => {i k}, fun k => Finset.singleton_nonempty _, by simp⟩
  have hI : ∀ k, ∀ j ∈ I.1 k, (X ⟨k, j⟩ : MRingOver S ι) ∉ P := by
    intro k j hj
    rw [Finset.mem_singleton.mp hj]
    exact hi k
  have : IsNoetherianRing (MRingOver S ι) := inferInstance

  obtain ⟨hWhom, hMsub⟩ := hG S K ι M 𝓜 hgr
  have : IsNoetherian (MRingOver S ι) M := isNoetherian_of_isNoetherianRing_of_finite _ _
  have hVPM : V ≤ Module.annihilator (MRingOver S ι) (P • ⊤ : Submodule (MRingOver S ι) M) :=
    hV.trans (LinearMap.annihilator_le_of_injective (P • ⊤ : Submodule (MRingOver S ι) M).subtype
      (P • ⊤ : Submodule (MRingOver S ι) M).injective_subtype)
  obtain ⟨cM, hcM⟩ := hH (P • ⊤ : Submodule (MRingOver S ι) M) (subGrading 𝓜 (P • ⊤)) inferInstance
    (hMsub P hPhom).1 hVPM e
  obtain ⟨fM, δM, hfM, hfMP, hgenM⟩ := hN S K ι M 𝓜 P (e + cM • N) hS hfin hgr hPprime hPhom I hI
    (hF S K ι M 𝓜 P (e + cM • N) hS hfin hgr hP (hcM cM le_rfl) I hI)

  set W := Module.annihilator (MRingOver S ι) M with hWdef
  have hWgr : KH.IsMGraded S ι (KH.quotPart S W) := QuotPartGraded.proof S K ι W hWhom
  have hQfin : Module.Finite (MRingOver S ι) (MRingOver S ι ⧸ W) := inferInstance
  obtain ⟨-, hQsub⟩ := hG S K ι (MRingOver S ι ⧸ W) (KH.quotPart S W) hWgr
  have : IsNoetherian (MRingOver S ι) (MRingOver S ι ⧸ W) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have hVQ : V ≤ Module.annihilator (MRingOver S ι) (MRingOver S ι ⧸ W) := by
    rw [Ideal.annihilator_quotient]
    exact hV
  have hVPQ : V ≤ Module.annihilator (MRingOver S ι) (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)) :=
    hVQ.trans (LinearMap.annihilator_le_of_injective
      (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)).subtype
      (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)).injective_subtype)
  obtain ⟨cO, hcO⟩ := hH (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W))
    (subGrading (KH.quotPart S W) (P • ⊤)) inferInstance (hQsub P hPhom).1 hVPQ 0
  have hgenO : ∀ n : ℕ, cO ≤ n → ∃ (g : MRingOver S ι) (γ : K → ℕ), IsMultiHomog g γ ∧ g ∉ P ∧
      GenNear S ι (KH.quotPart S W) (0 + n • N) g γ := fun n hn =>
    hN S K ι _ (KH.quotPart S W) P (0 + n • N) hS hQfin hWgr hPprime hPhom I hI
      (hF S K ι _ (KH.quotPart S W) P (0 + n • N) hS hQfin hWgr hP (hcO n hn) I hI)
  set n₁ := cO + 1 with hn₁
  obtain ⟨g₁, γ₁, hg₁, hg₁P, hgen₁⟩ := hgenO n₁ (by omega)
  obtain ⟨g₂, γ₂, hg₂, hg₂P, hgen₂⟩ := hgenO (n₁ + 1) (by omega)

  refine ⟨fM * g₁ * g₂, δM + γ₁ + γ₂, cM + n₁ * n₁, isMultiHomog_mul (isMultiHomog_mul hfM hg₁) hg₂, ?_, ?_⟩
  · intro hmem
    rcases hPprime.mem_or_mem hmem with h | h
    · rcases hPprime.mem_or_mem h with h | h
      · exact hfMP h
      · exact hg₁P h
    · exact hg₂P h
  intro c hc
  have hpos : 0 < n₁ := by omega
  set q := (c - cM) / n₁ with hq
  set s := (c - cM) % n₁ with hs
  have hdm : n₁ * q + s = c - cM := Nat.div_add_mod (c - cM) n₁
  have hsn : s < n₁ := Nat.mod_lt _ hpos
  have hqn : n₁ ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hpos]
    omega
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le (le_trans hsn.le hqn)
  have hca : c = cM + a * n₁ + s * (n₁ + 1) := by
    have h1 : c - cM + cM = c := Nat.sub_add_cancel (by omega)
    rw [← h1, ← hdm, ha]
    ring
  have hA := genNear_mul_pow hM hgr le_rfl hfM hg₁ hgenM hgen₁ a
  have hB := genNear_mul_pow hM hgr le_rfl (isMultiHomog_mul hfM (isMultiHomog_pow hg₁ a)) hg₂ hA hgen₂ s
  have htw : e + cM • N + a • (0 + n₁ • N) + s • (0 + (n₁ + 1) • N) = e + c • N := by
    rw [hca]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_add]
    push_cast
    ring
  rw [htw] at hB
  refine genNear_of_mul_eq_pow hB
    (isMultiHomog_mul (isMultiHomog_mul (isMultiHomog_pow hfM (a + s)) (isMultiHomog_pow hg₁ (s + 1)))
      (isMultiHomog_pow hg₂ (a + 1))) (m := a + s + 1) (by ring) ?_
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
