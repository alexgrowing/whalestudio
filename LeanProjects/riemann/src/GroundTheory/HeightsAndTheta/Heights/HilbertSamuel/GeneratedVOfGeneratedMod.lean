import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsExtra
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsQuotPartGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenerationOfH1GenAmple

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def chartExp (c : ∀ k, ι k) (n : K → ℕ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun q => if q.2 = c q.1 then n q.1 else 0

def chartMon (c : ∀ k, ι k) (n : K → ℕ) : MRingOver S ι :=
  monomial (chartExp c n) 1

theorem chartMon_homog (c : ∀ k, ι k) (n : K → ℕ) : IsMultiHomog (chartMon (S := S) c n) n :=
  GenTwistGenerated.isMultiHomog_monomial _ _ _ fun k => by simp [chartExp]

theorem chartMon_mem {I : ∀ k, Finset (ι k)} {c : ∀ k, ι k} (hc : ∀ k, c k ∈ I k) (n : K → ℕ) :
    chartMon (S := S) c n ∈ KH.cellMon S I := by
  unfold chartMon
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  refine Submonoid.prod_mem _ fun q hq => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
  have hq' : q.2 = c q.1 := by
    by_contra h
    simp [chartExp, h] at hq
  obtain ⟨k, i⟩ := q
  simp only at hq'
  subst hq'
  exact ⟨k, c k, hc k, rfl⟩

variable {V : Ideal (MRingOver S ι)}

theorem smul_quot (f : MRingOver S ι) (m : MRingOver S ι ⧸ V) : f • m = Ideal.Quotient.mk V f * m := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
  rfl

theorem smul_mul_eq_mul_smul {T : Submonoid (MRingOver S ι)} (p : MRingOver S ι)
    (x y : LocalizedModule T (MRingOver S ι ⧸ V)) : (p • x) * y = x * (p • y) := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_mul_mk, LocalizedModule.smul'_mk,
        LocalizedModule.mk_mul_mk, smul_mul_assoc, mul_smul_comm]

theorem generatedV_of_generatedMod {d : K → ℤ} (h : GeneratedMod S ι (KH.quotPart S V) d) :
    KH.GeneratedV S V d := by
  classical
  intro I
  let c : ∀ k, ι k := fun k => (I.2.1 k).choose
  have hc : ∀ k, c k ∈ I.1 k := fun k => (I.2.1 k).choose_spec
  let dp : K → ℕ := fun k => (d k).toNat
  let dm : K → ℕ := fun k => (-d k).toNat
  have hd : ∀ k, (dp k : ℤ) - dm k = d k := fun k => Int.toNat_sub_toNat_neg (d k)
  let P : MRingOver S ι := chartMon c dp
  let Q : MRingOver S ι := chartMon c dm
  have hP : P ∈ KH.cellMon S I.1 := chartMon_mem hc dp
  have hQ : Q ∈ KH.cellMon S I.1 := chartMon_mem hc dm
  have hpart : ∀ (f : MRingOver S ι) (a : K → ℕ), IsMultiHomog f a →
      Ideal.Quotient.mk V f ∈ KH.quotPart S V (fun k => (a k : ℤ)) := fun f a hf =>
    Submodule.subset_span ⟨f, ⟨fun k => Int.natCast_nonneg _, by simpa using hf⟩, rfl⟩
  let x : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    LocalizedModule.mk (Ideal.Quotient.mk V P) ⟨Q, hQ⟩
  have hx : x ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) d := by
    refine GenTwistGenerated.mk_mem_locPart _ _ dm (chartMon_homog c dm) ?_
    have e : (d + fun k => (dm k : ℤ)) = fun k => (dp k : ℤ) := by
      funext k
      have := hd k
      simp only [Pi.add_apply]
      omega
    rw [e]
    exact hpart P dp (chartMon_homog c dp)
  obtain ⟨t, a, r, p, z, ht, hta, hpa, hz, htx⟩ := h I x hx
  let w : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    LocalizedModule.mk (Ideal.Quotient.mk V Q) ⟨t * P, mul_mem ht hP⟩
  refine ⟨r, z, fun j => p j • w, hz, fun j => ?_, ?_⟩
  · have e0 : p j • Ideal.Quotient.mk V Q = Ideal.Quotient.mk V (p j * Q) := by
      rw [smul_quot, map_mul]
    have e1 : p j • w =
        LocalizedModule.mk (Ideal.Quotient.mk V (p j * Q)) ⟨t * P, mul_mem ht hP⟩ :=
      (LocalizedModule.smul'_mk ..).trans (congrArg (fun m => LocalizedModule.mk m _) e0)
    refine (congrArg (· ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-d)) e1).mpr ?_
    refine GenTwistGenerated.mk_mem_locPart _ _ (a + dp)
      (GenTwistGenerated.isMultiHomog_mul hta (chartMon_homog c dp)) ?_
    have e2 : (-d + fun k => ((a + dp) k : ℤ)) = fun k => ((a + dm) k : ℤ) := by
      funext k
      have := hd k
      simp only [Pi.add_apply, Pi.neg_apply, Nat.cast_add]
      omega
    rw [e2]
    exact hpart _ _ (GenTwistGenerated.isMultiHomog_mul (hpa j) (chartMon_homog c dm))
  · calc ∑ j, p j • w * z j I = ∑ j, w * (p j • z j I) :=
          Finset.sum_congr rfl fun j _ => smul_mul_eq_mul_smul (p j) w (z j I)
      _ = w * (t • x) := by rw [← Finset.mul_sum, htx]
      _ = 1 := by
        have e3 : Ideal.Quotient.mk V Q * (t • Ideal.Quotient.mk V P) =
            ((⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩ : KH.cellMon S I.1) • (1 : MRingOver S ι ⧸ V)) := by
          rw [Submonoid.smul_def, smul_quot, smul_quot, mul_one]
          simp only [Submonoid.coe_mul, map_mul]
          ring
        calc w * (t • x)
            = w * LocalizedModule.mk (t • Ideal.Quotient.mk V P) ⟨Q, hQ⟩ :=
              congrArg (w * ·) (LocalizedModule.smul'_mk ..)
          _ = LocalizedModule.mk (Ideal.Quotient.mk V Q * (t • Ideal.Quotient.mk V P))
                (⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩) := LocalizedModule.mk_mul_mk
          _ = LocalizedModule.mk ((⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩ : KH.cellMon S I.1) •
                (1 : MRingOver S ι ⧸ V)) (⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩) :=
              congrArg (fun m => LocalizedModule.mk m _) e3
          _ = LocalizedModule.mk 1 1 := LocalizedModule.mk_cancel _ _
          _ = 1 := OreLocalization.one_def.symm

end GenerationOfH1GenAmple

theorem GenerationOfH1GenAmple.proof (hQ : QuotPartGraded.Statement) : GenerationOfH1GenAmple.Statement := by
  intro S _ K _ _ ι _ _ V N hV hH e
  have hann : V ≤ Module.annihilator (MRingOver S ι) (MRingOver S ι ⧸ V) := fun v hv =>
    Module.mem_annihilator.mpr fun m => by
      rw [GenerationOfH1GenAmple.smul_quot, Ideal.Quotient.eq_zero_iff_mem.mpr hv, zero_mul]
  obtain ⟨c₁, hc₁⟩ := hH (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance (hQ S K ι V hV) hann e
  exact ⟨c₁, fun c hc => GenerationOfH1GenAmple.generatedV_of_generatedMod (hc₁ c hc).2⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
