import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaloisRepLocallyConstantModPrimePowStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.ResidualCocycleReduction

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem redL_add_l_mul (c : Coef l) {x d : Qbar l} (hx : x ∈ c.O) (hd : d ∈ c.O) :
    redL c (x + (l : Qbar l) * d) = redL c x := by
  rw [redL_add c hx (c.O.mul_mem (c.O.natCast_mem l) hd),
    (redL_eq_zero_iff c (c.O.mul_mem (c.O.natCast_mem l) hd)).2 ⟨d, hd, rfl⟩, add_zero]

theorem redL_mulVec (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (v : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hv : ∀ j, v j ∈ c.O) (i : Fin 2) :
    redL c ((M *ᵥ v) i) = ((fun i j => redL c (M i j)) *ᵥ (fun j => redL c (v j))) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [redL_add c (c.O.mul_mem (hM _ _) (hv _)) (c.O.mul_mem (hM _ _) (hv _)),
    redL_mul c (hM _ _) (hv _), redL_mul c (hM _ _) (hv _)]

theorem mulVec_mem (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (v : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hv : ∀ j, v j ∈ c.O) (i : Fin 2) : (M *ᵥ v) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hM _ _) (hv _)) (c.O.mul_mem (hM _ _) (hv _))

theorem resCoc_mul (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) (y : Fin 2 → Qbar l)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) (s t : G ℚ Ω) :
    resCoc c W z y (s * t) = resCoc c W z y s + resAct c W hO s (resCoc c W z y t) := by
  obtain ⟨-, h2, -, -, -, -⟩ := hz
  funext i
  have hM : mat W (s * t) = mat W s * mat W t := by simp only [mat, map_mul, Units.val_mul]
  set a : G ℚ Ω → Fin 2 → Qbar l := fun s i => (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i with ha
  have e : (l : Qbar l) * z (s * t) i - (mat W (s * t) *ᵥ y - y) i =
      (a s i + (mat W s *ᵥ a t) i) + (l : Qbar l) * (z (s * t) i - z s i - (mat W s *ᵥ z t) i) := by
    have ea : a t = (l : Qbar l) • z t - (mat W t *ᵥ y - y) := by
      funext j; simp only [ha, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hM, ea, ← Matrix.mulVec_mulVec]
    simp only [ha, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hat : ∀ j, a t j ∈ c.O := fun j => hzy t j
  show redL c _ = redL c (a s i) + (wRed c W s *ᵥ (fun j => redL c (a t j))) i
  rw [e, redL_add_l_mul c (c.O.add_mem (hzy s i) (mulVec_mem c _ _ (hO s) hat i)) (h2 s t i),
    redL_add c (hzy s i) (mulVec_mem c _ _ (hO s) hat i), redL_mulVec c _ _ (hO s) hat i]
  rfl

theorem resCoc_locConst (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hlc : ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) {y : Fin 2 → Qbar l} (hy : VecE c y)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) :
    IsLocallyConstant (resCoc c W z y) := by
  obtain ⟨-, -, h3, -, -, -⟩ := hz
  obtain ⟨k, hk⟩ := hy
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun s => ?_
  filter_upwards [h3 s, hlc (k + 1) s] with t ht hW
  funext i
  choose o ho he using hW
  have e : (l : Qbar l) * z t i - (mat W t *ᵥ y - y) i =
      ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) + (l : Qbar l) *
        ((z t i - z s i) - (o i 0 * ((l : Qbar l) ^ k * y 0) + o i 1 * ((l : Qbar l) ^ k * y 1))) := by
    have h0 : mat W t i 0 = mat W s i 0 + (l : Qbar l) ^ (k + 1) * o i 0 := by rw [← he i 0]; ring
    have h1 : mat W t i 1 = mat W s i 1 + (l : Qbar l) ^ (k + 1) * o i 1 := by rw [← he i 1]; ring
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [h0, h1]; ring
  show redL c _ = redL c _
  rw [e, redL_add_l_mul c (hzy s i) (c.O.sub_mem (ht i) (c.O.add_mem (c.O.mul_mem (ho i 0) (hk 0))
    (c.O.mul_mem (ho i 1) (hk 1))))]

theorem reduced_selmer_cochain_mem_continuous_cocycles_S (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    (hlc : ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) {y : Fin 2 → Qbar l} (hy : VecE c y)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) :
    descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  have hd : ∀ s, descS S (resCoc c W z y) (toGS Ω (S : Set Pl) s) = resCoc c W z y s :=
    descS_resCoc_toGS c W S A hO hN hz y hzy
  refine ⟨?_, fun g h => ?_⟩
  · rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
    have : descS S (resCoc c W z y) ∘ (QuotientGroup.mk : G ℚ Ω → GS Ω (S : Set Pl)) = resCoc c W z y :=
      funext fun s => hd s
    rw [this]
    exact (resCoc_locConst c W S A hlc hz hy hzy).continuous
  · obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective h
    have e1 : ((s : GS Ω (S : Set Pl)) * (t : GS Ω (S : Set Pl))) = toGS Ω (S : Set Pl) (s * t) := rfl
    have e2 : (s : GS Ω (S : Set Pl)) = toGS Ω (S : Set Pl) s := rfl
    have e3 : (t : GS Ω (S : Set Pl)) = toGS Ω (S : Set Pl) t := rfl
    rw [e1, e2, e3, hd, hd, hd, resRep_toGS]
    exact resCoc_mul c W S A hO hz y hzy s t

theorem _root_.GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O)
    (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ∀ z ∈ divSelCoc c W S A,
    ∀ y : Fin 2 → Qbar l, VecE c y → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) →
    descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  intro l _ Ω _ _ S A W c hO hN hW z hz y hy hzy
  exact GlobalTheory.Ord2.ResidualCocycleReduction.reduced_selmer_cochain_mem_continuous_cocycles_S c W S A hO hN (GlobalTheory.T.integralGaloisRep_locallyConstant_modPrimePow l Ω c W hW hO) hz hy hzy

end GlobalTheory.Ord2.ResidualCocycleReduction
