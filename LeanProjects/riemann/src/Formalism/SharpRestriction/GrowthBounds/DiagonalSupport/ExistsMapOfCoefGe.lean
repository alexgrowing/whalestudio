import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDefs
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecompositionOfThreeParts

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Model

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] (K : ℕ) {J : ℕ} (nL : ZMod J → ℕ)

def mlPos : ML J nL r → ZMod J × ℤ
  | ML.ll j l => (j, llPos Fr (segZ j) l.val)
  | ML.lab j m => (j, Fr.fr (segZ j) (r - 1 - m.val))
  | ML.wc j m => (j + 1, Fr.fr (segZ (j + 1) - 1) (r - 1 - m.val))
  | ML.tp j m _ => (j, Fr.fr (segZ j) (r - 1 - m.val))

def tlPos (x : TL J nL r) : ZMod J × ℤ := (x.1, posTL Fr x)

def LSeg (J : ℕ) : Letters (ZMod J × ℤ) := ⟨fun x => decide (Even x.2)⟩

def xiPl (Go : MvPolynomial (ML J nL r × Fin r) O) : MvPolynomial ((ZMod J × ℤ) × Fin r) O :=
  rename (fun v => (mlPos Fr nL v.1, v.2)) Go

def xiNo (No : MvPolynomial (TL J nL r × Fin K) O) : MvPolynomial ((ZMod J × ℤ) × Fin K) O :=
  rename (fun v => (tlPos Fr nL v.1, v.2)) No

def PhiPl (J : ℕ) : MvPolynomial ((ZMod J × ℤ) × Fin r) O →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => X (posOf n' v.1.2, Fin.castAdd K v.2) ^ (p ^ Fr.dist (segZ v.1.1) v.1.2)

def PhiNo (J : ℕ) : MvPolynomial ((ZMod J × ℤ) × Fin K) O →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => X (posOf n' v.1.2, Fin.natAdd r v.2) ^ (p ^ Fr.dist (segZ v.1.1) v.1.2)

def labO [NeZero J] (rho : TL J nL r × Fin (r + K) → ℕ) : Fin n' × Fin (r + K) →₀ ℕ :=
  ∑ x : TL J nL r, ∑ c : Fin (r + K), Finsupp.single (posOf n' (posTL Fr x), c) (rho (x, c))

end Model

def toKK {O : Type} [CommRing O] [IsDomain O] {n' m r K : ℕ} (hk : m + 1 = r + K) (P : RRing O n' (r + K)) :
    MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O)) (rename (castVK hk) P)

structure MFH (p : ℕ) {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (TT : Finset (Fin n')) (L₁ L₂ N₁ G' : ℕ)
    (deg d : Fin n' → ℕ) (Y : ℝ) (k cP : ℕ) : Prop where
  prime : p.Prime
  two_le_r : 2 ≤ r
  frames : FramesOK TT L₁ L₂ N₁ G' Fr
  d_top : ∀ s ∈ Fr.TT, d s = deg s
  d_off : ∀ s, s ∉ Fr.TT → d s = 0
  margin : ∀ j x : ℤ, x ∈ Fr.letters j → ¬ Fr.IsW j x → 128 * (cP : ℝ) ≤ (sl p Fr deg Y k j x : ℝ)

section At

variable (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  (d : Fin n' → ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ)
  (ka : ZMod J → ℕ → Fin K → ℤ) (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
  (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)

def MH : Prop :=
  SignedChainDegreeCondition p O Fr deg Y N₁ G' cP Dt dPl ka ∧ BlockOK Fr p Dt.nL d rho dPl dNo ∧
  NormTest p O cP Dt dNo ka (MvPolynomial.map (algebraMap O (KK O)) No) ∧
  Dt.YY 24 60 (MvPolynomial.map (algebraMap O (KK O)) Go) ∧
  ∀ mo ∈ Go.support, Dt.ph (monomial mo 1) ∈ Pol (KK O) r Dt.d

def Occ (δ : ZMod J × ℤ → ℕ) : Prop := ∃ mo ∈ (xiPl Fr O Dt.nL Go).support, ∀ i, multideg mo i = δ i

def DecAt : Prop :=
  ∀ δ : ZMod J × ℤ → ℕ, Occ p O Fr Dt Go δ →
    ∃ (n : ℕ) (obd : ℤ → ℤ → ℝ) (xi : Fin n → ℤ → SegRing O r K) (dd : ℤ → ℤ → ℕ),
      (∀ (i : Fin n) (j : ℕ), j < Fr.J →
        xi i j ∈ XX' O r K Fr j (fun _ => (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ))
          (fun x => Bo p Fr deg j x / 2 - sl p Fr deg Y (r + K) j x) (obd j) ∧
        xi i j ∈ restrictSupport O {mm | ∀ x ∈ Fr.letters j, ∑ c : Fin (r + K), mm (x, c) = dd j x}) ∧
      (∀ j : ℕ, j < Fr.J → ∀ x ∈ Fr.letters j, (Fr.IsW j x ∨ x ∈ Fr.LLset j) →
        (dd j x : ℝ) ≤ levDeg p Fr deg j x + levDeg p Fr deg j x / 100) ∧
      ∑ i, ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (xi i j) =
        PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No)

def AlgAt : Prop :=
  toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))) =
    asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
      (MvPolynomial.map (algebraMap O (KK O)) No)

def DegAt : Prop :=
  ∀ δ : ZMod J × ℤ → ℕ, Occ p O Fr Dt Go δ →
    HasMultideg (toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No)))) d ∧
    ∃ o : ℕ, ∀ mm ∈ (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))).support,
      normDeg r mm = o

def LabAt : Prop :=
  IsLabel p Fr (labO Fr K Dt.nL rho) ∧ ∀ v ∈ (labO Fr K Dt.nL rho).support, v.1 ∈ Fr.TT

end At

theorem sum_homComp {R : Type} [CommRing R] {ι : Type} {n : ℕ} (F : MvPolynomial (ι × Fin n) R) :
    ∑ δ ∈ F.support.image (fun mo => fun i => multideg mo i), homComp δ F = F := by
  classical
  conv_rhs => rw [F.as_sum]
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (s := F.support)
    (t := F.support.image (fun mo => fun i => multideg mo i)) (g := fun mo => fun i => multideg mo i)
    (fun mo hmo => Finset.mem_image_of_mem _ hmo)]
  apply Finset.sum_congr rfl
  intro δ _
  unfold homComp
  apply Finset.sum_congr
  · ext mo
    simp only [Finset.mem_filter, funext_iff]
  · intro _ _
    rfl

private theorem mem_range_algebraMap_of_vK_nonneg {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (x : KK O) (h : geQ (vK p x) 0) : x ∈ Set.range (algebraMap O (KK O)) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero]⟩
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) x
  have hb : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hbK : algebraMap O (KK O) (b : O) ≠ 0 :=
    fun h0 => hb ((IsFractionRing.injective O (KK O)) (h0.trans (map_zero _).symm))
  have ha : a ≠ 0 := by
    intro ha0
    apply hx
    rw [ha0, map_zero] at hab
    exact (mul_eq_zero.mp hab).resolve_right hbK
  have hord := Formalism.MainNotions.G.Joints.ordW_eq x a b ha hb hab
  have hp0 : IsDiscreteValuationRing.addVal O (p : O) ≠ 0 := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mp S.p_mem
  have hpt : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact S.p_ne
  have hram : 0 < ramE p O := by
    unfold ramE
    rcases ENat.ne_top_iff_exists.mp hpt with ⟨k, hk⟩
    rw [← hk] at hp0 ⊢
    simp only [ENat.toNat_coe]
    exact Nat.pos_of_ne_zero (by exact_mod_cast hp0)
  have hq := h ((((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) / (ramE p O : ℚ))
    (by rw [vK, hord, WithTop.map_coe])
  have hq' : (0 : ℚ) ≤ (((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) /
      (ramE p O : ℚ) := by exact_mod_cast hq
  have hd : (0 : ℚ) < ramE p O := by exact_mod_cast hram
  have hnum : (0 : ℚ) ≤ (((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) :=
    (div_nonneg_iff.mp hq').elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hd))
  have hle : Formalism.MainNotions.G.Joints.nv (b : O) ≤ Formalism.MainNotions.G.Joints.nv a := by
    have : (0 : ℤ) ≤ (Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) := by exact_mod_cast hnum
    omega
  have hat : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact ha
  have hbt : IsDiscreteValuationRing.addVal O (b : O) ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hb
  have hvle : IsDiscreteValuationRing.addVal O (b : O) ≤ IsDiscreteValuationRing.addVal O a := by
    rw [← ENat.coe_toNat hat, ← ENat.coe_toNat hbt]
    exact_mod_cast hle
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.mp hvle
  refine ⟨c, ?_⟩
  rw [hc, map_mul] at hab
  exact (mul_left_cancel₀ hbK (by rw [← hab, mul_comm])).symm

theorem exists_map_of_coefGe {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) {σ : Type} (F : MvPolynomial σ (KK O)) (h : CoefGe p F 0) :
    ∃ Fo : MvPolynomial σ O, MvPolynomial.map (algebraMap O (KK O)) Fo = F := by
  have hrange : F ∈ Set.range (MvPolynomial.map (algebraMap O (KK O))) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro x hx
    obtain ⟨mo, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hx
    exact mem_range_algebraMap_of_vK_nonneg S _ (h mo)
  obtain ⟨Fo, hFo⟩ := hrange
  exact ⟨Fo, hFo⟩

theorem support_of_map {O : Type} [CommRing O] [IsDomain O] {σ : Type} (Fo : MvPolynomial σ O) :
    (MvPolynomial.map (algebraMap O (KK O)) Fo).support = Fo.support := by
  exact MvPolynomial.support_map_of_injective _ (IsFractionRing.injective O (KK O))

theorem membAt_core (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
    (d : Fin n' → ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J)
    (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
    (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)
    (hDec : DecAt p O Fr deg Y N₁ G' cP Dt No Go) (hAlg : AlgAt p O hk Fr Dt rho No Go)
    (hDeg : DegAt p O hk Fr d Dt rho No Go) (hLab : LabAt p O Fr Dt rho) :
    ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
      (∀ q, HasMultideg (sig q) d ∧ OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk (o q) (sig q)) ∧
      ∑ q, sig q = asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
        (MvPolynomial.map (algebraMap O (KK O)) No) := by
  classical
  set S := (xiPl Fr O Dt.nL Go).support.image (fun mo => fun i => multideg mo i) with hS
  have hocc : ∀ δ ∈ S, Occ p O Fr Dt Go δ := by
    intro δ hδ
    obtain ⟨mo, hmo, rfl⟩ := Finset.mem_image.mp hδ
    exact ⟨mo, hmo, fun i => rfl⟩
  let e := S.equivFin
  let δq : Fin S.card → (ZMod J × ℤ → ℕ) := fun q => ((e.symm q : S) : ZMod J × ℤ → ℕ)
  let G : (ZMod J × ℤ → ℕ) → MvPolynomial (Fin n' × Fin (r + K)) O := fun δ =>
    monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))
  have hoc : ∀ q, Occ p O Fr Dt Go (δq q) := fun q => hocc _ (e.symm q).2
  choose o ho using fun q => (hDeg (δq q) (hoc q)).2
  refine ⟨S.card, o, fun q => toKK hk (G (δq q)), fun q => ⟨(hDeg (δq q) (hoc q)).1, ?_⟩, ?_⟩
  · obtain ⟨n, obd, xi, dd, h1, h2, h3⟩ := hDec (δq q) (hoc q)
    have hmon : monPh O K p Fr (labO Fr K Dt.nL rho) xi = G (δq q) := by
      simp only [monPh, G, h3]
    refine ⟨n, obd, xi, dd, labO Fr K Dt.nL rho, h1, h2, hLab.1, hLab.2, ?_, ?_⟩
    · rw [hmon]
      exact ho q
    · rw [hmon]
      rfl
  · have hAlg' : toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
        (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))) =
        asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
          (MvPolynomial.map (algebraMap O (KK O)) No) := hAlg
    rw [← hAlg']
    have hsum : ∑ q, toKK hk (G (δq q)) = ∑ δ ∈ S, toKK hk (G δ) := by
      rw [Equiv.sum_comp e.symm (fun x : S => toKK hk (G x)), Finset.sum_coe_sort S (fun δ => toKK hk (G δ))]
    rw [hsum]
    have e2 : ∑ δ ∈ S, toKK hk (G δ) = toKK hk (∑ δ ∈ S, G δ) := by
      simp only [toKK, map_sum]
    rw [e2]
    congr 1
    simp only [G]
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← map_sum, hS, sum_homComp]

end Formalism.MainNotions.Proposition5Numerics
