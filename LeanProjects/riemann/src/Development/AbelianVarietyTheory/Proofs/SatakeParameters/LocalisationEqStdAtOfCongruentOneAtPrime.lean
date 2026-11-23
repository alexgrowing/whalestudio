import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizedLatticeEqOfAdelicMatricesAgreeAtPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceMoveRationalFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumJetsTranslate
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongStdLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

def HP (P : HeightOneSpectrum (𝓞 E)) (L : Submodule (𝓞 E) (Fin N → E)) (z : Fin N → E ⊗[F] 𝔸) : Prop :=
  ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ iA F E (algebraMap (𝓞 E) E s) • z ∈ Formalism.L2.Herm.hatL (F := F) L

theorem iA_mem (s : 𝓞 E) : iA F E (algebraMap (𝓞 E) E s) ∈ Formalism.L2.Herm.intAf F E :=
  Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E s, s, rfl⟩, rfl⟩)

theorem smul_mem_hatL {L : Submodule (𝓞 E) (Fin N → E)} {a : E ⊗[F] 𝔸} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    {z : Fin N → E ⊗[F] 𝔸} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) L) : a • z ∈ Formalism.L2.Herm.hatL (F := F) L :=
  Submodule.smul_mem _ (⟨a, ha⟩ : Formalism.L2.Herm.intAf F E) hz

theorem one_notMem (P : HeightOneSpectrum (𝓞 E)) : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem mul_notMem {P : HeightOneSpectrum (𝓞 E)} {s t : 𝓞 E} (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) :
    s * t ∉ P.asIdeal :=
  fun h => (P.isPrime.mem_or_mem h).elim hs ht

variable {P : HeightOneSpectrum (𝓞 E)} {L : Submodule (𝓞 E) (Fin N → E)}

theorem HP.of_mem {z : Fin N → E ⊗[F] 𝔸} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) L) : HP P L z :=
  ⟨1, one_notMem P, by simpa using hz⟩

theorem HP.zero : HP (F := F) P L 0 := HP.of_mem (zero_mem _)

theorem HP.add {z z' : Fin N → E ⊗[F] 𝔸} (h : HP P L z) (h' : HP P L z') : HP P L (z + z') := by
  obtain ⟨s, hs, hz⟩ := h
  obtain ⟨t, ht, hz'⟩ := h'
  refine ⟨s * t, mul_notMem hs ht, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * t)) • (z + z') =
      iA F E (algebraMap (𝓞 E) E t) • (iA F E (algebraMap (𝓞 E) E s) • z) +
        iA F E (algebraMap (𝓞 E) E s) • (iA F E (algebraMap (𝓞 E) E t) • z') := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [e]
  exact add_mem (smul_mem_hatL (iA_mem t) hz) (smul_mem_hatL (iA_mem s) hz')

theorem HP.smul {a : E ⊗[F] 𝔸} (ha : IntAtA P a) {z : Fin N → E ⊗[F] 𝔸} (h : HP P L z) : HP P L (a • z) := by
  obtain ⟨t, ht, hta⟩ := ha
  obtain ⟨s, hs, hz⟩ := h
  refine ⟨t * s, mul_notMem ht hs, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (t * s)) • (a • z) =
      (iA F E (algebraMap (𝓞 E) E t) * a) • (iA F E (algebraMap (𝓞 E) E s) • z) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [e]
  exact smul_mem_hatL hta hz

theorem HP.neg {z : Fin N → E ⊗[F] 𝔸} (h : HP P L z) : HP P L (-z) := by
  obtain ⟨s, hs, hz⟩ := h
  exact ⟨s, hs, by rw [smul_neg]; exact neg_mem hz⟩

theorem HP.sub {z z' : Fin N → E ⊗[F] 𝔸} (h : HP P L z) (h' : HP P L z') : HP P L (z - z') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem HP.sum {ι : Type} (S : Finset ι) (f : ι → Fin N → E ⊗[F] 𝔸) (h : ∀ i ∈ S, HP P L (f i)) :
    HP P L (∑ i ∈ S, f i) :=
  Finset.sum_induction _ (HP P L) (fun _ _ => HP.add) HP.zero h

theorem intAtA_zero : IntAtA (F := F) P (0 : E ⊗[F] 𝔸) := by
  simpa using GlobalTheory.CongMove.intAtA_int (F := F) (P := P) 0

theorem intAtA_inv {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E s)⁻¹) := by
  have hs0 : algebraMap (𝓞 E) E s ≠ 0 := by
    intro h0
    apply hs
    rw [(IsFractionRing.injective (𝓞 E) E) (h0.trans (map_zero _).symm)]
    exact zero_mem _
  refine ⟨s, hs, ?_⟩
  rw [← map_mul, mul_inv_cancel₀ hs0, map_one]
  exact one_mem _

abbrev ev (i : Fin N) : Fin N → E ⊗[F] 𝔸 := fun j => if i = j then 1 else 0

theorem mem_hatL_std_iff (z : Fin N → E ⊗[F] 𝔸) :
    z ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E N) ↔ ∀ i, z i ∈ Formalism.L2.Herm.intAf F E :=
  Formalism.L2.Col.mem_latS_std z

theorem ev_mem_std (i : Fin N) : ev (F := F) (E := E) i ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E N) := by
  rw [mem_hatL_std_iff]
  intro j
  by_cases h : i = j
  · simp only [ev, if_pos h]; exact one_mem _
  · simp only [ev, if_neg h]; exact zero_mem _

theorem integralAt_stdLattice_iff (z : Fin N → E ⊗[F] 𝔸) :
    HP P (Formalism.L2.Col.stdLat E N) z ↔ ∀ i, IntAtA (F := F) P (z i) := by
  constructor
  · rintro ⟨s, hs, hz⟩ i
    exact ⟨s, hs, by simpa using (mem_hatL_std_iff _).1 hz i⟩
  · intro h
    rw [pi_eq_sum_univ z]
    exact HP.sum _ _ fun i _ => HP.smul (h i) (HP.of_mem (ev_mem_std i))

theorem integralAt_stdLattice_mulVec (K : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) (hK : ∀ a b, IntAtA (F := F) P (K a b))
    {z : Fin N → E ⊗[F] 𝔸} (hz : HP P (Formalism.L2.Col.stdLat E N) z) : HP P (Formalism.L2.Col.stdLat E N) (K *ᵥ z) := by
  rw [integralAt_stdLattice_iff] at hz ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_induction _ (IntAtA P) (fun _ _ => GlobalTheory.CongMove.intAtA_add) intAtA_zero
    fun j _ => GlobalTheory.CongMove.intAtA_mul (hK i j) (hz j)

theorem hatL_eq_lamAf (L : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.Herm.hatL (F := F) L = Formalism.MainNotions.S.lamAf (F := F) L := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.lamAf
  congr 1
  ext x
  simp

theorem incl_mem_hatL_iff (hL : L.FG) (hspan : Submodule.span E (L : Set (Fin N → E)) = ⊤) (u : Fin N → E) :
    (fun i => iA F E (u i)) ∈ Formalism.L2.Herm.hatL (F := F) L ↔ u ∈ L := by
  rw [hatL_eq_lamAf]
  exact GlobalTheory.AdelicLattice.incl_mem_iff (F := F) L hL hspan u

theorem exists_nsmul_mem (M : Submodule (𝓞 E) (Fin N → E)) (hspan : Submodule.span E (M : Set (Fin N → E)) = ⊤)
    (z : Fin N → E ⊗[F] 𝔸) : ∃ n : ℕ, 0 < n ∧ n • z ∈ Formalism.L2.Herm.hatL (F := F) M := by
  obtain ⟨m, hm, h⟩ := GlobalTheory.AutInhab.lamAf_absorbs (F := F) M hspan z
  refine ⟨m, hm, ?_⟩
  rw [hatL_eq_lamAf, ← Nat.cast_smul_eq_nsmul (E ⊗[F] 𝔸)]
  exact h

theorem iA_smul_incl (s : 𝓞 E) (u : Fin N → E) :
    iA F E (algebraMap (𝓞 E) E s) • (fun i => iA F E (u i)) = fun i => iA F E ((s • u) i) := by
  funext i
  simp [Algebra.smul_def]

theorem integralAt_incl_iff (hL : L.FG) (hspan : Submodule.span E (L : Set (Fin N → E)) = ⊤) (u : Fin N → E) :
    HP P L (fun i => iA F E (u i)) ↔ u ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L := by
  show _ ↔ ∃ s ∈ P.asIdeal.primeCompl, s • u ∈ L
  constructor
  · rintro ⟨s, hs, h⟩
    rw [iA_smul_incl, incl_mem_hatL_iff hL hspan] at h
    exact ⟨s, hs, h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, by rw [iA_smul_incl, incl_mem_hatL_iff hL hspan]; exact h⟩

theorem exists_nat_smul (M : Submodule (𝓞 E) (Fin N → E)) (hspan : Submodule.span E (M : Set (Fin N → E)) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ z : Fin N → E ⊗[F] 𝔸, HP P (Formalism.L2.Col.stdLat E N) z → HP P M ((c : E ⊗[F] 𝔸) • z) := by
  choose n hn hmem using fun i : Fin N => exists_nsmul_mem (F := F) M hspan (ev (F := F) (E := E) i)
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, fun z hz => ?_⟩
  have hc : ∀ i, HP (F := F) P M ((∏ j, n j) • ev (F := F) (E := E) i) := fun i => by
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    rw [hm, mul_nsmul]
    exact HP.of_mem (nsmul_mem (hmem i) _)
  rw [integralAt_stdLattice_iff] at hz
  rw [pi_eq_sum_univ z, Finset.smul_sum]
  refine HP.sum _ _ fun i _ => ?_
  rw [smul_comm, Nat.cast_smul_eq_nsmul]
  exact HP.smul (hz i) (hc i)

theorem exists_approx (g : ℕ) (hg : 1 ≤ g) {z : Fin N → E ⊗[F] 𝔸} (hz : HP P (Formalism.L2.Col.stdLat E N) z) :
    ∃ u : Fin N → E, ∃ w, HP P (Formalism.L2.Col.stdLat E N) w ∧
      z = (fun i => iA F E (u i)) + (g : E ⊗[F] 𝔸) • w := by
  obtain ⟨s, hs, h⟩ := hz
  have hl : Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E N) = Formalism.MainNotions.S.lamAf (F := F) (Formalism.L2.Col.stdLat E N) := by
    unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.lamAf
    congr 1
    ext x
    simp
  rw [hl] at h
  obtain ⟨x, -, w₀, hw₀, e⟩ := GlobalTheory.AdelicLattice.exists_approx (F := F) _ g hg _ h
  rw [← hl] at hw₀
  set a := iA F E (algebraMap (𝓞 E) E s)⁻¹ with ha
  have hinv : a * iA F E (algebraMap (𝓞 E) E s) = 1 := by
    have hs0 : algebraMap (𝓞 E) E s ≠ 0 := by
      intro h0
      apply hs
      rw [(IsFractionRing.injective (𝓞 E) E) (h0.trans (map_zero _).symm)]
      exact zero_mem _
    rw [ha, ← map_mul, inv_mul_cancel₀ hs0, map_one]
  refine ⟨fun i => (algebraMap (𝓞 E) E s)⁻¹ * x i, a • w₀, HP.smul (intAtA_inv hs) (HP.of_mem hw₀), ?_⟩
  funext i
  have ei := congrFun e i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at ei ⊢
  rw [map_mul, ← ha]
  linear_combination a * ei - z i * hinv

theorem intAtA_nat (n : ℕ) : IntAtA (F := F) P (n : E ⊗[F] 𝔸) := by
  simpa using GlobalTheory.CongMove.intAtA_int (F := F) (P := P) (n : 𝓞 E)

theorem mvL_mulVec_mem_iff (R : GL (Fin N) E) (X : Submodule (𝓞 E) (Fin N → E)) (v : Fin N → E) :
    (R : Matrix (Fin N) (Fin N) E) *ᵥ v ∈ mvL R X ↔ v ∈ X := by
  constructor
  · rintro ⟨x, hx, hxv⟩
    have hxv' : (R : Matrix (Fin N) (Fin N) E) *ᵥ x = (R : Matrix (Fin N) (Fin N) E) *ᵥ v := hxv
    have h2 := congrArg (fun w => ((R⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ w) hxv'
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    exact h2 ▸ hx
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem span_std : Submodule.span E ((Formalism.L2.Col.stdLat E N : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show _ ∈ Submodule.pi Set.univ _
  rw [Submodule.mem_pi]
  intro j _
  rw [Submodule.mem_one]
  by_cases h : i = j
  · exact ⟨1, by simp [h]⟩
  · exact ⟨0, by simp [h]⟩

theorem key_iff (y : GL (Fin N) (E ⊗[F] 𝔸)) (R : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E))
    (h : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd y M) = mvL R (stdAt E N P)) (v : Fin N → E) :
    HP P M (((y⁻¹ * ratA F R : GL (Fin N) (E ⊗[F] 𝔸)) : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) *ᵥ
        fun i => iA F E (v i)) ↔ v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.L2.Col.stdLat E N) := by
  have e : ∀ s : 𝓞 E, ((y⁻¹ : GL (Fin N) (E ⊗[F] 𝔸)) : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) *ᵥ
      (fun i => inclE 𝔸 ((s • ((R : Matrix (Fin N) (Fin N) E) *ᵥ v)) i)) =
      iA F E (algebraMap (𝓞 E) E s) • (((y⁻¹ * ratA F R : GL (Fin N) (E ⊗[F] 𝔸)) :
        Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) *ᵥ fun i => iA F E (v i)) := by
    intro s
    have h1 : (fun i => iA F E (((R : Matrix (Fin N) (Fin N) E) *ᵥ v) i)) =
        ((ratA F R : GL (Fin N) (E ⊗[F] 𝔸)) : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) *ᵥ fun i => iA F E (v i) := by
      funext i
      exact RingHom.map_mulVec _ _ _ i
    have h2 := iA_smul_incl (F := F) s ((R : Matrix (Fin N) (Fin N) E) *ᵥ v)
    change _ *ᵥ (fun i => iA F E ((s • ((R : Matrix (Fin N) (Fin N) E) *ᵥ v)) i)) = _
    rw [← h2, h1, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul]
  have hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.L2.Col.stdLat E N) ↔
      (R : Matrix (Fin N) (Fin N) E) *ᵥ v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd y M) := by
    rw [h]
    exact (mvL_mulVec_mem_iff R _ v).symm
  rw [hv]
  show _ ↔ ∃ s ∈ P.asIdeal.primeCompl, s • ((R : Matrix (Fin N) (Fin N) E) *ᵥ v) ∈ latAd y M
  constructor
  · rintro ⟨s, hs, hm⟩
    refine ⟨s, hs, ?_⟩
    rw [GlobalTheory.LatAway.mem_latAd_iff, e]
    exact hm
  · rintro ⟨s, hs, hm⟩
    refine ⟨s, hs, ?_⟩
    rw [GlobalTheory.LatAway.mem_latAd_iff, e] at hm
    exact hm

theorem localization_eq_stdAt_of_congAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ), 1 ≤ d → ∀ (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (R : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), M.FG → Submodule.span E (M : Set (Fin N → E)) = ⊤ → CongAt (F := F) P d (y⁻¹ * ratA F R) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd y M) = mvL R (stdAt E N P) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M = stdAt E N P := by
  intro F E _ _ _ _ _ _ N P d hd y R M hfg hspan hcong hloc
  have hsfin : (Formalism.L2.Col.stdLat E N).FG := GlobalTheory.DatumJets.Transl.stdLat_fg E N
  set k := y⁻¹ * ratA F R with hk
  set K : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := (↑k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) with hK
  set K' : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    (↑(k⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) with hK'
  have hKK' : K * K' = 1 := by rw [hK, hK', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hKi : ∀ a b, IntAtA P (K a b) := GlobalTheory.CongMove.intAtA_of_congAt d hcong
  have hK'i : ∀ a b, IntAtA P (K' a b) :=
    GlobalTheory.CongMove.intAtA_of_congAt d (GlobalTheory.LevFrame.congAt_inv F E N d P k hd hcong)
  obtain ⟨c, hc0, hc⟩ := exists_nat_smul (F := F) (P := P) M hspan
  have step1 : ∀ z : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F, HP P (Formalism.L2.Col.stdLat E N) z → HP P M (K *ᵥ z) := by
    intro z hz
    obtain ⟨u, w, hw, rfl⟩ := exists_approx (P := P) c hc0 hz
    have hu : HP P (Formalism.L2.Col.stdLat E N) (fun i => iA F E (u i)) := by
      have e : (fun i => iA F E (u i)) =
          ((fun i => iA F E (u i)) + ((c : ℕ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) • w) -
            ((c : ℕ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) • w := by abel
      rw [e]
      exact hz.sub (HP.smul (intAtA_nat c) hw)
    have hKu := (key_iff y R M hloc u).2 ((integralAt_incl_iff hsfin span_std u).1 hu)
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    exact hKu.add (hc _ (integralAt_stdLattice_mulVec K hKi hw))
  have step2 : ∀ h : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F, HP P M h →
      HP P (Formalism.L2.Col.stdLat E N) (K' *ᵥ h) := by
    intro h hh
    obtain ⟨n, hn, hnz⟩ := exists_nsmul_mem (F := F) (Formalism.L2.Col.stdLat E N) span_std (K' *ᵥ h)
    have hz : HP P (Formalism.L2.Col.stdLat E N) (((n : ℕ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) • (K' *ᵥ h)) :=
      HP.of_mem (by rw [Nat.cast_smul_eq_nsmul]; exact hnz)
    obtain ⟨u', w, hw, e⟩ := exists_approx (P := P) (n * c) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hn.ne' hc0.ne')) hz
    have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hinv : iA F E ((n : E)⁻¹) * ((n : ℕ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = 1 := by
      rw [← map_natCast (iA F E), ← map_mul, inv_mul_cancel₀ hnE, map_one]
    have ez : K' *ᵥ h = (fun i => iA F E ((n : E)⁻¹ * u' i)) +
        ((c : ℕ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) • w := by
      funext i
      have ei := congrFun e i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Nat.cast_mul] at ei ⊢
      rw [map_mul]
      linear_combination iA F E ((n : E)⁻¹) * ei - (K' *ᵥ h) i * hinv +
        ((c : ℕ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * w i * hinv
    have hKu : HP P M (K *ᵥ fun i => iA F E ((n : E)⁻¹ * u' i)) := by
      have e2 : (fun i => iA F E ((n : E)⁻¹ * u' i)) =
          K' *ᵥ h - ((c : ℕ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) • w := by
        rw [ez]; abel
      rw [e2, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hKK', Matrix.one_mulVec, Matrix.mulVec_smul]
      exact hh.sub (hc _ (integralAt_stdLattice_mulVec K hKi hw))
    have hu := (integralAt_incl_iff (F := F) (P := P) hsfin span_std _).2 ((key_iff y R M hloc _).1 hKu)
    rw [ez]
    exact hu.add (HP.smul (intAtA_nat c) hw)
  show Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.L2.Col.stdLat E N)
  ext u
  rw [← integralAt_incl_iff (F := F) hfg hspan u, ← integralAt_incl_iff (F := F) hsfin span_std u]
  constructor
  · intro hu
    have h3 := integralAt_stdLattice_mulVec K hKi (step2 _ hu)
    rwa [Matrix.mulVec_mulVec, hKK', Matrix.one_mulVec] at h3
  · intro hu
    have h3 := step1 _ (integralAt_stdLattice_mulVec K' hK'i hu)
    rwa [Matrix.mulVec_mulVec, hKK', Matrix.one_mulVec] at h3

end GlobalTheory.CongStdLoc
