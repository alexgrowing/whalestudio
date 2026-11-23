import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsIsotropicFlagUnitaryOneOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMapMulRightEqSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocSizeBlocks

noncomputable section

open MeasureTheory Matrix Finset Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule
open GlobalTheory.SmoothGlob (lieSet)
open scoped InnerProductSpace

namespace GlobalTheory.RealInd

variable {n a : ℕ}

abbrev Flag (n a : ℕ) : Type := Fin (a + 1) → Submodule ℂ (Fin n → ℂ)

theorem detOn_mul {g h : Matrix (Fin n) (Fin n) ℂ} {V : Submodule ℂ (Fin n → ℂ)} (hg : ∀ y ∈ V, g *ᵥ y ∈ V)
    (hh : ∀ y ∈ V, h *ᵥ y ∈ V) : detOn (g * h) V = detOn g V * detOn h V := by
  have hg' : ∀ y ∈ V, Matrix.toLin' g y ∈ V := hg
  have hh' : ∀ y ∈ V, Matrix.toLin' h y ∈ V := hh
  have hgh : ∀ y ∈ V, Matrix.toLin' (g * h) y ∈ V := fun y hy => by
    rw [Matrix.toLin'_mul]; exact hg _ (hh y hy)
  rw [detOn, detOn, detOn, dif_pos hg', dif_pos hh', dif_pos hgh, ← norm_mul, ← map_mul]
  congr 2
  ext y : 2
  simp [Matrix.toLin'_mul]

theorem detOn_one (V : Submodule ℂ (Fin n → ℂ)) : detOn 1 V = 1 := by
  have h : ∀ y ∈ V, Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ) y ∈ V := by simp
  rw [detOn, dif_pos h, show (Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ)).restrict h = 1 by ext y : 2; simp]
  simp

variable (ε : Fin n → Bool)

def opp (W : Flag n a) : Flag n a := fun i => (W i).map (Jm ε).mulVecLin

def leviOne (W : Flag n a) : Subgroup (UJ ε) where
  carrier := {g | g ∈ flagM ε W ∧ ∀ i, detOn (uMat g) (W i) = 1}
  one_mem' := ⟨(leviSub ε W).one_mem, fun _ => detOn_one _⟩
  mul_mem' := fun {g h} hg hh => ⟨(leviSub ε W).mul_mem hg.1 hh.1, fun i => by
    rw [uMat_mul, detOn_mul (fun y hy => (hg.1 i y hy).1) (fun y hy => (hh.1 i y hy).1), hg.2, hh.2, one_mul]⟩
  inv_mem' := fun {g} hg => by
    have hi : g⁻¹ ∈ flagM ε W := (leviSub ε W).inv_mem hg.1
    refine ⟨hi, fun i => ?_⟩
    have := detOn_mul (fun y hy => (hg.1 i y hy).1) (fun y hy => (hi i y hy).1)
    rwa [uMat_mul_inv, detOn_one, hg.2, one_mul, eq_comm] at this

def IsSplit (W : Flag n a) (x : Fin a → ℝ) (t : UJ ε) : Prop :=
  t ∈ flagM ε W ∧ (∀ i : Fin a, ∀ y ∈ W i.succ, uMat t *ᵥ y - (Real.exp (x i) : ℂ) • y ∈ W i.castSucc) ∧
    ∀ y : Fin n → ℂ, (∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ y) = 0) → uMat t *ᵥ y - y ∈ W (Fin.last a)

def pairing (j : Fin a → ℕ) (s : Fin a → ℂ) (x : Fin a → ℝ) : ℂ := ∑ i, (j i : ℂ) * s i * x i

def rho (n : ℕ) (j : Fin a → ℕ) (i : Fin a) : ℂ := (n : ℂ) - 2 * ∑ l ∈ Iio i, (j l : ℂ) - j i

def InChamber (x : Fin a → ℝ) : Prop := StrictAnti x ∧ ∀ i, 0 < x i

variable {ε}

def mats (S : Subgroup (UJ ε)) : Set (Matrix (Fin n) (Fin n) ℂ) := (fun g : UJ ε => uMat g) '' S

section Induced

variable {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def indFun (S : Subgroup (UJ ε)) (j : Fin a → ℕ) (W : Flag n a) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V))
    (s : Fin a → ℂ) : Submodule ℂ (UJ ε → V) where
  carrier := {f | ContinuousOn f S ∧ (∀ g ∉ S, f g = 0) ∧
    ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → u ∈ S → m ∈ S → t ∈ S → ∀ g ∈ S,
      f (u * m * t * g) = Complex.exp (pairing j (s + rho n j) x) • σ (uMat m) (f g)}
  zero_mem' := ⟨continuousOn_const, fun _ _ => rfl, by simp⟩
  add_mem' := fun {f f'} h h' => ⟨h.1.add h'.1, fun g hg => by simp [h.2.1 g hg, h'.2.1 g hg],
    fun u hu m hm x t ht h1 h2 h3 g hg => by
      simp [h.2.2 u hu m hm x t ht h1 h2 h3 g hg, h'.2.2 u hu m hm x t ht h1 h2 h3 g hg]⟩
  smul_mem' := fun c f h => ⟨h.1.const_smul c, fun g hg => by simp [h.2.1 g hg],
    fun u hu m hm x t ht h1 h2 h3 g hg => by
      simp [h.2.2 u hu m hm x t ht h1 h2 h3 g hg, smul_comm c]⟩

theorem mem_indFun_top {j : Fin a → ℕ} {W : Flag n a} {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} {s : Fin a → ℂ}
    {f : UJ ε → V} : f ∈ indFun ⊤ j W σ s ↔ Continuous f ∧
      ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → ∀ g,
        f (u * m * t * g) = Complex.exp (pairing j (s + rho n j) x) • σ (uMat m) (f g) :=
  ⟨fun h => ⟨continuousOn_univ.1 h.1, fun u hu m hm x t ht g =>
      h.2.2 u hu m hm x t ht trivial trivial trivial g trivial⟩,
    fun h => ⟨h.1.continuousOn, fun _ hg => (hg trivial).elim, fun u hu m hm x t ht _ _ _ g _ => h.2 u hu m hm x t ht g⟩⟩

theorem indFun_mul_right {S : Subgroup (UJ ε)} {j : Fin a → ℕ} {W : Flag n a}
    {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} {s : Fin a → ℂ} {f : UJ ε → V} (h : f ∈ indFun S j W σ s) {y : UJ ε}
    (hy : y ∈ S) : (fun g => f (g * y)) ∈ indFun S j W σ s :=
  ⟨h.1.comp (continuous_mul_const y).continuousOn fun _ hg => S.mul_mem hg hy,
    fun _ hg => h.2.1 _ fun e => hg ((S.mul_mem_cancel_right hy).1 e),
    fun u hu m hm x t ht h1 h2 h3 g hg => by
      simpa only [mul_assoc] using h.2.2 u hu m hm x t ht h1 h2 h3 _ (S.mul_mem hg hy)⟩

def IsKFinFun (f : UJ ε → V) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {φ : UJ ε → V | ∃ k ∈ KG ε, φ = fun g => f (g * k)})

structure IsIndModel (S C : Subgroup (UJ ε)) (μ : Measure C) (F : Submodule ℂ (UJ ε → V))
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : F →ₗ[ℂ] H) : Prop where

  dense : DenseRange ι

  norm_sq : ∀ f : F, ‖ι f‖ ^ 2 = ∫ k : C, ‖f.1 k‖ ^ 2 ∂μ

  transl : ∀ y ∈ S, ∀ f f' : F, (∀ g, f'.1 g = f.1 (g * y)) → ρ (uMat y) (ι f) = ι f'

def IsIrrTempered (M : Subgroup (UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) : Prop :=
  Nontrivial V ∧ IsIrredOn (mats M) σ ∧ ∃ (h : IsURepOn (mats M) σ) (μ : Measure M), μ.IsHaarMeasure ∧
    GlobalTheory.Orb.IsTempered μ (GlobalTheory.Orb.repVia h ((GlobalTheory.Orb.ujMat ε).comp M.subtype) fun g => ⟨g, g.2, rfl⟩)

def IsKFinIn (M : Subgroup (UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (v : V) : Prop :=
  ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ v ∈ U ∧ ∀ k ∈ KG ε ⊓ M, ∀ w ∈ U, σ (uMat k) w ∈ U

end Induced

section Admissible

variable (ε) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
  [InnerProductSpace ℂ H']

def IsAdmRep (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π ∧ (∀ v, ContinuousOn (fun g => π g v) (UJset ε)) ∧
    (∀ k ∈ Kset ε, ∀ v, ‖π k v‖ = ‖v‖) ∧ IsAdmissibleSub ε π ⊤

def IsIrrAdm (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  Nontrivial H ∧ IsAdmRep ε π ∧ IsIrredOn (UJset ε) π

def groupRep {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) :
    UJ ε →* (H →L[ℂ] H) where
  toFun g := π (uMat g)
  map_one' := h.1
  map_mul' g g' := h.2 _ g.2 _ g'.2

theorem groupRep_eq_ujRep {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn (UJset ε) π) :
    groupRep ε h.1 = GlobalTheory.Orb.ujRep h := rfl

def IsFactor (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Z Y : Submodule ℂ H)
    (π : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) : Prop :=
  IsGKSub ε ρ Z ∧ IsGKSub ε ρ Y ∧ Z ≤ Y ∧ ∃ T : H →ₗ[ℂ] H', Y.map T = kFinVec ε π ∧ (∀ w ∈ Y, T w = 0 ↔ w ∈ Z) ∧
    (∀ k ∈ Kset ε, ∀ w ∈ Y, T (ρ k w) = π k (T w)) ∧ ∀ X ∈ lieSet ε, ∀ w ∈ Y, T (dRep ρ X w) = dRep π X (T w)

def mult (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) : ℕ∞ :=
  ⨆ (r : ℕ) (_ : ∃ Z Y : Fin r → Submodule ℂ H, (∀ i, IsFactor ε ρ (Z i) (Y i) π) ∧ ∀ i l, i < l → Y i ≤ Z l),
    (r : ℕ∞)

def HasFiniteLength (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ l : ℕ, ∀ (r : ℕ) (Y : Fin (r + 1) → Submodule ℂ H), (∀ i, IsGKSub ε ρ (Y i)) → StrictMono Y → r ≤ l

end Admissible
section Opposite

variable {j : Fin a → ℕ} {W : Flag n a}

theorem opp_opp : opp ε (opp ε W) = W := funext fun i => by
  rw [opp, opp, ← Submodule.map_comp, ← mulVecLin_mul, Jm_mul_self, mulVecLin_one, Submodule.map_id]

theorem inv_mul_Jm (g : UJ ε) : uMat g⁻¹ * Jm ε = Jm ε * (uMat g)ᴴ := by
  have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
  calc uMat g⁻¹ * Jm ε = Jm ε * (Jm ε * uMat g⁻¹) * Jm ε := by rw [← mul_assoc, Jm_mul_self, one_mul]
    _ = Jm ε * ((uMat g)ᴴ * Jm ε * (uMat g * uMat g⁻¹)) * Jm ε := by rw [← mul_assoc _ (uMat g), hg]
    _ = _ := by rw [uMat_mul_inv, mul_one, mul_assoc, mul_assoc, Jm_mul_self, mul_one]

theorem conjTranspose_inv_mul_Jm (g : UJ ε) : (uMat g⁻¹)ᴴ * Jm ε = Jm ε * uMat g := by
  have := congrArg (fun x => Jm ε * x * Jm ε) (inv_mul_Jm g⁻¹)
  simp only [inv_inv, ← mul_assoc, Jm_mul_self, one_mul] at this
  rw [← this, mul_assoc, Jm_mul_self, mul_one]

theorem isIsoFlag_opp (hW : IsIsoFlag ε j W) : IsIsoFlag ε j (opp ε W) := by
  have hr : ∀ i, Module.finrank ℂ (opp ε W i) = Module.finrank ℂ (W i) := fun i =>
    GlobalTheory.RealIwasawa.finrank_map_toLin _ _ (Jm_mul_self ε) _
  refine ⟨by rw [opp, hW.1, Submodule.map_bot], fun _ _ h => Submodule.map_mono (hW.2.1 h),
    fun i => by rw [hr, hr, hW.2.2.1], ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, Jm_mul_self, one_mulVec, star_mulVec, Jm_conjTranspose,
    ← dotProduct_mulVec]
  exact hW.2.2.2 x hx y hy

theorem inv_mem_flagM_opp {g : UJ ε} (h : g ∈ flagM ε W) : g⁻¹ ∈ flagM ε (opp ε W) := by
  rintro i _ ⟨y, hy, rfl⟩
  rw [mulVecLin_apply, mulVec_mulVec, mulVec_mulVec, inv_mul_Jm, conjTranspose_inv_mul_Jm, ← mulVec_mulVec,
    ← mulVec_mulVec]
  exact ⟨⟨_, (h i y hy).2, rfl⟩, _, (h i y hy).1, rfl⟩

theorem leviOne_opp : leviOne ε (opp ε W) = leviOne ε W := by
  have le : ∀ W : Flag n a, leviOne ε W ≤ leviOne ε (opp ε W) := fun W g hg => by
    refine (Subgroup.inv_mem_iff _).1 ⟨inv_mem_flagM_opp hg.1, fun i => ?_⟩
    obtain ⟨r, C, h1, h2⟩ := GlobalTheory.IsoTorus.exists_frame (W i)
    have hC : ∀ y, y ∈ W i ↔ ∃ v, y = C *ᵥ v := fun y => ⟨fun hy => ⟨Cᴴ *ᵥ y, by rw [mulVec_mulVec, (h2 y).1 hy]⟩,
      fun ⟨v, hv⟩ => by rw [h2, hv, mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one]⟩
    have e : ∀ p : Matrix (Fin n) (Fin n) ℂ, (∀ y ∈ W i, p *ᵥ y ∈ W i) → p * C = C * (Cᴴ * p * C) := fun p hp =>
      Matrix.ext_iff_mulVec.2 fun v => by
        have := (h2 _).1 (hp _ ((hC _).2 ⟨v, rfl⟩))
        simp only [← mulVec_mulVec] at this ⊢
        exact this.symm
    rw [← hg.2 i, GlobalTheory.LeviIso.Size.detOn_of_frame _ C _ _ h1 hC (e _ fun y hy => (hg.1 i y hy).1),
      GlobalTheory.LeviIso.Size.detOn_of_frame _ (Jm ε * C) (Cᴴ * uMat g * C)ᴴ, det_conjTranspose, norm_star]
    · rw [conjTranspose_mul, Jm_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm ε), Jm_mul_self,
        Matrix.one_mul, h1]
    · intro y
      simp only [opp, Submodule.mem_map, mulVecLin_apply, hC, ← mulVec_mulVec]
      exact ⟨fun ⟨_, ⟨v, hv⟩, h⟩ => ⟨v, by rw [← h, hv]⟩, fun ⟨v, hv⟩ => ⟨_, ⟨v, rfl⟩, hv.symm⟩⟩
    · rw [← Matrix.mul_assoc, inv_mul_Jm, Matrix.mul_assoc, e _ fun y hy => (hg.1 i y hy).2]
      simp [Matrix.mul_assoc]
  exact le_antisymm (by simpa only [opp_opp] using le (opp ε W)) (le W)

end Opposite

section Structure

variable {j : Fin a → ℕ} {W : Flag n a}

variable (ε) in

theorem KG_eq : (KG ε : Set (UJ ε)) = maxK ε := by
  ext g
  refine ⟨fun h => Matrix.mem_unitaryGroup_iff'.1 h.1, fun h => ⟨Matrix.mem_unitaryGroup_iff'.2 h, ?_⟩⟩
  have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
  change uMat g * Jm ε = Jm ε * uMat g
  conv_lhs => rw [← hg, ← mul_assoc, ← mul_assoc, mul_eq_one_comm.1 h, one_mul]

theorem detOn_step {g : Matrix (Fin n) (Fin n) ℂ} {U U' : Submodule ℂ (Fin n → ℂ)} (hle : U ≤ U') {d : ℕ}
    (hd : Module.finrank ℂ U' = Module.finrank ℂ U + d) (hU : ∀ y ∈ U, g *ᵥ y ∈ U) {c : ℂ}
    (hc : ∀ y ∈ U', g *ᵥ y - c • y ∈ U) : detOn g U' = detOn g U * ‖c‖ ^ d := by
  have hU1 : ∀ y ∈ U, Matrix.toLin' g y ∈ U := hU
  have hU' : ∀ y ∈ U', Matrix.toLin' g y ∈ U' := fun y hy => by
    simpa using U'.add_mem (hle (hc y hy)) (U'.smul_mem c hy)
  set e := (Matrix.toLin' g).restrict hU'
  have he : U.submoduleOf U' ≤ (U.submoduleOf U').comap e := fun y hy => hU _ hy
  have h1 : e.restrict he = (Submodule.submoduleOfEquivOfLe hle).symm.toLinearMap ∘ₗ
      (Matrix.toLin' g).restrict hU1 ∘ₗ (Submodule.submoduleOfEquivOfLe hle).symm.symm.toLinearMap := by
    ext y : 3; rfl
  have h2 : (U.submoduleOf U').mapQ (U.submoduleOf U') e he = c • LinearMap.id := by
    ext y : 2
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.smul_apply,
      LinearMap.id_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    exact hc _ y.2
  have h3 : Module.finrank ℂ (U' ⧸ U.submoduleOf U') = d := by
    have := Submodule.finrank_quotient_add_finrank (U.submoduleOf U')
    rw [(Submodule.submoduleOfEquivOfLe hle).finrank_eq] at this
    omega
  rw [detOn, detOn, dif_pos hU1, dif_pos hU', LinearMap.det_eq_det_mul_det _ e he, h1, h2, LinearMap.det_conj,
    LinearMap.det_smul, h3]
  simp

theorem detOn_bot (g : Matrix (Fin n) (Fin n) ℂ) : detOn g ⊥ = 1 := by
  rw [detOn, dif_pos (by simp), LinearMap.det_eq_one_of_subsingleton]; simp

theorem detOn_pos {g : UJ ε} {U : Submodule ℂ (Fin n → ℂ)} (h : ∀ y ∈ U, uMat g *ᵥ y ∈ U) :
    0 < detOn (uMat g) U := by
  have := detOn_mul (inv_keeps (uMat_inv_mul g) U h) h
  rw [uMat_inv_mul, detOn_one] at this
  refine lt_of_le_of_ne (by unfold detOn; split_ifs <;> positivity) fun e => ?_
  rw [← e, mul_zero] at this
  exact one_ne_zero this

theorem IsSplit.detOn_succ (hW : IsIsoFlag ε j W) {x : Fin a → ℝ} {t : UJ ε} (ht : IsSplit ε W x t) (i : Fin a) :
    detOn (uMat t) (W i.succ) = detOn (uMat t) (W i.castSucc) * Real.exp (j i * x i) := by
  rw [detOn_step (hW.2.1 (Fin.castSucc_lt_succ (i := i)).le) (hW.2.2.1 i) (fun y hy => (ht.1 _ y hy).1) (ht.2.1 i),
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_nat_mul]

theorem detOn_flagN (hW : IsIsoFlag ε j W) {u : UJ ε} (hu : u ∈ flagN ε W) (i : Fin (a + 1)) :
    detOn (uMat u) (W i) = 1 := by
  induction i using Fin.induction with
  | zero => rw [hW.1, detOn_bot]
  | succ i ih =>
    rw [detOn_step (c := 1) (hW.2.1 (Fin.castSucc_lt_succ (i := i)).le) (hW.2.2.1 i)
      ((UnipRad.flagN_subgroup_closed_keeps n ε a j W hW).2.2 u hu _) (by simpa using hu.1 i), ih]
    simp

theorem isSplit_one : IsSplit ε W 0 1 :=
  ⟨(leviSub ε W).one_mem, fun i y _ => by simp [uMat_one], fun y _ => by simp [uMat_one]⟩

theorem IsSplit.mul {x x' : Fin a → ℝ} {t t' : UJ ε} (h : IsSplit ε W x t) (h' : IsSplit ε W x' t') :
    IsSplit ε W (x + x') (t * t') := by
  refine ⟨(leviSub ε W).mul_mem h.1 h'.1, fun i y hy => ?_, fun y hy => ?_⟩
  · convert (W _).add_mem (h.1 _ _ (h'.2.1 i y hy)).1 ((W _).smul_mem (Real.exp (x' i) : ℂ) (h.2.1 i y hy)) using 1
    rw [uMat_mul, ← mulVec_mulVec, mulVec_sub, mulVec_smul, Pi.add_apply, Real.exp_add]
    push_cast
    module
  · convert (W _).add_mem (h.1 _ _ (h'.2.2 y hy)).1 (h.2.2 y hy) using 1
    rw [uMat_mul, ← mulVec_mulVec, mulVec_sub]
    abel

theorem isSplit_of_tor (hW : IsIsoFlag ε j W) {l : Fin (a + 1)} {r : ℝ} {P : Matrix (Fin n) (Fin n) ℂ} (h0 : Pᴴ = P)
    (h1 : ∀ y, P *ᵥ y ∈ W l) (h2 : ∀ y ∈ W l, P *ᵥ y = y) {t : UJ ε}
    (ht : uMat t = GlobalTheory.IsoTorus.tor P (Jm ε * P * Jm ε) (Real.exp r) (Real.exp (-r))) :
    IsSplit ε W (fun i => if i.succ ≤ l then r else 0) t := by
  have hl : W l ≤ W (Fin.last a) := hW.2.1 (Fin.le_last l)
  set c : ℂ := (Real.exp r : ℂ) with hc
  have hH : (uMat t)ᴴ = uMat t := by
    simp [ht, GlobalTheory.IsoTorus.tor, h0, Jm_conjTranspose, hc, mul_assoc, -Complex.ofReal_exp]
  have key : ∀ y, (∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ y) = 0) → uMat t *ᵥ y = y + (c - 1) • P *ᵥ y := by
    intro y hy
    have : (Jm ε * P * Jm ε) *ᵥ y = 0 := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, GlobalTheory.RealIwasawa.proj_mulVec_eq_zero h0 h1 fun z hz => hy z (hl hz),
        mulVec_zero]
    simp [ht, GlobalTheory.IsoTorus.tor, add_mulVec, smul_mulVec, this]
  have key' : ∀ i, ∀ y ∈ W i, uMat t *ᵥ y = y + (c - 1) • P *ᵥ y := fun i y hy =>
    key y fun z hz => hW.2.2.2 z hz y (hW.2.1 (Fin.le_last i) hy)
  have keep : ∀ i, ∀ y ∈ W i, uMat t *ᵥ y ∈ W i := fun i y hy => by
    rw [key' i y hy]
    refine (W i).add_mem hy ((W i).smul_mem _ ?_)
    rcases le_total i l with h | h
    · rwa [h2 y (hW.2.1 h hy)]
    · exact hW.2.1 h (h1 y)
  refine ⟨fun i y hy => ⟨keep i y hy, hH.symm ▸ keep i y hy⟩, fun i y hy => ?_, fun y hy => ?_⟩
  · rw [key' _ y hy]
    dsimp only
    split_ifs with h
    · rw [h2 y (hW.2.1 h hy), ← hc, show y + (c - 1) • y - c • y = 0 by module]
      exact zero_mem _
    · simpa using (W _).smul_mem (c - 1) (hW.2.1 (Fin.le_castSucc_iff.2 (not_le.1 h)) (h1 y))
  · simpa [key y hy] using (W _).smul_mem (c - 1) (hl (h1 y))

theorem exists_isSplit_step (hW : IsIsoFlag ε j W) (l : Fin (a + 1)) (r : ℝ) :
    ∃ t, IsSplit ε W (fun i => if i.succ ≤ l then r else 0) t ∧
      IsSplit ε (opp ε W) (-fun i => if i.succ ≤ l then r else 0) t := by
  obtain ⟨P, h0, h1, h2⟩ := GlobalTheory.RealIwasawa.exists_proj (W l)
  have hJ := Jm_mul_self ε
  have hl : W l ≤ W (Fin.last a) := hW.2.1 (Fin.le_last l)
  have hPP : P * P = P := Matrix.ext_iff_mulVec.2 fun y => by rw [← mulVec_mulVec, h2 _ (h1 y)]
  have hi : P * Jm ε * P = 0 := GlobalTheory.RealIwasawa.proj_iso hW h0 fun y => hl (h1 y)
  set Q := Jm ε * P * Jm ε with hQ
  have hQQ : Q * Q = Q := by
    simp only [hQ, mul_assoc]; rw [← mul_assoc (Jm ε) (Jm ε), hJ, one_mul, ← mul_assoc P P, hPP]
  have hPQ : P * Q = 0 := by rw [hQ, ← mul_assoc, ← mul_assoc, hi, zero_mul]
  have hQP : Q * P = 0 := by rw [hQ, mul_assoc, mul_assoc, ← mul_assoc P, hi, mul_zero]
  set c : ℂ := (Real.exp r : ℂ) with hc
  set d : ℂ := (Real.exp (-r) : ℂ) with hd
  have hH : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ = GlobalTheory.IsoTorus.tor P Q c d := by
    simp [GlobalTheory.IsoTorus.tor, hQ, h0, Jm_conjTranspose, hc, hd, mul_assoc, -Complex.ofReal_exp]
  have hm : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ * Jm ε * GlobalTheory.IsoTorus.tor P Q c d = Jm ε := by
    have e : GlobalTheory.IsoTorus.tor P Q c d * Jm ε = Jm ε * GlobalTheory.IsoTorus.tor P Q d c := by
      simp only [GlobalTheory.IsoTorus.tor, hQ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc,
        hJ, ← mul_assoc (Jm ε) (Jm ε)]
      abel
    rw [hH, e, mul_assoc, GlobalTheory.IsoTorus.tor_tor hPP hQQ hPQ hQP, hc, hd, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Real.exp_add, ← Real.exp_add]
    simp [GlobalTheory.IsoTorus.tor_one]
  obtain ⟨t, ht, -⟩ := GlobalTheory.RealIwasawa.exists_uMat _ hm
  refine ⟨t, isSplit_of_tor hW h0 h1 h2 ht, ?_⟩
  convert isSplit_of_tor (isIsoFlag_opp hW) (l := l) (r := -r) (P := Q) (t := t)
    (by simp [hQ, h0, Jm_conjTranspose, mul_assoc]) (fun y => ⟨_, h1 (Jm ε *ᵥ y), by simp [hQ, mul_assoc]⟩) ?_ ?_ using 1
  · funext i
    simp only [Pi.neg_apply]
    split_ifs <;> simp
  · rintro _ ⟨y, hy, rfl⟩
    rw [mulVecLin_apply, mulVec_mulVec, hQ, mul_assoc, hJ, mul_one, ← mulVec_mulVec, h2 y hy]
  · rw [ht, GlobalTheory.IsoTorus.tor_symm, neg_neg, hQ]
    simp only [← mul_assoc, hJ, one_mul]
    rw [mul_assoc P, hJ, mul_one]

theorem exists_isSplit (hW : IsIsoFlag ε j W) (x : Fin a → ℝ) :
    ∃ t, IsSplit ε W x t ∧ IsSplit ε (opp ε W) (-x) t := by
  let B : AddSubmonoid (Fin a → ℝ) :=
    { carrier := {x | ∃ t, IsSplit ε W x t ∧ IsSplit ε (opp ε W) (-x) t}
      zero_mem' := ⟨1, isSplit_one, by simpa only [neg_zero] using isSplit_one⟩
      add_mem' := fun ⟨_, h⟩ ⟨_, h'⟩ => ⟨_, h.1.mul h'.1, neg_add (α := Fin a → ℝ) _ _ ▸ h.2.mul h'.2⟩ }
  rw [← Finset.univ_sum_single x]
  refine B.sum_mem fun i _ => ?_
  convert B.add_mem (exists_isSplit_step hW i.succ (x i)) (exists_isSplit_step hW i.castSucc (-x i)) using 1
  funext l
  rcases lt_trichotomy l i with h | rfl | h
  · simp [h.ne, h.le, Fin.succ_le_castSucc_iff, h]
  · simp
  · simp [h.ne', h.not_ge, Fin.succ_le_castSucc_iff, h.le.not_gt]

theorem existsUnique_isSplit (hW : IsIsoFlag ε j W) (x : Fin a → ℝ) : ∃! t, IsSplit ε W x t := by
  have ex : ∀ x : Fin a → ℝ, ∃ t, IsSplit ε W x t := fun x => (exists_isSplit hW x).imp fun _ h => h.1
  obtain ⟨t, ht⟩ := ex x
  obtain ⟨t₀, h₀⟩ := ex (-x)
  have one : ∀ t', IsSplit ε W x t' → t' * t₀ = 1 := fun t' h => by
    have h1 := h.mul h₀
    rw [add_neg_cancel] at h1
    exact GlobalTheory.RealIwasawa.eq_one_of_mul_mem_compact hW _ ⟨fun i y hy => by simpa using h1.2.1 i y hy, h1.2.2⟩ _
      ((leviSub ε W).inv_mem h1.1) (by rw [mul_inv_cancel]; exact (compactSub ε).one_mem)
  exact ⟨t, ht, fun t' h => mul_right_cancel ((one t' h).trans (one t ht).symm)⟩

theorem IsSplit.opp (hW : IsIsoFlag ε j W) {x : Fin a → ℝ} {t : UJ ε} (ht : IsSplit ε W x t) :
    IsSplit ε (opp ε W) (-x) t := by
  obtain ⟨t', h1, h2⟩ := exists_isSplit hW x
  rwa [(existsUnique_isSplit hW x).unique ht h1]

theorem exists_leviOne_mul (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) {l : UJ ε} (hl : l ∈ flagM ε W) :
    ∃ m ∈ leviOne ε W, ∃ x t, IsSplit ε W x t ∧ l = m * t := by
  have hp : ∀ i, 0 < detOn (uMat l) (W i) := fun i => detOn_pos fun y hy => (hl i y hy).1
  obtain ⟨t, ht, -⟩ := existsUnique_isSplit hW fun i =>
    Real.log (detOn (uMat l) (W i.succ) / detOn (uMat l) (W i.castSucc)) / j i
  have he : ∀ i, detOn (uMat t) (W i) = detOn (uMat l) (W i) := fun i => by
    induction i using Fin.induction with
    | zero => rw [hW.1, detOn_bot, detOn_bot]
    | succ i ih =>
      have : (j i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hj i; omega)
      rw [ht.detOn_succ hW, ih, mul_div_cancel₀ _ this, Real.exp_log (div_pos (hp _) (hp _)),
        mul_div_cancel₀ _ (hp _).ne']
  have hm : l * t⁻¹ ∈ flagM ε W := (leviSub ε W).mul_mem hl ((leviSub ε W).inv_mem ht.1)
  refine ⟨l * t⁻¹, ⟨hm, fun i => ?_⟩, _, t, ht, by group⟩
  have := detOn_mul (fun y hy => (hm i y hy).1) (fun y hy => (ht.1 i y hy).1)
  rw [← uMat_mul, inv_mul_cancel_right, he] at this
  exact (mul_eq_right₀ (hp i).ne').1 this.symm

theorem exists_langlands_decomp (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) {p : UJ ε}
    (hp : ∀ i, ∀ y ∈ W i, uMat p *ᵥ y ∈ W i) :
    ∃ u ∈ flagN ε W, ∃ m ∈ leviOne ε W, ∃ x t, IsSplit ε W x t ∧ p = u * m * t := by
  obtain ⟨l, hl, hu⟩ := GlobalTheory.RealIwasawa.exists_unip_mul_levi hW p hp
  obtain ⟨m, hm, x, t, ht, rfl⟩ := exists_leviOne_mul hW hj hl
  exact ⟨_, hu, m, hm, x, t, ht, by group⟩

theorem exists_gram (U : Submodule ℂ (Fin n → ℂ)) : ∃ w : UJ ε → ℝ, Continuous w ∧ w 1 = 1 ∧
    (∀ g, ∀ k ∈ KG ε, w (g * k) = w g) ∧
    ∀ p, (∀ y ∈ U, uMat p *ᵥ y ∈ U) → ∀ g, w (p * g) * detOn (uMat p) U ^ 2 = w g := by
  obtain ⟨r, C, h1, h2⟩ := GlobalTheory.IsoTorus.exists_frame U
  have hc : Continuous fun g : UJ ε => uMat g⁻¹ * C := (continuous_uMat.comp continuous_inv).matrix_mul continuous_const
  refine ⟨fun g => ‖((uMat g⁻¹ * C)ᴴ * (uMat g⁻¹ * C)).det‖, (hc.matrix_conjTranspose.matrix_mul hc).matrix_det.norm,
    by simp [uMat_one, h1], fun g k hk => ?_, fun p hp g => ?_⟩
  · have : (uMat k⁻¹)ᴴ * uMat k⁻¹ = 1 := Matrix.mem_unitaryGroup_iff'.1 ((KG ε).inv_mem hk).1
    simp only [_root_.mul_inv_rev, uMat_mul, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (uMat k⁻¹)ᴴ, this, Matrix.one_mul]
  · have hC : ∀ y, y ∈ U ↔ ∃ v, y = C *ᵥ v := fun y => ⟨fun hy => ⟨Cᴴ *ᵥ y, by rw [mulVec_mulVec, (h2 y).1 hy]⟩,
      fun ⟨v, hv⟩ => by rw [h2, hv, mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one]⟩
    have e : uMat p * C = C * (Cᴴ * uMat p * C) := Matrix.ext_iff_mulVec.2 fun v => by
      have := (h2 _).1 (hp _ ((hC _).2 ⟨v, rfl⟩))
      simp only [← mulVec_mulVec] at this ⊢
      exact this.symm
    have e' : uMat g⁻¹ * C = uMat (p * g)⁻¹ * C * (Cᴴ * uMat p * C) := by
      rw [Matrix.mul_assoc, ← e, ← Matrix.mul_assoc, ← uMat_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
    simp only
    rw [GlobalTheory.LeviIso.Size.detOn_of_frame _ C _ U h1 hC e, e']
    generalize uMat (p * g)⁻¹ * C = B
    generalize Cᴴ * uMat p * C = X
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ, det_mul, det_mul, det_conjTranspose, norm_mul,
      norm_mul, norm_star]
    ring

theorem exists_height (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) : ∃ h : UJ ε → Fin a → ℝ, Continuous h ∧ h 1 = 0 ∧
    (∀ g, ∀ k ∈ KG ε, h (g * k) = h g) ∧
    ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → ∀ g, h (u * m * t * g) = x + h g := by
  choose w hc h1 hK hP using fun i => exists_gram (ε := ε) (W i)
  have hpos : ∀ i g, w i g ≠ 0 := fun i g e => by
    obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW g
    have := hP i _ (hp i) 1
    rw [mul_one, hK i g _ ((KG ε).inv_mem ((KG_eq ε).symm ▸ hk :)), e, h1, zero_mul] at this
    exact zero_ne_one this
  refine ⟨fun g i => (Real.log (w i.castSucc g) - Real.log (w i.succ g)) / (2 * j i), continuous_pi fun i =>
    (((hc _).log (hpos _)).sub ((hc _).log (hpos _))).div_const _, by funext i; simp [h1],
    fun g k hk => by simp only [hK _ g k hk], fun u hu m hm x t ht g => funext fun i => ?_⟩
  have hu' := (UnipRad.flagN_subgroup_closed_keeps n ε a j W hW).2.2 u hu
  have e : ∀ l, Real.log (w l (u * m * t * g)) = Real.log (w l g) - 2 * Real.log (detOn (uMat t) (W l)) := fun l => by
    have a1 := hP l u (hu' l) (m * (t * g))
    have a2 := hP l m (fun y hy => (hm.1 l y hy).1) (t * g)
    have a3 := hP l t (fun y hy => (ht.1 l y hy).1) g
    rw [detOn_flagN hW hu, one_pow, mul_one] at a1
    rw [hm.2, one_pow, mul_one] at a2
    rw [mul_assoc, mul_assoc, a1, a2, ← a3, Real.log_mul (hpos _ _)
      (pow_ne_zero _ (detOn_pos fun y hy => (ht.1 l y hy).1).ne'), Real.log_pow]
    push_cast; ring
  have : (j i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hj i; omega)
  simp only [e, Pi.add_apply]
  rw [ht.detOn_succ hW, Real.log_mul (detOn_pos fun y hy => (ht.1 _ y hy).1).ne' (Real.exp_pos _).ne', Real.log_exp]
  field_simp
  ring

end Structure

section Model

variable {j : Fin a → ℕ} {W : Flag n a}

variable (ε W) in

def parab : Subgroup (UJ ε) where
  carrier := {g | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i}
  one_mem' := fun i y hy => by simpa [uMat_one] using hy
  mul_mem' := fun {g h} hg hh i y hy => by rw [uMat_mul, ← mulVec_mulVec]; exact hg i _ (hh i y hy)
  inv_mem' := fun {g} hg i => inv_keeps (uMat_inv_mul g) _ (hg i)

theorem isClosed_parab : IsClosed (parab ε W : Set (UJ ε)) := by
  change IsClosed {g : UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ =>
    (W i).closed_of_finiteDimensional.preimage (continuous_uMat.matrix_mulVec continuous_const)

open scoped Pointwise in

theorem lintegral_transl_le (hW : IsIsoFlag ε j W) {c : UJ ε → ℝ} (hc : Continuous c) (hc0 : ∀ g, 0 < c g)
    (y : UJ ε) : ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ Φ : UJ ε → ENNReal, Measurable Φ →
      (∀ p ∈ parab ε W, ∀ g, Φ (p * g) = ENNReal.ofReal (c p) * Φ g) →
      ∫⁻ k : KG ε, Φ (k * y) ∂muK ε ≤ C * ∫⁻ k : KG ε, Φ k ∂muK ε := by
  have hP := isClosed_parab (ε := ε) (W := W)
  have hK : IsCompact (KG ε : Set (UJ ε)) := isCompact_iff_compactSpace.2 (instCompactKG n ε)
  haveI : LocallyCompactSpace (parab ε W) := hP.locallyCompactSpace
  haveI : IsProbabilityMeasure (muK ε) := ⟨Measure.haarMeasure_self⟩
  haveI : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  have inv : ∀ (S : Subgroup (UJ ε)) (ν : Measure S) [ν.IsMulLeftInvariant], ∀ s ∈ S,
      (ν.map Subtype.val).map (fun g => s * g) = ν.map Subtype.val := fun S ν _ s hs => by
    conv_rhs => rw [← map_mul_left_eq_self ν ⟨s, hs⟩]
    rw [Measure.map_map (measurable_const_mul s) measurable_subtype_coe,
      Measure.map_map measurable_subtype_coe (measurable_const_mul _)]
    rfl
  set κ : Measure (UJ ε) := (muK ε).map Subtype.val with hκ
  set ρ : Measure (UJ ε) := (Measure.haar : Measure (parab ε W)).map Subtype.val with hρ
  haveI : IsProbabilityMeasure κ := Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  haveI : IsFiniteMeasureOnCompacts ρ := ⟨fun T hT => by
    rw [hρ, Measure.map_apply measurable_subtype_coe hT.measurableSet]
    exact (hP.isClosedEmbedding_subtypeVal.isCompact_preimage hT).measure_lt_top⟩
  have aP : ∀ᵐ p ∂ρ, p ∈ parab ε W :=
    (ae_map_iff measurable_subtype_coe.aemeasurable hP.measurableSet).2 (.of_forall fun p => p.2)
  obtain ⟨B, hB, hB1⟩ := exists_compact_mem_nhds (1 : UJ ε)
  have pos : ∀ T : Set (UJ ε), IsCompact T → B ⊆ T → ρ T ≠ 0 := fun T hT h => by
    rw [hρ, Measure.map_apply measurable_subtype_coe hT.measurableSet]
    exact (Measure.measure_pos_of_mem_nhds _ (continuous_subtype_val.continuousAt.preimage_mem_nhds
      (Filter.mem_of_superset hB1 h : T ∈ nhds ((1 : parab ε W) : UJ ε)))).ne'
  have hT := hK.mul hB
  have hT0 := pos _ hT fun b hb => ⟨1, one_mem _, b, hb, one_mul b⟩
  have hTK : ∀ k ∈ KG ε, ∀ g ∈ (KG ε : Set (UJ ε)) * B, k * g ∈ (KG ε : Set (UJ ε)) * B := by
    rintro k hk _ ⟨k', hk', b, hb, rfl⟩
    exact ⟨k * k', mul_mem hk hk', b, hb, mul_assoc _ _ _⟩
  obtain ⟨e, e0, e1, he⟩ := GlobalTheory.IwasawaShape.exists_lintegral_eq_mul (muG ε) ρ κ (NeZero.ne _) (parab ε W) (KG ε)
    (inv _ _) (inv _ _) (GlobalTheory.IwasawaShape.exists_map_mul_right_eq_smul _ hP.measurableSet ρ (mem_ae_iff.1 aP) (inv _ _)
      _ hT.measurableSet hT0 hT.measure_ne_top)
    (fun g => by
      obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW g
      exact ⟨_, hp, k, (KG_eq ε).symm ▸ hk, by group⟩)
    _ hT.measurableSet (fun k hk g => ⟨fun h => by simpa using hTK k hk _ h, hTK _ (inv_mem hk) g⟩) hT0
    hT.measure_ne_top
  have hcm : Measurable fun p => ENNReal.ofReal (c p) := hc.measurable.ennreal_ofReal
  have main : ∀ D : Set (UJ ε), IsCompact D → ∀ Φ : UJ ε → ENNReal, Measurable Φ →
      (∀ p ∈ parab ε W, ∀ g, Φ (p * g) = ENNReal.ofReal (c p) * Φ g) →
      ∫⁻ g, (D * (KG ε : Set (UJ ε))).indicator Φ g ∂muG ε =
        e * ((∫⁻ p in D * (KG ε : Set (UJ ε)), ENNReal.ofReal (c p) ∂ρ) * ∫⁻ k : KG ε, Φ k ∂muK ε) := by
    intro D hD Φ hΦ h
    have hm := (hD.mul hK).measurableSet
    rw [he _ (hΦ.indicator hm), ← lintegral_indicator hm, ← lintegral_mul_const _ (hcm.indicator hm)]
    congr 1
    refine lintegral_congr_ae (aP.mono fun p hp => ?_)
    dsimp only
    rw [hκ, lintegral_map (f := fun k => (D * (KG ε : Set (UJ ε))).indicator Φ (p * k))
      ((hΦ.indicator hm).comp (measurable_const_mul p)) measurable_subtype_coe,
      ← lintegral_const_mul (f := fun k : KG ε => Φ k) _ (hΦ.comp measurable_subtype_coe)]
    refine lintegral_congr fun k => ?_
    have st : ∀ k ∈ KG ε, ∀ g ∈ D * (KG ε : Set (UJ ε)), g * k ∈ D * (KG ε : Set (UJ ε)) := by
      rintro k hk _ ⟨b, hb, k', hk', rfl⟩
      exact ⟨b, hb, k' * k, mul_mem hk' hk, (mul_assoc _ _ _).symm⟩
    by_cases hpD : p ∈ D * (KG ε : Set (UJ ε))
    · rw [Set.indicator_of_mem hpD, Set.indicator_of_mem (st k k.2 p hpD), h p hp]
    · rw [Set.indicator_of_notMem hpD, Set.indicator_of_notMem fun e => hpD (by simpa using st _ (inv_mem k.2) _ e),
        zero_mul]
  have fin : ∀ D : Set (UJ ε), IsCompact D → ∫⁻ p in D, ENNReal.ofReal (c p) ∂ρ ≠ ⊤ := fun D hD =>
    (hc.continuousOn.integrableOn_compact hD).lintegral_lt_top.ne
  have hD := (hB.mul hK).mul (isCompact_singleton (x := y))
  have I0 : ∫⁻ p in B * (KG ε : Set (UJ ε)), ENNReal.ofReal (c p) ∂ρ ≠ 0 := fun h => by
    rw [lintegral_eq_zero_iff hcm] at h
    refine pos _ (hB.mul hK) (fun b hb => ⟨b, hb, 1, one_mem _, mul_one b⟩) ?_
    rw [← Measure.restrict_eq_zero, ← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
    exact h.mono fun p hp => (ENNReal.ofReal_pos.2 (hc0 p)).ne' hp
  refine ⟨_ / _, ENNReal.div_ne_top (fin _ (hD.mul hK)) I0, fun Φ hΦ h => ?_⟩
  have h1 := main B hB (fun g => Φ (g * y)) (hΦ.comp (measurable_mul_const y)) fun p hp g => by rw [mul_assoc, h p hp]
  have h2 := main _ hD Φ hΦ h
  have h3 : ∫⁻ g, (B * (KG ε : Set (UJ ε))).indicator (fun g => Φ (g * y)) g ∂muG ε ≤
      ∫⁻ g, (B * (KG ε : Set (UJ ε)) * {y} * (KG ε : Set (UJ ε))).indicator Φ g ∂muG ε := by
    rw [← lintegral_mul_right_eq_self ((B * (KG ε : Set (UJ ε)) * {y} * (KG ε : Set (UJ ε))).indicator Φ) y]
    refine lintegral_mono fun g => Set.indicator_apply_le' (fun hg => ?_) fun _ => zero_le
    exact (Set.indicator_of_mem (s := B * (KG ε : Set (UJ ε)) * {y} * (KG ε : Set (UJ ε)))
      (Set.mem_mul.2 ⟨g * y, Set.mul_mem_mul hg rfl, 1, one_mem (KG ε), mul_one _⟩) Φ).ge
  rw [h1, h2, ENNReal.mul_le_mul_iff_right e0 e1] at h3
  rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (.inl I0) (.inl (fin _ (hB.mul hK))),
    mul_comm]
  exact h3

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}

theorem exists_isIndModel_of_bound [CompleteSpace V] (F : Submodule ℂ (UJ ε → V)) (hcont : ∀ f ∈ F, Continuous f)
    (hR : ∀ f ∈ F, ∀ y, (fun g => f (g * y)) ∈ F)
    (hb : ∀ y, ∃ C, 0 ≤ C ∧ ∀ f ∈ F, ∫ k : KG ε, ‖f (k * y)‖ ^ 2 ∂muK ε ≤ C * ∫ k : KG ε, ‖f k‖ ^ 2 ∂muK ε) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : F →ₗ[ℂ] H), IsIndModel ⊤ (KG ε) (muK ε) F ρ ι := by
  classical
  haveI : IsProbabilityMeasure (muK ε) := ⟨Measure.haarMeasure_self⟩
  let r : F →ₗ[ℂ] C(KG ε, V) :=
    { toFun := fun f => ⟨fun k => f.1 k, (hcont f f.2).comp continuous_subtype_val⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨L, _, _, _, ι₀, hn⟩ : ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L)
      (_ : CompleteSpace L) (ι₀ : F →ₗ[ℂ] L), ∀ f, ‖ι₀ f‖ ^ 2 = ∫ k : KG ε, ‖f.1 k‖ ^ 2 ∂muK ε := by
    refine ⟨Lp V 2 (muK ε), _, _, inferInstance, (ContinuousMap.toLp 2 (muK ε) ℂ).toLinearMap ∘ₗ r, fun f => ?_⟩
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    refine integral_congr_ae ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (muK ε) (r f)).mono fun k hk => ?_)
    dsimp only
    rw [inner_self_eq_norm_sq, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hk]
    rfl
  let H := (LinearMap.range ι₀).topologicalClosure
  haveI : CompleteSpace H := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let ι : F →ₗ[ℂ] H := ι₀.codRestrict H fun f => Submodule.le_topologicalClosure _ ⟨f, rfl⟩
  have hd : DenseRange ι := fun x => by
    rw [closure_subtype, ← Set.range_comp]
    exact x.2
  let R : UJ ε → (F →ₗ[ℂ] F) := fun y =>
    { toFun := fun f => ⟨_, hR _ f.2 y⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hb' : ∀ y, ∃ C, ∀ f, ‖(ι ∘ₗ R y) f‖ ≤ C * ‖ι f‖ := fun y => by
    obtain ⟨C, hC, hle⟩ := hb y
    refine ⟨√C, fun f => (abs_le_of_sq_le_sq' ?_ (by positivity)).2⟩
    change ‖ι₀ (R y f)‖ ^ 2 ≤ (√C * ‖ι₀ f‖) ^ 2
    rw [mul_pow, Real.sq_sqrt hC, hn, hn]
    exact hle _ f.2
  refine ⟨H, inferInstance, inferInstance, this,
    fun g => if e : ∃ y : UJ ε, uMat y = g then (ι ∘ₗ R e.choose).extendOfNorm ι else 0, ι, hd, hn,
    fun y _ f f' e => ?_⟩
  have ex : ∃ y' : UJ ε, uMat y' = uMat y := ⟨y, rfl⟩
  have : ex.choose = y := Subtype.ext (Units.ext ex.choose_spec)
  rw [dif_pos ex, this, LinearMap.extendOfNorm_eq hd (hb' y)]
  exact congrArg ι (Subtype.ext (funext fun g => (e g).symm))

theorem exists_isIndModel [CompleteSpace V] (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i)
    (hσ : ∀ m ∈ leviOne ε W, ∀ v, ‖σ (uMat m) v‖ = ‖v‖) (s : Fin a → ℂ) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : indFun (ε := ε) ⊤ j W σ s →ₗ[ℂ] H),
      IsIndModel ⊤ (KG ε) (muK ε) _ ρ ι := by
  haveI : IsProbabilityMeasure (muK ε) := ⟨Measure.haarMeasure_self⟩
  have hcont : ∀ f ∈ indFun (ε := ε) ⊤ j W σ s, Continuous f := fun f hf => (mem_indFun_top.1 hf).1
  refine exists_isIndModel_of_bound _ hcont (fun f hf y => indFun_mul_right hf trivial) fun y => ?_
  obtain ⟨h, hc, h1, -, hh⟩ := exists_height hW hj
  obtain ⟨C, hC, hle⟩ := lintegral_transl_le hW (c := fun g => ‖Complex.exp (pairing j (s + rho n j) (h g))‖ ^ 2)
    (by unfold pairing; fun_prop) (fun g => pow_pos (norm_pos_iff.2 (Complex.exp_ne_zero _)) 2) y
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun f hf => ?_⟩
  have e : ∀ f : UJ ε → V, Continuous f → ENNReal.ofReal (∫ k : KG ε, ‖f k‖ ^ 2 ∂muK ε) =
      ∫⁻ k : KG ε, ENNReal.ofReal (‖f k‖ ^ 2) ∂muK ε := fun f hf =>
    ofReal_integral_eq_lintegral_ofReal (((hf.comp continuous_subtype_val).norm.pow 2).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact) (.of_forall fun k => by positivity)
  have := hle (fun g => ENNReal.ofReal (‖f g‖ ^ 2)) ((hcont f hf).norm.pow 2).measurable.ennreal_ofReal
    fun p hp g => by
      obtain ⟨u, hu, m, hm, x, t, ht, rfl⟩ := exists_langlands_decomp hW hj hp
      have := hh u hu m hm x t ht 1
      rw [mul_one, h1, add_zero] at this
      rw [(mem_indFun_top.1 hf).2 u hu m hm x t ht, this, norm_smul, hσ m hm, mul_pow,
        ENNReal.ofReal_mul (by positivity)]
  rwa [← e f (hcont f hf), ← e (fun g => f (g * y)) ((hcont f hf).comp (continuous_mul_const y)),
    ← ENNReal.ofReal_toReal hC, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg ENNReal.toReal_nonneg (integral_nonneg fun _ => by positivity))] at this

theorem exists_spherical (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) (s : Fin a → ℂ) :
    ∃ f ∈ indFun (ε := ε) ⊤ j W (fun _ => (1 : ℂ →L[ℂ] ℂ)) s, f 1 = 1 ∧ ∀ g, ∀ k ∈ KG ε, f (g * k) = f g := by
  obtain ⟨h, hc, h1, hK, hh⟩ := exists_height hW hj
  refine ⟨fun g => Complex.exp (pairing j (s + rho n j) (h g)), mem_indFun_top.2 ⟨by unfold pairing; fun_prop,
    fun u hu m hm x t ht g => ?_⟩, by simp [h1, pairing], fun g k hk => by simp only [hK g k hk]⟩
  simp [hh u hu m hm x t ht, pairing, mul_add, Finset.sum_add_distrib, Complex.exp_add]

theorem isClosed_leviOne (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) : IsClosed (leviOne ε W : Set (UJ ε)) := by
  obtain ⟨h, hc, h1, -, hh⟩ := exists_height hW hj
  have h0 : (1 : UJ ε) ∈ flagN ε W := ⟨fun i y _ => by simp [uMat_one], fun y _ => by simp [uMat_one]⟩
  convert (isClosed_flagM W).inter (isClosed_eq hc (continuous_const (y := 0))) using 1
  ext l
  refine ⟨fun hl => ⟨hl.1, by simpa [h1] using hh 1 h0 l hl 0 1 isSplit_one 1⟩, fun hl => ?_⟩
  obtain ⟨m, hm, x, t, ht, rfl⟩ := exists_leviOne_mul hW hj hl.1
  have := hh 1 h0 m hm x t ht 1
  rw [one_mul, mul_one, h1, add_zero, show h (m * t) = 0 from hl.2] at this
  rw [(existsUnique_isSplit hW x).unique ht (this ▸ isSplit_one), mul_one]
  exact hm

end Model

section Models

variable {V H H' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {S C : Subgroup (UJ ε)} {μ : Measure C}
  {F : Submodule ℂ (UJ ε → V)} {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ι : F →ₗ[ℂ] H}
  {ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} {ι' : F →ₗ[ℂ] H'}

omit [InnerProductSpace ℂ V] in
theorem mats_top : mats (⊤ : Subgroup (UJ ε)) = UJset ε := by
  ext g
  exact ⟨fun ⟨y, _, h⟩ => h ▸ y.2, fun h => let ⟨y, hy, _⟩ := GlobalTheory.RealIwasawa.exists_uMat g h; ⟨y, trivial, hy⟩⟩

theorem IsIndModel.isCRepOn (h : IsIndModel S C μ F ρ ι) (hR : ∀ f ∈ F, ∀ y ∈ S, (fun g => f (g * y)) ∈ F) :
    Formalism.QuantumDeterminants.IsCRepOn (mats S) ρ := by
  refine ⟨ContinuousLinearMap.ext fun v => ?_, ?_⟩
  · exact h.dense.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun f => h.transl 1 S.one_mem f f (by simp)
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    refine ContinuousLinearMap.ext fun v => h.dense.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun f => ?_
    rw [ContinuousLinearMap.comp_apply, h.transl z hz f ⟨_, hR _ f.2 z hz⟩ fun _ => rfl,
      h.transl y hy _ ⟨_, hR _ f.2 _ (S.mul_mem hy hz)⟩ fun _ => by simp [mul_assoc]]
    exact h.transl _ (S.mul_mem hy hz) _ _ fun _ => rfl

theorem IsIndModel.unique [CompleteSpace H] [CompleteSpace H'] (h : IsIndModel S C μ F ρ ι)
    (h' : IsIndModel S C μ F ρ' ι') (hR : ∀ f ∈ F, ∀ y ∈ S, (fun g => f (g * y)) ∈ F) :
    ∃ U : H ≃ₗᵢ[ℂ] H', (∀ f, U (ι f) = ι' f) ∧ ∀ g ∈ mats S, ∀ v, U (ρ g v) = ρ' g (U v) := by
  have hn : ∀ f, ‖ι' (LinearEquiv.refl ℂ F f)‖ = ‖ι f‖ := fun f =>
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ((h'.norm_sq f).trans (h.norm_sq f).symm)
  have e := (LinearEquiv.refl ℂ F).extendOfIsometry_eq ι ι' h.dense h'.dense hn
  refine ⟨_, e, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ v
  refine h.dense.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun f => ?_
  rw [h.transl y hy f ⟨_, hR _ f.2 y hy⟩ fun _ => rfl, e, e]
  exact (h'.transl y hy _ _ fun _ => rfl).symm

theorem leviOne_zero {j : Fin 0 → ℕ} {W : Flag n 0} (hW : IsIsoFlag ε j W) : leviOne ε W = ⊤ := by
  have h : ∀ i, W i = ⊥ := fun i => by rw [Fin.eq_zero i, hW.1]
  exact eq_top_iff.2 fun g _ => ⟨fun i y hy => by rw [h] at hy ⊢; simp_all, fun i => by rw [h, detOn_bot]⟩

theorem isIndModel_zero {j : Fin 0 → ℕ} {W : Flag n 0} (hW : IsIsoFlag ε j W)
    {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hσ : IsURepOn (UJset ε) σ) (s : Fin 0 → ℂ) :
    IsIndModel ⊤ (KG ε) (muK ε) (indFun ⊤ j W σ s) σ (LinearMap.proj 1 ∘ₗ Submodule.subtype _) := by
  haveI : IsProbabilityMeasure (muK ε) := ⟨Measure.haarMeasure_self⟩
  have one : ∀ {u : UJ ε}, (∀ y, (∀ z ∈ W (Fin.last 0), star z ⬝ᵥ (Jm ε *ᵥ y) = 0) → uMat u *ᵥ y - y ∈ W (Fin.last 0)) →
      u = 1 := fun {u} hu => Subtype.ext (Units.ext (Matrix.ext_iff_mulVec.2 fun y => by
    have h0 : W (Fin.last 0) = ⊥ := hW.1
    have := hu y (by rw [h0]; simp)
    rw [h0, Submodule.mem_bot, sub_eq_zero] at this
    exact this.trans (one_mulVec y).symm))
  have law : ∀ f ∈ indFun (ε := ε) ⊤ j W σ s, ∀ g, f g = σ (uMat g) (f 1) := fun f hf g => by
    simpa [pairing] using (mem_indFun_top.1 hf).2 1 ⟨fun i => i.elim0, fun y _ => by simp [uMat_one]⟩ g
      (leviOne_zero hW ▸ trivial) 0 1 isSplit_one 1
  refine ⟨Function.Surjective.denseRange fun v => ⟨⟨fun g => σ (uMat g) v, mem_indFun_top.2
    ⟨(hσ.2.2 v).comp_continuous continuous_uMat fun g => g.2, fun u hu m hm x t ht g => ?_⟩⟩, ?_⟩,
    fun f => ?_, fun y _ f f' e => ?_⟩
  · rw [one hu.2, one ht.2.2, one_mul, mul_one, uMat_mul, hσ.1.2 _ m.2 _ g.2]
    simp [pairing]
  · simp [uMat_one, hσ.1.1]
  · have : ∀ k : KG ε, ‖f.1 k‖ = ‖f.1 1‖ := fun k => by rw [law _ f.2, hσ.2.1 _ k.1.2]
    simp [this]
  · simpa [e] using (law _ f.2 y).symm

theorem isIrrTempered_top_iff {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (μ : Measure (UJ ε)) [μ.IsHaarMeasure] :
    IsIrrTempered (⊤ : Subgroup (UJ ε)) σ ↔ Nontrivial V ∧ IsIrredOn (UJset ε) σ ∧
      ∃ h : IsURepOn (UJset ε) σ, GlobalTheory.Orb.IsTempered μ (GlobalTheory.Orb.ujRep h) := by
  let e : (⊤ : Subgroup (UJ ε)) ≃ₜ* UJ ε :=
    { Subgroup.topEquiv with continuous_toFun := continuous_subtype_val
                             continuous_invFun := continuous_id.subtype_mk _ }
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have he' : MeasurableEmbedding e.symm := e.symm.toHomeomorph.measurableEmbedding
  refine and_congr_right fun _ => and_congr (by rw [mats_top]) ⟨fun ⟨h, ν, _, v, hv, hi⟩ => ⟨mats_top ▸ h, v, hv,
    fun r hr => ?_⟩, fun ⟨h, v, hv, hi⟩ => ⟨mats_top.symm ▸ h, μ.map e.symm, inferInstance, v, hv, fun r hr => ?_⟩⟩
  · rw [Measure.isMulLeftInvariant_eq_smul μ (ν.map e)]
    refine Integrable.smul_measure_nnreal (he.integrable_map_iff.2 ?_)
    exact hi r hr
  · exact he'.integrable_map_iff.2 (hi r hr)

theorem isIrrTempered_one {M : Subgroup (UJ ε)} (hM : IsClosed (M : Set (UJ ε))) (hK : M ≤ KG ε) :
    IsIrrTempered M fun _ => (1 : ℂ →L[ℂ] ℂ) := by
  haveI : CompactSpace M := isCompact_iff_compactSpace.1
    ((isCompact_iff_compactSpace.2 (instCompactKG n ε)).of_isClosed_subset hM hK)
  have h : IsURepOn (mats M) fun _ => (1 : ℂ →L[ℂ] ℂ) := ⟨⟨rfl, fun _ _ _ _ => rfl⟩, fun _ _ _ => rfl,
    fun _ => continuousOn_const⟩
  exact ⟨inferInstance, fun S _ _ => eq_bot_or_eq_top S, h, Measure.haar, inferInstance,
    GlobalTheory.Orb.isTempered_of_finite ⟨fun _ _ => rfl, fun _ => continuous_const⟩⟩

end Models

variable (ε) in

structure Datum where

  a : ℕ

  j : Fin a → ℕ

  W : Flag n a

  flag : IsIsoFlag ε j W

  pos : ∀ i, 1 ≤ j i

  V : Type
  [nacg : NormedAddCommGroup V]
  [ips : InnerProductSpace ℂ V]
  [cs : CompleteSpace V]

  σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)

  temp : IsIrrTempered (leviOne ε W) σ

  s : Fin a → ℂ

attribute [instance] Datum.nacg Datum.ips Datum.cs

variable (ε) in

def IsMinimalFlag {b : ℕ} (W₀ : Flag n b) : Prop :=
  IsIsoFlag ε (fun _ => 1) W₀ ∧ ∀ (b' : ℕ) (W' : Flag n b'), IsIsoFlag ε (fun _ => 1) W' → b' ≤ b

variable (ε) in

theorem exists_isMinimalFlag : ∃ (b : ℕ) (W₀ : Flag n b), IsMinimalFlag ε W₀ := by
  classical
  let p : ℕ → Prop := fun b => ∃ W : Flag n b, IsIsoFlag ε (fun _ => 1) W
  have h0 : p 0 := ⟨fun _ => ⊥, rfl, monotone_const, fun i => i.elim0, by simp⟩
  have hb : ∀ b, p b → b ≤ n := fun b ⟨W, hW⟩ => by
    have : ∀ i : Fin (b + 1), Module.finrank ℂ (W i) = i := fun i => by
      induction i using Fin.induction with
      | zero => rw [hW.1]; simp
      | succ i ih => rw [hW.2.2.1, ih]; simp
    simpa [this] using (W (Fin.last b)).finrank_le
  obtain ⟨W, hW⟩ := Nat.findGreatest_spec (P := p) (Nat.zero_le n) h0
  exact ⟨_, W, hW, fun b' W' h => Nat.le_findGreatest (hb _ ⟨W', h⟩) ⟨W', h⟩⟩

namespace Datum

variable (D : Datum ε)

abbrev M : Subgroup (UJ ε) := leviOne ε D.W

abbrev fns : Submodule ℂ (UJ ε → D.V) := indFun ⊤ D.j D.W D.σ D.s

abbrev dualFns : Submodule ℂ (UJ ε → D.V) := indFun ⊤ D.j D.W D.σ (-star D.s)

abbrev oppFns : Submodule ℂ (UJ ε → D.V) := indFun ⊤ D.j (opp ε D.W) D.σ (-D.s)

abbrev Nbar : Set (UJ ε) := flagN ε (opp ε D.W)

def Positive : Prop := InChamber fun i => (D.s i).re

def IsStandard {b : ℕ} (W₀ : Flag n b) : Prop := (∀ i, D.W i ∈ Set.range W₀) ∧ D.Positive

def Equiv (D' : Datum ε) : Prop :=
  ∃ e : D.a = D'.a, (∀ i, D.W i = D'.W (Fin.cast (congrArg (· + 1) e) i)) ∧ (∀ i, D.s i = D'.s (Fin.cast e i)) ∧
    ∃ U : D.V ≃ₗᵢ[ℂ] D'.V, ∀ m ∈ D.M, ∀ v, U (D.σ (uMat m) v) = D'.σ (uMat m) (U v)

def IsIntegral (ν : Measure (UJ ε)) (f h : UJ ε → D.V) : Prop :=
  ∀ x v, IsKFinIn D.M D.σ v → Integrable (fun u => ⟪v, f (u * x)⟫_ℂ) ν ∧ ⟪v, h x⟫_ℂ = ∫ u, ⟪v, f (u * x)⟫_ℂ ∂ν

end Datum

variable (ε) in

structure IndModule extends Datum ε where

  H : Type
  [hacg : NormedAddCommGroup H]
  [hips : InnerProductSpace ℂ H]
  [hcs : CompleteSpace H]

  ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)

  ι : toDatum.fns →ₗ[ℂ] H

  model : IsIndModel ⊤ (KG ε) (muK ε) toDatum.fns ρ ι

attribute [instance] IndModule.hacg IndModule.hips IndModule.hcs

theorem Datum.exists_indModule (D : Datum ε) : ∃ I : IndModule ε, I.toDatum = D := by
  obtain ⟨H, _, _, _, ρ, ι, h⟩ := exists_isIndModel D.flag D.pos
    (fun m hm => D.temp.2.2.1.2.1 _ ⟨m, hm, rfl⟩) D.s
  exact ⟨{ D with H := H, ρ := ρ, ι := ι, model := h }, rfl⟩

theorem IndModule.isCRepOn (I : IndModule ε) : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) I.ρ :=
  mats_top ▸ I.model.isCRepOn fun _ hf _ hy => indFun_mul_right hf hy

def IndModule.rep (I : IndModule ε) : UJ ε →* (I.H →L[ℂ] I.H) := groupRep ε I.isCRepOn

def IndModule.intKer (I : IndModule ε) (ν : Measure (UJ ε)) : Set I.H :=
  {w | ∃ f : I.fns, IsKFinFun f.1 ∧ I.ι f = w ∧ I.IsIntegral ν f.1 0}

section Characters

variable (ε)

theorem isIrrAdm_det : IsIrrAdm ε fun g => g.det • (1 : ℂ →L[ℂ] ℂ) :=
  have h := isURepOn_det (H := ℂ) ε
  ⟨inferInstance, ⟨h.1, h.2.2, fun k hk => h.2.1 k (mem_UJset_of_mem_Kset hk), (isGKSub_det ε ⊤).2⟩,
    fun S _ _ => eq_bot_or_eq_top S⟩

theorem hasFiniteLength_of_finiteDimensional {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : HasFiniteLength ε ρ := by
  refine ⟨Module.finrank ℂ H, fun r Y _ hY => ?_⟩
  have : ∀ i : Fin (r + 1), i.val ≤ Module.finrank ℂ (Y i) := fun i => by
    induction i using Fin.induction with
    | zero => simp
    | succ i ih => exact Nat.lt_of_le_of_lt ih (Submodule.finrank_lt_finrank_of_lt (hY Fin.castSucc_lt_succ))
  exact (this (Fin.last r)).trans (Submodule.finrank_le _)

theorem mult_det : mult ε (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) = 1 := by
  have hk := (GlobalTheory.Published.infinitesimalEquivalence_hyp_det ε).2.2.1
  refine le_antisymm (iSup₂_le fun r ⟨Z, Y, h, h'⟩ => ?_) (le_iSup₂_of_le (f := fun (r : ℕ) _ => (r : ℕ∞)) 1
    ⟨fun _ => ⊥, fun _ => ⊤, fun _ => ⟨(isGKSub_det ε _).1, (isGKSub_det ε _).1, bot_le, LinearMap.id, by simp [hk],
      by simp, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩, fun i l e => absurd e (by omega)⟩ le_rfl)
  have ne : ∀ i, ¬ Y i ≤ Z i := fun i e => by
    obtain ⟨-, -, -, T, h1, h2, -⟩ := h i
    obtain ⟨w, hw, hw1⟩ : (1 : ℂ) ∈ (Y i).map T := by rw [h1, hk]; trivial
    exact one_ne_zero (hw1 ▸ (h2 w hw).2 (e hw))
  by_contra hr
  have hr : 1 < r := by simpa using hr
  have := h' ⟨0, by omega⟩ ⟨1, hr⟩ (by simp)
  rcases eq_bot_or_eq_top (Y ⟨0, by omega⟩) with e | e
  · exact ne _ (e ▸ bot_le)
  · exact ne _ (le_top.trans (e ▸ this))

end Characters

section RankOne

open GlobalTheory.FlagMeas.Model

theorem levi_borel_le_compact : leviOne e2 W2 ≤ KG e2 := by
  intro m hm
  have hv : (![1, 1] : Fin 2 → ℂ) ∈ W2 1 := Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hm.1 1 _ hv).1
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 (hm.1 1 _ hv).2
  have h1 := detOn_step (g := uMat m) (c := c) (isIsotropicFlag_unitary_one_one.2.1 (Fin.zero_le 1)) (isIsotropicFlag_unitary_one_one.2.2.1 0)
    (fun y hy => (hm.1 0 y hy).1) fun y hy => by
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [mulVec_smul, ← hc, smul_comm, sub_self]; exact zero_mem _
  rw [hm.2, hm.2] at h1
  have h2 : c * starRingEnd ℂ c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, show ‖c‖ = 1 by simpa using h1.symm]; simp
  have hJ : (uMat m)ᴴ * Jm e2 * uMat m = Jm e2 := m.2
  rw [← SetLike.mem_coe, KG_eq]
  change (uMat m)ᴴ * uMat m = 1
  generalize uMat m = g at *
  have c0 := congrFun hc 0
  have c1 := congrFun hc 1
  have d0 := congrArg (starRingEnd ℂ) (congrFun hd 0)
  have d1 := congrArg (starRingEnd ℂ) (congrFun hd 1)
  have j0 := congrFun (congrFun hJ 0) 0
  have j1 := congrFun (congrFun hJ 0) 1
  simp [mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, Jm, e2, diagonal] at c0 c1 d0 d1 j0 j1
  have e1 : g 1 0 = g 0 1 := by linear_combination (c0 - c1 - d0 + d1) / 2
  have e2 : g 1 1 = g 0 0 := by linear_combination c0 - c1 - e1
  rw [e1] at j0 j1
  rw [e2] at j1
  rw [c0, map_add] at h2
  have e3 : starRingEnd ℂ (g 0 1) * c = 0 := by rw [c0]; linear_combination (h2 - j0 - j1) / 2
  have e4 : g 0 1 = 0 := by
    rcases mul_eq_zero.1 e3 with h | h
    · simpa using h
    · rw [← c0, h] at h2; simp at h2
  ext i l
  fin_cases i <;> fin_cases l <;> simp_all [Matrix.mul_apply, Fin.sum_univ_two]

def sphericalDatum (s : ℂ) : Datum e2 where
  a := 1
  j := ![1]
  W := W2
  flag := isIsotropicFlag_unitary_one_one
  pos := by simp
  V := ℂ
  σ := fun _ => 1
  temp := isIrrTempered_one (isClosed_leviOne isIsotropicFlag_unitary_one_one (by simp)) levi_borel_le_compact
  s := ![s]

theorem exists_standard_indModule {s : ℂ} (hs : 0 < s.re) : ∃ I : IndModule e2, I.toDatum = sphericalDatum s ∧
    I.IsStandard W2 ∧ rho 2 ![1] 0 = 1 ∧ ∃ w : I.H, ‖w‖ = 1 ∧ ∀ k ∈ KG e2, I.ρ (uMat k) w = w := by
  haveI : IsProbabilityMeasure (muK e2) := ⟨Measure.haarMeasure_self⟩
  obtain ⟨H, _, _, _, ρ, ι, h⟩ := exists_isIndModel (σ := fun _ => (1 : ℂ →L[ℂ] ℂ)) isIsotropicFlag_unitary_one_one (by simp)
    (fun _ _ _ => rfl) ![s]
  obtain ⟨f, hf, h1, h2⟩ := exists_spherical isIsotropicFlag_unitary_one_one (by simp) ![s]
  refine ⟨{ sphericalDatum s with H := H, ρ := ρ, ι := ι, model := h }, rfl,
    ⟨fun i => ⟨i, rfl⟩, Subsingleton.strictAnti (α := Fin 1) _, fun i => ?_⟩, by simp [rho]; norm_num, ι ⟨f, hf⟩, ?_,
    fun k hk => h.transl k trivial _ _ fun g => (h2 g k hk).symm⟩
  · obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    exact hs
  · have := h.norm_sq ⟨f, hf⟩
    have e : ∀ k : KG e2, f k = 1 := fun k => by rw [← one_mul k.1, h2 _ _ k.2, h1]
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by simpa [e] using this)

end RankOne

end GlobalTheory.RealInd

end
