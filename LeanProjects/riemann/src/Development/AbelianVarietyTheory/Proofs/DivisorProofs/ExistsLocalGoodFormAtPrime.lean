import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionUniformizerPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLocalBasisRealSubfieldStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.SUCong

noncomputable section
namespace GlobalTheory.SUFrame

section Local
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_intA_iff (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    y ∈ intA (E := E) v ↔ y ∈ GlobalTheory.AdelicU.intLoc F E v := by
  constructor
  · intro hy
    exact (Subring.closure_le (t := GlobalTheory.AdelicU.intLoc F E v)).2 (fun z hz => AddSubgroup.subset_closure hz) hy
  · intro hy
    exact GlobalTheory.AdelicU.intLoc_induction (p := fun y => y ∈ intA (E := E) v)
      (fun a ha x => Subring.subset_closure ⟨a, ha, x, rfl⟩) (zero_mem _) (fun _ _ h h' => add_mem h h')
      (fun _ h => neg_mem h) hy

theorem exists_frame (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ P : GL (Fin n) E,
      (∀ j, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ (algebraMap F E s • fun i => (P : Matrix (Fin n) (Fin n) E) i j) ∈ L) ∧
      (∀ x ∈ L, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧
        algebraMap F E s • ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ GlobalTheory.AdelicU.stdLattice E n) ∧
      ∀ y : Fin n → Fv F v ⊗[F] E, (∀ i, y i ∈ intA (E := E) v) ↔
        ((Formalism.UG.bc (inclR (Fv F v)) P : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ y ∈
          GlobalTheory.TamCnt.compLat v (L : Set (Fin n → E)) := by
  haveI : Submodule.IsLattice E L := ⟨hfg, hsp⟩
  obtain ⟨P, h1, h2⟩ := GlobalTheory.AdelicU.Frames.exists_rational_frame (F := F) L v
  refine ⟨P, fun j => by simpa using h1 j, fun x hx => by simpa using h2 x hx, fun y => ?_⟩
  have := GlobalTheory.AdelicU.Frames.frame_of_rational (L := L) (v := v) P h1 h2 y
  simp only [mem_intA_iff]
  exact this

theorem incl_mem_intA (v : HeightOneSpectrum (𝓞 F)) {e : E} {s : 𝓞 F} (hs : s ∉ v.asIdeal)
    (he : IsIntegral ℤ (algebraMap F E s * e)) : inclR (Fv F v) e ∈ intA (E := E) v := by
  have hs0 : (s : F) ≠ 0 := fun h => hs (by
    rw [show s = 0 from RingOfIntegers.coe_injective (by simpa using h)]; exact zero_mem _)
  have ha : algebraMap F (Fv F v) (s : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : v.valuation F (s : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 hs
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (s : F)⁻¹
    exact (h2.trans ((map_inv₀ _ _).trans ((congrArg _ h1).trans inv_one))).le
  have hmem : algebraMap F (Fv F v) (s : F)⁻¹ ⊗ₜ[F] (((⟨_, he⟩ : 𝓞 E)) : E) ∈ intA (E := E) v :=
    Subring.subset_closure ⟨_, ha, ⟨_, he⟩, rfl⟩
  convert hmem using 1
  change (1 : Fv F v) ⊗ₜ[F] e = algebraMap F (Fv F v) (s : F)⁻¹ ⊗ₜ[F] (algebraMap F E (s : F) * e)
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hs0, map_one]

end Local

section Conj
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mem_map_conj_iff (K : Subgroup (GL n A)) (P g : GL n A) :
    g ∈ K.map (MulAut.conj P).toMonoidHom ↔ P⁻¹ * g * P ∈ K := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    convert hx using 1
    simp [MulAut.conj_apply, mul_assoc]
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem uj_iff (σ : A →+* A) (J : Matrix n n A) (P g : GL n A) :
    g ∈ Formalism.UG.UJ σ J ↔
      P⁻¹ * g * P ∈ Formalism.UG.UJ σ (Formalism.UG.cT σ (P : Matrix n n A) * J * (P : Matrix n n A)) := by
  set Pm := (P : Matrix n n A)
  set Pi := ((P⁻¹ : GL n A) : Matrix n n A)
  set gm := (g : Matrix n n A)
  have hPiP : Pi * Pm = 1 := by simp [Pi, Pm]
  have hPPi : Pm * Pi = 1 := by simp [Pi, Pm]
  have hcc : Formalism.UG.cT σ Pi * Formalism.UG.cT σ Pm = 1 := by rw [← Formalism.UG.cT_mul, hPPi, Formalism.UG.cT_one]
  have hcc' : Formalism.UG.cT σ Pm * Formalism.UG.cT σ Pi = 1 := by rw [← Formalism.UG.cT_mul, hPiP, Formalism.UG.cT_one]
  have a1 : ∀ X : Matrix n n A, Formalism.UG.cT σ Pi * (Formalism.UG.cT σ Pm * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hcc, Matrix.one_mul]
  have a2 : ∀ X : Matrix n n A, Formalism.UG.cT σ Pm * (Formalism.UG.cT σ Pi * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hcc', Matrix.one_mul]
  have a3 : ∀ X : Matrix n n A, Pm * (Pi * X) = X := fun X => by rw [← Matrix.mul_assoc, hPPi, Matrix.one_mul]
  have a4 : ∀ X : Matrix n n A, Pi * (Pm * X) = X := fun X => by rw [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have hm : ((P⁻¹ * g * P : GL n A) : Matrix n n A) = Pi * gm * Pm := by simp [Pi, gm, Pm]
  have key : Formalism.UG.cT σ ((P⁻¹ * g * P : GL n A) : Matrix n n A) * (Formalism.UG.cT σ Pm * J * Pm) *
      ((P⁻¹ * g * P : GL n A) : Matrix n n A) = Formalism.UG.cT σ Pm * (Formalism.UG.cT σ gm * J * gm) * Pm := by
    rw [hm]
    simp only [Formalism.UG.cT_mul, Matrix.mul_assoc, a1, a2, a3, a4]
  change Formalism.UG.cT σ gm * J * gm = J ↔ Formalism.UG.cT σ ((P⁻¹ * g * P : GL n A) : Matrix n n A) *
      (Formalism.UG.cT σ Pm * J * Pm) * ((P⁻¹ * g * P : GL n A) : Matrix n n A) = Formalism.UG.cT σ Pm * J * Pm
  rw [key]
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg (fun M => Formalism.UG.cT σ Pi * M * Pi) h
    simpa only [Matrix.mul_assoc, a1, a2, a3, a4, hPPi, Matrix.mul_one] using this

theorem mulVec_int (S : Subring A) (M : Matrix n n A) (hM : ∀ i j, M i j ∈ S) (w : n → A) (hw : ∀ i, w i ∈ S) :
    ∀ i, (M *ᵥ w) i ∈ S := fun i => Subring.sum_mem _ fun j _ => mul_mem (hM i j) (hw j)

theorem single_int (S : Subring A) (j : n) : ∀ i, (Pi.single j (1 : A) : n → A) i ∈ S := fun i => by
  by_cases h : i = j
  · subst h; simp [one_mem]
  · simp [h, zero_mem]

theorem stab_iff (S : Subring A) (M : GL n A) :
    (∀ w : n → A, (∀ i, w i ∈ S) ↔ ∀ i, ((M : Matrix n n A) *ᵥ w) i ∈ S) ↔
      (∀ i j, (M : Matrix n n A) i j ∈ S) ∧ ∀ i j, ((M⁻¹ : GL n A) : Matrix n n A) i j ∈ S := by
  constructor
  · intro h
    have c1 : ∀ i j, (M : Matrix n n A) i j ∈ S := fun i j => by
      have := (h _).1 (single_int S j) i
      simpa [Matrix.mulVec_single_one] using this
    refine ⟨c1, fun i j => ?_⟩
    have e : (M : Matrix n n A) *ᵥ (((M⁻¹ : GL n A) : Matrix n n A) *ᵥ Pi.single j 1) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have := (h _).2 (by rw [e]; exact single_int S j) i
    simpa [Matrix.mulVec_single_one] using this
  · rintro ⟨h1, h2⟩ w
    refine ⟨mulVec_int S _ h1 w, fun hw => ?_⟩
    have := mulVec_int S _ h2 _ hw
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this

theorem conj_iff (S : Subring A) (σ : A →+* A) (J : Matrix n n A) (ϖ : A) (k : ℕ) (P : GL n A)
    (L K : Set (n → A)) (hL : ∀ y, (∀ i, y i ∈ S) ↔ (P : Matrix n n A) *ᵥ y ∈ L)
    (hK : ∀ y, y ∈ K ↔ ∃ z ∈ L, y = ϖ ^ k • z) (g : GL n A) :
    (g ∈ Formalism.UG.UJ σ J ∧ (g : Matrix n n A).det = 1 ∧ (∀ y, y ∈ L ↔ (g : Matrix n n A) *ᵥ y ∈ L) ∧
      ∀ y ∈ L, ((g : Matrix n n A) - 1) *ᵥ y ∈ K) ↔
    g ∈ (congSU S σ (Formalism.UG.cT σ (P : Matrix n n A) * J * (P : Matrix n n A)) ϖ k).map
      (MulAut.conj P).toMonoidHom := by
  rw [mem_map_conj_iff]
  set Pm := (P : Matrix n n A)
  set Q := ((P⁻¹ : GL n A) : Matrix n n A)
  set gm := (g : Matrix n n A)
  have hPiP : Q * Pm = 1 := by simp [Q, Pm]
  have hPPi : Pm * Q = 1 := by simp [Q, Pm]
  have hm : ((P⁻¹ * g * P : GL n A) : Matrix n n A) = Q * gm * Pm := by simp [Q, gm, Pm]
  have hLi : ∀ y, y ∈ L ↔ ∀ i, (Q *ᵥ y) i ∈ S := fun y => by
    rw [hL, Matrix.mulVec_mulVec, hPPi, Matrix.one_mulVec]

  have hdet : ((P⁻¹ * g * P : GL n A) : Matrix n n A).det = gm.det := by
    rw [hm, Matrix.det_mul, Matrix.det_mul, mul_comm (Q.det), mul_assoc, ← Matrix.det_mul, hPiP, Matrix.det_one,
      mul_one]

  have hstab : (∀ y, y ∈ L ↔ gm *ᵥ y ∈ L) ↔
      ∀ w : n → A, (∀ i, w i ∈ S) ↔ ∀ i, (((P⁻¹ * g * P : GL n A) : Matrix n n A) *ᵥ w) i ∈ S := by
    rw [hm]
    constructor
    · intro h w
      have := h (Pm *ᵥ w)
      rwa [hLi, hLi, Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    · intro h y
      have := h (Q *ᵥ y)
      rwa [← hLi, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPPi, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, ← hLi] at this

  have hcong : (∀ y ∈ L, (gm - 1) *ᵥ y ∈ K) ↔
      ∀ i j, InPow S ϖ k ((((P⁻¹ * g * P : GL n A) : Matrix n n A) - 1) i j) := by
    have hm1 : ((P⁻¹ * g * P : GL n A) : Matrix n n A) - 1 = Q * (gm - 1) * Pm := by
      rw [hm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPiP]
    rw [hm1]
    constructor
    · intro h i j
      have hy : Pm *ᵥ Pi.single j 1 ∈ L := (hL _).1 (single_int S j)
      obtain ⟨z, hz, hze⟩ := (hK _).1 (h _ hy)
      refine ⟨(Q *ᵥ z) i, (hLi z).1 hz i, ?_⟩
      have := congrArg (fun u => (Q *ᵥ u) i) hze
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at this
      rw [← this, Matrix.mulVec_single_one]
      simp [Matrix.mul_assoc]
    · intro h y hy
      choose s hs he using h
      set w := Q *ᵥ y
      have hw := (hLi y).1 hy
      refine (hK _).2 ⟨Pm *ᵥ fun i => ∑ j, s i j * w j, ?_, ?_⟩
      · rw [hLi, Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec]
        exact fun i => Subring.sum_mem _ fun j _ => mul_mem (hs i j) (hw j)
      · have e1 : (gm - 1) *ᵥ y = Pm *ᵥ ((Q * (gm - 1) * Pm) *ᵥ w) := by
          simp only [w, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPPi, Matrix.one_mul]
          rw [Matrix.mul_assoc, hPPi, Matrix.mul_one]
        have e2 : (Q * (gm - 1) * Pm) *ᵥ w = ϖ ^ k • fun i => ∑ j, s i j * w j := by
          funext i
          simp only [Matrix.mulVec, dotProduct, he, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
        rw [e1, e2, Matrix.mulVec_smul]
  change _ ↔ (P⁻¹ * g * P ∈ Formalism.UG.UJ σ (Formalism.UG.cT σ Pm * J * Pm) ∧ _ ∧ _ ∧ _ ∧ _)
  rw [← uj_iff, hdet, ← and_assoc (a := ∀ i j, _), ← stab_iff, ← hstab, ← hcong]

end Conj

section Main

theorem compK_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (π : 𝓞 F) (hπ : π ∈ v.asIdeal)
    (hπ2 : π ∉ v.asIdeal ^ 2) (k : ℕ) (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ GlobalTheory.TamCnt.compK Λ v k ↔ ∃ z ∈ GlobalTheory.TamCnt.compLat v (Λ : Set (Fin n → E)),
      y = ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k • z :=
  GlobalTheory.T.lattice_completion_uniformizer_power Λ v π hπ hπ2 k y

theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem cT_map_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {m p : Type} (M : Matrix m p E) :
    Formalism.UG.cT (sigR R σ) (M.map (inclR R)) = (Formalism.UG.cT (σ : E →+* E) M).map (inclR R) := by
  ext i j
  simp [Formalism.UG.cT, sigR_inclR]

theorem frame_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (π : 𝓞 (maximalRealSubfield E)), π ∈ v.asIdeal → π ∉ v.asIdeal ^ 2 → ∃ P : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E), GoodForm (intA (E := E) v) (sigR (Fv (maximalRealSubfield E) v) (IsCMField.complexConj E).toAlgHom) (Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) (IsCMField.complexConj E).toAlgHom) (P : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) * JR (Fv (maximalRealSubfield E) v) Gᵀ * (P : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E))) ∧ ∀ k : ℕ, GlobalTheory.TamCnt.locCong (IsCMField.complexConj E).toAlgHom Gᵀ Λ v k = (congSU (intA (E := E) v) (sigR (Fv (maximalRealSubfield E) v) (IsCMField.complexConj E).toAlgHom) (Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) (IsCMField.complexConj E).toAlgHom) (P : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) * JR (Fv (maximalRealSubfield E) v) Gᵀ * (P : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E))) ((1 : Fv (maximalRealSubfield E) v) ⊗ₜ[maximalRealSubfield E] algebraMap (maximalRealSubfield E) E (π : maximalRealSubfield E)) k).map (MulAut.conj P).toMonoidHom := by
  intro E _ _ _ r G Λ _ _ hSD v π hπ hπ2
  obtain ⟨P, h1, h2, hfr⟩ := exists_frame (F := maximalRealSubfield E) Λ hSD.2.2.1 hSD.2.2.2.1 v
  refine ⟨Formalism.UG.bc (inclR (Fv (maximalRealSubfield E) v)) P, ?_, fun k => ?_⟩
  · set σ := (IsCMField.complexConj E).toAlgHom
    set H₀ := Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin r) (Fin r) E) * Gᵀ * (P : Matrix (Fin r) (Fin r) E) with hH₀
    have hbc : ((Formalism.UG.bc (inclR (Fv (maximalRealSubfield E) v)) P : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) =
        (P : Matrix (Fin r) (Fin r) E).map (inclR (Fv (maximalRealSubfield E) v)) := rfl
    have hH : Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) σ)
        ((Formalism.UG.bc (inclR (Fv (maximalRealSubfield E) v)) P : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) *
        JR (Fv (maximalRealSubfield E) v) Gᵀ *
        ((Formalism.UG.bc (inclR (Fv (maximalRealSubfield E) v)) P : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) =
        H₀.map (inclR (Fv (maximalRealSubfield E) v)) := by
      rw [hbc, cT_map_inclR, hH₀, Matrix.map_mul, Matrix.map_mul]
      rfl
    have hσσ : ∀ x : E, σ (σ x) = x := fun x => by simp [σ]
    have hG : Formalism.UG.cT (σ : E →+* E) Gᵀ = Gᵀ := by
      ext a b
      exact hSD.1 a b
    have hPP : Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin r) (Fin r) E)) = P := by
      ext a b
      exact hσσ _
    have hherm : Formalism.UG.cT (σ : E →+* E) H₀ = H₀ := by
      rw [hH₀, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hPP, hG, Matrix.mul_assoc]
    have hdet : IsUnit H₀.det := by
      rw [isUnit_iff_ne_zero, hH₀, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      refine mul_ne_zero (mul_ne_zero ?_ hSD.2.1) ?_
      · have e : ((P : Matrix (Fin r) (Fin r) E).map (σ : E →+* E)).det = (σ : E →+* E) (P : Matrix (Fin r) (Fin r) E).det :=
          (RingHom.map_det _ _).symm
        rw [Formalism.UG.cT, Matrix.det_transpose, e]
        exact (map_ne_zero _).2 (P.isUnit.map Matrix.detMonoidHom).ne_zero
      · exact (P.isUnit.map Matrix.detMonoidHom).ne_zero
    rw [hH]
    refine ⟨fun i j => ?_, ?_, ⟨H₀⁻¹.map (inclR (Fv (maximalRealSubfield E) v)), fun i j => ?_, ?_⟩⟩
    · obtain ⟨s, hs, hi⟩ := (GlobalTheory.T.lattice_local_basis_real_subfield E r G Λ hSD v P h1 h2 i j).1
      exact incl_mem_intA v hs hi
    · rw [cT_map_inclR, hherm]
    · obtain ⟨s, hs, hi⟩ := (GlobalTheory.T.lattice_local_basis_real_subfield E r G Λ hSD v P h1 h2 i j).2
      exact incl_mem_intA v hs hi
    · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet]
      exact Matrix.map_one _ (map_zero _) (map_one _)
  · ext g
    exact conj_iff _ _ _ _ k _ _ _ hfr (compK_iff Λ v π hπ hπ2 k) g

end Main
end GlobalTheory.SUFrame
