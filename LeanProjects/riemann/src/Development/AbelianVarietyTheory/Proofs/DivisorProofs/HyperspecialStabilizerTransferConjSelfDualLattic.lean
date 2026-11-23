import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TransferHyp

theorem stab_iff_entries {R : Type} [CommRing R] {n : ℕ} (O : Subring R) {X Y : Matrix (Fin n) (Fin n) R}
    (hXY : X * Y = 1) (hYX : Y * X = 1) :
    (∀ z : Fin n → R, (∀ i, z i ∈ O) ↔ ∀ i, X.mulVec z i ∈ O) ↔ (∀ i j, X i j ∈ O) ∧ ∀ i j, Y i j ∈ O := by
  have hs : ∀ j i : Fin n, (Pi.single j 1 : Fin n → R) i ∈ O := fun j i => by
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hm : ∀ {A : Matrix (Fin n) (Fin n) R}, (∀ i j, A i j ∈ O) → ∀ z : Fin n → R, (∀ i, z i ∈ O) →
      ∀ i, A.mulVec z i ∈ O := fun {A} hA z hz i => by
    change ∑ j, A i j * z j ∈ O
    exact sum_mem fun j _ => mul_mem (hA i j) (hz j)
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using (h _).1 (hs j) i
    · have := (h (Y.mulVec (Pi.single j 1))).2 (by
        rw [Matrix.mulVec_mulVec, hXY, Matrix.one_mulVec]
        exact hs j) i
      simpa using this
  · rintro ⟨h1, h2⟩ z
    refine ⟨hm h1 z, fun hz => ?_⟩
    have := hm h2 _ hz
    rwa [Matrix.mulVec_mulVec, hYX, Matrix.one_mulVec] at this

theorem stab_conj {R : Type} [CommRing R] {n : ℕ} (I Λ : (Fin n → R) → Prop) {A B H G X : Matrix (Fin n) (Fin n) R}
    (hAB : A * B = 1) (hBA : B * A = 1) (hHG : H * G = 1)
    (hΛ : ∀ y, Λ y ↔ I (B.mulVec (H.mulVec y))) :
    (∀ y, Λ y ↔ Λ ((G * (A * X * B) * H).mulVec y)) ↔ ∀ z, I z ↔ I (X.mulVec z) := by
  have key : ∀ y, B.mulVec (H.mulVec ((G * (A * X * B) * H).mulVec y)) = X.mulVec (B.mulVec (H.mulVec y)) := fun y => by
    simp only [Matrix.mulVec_mulVec]
    congr 1
    calc B * (H * (G * (A * X * B) * H)) = B * (H * G) * A * X * (B * H) := by simp only [Matrix.mul_assoc]
      _ = X * (B * H) := by rw [hHG, Matrix.mul_one, hBA, Matrix.one_mul]
  simp only [hΛ, key]
  refine ⟨fun h z => ?_, fun h y => h _⟩
  have e : B.mulVec (H.mulVec (G.mulVec (A.mulVec z))) = z := by
    rw [Matrix.mulVec_mulVec _ H, hHG, Matrix.one_mulVec, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  have := h (G.mulVec (A.mulVec z))
  rwa [e] at this

theorem finMat_mul {D : D7} (V : HSp D) (g h : GA D V) :
    finMat D.sp.cm.sig V.gram (g * h) = finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram h :=
  congrArg Units.val (map_mul (finHom V) g h)

theorem finMat_one {D : D7} (V : HSp D) : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 :=
  congrArg Units.val (map_one (finHom V))

def finComp (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Ad E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E :=
  (GlobalTheory.LFun.finAdEquiv F E).symm.toRingHom.comp (pFin E)

def intRing (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
  ⨅ u : HeightOneSpectrum (𝓞 E), (Ov E u).comap (GlobalTheory.LFun.compAt F u)

theorem mem_intRing {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) : z ∈ intRing F E ↔ ∀ u, GlobalTheory.LFun.compAt F u z ∈ Ov E u := by
  simp only [intRing, Subring.mem_iInf, Subring.mem_comap]

theorem stab_finComp_iff (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsCMField E] {n : ℕ} (x : UA E n) :
    (∀ z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E, (∀ i, z i ∈ intRing F E) ↔
      ∀ i, (x.1.1.map (finComp F E)).mulVec z i ∈ intRing F E) ↔
    (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers E) ∧
      ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers E := by
  have hκ : ∀ (y : UA E n) a b, (y.1.1.map (finComp F E)) a b ∈ intRing F E ↔
      ∀ u, (cLoc u y).1 a b ∈ u.adicCompletionIntegers E := fun y a b => by
    refine (mem_intRing _).trans (forall_congr' fun u => ?_)
    have e : GlobalTheory.LFun.compAt F u ((y.1.1.map (finComp F E)) a b) = (cLoc u y).1 a b :=
      congrArg (fun t => pLoc E u t) ((GlobalTheory.LFun.finAdEquiv F E).apply_symm_apply (pFin E (y.1.1 a b)))
    rw [e]
    exact Iff.rfl
  have hXY : ∀ y : UA E n, y.1.1.map (finComp F E) * (y⁻¹).1.1.map (finComp F E) = 1 := fun y => by
    rw [← Matrix.map_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hYX := hXY x⁻¹
  rw [inv_inv] at hYX
  refine (stab_iff_entries _ (hXY x) hYX).trans ?_
  simp only [hκ]

theorem mem_KGL_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {x : UA E n} (hx : x ∈ locU n P) : cLoc P x ∈ GlobalTheory.LFun.KGL P n ↔
    (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers E) ∧
      ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers E := by
  constructor
  · intro h2
    exact ⟨fun a b u => GlobalTheory.UnramDict.cLoc_entry_mem hx h2 u a b, fun a b u =>
      GlobalTheory.UnramDict.cLoc_entry_mem (inv_mem hx) (by rw [map_inv]; exact inv_mem h2) u a b⟩
  · rintro ⟨h4, h5⟩
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun a b => h4 a b P, fun a b => ?_⟩
    rw [← map_inv]
    exact h5 a b P

theorem map_mul_map_inv {K R : Type} [Field K] [CommRing R] {n : ℕ} (ι : K →+* R) {M N : Matrix (Fin n) (Fin n) K}
    (h : N * M = 1) : M.map ι * M⁻¹.map ι = 1 ∧ M⁻¹.map ι * M.map ι = 1 := by
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse h
  constructor
  · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ ι.map_zero ι.map_one]
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ ι.map_zero ι.map_one]

theorem cj_mem_hyp_iff : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU D.host.E V.rank ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ SuppF V f (cj j h₀ x)) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, cj j h₀ x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P := by
  intro D _ V j h₀ M hM _ _ hj hlat hloc P x
  have hO : ∀ z, z ∈ intAE D ↔ z ∈ intRing D.host.F D.host.E := fun z =>
    (GlobalTheory.LFun.mem_intAE_iff_compAt z).trans (mem_intRing z).symm
  obtain ⟨hAB, hBA⟩ := map_mul_map_inv (Algebra.TensorProduct.includeRight :
      D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E).toRingHom hM
  have hHG : finMat D.sp.cm.sig V.gram h₀ * finMat D.sp.cm.sig V.gram h₀⁻¹ = 1 := by
    rw [← finMat_mul, mul_inv_cancel, finMat_one]
  have hst : (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (finMat D.sp.cm.sig V.gram (cj j h₀ x)).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ↔
      (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers D.host.E) ∧
        ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers D.host.E := by
    rw [cj_apply, finMat_mul, finMat_mul, hj]
    exact (stab_conj (fun z => ∀ i, z i ∈ intRing D.host.F D.host.E)
      (fun y => y ∈ latHat D.host.F D.host.E (L0c D V)) hAB hBA hHG
      fun y => (hlat y).trans (forall_congr' fun i => hO _)).trans (stab_finComp_iff D.host.F x)
  constructor
  · rintro ⟨⟨h1, h2, -⟩, e, f, hef, h3⟩
    have hx := (hloc P e f hef x).2 ⟨h1, h3⟩
    exact ⟨hx, (mem_KGL_iff hx).2 (hst.1 h2)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨e, f, hef⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (GlobalTheory.LFun.comp_finAdEquiv D) P
    obtain ⟨h3, h4⟩ := (hloc P e f hef x).1 h1
    exact ⟨⟨h3, hst.2 ((mem_KGL_iff h1).1 h2), fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, f, hef, h4⟩

end GlobalTheory.TransferHyp

end
