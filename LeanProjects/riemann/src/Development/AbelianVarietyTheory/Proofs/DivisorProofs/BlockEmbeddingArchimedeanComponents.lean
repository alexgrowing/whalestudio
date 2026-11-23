import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.BlockArch

open GlobalTheory.CuspRep Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def evTens (w : InfinitePlace F) : Ainf F ⊗[F] E →+* w.Completion ⊗[F] E :=
  (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom

theorem compInf_eq_evTens (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    GlobalTheory.AdelicU.compInf F E w z = evTens w (GlobalTheory.LFun.infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_sigR {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (a : R →ₐ[F] R')
    (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map a (AlgHom.id F E) (sigR R σ z) =
      sigR R' σ (Algebra.TensorProduct.map a (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_cT_sigR_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (a : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {m p : Type} (M : Matrix m p (R ⊗[F] E)) :
    (cT (sigR R σ) M).map (Algebra.TensorProduct.map a (AlgHom.id F E)) =
      cT (sigR R' σ) (M.map (Algebra.TensorProduct.map a (AlgHom.id F E))) := by
  ext i k
  exact map_sigR a σ (M k i)

theorem map_inclR_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (a : R →ₐ[F] R')
    {m p : Type} (M : Matrix m p E) :
    (M.map (inclR (F := F) R)).map (Algebra.TensorProduct.map a (AlgHom.id F E)) = M.map (inclR (F := F) R') := by
  ext i k
  simp [inclR]

variable [IsTotallyComplex E]

def rhoW (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E) (w : InfinitePlace F) : Cinf E →+* w.Completion ⊗[F] E :=
  (evTens w).comp (j.symm.toRingHom.comp (infEq E).toRingHom)

end GlobalTheory.BlockArch

noncomputable section

namespace GlobalTheory.BlockArch

open GlobalTheory.CuspRep Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex E]

section Split

variable {Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E} {j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E}
  (hs : ∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z)))
include hs

theorem infTens_symm_sInf (x : Cinf E) : GlobalTheory.LFun.infTens F E (Φ.symm (sInf E x)) = j.symm (infEq E x) := by
  have h := hs (Φ.symm (sInf E x))
  rw [Φ.apply_symm_apply] at h
  have h1 := congrArg Prod.fst h
  exact j.injective ((j.apply_symm_apply _).trans h1).symm

theorem finTens_symm_sInf (x : Cinf E) : GlobalTheory.LFun.finTens F E (Φ.symm (sInf E x)) = 0 := by
  have h := hs (Φ.symm (sInf E x))
  rw [Φ.apply_symm_apply] at h
  have h1 := congrArg Prod.snd h
  exact (GlobalTheory.LFun.finAdEquiv F E).injective (((map_zero _).trans h1).symm)

theorem compInf_symm_sInf (w : InfinitePlace F) (x : Cinf E) :
    GlobalTheory.AdelicU.compInf F E w (Φ.symm (sInf E x)) = rhoW j w x := by
  rw [compInf_eq_evTens, infTens_symm_sInf hs]; rfl

end Split

theorem map_star_of_continuous {ι : Type} [Fintype ι] (ψ : (ι → ℂ) →+* ℂ) (hψ : Continuous ψ)
    (z : ι → ℂ) : ψ (star z) = star (ψ z) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, ψ (Pi.single i 1) ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h1 : ψ 1 = ∑ i, ψ (Pi.single i 1) := by
      rw [← map_sum]
      congr 1
      exact (Finset.univ_sum_single (1 : ι → ℂ)).symm
    rw [map_one, Finset.sum_eq_zero fun i _ => hc i] at h1
    exact one_ne_zero h1
  have he : ψ (Pi.single i 1) = 1 := by
    have h2 : ψ (Pi.single i 1) * ψ (Pi.single i 1) = ψ (Pi.single i 1) * 1 := by
      rw [← map_mul, mul_one, ← Pi.single_mul, mul_one]
    exact mul_left_cancel₀ hi h2
  let φ : ℂ →+* ℂ := ψ.comp (Pi.constRingHom ι ℂ)
  have hφ : Continuous φ := hψ.comp (continuous_pi fun _ => continuous_id)
  have key : ∀ y : ι → ℂ, ψ y = φ (y i) := fun y => by
    have h3 : y * Pi.single i 1 = Pi.constRingHom ι ℂ (y i) * Pi.single i 1 := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    calc ψ y = ψ y * ψ (Pi.single i 1) := by rw [he, mul_one]
      _ = ψ (y * Pi.single i 1) := (map_mul _ _ _).symm
      _ = φ (y i) * ψ (Pi.single i 1) := by rw [h3, map_mul]; rfl
      _ = φ (y i) := by rw [he, mul_one]
  rw [key, key, Pi.star_apply]
  rcases Complex.ringHom_eq_id_or_conj_of_continuous hφ with h | h
  · rw [h]; rfl
  · rw [h]; simp

end GlobalTheory.BlockArch

noncomputable section

namespace GlobalTheory.BlockArch

open GlobalTheory.CuspRep Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evTens_rTensor_self (w : InfinitePlace F) (s : w.Completion ⊗[F] E) :
    evTens w (LinearMap.rTensor E (GlobalTheory.AutFunCompare.sgW w) s) = s := by
  classical
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change (GlobalTheory.AutFunCompare.evW w (GlobalTheory.AutFunCompare.sgW w a)) ⊗ₜ[F] x = a ⊗ₜ[F] x
    congr 1
    exact Pi.single_eq_same w a
  | add x y hx hy => simp only [map_add, hx, hy]

theorem evTens_rTensor_ne {w u : InfinitePlace F} (h : u ≠ w) (s : w.Completion ⊗[F] E) :
    evTens u (LinearMap.rTensor E (GlobalTheory.AutFunCompare.sgW w) s) = 0 := by
  classical
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change (GlobalTheory.AutFunCompare.evW u (GlobalTheory.AutFunCompare.sgW w a)) ⊗ₜ[F] x = 0
    rw [show GlobalTheory.AutFunCompare.evW u (GlobalTheory.AutFunCompare.sgW w a) = 0 from Pi.single_eq_of_ne h a]
    exact TensorProduct.zero_tmul _ _
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem evTens_pi_bijective : Function.Bijective (Pi.ringHom fun w : InfinitePlace F => (evTens w : Ainf F ⊗[F] E →+* _)) := by
  classical
  refine ⟨fun z z' h => GlobalTheory.AutFunCompare.infTens_ext fun w => congrFun h w, fun t => ?_⟩
  refine ⟨∑ w, LinearMap.rTensor E (GlobalTheory.AutFunCompare.sgW w) (t w), funext fun u => ?_⟩
  change evTens u (∑ w, LinearMap.rTensor E (GlobalTheory.AutFunCompare.sgW w) (t w)) = t u
  rw [map_sum, Finset.sum_eq_single u (fun w _ hw => evTens_rTensor_ne (Ne.symm hw) _) (by simp),
    evTens_rTensor_self]

variable [IsTotallyComplex E]

theorem rhoW_pi_bijective (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E) :
    Function.Bijective (Pi.ringHom fun w : InfinitePlace F => rhoW j w) :=
  (evTens_pi_bijective (E := E)).comp (j.symm.bijective.comp (infEq E).bijective)

theorem exists_lift_GL (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E) {d : ℕ}
    (m : ∀ w : InfinitePlace F, GL (Fin d) (w.Completion ⊗[F] E)) :
    ∃ y : GL (Fin d) (Cinf E), ∀ w, Matrix.GeneralLinearGroup.map (rhoW j w) y = m w := by
  let e := RingEquiv.ofBijective _ (rhoW_pi_bijective (F := F) (E := E) j)
  have he : ∀ x w, rhoW j w x = e x w := fun _ _ => rfl
  let Y : Matrix (Fin d) (Fin d) (Cinf E) := Matrix.of fun a b => e.symm fun w => (m w).1 a b
  let Yi : Matrix (Fin d) (Fin d) (Cinf E) := Matrix.of fun a b => e.symm fun w => ((m w)⁻¹).1 a b
  have hY : ∀ w, Y.map (rhoW j w) = (m w).1 := fun w => by
    ext a b; simp only [Matrix.map_apply, he, Y, Matrix.of_apply, e.apply_symm_apply]
  have hYi : ∀ w, Yi.map (rhoW j w) = ((m w)⁻¹).1 := fun w => by
    ext a b; simp only [Matrix.map_apply, he, Yi, Matrix.of_apply, e.apply_symm_apply]
  have inj : ∀ {M N : Matrix (Fin d) (Fin d) (Cinf E)}, (∀ w, M.map (rhoW j w) = N.map (rhoW j w)) → M = N :=
    fun {M N} h => Matrix.ext fun a b => e.injective (funext fun w =>
      congrArg (fun P : Matrix (Fin d) (Fin d) _ => P a b) (h w))
  have h1 : Y * Yi = 1 := inj fun w => by
    rw [Matrix.map_mul, hY, hYi, Matrix.map_one _ (map_zero _) (map_one _)]; exact (m w).mul_inv
  have h2 : Yi * Y = 1 := inj fun w => by
    rw [Matrix.map_mul, hY, hYi, Matrix.map_one _ (map_zero _) (map_one _)]; exact (m w).inv_mul
  exact ⟨⟨Y, Yi, h1, h2⟩, fun w => Units.ext (hY w)⟩

end GlobalTheory.BlockArch

noncomputable section

namespace GlobalTheory.BlockArch

open GlobalTheory.CuspRep Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_blockForm {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n d : Type} [Fintype d] [Fintype n]
    [DecidableEq n] [DecidableEq d] (A : Matrix n d R) (B : Matrix d d R) (C : Matrix d n R) (D : Matrix n d R)
    (B' : Matrix d d R) (C' : Matrix d n R) :
    (1 + A * (B - 1) * C + D * (B' - 1) * C').map f =
      1 + A.map f * (B.map f - 1) * C.map f + D.map f * (B'.map f - 1) * C'.map f := by
  simp only [Matrix.map_add f (map_add f), Matrix.map_sub f (map_sub f), Matrix.map_mul,
    Matrix.map_one f (map_zero f) (map_one f)]

theorem continuous_sInf [IsTotallyComplex E] : Continuous (sInf E) :=
  (continuous_infEq E).prodMk continuous_const

end GlobalTheory.BlockArch

open GlobalTheory.CuspRep GlobalTheory.BlockArch in

theorem GlobalTheory.BlockForms.exists_archComp_of_isBlockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J),
    GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
    ∃ ρ : ∀ w : InfinitePlace F, GlobalTheory.CuspRep.Cinf E →+* w.Completion ⊗[F] E,
      (∀ w z, ρ w (star z) = sigR w.Completion σ (ρ w z)) ∧
      (∀ m : ∀ w : InfinitePlace F, GL (Fin d) (w.Completion ⊗[F] E), ∃ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E),
        ∀ w, Matrix.GeneralLinearGroup.map (ρ w) y = m w) ∧
      ∀ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E), ι (GlobalTheory.CuspRep.infGL E d y) ∈ infPts σ J ∧
        ∀ w, (matHom _ σ J (projArch σ J w (ι (GlobalTheory.CuspRep.infGL E d y)))).1 =
          1 + (GlobalTheory.BlockForms.blkCols h Xf).map (inclR (F := F) w.Completion) * ((Matrix.GeneralLinearGroup.map (ρ w) y).1 - 1) *
            (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J).map (inclR (F := F) w.Completion) +
          (GlobalTheory.BlockForms.blkCols h Yf).map (inclR (F := F) w.Completion) * (Formalism.UG.cT (sigR w.Completion σ) ((Matrix.GeneralLinearGroup.map (ρ w) y)⁻¹).1 - 1) *
            (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J).map (inclR (F := F) w.Completion) := by
  intro F E _ _ _ _ _ _ σ hcm n J r Xf Yf l d h ι hB
  obtain ⟨Φ, j, -, hΦs, -, hs, hform⟩ := hB
  refine ⟨rhoW j, fun w z => ?_, fun m => exists_lift_GL j m, fun y => ⟨?_, fun w => ?_⟩⟩
  · obtain ⟨τ⟩ : Nonempty (GlobalTheory.AdelicU.EmbOver E w) := inferInstance
    have hc : Continuous ((GlobalTheory.AdelicU.infEmb τ).comp (rhoW j w)) := by
      have e : ⇑((GlobalTheory.AdelicU.infEmb τ).comp (rhoW j w)) =
          fun x => GlobalTheory.AdelicU.infEmb τ (compInf F E w (Φ.symm (sInf E x))) :=
        funext fun x => by rw [compInf_symm_sInf hs]; rfl
      rw [e]
      exact (GlobalTheory.Grow.continuous_infEmb_compInf F w τ).comp (hΦs.comp continuous_sInf)
    apply (GlobalTheory.AdelicU.infEmb_bijective hcm τ).1
    rw [← GlobalTheory.AdelicU.infEmb_sigR hcm τ]
    exact map_star_of_continuous _ hc z
  · have hq : ((infGL E d y).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) = 1 := by
      rw [Matrix.map_map]
      exact congrArg Units.val (map_cornerGL_of_zero (sInf E) ((GlobalTheory.LFun.finTens F E).comp Φ.symm.toRingHom)
        (finTens_symm_sInf hs) y)
    have hq' : ((infGL E d y⁻¹).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) = 1 := by
      rw [Matrix.map_map]
      exact congrArg Units.val (map_cornerGL_of_zero (sInf E) ((GlobalTheory.LFun.finTens F E).comp Φ.symm.toRingHom)
        (finTens_symm_sInf hs) y⁻¹)
    have hA : ∀ {m p : Type} (M : Matrix m p E), (adMat F M).map (GlobalTheory.LFun.finTens F E) =
        M.map (inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) := fun M => map_inclR_map (sndA F) M
    have hC : ∀ {m p : Type} (M : Matrix m p (AF F ⊗[F] E)), (Formalism.UG.cT (sigR (AF F) σ) M).map (GlobalTheory.LFun.finTens F E) =
        Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ) (M.map (GlobalTheory.LFun.finTens F E)) := fun M => map_cT_sigR_map (sndA F) σ M
    show ι (infGL E d y) ∈ MonoidHom.ker _
    rw [MonoidHom.mem_ker]
    apply Units.ext
    change ((matHom _ σ J (ι (infGL E d y))).1).map (GlobalTheory.LFun.finTens F E) = 1
    rw [hform, ← map_inv]
    rw [map_blockForm, hC, hq, hq', Formalism.UG.cT_one]
    simp
  · have hp : ∀ y : GL (Fin d) (Cinf E), ((infGL E d y).1.map Φ.symm).map (compInf F E w) =
        (Matrix.GeneralLinearGroup.map (rhoW j w) y).1 := fun y => by
      rw [Matrix.map_map]
      exact congrArg Units.val (map_cornerGL_of_hom (sInf E) ((compInf F E w).comp Φ.symm.toRingHom) (rhoW j w)
        (compInf_symm_sInf hs w) y)
    have hA : ∀ {m p : Type} (M : Matrix m p E), (adMat F M).map (compInf F E w) =
        M.map (inclR (F := F) w.Completion) := fun M => map_inclR_map (evInf F w) M
    have hC : ∀ {m p : Type} (M : Matrix m p (AF F ⊗[F] E)), (Formalism.UG.cT (sigR (AF F) σ) M).map (compInf F E w) =
        Formalism.UG.cT (sigR w.Completion σ) (M.map (compInf F E w)) := fun M => map_cT_sigR_map (evInf F w) σ M
    rw [matHom_projArch]
    change ((matHom _ σ J (ι (infGL E d y))).1).map (compInf F E w) = _
    rw [hform, ← map_inv]
    rw [map_blockForm, hA, hA, hA, hA, hC, hp, hp, map_inv]
