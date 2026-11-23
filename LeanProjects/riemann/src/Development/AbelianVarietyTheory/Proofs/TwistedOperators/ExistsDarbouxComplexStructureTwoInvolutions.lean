import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfComStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlaceStatement

noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacLn

namespace GlobalTheory.SignInvolDarboux

section Coords

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def mulC (t : mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun x := fun i => t * x i
  map_add' x y := by funext i; simp [mul_add]
  map_smul' r x := by funext i; simp [mul_smul_comm]

theorem evI_mul' (a b : AF F) : evI F (a * b) = evI F a * evI F b := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 * b.1) =
    InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 * InfiniteAdeleRing.ringEquiv_mixedSpace F b.1
  rw [map_mul]

theorem evI_realAd' (r : ℝ) : evI F (realAd F r) = algebraMap ℝ _ r := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ r)) = _
  exact RingEquiv.apply_symm_apply _ _

theorem smul_ptAt (u : AF F) (x : κ → mixedEmbedding.mixedSpace F) :
    u • GlobalTheory.RealLift.ptAt x 0 = GlobalTheory.RealLift.ptAt (mulC (evI F u) x) 0 := by
  funext i
  refine Prod.ext ?_ ?_
  · show u.1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 * x i)
    rw [map_mul, RingEquiv.symm_apply_apply]
  · show u.2 * 0 = 0
    exact mul_zero _

theorem ptAt_add (x y : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.RealLift.ptAt (x + y) 0 = GlobalTheory.RealLift.ptAt x 0 + GlobalTheory.RealLift.ptAt y 0 := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i + y i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)
    exact map_add _ _ _
  · show (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) = 0 + 0
    rw [add_zero]

theorem ptAt_zero : GlobalTheory.RealLift.ptAt (0 : κ → mixedEmbedding.mixedSpace F) 0 = 0 := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
    exact map_zero _
  · rfl

end Coords

section Dar

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
  {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}

def mulP (t : mixedEmbedding.mixedSpace F) :
    ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :=
  (mulC t).prodMap (mulC t)

def mk (d : Darboux B κ) (y : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) : W :=
  d.e.symm (GlobalTheory.RealLift.ptAt y.1 0, GlobalTheory.RealLift.ptAt y.2 0)

theorem mk_mulP (d : Darboux B κ) (u : AF F) (y : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mk d (mulP (evI F u) y) = u • mk d y := by
  rw [mk, mk, ← LinearEquiv.map_smul, Prod.smul_mk, smul_ptAt, smul_ptAt]
  rfl

theorem mk_add (d : Darboux B κ) (y y' : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mk d (y + y') = mk d y + mk d y' := by
  show d.e.symm (GlobalTheory.RealLift.ptAt (y.1 + y'.1) 0, GlobalTheory.RealLift.ptAt (y.2 + y'.2) 0) =
    d.e.symm (GlobalTheory.RealLift.ptAt y.1 0, GlobalTheory.RealLift.ptAt y.2 0) + d.e.symm (GlobalTheory.RealLift.ptAt y'.1 0, GlobalTheory.RealLift.ptAt y'.2 0)
  rw [ptAt_add, ptAt_add, ← map_add]
  rfl

theorem mk_zero (d : Darboux B κ) : mk d (0 : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) = 0 := by
  rw [mk]
  show d.e.symm (GlobalTheory.RealLift.ptAt 0 0, GlobalTheory.RealLift.ptAt 0 0) = 0
  rw [ptAt_zero, Prod.mk_zero_zero, map_zero]

theorem mk_smul_real (d : Darboux B κ) (r : ℝ) (y : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mk d (r • y) = realAd F r • mk d y := by
  rw [← mk_mulP, evI_realAd']
  congr 1

theorem coord_mk (d : Darboux B κ) (y : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    coord d (mk d y) = y := by
  simp only [coord, mk, LinearEquiv.apply_symm_apply]
  exact Prod.ext (funext fun i => RingEquiv.apply_symm_apply _ _) (funext fun i => RingEquiv.apply_symm_apply _ _)

theorem at_mk (d : Darboux B κ) (y : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    At (evI F) (mk d y) := by
  intro u hu
  rw [← mk_mulP, hu]
  have h0 : mulP (0 : mixedEmbedding.mixedSpace F) y = 0 :=
    Prod.ext (funext fun i => zero_mul _) (funext fun i => zero_mul _)
  rw [h0, mk_zero]

theorem mk_coord (d : Darboux B κ) {w : W} (hw : At (evI F) w) : mk d (coord d w) = w := by
  apply d.e.injective
  rw [mk, LinearEquiv.apply_symm_apply]
  have h1 : At (evI F) (d.e w).1 := fun u hu => by
    have h := congrArg (fun z => (d.e z).1) (hw u hu)
    simpa only [LinearEquiv.map_smul, Prod.smul_fst, map_zero, Prod.fst_zero] using h
  have h2 : At (evI F) (d.e w).2 := fun u hu => by
    have h := congrArg (fun z => (d.e z).2) (hw u hu)
    simpa only [LinearEquiv.map_smul, Prod.smul_snd, map_zero, Prod.snd_zero] using h
  refine Prod.ext (funext fun i => Prod.ext ?_ ?_) (funext fun i => Prod.ext ?_ ?_)
  · exact RingEquiv.symm_apply_apply _ _
  · exact (GlobalTheory.RealLift.fin_eq_zero_of_at h1 i).symm
  · exact RingEquiv.symm_apply_apply _ _
  · exact (GlobalTheory.RealLift.fin_eq_zero_of_at h2 i).symm

end Dar

section Comp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {α β : Type}

theorem piInf_algebraMap {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  show infEmb τ (compInf F E w (a ⊗ₜ[F] (1 : E))) = _
  simp only [compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    infEmb_tmul, map_one, mul_one]
  rfl

theorem piInf_smul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (z : AE F E) :
    piInf τ (a • z) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * piInf τ z := by
  rw [Algebra.smul_def, map_mul, piInf_algebraMap]

theorem map_smul_piInf {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (M : Matrix α β (AE F E)) :
    (a • M).map (piInf τ) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) • M.map (piInf τ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, piInf_smul, smul_eq_mul]

end Comp

section Sign

variable {F : Type} [Field F] [NumberField F]

def sgnAd (ε ε' : InfinitePlace F → ℤˣ) : AF F :=
  ((fun w => if ε w = ε' w then 0 else 1 : InfiniteAdeleRing F), 0)

theorem sgnAd_mul_self (ε ε' : InfinitePlace F → ℤˣ) : sgnAd ε ε' * sgnAd ε ε' = sgnAd ε ε' := by
  refine Prod.ext (funext fun w => ?_) ?_
  · show (if ε w = ε' w then (0 : w.Completion) else 1) * (if ε w = ε' w then 0 else 1) = if ε w = ε' w then 0 else 1
    split_ifs <;> simp
  · show (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * 0 = 0
    exact mul_zero _

theorem ext_sgnAd (ε ε' : InfinitePlace F → ℤˣ) (w : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding w ((sgnAd ε ε').1 w) = if ε w = ε' w then 0 else 1 := by
  show InfinitePlace.Completion.extensionEmbedding w (if ε w = ε' w then (0 : w.Completion) else 1) = _
  split_ifs <;> simp

theorem evI_sgnAd_mul_self (ε ε' : InfinitePlace F → ℤˣ) :
    evI F (sgnAd ε ε') * evI F (sgnAd ε ε') = evI F (sgnAd ε ε') := by
  rw [← evI_mul', sgnAd_mul_self]

end Sign

section Main

theorem exists_bridge : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (θA : InfinitePlace F → Matrix α α ℂ)
    (θB : InfinitePlace F → Matrix β β ℂ) (ε ε' : InfinitePlace F → ℤˣ), IsCMExt F E σ →
    (∀ w, θA w * θA w = 1) → (∀ w, θB w * θB w = 1) →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ u u' u₁ : Matrix α β (AE F E),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧
        (∀ w, u'.map (piInf (τ w)) = (((ε' w : ℤ) : ℂ) * Complex.I) • (θA w * u.map (piInf (τ w)) * (θB w)ᵀ)) ∧
        (∀ w, u₁.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (θA w * u.map (piInf (τ w)) * (θB w)ᵀ)) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ τ JA JB d θA θB ε ε' hcm hA hB

  let Ψl : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      (InfinitePlace F → Matrix α β ℂ) :=
    { toFun := fun y w => (mk d y).map (piInf (τ w))
      map_add' := fun y y' => by
        funext w
        ext i j
        simp only [mk_add, Matrix.map_apply, Matrix.add_apply, map_add, Pi.add_apply]
      map_smul' := fun r y => by
        funext w
        rw [mk_smul_real, GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hcm (mk d y) r w]
        ext i j
        simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, RingHom.id_apply, Pi.smul_apply] }
  have hΨl : ∀ y w, Ψl y w = (mk d y).map (piInf (τ w)) := fun _ _ => rfl
  have hinj : Function.Injective Ψl := by
    intro y y' h
    have hu := (GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hcm (Ψl y)).unique ⟨at_mk d y, fun w => rfl⟩
      ⟨at_mk d y', fun w => (congrFun h w).symm⟩
    rw [← coord_mk d y, ← coord_mk d y', hu]
  have hsurj : Function.Surjective Ψl := by
    intro M
    obtain ⟨u, ⟨hu, hM⟩, -⟩ := GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hcm M
    refine ⟨coord d u, funext fun w => ?_⟩
    rw [hΨl, mk_coord d hu]
    exact hM w
  let Ψ := LinearEquiv.ofBijective Ψl ⟨hinj, hsurj⟩

  let L : (InfinitePlace F → Matrix α β ℂ) →ₗ[ℝ] (InfinitePlace F → Matrix α β ℂ) :=
    { toFun := fun c w => (((ε w : ℤ) : ℂ) * Complex.I) • (θA w * c w * (θB w)ᵀ)
      map_add' := fun c c' => by
        funext w
        simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add]
      map_smul' := fun r c => by
        funext w
        simp only [Pi.smul_apply, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
        exact smul_comm _ _ _ }

  let P : (InfinitePlace F → Matrix α β ℂ) →ₗ[ℝ] (InfinitePlace F → Matrix α β ℂ) :=
    { toFun := fun c w => (if ε w = ε' w then (0 : ℂ) else 1) • c w
      map_add' := fun c c' => by
        funext w
        simp only [Pi.add_apply, smul_add]
      map_smul' := fun r c => by
        funext w
        simp only [Pi.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hLL : ∀ c, L (L c) = -c := by
    intro c
    funext w
    show (((ε w : ℤ) : ℂ) * Complex.I) • (θA w * ((((ε w : ℤ) : ℂ) * Complex.I) • (θA w * c w * (θB w)ᵀ)) * (θB w)ᵀ) =
      -c w
    have hB' : (θB w)ᵀ * (θB w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hB w, Matrix.transpose_one]
    have key : θA w * (θA w * c w * (θB w)ᵀ) * (θB w)ᵀ = c w := by
      calc _ = (θA w * θA w) * c w * ((θB w)ᵀ * (θB w)ᵀ) := by simp only [Matrix.mul_assoc]
        _ = c w := by rw [hA w, hB', Matrix.one_mul, Matrix.mul_one]
    have hε : ((ε w : ℤ) : ℂ) * ((ε w : ℤ) : ℂ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have hsq : (((ε w : ℤ) : ℂ) * Complex.I) * (((ε w : ℤ) : ℂ) * Complex.I) = -1 := by
      calc _ = (((ε w : ℤ) : ℂ) * ((ε w : ℤ) : ℂ)) * (Complex.I * Complex.I) := by ring
        _ = -1 := by rw [hε, Complex.I_mul_I, one_mul]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, key, hsq, neg_one_smul]
  have hLP : ∀ c, L (P c) = P (L c) := by
    intro c
    funext w
    show (((ε w : ℤ) : ℂ) * Complex.I) • (θA w * ((if ε w = ε' w then (0 : ℂ) else 1) • c w) * (θB w)ᵀ) =
      (if ε w = ε' w then (0 : ℂ) else 1) • ((((ε w : ℤ) : ℂ) * Complex.I) • (θA w * c w * (θB w)ᵀ))
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]

  have htt := evI_sgnAd_mul_self ε ε'
  have hΨe : ∀ y, Ψl (mulP (evI F (sgnAd ε ε')) y) = P (Ψl y) := by
    intro y
    funext w
    show (mk d (mulP (evI F (sgnAd ε ε')) y)).map (piInf (τ w)) = (if ε w = ε' w then (0 : ℂ) else 1) • Ψl y w
    rw [mk_mulP, map_smul_piInf, ext_sgnAd]
    rfl
  let J : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :=
    (Ψ.symm : (InfinitePlace F → Matrix α β ℂ) →ₗ[ℝ] _).comp (L.comp Ψl)
  have hΨJ : ∀ y, Ψl (J y) = L (Ψl y) := fun y => Ψ.apply_symm_apply _
  refine ⟨J, mulP (evI F (sgnAd ε ε')), mulC (evI F (sgnAd ε ε')), ?_, ?_, ?_, fun y => rfl, ?_, ?_⟩
  · intro y
    apply hinj
    rw [hΨJ, hΨJ, hLL, map_neg]
  · intro y
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show evI F (sgnAd ε ε') * (evI F (sgnAd ε ε') * y.1 i) = evI F (sgnAd ε ε') * y.1 i
      rw [← mul_assoc, htt]
    · show evI F (sgnAd ε ε') * (evI F (sgnAd ε ε') * y.2 i) = evI F (sgnAd ε ε') * y.2 i
      rw [← mul_assoc, htt]
  · intro y
    apply hinj
    rw [hΨJ, hΨe, hΨe, hΨJ, hLP]
  · intro y x
    simp only [trPair_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show x i * (evI F (sgnAd ε ε') * y.2 i) = (evI F (sgnAd ε ε') * x i) * y.2 i
    ring
  · intro y
    refine ⟨mk d y, mk d (J (y - (2 : ℝ) • mulP (evI F (sgnAd ε ε')) y)), mk d (J y), at_mk d _, at_mk d _, at_mk d _, fun w => ?_,
      fun w => ?_, coord_mk d _, coord_mk d _, coord_mk d _⟩
    · show Ψl (J (y - (2 : ℝ) • mulP (evI F (sgnAd ε ε')) y)) w = _
      rw [hΨJ, map_sub, map_smul, hΨe]
      show (((ε w : ℤ) : ℂ) * Complex.I) •
          (θA w * (Ψl y w - (2 : ℝ) • ((if ε w = ε' w then (0 : ℂ) else 1) • Ψl y w)) * (θB w)ᵀ) =
        (((ε' w : ℤ) : ℂ) * Complex.I) • (θA w * Ψl y w * (θB w)ᵀ)
      generalize Ψl y w = X
      rcases Int.units_eq_one_or (ε w) with h1 | h1 <;> rcases Int.units_eq_one_or (ε' w) with h2 | h2 <;>
        simp [h1, h2, two_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul]
    · show Ψl (J y) w = _
      rw [hΨJ]
      rfl

end Main

end GlobalTheory.SignInvolDarboux
