import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ArchTransportDir

section Mixed

variable (F : Type) [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

def eInf : AF F := (1, 0)

def rInf (t : ℝ) : AF F := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t), 0)

variable {F} {κ : Type} [Fintype κ]

def archParts (y : (κ → AF F) × (κ → AF F)) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) :=
  (GlobalTheory.WeilL2Words.archPart F y.1, GlobalTheory.WeilL2Words.archPart F y.2)

local notation "toM" => InfiniteAdeleRing.ringEquiv_mixedSpace F

theorem archimedean_map_add (z z' : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (z + z') = GlobalTheory.WeilL2Words.arch1 F z + GlobalTheory.WeilL2Words.arch1 F z' := by
  show (((toM).symm (z + z'), 0) : AF F) = (((toM).symm z + (toM).symm z', 0 + 0) : AF F)
  rw [map_add, add_zero]

theorem arch_projection_real_smul (t : ℝ) (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (t • z) = rInf F t * GlobalTheory.WeilL2Words.arch1 F z := by
  show (((toM).symm (t • z), 0) : AF F) = (((toM).symm (algebraMap ℝ _ t) * (toM).symm z, 0 * 0) : AF F)
  rw [Algebra.smul_def, map_mul, mul_zero]

theorem arch_projection_idempotent (z : mixedEmbedding.mixedSpace F) : GlobalTheory.WeilL2Words.arch1 F z = eInf F * GlobalTheory.WeilL2Words.arch1 F z := by
  show (((toM).symm z, 0) : AF F) = ((1 * (toM).symm z, 0 * 0) : AF F)
  rw [one_mul, mul_zero]

theorem toM_add (a b : AF F) : toM (a + b).1 = toM a.1 + toM b.1 := map_add (toM) a.1 b.1

theorem toM_rInf (t : ℝ) (a : AF F) : toM (rInf F t * a).1 = t • toM a.1 := by
  show toM ((toM).symm (algebraMap ℝ _ t) * a.1) = _
  rw [map_mul, RingEquiv.apply_symm_apply, Algebra.smul_def]

theorem arch_projection_to_mixed_space {a : AF F} (ha : eInf F * a = a) : GlobalTheory.WeilL2Words.arch1 F (toM a.1) = a := by
  have h2 : a.2 = 0 := by
    rw [← ha]
    show (0 : FiniteAdeleRing (𝓞 F) F) * a.2 = 0
    exact zero_mul _
  show (((toM).symm (toM a.1), 0) : AF F) = a
  rw [RingEquiv.symm_apply_apply]
  show ((a.1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = a
  exact Prod.ext rfl h2.symm

theorem archPair_add (h h' : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    GlobalTheory.WeilL2Words.archPair F (h + h') = GlobalTheory.WeilL2Words.archPair F h + GlobalTheory.WeilL2Words.archPair F h' :=
  Prod.ext (funext fun i => archimedean_map_add (h.1 i) (h'.1 i)) (funext fun i => archimedean_map_add (h.2 i) (h'.2 i))

theorem archPair_smul (t : ℝ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    GlobalTheory.WeilL2Words.archPair F (t • h) = rInf F t • GlobalTheory.WeilL2Words.archPair F h :=
  Prod.ext (funext fun i => arch_projection_real_smul t (h.1 i)) (funext fun i => arch_projection_real_smul t (h.2 i))

theorem archPair_eInf (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    GlobalTheory.WeilL2Words.archPair F h = eInf F • GlobalTheory.WeilL2Words.archPair F h :=
  Prod.ext (funext fun i => arch_projection_idempotent (h.1 i)) (funext fun i => arch_projection_idempotent (h.2 i))

theorem archParts_add (y y' : (κ → AF F) × (κ → AF F)) : archParts (y + y') = archParts y + archParts y' :=
  Prod.ext (funext fun i => toM_add (y.1 i) (y'.1 i)) (funext fun i => toM_add (y.2 i) (y'.2 i))

theorem archParts_smul (t : ℝ) (y : (κ → AF F) × (κ → AF F)) : archParts (rInf F t • y) = t • archParts y :=
  Prod.ext (funext fun i => toM_rInf t (y.1 i)) (funext fun i => toM_rInf t (y.2 i))

theorem archPair_archParts {y : (κ → AF F) × (κ → AF F)} (hy : eInf F • y = y) :
    GlobalTheory.WeilL2Words.archPair F (archParts y) = y :=
  Prod.ext (funext fun i => arch_projection_to_mixed_space (congrFun (congrArg Prod.fst hy) i))
    (funext fun i => arch_projection_to_mixed_space (congrFun (congrArg Prod.snd hy) i))

theorem continuous_archParts : Continuous (archParts (F := F) (κ := κ)) := by
  refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_)
  · exact (continuous_toMixed F).comp (continuous_fst.comp ((continuous_apply i).comp continuous_fst))
  · exact (continuous_toMixed F).comp (continuous_fst.comp ((continuous_apply i).comp continuous_snd))

end Mixed

section Lin

variable {S R' : Type} [CommRing S] [CommRing R'] [Algebra S R'] {α β : Type} [Fintype α] [Fintype β]

def mulMulT (P : Matrix α α R') (Q : Matrix β β R') : Matrix α β R' →ₗ[S] Matrix α β R' where
  toFun x := P * x * Qᵀ
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

end Lin

theorem archDir_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ p w, ∀ φ ∈ schA F κ, om p (co.rho ψ w φ) = co.rho ψ (actAB (cA σ) p w) (om p φ)) →
    ∃ M : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ p h, ∀ φ ∈ schA F κ,
        om p (schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  intro F E _ _ _ _ _ σ ψ m n JA JB ξ κ _ co om hom
  let L : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →
      ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F)) := fun p =>
    co.e.toLinearMap ∘ₗ mulMulT (S := AF F) (((p⁻¹).1 : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E))
      (((p⁻¹).2 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) ∘ₗ co.e.symm.toLinearMap
  have hL : ∀ p x, L p x = co.e (actAB (cA σ) p⁻¹ (co.e.symm x)) := fun p x => rfl
  have hfix : ∀ p h, eInf F • L p (GlobalTheory.WeilL2Words.archPair F h) = L p (GlobalTheory.WeilL2Words.archPair F h) := by
    intro p h
    conv_rhs => rw [archPair_eInf h, map_smul]
  have hact : ∀ (p : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) (x : Matrix (Fin m) (Fin n) (AE F E)), actAB (cA σ) p (actAB (cA σ) p⁻¹ x) = x := by
    intro p x
    have h1 : ((p.1 : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)) *
        (((p⁻¹).1 : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)) = 1 := by
      rw [Prod.fst_inv, Subgroup.coe_inv, Units.mul_inv]
    have h2 : (((p⁻¹).2 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ *
        ((p.2 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Prod.snd_inv, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one]
    simp only [actAB, Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨fun p => { toFun := fun h => archParts (L p (GlobalTheory.WeilL2Words.archPair F h)), map_add' := ?_, map_smul' := ?_ },
    ?_, ?_⟩
  · intro h h'
    rw [archPair_add, map_add, archParts_add]
  · intro t h
    rw [RingHom.id_apply, archPair_smul, map_smul, archParts_smul]
  · intro p h φ hφ
    have key := hom p (actAB (cA σ) p⁻¹ (co.e.symm (GlobalTheory.WeilL2Words.archPair F h))) φ hφ
    show om p (schr ψ (GlobalTheory.WeilL2Words.archPair F (archParts (L p (GlobalTheory.WeilL2Words.archPair F h)))) φ) = _
    rw [archPair_archParts (hfix p h), hL]
    simp only [Darboux.rho] at key
    rw [hact, LinearEquiv.apply_symm_apply] at key
    exact key
  · intro h
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
    haveI : IsModuleTopology (AF F) (Matrix (Fin m) (Fin n) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin m → Fin n → AE F E))
    have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
    have hP : Continuous fun p : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) =>
        (((p⁻¹).1 : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_inv))
    have hQ : Continuous fun p : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) =>
        (((p⁻¹).2 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_inv))
    exact continuous_archParts.comp (hce.comp ((hP.matrix_mul continuous_const).matrix_mul hQ.matrix_transpose))

end GlobalTheory.ArchTransportDir

end
