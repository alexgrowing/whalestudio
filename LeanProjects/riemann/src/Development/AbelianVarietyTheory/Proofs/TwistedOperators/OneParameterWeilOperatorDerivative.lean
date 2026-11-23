import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchLineAct

variable {F : Type} [Field F] [NumberField F]

def archLift {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)

def archPart {κ : Type} (z : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (z i)

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def finHom : AF F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := map_add evIHom a b

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b := map_mul evIHom a b

theorem continuous_evI : Continuous (evI F) := by
  have h : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  exact h.comp continuous_fst

theorem fst_eq_zero {a : AF F} (h : evI F a = 0) : a.1 = 0 :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact h)

theorem mul_eq_zero_of {a b : AF F} (ha : evI F a = 0) (hb : b.2 = 0) : a * b = 0 :=
  Prod.ext (by show a.1 * b.1 = 0; rw [fst_eq_zero ha, zero_mul]) (by show a.2 * b.2 = 0; rw [hb, mul_zero])

theorem at_of_snd {a : AF F} (h : a.2 = 0) : At (evI F) a := fun u hu => mul_eq_zero_of hu h

theorem snd_of_at {a : AF F} (h : At (evI F) a) : a.2 = 0 := by
  have h1 := h (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AF F)
    (by show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0; exact map_zero _)
  have h2 : (1 : FiniteAdeleRing (𝓞 F) F) * a.2 = 0 := congrArg Prod.snd h1
  rwa [one_mul] at h2

theorem at_vec_iff {κ : Type} {z : κ → AF F} : At (evI F) z ↔ ∀ i, (z i).2 = 0 :=
  ⟨fun h i => snd_of_at (fun u hu => congrFun (h u hu) i),
    fun h u hu => funext fun i => mul_eq_zero_of hu (h i)⟩

theorem archPart_archLift {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) : archPart (archLift x) = x :=
  funext fun i => RingEquiv.apply_symm_apply _ _

theorem archLift_archPart {κ : Type} {z : κ → AF F} (hz : At (evI F) z) : archLift (archPart z) = z := by
  funext i
  refine Prod.ext ?_ ?_
  · exact RingEquiv.symm_apply_apply _ _
  · exact (at_vec_iff.1 hz i).symm

theorem at_archLift {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) : At (evI F) (archLift x) :=
  at_vec_iff.2 fun _ => rfl

theorem archLift_add {κ : Type} (x y : κ → mixedEmbedding.mixedSpace F) :
    archLift (x + y) = archLift x + archLift y := by
  funext i
  refine Prod.ext ?_ ?_
  · exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) (y i)
  · exact (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

theorem evI_realAd (c : ℝ) : evI F (realAd F c) = algebraMap ℝ (mixedEmbedding.mixedSpace F) c :=
  RingEquiv.apply_symm_apply _ _

theorem archLift_smul {κ : Type} (c : ℝ) (x : κ → mixedEmbedding.mixedSpace F) :
    archLift (c • x) = realAd F c • archLift x := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (c • x i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ c) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i)
    rw [Algebra.smul_def, map_mul]
  · show (0 : FiniteAdeleRing (𝓞 F) F) = 0 * 0
    rw [mul_zero]

theorem archPart_add {κ : Type} (z z' : κ → AF F) : archPart (z + z') = archPart z + archPart z' :=
  funext fun i => evI_add (z i) (z' i)

theorem archPart_smul {κ : Type} (c : ℝ) (z : κ → AF F) : archPart (realAd F c • z) = c • archPart z := by
  funext i
  show evI F (realAd F c * z i) = c • evI F (z i)
  rw [evI_mul, evI_realAd, Algebra.smul_def]

theorem evI_invTwo : evI F (⅟(2 : AF F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
  have h : evIHom (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evIHom (F := F)) 2, ← map_mul, invOf_mul_self, map_one]
  have h2 : algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2, ← map_mul]; norm_num
  rw [← evIHom_apply]
  calc evIHom (⅟(2 : AF F)) = evIHom (⅟(2 : AF F)) * (algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) * 2) := by
        rw [h2, mul_one]
    _ = (evIHom (⅟(2 : AF F)) * 2) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by ring
    _ = _ := by rw [h, one_mul]

theorem tens_archLift {κ : Type} (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (R : (κ → AF F) → ℂ)
    (hR : ∀ x z, At (evI F) z → R (x + z) = R x) (x : κ → mixedEmbedding.mixedSpace F) :
    tens (evI F) φ R (archLift x) = φ x * R 0 := by
  have h := hR 0 (archLift x) (at_archLift x)
  rw [zero_add] at h
  show φ (archPart (archLift x)) * R (archLift x) = φ x * R 0
  rw [archPart_archLift, h]

end GlobalTheory.ArchLineAct

end

noncomputable section

namespace GlobalTheory.ArchLineAct

variable {F : Type} [Field F] [NumberField F]

section Coord

variable {κ : Type} [Fintype κ] {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F}

def archMap (co : GlobalTheory.WeilM.Darboux Bf κ) (L : W →ₗ[AF F] W) :
    ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) where
  toFun w := (archPart (co.e (L (co.e.symm (archLift w.1, archLift w.2)))).1,
    archPart (co.e (L (co.e.symm (archLift w.1, archLift w.2)))).2)
  map_add' w w' := by
    have e : ((archLift (w + w').1, archLift (w + w').2) : (κ → AF F) × (κ → AF F)) =
        (archLift w.1, archLift w.2) + (archLift w'.1, archLift w'.2) := by
      rw [Prod.fst_add, Prod.snd_add, archLift_add, archLift_add]; rfl
    rw [e, map_add, map_add, map_add]
    exact Prod.ext (archPart_add _ _) (archPart_add _ _)
  map_smul' c w := by
    have e : ((archLift (c • w).1, archLift (c • w).2) : (κ → AF F) × (κ → AF F)) =
        realAd F c • (archLift w.1, archLift w.2) := by
      rw [Prod.smul_fst, Prod.smul_snd, archLift_smul, archLift_smul]; rfl
    rw [e, map_smul, map_smul, map_smul]
    exact Prod.ext (archPart_smul _ _) (archPart_smul _ _)

theorem archMap_apply (co : GlobalTheory.WeilM.Darboux Bf κ) (L : W →ₗ[AF F] W) (w) :
    archMap co L w = (archPart (co.e (L (co.e.symm (archLift w.1, archLift w.2)))).1,
      archPart (co.e (L (co.e.symm (archLift w.1, archLift w.2)))).2) := rfl

theorem at_lin (L : W →ₗ[AF F] W) {u : W} (hu : At (evI F) u) : At (evI F) (L u) := fun a ha => by
  rw [← map_smul, hu a ha, map_zero]

theorem at_symm (co : GlobalTheory.WeilM.Darboux Bf κ) (x y : κ → mixedEmbedding.mixedSpace F) :
    At (evI F) (co.e.symm (archLift x, archLift y)) := fun a ha => by
  rw [← map_smul, Prod.smul_mk, at_archLift x a ha, at_archLift y a ha, Prod.mk_zero_zero, map_zero]

theorem coord_eq (co : GlobalTheory.WeilM.Darboux Bf κ) {u : W} (hu : At (evI F) u) :
    co.e u = (archLift (archPart (co.e u).1), archLift (archPart (co.e u).2)) := by
  have h1 : At (evI F) (co.e u).1 := fun a ha => by
    rw [← Prod.smul_fst, ← map_smul, hu a ha, map_zero]; rfl
  have h2 : At (evI F) (co.e u).2 := fun a ha => by
    rw [← Prod.smul_snd, ← map_smul, hu a ha, map_zero]; rfl
  rw [archLift_archPart h1, archLift_archPart h2]

theorem archMap_comp (co : GlobalTheory.WeilM.Darboux Bf κ) (L₁ L₂ : W →ₗ[AF F] W) :
    (archMap co L₁).comp (archMap co L₂) = archMap co (L₁.comp L₂) := by
  refine LinearMap.ext fun w => ?_
  have h := coord_eq co (at_lin L₂ (at_symm co w.1 w.2))
  rw [LinearMap.comp_apply, archMap_apply co L₁, archMap_apply co L₂, archMap_apply co (L₁.comp L₂)]
  dsimp only
  rw [← h, LinearEquiv.symm_apply_apply, LinearMap.comp_apply]

theorem archMap_id (co : GlobalTheory.WeilM.Darboux Bf κ) : archMap co LinearMap.id = LinearMap.id := by
  refine LinearMap.ext fun w => ?_
  rw [archMap_apply, LinearMap.id_apply, LinearMap.id_apply, LinearEquiv.apply_symm_apply, archPart_archLift,
    archPart_archLift]

theorem rho_tens {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (co : GlobalTheory.WeilM.Darboux Bf κ) (u : W)
    (p q : κ → mixedEmbedding.mixedSpace F) (hu : co.e u = (archLift p, archLift q))
    (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (R : (κ → AF F) → ℂ)
    (hR : ∀ x z, At (evI F) z → R (x + z) = R x) :
    co.rho ψ u (tens (evI F) φ R) =
      tens (evI F) (GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F κ) p q φ) R := by
  funext y
  simp only [GlobalTheory.WeilM.Darboux.rho, hu, GlobalTheory.WeilM.schr, tens, GlobalTheory.GaussLine.heisFun_apply]
  have e1 : R (y + archLift p) = R y := hR y _ (at_archLift p)
  have e2 : (fun i => evI F ((y + archLift p) i)) = (fun i => evI F (y i)) + p := by
    funext i
    rw [Pi.add_apply, evI_add, Pi.add_apply]
    exact congrArg _ (congrFun (archPart_archLift p) i)
  set z : AF F := y ⬝ᵥ archLift q + ⅟(2 : AF F) * (archLift p ⬝ᵥ archLift q) with hz
  have hzat : At (evI F) z := by
    refine at_of_snd ?_
    show finHom z = 0
    simp only [hz, dotProduct, map_add, map_mul, map_sum]
    have h0 : ∀ i, finHom (archLift q i) = 0 := fun _ => rfl
    simp [h0]
  have hev : evI F z = (∑ i, evI F (y i) * q i) +
      algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) * ∑ i, p i * q i := by
    rw [← evIHom_apply, hz]
    simp only [dotProduct, map_add, map_mul, map_sum, evIHom_apply, evI_invTwo]
    have h1 : ∀ i, evI F (archLift q i) = q i := fun i => congrFun (archPart_archLift q) i
    have h2 : ∀ i, evI F (archLift p i) = p i := fun i => congrFun (archPart_archLift p) i
    simp only [h1, h2]
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F z) =
      GlobalTheory.GaussLine.pairInf F κ (fun i => evI F (y i)) q + GlobalTheory.GaussLine.pairInf F κ p q / 2 := by
    rw [hev, GlobalTheory.GaussLine.pairInf_apply, GlobalTheory.GaussLine.pairInf_apply, map_add, ← Algebra.smul_def, map_smul,
      smul_eq_mul]
    ring
  rw [e1, e2, hψ.2.2 z hzat, htr]
  ring

end Coord

end GlobalTheory.ArchLineAct

end

noncomputable section

namespace GlobalTheory.ArchLineAct

section Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rmulT {m n : ℕ} (N : Matrix (Fin n) (Fin n) (AE F E)) :
    Matrix (Fin m) (Fin n) (AE F E) →ₗ[AF F] Matrix (Fin m) (Fin n) (AE F E) where
  toFun x := x * Nᵀ
  map_add' x y := Matrix.add_mul x y Nᵀ
  map_smul' c x := Matrix.smul_mul c x Nᵀ

def lmulL {m n k : ℕ} (u : Matrix (Fin m) (Fin n) (AE F E)) :
    Matrix (Fin n) (Fin k) (AE F E) →ₗ[AF F] Matrix (Fin m) (Fin k) (AE F E) where
  toFun N := u * N
  map_add' := Matrix.mul_add u
  map_smul' c N := Matrix.mul_smul u c N

end Mat

end GlobalTheory.ArchLineAct

theorem GlobalTheory.ArchLineAct.intertwine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    ∃ A : ℝ → ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)),
      (∀ w, Continuous fun t => A t w) ∧ (∀ s t, A (s + t) = (A s).comp (A t)) ∧ A 0 = LinearMap.id ∧
      ∀ (t : ℝ) (p q : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) (f g : SInf F (Fin a × Fin (a + a'))),
        ⇑g = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a'))) p q ⇑f →
        ⇑(T t g) = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a'))) (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f) := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ T hTact
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin a × Fin (a + a'))
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil
  have hRsh : ∀ x z, At (evI F) z → R (x + z) = R x := (hR 0).1
  let L : ℝ → Matrix (Fin a) (Fin (a + a')) (AE F E) →ₗ[AF F] Matrix (Fin a) (Fin (a + a')) (AE F E) :=
    fun t => GlobalTheory.ArchLineAct.rmulT (mat (γ (Multiplicative.ofAdd t)))
  have hmat : ∀ g h : UA σ G.W.J, mat (g * h) = mat g * mat h := fun _ _ => rfl
  have hmat1 : mat (1 : UA σ G.W.J) = 1 := rfl
  refine ⟨fun t => GlobalTheory.ArchLineAct.archMap G.M.co (L t), fun w => ?_, fun s t => ?_, ?_, fun t p q f g hg => ?_⟩
  · have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t)))ᵀ :=
      (Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd))).matrix_transpose
    set u := G.M.co.e.symm (GlobalTheory.ArchLineAct.archLift w.1, GlobalTheory.ArchLineAct.archLift w.2) with hu
    let K := G.M.co.e.toLinearMap ∘ₗ (GlobalTheory.ArchLineAct.lmulL (k := a + a') u)
    haveI : IsModuleTopology (AF F) (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin (a + a') → Fin (a + a') → AE F E))
    have hK : Continuous K := IsModuleTopology.continuous_of_linearMap K
    have hc : Continuous fun t : ℝ => G.M.co.e (L t u) := hK.comp hm
    show Continuous fun t : ℝ => (GlobalTheory.ArchLineAct.archPart (G.M.co.e (L t u)).1,
      GlobalTheory.ArchLineAct.archPart (G.M.co.e (L t u)).2)
    exact Continuous.prodMk
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_fst.comp hc)))
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_snd.comp hc)))
  · show GlobalTheory.ArchLineAct.archMap G.M.co (L (s + t)) =
      (GlobalTheory.ArchLineAct.archMap G.M.co (L s)).comp (GlobalTheory.ArchLineAct.archMap G.M.co (L t))
    rw [GlobalTheory.ArchLineAct.archMap_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    show x * (mat (γ (Multiplicative.ofAdd (s + t))))ᵀ =
      (x * (mat (γ (Multiplicative.ofAdd t)))ᵀ) * (mat (γ (Multiplicative.ofAdd s)))ᵀ
    rw [ofAdd_add, map_mul, hmat, Matrix.transpose_mul, Matrix.mul_assoc]
  · show GlobalTheory.ArchLineAct.archMap G.M.co (L 0) = LinearMap.id
    have hL : L 0 = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      show x * (mat (γ (Multiplicative.ofAdd 0)))ᵀ = x
      rw [ofAdd_zero, map_one, hmat1, Matrix.transpose_one, Matrix.mul_one]
    rw [hL, GlobalTheory.ArchLineAct.archMap_id]
  · set u := G.M.co.e.symm (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) with hu
    have hue : G.M.co.e u = (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) :=
      LinearEquiv.apply_symm_apply _ _
    have hu' : At (evI F) (L t u) := GlobalTheory.ArchLineAct.at_lin _ (GlobalTheory.ArchLineAct.at_symm _ p q)
    have hue' := GlobalTheory.ArchLineAct.coord_eq G.M.co hu'
    have himpl := hW.impl (1, γ (Multiplicative.ofAdd t)) u (tens (evI F) (⇑f) R) (hR f).2
    have hact : GlobalTheory.WeilM.actAB (cA σ) ((1 : UA σ G.V.J), γ (Multiplicative.ofAdd t)) u = L t u := by
      show ((1 : UA σ G.V.J) : GL (Fin a) (AE F E)).1 * u * (mat (γ (Multiplicative.ofAdd t)))ᵀ =
        u * (mat (γ (Multiplicative.ofAdd t)))ᵀ
      rw [show ((1 : UA σ G.V.J) : GL (Fin a) (AE F E)).1 = 1 from rfl, Matrix.one_mul]
    rw [hact, GlobalTheory.ArchLineAct.rho_tens hT.base.std G.M.co u p q hue (⇑f) R hRsh, ← hg, hTact t g R (hR g),
      hTact t f R (hR f), GlobalTheory.ArchLineAct.rho_tens hT.base.std G.M.co (L t u) _ _ hue' _ R hRsh] at himpl
    funext x
    have h := congrFun himpl (GlobalTheory.ArchLineAct.archLift x)
    rw [GlobalTheory.ArchLineAct.tens_archLift _ R hRsh, GlobalTheory.ArchLineAct.tens_archLift _ R hRsh] at h
    exact mul_right_cancel₀ hR0 h

end
