import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.FockPair

open GlobalTheory.ThK.EvAt0.PolD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def pt (M : Model σ X W)
    (x : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    Matrix (Fin n) (Fin d) (AE F E) :=
  M.co.e.symm (fun i => liftA (x.1 i), fun i => liftA (x.2 i))

def crd (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  (arc (M.co.e u).1, arc (M.co.e u).2)

def vals (τ : ∀ w : InfinitePlace F, EmbOver E w) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    InfinitePlace F → Matrix (Fin n) (Fin d) ℂ :=
  fun v => u.map (piInf (τ v))

def cx (X : Spc F E n) (W : Spc F E d) (ε : InfinitePlace F → ℤˣ) (m : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ) :
    InfinitePlace F → Matrix (Fin n) (Fin d) ℂ :=
  fun v => (((ε v : ℤ) : ℂ) * Complex.I) • (X.θ v * m v * (W.θ v)ᵀ)

def liftN [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) (ξ : E)
    (m : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ) : Matrix (Fin n) (Fin d) (AE F E) :=
  Matrix.of fun i j => GlobalTheory.RealLift.OneParam.liftC τ ξ fun v => m v i j

def jF [IsTotallyReal F] (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (ξ : E) (ε : InfinitePlace F → ℤˣ)
    (x : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  crd M (liftN τ ξ (cx X W ε (vals τ (pt M x))))

theorem at_pt (M : Model σ X W) (x) : At (evI F) (pt M x) := GlobalTheory.ThK.EvAt0.PolEv.at_symm M x.1 x.2

theorem crd_pt (M : Model σ X W) (x) : crd M (pt M x) = x := by
  simp only [crd, pt, LinearEquiv.apply_symm_apply]
  rw [GlobalTheory.ThK.EvAt0.PolEv.arc_liftA, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA]

theorem liftA_evI {c : AF F} (h : c.2 = 0) : liftA (evI F c) = c := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F c.1) = c.1
    exact RingEquiv.symm_apply_apply _ _
  · rw [h]; rfl

theorem at_coords (M : Model σ X W) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) :
    At (evI F) (M.co.e u).1 ∧ At (evI F) (M.co.e u).2 := by
  have k : ∀ r : AF F, evI F r = 0 → r • M.co.e u = 0 := fun r hr => by rw [← map_smul, hu r hr, map_zero]
  exact ⟨fun r hr => by simpa using congrArg Prod.fst (k r hr), fun r hr => by simpa using congrArg Prod.snd (k r hr)⟩

theorem pt_crd (M : Model σ X W) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) : pt M (crd M u) = u := by
  obtain ⟨h1, h2⟩ := at_coords M hu
  apply M.co.e.injective
  simp only [pt, crd, LinearEquiv.apply_symm_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact liftA_evI (GlobalTheory.RealLift.fin_eq_zero_of_at h1 i)
  · exact liftA_evI (GlobalTheory.RealLift.fin_eq_zero_of_at h2 i)

theorem at_entry {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (i : Fin n) (j : Fin d) :
    At (evI F) (u i j) := fun r hr => by
  have := congrFun (congrFun (hu r hr) i) j
  simpa using this

theorem uniq (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {u u' : Matrix (Fin n) (Fin d) (AE F E)}
    (hu : At (evI F) u) (hu' : At (evI F) u') (h : vals τ u = vals τ u') : u = u' := by
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.RealLift.OneParam.eq_zero_of_at hcm τ (fun r hr => ?_) fun v => ?_)
  · rw [smul_sub, at_entry hu i j r hr, at_entry hu' i j r hr, sub_zero]
  · have := congrFun (congrFun (congrFun h v) i) j
    simp only [vals, Matrix.map_apply] at this
    rw [map_sub, this, sub_self]

theorem at_liftN [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) (ξ : E)
    (m : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ) : At (evI F) (liftN τ ξ m) := fun r hr => by
  ext i j
  simp only [liftN, Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
  exact GlobalTheory.RealLift.OneParam.at_liftC τ ξ _ r hr

theorem vals_liftN [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) {ξ : E} (hξ : ∀ w, ((τ w).1 ξ).im ≠ 0)
    (m : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ) : vals τ (liftN τ ξ m) = m := by
  funext v
  ext i j
  exact GlobalTheory.RealLift.OneParam.piInf_liftC τ hξ _ v

theorem at_add {u u' : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (hu' : At (evI F) u') :
    At (evI F) (u + u') := fun r hr => by rw [smul_add, hu r hr, hu' r hr, add_zero]

theorem at_neg {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) : At (evI F) (-u) := fun r hr => by
  rw [smul_neg, hu r hr, neg_zero]

theorem at_smul {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (s : AF F) : At (evI F) (s • u) :=
  fun r hr => by rw [smul_smul, mul_comm, ← smul_smul, hu r hr, smul_zero]

theorem vals_add (τ : ∀ w : InfinitePlace F, EmbOver E w) (u u' : Matrix (Fin n) (Fin d) (AE F E)) :
    vals τ (u + u') = vals τ u + vals τ u' := by
  funext v; ext i j; simp [vals]

theorem vals_neg (τ : ∀ w : InfinitePlace F, EmbOver E w) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    vals τ (-u) = -vals τ u := by
  funext v; ext i j; simp [vals]

theorem vals_smul (τ : ∀ w : InfinitePlace F, EmbOver E w) (r : AF F) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    vals τ (r • u) = fun v => piInf (τ v) (algebraMap (AF F) (AE F E) r) • vals τ u v := by
  funext v; ext i j
  simp [vals, Algebra.smul_def, map_mul]

theorem cx_add (ε : InfinitePlace F → ℤˣ) (m m' : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ) :
    cx X W ε (m + m') = cx X W ε m + cx X W ε m' := by
  funext v; simp [cx, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem cx_smul (ε : InfinitePlace F → ℤˣ) (c : InfinitePlace F → ℂ) (m : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ) :
    cx X W ε (fun v => c v • m v) = fun v => c v • cx X W ε m v := by
  funext v; simp only [cx]; rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]

theorem cx_cx (ε : InfinitePlace F → ℤˣ) (hX : ∀ v, X.θ v * X.θ v = 1) (hW : ∀ v, W.θ v * W.θ v = 1)
    (m : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ) : cx X W ε (cx X W ε m) = -m := by
  funext v
  have he : ((ε v : ℤ) : ℂ) * ((ε v : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  have hWt : (W.θ v)ᵀ * (W.θ v)ᵀ = 1 := by rw [← Matrix.transpose_mul, hW v, Matrix.transpose_one]
  simp only [cx, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  have e : X.θ v * (X.θ v * m v * (W.θ v)ᵀ) * (W.θ v)ᵀ = m v := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hX v, Matrix.one_mul, Matrix.mul_assoc, hWt, Matrix.mul_one]
  rw [e, Pi.neg_apply]
  have : ((ε v : ℤ) : ℂ) * Complex.I * (((ε v : ℤ) : ℂ) * Complex.I) = -1 := by
    linear_combination (Complex.I ^ 2) * he + Complex.I_sq
  rw [this, neg_one_smul]

theorem liftA_add (a b : mixedEmbedding.mixedSpace F) : liftA (F := F) (a + b) = liftA a + liftA b := by
  simp only [liftA]
  rw [map_add, map_add]
  rfl

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_neg (a : AF F) : evI F (-a) = -evI F a :=
  map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1

theorem realAd_mul_liftA (t : ℝ) (a : mixedEmbedding.mixedSpace F) : realAd F t * liftA a = liftA (t • a) := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • a)
    rw [← map_mul, Algebra.smul_def]
  · show (0 : Af F) * 0 = 0
    exact mul_zero _

theorem evI_realAd_mul (t : ℝ) (c : AF F) : evI F (realAd F t * c) = t • evI F c := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((realAd F t).1 * c.1) = _
  rw [map_mul]
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) * _ = _
  rw [RingEquiv.apply_symm_apply, ← Algebra.smul_def]
  rfl

theorem pt_add (M : Model σ X W) (x y) : pt M (x + y) = pt M x + pt M y := by
  simp only [pt]
  rw [← map_add]
  congr 1
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [liftA_add]

theorem pt_smul (M : Model σ X W) (t : ℝ) (x) : pt M (t • x) = realAd F t • pt M x := by
  simp only [pt]
  rw [← map_smul]
  congr 1
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [realAd_mul_liftA]

theorem crd_add (M : Model σ X W) (u u' : Matrix (Fin n) (Fin d) (AE F E)) : crd M (u + u') = crd M u + crd M u' := by
  simp only [crd, map_add]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  · exact evI_add _ _

theorem crd_neg (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) : crd M (-u) = -crd M u := by
  simp only [crd, map_neg]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  · exact evI_neg _

theorem crd_smul (M : Model σ X W) (t : ℝ) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    crd M (realAd F t • u) = t • crd M u := by
  simp only [crd, map_smul]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  · show evI F (realAd F t * _) = t • evI F _
    exact evI_realAd_mul t _

end GlobalTheory.FockPair

namespace GlobalTheory.FockPair

open GlobalTheory.ThK.EvAt0.PolD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d} [IsTotallyReal F]

theorem img_add (hcm : IsCMExt F E σ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) {ξ : E}
    (hξ : ∀ w, ((τ w).1 ξ).im ≠ 0) (ε : InfinitePlace F → ℤˣ) (x y) :
    liftN τ ξ (cx X W ε (vals τ (pt M (x + y)))) =
      liftN τ ξ (cx X W ε (vals τ (pt M x))) + liftN τ ξ (cx X W ε (vals τ (pt M y))) := by
  apply uniq hcm τ (at_liftN τ ξ _) (at_add (at_liftN τ ξ _) (at_liftN τ ξ _))
  rw [vals_add, vals_liftN τ hξ, vals_liftN τ hξ, vals_liftN τ hξ, pt_add, vals_add, cx_add]

theorem img_smul (hcm : IsCMExt F E σ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) {ξ : E}
    (hξ : ∀ w, ((τ w).1 ξ).im ≠ 0) (ε : InfinitePlace F → ℤˣ) (t : ℝ) (x) :
    liftN τ ξ (cx X W ε (vals τ (pt M (t • x)))) = realAd F t • liftN τ ξ (cx X W ε (vals τ (pt M x))) := by
  apply uniq hcm τ (at_liftN τ ξ _) (at_smul (at_liftN τ ξ _) _)
  rw [vals_smul, vals_liftN τ hξ, vals_liftN τ hξ, pt_smul, vals_smul, cx_smul]

theorem jF_add (hcm : IsCMExt F E σ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) {ξ : E}
    (hξ : ∀ w, ((τ w).1 ξ).im ≠ 0) (ε : InfinitePlace F → ℤˣ) (x y) :
    jF M τ ξ ε (x + y) = jF M τ ξ ε x + jF M τ ξ ε y := by
  simp only [jF]
  rw [img_add hcm M τ hξ ε, crd_add]

theorem jF_smul (hcm : IsCMExt F E σ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) {ξ : E}
    (hξ : ∀ w, ((τ w).1 ξ).im ≠ 0) (ε : InfinitePlace F → ℤˣ) (t : ℝ) (x) :
    jF M τ ξ ε (t • x) = t • jF M τ ξ ε x := by
  simp only [jF]
  rw [img_smul hcm M τ hξ ε, crd_smul]

theorem jF_jF (hcm : IsCMExt F E σ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) {ξ : E}
    (hξ : ∀ w, ((τ w).1 ξ).im ≠ 0) (ε : InfinitePlace F → ℤˣ) (hX : ∀ v, X.θ v * X.θ v = 1)
    (hW : ∀ v, W.θ v * W.θ v = 1) (x) : jF M τ ξ ε (jF M τ ξ ε x) = -x := by
  have e : liftN τ ξ (cx X W ε (vals τ (pt M (jF M τ ξ ε x)))) = -pt M x := by
    apply uniq hcm τ (at_liftN τ ξ _) (at_neg (at_pt M x))
    rw [vals_liftN τ hξ]
    show cx X W ε (vals τ (pt M (crd M (liftN τ ξ (cx X W ε (vals τ (pt M x))))))) = _
    rw [pt_crd M (at_liftN τ ξ _), vals_liftN τ hξ, cx_cx ε hX hW, vals_neg]
  show crd M (liftN τ ξ (cx X W ε (vals τ (pt M (jF M τ ξ ε x))))) = -x
  rw [e, crd_neg, crd_pt]

end GlobalTheory.FockPair

open GlobalTheory.FockPair GlobalTheory.ThK.EvAt0.PolD in

theorem GlobalTheory.FockPair.exists_fock_cx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ f₀ : SInf F (Fin n × Fin d), M.IsGauss ψ τ f₀ →
        ∃ J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
          (∀ w, J₀ (J₀ w) = -w) ∧ ∀ w x, GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (J₀ w) ⇑f₀ x =
            Complex.I * GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) w ⇑f₀ x := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ _ τ hX hW f₀ hf₀
  haveI := hcm.1
  obtain ⟨ξ, hξ⟩ := GlobalTheory.RealLift.OneParam.exists_moved hcm
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => GlobalTheory.RealLift.OneParam.im_ne_zero hcm hξ (τ w).1
  obtain ⟨ε, hε⟩ := (GlobalTheory.ThK.EvAt0.PolEv.isGauss_iff hψ M τ f₀).1 hf₀
  refine ⟨LinearMap.mk (AddHom.mk (jF M τ ξ ε) (jF_add hcm M τ hξ' ε))
      (fun t x => (jF_smul hcm M τ hξ' ε t x).trans (by rw [RingHom.id_apply])),
    fun x => jF_jF hcm M τ hξ' ε (fun v => (hX v).1) (fun v => (hW v).1) x, fun w x => ?_⟩
  have e := hε (pt M w) (liftN τ ξ (cx X W ε (vals τ (pt M w)))) (at_pt M w) (at_liftN τ ξ _)
    (fun v => congrFun (vals_liftN τ hξ' (cx X W ε (vals τ (pt M w)))) v)
  change dOp (jF M τ ξ ε w).1 (jF M τ ξ ε w).2 f₀ = Complex.I • dOp (crd M (pt M w)).1 (crd M (pt M w)).2 f₀ at e
  rw [crd_pt] at e
  have e2 := congrArg (fun g : SInf F (Fin n × Fin d) => g x) e
  simp only [SchwartzMap.smul_apply, smul_eq_mul, dOp_apply, lin] at e2
  show GlobalTheory.GaussLine.dHeis _ (jF M τ ξ ε w) _ x = _
  simp only [GlobalTheory.GaussLine.dHeis, GlobalTheory.GaussLine.pairInf_apply]
  exact e2
