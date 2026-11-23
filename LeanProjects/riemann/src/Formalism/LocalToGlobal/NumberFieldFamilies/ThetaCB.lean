import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInfEmbUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Emb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isInfEmb_unique (τ : E →+* ℂ) {θ θ' : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmb τ θ) (h' : IsInfEmb τ θ') : θ = θ' := by
  first | exact UpperTheory.Reformulated.B.Qh26.isInfEmb_unique .. | (apply UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› τ θ θ' h h' | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› τ θ θ' h | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› τ θ θ' | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› τ θ | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› τ | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F

def plF (τ : E →+* ℂ) : InfinitePlace F := InfinitePlace.mk (τ.comp (algebraMap F E))

def compF (τ : E →+* ℂ) : Ainf F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding (plF (F := F) τ)).comp
    (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) (plF (F := F) τ))

theorem compF_cont (τ : E →+* ℂ) : Continuous (compF (F := F) τ) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (plF (F := F) τ)).continuous.comp (continuous_apply _)

theorem compF_alg [IsTotallyReal F] (τ : E →+* ℂ) (x : F) : compF (F := F) τ (algebraMap F (Ainf F) x) = τ (algebraMap F E x) := by
  have h1 : compF (F := F) τ (algebraMap F (Ainf F) x) = (plF (F := F) τ).embedding x :=
    InfinitePlace.Completion.extensionEmbedding_coe (plF (F := F) τ) _
  rw [h1]
  have hr : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) := IsTotallyReal.complexEmbedding_isReal _
  unfold plF
  rw [InfinitePlace.embedding_mk_eq_of_isReal hr]
  rfl

def projAt [IsTotallyReal F] (τ : E →+* ℂ) : Ainf F ⊗[F] E →+* ℂ :=
  letI : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  (Algebra.TensorProduct.productMap (R := F)
    ({ compF (F := F) τ with commutes' := fun x => compF_alg τ x } : Ainf F →ₐ[F] ℂ)
    ({ τ with commutes' := fun _ => rfl } : E →ₐ[F] ℂ)).toRingHom

theorem projAt_tmul [IsTotallyReal F] (τ : E →+* ℂ) (a : Ainf F) (x : E) :
    projAt (F := F) τ (a ⊗ₜ[F] x) = compF (F := F) τ a * τ x := rfl

theorem projAt_isInfEmb [IsTotallyReal F] (τ : E →+* ℂ) : IsInfEmb τ (projAt (F := F) τ) := by
  refine ⟨fun x => by rw [projAt_tmul, map_one, one_mul], ?_⟩
  simp only [projAt_tmul, map_one, mul_one]
  exact compF_cont τ

def inlA : Ainf F →ₗ[F] AF F where
  toFun a := pairA F a 0
  map_add' a b := Prod.ext rfl (add_zero (0 : Af F)).symm
  map_smul' c a := Prod.ext rfl (smul_zero (A := Af F) c).symm

def inrA : Af F →ₗ[F] AF F where
  toFun b := pairA F 0 b
  map_add' a b := Prod.ext (add_zero (0 : Ainf F)).symm rfl
  map_smul' c a := Prod.ext (smul_zero (A := Ainf F) c).symm rfl

def pairE (a : Ainf F ⊗[F] E) (b : Af F ⊗[F] E) : AF F ⊗[F] E :=
  TensorProduct.map (inlA (F := F)) LinearMap.id a + TensorProduct.map (inrA (F := F)) LinearMap.id b

theorem pairE_eta (z : AF F ⊗[F] E) :
    pairE (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) = z := by
  unfold pairE
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, AlgHom.id_apply, ← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero (fstA F a)) (zero_add (sndA F a))
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, add_add_add_comm, ha, hb]

theorem fst_pairE (a : Ainf F ⊗[F] E) (b : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairE a b) = a := by
  unfold pairE
  have h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (TensorProduct.map (inlA (F := F)) LinearMap.id a) = a := by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x e => rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have h2 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (TensorProduct.map (inrA (F := F)) LinearMap.id b) = 0 := by
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x e =>
      rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      exact TensorProduct.zero_tmul _ _
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  rw [map_add, h1, h2, add_zero]

theorem snd_pairE (a : Ainf F ⊗[F] E) (b : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (pairE a b) = b := by
  unfold pairE
  have h1 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (TensorProduct.map (inlA (F := F)) LinearMap.id a) = 0 := by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x e =>
      rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      exact TensorProduct.zero_tmul _ _
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (TensorProduct.map (inrA (F := F)) LinearMap.id b) = b := by
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x e => rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [map_add, h1, h2, zero_add]

end Emb

section Raw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (cm : CMData F E) {T : Type} [Fintype T] (emb : T → E →+* ℂ) (cd : CDHaar)

def IsVolMeasR (W : HSpace E) (μ : Measure (HA (AF F) cm.sig W.gram)) : Prop :=
  μ.IsHaarMeasure ∧
  AllSome (fun θ : T → (Ainf F ⊗[F] E →+* ℂ) => ∀ ρ, IsInfEmb (emb ρ) (θ ρ)) fun θ =>
  AllSome (fun A : ∀ ρ : T, Matrix (Fin (W.sig (emb ρ)).1 ⊕ Fin (W.sig (emb ρ)).2) (Fin W.rank) ℂ =>
    ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (W.sig (emb ρ)).1 (W.sig (emb ρ)).2 * A ρ = W.gram.map (emb ρ)) fun A =>
  ∀ B : ∀ ρ : T, Set (UpqT (W.sig (emb ρ)).1 (W.sig (emb ρ)).2), (∀ ρ, MeasurableSet (B ρ)) →
    μ {h | (∀ y, y ∈ latHat F E {x | ∑ i, x i • W.frame i ∈ W.L0} ↔
          (finMat cm.sig W.gram h).mulVec y ∈ latHat F E {x | ∑ i, x i • W.frame i ∈ W.L0}) ∧
        ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat cm.sig W.gram (θ ρ) h} =
      ∏ ρ, cd.cd (W.sig (emb ρ)).1 (W.sig (emb ρ)).2 (B ρ)

def GoodPairR (V : HSpace E) (p : Measure (HA (AF F) cm.sig V.gram) × Set (HA (AF F) cm.sig V.gram)) : Prop :=
  p.1.IsHaarMeasure ∧ IsFundamentalDomain (HFinIn (AF F) cm.sig V.gram) p.2 p.1 ∧ (V.SigOK → IsVolMeasR cm emb cd V p.1)

open Classical in

def pairR (V : HSpace E) : Measure (HA (AF F) cm.sig V.gram) × Set (HA (AF F) cm.sig V.gram) :=
  if h : ∃ p, GoodPairR cm emb cd V p then h.choose else (0, ∅)

def volR (V : HSpace E) : ℝ := ((pairR cm emb cd V).1 (pairR cm emb cd V).2).toReal

end Raw

variable (D : D7)

abbrev InfF : Type := D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

def th0 : InfF D := fun τ => haveI := D.sp.cm.totReal; projAt (F := D.host.F) (tauE D τ)

theorem theta_infinite_family : IsInfFam (D := D) (th0 D) := fun τ => haveI := D.sp.cm.totReal; projAt_isInfEmb (tauE D τ)

variable {D}

theorem fam_eq {θ : InfF D} (h : IsInfFam (D := D) θ) : θ = th0 D :=
  funext fun τ => isInfEmb_unique _ (h τ) (theta_infinite_family D τ)

theorem allSome_fam {Q : InfF D → Prop} : AllSome (IsInfFam (D := D)) Q ↔ Q (th0 D) :=
  ⟨fun h => h.2 _ (theta_infinite_family D), fun h => ⟨⟨_, theta_infinite_family D⟩, fun _ hθ => fam_eq hθ ▸ h⟩⟩

theorem ae_ext {x y : AE D} (h1 : infPart D x = infPart D y) (h2 : finPart D x = finPart D y) : x = y := by
  have key : ∀ z : AE D, pairE (infPart D z) (finPart D z) = z := fun z => pairE_eta z
  rw [← key x, ← key y, h1, h2]

theorem ga_ext {V : HSp D} {g h : GA D V} (h1 : infHom V g = infHom V h) (h2 : finHom V g = finHom V h) : g = h := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply ae_ext
  · exact congrArg (fun u : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1 i j) h1
  · exact congrArg (fun u : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) => u.1 i j) h2

theorem fin_inf_comm {V : HSp D} {k h : GA D V} (hk : k ∈ GfC V) (hh : h ∈ GinfC V) : k * h = h * k := by
  have a : infHom V k = 1 := hk
  have b : finHom V h = 1 := hh
  apply ga_ext
  · rw [map_mul, map_mul, a, one_mul, mul_one]
  · rw [map_mul, map_mul, b, one_mul, mul_one]

theorem atTau_mem (θ : InfF D) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem _

theorem infMat_mul (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have e : ∀ x : GA D V, infMat D.sp.cm.sig V.gram θ x = ((infHom V x).1).map θ := fun _ => rfl
  rw [e, e, e, map_mul, Units.val_mul, Matrix.map_mul]

theorem infMat_one (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) :
    infMat D.sp.cm.sig V.gram θ 1 = 1 := by
  have e : ∀ x : GA D V, infMat D.sp.cm.sig V.gram θ x = ((infHom V x).1).map θ := fun _ => rfl
  rw [e, map_one, Units.val_one, Matrix.map_one _ (map_zero θ) (map_one θ)]

end Formalism.L2.Fam.ThC

end
