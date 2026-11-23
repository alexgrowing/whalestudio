import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer
open Formalism.L2.SG.PoincareInHH Formalism.L2.SG.PoincareInHH.PoincareSetting
open Formalism.L2.SG.HidaSetting (HidaSetting rv incl)
open Formalism.L2.SG.InstExistsPf (instOf)
open Formalism.L2.SG.RowsJoinPinned (iotaX castGA)
open Formalism.MainNotions.S (AutInst uMat)
open scoped InnerProductSpace TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyTypeUnfolding

variable {D : D7}

def castV {I I' : AutInst} (h : I = I') (x : Fin I.n → I.E) : Fin I'.n → I'.E := h ▸ x

def crdY {I : AutInst} (h : I = instOf D) (x : Fin I.n → I.E) : Fin (D.sp.Y 0).rank → D.host.E := castV h x

theorem fix_of_fix {I : AutInst} (h : I = instOf D) (x : Fin I.n → I.E) (g : GA D (D.sp.Y 0))
    (hg : Formalism.L2.Theta.mt (D.sp.Y 0) g *ᵥ ratV (crdY h x) = ratV (crdY h x)) :
    (∀ v, uMat ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) g).1 v) *ᵥ rv I v x = rv I v x) ∧
      I.fmat (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) g).2 *ᵥ incl I x = incl I x := by
  subst h
  obtain ⟨h1, h2⟩ := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have hs : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  have h1 := fun v => (h1 v).trans (congrArg (fun t => Formalism.L2.SG.AdBridge.ofHAInf (instOf D) t v) hs)
  have h2 := h2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (instOf D)) hs)
  have hg' : Formalism.L2.SG.AdBridge.hmat (instOf D) g *ᵥ (fun i => (1 : AF (instOf D).F) ⊗ₜ[(instOf D).F] x i) =
      fun i => (1 : AF (instOf D).F) ⊗ₜ[(instOf D).F] x i := hg
  have key : ∀ {R : Type} [CommRing R] (t : AF (instOf D).F ⊗[(instOf D).F] (instOf D).E →+* R),
      (Formalism.L2.SG.AdBridge.hmat (instOf D) g).map t *ᵥ (fun i => t ((1 : AF (instOf D).F) ⊗ₜ[(instOf D).F] x i)) =
        fun i => t ((1 : AF (instOf D).F) ⊗ₜ[(instOf D).F] x i) := by
    intro R _ t
    funext i
    have := congrArg t (congrFun hg' i)
    rw [RingHom.map_mulVec] at this
    exact this
  refine ⟨fun v => ?_, ?_⟩
  · change uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) *ᵥ _ = _
    have k := key (Formalism.L2.SG.AdBridge.thetaV (instOf D) v)
    simp only [Formalism.L2.SG.AdBridge.thetaV_tmul, map_one, one_mul] at k
    have hP : (instOf D).P v * ((instOf D).P v)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((instOf D).P_unit v))
    refine (congrArg (· *ᵥ rv (instOf D) v x) (h1 v)).trans ?_
    change (((instOf D).P v)⁻¹ * (Formalism.L2.SG.AdBridge.hmat (instOf D) g).map (Formalism.L2.SG.AdBridge.thetaV (instOf D) v) *
      (instOf D).P v) *ᵥ _ = _
    rw [rv, Matrix.mulVec_mulVec, Matrix.mul_assoc, hP, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, k]
  · change (instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ _ = _
    have k := key (Formalism.L2.SG.AdBridge.tauF (instOf D))
    simp only [Formalism.L2.SG.AdBridge.tauF_tmul] at k
    exact (congrArg (· *ᵥ incl (instOf D) x) h2).trans k

section Frame

variable (X : HidaSetting D) (h : X.B.I = instOf D) (u : D.what₂.Word) {V₀ A L : HSp D}
  (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)

structure IsFrame : Prop where
  e_eq : ∀ a i, d.e i a = crdY h (X.eR a) i
  f_eq : ∀ a i, d.e' i a = crdY h (X.fR a) i
  line : IsLineVec L ζ
  z_eq : d.i₀ *ᵥ vecB o ζ = crdY h (X.zR u)

variable {X h u d o ζ}

theorem embA_fix (hF : IsFrame X h u d o ζ) (a : GA D A) (x : Fin X.B.I.n → X.B.I.E) (hx : x ∈ fixSet X u) :
    Formalism.L2.Theta.mt (D.sp.Y 0) (embA d o a) *ᵥ ratV (crdY h x) = ratV (crdY h x) := by
  rcases hx with (⟨b, rfl⟩ | ⟨b, rfl⟩) | rfl
  · have e : ratV (crdY h (X.eR b)) = fun i => d.jX i b := funext fun i => congrArg (incA D) (hF.e_eq b i).symm
    rw [e]
    exact funext fun i => congrFun (congrFun (d.wittDecomp_anisotropicEmbedding_inclX (o.emb (a, 1))) i) b
  · have e : ratV (crdY h (X.fR b)) = fun i => d.jY i b := funext fun i => congrArg (incA D) (hF.f_eq b i).symm
    rw [e]
    exact funext fun i => congrFun (congrFun (d.wittDecomp_anisotropicEmbedding_inclY (o.emb (a, 1))) i) b
  · have e : Formalism.L2.Theta.mt (D.sp.Y 0) (embA d o a) ⬝ (d.j0 ⬝ o.jB) = d.j0 ⬝ o.jB := by
      rw [embA_apply, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jB, mt_one, Matrix.mul_one]
    rw [← hF.z_eq, vecB, ratV_mulVec, ratV_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact (congrArg (· *ᵥ ratV ζ) ((Matrix.mul_assoc _ _ _).trans e)).trans (Matrix.mulVec_mulVec _ _ _).symm

def toH (hF : IsFrame X h u d o ζ) (a : GA D A) : Hinf X u × Hfin X u :=
  (⟨(iotaX X h (embA d o a)).1, fun v x hx => (fix_of_fix h x _ (embA_fix hF a x hx)).1 v⟩,
   ⟨(iotaX X h (embA d o a)).2, fun x hx => (fix_of_fix h x _ (embA_fix hF a x hx)).2⟩)

def scalForm (hF : IsFrame X h u d o ζ) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (ξ : X.Vpi u) : GA D A → ℂ :=
  fun a => (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (toH hF a)

end Frame

def transl (X : HidaSetting D) (h : X.B.I = instOf D) (u : D.what₂.Word) (f : X.B.I.GA → ℂ) (y : X.B.I.Ginf) :
    GA D (D.sp.Y 0) → ℂ :=
  fun g => f (iotaX X h g * (y, X.xu u))

structure IsConjType (X : HidaSetting D) (f : X.B.I.GA → ℂ) : Prop where
  cont : Continuous f
  bdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
  left : ∀ γ ∈ X.B.I.GFset, ∀ x, f (γ * x) = f x
  right : ∀ κ ∈ X.K2, ∀ x, f (x * (1, κ)) = star (X.chi2 κ) * f x

def thetaS (D : D7) : D.host.E := 1 / ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E)

section Per

variable {X : HidaSetting D} {h : X.B.I = instOf D} {u : D.what₂.Word} {V₀ A L : HSp D}
  {d : HypDec (D.sp.Y 0) V₀ D.R.rS} {o : OrthDec V₀ A L} {ζ : Fin L.rank → D.host.E}
  (hF : IsFrame X h u d o ζ) (hK : X.LevelSubgroupCharacter) (ψ : AddChar (AF D.host.F) ℂ)
  (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (ν : Measure (flagN d)) (𝓝 : Set (flagN d))
  (T : Cu X u hK) (f : X.B.I.GA → ℂ)

def perFun (y : X.B.I.Ginf) : GA D A → flagN d → ℂ :=
  besFun ψ (thetaS D) d o ζ (scalForm hF hK T (X.Wu u y)) (transl X h u f y)

def perAt (y : X.B.I.Ginf) : ℂ :=
  besPer ψ (thetaS D) d o ζ μ 𝓕 ν 𝓝 (scalForm hF hK T (X.Wu u y)) (transl X h u f y)

def Unfolds (Dt : Set X.B.I.GA) (c : ℝ) : Prop :=
  (∀ y, AbsConv μ 𝓕 ν 𝓝 (perFun hF hK ψ T f y)) ∧
  Integrable (perAt hF hK ψ μ 𝓕 ν 𝓝 T f) (X.nuQ u) ∧
  (∀ᵐ x ∂((X.B.I.muA X.B.μf).restrict X.B.fund), Summable fun δ : Dt => ‖Ph X u hK T ((δ : X.B.I.GA) * x)‖) ∧
  Integrable (fun x => f x * Pser X u hK Dt T x) ((X.B.I.muA X.B.μf).restrict X.B.fund) ∧
  ∫ x in X.B.fund, f x * Pser X u hK Dt T x ∂(X.B.I.muA X.B.μf) =
    (c : ℂ) * ∫ y, perAt hF hK ψ μ 𝓕 ν 𝓝 T f y ∂(X.nuQ u) ∧
  (MemLp (Pser X u hK Dt T) 2 ((X.B.I.muA X.B.μf).restrict X.B.fund) →
    ∀ φ : X.B.I.L2 X.B.μf X.B.fund, (φ : X.B.I.GA → ℂ) =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] (fun x => star (f x)) →
      ⟪φ, PuFun X u hK Dt T⟫_ℂ = (c : ℂ) * ∫ y, perAt hF hK ψ μ 𝓕 ν 𝓝 T f y ∂(X.nuQ u))

end Per

def Stmt : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = instOf D) (hK : X.LevelSubgroupCharacter)
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (u : D.what₂.Word) (V₀ A L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L)
      (ζ : Fin L.rank → D.host.E) (hF : IsFrame X h u d o ζ)
      (μ : Measure (GA D A)) (ν : Measure (flagN d)), μ.IsHaarMeasure → ν.IsHaarMeasure →
      ∃ c : ℝ, 0 < c ∧
        ∀ (𝓕 : Set (GA D A)) (𝓝 : Set (flagN d)), IsFundamentalDomain (GQ A) 𝓕 μ →
          IsFundamentalDomain (NFlagQ (D.sp.Y 0) d.e) 𝓝 ν →
          ∀ Dt : Set X.B.I.GA, IsReps X u Dt →
            ∀ (T : Cu X u hK) (f : X.B.I.GA → ℂ), IsConjType X f → Unfolds hF hK ψ μ 𝓕 ν 𝓝 T f Dt c

example (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (Dt : Set X.B.I.GA) (T : Cu X u hK) (f : X.B.I.GA → ℂ)
    (hm : MemLp (Pser X u hK Dt T) 2 ((X.B.I.muA X.B.μf).restrict X.B.fund)) (φ : X.B.I.L2 X.B.μf X.B.fund)
    (hφ : (φ : X.B.I.GA → ℂ) =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] (fun x => star (f x))) :
    ⟪φ, PuFun X u hK Dt T⟫_ℂ = ∫ x in X.B.fund, f x * Pser X u hK Dt T x ∂(X.B.I.muA X.B.μf) := by
  have e : PuFun X u hK Dt T = hm.toLp _ := dif_pos hm
  rw [e, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hφ, hm.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

example {X : HidaSetting D} {h : X.B.I = instOf D} {u : D.what₂.Word} {V₀ A L : HSp D} {d : HypDec (D.sp.Y 0) V₀ D.R.rS}
    {o : OrthDec V₀ A L} {ζ : Fin L.rank → D.host.E} (hF : IsFrame X h u d o ζ) : toH hF 1 = 1 := by
  have e : iotaX X h (embA d o 1) = 1 := by rw [map_one, map_one]
  exact Prod.ext (Subtype.ext (congrArg Prod.fst e)) (Subtype.ext (congrArg Prod.snd e))

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyTypeUnfolding

end
