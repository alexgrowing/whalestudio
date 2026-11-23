import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ring

variable {l : ℕ} [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))

abbrev intR : Type := integralClosure ℤ_[l] Lf

def intEmb : intR Lf →+* PadicAlgCl l := Lf.val.toRingHom.comp (algebraMap (integralClosure ℤ_[l] Lf) Lf)

end Ring

section Adeles

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]

def EvOk (i : E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l) : Prop :=
  (∀ x, ev (1 ⊗ₜ[F] x) = i x) ∧
    (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ‖ev (a ⊗ₜ[F] 1)‖ ≤ 1) ∧
    (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → a v = 0) → ev (a ⊗ₜ[F] 1) = 0) ∧
    ∀ y, ev y ∈ IntermediateField.adjoin ℚ_[l] (Set.range i)

end Adeles

def incOf (D : D7) {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (τ : D.what₂.Tau) :
    D.host.E →+* PadicAlgCl l :=
  cond b (cj (e0.comp (labLL D τ))) (e0.comp (labLL D τ))

def HalfAt (D : D7) (l : ℕ) : Prop := ∀ [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool), IsHalf (incOf D e0 b)

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def Ix (j : Fin D.R.m) (t : p.P.T) (l N : ℕ) : Type :=
  {i : (blk p j t).Pl × ℕ // 1 ≤ i.2 ∧ i.2 ≤ N ∧ ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t i.1).asIdeal}

def frameOf (j : Fin D.R.m) (t : p.P.T) (l : ℕ) [Fact l.Prime] (N : ℕ) (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] Lf] (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j t →* (intR Lf)ˣ) :
    Frame l D.what₂.Tau N where
  O := intR Lf
  emb := intEmb Lf
  G := Bridge.Gf (Vc D j)
  Γ := (Bridge.ratF (Vc D j)).range
  K := levJ p j t
  kap := kap
  chi := chi
  I := Ix p j t l N
  tr i := hkA p j t i.1
  cst _ := 1

def kapMat (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (κ : levJ p j t) (τ : D.what₂.Tau) :
    Matrix (Fin N) (Fin N) (PadicAlgCl l) :=
  ((bs τ)⁻¹).val * ((matOf j (κ : Bridge.Gf (Vc D j))).map (ev τ)).submatrix rk rk * (bs τ).val

def KapEq (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) {Lf : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) : Prop :=
  ∀ κ τ, (Matrix.GeneralLinearGroup.map (intEmb Lf) (kap κ τ)).val = kapMat p j t ev bs rk κ τ

def ChiEq (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (io : PadicAlgCl l ≃+* ℂ) (sh : D.what₂.Tau → ℤ)
    {Lf : IntermediateField ℚ_[l] (PadicAlgCl l)} (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf)))
    (chi : levJ p j t →* (intR Lf)ˣ) : Prop :=
  ∀ κ, io (intEmb Lf (chi κ) * ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) * ((levChi p j t κ : ℂˣ) : ℂ) = 1

def KapAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (rk : Fin P.Nr ≃o Fin (Vc D j).rank), (∀ x : 𝓞 D.what₂.LL, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1) →
    (∀ τ, EvOk (incOf D e0 b τ) (ev τ)) →
    ∃ bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, bs τ = 1) ∧ ∀ κ τ a c,
      kapMat p j (p.R.mu w) ev bs rk κ τ a c ∈ IntermediateField.adjoin ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (Set.range e0) ∧
        ‖kapMat p j (p.R.mu w) ev bs rk κ τ a c‖ ≤ 1

def ChiAt (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ∀ κ : levJ p j (p.R.mu w), ((levChi p j (p.R.mu w) κ : ℂˣ) : ℂ) ^ M = 1

def ClassesAt (j : Fin D.R.m) (t : p.P.T) : Prop :=
  ∃ S : Finset (Bridge.Gf (Vc D j)), ∀ g, ∃ γ ∈ (Bridge.ratF (Vc D j)).range, ∃ s ∈ S, ∃ κ ∈ levJ p j t, g = γ * s * κ

def TameAt (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ g : Bridge.Gf (Vc D j),
    Finite {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)} ∧
      ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ Nat.card {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)}

def ChoiceOk (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    {Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))}
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ) : Prop :=
  (∀ x : 𝓞 D.what₂.LL, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1) ∧ (∀ x, e0 x ∈ Lf) ∧ (∀ x, io (e0 x) = D.what₂.embLL x) ∧
    (∀ τ, EvOk (incOf D e0 b τ) (ev τ)) ∧ KapEq p j (p.R.mu w) ev bs rk kap ∧ ChiEq p j (p.R.mu w) io sh kap chi

open Classical in

def PermAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi →
    let F := frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi
    ∀ i (κ : F.K), ∃ σ : Equiv.Perm (F.tr i), ∀ s : F.tr i, ∃ κ' : F.K,
      (κ : F.G) * s = σ s * κ' ∧ F.kap κ' = F.kap κ ∧ F.chi κ' = F.chi κ

open Classical in

def CommAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi →
    let F := frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi
    ∀ i i', ∃ σ : F.tr i × F.tr i' ≃ F.tr i' × F.tr i, ∀ x, F.Triv ((((σ x).1 : F.G) * (σ x).2)⁻¹ * ((x.1 : F.G) * x.2))

def ReadsAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime], ∃ (b : Bool) (sh : D.what₂.Tau → ℤ),
    ∀ (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi → (∀ τ, bs τ = 1) →
    ∃ R : Reads (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi) W.lam (blk p j (p.R.mu w)) w,
      R.e0 = e0 ∧ R.ix = Subtype.val

end Point

end GlobalTheory.FrameOf

end
