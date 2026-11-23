import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.KeepsOfGood

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.BadRep

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.BadCount
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed typeEmb grpHR grpGHR transl levelGU)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU unitri superDiag)
open GlobalTheory.LevPull (CongMod)
open Formalism.MainNotions.ArithmeticCylinders
open scoped TensorProduct

section Mid

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

set_option maxHeartbeats 1000000 in

theorem rank_cover {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (fw : FWTie T R κ v₀) (Fc : Face D A) (i : Fin D.R.m) (Y : Deep T.toCore ((i : ℕ) + 1)) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
    (hact : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c
      (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))))
    (hρ : ActRho R i (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) (fw.e i) (actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c
      (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)))))
    (θ : LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂ →* G) (h1 : ∀ γ, CongMod T.Q.l.Mb (liftLa γ) (lev (θ γ)))
    (h2 : ∀ γ, CongMod T.Q.l.Mb (liftLa γ) LinearMap.id → θ γ = 1) {G' : Type} [Group G']
    (c : G ≃* G') (s : G' →* LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂) (hs : ∀ g, θ (s (c g)) = g)
    (Q : Subgroup (LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂))
    (hQ : ∀ γ, γ ∈ Q ↔ θ γ ∈ (Fc.lvl false).P) (lamb : Q →* ℂˣ)
    (hlam : ∀ γ : Q, ((lamb γ : ℂˣ) : ℂ) =
      D.what₂.embLL (((Fc.lvl false).ψ⁻¹ ⟨θ γ, (hQ _).1 γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL))
    (e0 : MonoidAlgebra ℂ G') (he : ∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = e0.coeff (c g)) :
    ∃ (ρ : Representation ℂ (LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (wtZ (wtA (κ i)) (κ i).n)))
      (χ : (LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂) →* ℂˣ),
      (∀ (g : (LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂)) (v w : Y.V (wtZ (wtA (κ i)) (κ i).n)),
        (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v →
        ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧
      Formalism.HN.rkK (latType R Fc i) = Module.finrank ℂ (eig ρ Q lamb) ∧
      Formalism.HN.rkK (CovTop.latBad R Fc i) = Module.finrank ℂ (eig ρ Q lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom
          (ρ.comp s : Representation ℂ G' (ℂ ⊗[Y.d.c₂.F] Y.V (wtZ (wtA (κ i)) (κ i).n))) e0) :
          Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (wtZ (wtA (κ i)) (κ i).n))) := by
  have hk : ∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c
      (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) g f ∈
        T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := fun g f hf => by
    obtain ⟨h, -⟩ := hρ g ⟨f, hf⟩
    exact h
  have hI : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, i.2⟩
  have hC : cuspW (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) =
      T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := cuspW_wtZ _ _
  have hj : ∀ a, algebraMap Y.d.c₂.F ℂ (((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)) a) = T.σ₀ a :=
    fun a => rfl
  have H := rep_data fw.laws hI Y hY (dom_wtA (κ i)) lev hact hk θ h1 h2
  refine H.elim fun π h => h.elim fun τ a => ?_
  have H' := rank_gen fw Fc i _ hρ hC hj π τ θ a.2.1 a.2.2.1 a.2.2.2 c s hs Q hQ lamb hlam e0 he
  refine H'.imp fun ρ h' => h'.imp fun χ b => ⟨fun g v w hw => ?_, b.2⟩
  rw [b.1, show τ g v = w from Subtype.ext ((a.1 g v).trans hw.symm)]

end Mid

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

set_option maxHeartbeats 1000000 in

theorem rank_data (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    (θ : LevelAut (dat p i) Y.d.l₂ →* p.P.Gp) (h1 : ∀ γ, CongMod p.T.Q.l.Mb (liftLa γ) ((p.O i).lev (θ γ)))
    (h2 : ∀ γ, CongMod p.T.Q.l.Mb (liftLa γ) LinearMap.id → θ γ = 1) {G' : Type} [Group G'] (c : p.P.Gp ≃* G')
    (s : G' →* LevelAut (dat p i) Y.d.l₂) (hs : ∀ g, θ (s (c g)) = g) (Q : Subgroup (LevelAut (dat p i) Y.d.l₂))
    (hQ : ∀ γ, γ ∈ Q ↔ θ γ ∈ (p.F.lv2.lvl false).P) (lamb : Q →* ℂˣ)
    (hlam : ∀ γ : Q, ((lamb γ : ℂˣ) : ℂ) =
      D.what₂.embLL (((p.F.lv2.lvl false).ψ⁻¹ ⟨θ γ, (hQ _).1 γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL))
    (e0 : MonoidAlgebra ℂ G') (he : ∀ g, D.what₂.embLL ((idemOf p.P.A3.A.X).coeff g) = e0.coeff (c g)) :
    ∃ (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ),
      (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v →
        ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧
      Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ Q lamb) ∧
      Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ Q lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ G' (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) e0) :
          Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) :=
  rank_cover p.fw p.F.lv2 i Y hY (p.O i).lev (p.pins i).2.act.1 ((p.rhoGeo i).1 fun g =>
    GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev p.T p.κ i _ p.fw.laws (p.pins i).2.act.1 g fun _ => rfl)
    θ h1 h2 c s hs Q hQ lamb hlam e0 he

end Point

end GlobalTheory.CovTop.BadRep
