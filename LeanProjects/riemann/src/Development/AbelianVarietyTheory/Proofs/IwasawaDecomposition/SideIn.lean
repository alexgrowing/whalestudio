import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

variable {D : D7}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure SideIn (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (c : CoefA V) (j : ℕ) (hr : D.R.r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) : Type 1 where
  G₀ : Type
  [grp : Group G₀]
  [fin : Fintype G₀]
  S : CSD D.what₂.LL
  act : Representation D.what₂.LL G₀ S.Forms
  pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J
    (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ
  tie : Bridge.ActTie (Bridge.ratF V) pres (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q
    (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch act
  eG : G₀ ≃* G0 Pg D.R.r
  P₀ : Subgroup G₀
  ψ₀ : P₀ →* D.what₂.LLˣ
  red : ∀ q : (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (tie.red q) =
    rTup β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))
  lev : levPOf eG D.what₂.embLL P₀ ψ₀ = P0 Pg D.R.r ψ
  c0 : VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ) →ₛₗ[D.what₂.embLL] c.W
  pair : VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ) →ₗ⋆[D.what₂.LL]
    VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ) →ₗ[D.what₂.LL] D.what₂.LL
  del : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) →
    Submodule (𝓞 D.what₂.LL) (VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ))
  map : Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) _)
  coef : Bridge.CoefTie V c.coef pres _ c0 pair (nabAtr (labLL D) _) del
  vals : ∀ k : (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J, ∃ z : 𝓞 D.what₂.LL,
    D.what₂.embLL (z : D.what₂.LL) = ((levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ k : ℂ)

attribute [instance] SideIn.grp SideIn.fin

namespace SideIn

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {c : CoefA V} {j : ℕ} {hr : D.R.r ≤ V.rank}
  {Pg Q : Finset (Pl D.host.E)} {chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ}
  (u : SideIn V β c j hr Pg Q chi xi ψ)

abbrev dim : ℕ := u.S.lvlDim u.act u.P₀ u.ψ₀⁻¹

abbrev nab : Submodule (𝓞 D.what₂.LL) (Fin u.dim → D.what₂.LL) := u.S.lvlNab u.act u.P₀ u.ψ₀⁻¹

def fn (x : Fin u.dim → D.what₂.LL) : Bridge.Gf V → c.W := u.pres.ext (lvlForm u.S u.act u.P₀ u.ψ₀⁻¹ x).1

end SideIn

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure TupIn (μ : D.what₂.Tup) (i : Fin D.R.m) (c : CoefA (Vc D i)) {T : Type} (L : LevCh D T) (t : T)
    (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) : Type 1 where
  u : SideIn (Vc D i) (L.βV i) c ((i : ℕ) + 1) (r_le_V i) L.Pg (L.Q t) (L.chi ((i : ℕ) + 1)) (L.xiR t) ψ
  e : (Fin u.dim → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ ((i : ℕ) + 1)
  li : LinearIndependent ℂ fun a => D.what₂.jMt μ ((i : ℕ) + 1) (e (Pi.single a 1))
  span : Submodule.span ℂ (Set.range fun a => D.what₂.jMt μ ((i : ℕ) + 1) (e (Pi.single a 1))) = ⊤
  lat : OLatTie D.what₂.embLL (D.what₂.MtLat μ ((i : ℕ) + 1)) ((D.what₂.jMt μ ((i : ℕ) + 1)).comp e.toLinearMap) u.nab

structure Good {μ : D.what₂.Tup} (i : Fin D.R.m) (m : MtReal D μ ((i : ℕ) + 1)) (χ : HChar D.host.E) : Prop where
  prod : NG.IsProdLevel m.J
  para : ∀ v ∈ qPl D χ, ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ),
    s.v = v ∧ NG.IsCompAt χ s ξ ∧ NG.LevelPara m.J m.χ s D.R.r ξ
  uni : ∀ (k : Fin 2) (v : D.nd.PlG k) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w = D.naut.plGw k v →
    ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
      (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt χ s ξ ∧
      NG.LevelUni m.J m.χ s D.R.r ψ₀ ξ
  hyp : NG.HypOutside m.J m.χ (gPl D ∪ qPl D χ)
  wt : ∀ (t : D.what₂.Tau) (a : NG.AlgWt D.host.E D.R.nV) (lam : Fin D.R.nV → ℤ),
    m.wt.IsDual a → a.HWAt (embT D t) lam → NG.infOf lam = NG.paramV D.R (D.hc t) i (1 / 2)
  rat : ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ),
    s.v ∉ gPl D ∪ qPl D χ → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ x, ∃ x',
      m.real (D.what₂.jMt μ ((i : ℕ) + 1) x') = NG.tN m.J s ϖ k (m.real (D.what₂.jMt μ ((i : ℕ) + 1) x))
  int : ∀ (w : D.what₂.places.Pl) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ),
    s.v ∉ gPl D ∪ qPl D χ → ¬ s.Above (D.what₂.places.resChar w) → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV →
    ∀ y ∈ (D.what₂.MtLat μ ((i : ℕ) + 1)).gen, ∃ c : D.what₂.Mt μ ((i : ℕ) + 1) → D.what₂.LL, (∀ g, 0 ≤ D.what₂.places.val w (c g)) ∧
      NG.tN m.J s ϖ k (m.real y) = m.real (∑ g ∈ (D.what₂.MtLat μ ((i : ℕ) + 1)).gen, D.what₂.embLL (c g) • g)
  full : (∀ y ∈ (D.what₂.MtLat μ ((i : ℕ) + 1)).gen, y ∈ Set.range (D.what₂.jMt μ ((i : ℕ) + 1))) ∧
    Submodule.span ℂ ((D.what₂.MtLat μ ((i : ℕ) + 1)).gen : Set (D.what₂.Mt μ ((i : ℕ) + 1))) = ⊤

end GlobalTheory.MtIn

end
