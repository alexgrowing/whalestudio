import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EvLApply

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Numbers

open Formalism.BasicNotions Formalism.MainNotions
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (conjEmb)

variable (D : D7) (i : Fin D.R.m)

def jp : ℕ := D.R.m - ((i : ℕ) + 1)

def pp : ℕ := (D.R.sigW ((i : ℕ) + 1)).1

theorem pp_add_jp : pp D i + jp D i = D.R.r := by
  have := i.2
  have := D.R.m_add_three_le_k
  simp only [pp, jp, Ranks.sigW, Ranks.r]; omega

def anc : ℕ := D.R.k - 2

def Dn : ℕ := D.R.f * D.R.r.choose 2

def degW {Tau : Type} [Fintype Tau] {N : ℕ} (lam : Tau → Fin N → ℝ) : ℝ :=
  ∏ τ, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (lam τ a - lam τ b)

def entZ {N : ℕ} (v : Fin N → ℝ) (n : ℕ) : ℤ := if h : n < N then ⌊v ⟨n, h⟩⌋ else 0

open Classical in

def wtZ' (lam : D.what₂.Tau → Fin D.R.r → ℝ) : WZ D.host.E := fun x =>
  ∑ t : D.what₂.Tau, ((if x.1 = DV.tauEmb D t ∧ x.2 < pp D i then entZ (lam t) x.2 else 0) +
    if x.1 = conjEmb (DV.tauEmb D t) ∧ x.2 < jp D i then -entZ (lam t) (D.R.r - 1 - x.2) else 0)

end Numbers

section Geo

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure SharpGeo (Q : Par D) (M : ℕ) : Type 1 where
  l : Level Q.H
  c : Coeff l
  Xo : ∀ i : Fin D.R.m, Moduli (Q.Dw ((i : ℕ) + 1)) l
  U : ∀ i (σ : c.F →+* ℂ), Unf (Xo i) c σ D.R.r
  dict : ∀ (i : Fin D.R.m) σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U i σ).X k).Ψ D.R.r

  e : ∀ i, Comp (Xo i) c → Rul (Xo i) c
  gen : ∀ i, GenFrEx (Xo i) c
  pins : Q.Pins
  level : l.M = M ∧ l.A = 1 ∧ l.Mb ≤ Q.l.Mb
  field : Q.c.F ≤ c.F

  comps : ∀ i, Nat.card (Comp (Xo i) c) = Fintype.card (U i c.F.val.toRingHom).Comp
  genT : ∀ i, GenFromTest (Xo i) c (gen i)
  evalWD : ∀ i, EvalWD (K := c.F) (fun S _ _ => FrPt (Xo i) c S) (fun φ y z => FrMap φ y z)
  unf : ∀ i σ, GoodEmb c σ → IsUnf (U i σ)
  unTest : ∀ i σ, GoodEmb c σ → ∀ k x,
    FromTest (K := c.F) (fun S _ _ => FrPt (Xo i) c S) (fun φ y z => FrMap φ y z) ((U i σ).un k x)
  chiTriv : ∀ i σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U i σ).X k).Γ,
    ((U i σ).X k).χ (laU (U i σ) a n k) γ = 1

  dictU : ∀ (i : Fin D.R.m) σ, GoodEmb c σ → ∃ Kf th hr, IsLevelK (D.sp.W ((i : ℕ) + 1)) l.M Kf ∧
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (D.sp.W ((i : ℕ) + 1)) (dict i σ) Kf th hr ∧
    ∀ g τ k, ‖dmin ((U i σ).X (dict i σ g).1).Gm (dict i σ g).2 τ k‖ = 1
  modelW : ∀ (i : Fin D.R.m) σ, GoodEmb c σ → ∃ hr : (D.sp.W ((i : ℕ) + 1)).rank = D.R.r,
    ∀ k, ModelW (D.sp.W ((i : ℕ) + 1)) hr ((U i σ).X k)
  xiAbs : ∀ i σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U i σ).X k).ξ0‖ = xiR D
  finVol : ∀ i : Fin D.R.m, FinVol (D.sp.W ((i : ℕ) + 1))
  ptNe : ∀ i, IntFrNe (Xo i) c (algCls (Xo i) c)
  intAll : ∀ i, IntAll (Xo i) c
  e_sec : ∀ i Z, e i Z ∈ sec (Xo i) c 0 0
  e_val : ∀ i Z, evC (gen i) Z (e i Z) = 1 ∧ ∀ Z', Z' ≠ Z → evC (gen i) Z' (e i Z) = 0

theorem SharpGeo.card_pos {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m) : 0 < Nat.card (Comp (S.Xo i) S.c) := by
  rw [S.comps i]
  exact Fintype.card_pos_iff.mpr ⟨(S.dict i _ 1).1⟩

instance SharpGeo.ne {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m) : Nonempty (Comp (S.Xo i) S.c) :=
  (Nat.card_pos_iff.mp (S.card_pos i)).1

instance SharpGeo.fin {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m) : Fintype (Comp (S.Xo i) S.c) :=
  @Fintype.ofFinite _ (Nat.card_pos_iff.mp (S.card_pos i)).2

variable {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m)

abbrev RW (D : D7) : Type := D.what₂.Tau → Fin D.R.r → ℝ

abbrev Cmp : Type := Comp (S.Xo i) S.c

abbrev latW (lam : RW D) (Z : Cmp S i) : Submodule (𝓞 S.c.F) (Rul (S.Xo i) S.c) :=
  latOn (S.U i) (S.gen i) (wtZ' D i lam) Z

abbrev ipW (lam : RW D) (Z : Cmp S i) :
    (S.c.F →+* ℂ) → Rul (S.Xo i) S.c → Rul (S.Xo i) S.c → ℂ :=
  ipOn (S.U i) (D.sp.W ((i : ℕ) + 1)) (S.dict i) (xiR D) (wtZ' D i lam) (S.e i Z)

def delC (u1 : RW D) (Z : Cmp S i) : ℝ := (delL S.c.F (Dn D) (latW S i u1 Z) (evC (S.gen i) Z) : ℝ)

def htC (u1 : RW D) (Z : Cmp S i) : ℝ := htL S.c.F (Dn D) (latW S i u1 Z) (evC (S.gen i) Z) (ipW S i u1 Z)

def rkC (uT : RW D) (Z : Cmp S i) : ℝ := (rkL S.c.F (latW S i uT Z) : ℝ)

def degC (uT : RW D) (Z : Cmp S i) : ℝ := degL S.c.F (latW S i uT Z) (ipW S i uT Z)

def volC (up : RW D) (Z : Cmp S i) : ℝ := volL (S.U i) (S.gen i) (wtZ' D i up) Z (Dn D)

def delP (up : RW D) : ℝ := volC S i up (Classical.arbitrary _)

structure MbarIn (up : RW D) where
  top : Cmp S i → ℚ → ℝ
  dg : Cmp S i → ℚ → ℝ
  dg_lim : ∀ Z, Tendsto (dg Z) (𝓝[>] 0) (𝓝 (volC S i up Z))
  conv : ∀ Z, ∃ y, Tendsto (fun s => top Z s / (((Dn D : ℝ) + 1) * dg Z s)) (𝓝[>] 0) (𝓝 y)

def slC {up : RW D} (B : MbarIn S i up) (Z : Cmp S i) : ℝ :=
  limUnder (𝓝[>] (0 : ℚ)) fun s => B.top Z s / (((Dn D : ℝ) + 1) * B.dg Z s)

theorem slC_tendsto {up : RW D} (B : MbarIn S i up) (Z : Cmp S i) :
    Tendsto (fun s => B.top Z s / (((Dn D : ℝ) + 1) * B.dg Z s)) (𝓝[>] 0) (𝓝 (slC S i B Z)) :=
  tendsto_nhds_limUnder (B.conv Z)

def rndDown {K : Type} [Field K] (la : HeightOneSpectrum (𝓞 K)) (q : ℕ) (m : ℝ) : ℝ :=
  (⌊(multiplicity la.asIdeal (Ideal.span {((q : ℕ) : 𝓞 K)}) : ℝ) * m⌋ : ℝ) /
    (multiplicity la.asIdeal (Ideal.span {((q : ℕ) : 𝓞 K)}) : ℝ)

structure ELocIn where
  supNu : HeightOneSpectrum (𝓞 S.c.F) → Cmp S i → ℝ
  mEta : HeightOneSpectrum (𝓞 S.c.F) → Cmp S i → ℝ
  fin : {la : HeightOneSpectrum (𝓞 S.c.F) | ∃ (q : ℕ) (Z : Cmp S i), q.Prime ∧ ((q : ℕ) : 𝓞 S.c.F) ∈ la.asIdeal ∧
    0 < supNu la Z - rndDown la q (mEta la Z)}.Finite

def eLa (El : ELocIn S i) (DF : ℝ) (q : ℕ) (la : HeightOneSpectrum (𝓞 S.c.F)) (Z : Cmp S i) : ℝ :=
  if q = D.host.g 0 ∨ q = D.host.g 1 then DF / ((q : ℝ) - 1) + 1
  else El.supNu la Z - rndDown la q (El.mEta la Z)

end Geo

end GlobalTheory.CompanionTheory.Ar.Rec
