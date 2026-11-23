import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

open NumberField Matrix
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsONLatBasis (V : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) : Prop :=
  (∀ a a', ∑ i, ∑ j, star (b i a) * V.gram i j * b j a' = if a = a' then 1 else 0) ∧
    L0c D V = (Submodule.span (𝓞 D.host.E) (Set.range fun a i => b i a) : Set (Fin V.rank → D.host.E))

def realPt (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : WO S T :=
  Matrix.of fun i j => (pairA D.host.F 1 0) ⊗ₜ[D.host.F] X i j

def thetaAt (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (v : WO S T → ℂ) (g : GA D T) (w : WO S T) : ℂ :=
  heisO ψ S T w (om (1, g) v) 0

theorem thetaAt_eq (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (v : WO S T → ℂ) (g : GA D T) (w : WO S T) : thetaAt ψ om v g w = om (1, g) v w := by
  simp [thetaAt, heisO, symplOH, symplO, hO]

section Period

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

def perVec (Wt : UnfAt U k x) (v : Fin r → D.host.E) : Fin Wt.g → ℂ :=
  fun j => perFr (U.X k) x.1 v (relab c σ (Wt.e j).1) (Wt.e j).2

theorem perVec_lat (Wt : UnfAt U k x) (a : (Wt.F.Di (Wt.ik k)).La) :
    perVec Wt (Wt.φ k a : Fin r → D.host.E) = Wt.Pm a := funext fun j => (Wt.pm_eq a j).symm

end Period

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ)
  (hV : T.V ((i : ℕ) + 1) σ = Wc D i)

abbrev dictW : GA D (Wc D i) → Σ k, Frame ((T.U ((i : ℕ) + 1) σ).X k).Ψ D.R.r := castDict hV (T.dict ((i : ℕ) + 1) σ)

abbrev phiW (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  castDict hV (T.phiJ ((i : ℕ) + 1) σ a f)

def FramePin : Prop :=
  ∃ (ph : ℂ) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 ∧ IsONLatBasis (Vc D i) b ∧
    ∀ (h : GA D (Wc D i)), ∀ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ h →
      ∀ (hx : (dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).dom)
        (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt)
        (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z : Fin (Vc D i).rank → Fin Wt.g → ℂ),
        (∀ a, z a = perVec Wt fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
        Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (z a) (z a)) *
            thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (realPt (Vc D i) (Wc D i) X) =
          ph * (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ a, Y.θ (z a)

omit [Algebra T.Q.c.F D.what₂.LL] in

theorem exists_witness (hL : LawsM T.toCore) (hσ : GoodEmb T.Q.c σ) (h : GA D (Wc D i)) :
    ∃ (hx : (dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).dom)
      (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩), Nonempty (UnitAt Wt) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨th, hr, -, hd⟩ := hL.dictU _ hj σ hσ
  have hx := hd.2.2.2.1 (cast (congrArg (GA D) hV.symm) h)
  obtain ⟨Wt⟩ := nonempty_unfAt (hL.unf _ hj σ hσ) _ ⟨_, hx⟩
  exact ⟨hx, Wt, nonempty_unitAt Wt ((hL.muUnit _ hj σ hσ).2.2.2 _)⟩

def GeoHecke (j : ℕ) (𝔓 : Ideal (𝓞 D.host.E)) (p k : ℕ) (s : T.Q.c.F) (f g : T.R j) : Prop :=
  HkRel (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)
    (fun Ω _ _ _ y => hkKer (Xo := T.Q.Xo j) 𝔓 p k Ω y)
    (fun Ω _ _ _ y C z => hkRelFr 𝔓 p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo j) T.Q.c p) Ω y C z) s f g

def IsUnitaryHeckeOperatorSplitPrimeData (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))) : Prop :=
  Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧ p.Prime ∧ (p : 𝓞 D.host.E) ∈ P.asIdeal ∧ ¬ p ∣ T.Q.l.M' ∧
    k ≤ D.R.r ∧ IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc

def muAt (P : Formalism.L2.DIV.Pl D.host.E) : ℂ := (((R.C.mu0 i).val P : ℂˣ) : ℂ)

def ReadsAt (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) : Prop :=
  ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
    IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc → ∀ (cq : T.Q.c.F) (f g : T.R ((i : ℕ) + 1)),
      f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA κ) κ.n → g ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA κ) κ.n →
      GeoHecke T ((i : ℕ) + 1) P.asIdeal p k (hkScal T.Q.c cq P.asIdeal k D.R.nV) f g →
      ∀ h, phiW T i σ hV (wtA κ) g h =
        σ cq * (muAt T R i P)⁻¹ ^ k * ∑ a ∈ Rc, phiW T i σ hV (wtA κ) f (h * a)

def HeckeRead : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.Char F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ →
      ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, FramePin T R i σ hV → ReadsAt T R i σ hV (κ i)

variable {T R i σ hV}

theorem ReadsAt.unitary {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} (H : ReadsAt T R i σ hV κ) {P : Formalism.L2.DIV.Pl D.host.E} {p k : ℕ}
    {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))} (hs : IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc) {f g : T.R ((i : ℕ) + 1)}
    (hf : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA κ) κ.n) (hg : g ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA κ) κ.n)
    (hr : GeoHecke T ((i : ℕ) + 1) P.asIdeal p k (hkScal T.Q.c 1 P.asIdeal k D.R.nV) f g) (h : GA D (Wc D i)) :
    phiW T i σ hV (wtA κ) g h = (muAt T R i P)⁻¹ ^ k * ∑ a ∈ Rc, phiW T i σ hV (wtA κ) f (h * a) := by
  rw [H P p k α Rc hs 1 f g hf hg hr h, map_one, one_mul]

theorem ReadsAt.modulus {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} (H : ReadsAt T R i σ hV κ) {P : Formalism.L2.DIV.Pl D.host.E} {p k : ℕ}
    {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))} (hs : IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc) {f g : T.R ((i : ℕ) + 1)}
    (hf : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA κ) κ.n) (hg : g ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA κ) κ.n)
    (hr : GeoHecke T ((i : ℕ) + 1) P.asIdeal p k
      (hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV) f g) (h : GA D (Wc D i)) :
    phiW T i σ hV (wtA κ) g h =
      (muAt T R i P)⁻¹ ^ k * (Nat.card (kP P) : ℂ)⁻¹ ^ (k * D.R.nV / 2) * ∑ a ∈ Rc, phiW T i σ hV (wtA κ) f (h * a) := by
  rw [H P p k α Rc hs _ f g hf hg hr h, map_pow, map_inv₀, map_natCast, mul_comm ((Nat.card (kP P) : ℂ)⁻¹ ^ _)]

end GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues
