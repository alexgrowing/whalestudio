import Mathlib
import Formalism.LocalToGlobal.HermitianForms.ExtraSym
import Formalism.LocalToGlobal.HermitianForms.TiedTwSym
import Formalism.LocalToGlobal.HermitianForms.TiedBr
import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.LocalToGlobal.KernelLattices.KerChTie
import Formalism.LocalToGlobal.KernelLattices.KerMemPin
import Formalism.LocalToGlobal.KernelLattices.KerMtPin
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists

noncomputable section

namespace GlobalTheory.Core.Cls

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 NumberField IsDedekindDomain Matrix Formalism.UG

def LowerTie {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : Forms.FormsTiedSym D u Ch chOf) : Prop :=
  IsUnit (Forms.bZ u Tf.til.z0).det → ∀ (ψ : (D.mem u).P.Wz) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, Tf.eWz ψ c s =
      Forms.fnOf _ (Forms.shiftOf (Forms.lamT u D.R.m)) (Forms.mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) →
    Tf.valP.eW ((D.mem u).P.lowerMap ψ) c = Forms.fnOf _ (Forms.shiftOf (Forms.sgT u)) 1 (Ker.brTen D u P)

def RootsG (D : D7) : Prop :=
  ∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

structure SelC (ex : Extra D L hT Gi Gl K Y cX) : Type 1 where

  host : Host.HostTied D

  real : Theta.RealTied D

  cols : Forms.ColsTiedSym D

  full : Forms.ColsFullS cols

  extra : Forms.ColsExtraTiedS full ex

  cf : Host.CharFrame D

  tp : Host.TupTied D cf ex.nch

  chrVal : Host.ValLL0 D cf

  chrDt : Host.DtTied D cf

  roots : RootsG D

  tw : Forms.SymmetricTwistedColumnsAtPrimes tp cols ex.tw

  emt : Rows.EMtTied D cols tw

  g : G.GroupCompatibilityAll D hT ex.cmp

  herm_eq : g.herm = full.1.to0

  forms_eq : g.forms = fun u => (cols.forms u).to0

  beOn : ∀ u, Ker.BeOnTie D u

  lower : ∀ u, LowerTie (cols.forms u)

  ambMetric : ∀ u, Rk.AmbMetric D u ex.amb

  ambLattice : ∀ u, Rk.AmbLattice D u ex.amb

structure SelB (ex : Extra D L hT Gi Gl K Y cX) : Type 1 extends SelC ex where

  ker : Ker.KerEntTied ex

  crd : ∀ (u : D.what₂.Word) i, i ≤ D.R.m → GL (Fin (D.R.N i)) D.host.E

  crd_gram : ∀ u i (hi : i ≤ D.R.m),
    cT (Forms.sigD D : D.host.E →+* D.host.E) (crd u i hi).1 * (crd u i hi).1 = Forms.gramN D i hi

  crd_lat : ∀ u i (hi : i ≤ D.R.m) (x : Fin (D.R.N i) → D.host.E),
    x ∈ Forms.selfDualLatticeCoords D i hi ↔ ∀ a, ((crd u i hi).1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

  ker_sharp : ∀ μ, (ker.cst μ).sharp = true

  ker_frm : ∀ u μ i (hi : i ≤ D.R.m) (y : (D.chTw u μ).Y i) (τ : D.what₂.Tau),
    (ker.O u μ).frm i y τ = Forms.atInf (Forms.embT D) (crd u i hi).1 τ * (Forms.twYS tw.ch cols.forms u μ i hi y).1 τ

  aaUnit : ker.AAUnit

  unfAll : ker.UnfAll

  adapted : ker.Adapted

  top : ker.TopPinned

  chTie : ker.ChTie

  memSide : ker.MemSideU

  mtTw : ker.MtTwTie

  om : Formalism.L2.GlobalTheoryTheory.OmegaCompatible D ker.δ

def SelBF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), Nonempty (SelB (Fm.ex x hx i))

theorem SelBF.gTiedF {eps : ℝ} {Fm : FamP eps} (h : SelBF Fm) : Formalism.L2.G.GroupCompatibilityFamily Fm :=
  let ⟨x0, h⟩ := h; ⟨x0, fun x hx i h1 => (h x hx h1 i).elim fun s => ⟨s.g⟩⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SelC.Joints {ex : Extra D L hT Gi Gl K Y cX} (s : SelC ex) : Prop where

  dt : ∀ (x : Herm.unitaryOneFiniteAdeles D.sp.cm) (a : Neutral.B1.Ideles D.host.E), GlobalTheory.Mem.Col2.IsDetLift D.sp.cm x.1 a →
    s.full.1.base.dt x = s.chrDt.eDt a

  piBar : ∀ k : Fin 2, ∃ y : 𝓞 D.host.K,
    ((y : D.host.K) : D.host.E) = Forms.sigD D ((s.cols.forms D.u₀).gl.piG k : D.host.E) ∧ y ∈ (s.cf.P.pb k).asIdeal

  om : ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g k : 𝓞 D.host.F) ∈ v.asIdeal) (a n : ℕ)
    (hn : n.Coprime (D.host.g k)), a < D.R.m →
    (s.cols.forms D.u₀).gl.chiB k v h a (n : Forms.kv D.host.F v) =
      ((s.cf.W.om k (ZMod.unitOfCoprime n hn) ^ (2 * (a + 1)) : ℂˣ) : ℂ)

  psiG : ∀ ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ, Theta.IsStdChar D ψ (-1) →
    ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g k : 𝓞 D.host.F) ∈ v.asIdeal)
    (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), Theta.IsPlaceIdem D v ε → ∀ c y : 𝓞 D.host.F,
    Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (c : D.host.F) -
        (s.cols.forms D.u₀).gl.phi k v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) D.host.xi0)) < 1 →
    ∀ z : v.adicCompletionIntegers D.host.F,
      (z : v.adicCompletion D.host.F) = algebraMap D.host.F (v.adicCompletion D.host.F) (y : D.host.F) →
      (s.cols.forms D.u₀).gl.psi0 k v h (IsLocalRing.residue _ z) =
        ψ (ε * algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ((c : D.host.F) * (y : D.host.F) / (D.host.g k : D.host.F)))

  qp : ∀ μ p, p ∈ Y.Qp μ ↔ p.Prime ∧ ∃ w, Host.OverP D.host p w ∧ ¬ (s.tp.xi μ).UnrAt w

structure SelB.Joints {ex : Extra D L hT Gi Gl K Y cX} (s : SelB ex) : Prop extends s.toSelC.Joints where

  mu0 : ∀ j : Fin D.R.m, s.ker.glob.mu0 j = Host.CT.transport s.ker.seam.iE (s.cf.mu0 j)

  gside : ∀ (i : Fin 2) (P' : HeightOneSpectrum (𝓞 D.host.E)),
    (∃ P ∈ s.ker.Pr.vG i, P'.asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.ker.seam.iE)) ↔ s.cf.P.Div i P'

  tup : ∀ μ : D.what₂.Tup, GlobalTheory.Mem.Col2.Reads s.ker.seam.σ₀ (s.ker.tup μ : DIV.Chr s.ker.X.F s.ker.X.E s.ker.X.K)
    (Host.CT.transport s.ker.seam.iE (s.tp.xi μ))

  sel : Col.IsSel s.ker.X s.ker.sel

structure SelBJ (ex : Extra D L hT Gi Gl K Y cX) : Type 1 extends SelB ex where

  joints : toSelB.Joints

def SelBJF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), Nonempty (SelBJ (Fm.ex x hx i))

theorem SelBJF.selBF {eps : ℝ} {Fm : FamP eps} (h : SelBJF Fm) : SelBF Fm :=
  let ⟨x0, h⟩ := h; ⟨x0, fun x hx h1 i => (h x hx h1 i).elim fun s => ⟨s.toSelB⟩⟩

variable {ex : Extra D L hT Gi Gl K Y cX}

theorem SelC.Joints.sig_piG_mem {s : SelC ex} (J : s.Joints) (k : Fin 2) :
    Forms.sigD D ((s.cols.forms D.u₀).gl.piG k : D.host.E) ∈ D.host.K := by
  obtain ⟨y, hy, -⟩ := J.piBar k
  rw [← hy]
  exact (y : D.host.K).2

theorem SelC.Joints.not_mem_primes_referenceTuple {s : SelC ex} (J : s.Joints) (p : ℕ) : p ∉ Y.Qp D.what₂.mu0 := fun h => by
  obtain ⟨-, w, -, hw⟩ := (J.qp _ p).1 h
  rw [s.tp.trueColumnChoices_heckeChar_reference_eq_one] at hw
  exact hw fun _ _ => rfl

theorem SelB.Joints.heckeChar_isUnitary_of_joints {s : SelB ex} (J : s.Joints) (j : Fin D.R.m) : (s.ker.glob.mu0 j).IsUnitary :=
  J.mu0 j ▸ Host.CT.transport_isUnitary _ _ (s.cf.isMu0 j).unitary

theorem SelB.Joints.trueColumn_tuple_trivial_eq_one {s : SelB ex} (J : s.Joints) : s.ker.tup D.what₂.mu0 = 1 := by
  have h := J.tup D.what₂.mu0
  rw [s.tp.trueColumnChoices_heckeChar_reference_eq_one, map_one] at h
  exact Subtype.ext (h.inj (GlobalTheory.Mem.Col2.reads_one _))

theorem SelB.Joints.transport_xi_eq {s : SelB ex} (J : s.Joints) {μ μ' : D.what₂.Tup} (h : s.ker.tup μ = s.ker.tup μ') :
    Host.CT.transport s.ker.seam.iE (s.tp.xi μ) = Host.CT.transport s.ker.seam.iE (s.tp.xi μ') :=
  (J.tup μ).unique (h ▸ J.tup μ')

theorem SelB.Joints.div_plMap {s : SelB ex} (J : s.Joints) {i : Fin 2} {P : HeightOneSpectrum (𝓞 s.ker.X.E)} (h : P ∈ s.ker.Pr.vG i) :
    s.cf.P.Div i (Host.CT.plMap s.ker.seam.iE P) :=
  (J.gside i _).1 ⟨P, h, Host.CT.asIdeal_plMap _ P⟩

example {s : SelC ex} (J : s.Joints) (k : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g k : 𝓞 D.host.F) ∈ v.asIdeal)
    (n : ℕ) (hn : n.Coprime (D.host.g k)) :
    (s.cols.forms D.u₀).gl.chiB k v h 0 (n : Forms.kv D.host.F v) = ((s.cf.W.om k (ZMod.unitOfCoprime n hn) ^ 2 : ℂˣ) : ℂ) :=
  J.om k v h 0 n hn (by have := D.R.two_le_m; omega)

example (s : SelB ex) (h : s.ker.tup D.what₂.mu0 ≠ 1) : ¬ s.Joints := fun J => h J.trueColumn_tuple_trivial_eq_one

example {s : SelB ex} (J : s.Joints) {i : Fin 2} {P : HeightOneSpectrum (𝓞 s.ker.X.E)} (h : P ∈ s.ker.Pr.vG i) (j : Fin D.R.m)
    (a : ℕ) (ha : a.Coprime (D.host.g i)) (x : D.host.Eˣ) (hx : (x : D.host.E) = (a : D.host.E)) :
    (s.cf.mu0 j).locK (Host.CT.plMap s.ker.seam.iE P) x = (s.cf.W.om i (ZMod.unitOfCoprime a ha) ^ (2 * (j.1 + 1)))⁻¹ :=
  (s.cf.isMu0 j).atg i _ (J.div_plMap h) a ha x hx

end GlobalTheory.Core.Cls

end
