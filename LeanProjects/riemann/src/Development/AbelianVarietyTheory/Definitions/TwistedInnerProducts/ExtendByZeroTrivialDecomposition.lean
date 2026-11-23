import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AscInh

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def besOfLev {ρ : ℕ} (B : BesLev D ρ) : BesL D ρ := ⟨_, _, _, _, B.d, B.o, B.ζ, B.line, B.vA, B.vN⟩

def jacOfLev {ρ : ℕ} (J : JacLev D ρ) : JacL D ρ := ⟨_, _, J.d, J.v0, J.vN⟩

abbrev besOf {V V₀ A L : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)
    (h : IsLineVec L ζ) : BesL D ρ :=
  ⟨V, V₀, A, L, d, o, ζ, h, (Inhab.nonempty_vol A).some, (Inhab.nonempty_volN d).some⟩

abbrev jacOf {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : JacL D ρ :=
  ⟨W, W₀, d, (Inhab.nonempty_vol W₀).some, (Inhab.nonempty_volN d).some⟩

def lnkScale (L : HSp D) (ζ ζ' : Fin L.rank → D.host.E) (h : ζ = (-D.host.xi0) • ζ') : Lnk L ζ L ζ' where
  τ := D.host.xi0 • (1 : Matrix (Fin L.rank) (Fin L.rank) D.host.E)
  map := by rw [h, Matrix.smul_mulVec, Matrix.one_mulVec, neg_smul, neg_neg]
  norm := by
    rw [h, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, star_neg]; ring

abbrev stdLat (S T : HSp D) : AddSubgroup (WO S T) :=
  latO S T (GlobalTheory.PlaceModel.latFrame S : Set _) (GlobalTheory.PlaceModel.latFrame T : Set _) fun _ => True

theorem stab_compact_open (W : HSp D) (β : GL (Fin W.rank) (Lev.EAf D)) :
    IsCompact (Lev.levA W (Formalism.L2.DIV.St β) : Set (GA D W)) ∧
      IsOpen (((Lev.levA W (Formalism.L2.DIV.St β)).subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig W.gram
  have ho : IsOpen (((Formalism.L2.DIV.St β).comap (Lev.finE W) : Subgroup (GA D W)) : Set (GA D W)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ W β ∅] with κ hh
    exact hh.2.1
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact W β
  refine ⟨hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC W).inter (Subgroup.isClosed_of_isOpen _ ho))
    fun k hk => hCm k hk.1 hk.2, ?_⟩
  convert ho.preimage (continuous_subtype_val (p := fun x => x ∈ GfC W)) using 1
  ext k
  exact ⟨fun hk => hk.2, fun hk => ⟨k.2, hk⟩⟩

theorem isHalf_mul {k l m : ℕ} {e : AE D} (p : Mx D k l) {u : Mx D l m} (hu : IsHalf e u) : IsHalf e (p ⬝ u) := by
  intro i j
  show e * ∑ r, p i r * u r j = ∑ r, p i r * u r j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [mul_left_comm, hu r j]

theorem gram_mul {n k l k' l' : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin k) D.host.E)
    (b : Matrix (Fin n) (Fin l) D.host.E) (u : Matrix (Fin k) (Fin k') D.host.E) (v : Matrix (Fin l) (Fin l') D.host.E) :
    (a * u)ᴴ * M * (b * v) = uᴴ * (aᴴ * M * b) * v := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

def rescale {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : Fin ρ → D.host.E) (hc : ∀ p, c p ≠ 0) : HypDec S S₀ ρ where
  e := d.e * diagonal c
  e' := d.e' * diagonal fun p => (star (c p))⁻¹
  i₀ := d.i₀
  ee := by rw [gram_mul, d.ee, Matrix.mul_zero, Matrix.zero_mul]
  e'e' := by rw [gram_mul, d.e'e', Matrix.mul_zero, Matrix.zero_mul]
  e'e := by
    rw [gram_mul, d.e'e, Matrix.mul_one, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext p
    rw [Pi.star_apply, star_inv₀, star_star, inv_mul_cancel₀ (hc p)]
  iso := d.iso
  i₀e := by rw [← Matrix.mul_assoc, d.i₀e, Matrix.zero_mul]
  i₀e' := by rw [← Matrix.mul_assoc, d.i₀e', Matrix.zero_mul]
  rank_add := d.rank_add

abbrev pLine (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

def lineDec {A B : HSp D} (d : HermitianOrthogonalExtensionData A B 1 1) : OrthDec B A (pLine D) where
  iA := frameMat B A d.ι
  iB := d.a
  isoA := GlobalTheory.RowUnf.frameMat_isom d
  isoB := by
    refine d.gram.trans (Matrix.ext fun i j => ?_)
    refine Eq.trans ?_ (neg_injective (GlobalTheory.RowUnf.nLine_gram (D := D) i j)).symm
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    rfl
  orth := GlobalTheory.RowUnf.perp_sub' d id
  rank_add := d.rank

theorem xiPow_ne (D : D7) (n : ℕ) : (-D.host.xi0) ^ n ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (Inhab.cmHost_imaginaryGenerator_ne_zero D))

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def besselWittDecomposition (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) :
    HypDec (G.V (.grid (2 * ρ + 2) 0)) (GlobalTheory.Doubling.hsum (G.V (.core (2 * ρ + 2))) (negSp (pLine D))) ρ :=
  rescale (GlobalTheory.RowUnf.besDec (G.colDec (2 * ρ + 2) (by omega) h) (by omega)) (fun p => (-D.host.xi0) ^ (p.1 + 1)) fun _ => xiPow_ne D _

def jacobiWittDecomposition (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) : HypDec (G.V (.grid (2 * ρ + 1) 0)) (G.V (.core (2 * ρ + 1))) ρ :=
  rescale (GlobalTheory.RowUnf.jacDec (G.colDec (2 * ρ + 1) (by omega) (by omega)) (by omega)) (fun p => (-D.host.xi0) ^ (p.1 + 1))
    fun _ => xiPow_ne D _

def auxiliaryFrames : Frames G where
  Lz := pLine D
  rk := rfl
  oz := lineDec G.sp.dec0
  ζ ρ := fun _ => (-D.host.xi0) ^ ρ
  line ρ := GlobalTheory.SeeSaw.Model.isLineVec_nLine (xiPow_ne D ρ)
  lnk ρ := lnkScale _ _ _ (funext fun _ => pow_succ' _ _)
  V₀ ρ := GlobalTheory.Doubling.hsum (G.V (.core (2 * ρ + 2))) (negSp (pLine D))
  dB := besselWittDecomposition G
  oB ρ _ := GlobalTheory.OrthSumExists.orthDecHsum D _ _
  nB ρ h := (Inhab.nonempty_volN (besselWittDecomposition G ρ h)).some
  dJ := jacobiWittDecomposition G
  nJ ρ h := (Inhab.nonempty_volN (jacobiWittDecomposition G ρ h)).some

end GlobalTheory.AscInh

end
