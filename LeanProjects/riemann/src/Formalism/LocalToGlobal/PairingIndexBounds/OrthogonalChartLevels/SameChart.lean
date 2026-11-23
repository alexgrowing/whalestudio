import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.UnitOfBr
import Formalism.LocalToGlobal.HermitianColumns.ZeroPointScaledByCharacter
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosCompatOfBase
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.G.Cmp
open Formalism.L2.Col Formalism.HermitianLatticesTheory
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (hg : ∀ a, D.host.g a ≠ 0)
  (hpg : ∀ a, Nat.Coprime p (D.host.g a))
  (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
  (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ (D.mem u).A.T D.R.f (i + 1))
  (Ch : Chain (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k)
  (hfin : ∀ j c', ((levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx).lev j c').FinClasses)

variable (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1) → Formalism.L2.Col.HomE D.host.E
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def OrthTie : Prop :=
  (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 co) ∧
    ∀ i, i < D.R.m → ∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram co

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def ATie : Prop :=
  compan (sp := D.sp) D.sp.gram0 a Lc.Lb = D.sp.crdLat0 (D.sp.X 0).L0 ∧
    ∀ (i : ℕ) (hi : i < D.R.m) (β : Cb i hi), compan (sp := D.sp) (D.sp.X (i + 1)).gram a (Sx i hi β).lev.Lb =
      Formalism.L2.Herm.crdLat (D.sp.X (i + 1)) (D.sp.X (i + 1)).L0

def MuTie (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) : Prop :=
  ∀ j, muT j 1 = 1 ∧ (∀ x y, muT j (x * y) = muT j x * muT j y) ∧ ∀ x, muT j x ≠ 0 ∧ muT j x ∈ TaylorLogMetric.Qbar

def ChiTie (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  TaylorLogMetric.IsChi D χ ∧ ∀ 𝔞, χ 𝔞 ≠ 0 ∧ χ 𝔞 ∈ TaylorLogMetric.Qbar

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def baseComp : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → Submodule (𝓞 D.host.E) (Fin (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1) → D.host.E)
  | 0, _ => (compan (sp := D.sp) D.sp.gram0 a Lc.Lb).map
      (((reE (E := D.host.E) (n := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj 0).m + 1) (by exact (k_pred D.R).symm) : _ ≃ₗ[D.host.E] _) : _ →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))
  | i + 1, La => (compan (sp := D.sp) (D.sp.X (i + 1)).gram a (Sx i La.1.1 La.1.2.1).lev.Lb).map
      (((reE (E := D.host.E) (n := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (i + 1)).m + 1) (by exact (rank_step D i La.1.1).symm) : _ ≃ₗ[D.host.E] _) :
        _ →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def sameChart : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → Prop
  | 0, _, _ => True
  | _ + 1, La, Lb => La.1.2.1 = Lb.1.2.1

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def XiInv : Prop :=
  ∀ j (La : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j) (La' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1)) (x m : HomE D.host.E (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1) (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1)),
    (∀ P ∈ SS, ((cl : D.host.E)⁻¹ • m) ∈ localization₂ (W := HomE D.host.E (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1) (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1)) P.asIdeal
      (homO (E := D.host.E) (a := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1) (b := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) (baseComp D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a j La)
        (baseComp D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a (j + 1) La'))) →
    Ξ₀ j La La' (x + m) = Ξ₀ j La La' x

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def XiLat : Prop :=
  ∀ j, j < D.R.m → ∀ (La : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j) (La' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1)),
    ∃ x ∈ homO (E := D.host.E) (a := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1) (b := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) (baseComp D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a j La)
      (baseComp D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a (j + 1) La'), Ξ₀ j La La' x ≠ 0

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def XiChart : Prop :=
  ∀ j (La Lb : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j) (La' Lb' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1)),
    sameChart D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin j La Lb →
    sameChart D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin (j + 1) La' Lb' → Ξ₀ j La La' = Ξ₀ j Lb Lb'

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def LamPos : Prop :=
  ∀ (τ : D.what₂.Tau) (x : D.host.E) (hx : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar),
    lam ⟨TaylorLogMetric.embT D τ x, hx⟩ =
      twC D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1 ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).2
        ((I.eQ ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1).symm
          (fstV I ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1 (inclE (F := D.host.F) (((I.plc ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1)).adicCompletion D.host.F)
            (if IsOddPos ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).2 then D.host.conj x else x))))

def DeltaTie (_B : Base D cc δ) : Prop := TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ

def GTie (g : Formalism.MainNotions.GL3Theta.G1 p) : Prop := g.Ok ∧ g.lam = lam ∧ g.abelian₂ = TaylorLogMetric.lamOf D cc δ

def BadTie : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∈ bad ↔
    (((D.mem u).A.T : 𝓞 D.host.F) ∈ v.asIdeal ∨ (D.host.g 0 : 𝓞 D.host.F) ∈ v.asIdeal ∨ (D.host.g 1 : 𝓞 D.host.F) ∈ v.asIdeal)

def SSTie (a : 𝓞 D.host.E) : Prop :=
  (∀ P ∈ SS, ∃ v ∈ bad, P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) ∧
    (∀ v ∈ bad, ∃! P, P ∈ SS ∧ P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) ∧
    ∀ P ∈ SS, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → a ∉ P.asIdeal

def PosRec : Prop :=
  Formalism.L2.G.PosCompat D.host h ((extOf p (orderOf (zPsi D.R.toFrame h)) L).φK.comp (iota p (orderOf (zPsi D.R.toFrame h))))
    (sig p (orderOf (zPsi D.R.toFrame h))) I.iw (cembL D u h L h5 h2 he r Lc I ψ e).iK lam

def DataAway : Prop :=
  Formalism.L2.KerInert.RepRec.ClAway p cl ∧ Formalism.L2.KerInert.RepRec.XiAway (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin) D Ξ₀

def TiedF (g : Formalism.MainNotions.GL3Theta.G1 p) : Prop :=
  OrthTie D ∧ ATie D u h L Lc I Cb Sx a ∧ MuTie D muT ∧ ChiTie D χ ∧
    XiInv D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a SS cl Ξ₀ ∧
    XiLat D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a Ξ₀ ∧
    XiChart D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin Ξ₀ ∧
    PosRec D u h L h5 h2 he r Lc I ψ e lam ∧ DeltaTie D B ∧ GTie D (cc := cc) (δ := δ) lam g ∧
    BadTie D u bad ∧ SSTie D u bad SS a ∧
    DataAway D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin cl Ξ₀ ∧
    BRAt D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad χ lam muT

end Formalism.L2.PairingIndexBounds.F
