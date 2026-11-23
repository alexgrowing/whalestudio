import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.FinZeta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KerGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {r : ℕ} (N : ℕ) (z : ℂˣ)
    (φ : GL (Fin r) (w.adicCompletion E) → ℂ) : Prop :=
  ∀ ϖ, IsUnifV E w ϖ → ∀ (d : Fin r → ℤ) (t : GL (Fin r) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
    ∀ k₁ ∈ KGL w r, ∀ k₂ ∈ KGL w r,
      φ (k₁ * t * k₂) = (z : ℂ) ^ (∑ i, d i) * (qV E w : ℂ) ^ (-((N : ℂ) / 2) * ((∑ i, |d i| : ℤ) : ℂ))

def KerU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ} (ϖ : L) (q N : ℕ) (z : ℂˣ)
    (φ : GU σ r → ℂ) : Prop :=
  ∀ (d : Fin r → ℤ) (t : GU σ r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU σ r, ∀ k₂ ∈ KU σ r,
    φ (k₁ * t * k₂) = ((z : ℂ) * ((q : ℂ) ^ N)⁻¹) ^ (∑ i, max (d i) 0)

variable {D : D7}

abbrev Gv (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := GLoc D.sp.cm.sig V.gram v

abbrev Kv (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (Gv V v) := stabLoc D.sp.cm.sig V.gram (frameLat V) v

abbrev embV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Gv V v →* GA D V := emb D.sp.cm.sig V.gram v

abbrev projV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : GA D V →* Gv V v := proj D.sp.cm.sig V.gram v

def IsLocKer (V : HSp D) (N : ℕ) (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Gv V v → ℂ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v),
    (IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e → KerGL w N (z w) (φ ∘ e.symm)) ∧
    (IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) →
      IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e → KerU ϖ (qV D.host.F v) N (z w) (φ ∘ e.symm))

def VacFin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) (latO S T (frameLat S) (frameLat T) fun u => u = v) f

def bddAut (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | Continuous f ∧ (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) ∧ ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C}
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl, 0, fun _ => by simp⟩
  add_mem' := by
    rintro f f' ⟨h1, h2, C, h3⟩ ⟨h1', h2', C', h3'⟩
    exact ⟨h1.add h1', fun γ hγ g => by simp [h2 γ hγ, h2' γ hγ], C + C',
      fun g => (norm_add_le _ _).trans (add_le_add (h3 g) (h3' g))⟩
  smul_mem' := by
    rintro c f ⟨h1, h2, C, h3⟩
    exact ⟨h1.const_smul c, fun γ hγ g => by simp [h2 γ hγ], ‖c‖ * C,
      fun g => (norm_smul c (f g)).le.trans (mul_le_mul_of_nonneg_left (h3 g) (norm_nonneg _))⟩

def bddRep (V : HSp D) : Representation ℂ (GA D V) (bddAut V) :=
  GlobalTheory.PRep.sub (GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ) (bddAut V) (by
    rintro g f ⟨h1, h2, C, h3⟩
    haveI : IsTopologicalGroup (GA D V) := isTopologicalGroup_HA _ _ _
    exact ⟨h1.comp (continuous_mul_const g), fun γ hγ x => by
      show f (γ * x * g) = f (x * g)
      rw [mul_assoc, h2 γ hγ], C, fun x => h3 _⟩)

theorem coe_bddRep (V : HSp D) (g : GA D V) (f : bddAut V) : (bddRep V g f : GA D V → ℂ) = rTr V g f := rfl

theorem const_mem_bddAut (V : HSp D) (c : ℂ) : (fun _ => c) ∈ bddAut V :=
  ⟨continuous_const, fun _ _ _ => rfl, ‖c‖, fun _ => le_rfl⟩

open Classical in

def levDatum (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank)
    (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) : WO S T → ℂ :=
  fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaG LT m (fun PP => redM PP (frMapAdj S T βS βT x)) * omegaQ Q T.rank m (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
    else 0

open Classical in
theorem isLevelVec_iff {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {LT : LevDat D.host.E ℂ T.rank} {Q : Finset (Pl D.host.E)}
    {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec ψ θ S T sT ΛS ΛT βS βT LT Q m f₀ f ↔
      IsVacO ψ θ S T (fun _ => 1) sT ΛS ΛT f₀ ∧ ∃ e : AE D, IsIdemSum e (LT.Pg ∪ Q) ∧
        IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ (levDatum S T βS βT LT Q m e) f :=
  Iff.rfl

example {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (N : ℕ) (z : ℂˣ) :
    KerGL (r := 0) w N z fun _ => 1 := fun _ _ _ _ _ _ _ _ _ => by simp

end GlobalTheory.FinZeta

end
