import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

def CongE {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (c : ℕ)
    (g g' : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ x ∈ stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • (g x - g' x) ∈ stdAt E n P

theorem congE_refl {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (c : ℕ)
    (g : Sp E n ≃ₗ[E] Sp E n) : CongE P c g g := fun x _ => by
  rw [sub_self, smul_zero]
  exact Submodule.zero_mem _

theorem CongE.symm {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {c : ℕ}
    {g g' : Sp E n ≃ₗ[E] Sp E n} (h : CongE P c g g') : CongE P c g' g := fun x hx => by
  rw [← neg_sub, smul_neg]
  exact Submodule.neg_mem _ (h x hx)

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

abbrev sm : Seam (I.rec7 l Z) B.fields := seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G

abbrev SBof (a : I.ι) : Finset (HeightOneSpectrum (𝓞 B.fields.E)) := rowSG (B.primes X) I.sel (I.tup a)

abbrev Charts (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) {Ch : Type}
    (chOf : (I.stp u a i).Cl → Ch) : Type 1 :=
  ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
    (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))

abbrev ReadsAt {u : B.Word} {a : I.ι} {i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type}
    {chOf : (I.stp u a i).Cl → Ch} (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)) : Prop :=
  I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
    (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k

def ChiFin {T i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ κ : S.U, (∀ v ∈ badG (I.rec7 l Z), bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → S.chi κ ^ n = 1

def FrNear (a : I.ι) {n : ℕ} (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E) : Prop :=
  ∀ P : SBof I a, GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (k⁻¹ * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P)) ∧
    GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P))⁻¹ * k)

def LiftsInv {u : B.Word} {a : I.ι} {i : ℕ} {b : (I.stp u a i).β} (κ : (I.stp u a i).G b) (P : SBof I a)
    (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) : Prop :=
  g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
    (∀ h : P.1 ∈ (B.primes X).vGs, ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1,
      redV P.1 (g x) = ((κ.2.1.1 ⟨P.1, h⟩)⁻¹).1.mulVec (redV P.1 x)) ∧
    ∀ h : P.1 ∈ I.Q a, g = ((κ.2.2.1 ⟨P.1, h⟩)⁻¹).1

abbrev MidAt {u : B.Word} {a : I.ι} {i : ℕ} (hi : i < B.R.m) (b : (I.stp u a i).β) (P : SBof I a)
    (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K) : Prop :=
  GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i (Idx.get b hi) P) g z

def Keeps {u : B.Word} {a : I.ι} {i : ℕ} {b : (I.stp u a i).β} (κ : (I.stp u a i).G b) (p : (I.stp u a i).D b) : Prop :=
  (I.stp u a i).gam b κ = 1 ∧ cosetIn ((I.stp u a i).act b κ p) = cosetIn p

theorem liftsInv_one {u : B.Word} {a : I.ι} {i : ℕ} {b : (I.stp u a i).β} (P : SBof I a) :
    LiftsInv I (1 : (I.stp u a i).G b) P 1 := by
  refine ⟨one_mem _, fun h x _ => ?_, fun h => ?_⟩
  · show redV P.1 x = ((1 : GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ P.1.asIdeal))⁻¹).1.mulVec (redV P.1 x)
    simp
  · show _ = ((1 : Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)⁻¹).1
    simp

theorem keeps_one {u : B.Word} {a : I.ι} {i : ℕ} {b : (I.stp u a i).β} (p : (I.stp u a i).D b) :
    Keeps I (1 : (I.stp u a i).G b) p :=
  ⟨map_one _, congrArg cosetIn (@one_smul _ _ _ ((I.stp u a i).actD b) p)⟩

end GlobalTheory.Mem.Col2.AdT

end
