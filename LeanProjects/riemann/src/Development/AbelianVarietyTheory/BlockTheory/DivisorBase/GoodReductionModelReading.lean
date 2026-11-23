import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsOrthSum {X ι : Type} [AddCommGroup X] [Module ℂ X] (Orth : X → X → Prop) (Y : Submodule ℂ X)
    (part : ι → Submodule ℂ X) (Pi : Set ι) : Prop :=
  Pi.Finite ∧ Y = ⨆ c : Pi, part c ∧ iSupIndep (fun c : Pi => part c) ∧
    ∀ c ∈ Pi, ∀ c' ∈ Pi, c ≠ c' → ∀ x ∈ part c, ∀ y ∈ part c', Orth x y

example {X : Type} [AddCommGroup X] [Module ℂ X] (Orth : X → X → Prop) (Y : Submodule ℂ X) :
    IsOrthSum Orth Y (fun _ : Unit => Y) Set.univ := by
  refine ⟨Set.toFinite _, by simp, ?_, fun c _ c' _ h => absurd (Subsingleton.elim c c') h⟩
  exact iSupIndep_subsingleton _

example {X ι : Type} [AddCommGroup X] [Module ℂ X] (Orth : X → X → Prop) (Y : Submodule ℂ X) (part : ι → Submodule ℂ X)
    (h : IsOrthSum Orth Y part ∅) : Y = ⊥ := by
  rw [h.2.1]; exact iSup_of_empty _

variable {D : D7}

def IsBadSet (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ v, v ∈ Sb ↔ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal

def IsPlaceMatch {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg) : Prop :=
  ∀ (v : LevelCuspCharacters.Sq D.host) (x : 𝓞 D.host.F) (y : 𝓞 D.host.E),
    (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → (x ∈ v.2.1.asIdeal ↔ y ∈ (pl v).1.asIdeal)

def readG0 {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg)
    (red : ∀ v : LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1)) {n : ℕ} (hn : n = D.R.r)
    (x : Formalism.L2.DIV.G0 Pg n) : LevelCuspCharacters.LevelGroup D.host := fun v =>
  Units.map (Matrix.reindexAlgEquiv (ZMod (D.host.g v.1)) (ZMod (D.host.g v.1)) (finCongr hn)).toAlgHom.toMonoidHom
    (Matrix.GeneralLinearGroup.map (red v).toRingHom (x (pl v)))

def levelDatumAtBasePrime (V : HSp D) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ) :
    Formalism.L2.DIV.LevDat D.host.E ℂ V.rank :=
  Lev.datW V.rank Pg (Formalism.L2.DIV.P0 Pg V.rank ψ) Lev.Frm.A

def actLin (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (g0 : Formalism.L2.DIV.G0 L.Pg L.r) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := Lev.actG0 V β L g0
  map_add' F G := by
    unfold Lev.actG0
    split_ifs
    · funext h; exact mul_add _ _ _
    · exact (add_zero _).symm
  map_smul' a F := by
    unfold Lev.actG0
    split_ifs
    · funext h; exact mul_left_comm _ a _
    · exact (smul_zero _).symm

def eGoodOp (V : HSp D) (hV : V.rank = D.R.r) (β : GL (Fin V.rank) (Lev.EAf D)) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ) (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg)
    (red : ∀ v : LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1))
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) :=
  haveI : Finite (Formalism.L2.DIV.G0 Pg V.rank) := by
    haveI : ∀ PP : ↥Pg, Finite (Formalism.L2.DIV.kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    infer_instance
  haveI := Fintype.ofFinite (Formalism.L2.DIV.G0 Pg V.rank)
  ∑ x : Formalism.L2.DIV.G0 Pg V.rank,
    (LevelCuspCharacters.goodIdem (H := D.host) om).coeff (readG0 pl red hV x) • actLin V β (levelDatumAtBasePrime V Pg ψ) x

def IsFrameAtG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) : Prop :=
  ∃ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : ℕ), Lev.IsBaseFrame V β Λ ((D.host.g 0 * D.host.g 1) ^ a)

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

abbrev ModelW (D : D7) (j : ℕ) : Type 1 := DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))

section Spaces

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (j : ℕ) (hj : (D.sp.W j).rank = D.R.r) (M : ModelW D j) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D))
  {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ)
  (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg) (red : ∀ v : LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1))
  (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))

def goodW : Submodule ℂ (MMap M) :=
  WgoodRec θ j M (Lev.levG (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ) : Set (GA D (D.sp.W j)))
    (Lev.levChi (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ)) (eGoodOp (D.sp.W j) hj β ψ pl red om)

def partW (c : EigSys D) : Submodule ℂ (MMap M) :=
  Wpart θ j M (Lev.levG (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ) : Set (GA D (D.sp.W j)))
    (Lev.levChi (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ)) (eGoodOp (D.sp.W j) hj β ψ pl red om) Sb c

def occursW : Set (EigSys D) :=
  IxFull θ M (Lev.levG (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ) : Set (GA D (D.sp.W j)))
    (Lev.levChi (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ)) Sb (eGoodOp (D.sp.W j) hj β ψ pl red om)

end Spaces

def PetOrth {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (T T' : MMap M) : Prop :=
  AllSome (fun μ : Measure (GA D V) => μ.IsHaarMeasure) fun μ =>
    AllSome (fun 𝓕 : Set (GA D V) => IsFundamentalDomain (GQ V) 𝓕 μ) fun 𝓕 => IsMultIP M μ 𝓕 T T' 0

def SumW (D : D7) : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (pb : Fin 2 → 𝓞 D.host.E) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), Lev.IsTypePlaces D.host.g pb Pg →
  ∀ (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg), IsPlaceMatch pl →
  ∀ (red : ∀ v : LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1))
    (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ), Formalism.L2.DIV.IsGenericPsi Pg ψ →
  ∀ (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ), LevelCuspCharacters.IsGeneratorFamily (H := D.host) om →
  ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBadSet D Sb →
  ∀ (hm : (D.sp.W D.R.m).rank = D.R.r) (Mm : ModelW D D.R.m) (βm : GL (Fin (D.sp.W D.R.m).rank) (Lev.EAf D)),
    IsFrameAtG (D.sp.W D.R.m) βm →
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m →
  ∀ (hj : (D.sp.W j).rank = D.R.r) (M : ModelW D j) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    IsFrameAtG (D.sp.W j) β →
    IsOrthSum (PetOrth M) (goodW θ j hj M β ψ pl red om) (partW θ j hj M β ψ pl red om Sb)
      (occursW θ D.R.m hm Mm βm ψ pl red om Sb)

example (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (D.sp.W j).rank = D.R.r := D.sp.W_rank j h1 h2

end GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading
