import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.BadPlacesGoodCoefficients

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def badPlaces (D : D7) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  Formalism.L2.DIV.primesOf (((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F))

theorem mem_badPlaces (v : HeightOneSpectrum (𝓞 D.host.F)) :
    v ∈ badPlaces D ↔ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  unfold badPlaces
  rw [Formalism.L2.DIV.mem_primesOf, and_iff_right]
  exact_mod_cast mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

def IsReadingPlaces (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  ∃ pb : Fin 2 → 𝓞 D.host.E, (∀ i, (pb i : D.host.E) ∈ D.host.K) ∧ IsTypePlaces (D := D) D.host.g pb Pg

def IsBelow {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (b : Pg ≃ LevelCuspCharacters.Sq D.host) : Prop :=
  ∀ PP : Pg, (b PP).2.1.asIdeal = PP.1.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))

def toG0 {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (b : Pg ≃ LevelCuspCharacters.Sq D.host)
    (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* Formalism.L2.DIV.kP PP.1) (x : LevelCuspCharacters.LevelGroup D.host) :
    Formalism.L2.DIV.G0 Pg D.R.r :=
  fun PP => Matrix.GeneralLinearGroup.map (φ PP).toRingHom (x (b PP))

def goodCoeff {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (b : Pg ≃ LevelCuspCharacters.Sq D.host)
    (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* Formalism.L2.DIV.kP PP.1)
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) : Formalism.L2.DIV.G0 Pg D.R.r →₀ ℂ :=
  Finsupp.mapDomain (toG0 b φ) (LevelCuspCharacters.goodIdem (H := D.host) om).coeff

def IsFrameAtG (V : HSp D) (β : GL (Fin V.rank) (EAf D)) : Prop :=
  ∃ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ), IsBaseFrame V β Λ ((D.host.g 0 * D.host.g 1) ^ c)

def datR (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ)
    (fr : Lev.Frm) : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank :=
  datY V.rank D.R.r D.R.t 0 hr Pg ∅ P (fun _ _ => 1) (fun _ => 1) fr

def eLin (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (e : Formalism.L2.DIV.G0 L.Pg L.r →₀ ℂ) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := eAct V β L e
  map_add' F G := by
    funext h
    simp only [eAct, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  map_smul' a F := by
    funext h
    simp only [eAct, Finsupp.sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp

theorem rank_le_first_space_rank (D : D7) : D.R.r ≤ (D.sp.Y 0).rank := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Ranks.rankY]

theorem r_le_rank_Wc (D : D7) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : D.R.r ≤ (D.sp.W j).rank :=
  (D.sp.W_rank j h1 h2).ge

theorem rank_W_eq (D : D7) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (D.sp.W j).rank = (D.sp.Y 0).rank := by
  rw [D.sp.W_rank j h1 h2, D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Ranks.rankY]

section Parts

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}

def rowPart (M : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (β : GL (Fin (D.sp.Y 0).rank) (EAf D))
    (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ) (e : Formalism.L2.DIV.G0 Pg D.R.r →₀ ℂ)
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  EEpart θ M (levG (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B) : Set (GA D (D.sp.Y 0)))
    (levChi (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B))
    (eLin (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B) e) (badPlaces D) c

def formPart {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M : DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))) (β : GL (Fin (D.sp.W j).rank) (EAf D))
    (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ) (e : Formalism.L2.DIV.G0 Pg D.R.r →₀ ℂ)
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  Wpart θ j M (levG (D.sp.W j) β (datR _ (r_le_rank_Wc D h1 h2) Pg P Lev.Frm.A) : Set (GA D (D.sp.W j)))
    (levChi (D.sp.W j) β (datR _ (r_le_rank_Wc D h1 h2) Pg P Lev.Frm.A))
    (eLin (D.sp.W j) β (datR _ (r_le_rank_Wc D h1 h2) Pg P Lev.Frm.A) e) (badPlaces D) c

end Parts

def gramIn (V : HSp D) (β : GL (Fin V.rank) (EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (EAf D) :=
  Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) β.val *
    V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * β.val

def Matched (V V' : HSp D) (h : V'.rank = V.rank) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) : Prop :=
  ∃ y : GL (Fin V'.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
    (∀ PP ∈ Pg, Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) y = 1) ∧
    gramIn V' (β' * Formalism.L2.DIV.intGL D.host.F D.host.E V'.rank y) = (gramIn V β).submatrix (Fin.cast h) (Fin.cast h)

example (V : HSp D) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (β : GL (Fin V.rank) (EAf D)) : Matched V V rfl Pg β β :=
  ⟨1, fun _ _ => map_one _, by rw [map_one, mul_one]; rfl⟩

def DimPartsFor
    (lv : ∀ (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), (∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ) →
      Formalism.L2.DIV.LevelP Pg D.R.r ℂ)
    (ok : ∀ (D : D7) (V V' : HSp D), V'.rank = V.rank → Finset (Formalism.L2.DIV.Pl D.host.E) →
      GL (Fin V.rank) (EAf D) → GL (Fin V'.rank) (EAf D) → Prop) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsReadingPlaces D Pg →
  ∀ (b : Pg ≃ LevelCuspCharacters.Sq D.host), IsBelow b →
  ∀ (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* Formalism.L2.DIV.kP PP.1)
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ), LevelCuspCharacters.IsGeneratorFamily (H := D.host) om →
  ∀ (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ), Formalism.L2.DIV.IsGenericPsi Pg ψ →
  ∀ (M₀ : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (β₀ : GL (Fin (D.sp.Y 0).rank) (EAf D)), IsFrameAtG (D.sp.Y 0) β₀ →
  ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, ∃ d : ℕ,
    Module.rank ℂ (rowPart θ M₀ β₀ (lv D Pg ψ) (goodCoeff b φ om) c) = d ∧
    ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
      (M : DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))) (β : GL (Fin (D.sp.W j).rank) (EAf D)),
      IsFrameAtG (D.sp.W j) β → ok D (D.sp.Y 0) (D.sp.W j) (rank_W_eq D h1 h2) Pg β₀ β →
      Module.rank ℂ (formPart θ h1 h2 M β (lv D Pg ψ) (goodCoeff b φ om) c) = d

def DimParts : Prop := DimPartsFor (fun D Pg ψ => Formalism.L2.DIV.P0 Pg D.R.r ψ) (fun _ _ _ _ _ _ _ => True)

def DimPartsMatched : Prop :=
  DimPartsFor (fun D Pg ψ => Formalism.L2.DIV.P0 Pg D.R.r ψ) (fun _ V V' h Pg β β' => Matched V V' h Pg β β')

def DimPartsPrincipal : Prop :=
  DimPartsFor (fun D Pg _ => Formalism.L2.DIV.LevelP.triv Pg D.R.r ℂ) (fun _ _ _ _ _ _ _ => True)

def DimPartsSharp : Prop := DimPartsFor (fun D Pg ψ => Formalism.L2.DIV.Psharp Pg D.R.r D.R.k ψ) (fun _ _ _ _ _ _ _ => True)

def DimPartsSharpSym : Prop :=
  DimPartsFor (fun D Pg ψ => Formalism.L2.DIV.PsharpSym Pg D.R.r D.R.rS D.R.k ψ) (fun _ _ _ _ _ _ _ => True)

theorem DimParts.matched (h : DimParts) : DimPartsMatched := by
  intro D L hP θ hθ Pg hPg b hb φ om hom ψ hψ M₀ β₀ hβ₀ c
  obtain ⟨d, h0, hj⟩ := h D L hP θ hθ Pg hPg b hb φ om hom ψ hψ M₀ β₀ hβ₀ c
  exact ⟨d, h0, fun j h1 h2 M β hβ _ => hj j h1 h2 M β hβ trivial⟩

example (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ) :
    (datR V hr Pg P Lev.Frm.A).P = P.conj ∧ (datR V hr Pg P Lev.Frm.B).P = P := ⟨rfl, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.BadPlacesGoodCoefficients

end
