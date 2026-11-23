import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

def matF (V : HSp D) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
  Units.val (h : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))

def compAtPl (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  (matF V h).map (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E))

variable (D) in

def IsSplitPl (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∃ P P' : HeightOneSpectrum (𝓞 D.host.E), P ≠ P' ∧ P.under (𝓞 D.host.F) = v ∧ P'.under (𝓞 D.host.F) = v

def SuppSplitOff (V : HSp D) (bad : ℕ) (h : Bridge.Gf V) : Prop :=
  ∃ Sp : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    (∀ v ∈ Sp, IsSplitPl D v ∧ (bad : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, v ∉ Sp → compAtPl V v h = 1

def IsTransl (V : HSp D) (Λ : Lat V) (h : Bridge.Gf V) (L : Lat V) : Prop :=
  ∀ x : Fin V.rank → D.host.E, x ∈ L ↔
    (matF V h⁻¹).mulVec (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E))

def IsOpenLev (V : HSp D) (J' : Subgroup (Bridge.Gf V)) : Prop :=
  IsOpen ((J'.comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V))

def IsSubLev (V : HSp D) (J J' : Subgroup (Bridge.Gf V)) (vol : ℝ) : Prop :=
  J' ≤ J ∧ J'.relIndex J ≠ 0 ∧ IsOpenLev V J' ∧ vol = ((J'.relIndex J : ℕ) : ℝ)⁻¹

def IsAdReps (V : HSp D) (Λ : Lat V) (J' : Subgroup (Bridge.Gf V)) (bad : ℕ) {n : ℕ} (h : Fin n → Bridge.Gf V)
    (Lh : Fin n → Lat V) (gam : Fin n → ℕ) : Prop :=
  Bridge.IsReps (Bridge.ratF V) J' h ∧ (∀ a, SuppSplitOff V bad (h a)) ∧ (∀ a, IsTransl V Λ (h a) (Lh a)) ∧
    ∀ a, Finite (Bridge.stab (Bridge.ratF V) J' (h a)) ∧ gam a = Nat.card (Bridge.stab (Bridge.ratF V) J' (h a))

def IsLatReps (V : HSp D) (Λ : Lat V) (bad : ℕ) {n : ℕ} (Lh : Fin n → Lat V) : Prop :=
  (∀ a, Submodule.IsLattice D.host.E (Lh a) ∧ Formalism.L2.Herm.dualL D.sp.cm V (Lh a) = Lh a ∧
    ∃ M : ℕ, 0 < M ∧ M.Coprime bad ∧ (∀ x ∈ Λ, (M : D.host.E) • x ∈ Lh a) ∧ ∀ x ∈ Lh a, (M : D.host.E) • x ∈ Λ) ∧
  ∀ (g : Bridge.Gf V) (L : Lat V), IsTransl V Λ g L →
    ∃ (a : Fin n) (γ : GL (Fin V.rank) D.host.E), γ ∈ UR D.sp.cm V.gram ∧
      ∀ x, x ∈ Lh a ↔ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x ∈ L

variable {T : Type}

def levJ (L : LevCh D T) (i : Fin D.R.m) (t : T) : Subgroup (Bridge.Gf (Vc D i)) :=
  (levEnv (Vc D i) (L.βV i) (L.datVt i t)).J

def IsBad (L : LevCh D T) (t : T) (bad : ℕ) : Prop :=
  0 < bad ∧ ∀ PP : Pl D.host.E, PP ∈ L.Pg ∨ PP ∈ L.Q t → (bad : 𝓞 D.host.E) ∈ PP.asIdeal

def RepsAt (L : LevCh D T) (i : Fin D.R.m) (t : T) (N : ℕ) : Prop :=
  ∃ (n : ℕ) (h : Fin n → Bridge.Gf (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ) (Lh : Fin n → Lat (Vc D i))
    (gam : Fin n → ℕ) (vol : ℝ),
    IsBad L t bad ∧ N ∣ bad ∧ IsSubLev (Vc D i) (levJ L i t) J' vol ∧
      IsAdReps (Vc D i) (L.ΛV i) J' bad h Lh gam ∧ IsLatReps (Vc D i) (L.ΛV i) bad Lh

section Row

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowAt (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → RealDat.models_vpos (D := D) →
    ∀ (i : Fin D.R.m) (t : T) (N : ℕ), 0 < N → RepsAt R.toLevCh i t N

def RowPlainAt (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → RealDat.models_vpos (D := D) → ∀ (i : Fin D.R.m) (t : T), RepsAt R.toLevCh i t 1

theorem RowAt.plain {R : RealDat D A Ks} (h : RowAt R) : RowPlainAt R :=
  fun hL hp i t => h hL hp i t 1 Nat.one_pos

end Row

def Row : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), RowAt R

theorem IsSubLev.vol_pos {V : HSp D} {J J' : Subgroup (Bridge.Gf V)} {vol : ℝ} (h : IsSubLev V J J' vol) :
    0 < vol ∧ vol ≤ 1 := by
  obtain ⟨_, h2, _, rfl⟩ := h
  have h1 : (1 : ℝ) ≤ ((J'.relIndex J : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h2
  exact ⟨inv_pos.2 (by linarith), inv_le_one_of_one_le₀ h1⟩

theorem IsAdReps.pos {V : HSp D} {Λ : Lat V} {J' : Subgroup (Bridge.Gf V)} {bad n : ℕ} {h : Fin n → Bridge.Gf V}
    {Lh : Fin n → Lat V} {gam : Fin n → ℕ} (H : IsAdReps V Λ J' bad h Lh gam) : (∀ a, 0 < gam a) ∧ 0 < n := by
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨hf, e⟩ := H.2.2.2 a
    rw [e]; exact Nat.card_pos
  · obtain ⟨a, _⟩ := H.1 1
    exact a.pos

end GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

end
