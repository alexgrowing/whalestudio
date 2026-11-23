import Formalism.PeriodIntegrals.InHHClassFin
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEasy

noncomputable section

open NumberField Matrix IsDedekindDomain Formalism.UG PI.InHHClassFin
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

def ClassSetMono : Prop :=
  ∀ (G : Type) [Group G] (Γ K K' : Subgroup G), K ≤ K' →
    Finite (ClassSet Γ K) → Finite (ClassSet Γ K')

def ClassSetFinIdx : Prop :=
  ∀ (G : Type) [Group G] (Γ K K' : Subgroup G), K' ≤ K → K'.relIndex K ≠ 0 →
    Finite (ClassSet Γ K) → Finite (ClassSet Γ K')

def ClassSetMap : Prop :=
  ∀ (G G' : Type) [Group G] [Group G'] (Φ : G ≃* G') (Γ K : Subgroup G),
    Finite (ClassSet (Γ.map Φ.toMonoidHom) (K.map Φ.toMonoidHom)) → Finite (ClassSet Γ K)

def KgNhd : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (x : I.Gf), 1 ≤ g →
    ∃ g' : ℕ, 1 ≤ g' ∧ ∀ h : I.Gf, h ∈ I.Kg g' → x⁻¹ * h * x ∈ I.Kg g

def SigConj : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (τ : I.E →+* ℂ),
    τ.comp (I.cm.sig : I.E →+* I.E) = (starRingEnd ℂ).comp τ

abbrev stdLevel (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (J' : Matrix (Fin k) (Fin k) I.E) :
    Subgroup (UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)) :=
  (levelAfL I.cm.sig J' (stdLat (n := Fin k) (A := I.E) (𝓞 I.E))).subgroupOf
    (UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F))

abbrev congS (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) (g : ℕ) : Subgroup (HfinS I S) :=
  Subgroup.closure {h : HfinS I S | (h : I.Gf) ∈ I.Kg g}

def Restrict (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) : Prop :=
  ∃ (k : ℕ) (J' : Matrix (Fin k) (Fin k) I.E)
    (Φ : HfinS I S ≃* UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)),
    IsHerm (I.cm.sig : I.E →+* I.E) J' ∧ IsUnit J'.det ∧ IsTotDef I.cm.sig J' ∧
    (iotaFS I S).range.map Φ.toMonoidHom =
      (ratPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)).subgroupOf
        (UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)) ∧
    ∀ g : ℕ, 1 ≤ g →
      (stdLevel I J' ⊓ (congS I S g).map Φ.toMonoidHom).relIndex (stdLevel I J') ≠ 0

theorem stabClassFinite_of (hMono : ClassSetMono) (hIdx : ClassSetFinIdx) (hMap : ClassSetMap)
    (hTop : KgNhd) (hSig : SigConj)
    (hR : ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)), DefiniteCompl I S → Restrict I S) :
    StabClassFinite := by
  intro I S hS K g x hg hK
  obtain ⟨g', hg', hg'K⟩ := hTop I g x hg
  have hCK : congS I S g' ≤ K := by
    rw [Subgroup.closure_le]
    intro h hh
    exact hK h (hg'K _ hh)
  apply hMono _ _ _ _ hCK
  obtain ⟨k, J', Φ, hH, hU, hD, hrat, hidx⟩ := hR I S hS
  apply hMap _ _ Φ
  rw [hrat]
  have hStd : Formalism.UG.CS.StdLatFull := by
    first
      | exact Formalism.UG.P.standard_lattice_full_holds
      | exact Formalism.UG.P.stdLatFull
      | exact Formalism.UG.P.stdLatFull_holds
      | exact Formalism.UG.P.CsEasy.stdLatFull
      | exact Formalism.UG.Final.StdLatFull
  obtain ⟨hfin, hspan⟩ := hStd I.E (Fin k)
  have hL := Formalism.UG.Final.ClassSetFiniteL I.F I.E (Fin k) I.cm.sig J' (hSig I) hH hU hD _ hfin hspan
  have h2 := hIdx _ _ _ _ inf_le_left (hidx g' hg') hL
  exact hMono _ _ _ _ inf_le_right h2

structure Frame (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) where
  m : ℕ
  k : ℕ
  B : Matrix (Fin I.n) (Fin m ⊕ Fin k) I.E
  Bi : Matrix (Fin m ⊕ Fin k) (Fin I.n) I.E
  mul_inv : B * Bi = 1
  inv_mul : Bi * B = 1
  col_span : ∀ j, (fun i => B i (Sum.inl j)) ∈ Submodule.span I.E S
  S_coord : ∀ s ∈ S, ∀ j, (Bi *ᵥ s) (Sum.inr j) = 0
  orth : ∀ s ∈ S, ∀ j, hform (starRingEnd I.E) I.J s (fun i => B i (Sum.inr j)) = 0

def Frame.J' {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)} (fr : Frame I S) :
    Matrix (Fin fr.k) (Fin fr.k) I.E :=
  (cT (starRingEnd I.E) fr.B * I.J * fr.B).toBlocks₂₂

def psiMat {E F : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n m k : ℕ} (B : Matrix (Fin n) (Fin m ⊕ Fin k) E) (Bi : Matrix (Fin m ⊕ Fin k) (Fin n) E)
    (y : Matrix (Fin k) (Fin k) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R) :=
  (Matrix.map B (inclE (F := F) R) : Matrix (Fin n) (Fin m ⊕ Fin k) (E ⊗[F] R)) *
    Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (E ⊗[F] R)) 0 0 y *
    (Matrix.map Bi (inclE (F := F) R) : Matrix (Fin m ⊕ Fin k) (Fin n) (E ⊗[F] R))

def FrameExists : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)), DefiniteCompl I S → Nonempty (Frame I S)

def FrameIso : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) (fr : Frame I S),
    ∃ Φ : HfinS I S ≃* UPts I.cm.sig fr.J' (FiniteAdeleRing (𝓞 I.F) I.F),
      ∀ y, I.fmat ((Φ.symm y : HfinS I S) : I.Gf) =
        psiMat (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) fr.B fr.Bi
          ((y : GL (Fin fr.k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin fr.k) (Fin fr.k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F))

def FrameGram : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) (fr : Frame I S), DefiniteCompl I S →
    IsHerm (I.cm.sig : I.E →+* I.E) fr.J' ∧ IsUnit fr.J'.det ∧ IsTotDef I.cm.sig fr.J'

def FrameRat : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) (fr : Frame I S)
    (Φ : HfinS I S ≃* UPts I.cm.sig fr.J' (FiniteAdeleRing (𝓞 I.F) I.F)),
    (∀ y, I.fmat ((Φ.symm y : HfinS I S) : I.Gf) =
        psiMat (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) fr.B fr.Bi
          ((y : GL (Fin fr.k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin fr.k) (Fin fr.k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F))) →
    (iotaFS I S).range.map Φ.toMonoidHom =
      (ratPts I.cm.sig fr.J' (FiniteAdeleRing (𝓞 I.F) I.F)).subgroupOf
        (UPts I.cm.sig fr.J' (FiniteAdeleRing (𝓞 I.F) I.F))

def LevelStep : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (m k : ℕ) (B : Matrix (Fin I.n) (Fin m ⊕ Fin k) I.E)
    (Bi : Matrix (Fin m ⊕ Fin k) (Fin I.n) I.E), B * Bi = 1 → Bi * B = 1 →
    ∀ (J' : Matrix (Fin k) (Fin k) I.E) (g : ℕ), 1 ≤ g →
    ∃ N : Subgroup (UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)),
      N ≤ stdLevel I J' ∧ N.relIndex (stdLevel I J') ≠ 0 ∧
      ∀ y ∈ N, ∀ h : I.Gf,
        I.fmat h = psiMat (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) B Bi
          ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) → h ∈ I.Kg g

theorem restrict_of (hE : FrameExists) (hIso : FrameIso) (hG : FrameGram) (hRat : FrameRat)
    (hLev : LevelStep) (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) (hS : DefiniteCompl I S) :
    Restrict I S := by
  obtain ⟨fr⟩ := hE I S hS
  obtain ⟨Φ, hΦ⟩ := hIso I S fr
  obtain ⟨hH, hU, hD⟩ := hG I S fr hS
  refine ⟨fr.k, fr.J', Φ, hH, hU, hD, hRat I S fr Φ hΦ, ?_⟩
  intro g hg
  obtain ⟨N, hNL, hNi, hNK⟩ := hLev I fr.m fr.k fr.B fr.Bi fr.mul_inv fr.inv_mul fr.J' g hg
  have hle : N ≤ stdLevel I fr.J' ⊓ (congS I S g).map Φ.toMonoidHom := by
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨hNL hy, Subgroup.mem_map.mpr ⟨Φ.symm y, ?_, by simp⟩⟩
    exact Subgroup.subset_closure (hNK y hy _ (hΦ y))
  exact fun h0 => hNi (Subgroup.relIndex_eq_zero_of_le_left hle h0)

theorem stabClassFinite_of_steps (hMono : ClassSetMono) (hIdx : ClassSetFinIdx)
    (hMap : ClassSetMap) (hTop : KgNhd) (hSig : SigConj) (hE : FrameExists) (hIso : FrameIso)
    (hG : FrameGram) (hRat : FrameRat) (hLev : LevelStep) : StabClassFinite :=
  stabClassFinite_of hMono hIdx hMap hTop hSig
    (fun I S hS => restrict_of hE hIso hG hRat hLev I S hS)

end PI.UnitaryGroupMassFormula.InHHClassFin
