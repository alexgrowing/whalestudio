import Formalism.LocalToGlobal.HermitianForms.TiedTw

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

variable {D : D7}

abbrev LdG (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  dualL (sigD D : D.host.E →+* D.host.E) (gramN D i hi) L

abbrev LkG (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (Pv : Ideal (𝓞 D.host.E)) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  L ⊔ Pv • LdG D i hi L

section Gen

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def PvG (res : ∀ v : A.vT, 𝓞 D.host.E →+* A.Fv v) (v : A.vT) : Ideal (𝓞 D.host.E) := RingHom.ker (res v)

instance (res : ∀ v : A.vT, 𝓞 D.host.E →+* A.Fv v) (v : A.vT) : (PvG res v).IsPrime := RingHom.ker_isPrime _

set_option maxHeartbeats 1000000 in

structure LevelCompatibleLattices (T : ℕ) (res : ∀ v : A.vT, 𝓞 D.host.E →+* A.Fv v) (i : ℕ) (hi : i ≤ D.R.m)
    (lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) where

  pr : ∀ v c, ↥(LdG D i hi (lat c)) →+ M.lv i v c
  pr_surj : ∀ v c, Function.Surjective (pr v c)
  pr_smul : ∀ v c (a : 𝓞 D.host.E) z, pr v c (a • z) = res v a • pr v c z
  pr_ker : ∀ v c z, pr v c z = 0 ↔ z.1 ∈ PvG res v • LdG D i hi (lat c)

  fv_ker : ∀ v c z, M.fv i v c (pr v c z) = 0 ↔ z.1 ∈ LkG D i hi (PvG res v) (lat c)

  prk : ∀ v c, ↥(LkG D i hi (PvG res v) (lat c)) →+ M.lk i v c
  prk_surj : ∀ v c, Function.Surjective (prk v c)
  prk_smul : ∀ v c (a : 𝓞 D.host.E) z, prk v c (a • z) = res v a • prk v c z
  prk_ker : ∀ v c z, prk v c z = 0 ↔ z.1 ∈ PvG res v • LkG D i hi (PvG res v) (lat c)

  te : ∀ v c (z : ↥(LdG D i hi (lat c))), M.fv i v c (pr v c z) = 1 →
    ∀ h : ((T : ℕ) : 𝓞 D.host.E) • z.1 ∈ LkG D i hi (PvG res v) (lat c), prk v c ⟨_, h⟩ = M.te i v c

variable {M} {T : ℕ} {res : ∀ v : A.vT, 𝓞 D.host.E →+* A.Fv v} {i : ℕ} {hi : i ≤ D.R.m}
  {lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  {Ch : Type} {chOf : C.cls i → Ch}

set_option maxHeartbeats 1000000 in

def FvTieG (L : LevelCompatibleLattices M T res i hi lat)
    (eV : A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (T : 𝓞 D.host.F) ∈ v.asIdeal})
    (K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1))
    (fMe : ∀ β v, (K β).lev.fM (eV v).1 (eV v).2 ≃+ A.Fv v) : Prop :=
  ∀ v β (c : {c // chOf c = β}) (z : ↥(LdG D i hi (lat c.1)))
    (hz : ((bc (prV (E := D.host.E) (eV v).1) ((K β).y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((eV v).1.adicCompletion D.host.F) (z.1 a)) ∈
      latS (F := D.host.F) ((eV v).1.adicCompletion D.host.F) (intV D.host.E (eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (K β).lev.Lb))),
    M.fv i v c.1 (L.pr v c.1 z) = fMe β v ((K β).lev.fT (eV v).1 (eV v).2 ⟨_, hz⟩)

set_option maxHeartbeats 1000000 in

def UpNatTieG (L : LevelCompatibleLattices M T res i hi lat) (eY : C.Y i ≃ Fr D i hi)
    (eV : A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (T : 𝓞 D.host.F) ∈ v.asIdeal})
    (K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1)) : Prop :=
  ∀ v β (c : {c // chOf c = β}) (z : ↥(LdG D i hi (lat c.1))), M.fv i v c.1 (L.pr v c.1 z) = 1 →
    ∃ (hβ : chOf (M.up i v c.1 (L.pr v c.1 z)) = β)
      (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (K β).lev.U),
      (∀ v', v' ≠ (eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        ((K β).y ⟨M.up i v c.1 (L.pr v c.1 z), hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (mulLat γ.1.1 (lat (M.up i v c.1 (L.pr v c.1 z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (LdG D i hi (lat c.1)) ∧
      Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (mulLat γ.1.1 (LdG D i hi (lat (M.up i v c.1 (L.pr v c.1 z))))) =
        Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (LdG D i hi (lat c.1) ⊔
          Submodule.span (𝓞 D.host.E) {((T : ℕ) : D.host.E)⁻¹ • z.1}) ∧
      (∀ (x : ↥(LdG D i hi (lat (M.up i v c.1 (L.pr v c.1 z)))))
        (hx : ((T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ LdG D i hi (lat c.1)),
        M.fv i v _ (L.pr v _ x) = M.fv i v c.1 (L.pr v c.1 ⟨_, hx⟩)) ∧
      ∀ (h : C.Y i → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (eY s') (eY s) →
        M.upT i v c.1 (L.pr v c.1 z) h s = ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

set_option maxHeartbeats 1000000 in

def DnNatTieG (L : LevelCompatibleLattices M T res i hi lat) (eY : C.Y i ≃ Fr D i hi)
    (eV : A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (T : 𝓞 D.host.F) ∈ v.asIdeal})
    (K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1)) : Prop :=
  ∀ v β (c : {c // chOf c = β}) (g : Module.Dual (A.Fv v) (M.lk i v c.1)), g ≠ 0 →
    ∃ (hβ : chOf (M.dn i v c.1 g) = β)
      (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (K β).lev.U),
      (∀ v', v' ≠ (eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        ((K β).y ⟨M.dn i v c.1 g, hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (mulLat γ.1.1 (LdG D i hi (lat (M.dn i v c.1 g)))) =
        Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (lat c.1) ∧
      (∀ (x : ↥(LdG D i hi (lat (M.dn i v c.1 g)))) (hx : γ.1.1 *ᵥ x.1 ∈ LkG D i hi (PvG res v) (lat c.1)),
        M.fv i v _ (L.pr v _ x) = g (L.prk v c.1 ⟨_, hx⟩)) ∧
      ∀ (h : C.Y i → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (eY s') (eY s) →
        M.dnT i v c.1 g h s = ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

variable (M)

open Classical in

def BwTieG (T : ℕ) (res : ∀ v : A.vT, 𝓞 D.host.E →+* A.Fv v) {i : ℕ} {hi : i ≤ D.R.m} (eY : C.Y i ≃ Fr D i hi)
    (lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Prop :=
  ∀ w, D.what₂.places.resChar w = T → M.seenP w = true →
    ∀ v (x : (M.lat i).V), x ∈ M.Bw i w v ↔
    ∀ (c : C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis T (LdG D i hi (lat c) : Set _) B → IsLocBasis T (LkG D i hi (PvG res v) (lat c) : Set _) B' →
      ∃ P ∈ IntSpan D w (M.lam i), ∀ z, M.emb i x c z =
        fnOf _ (shiftOf (lamTG M i))
          (fun τ => if τ = M.tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ
            else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ) P (eY z)

end Gen

variable {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

set_option maxHeartbeats 4000000 in

structure TwistedLevelData {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {F : ∀ u, FormsTied D u} (W : TwFormsTied D Tw T F) where
  lv : ∀ u μ, μ ≠ D.what₂.mu0 → ∀ i, 1 ≤ i → ∀ hm : i ≤ D.R.m,
    LevelCompatibleLattices (Tw.fm u μ) (D.mem u).A.T ((W.atT u μ).res (F u).atT) i hm (fun c => latCrd D i hm (T.lat u μ i c))
  fMe : ∀ u μ hμ i h1 hm β v, (W.ch u μ hμ i h1 hm β).lev.fM (((W.atT u μ).eV (F u).atT) v).1 (((W.atT u μ).eV (F u).atT) v).2 ≃+
    (Tw.A u μ).Fv v
  fv : ∀ u μ hμ i h1 hm, FvTieG (lv u μ hμ i h1 hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm) (fMe u μ hμ i h1 hm)
  upN : ∀ u μ hμ i h1 hm, UpNatTieG (lv u μ hμ i h1 hm) (twY T F u μ i hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm)
  dnN : ∀ u μ hμ i h1 hm, DnNatTieG (lv u μ hμ i h1 hm) (twY T F u μ i hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm)
  bw : ∀ u μ, μ ≠ D.what₂.mu0 → ∀ i, 1 ≤ i → ∀ hm : i ≤ D.R.m,
    BwTieG (Tw.fm u μ) (D.mem u).A.T ((W.atT u μ).res (F u).atT) (twY T F u μ i hm) (fun c => latCrd D i hm (T.lat u μ i c))

end Formalism.L2.Forms

end
