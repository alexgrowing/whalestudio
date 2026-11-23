import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IotaEmbeddingColumns

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable (D) in

def fieldLL : IntermediateField ℚ ℂ := D.what₂.embLL.toRatAlgHom.fieldRange

def iotaW (T : CoreJ D) (i : Fin D.R.m) :
    (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

section Row

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def RowAt (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) {Tup : Type} (tup : Tup → T0)
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) : Prop :=
  ∃ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (jL : D.what₂.LL →+* c'.F)
    (c0' : VsV D i c'.F →ₛₗ[c'.F.val.toRingHom] (R.cV i).W)
    (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
      ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))
    (io : VVc c' (lamV D i) →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F) (hw : VVc c' (lamV D i))
    (dδ : Tup → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank)
    (U₂ : ∀ s, Unf (dδ s).Xo₂ (dδ s).c₂
      (c'.F.val.toRingHom.comp ((dδ s).eF.symm : (dδ s).c₂.F →+* c'.F)) D.R.r)
    (dict₂ : ∀ s, GA D (Wc D i) → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U₂ s).X k).Ψ D.R.r)
    (Cl : Tup → Type) (_ : ∀ s, Fintype (Cl s)) (bad : Tup → ℕ)
    (Lh : ∀ s, Cl s → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (La : ∀ s, Cl s → GenLat D.host.E (Vc D i).rank) (Nc gam : ∀ s, Cl s → ℕ) (vol : Tup → c'.F)
    (ep : ∀ s, Cl s → c'.F) (B : Tup → Ideal (𝓞 D.host.E) → c'.F)
    (epF : Tup → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E) → c'.F)
    (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (φ : ∀ s, (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) (dδ s).l₂) → c'.F)
    (w : ∀ s, Cl s → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (dδ s).l₂) → c'.F)
    (thAd : ∀ s, (Cl s → VsV D i c'.F) → AutQ (Wc D i) → ℂ) (Plc : ∀ s, (Cl s → VsV D i c'.F) → Prop),
    ThPinsR R i jL c'.F.val.toRingHom (v₀ i (sg0 D A)) c0' (iotaW T i) T.Q.l.M (Mfr T.Q.l) (fun g => (lev g).1) ∧
    (∀ s, ThPinsT R i c'.F.val.toRingHom (tup s) (v₀ i (sg0 D A)) c0' (iotaW T i) (bad s) T.Q.l.Mb (dδ s).I
      (Mfr (dδ s).l₂ • ⊤) (Lh s) (gam s) (vol s) (B s) (xi s) (φ s) (thAd s) (Plc s)) ∧
    OneMapTieP hle (fieldLL D) (T.U ((i : ℕ) + 1)) c'.F.val.toRingHom (Wc D i) (rank_Wc i)
      (castDict hV (T.dict ((i : ℕ) + 1) T.toCore.σ₀)) (castDict hV (T.mu ((i : ℕ) + 1) T.toCore.σ₀)) (xiR D) (wtA (κ i)) lev
      dδ Cl bad Lh La Nc gam vol ep B epF (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1) (tauE D) (lamV D i) io hw φ w U₂ dict₂
      (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) xi thAd Plc cc ph

def RowBase (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i)
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) : Prop :=
  RowAt T R κ v₀ i hV (fun _ : Unit => A.μ0) cc ph

def RowAll (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i)
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) : Prop :=
  RowAt T R κ v₀ i hV (fun t : T0 => t) cc ph

def PlaceGuard : Prop :=
  (∀ t, ∀ PP ∈ R.Q t, ∀ PP' ∈ R.Q t, PP.asIdeal.under ℤ = PP'.asIdeal.under ℤ →
      PP.asIdeal.under (𝓞 D.host.K) = PP'.asIdeal.under (𝓞 D.host.K)) ∧
    ∀ t PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

def HalfTie : Prop := T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal

def ConstTie : Prop :=
  ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i),
    (∃ cc ph, RowAll T R κ v₀ i hV cc ph) → ∃ ph, RowAll T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) ph

def PhaseAtBase (phs : Fin D.R.m → ℂ) : Prop :=
  ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i),
    (∃ ph, RowBase T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) ph) →
      RowBase T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (phs i)

def BaseNonzero : Prop :=
  ∀ i : Fin D.R.m, ∃ x₀ : A.fam.amb.FL i A.μ0,
    onQ (Wc D i) (R.thF i A.μ0 (jVx R i A.μ0 x₀) (v₀ i (sg0 D A))) ≠ 0

def Ties (F : Face D A) : Prop :=
  R.Char F ∧ TieIn T R κ v₀ ∧ (∀ i, VStd D i) ∧ HalfTie T R

def OneMapFree (F : Face D A) : Prop :=
  Ties T R κ v₀ F → PlaceGuard T R →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i), ∃ cc ph, RowAll T R κ v₀ i hV cc ph

def OneMapAll (F : Face D A) (phs : Fin D.R.m → ℂ) : Prop :=
  Ties T R κ v₀ F → ConstTie T R κ v₀ → PhaseAtBase T R κ v₀ phs → BaseNonzero T R v₀ → PlaceGuard T R →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i),
      RowAll T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (phs i)

theorem space_eq {F : Face D A} (h : Ties T R κ v₀ F) (i : Fin D.R.m) : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i :=
  h.2.1.laws.spaceW _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀

theorem RowAt.norm {i : Fin D.R.m} {hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i} {Tup : Type} {tup : Tup → T0}
    {cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ} {ph : ℂ} (h : RowAt T R κ v₀ i hV tup cc ph) :
    (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
  have h1 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact ⟨h1.1, h1.2.1⟩

end Row

end GlobalTheory.IndefiniteRowSideFullHecke.IotaEmbeddingColumns
