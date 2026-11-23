import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Module Module.End

namespace Formalism.L2

def placesS (D : D7) (l : ℕ) : Set (PlE D.host) :=
  {v | (v ∈ placesOver D.host.E (D.host.g 0) ∨ v ∈ placesOver D.host.E (D.host.g 1) ∨
      v ∈ placesOver D.host.E (if l = D.host.pde then D.host.pde' else D.host.pde)) ∧
    v ∉ placesOver D.host.E l}

def GenAt (D : D7) (l : ℕ) (Q : Finset (PlE D.host)) (v : PlE D.host) (k : ℕ) : Prop :=
  IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q ∧ 1 ≤ k ∧ k ≤ D.R.nV

theorem mtL_eq (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w) :
    D.what₂.MtL (D.nd.mu i) (D.nd.j i) = D.what₂.MtL (D.what₂.muTw w) j := by
  obtain ⟨h1, h2⟩ := (D.nd.locs_mem j w i).1 h
  rw [D.nd.mu_w i, h1, h2]

def castMt (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)) : D.what₂.MtL (D.what₂.muTw w) j :=
  cast (mtL_eq D h) x

def castMtInv (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (y : D.what₂.MtL (D.what₂.muTw w) j) : D.what₂.MtL (D.nd.mu i) (D.nd.j i) :=
  cast (mtL_eq D h).symm y

theorem castMt_castMtInv (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (y : D.what₂.MtL (D.what₂.muTw w) j) : castMt D h (castMtInv D h y) = y := by
  unfold castMt castMtInv
  exact cast_cast _ _ y

set_option synthInstance.maxHeartbeats 400000 in

structure NLocBase (D : D7) (M : MtFam D) where

  Oc : ℕ → D.what₂.places.Pl → Type
  [ringOc : ∀ j w, CommRing (Oc j w)]
  [domOc : ∀ j w, IsDomain (Oc j w)]
  [dvrOc : ∀ j w, IsDiscreteValuationRing (Oc j w)]

  ec : ∀ j w, D.what₂.LL →+* FractionRing (Oc j w)

  ec_w : ∀ j w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    ec j w x ∈ (algebraMap (Oc j w) (FractionRing (Oc j w))).range

  V : ℕ → D.what₂.places.Pl → Type
  [acgV : ∀ j w, AddCommGroup (V j w)]
  [modV : ∀ j w, Module (FractionRing (Oc j w)) (V j w)]
  [modVO : ∀ j w, Module (Oc j w) (V j w)]
  [towV : ∀ j w, IsScalarTower (Oc j w) (FractionRing (Oc j w)) (V j w)]
  iV : ∀ j w, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[ec j w] V j w

  iV_basis : ∀ j w (b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)),
    LinearIndependent (FractionRing (Oc j w)) (fun a => iV j w (b a)) ∧
      Submodule.span (FractionRing (Oc j w)) (Set.range fun a => iV j w (b a)) = ⊤

  Qc : ℕ → D.what₂.places.Pl → Finset (PlE D.host)

  hL : ∀ j w, PlE D.host → ℕ → Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)

  hL_def : ∀ j w (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    GenAt D (D.what₂.places.resChar w) (Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
    ∀ x, (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j (hL j w v k x)) =
      NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x))

  hK : ∀ j w, PlE D.host → ℕ → Module.End (FractionRing (Oc j w)) (V j w)
  hK_def : ∀ j w v k x, hK j w v k (iV j w x) = iV j w (hL j w v k x)

  split : ∀ j w v k, GenAt D (D.what₂.places.resChar w) (Qc j w) v k →
    ⨆ μ, (hK j w v k).maxGenEigenspace μ = ⊤

  Qc_over : ∀ j w (v v' : PlE D.host), v ∈ Qc j w →
    (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ Qc j w

  Qc_conj : ∀ j w (v v' : PlE D.host), v' ∈ Qc j w → IsConjPl D.host v v' → v ∈ Qc j w

attribute [instance] NLocBase.ringOc NLocBase.domOc NLocBase.dvrOc NLocBase.acgV NLocBase.modV
  NLocBase.modVO NLocBase.towV

def heckeGens {D : D7} {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) :
    Set (Module.End (FractionRing (B.Oc j w)) (B.V j w)) :=
  {f | ∃ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k ∧ f = B.hK j w v k}

abbrev heckeAlg {D : D7} {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) :
    Subalgebra (B.Oc j w) (Module.End (FractionRing (B.Oc j w)) (B.V j w)) :=
  Algebra.adjoin (B.Oc j w) (heckeGens B j w)

set_option synthInstance.maxHeartbeats 400000 in

structure NormalizedLocalCompatibility (D : D7) (M : MtFam D) where
  B : NLocBase D M

  Q_eq : ∀ j w i, i ∈ D.nd.locs j w → D.nd.Q i = B.Qc j w

  mx : ∀ j w, D.nd.Loc → Ideal (heckeAlg B j w)
  mx_max : ∀ j w i, i ∈ D.nd.locs j w → (mx j w i).IsMaximal

  mx_inj : ∀ j w, Set.InjOn (mx j w) (D.nd.locs j w)

  mx_all : ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → ∀ I : Ideal (heckeAlg B j w), I.IsMaximal →
    ∃ i ∈ D.nd.locs j w, mx j w i = I

  phO : ∀ j w i, i ∈ D.nd.locs j w → D.nd.O i ≃+* B.Oc j w
  phK : ∀ j w i, i ∈ D.nd.locs j w → FractionRing (D.nd.O i) ≃+* FractionRing (B.Oc j w)
  phK_alg : ∀ j w i (h : i ∈ D.nd.locs j w) (z : D.nd.O i),
    phK j w i h (algebraMap _ _ z) = algebraMap _ _ (phO j w i h z)
  phK_emb : ∀ j w i (h : i ∈ D.nd.locs j w) (x : D.what₂.LL), phK j w i h (D.nd.embK i x) = B.ec j w x

  Psi : ∀ j w i (h : i ∈ D.nd.locs j w),
    TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) →ₛₗ[(phK j w i h).toRingHom] B.V j w
  Psi_inj : ∀ j w i (h : i ∈ D.nd.locs j w), Function.Injective (Psi j w i h)
  Psi_range : ∀ j w i (h : i ∈ D.nd.locs j w) (y : B.V j w),
    y ∈ NCov.part (heckeAlg B j w) (mx j w i) ↔ ∃ z, Psi j w i h z = y

  Psi_pr : ∀ j w i (h : i ∈ D.nd.locs j w) (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    Psi j w i h (D.nd.prMt i x) - B.iV j w (castMt D h x) ∈ NCov.off (heckeAlg B j w) (mx j w i)

  ptX : ∀ j w i (h : i ∈ D.nd.locs j w), D.nd.X i ≃
    {ψ : heckeAlg B j w →ₐ[B.Oc j w] B.Oc j w //
      NCov.cls ψ = mx j w i ∧ NCov.W (heckeAlg B j w) (NCov.pt ψ) ≠ ⊥}

  ptX_hT : ∀ j w i (h : i ∈ D.nd.locs j w) (x : D.nd.X i) (v : PlE D.host) (k : ℕ)
    (hvk : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k),
    phO j w i h ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) =
      (ptX j w i h x).1 ⟨B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩

  iotaC : ∀ j w, B.Oc j w →+* ℂ

  iotaC_coh : ∀ j w i (h : i ∈ D.nd.locs j w) (z : D.nd.O i), iotaOC D i z = iotaC j w (phO j w i h z)

def HeckeStd {D : D7} {M : MtFam D} (B : NLocBase D M) : Prop :=
  ∀ j w, 1 ≤ j → j ≤ D.R.m →
    (∀ v k v' k', GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k →
      GenAt D (D.what₂.places.resChar w) (B.Qc j w) v' k' → Commute (B.hK j w v k) (B.hK j w v' k')) ∧
    (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∀ μ, (B.hK j w v k).maxGenEigenspace μ ≠ ⊥ →
      μ ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range)

def LocPl (D : D7) (j : ℕ) (w : D.what₂.places.Pl) : Prop :=
  D.what₂.muAt w ≠ D.what₂.mu0 ∨ (D.nd.locs j w).Nonempty

theorem locPl_iff (D : D7) (hw : ∀ j w, (D.nd.locs j w).Nonempty → D.what₂.muAt w ≠ D.what₂.mu0) (j : ℕ)
    (w : D.what₂.places.Pl) : LocPl D j w ↔ D.what₂.muAt w ≠ D.what₂.mu0 :=
  ⟨fun h => h.elim id (hw j w), Or.inl⟩

theorem locPl_of_mem (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w) :
    LocPl D j w :=
  Or.inr ⟨i, h⟩

def HeckeStdTw {D : D7} {M : MtFam D} (B : NLocBase D M) : Prop :=
  ∀ j w, 1 ≤ j → j ≤ D.R.m → LocPl D j w →
    (∀ v k v' k', GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k →
      GenAt D (D.what₂.places.resChar w) (B.Qc j w) v' k' → Commute (B.hK j w v k) (B.hK j w v' k')) ∧
    (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∀ μ, (B.hK j w v k).maxGenEigenspace μ ≠ ⊥ →
      μ ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range)

theorem heckeStdTw_of_std {D : D7} {M : MtFam D} {B : NLocBase D M} (h : HeckeStd B) : HeckeStdTw B :=
  fun j w h1 h2 _ => h j w h1 h2

end Formalism.L2
