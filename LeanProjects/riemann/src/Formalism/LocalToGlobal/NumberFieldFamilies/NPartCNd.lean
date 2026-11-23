import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus
import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsTameGen
import Formalism.LocalRingCardinality.SpanPowerMembership.Places

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Module Module.End Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace Formalism.L2.Fam.NPC

section Gen

variable {R : Ranks} (H : Host R) (what₂ : Rows.Data R)

def exceptionalPlaces (l : ℕ) : Set (HeightOneSpectrum (𝓞 H.E)) :=
  {v | (v ∈ placesOver H.E (H.g 0) ∨ v ∈ placesOver H.E (H.g 1) ∨
      v ∈ placesOver H.E (if l = H.pde then H.pde' else H.pde)) ∧
    v ∉ placesOver H.E l}

def GenAt0 (l : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 H.E))) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) : Prop :=
  IsSplitPl H v ∧ v ∉ placesOver H.E l ∧ v ∉ exceptionalPlaces H l ∧ v ∉ Q ∧ 1 ≤ k ∧ k ≤ R.nV

set_option synthInstance.maxHeartbeats 400000 in

structure LocBase0 where
  Oc : ℕ → what₂.places.Pl → Type
  [ringOc : ∀ j w, CommRing (Oc j w)]
  [domOc : ∀ j w, IsDomain (Oc j w)]
  [dvrOc : ∀ j w, IsDiscreteValuationRing (Oc j w)]
  [algOc : ∀ j w, haveI : Fact (what₂.places.resChar w).Prime := ⟨what₂.places.resChar_prime w⟩
    Algebra ℤ_[what₂.places.resChar w] (Oc j w)]
  [finOc : ∀ j w, haveI : Fact (what₂.places.resChar w).Prime := ⟨what₂.places.resChar_prime w⟩
    Module.Finite ℤ_[what₂.places.resChar w] (Oc j w)]
  [topOc : ∀ j w, TopologicalSpace (Oc j w)]
  [trOc : ∀ j w, IsTopologicalRing (Oc j w)]
  Oc_adic : ∀ j w, IsAdic (IsLocalRing.maximalIdeal (Oc j w))
  Oc_complete : ∀ j w, IsAdicComplete (IsLocalRing.maximalIdeal (Oc j w)) (Oc j w)
  ec : ∀ j w, what₂.LL →+* FractionRing (Oc j w)
  ec_w : ∀ j w (x : what₂.LL), 0 ≤ what₂.places.val w x ↔
    ec j w x ∈ (algebraMap (Oc j w) (FractionRing (Oc j w))).range
  V : ℕ → what₂.places.Pl → Type
  [acgV : ∀ j w, AddCommGroup (V j w)]
  [modV : ∀ j w, Module (FractionRing (Oc j w)) (V j w)]
  [modVO : ∀ j w, Module (Oc j w) (V j w)]
  [towV : ∀ j w, IsScalarTower (Oc j w) (FractionRing (Oc j w)) (V j w)]
  iV : ∀ j w, what₂.MtL (what₂.muTw w) j →ₛₗ[ec j w] V j w
  iV_basis : ∀ j w (b : Module.Basis (Module.Free.ChooseBasisIndex what₂.LL (what₂.MtL (what₂.muTw w) j))
      what₂.LL (what₂.MtL (what₂.muTw w) j)),
    LinearIndependent (FractionRing (Oc j w)) (fun a => iV j w (b a)) ∧
      Submodule.span (FractionRing (Oc j w)) (Set.range fun a => iV j w (b a)) = ⊤
  Qw : what₂.places.Pl → Finset (HeightOneSpectrum (𝓞 H.E))
  hL : ∀ j w, HeightOneSpectrum (𝓞 H.E) → ℕ → Module.End what₂.LL (what₂.MtL (what₂.muTw w) j)
  hK : ∀ j w, HeightOneSpectrum (𝓞 H.E) → ℕ → Module.End (FractionRing (Oc j w)) (V j w)
  hK_def : ∀ j w v k x, hK j w v k (iV j w x) = iV j w (hL j w v k x)
  split : ∀ j w v k, GenAt0 H (what₂.places.resChar w) (Qw w) v k → ⨆ μ, (hK j w v k).maxGenEigenspace μ = ⊤

attribute [instance] LocBase0.ringOc LocBase0.domOc LocBase0.dvrOc LocBase0.topOc LocBase0.trOc LocBase0.acgV LocBase0.modV
  LocBase0.modVO LocBase0.towV

abbrev OmC : Type := AlgebraicClosure H.E

def PlOverEx : Prop := ∀ v : HeightOneSpectrum (𝓞 H.E), ∃ A : ValuationSubring (OmC H), IsPlaceOver A v

theorem plOverEx_holds : PlOverEx H := fun v => exists_isPlaceOver (OmC H) v

def plOmC (h : PlOverEx H) : Formalism.GaloisCohomology.Places H.E (OmC H) := ⟨fun v => (h v).choose, fun v => (h v).choose_spec⟩

def ldatC (h : PlOverEx H) (p : ℕ) [Fact p.Prime] : Formalism.GaloisCohomology.LData H.E (OmC H) p where
  S := (Formalism.GaloisCohomology.above_finite (F := H.E) p).toFinset
  hS := by simp
  A v := (plOmC H h).1 v.1
  hA v := (plOmC H h).2 v.1
  chi := (Formalism.GaloisCohomology.chi_exists (F := H.E) (Ω := OmC H) p _ (fun v hv => by
    simpa [Formalism.GaloisCohomology.Above] using hv)).choose
  hchi := (Formalism.GaloisCohomology.chi_exists (F := H.E) (Ω := OmC H) p _ (fun v hv => by
    simpa [Formalism.GaloisCohomology.Above] using hv)).choose_spec

def TameEx (h : PlOverEx H) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 H.E), ∃ γ : G H.E (OmC H), TameGenAt ((plOmC H h).1 v) γ

theorem tameEx_holds (h : PlOverEx H) : TameEx H h := fun v => by
  obtain ⟨p, hp, hmem⟩ := Formalism.BasicNotions.Examples₂.PlacesToy.exists_prime_mem v
  have hlt : ((plOmC H h).1 v).valuation ((p : ℕ) : OmC H) < 1 := by
    have := (((plOmC H h).2 v) ((p : ℕ) : 𝓞 H.E)).mpr hmem
    simpa using this
  exact Formalism.BasicNotions.Examples₂.Tame.exists_tameGen _ p hp.ne_zero hlt

def gamW (h : PlOverEx H) (v : HeightOneSpectrum (𝓞 H.E)) : G H.E (OmC H) := by
  classical
  exact if hv : ∃ γ : G H.E (OmC H), TameGenAt ((plOmC H h).1 v) γ then hv.choose else 1

theorem gamW_mem (h : PlOverEx H) (v : HeightOneSpectrum (𝓞 H.E)) : gamW H h v ∈ Ine (F := H.E) ((plOmC H h).1 v) := by
  classical
  unfold gamW
  split_ifs with hv
  · exact hv.choose_spec.1
  · exact one_mem _

theorem gamW_gen (h : PlOverEx H) (ht : TameEx H h) (v : HeightOneSpectrum (𝓞 H.E)) :
    TameGenAt ((plOmC H h).1 v) (gamW H h v) := by
  classical
  unfold gamW
  rw [dif_pos (ht v)]
  exact (ht v).choose_spec

theorem placesOver_fin (p : ℕ) (hp : p.Prime) : (placesOver H.E p).Finite := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact Formalism.GaloisCohomology.above_finite (F := H.E) p

theorem exceptional_places_finite (l : ℕ) : (exceptionalPlaces H l).Finite := by
  refine (((placesOver_fin H _ (H.g_prime 0)).union (placesOver_fin H _ (H.g_prime 1))).union
    (placesOver_fin H (if l = H.pde then H.pde' else H.pde) (by split_ifs; exacts [H.pde'_prime, H.pde_prime]))).subset ?_
  rintro v ⟨hv | hv | hv, -⟩
  · exact Or.inl (Or.inl hv)
  · exact Or.inl (Or.inr hv)
  · exact Or.inr hv

def PlGC (k : Fin 2) : Type :=
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield H.E)) // ((H.g k : ℕ) : 𝓞 (maximalRealSubfield H.E)) ∈ v.asIdeal}

def PlGFin : Prop := ∀ k, Finite (PlGC H k)

theorem plGFin_holds : PlGFin H := fun k => by
  haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  exact (Formalism.GaloisCohomology.above_finite (F := maximalRealSubfield H.E) (H.g k)).to_subtype

variable {H what₂} (B : LocBase0 H what₂)

abbrev heckeAlg0 (j : ℕ) (w : what₂.places.Pl) :
    Subalgebra (B.Oc j w) (Module.End (FractionRing (B.Oc j w)) (B.V j w)) :=
  Algebra.adjoin (B.Oc j w) {f | ∃ v k, GenAt0 H (what₂.places.resChar w) (B.Qw w) v k ∧ f = B.hK j w v k}

def LocT : Type :=
  Σ jw : ℕ × what₂.places.Pl, {I : Ideal (heckeAlg0 B jw.1 jw.2) //
    I.IsMaximal ∧ 1 ≤ jw.1 ∧ jw.1 ≤ R.m ∧ what₂.muAt jw.2 ≠ what₂.mu0}

abbrev jOf (i : LocT B) : ℕ := i.1.1

abbrev wOf (i : LocT B) : what₂.places.Pl := i.1.2

abbrev lOf (i : LocT B) : ℕ := what₂.places.resChar (wOf B i)

abbrev OOf (i : LocT B) : Type := B.Oc (jOf B i) (wOf B i)

abbrev hAlg (i : LocT B) := heckeAlg0 B (jOf B i) (wOf B i)

def LocsFin : Prop := ∀ j w, Set.Finite {i : LocT B | jOf B i = j ∧ wOf B i = w}

def locsC (hF : LocsFin B) (j : ℕ) (w : what₂.places.Pl) : Finset (LocT B) := (hF j w).toFinset

theorem locsC_mem (hF : LocsFin B) (j : ℕ) (w : what₂.places.Pl) (i : LocT B) :
    i ∈ locsC B hF j w ↔ jOf B i = j ∧ wOf B i = w := by
  simp [locsC]

def XOf (i : LocT B) : Type :=
  {ψ : hAlg B i →ₐ[OOf B i] OOf B i // NCov.cls ψ = i.2.1 ∧ NCov.W (hAlg B i) (NCov.pt ψ) ≠ ⊥}

def hTfun (i : LocT B) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) : XOf B i → OOf B i := by
  classical
  exact if h : GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k then
    fun x => x.1 ⟨B.hK (jOf B i) (wOf B i) v k, Algebra.subset_adjoin ⟨v, k, h, rfl⟩⟩ else 0

def TOf (i : LocT B) : Subalgebra (OOf B i) (XOf B i → OOf B i) :=
  Algebra.adjoin (OOf B i) {f | ∃ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k ∧ f = hTfun B i v k}

def hTOf (i : LocT B) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) : TOf B i := by
  classical
  exact if h : GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k then
    ⟨hTfun B i v k, Algebra.subset_adjoin ⟨v, k, h, rfl⟩⟩ else 0

def partOf (i : LocT B) : Submodule (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i)) := NCov.part (hAlg B i) i.2.1

def offOf (i : LocT B) : Submodule (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i)) := NCov.off (hAlg B i) i.2.1

def PartCompl : Prop := ∀ i : LocT B, IsCompl (partOf B i) (offOf B i)

def projOf (hC : PartCompl B) (i : LocT B) : B.V (jOf B i) (wOf B i) →ₗ[FractionRing (OOf B i)] partOf B i :=
  Submodule.linearProjOfIsCompl _ _ (hC i)

def latL (i : LocT B) : Set (what₂.MtL (what₂.muTw (wOf B i)) (jOf B i)) :=
  {x | what₂.jMt (what₂.muTw (wOf B i)) (jOf B i) x ∈ (what₂.MtLat (what₂.muTw (wOf B i)) (jOf B i)).gen}

def MtSub (hC : PartCompl B) (i : LocT B) : Submodule (OOf B i) (partOf B i) :=
  Submodule.span (OOf B i) ((fun x => projOf B hC i (B.iV (jOf B i) (wOf B i) x)) '' latL B i)

def MtLoc (hC : PartCompl B) : Prop :=
  ∀ i : LocT B, IsLocalizedModule (nonZeroDivisors (OOf B i)) (MtSub B hC i).subtype

def mtEquiv (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) :
    TensorProduct (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) ≃ₗ[FractionRing (OOf B i)] partOf B i :=
  haveI := hL i
  (IsLocalizedModule.isBaseChange (nonZeroDivisors (OOf B i)) (FractionRing (OOf B i)) (MtSub B hC i).subtype).equiv

def prMtC (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) :
    what₂.MtL (what₂.muTw (wOf B i)) (jOf B i) →ₛₗ[B.ec (jOf B i) (wOf B i)]
      TensorProduct (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) :=
  ((mtEquiv B hC hL i).symm.toLinearMap.comp (projOf B hC i)).comp (B.iV (jOf B i) (wOf B i))

end Gen

end Formalism.L2.Fam.NPC
