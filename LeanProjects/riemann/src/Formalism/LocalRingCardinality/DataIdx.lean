import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataNChoice

noncomputable section

namespace Formalism.BasicNotions.Idx

open NumberField IsDedekindDomain Formalism.BasicNotions

variable (D : D7)

instance modO (μ : D.what₂.Tup) (j : ℕ) : Module (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  Module.compHom _ (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)

theorem smul_def (μ : D.what₂.Tup) (j : ℕ) (s : 𝓞 D.what₂.LL) (x : D.what₂.MtL μ j) :
    s • x = (s : D.what₂.LL) • x := rfl

instance towO (μ : D.what₂.Tup) (j : ℕ) : IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL (D.what₂.MtL μ j) :=
  ⟨fun a b x => by rw [smul_def, Algebra.smul_def, mul_smul]⟩

def TjL (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  Submodule.span (𝓞 D.what₂.LL) {x | D.what₂.jMt μ j x ∈ D.what₂.TjSet μ j}

def TjV (μ : D.what₂.Tup) (j : ℕ) : Submodule D.what₂.LL (D.what₂.MtL μ j) :=
  Submodule.span D.what₂.LL (TjL D μ j : Set (D.what₂.MtL μ j))

def TjDual (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) where
  carrier := {x | x ∈ TjV D μ j ∧ ∀ a ∈ TjL D μ j, ∃ c : 𝓞 D.what₂.LL,
    inner ℂ (D.what₂.jMt μ j a) (D.what₂.jMt μ j x) = D.what₂.embLL (c : D.what₂.LL)}
  add_mem' := by
    rintro x y ⟨hx, h1⟩ ⟨hy, h2⟩
    refine ⟨(TjV D μ j).add_mem hx hy, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    obtain ⟨d, hd⟩ := h2 a ha
    exact ⟨c + d, by rw [map_add, inner_add_right, hc, hd]; simp⟩
  zero_mem' := ⟨(TjV D μ j).zero_mem, fun a _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro s x ⟨hx, h1⟩
    refine ⟨by rw [smul_def]; exact (TjV D μ j).smul_mem _ hx, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    exact ⟨s * c, by rw [smul_def, LinearMap.map_smulₛₗ, inner_smul_right, hc]; simp⟩

variable {D} (X : DivX D)

def thImg (μ : D.what₂.Tup) (j : ℕ) (A : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j)) :
    Submodule (𝓞 D.what₂.LL) (X.MjH j).V where
  carrier := {y | ∃ x ∈ A, X.jM j y = D.what₂.thetaP μ j (D.what₂.jMt μ j x)}
  add_mem' := by
    rintro a b ⟨x, hx, h1⟩ ⟨y, hy, h2⟩
    exact ⟨x + y, A.add_mem hx hy, by rw [map_add, map_add, map_add, h1, h2]⟩
  zero_mem' := ⟨0, A.zero_mem, by simp⟩
  smul_mem' := by
    rintro s a ⟨x, hx, h1⟩
    refine ⟨s • x, A.smul_mem s hx, ?_⟩
    rw [smul_def, ← algebraMap_smul D.what₂.LL s a, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1,
      LinearMap.map_smul]

def thTj (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (X.MjH j).V := thImg X μ j (TjL D μ j)

def IjIdx (μ : D.what₂.Tup) (j : ℕ) (w : D.what₂.places.Pl) : ℤ :=
  Formalism.HermitianLatticesTheory.lidx (D.plEq w).asIdeal (X.MjH j).L (thTj X μ j)

variable (D) in

def jwIdx (μ : D.what₂.Tup) (j : ℕ) (w : D.what₂.places.Pl) : ℤ :=
  Formalism.HermitianLatticesTheory.lidx (D.plEq w).asIdeal (TjL D μ j) (TjDual D μ j)

end Formalism.BasicNotions.Idx

namespace Formalism.BasicNotions

structure IdxDefs (D : D7) (X : DivX D) : Prop where
  Ij_def : ∀ μ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.Ij μ j w = Idx.IjIdx X μ j w
  jw_def : ∀ μ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.jw μ j w = Idx.jwIdx D μ j w

end Formalism.BasicNotions

namespace Formalism.BasicNotions.Idx

open NumberField IsDedekindDomain Formalism.BasicNotions

variable (D : D7)

def HermRat : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ x y : D.what₂.MtL μ j,
    ∃ c : D.what₂.LL, D.what₂.embLL c = inner ℂ (D.what₂.jMt μ j x) (D.what₂.jMt μ j y)

def PrRat : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ x : D.what₂.MtL μ j,
    ∃ y, D.what₂.jMt μ j y = D.what₂.eMt μ j ((D.what₂.Zj μ j).starProjection (D.what₂.jMt μ j x))

def Z0 (μ : D.what₂.Tup) (j : ℕ) : Submodule ℂ (D.what₂.Mt μ j) :=
  (LinearMap.ker (D.what₂.thetaP μ j))ᗮ ⊓ LinearMap.range (D.what₂.eMt μ j)

def ProjectionIsSpectralProjector : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ x : D.what₂.Mt μ j,
    D.what₂.eMt μ j ((D.what₂.Zj μ j).starProjection x) = (Z0 D μ j).starProjection x

def ThetaBij : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → Function.Bijective ((D.what₂.thetaP μ j).domRestrict (Z0 D μ j))

open Classical in

def hLL (μ : D.what₂.Tup) (j : ℕ) (x y : D.what₂.MtL μ j) : D.what₂.LL :=
  if h : ∃ c : D.what₂.LL, D.what₂.embLL c = inner ℂ (D.what₂.jMt μ j x) (D.what₂.jMt μ j y) then h.choose else 0

theorem hLL_spec (h : HermRat D) (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (x y : D.what₂.MtL μ j) :
    D.what₂.embLL (hLL D μ j x y) = inner ℂ (D.what₂.jMt μ j x) (D.what₂.jMt μ j y) := by
  unfold hLL
  rw [dif_pos (h μ j h1 h2 x y)]
  exact (h μ j h1 h2 x y).choose_spec

def gramDet (μ : D.what₂.Tup) (j : ℕ) {n : ℕ} (b : Fin n → D.what₂.MtL μ j) : D.what₂.LL :=
  (Matrix.of fun i k => hLL D μ j (b i) (b k)).det

def IsLocBasis {V : Type} [AddCommGroup V] [Module D.what₂.LL V] [Module (𝓞 D.what₂.LL) V]
    (A : Submodule (𝓞 D.what₂.LL) V) (w : D.what₂.places.Pl) {n : ℕ} (b : Fin n → V) : Prop :=
  LinearIndependent D.what₂.LL b ∧
    Formalism.HermitianLatticesTheory.loc (K := D.what₂.LL) (D.plEq w).asIdeal (Submodule.span (𝓞 D.what₂.LL) (Set.range b)) =
      Formalism.HermitianLatticesTheory.loc (K := D.what₂.LL) (D.plEq w).asIdeal A

def FactGram : Prop :=
  HermRat D → ∀ μ j w, 1 ≤ j → j ≤ D.R.m → (TjL D μ j).FG →
    ∀ (n : ℕ) (b : Fin n → D.what₂.MtL μ j), IsLocBasis D (TjL D μ j) w b →
      vAdd (D.plEq w) (gramDet D μ j b) = - jwIdx D μ j w

def FactJwConj : Prop :=
  HermRat D → ∀ μ j w, 1 ≤ j → j ≤ D.R.m → (TjL D μ j).FG →
    jwIdx D μ j (D.what₂.places.conj w) = jwIdx D μ j w

variable {D} (X : DivX D)

def ThetaRat : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ x : D.what₂.MtL μ j,
    ∃ y, X.jM j y = D.what₂.thetaP μ j (D.what₂.jMt μ j x)

def FullRank : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → (TjL D μ j).FG ∧ (thTj X μ j).FG ∧
    Submodule.span D.what₂.LL (thTj X μ j : Set (X.MjH j).V) = ⊤

theorem jM_inj (j : ℕ) : Function.Injective (X.jM j) :=
  inj_of_li D.what₂.embLL (X.jM j) (X.MjH j).b (X.jM_basis j).1

def thetaL (μ : D.what₂.Tup) (j : ℕ)
    (h : ∀ x : D.what₂.MtL μ j, ∃ y, X.jM j y = D.what₂.thetaP μ j (D.what₂.jMt μ j x)) :
    D.what₂.MtL μ j →ₗ[D.what₂.LL] (X.MjH j).V :=
  descend (D.what₂.jMt μ j) (X.jM j) (jM_inj X j) (D.what₂.thetaP μ j) h

theorem thetaL_spec (μ : D.what₂.Tup) (j : ℕ)
    (h : ∀ x : D.what₂.MtL μ j, ∃ y, X.jM j y = D.what₂.thetaP μ j (D.what₂.jMt μ j x)) (x : D.what₂.MtL μ j) :
    X.jM j (thetaL X μ j h x) = D.what₂.thetaP μ j (D.what₂.jMt μ j x) :=
  descend_spec (D.what₂.jMt μ j) (X.jM j) (jM_inj X j) (D.what₂.thetaP μ j) h x

theorem thImg_eq_map (μ : D.what₂.Tup) (j : ℕ)
    (h : ∀ x : D.what₂.MtL μ j, ∃ y, X.jM j y = D.what₂.thetaP μ j (D.what₂.jMt μ j x))
    (A : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j)) :
    thImg X μ j A = A.map ((thetaL X μ j h).restrictScalars (𝓞 D.what₂.LL)) := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx, jM_inj X j (by rw [hy]; exact thetaL_spec X μ j h x)⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, thetaL_spec X μ j h x⟩

def FactStepBz : Prop :=
  ThetaRat X → ∀ μ j w, 1 ≤ j → j ≤ D.R.m →
    ∀ (n : ℕ) (b : Fin n → D.what₂.MtL μ j) (b0 : Fin n → D.what₂.MtL D.what₂.mu0 j)
      (Z : Matrix (Fin n) (Fin n) D.what₂.LL),
      IsLocBasis D (TjL D μ j) w b → IsLocBasis D (TjL D D.what₂.mu0 j) w b0 →
      LinearIndependent ℂ (fun k => D.what₂.thetaP D.what₂.mu0 j (D.what₂.jMt D.what₂.mu0 j (b0 k))) →
      Submodule.span ℂ (Set.range fun k => D.what₂.thetaP D.what₂.mu0 j (D.what₂.jMt D.what₂.mu0 j (b0 k))) = ⊤ →
      LinearIndependent ℂ (fun k => D.what₂.thetaP μ j (D.what₂.jMt μ j (b k))) →
      (∀ i, D.what₂.thetaP μ j (D.what₂.jMt μ j (b i)) =
        ∑ k, D.what₂.embLL (Z k i) • D.what₂.thetaP D.what₂.mu0 j (D.what₂.jMt D.what₂.mu0 j (b0 k))) →
      vAdd (D.plEq w) Z.det = IjIdx X μ j w - IjIdx X D.what₂.mu0 j w

end Formalism.BasicNotions.Idx

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain

def bridge_lidx_det : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V)
    (γ : V ≃ₗ[K] V), Submodule.IsLattice K A →
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (A.map ((γ : V →ₗ[K] V).restrictScalars (𝓞 K))) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B →
    Formalism.HermitianLatticesTheory.lidx w.asIdeal A B = vAdd w (LinearMap.det (γ : V →ₗ[K] V))

end Formalism.BasicNotions

namespace Formalism.BasicNotions.Idx

open NumberField IsDedekindDomain Formalism.BasicNotions

theorem IjIdx_of_subsingleton {D : D7} (X : DivX D) (μ : D.what₂.Tup) (j : ℕ) (w : D.what₂.places.Pl)
    [Subsingleton (X.MjH j).V] : IjIdx X μ j w = 0 := by
  have h : (X.MjH j).L = thTj X μ j := SetLike.ext fun x => by
    rw [Subsingleton.elim x 0]; exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  unfold IjIdx Formalism.HermitianLatticesTheory.lidx
  rw [h]; exact sub_self _

theorem jwIdx_of_subsingleton (D : D7) (μ : D.what₂.Tup) (j : ℕ) (w : D.what₂.places.Pl)
    [Subsingleton (D.what₂.MtL μ j)] : jwIdx D μ j w = 0 := by
  have h : TjL D μ j = TjDual D μ j := SetLike.ext fun x => by
    rw [Subsingleton.elim x 0]; exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  unfold jwIdx Formalism.HermitianLatticesTheory.lidx
  rw [← h]; exact sub_self _

end Formalism.BasicNotions.Idx

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

namespace NForms

variable (D : D7)

def eG (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) (D.nexp.eAlg i b)

def Fm0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  ⨅ u : D.nexp.U, LinearMap.ker ((D.nexp.actG i j b u).toLinearMap -
    ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • LinearMap.id)

def V0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  (Fm0 D i j b).map (eG D i j b)

def IsLatIn {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (M V : Submodule R W) : Prop :=
  M.FG ∧ M ≤ V ∧ ∀ x ∈ V, ∃ c : R, c ≠ 0 ∧ c • x ∈ M

end NForms

set_option synthInstance.maxHeartbeats 400000 in

def NChoice.thPe (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) :
    FractionRing (c.Oe w) ⊗[D.ntw.Ok (c.twI w) (c.k' w)]
        D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))) →ₗ[FractionRing (c.Oe w)]
      FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
      (FractionRing (c.Oe w)) (FractionRing (c.Oe w)) (D.nexp.Fm (c.twI w) j (c.sd w))).toLinearMap ∘ₗ
    (D.nexp.thP (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))).baseChange
      (FractionRing (c.Oe w))

set_option synthInstance.maxHeartbeats 400000 in

def NChoice.toFracE (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) :
    c.Oe w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w) →ₗ[D.ntw.O (c.twI w)]
      FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w) :=
  ((Algebra.linearMap (c.Oe w) (FractionRing (c.Oe w))).restrictScalars (D.ntw.O (c.twI w))).rTensor _

set_option synthInstance.maxHeartbeats 400000 in

theorem NChoice.thPe_one (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (m : D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))) :
    NChoice.thPe D c w j ((1 : FractionRing (c.Oe w)) ⊗ₜ m) =
      ((Algebra.linearMap (D.ntw.Ok (c.twI w) (c.k' w)) (FractionRing (c.Oe w))).restrictScalars (D.ntw.O (c.twI w))).rTensor
        (D.nexp.Fm (c.twI w) j (c.sd w))
        (D.nexp.thP (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))) m) := by
  simp only [NChoice.thPe, LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe]
  induction (D.nexp.thP (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))) m)
    using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul]
    simp [Algebra.smul_def]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]

set_option synthInstance.maxHeartbeats 400000 in

structure NMj (D : D7) (X : DivX D) (c : NChoice D) where

  eMj : ∀ w j, (X.MjH j).V →+ (c.Oe w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w))

  eMj_smul : ∀ w j (a : D.what₂.LL) (r : c.Oe w) (x : (X.MjH j).V),
    c.embW w a = algebraMap (c.Oe w) (FractionRing (c.Oe w)) r →
    eMj w j (a • x) = r • eMj w j x

  eMj_li : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
    LinearIndependent (c.Oe w) (fun a => eMj w j ((X.MjH j).b a))

  eMj_lat : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
    NForms.IsLatIn (Submodule.span (c.Oe w) (eMj w j '' ((X.MjH j).L : Set (X.MjH j).V)))
      (((NForms.V0 D (c.twI w) j (c.sd w)).restrictScalars (D.ntw.O (c.twI w))).baseChange (c.Oe w))

  eMj_th : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → ∀ x ∈ Idx.TjV D (D.what₂.muTw w) j, ∀ y : (X.MjH j).V,
    X.jM j y = D.what₂.thetaP (D.what₂.muTw w) j (D.what₂.jMt (D.what₂.muTw w) j x) →
    NChoice.toFracE D c w j (eMj w j y) = NChoice.thPe D c w j (c.eMt w j x)

namespace NMj

variable {D : D7} {X : DivX D} {c : NChoice D} (T : NMj D X c)

set_option synthInstance.maxHeartbeats 400000 in

def SupTie : Prop :=
  ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
    Submodule.span (c.Oe w) (T.eMj w j '' ((X.MjH j).L : Set (X.MjH j).V)) =
      (D.nexp.Bsup (c.twI w) j (c.sd w) ⊓
        (NForms.V0 D (c.twI w) j (c.sd w)).restrictScalars (D.ntw.O (c.twI w))).baseChange (c.Oe w)

end NMj

set_option synthInstance.maxHeartbeats 400000 in

def NCutCompat (D : D7) (c : NChoice D) : Prop :=
  ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → ∀ x x' : D.what₂.MtL (D.what₂.muTw w) j,
    D.what₂.jMt (D.what₂.muTw w) j x' = D.what₂.eMt (D.what₂.muTw w) j
      ((D.what₂.Zj (D.what₂.muTw w) j).starProjection (D.what₂.jMt (D.what₂.muTw w) j x)) →
    NChoice.thPe D c w j (c.eMt w j x') =
      (((NForms.eG D (c.twI w) j (c.sd w)).restrictScalars (D.ntw.O (c.twI w))).baseChange
        (FractionRing (c.Oe w))) (NChoice.thPe D c w j (c.eMt w j x))

end Formalism.BasicNotions

end
