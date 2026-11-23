import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocI
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.IsLocalRingOfComplete

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Formalism.BasicNotions.Loc TensorProduct

namespace Formalism.L2.Fam.NPC.BaseC

variable {R : Ranks} (H : Host R) (what₂ : Rows.Data R)

instance factRes (w : what₂.places.Pl) : Fact (what₂.places.resChar w).Prime := ⟨what₂.places.resChar_prime w⟩

structure PlEmb where
  emb : ∀ w : what₂.places.Pl, what₂.LL →+* PadicAlgCl (what₂.places.resChar w)
  emb_w : ∀ w (x : what₂.LL), 0 ≤ what₂.places.val w x ↔ ‖emb w x‖ ≤ 1

structure CoefIn where
  E : PlEmb what₂
  Kx : ∀ (_j : ℕ) (w : what₂.places.Pl), FinExt (what₂.places.resChar w)
  hKx : ∀ j w (x : what₂.LL), E.emb w x ∈ (Kx j w).1

variable {what₂} (X : CoefIn what₂)

def OcC (j : ℕ) (w : what₂.places.Pl) : Type := ↥(OL (X.Kx j w))

instance (j w) : CommRing (OcC X j w) := inferInstanceAs (CommRing ↥(OL (X.Kx j w)))
instance (j w) : IsDomain (OcC X j w) := inferInstanceAs (IsDomain ↥(OL (X.Kx j w)))
instance (j w) : IsDiscreteValuationRing (OcC X j w) := inferInstanceAs (IsDiscreteValuationRing ↥(OL (X.Kx j w)))
instance (j w) : Algebra ℤ_[what₂.places.resChar w] (OcC X j w) := inferInstanceAs (Algebra ℤ_[what₂.places.resChar w] ↥(OL (X.Kx j w)))
instance (j w) : Module.Finite ℤ_[what₂.places.resChar w] (OcC X j w) :=
  inferInstanceAs (Module.Finite ℤ_[what₂.places.resChar w] ↥(OL (X.Kx j w)))
instance (j w) : TopologicalSpace (OcC X j w) := inferInstanceAs (TopologicalSpace ↥(OL (X.Kx j w)))
instance (j w) : IsTopologicalRing (OcC X j w) := inferInstanceAs (IsTopologicalRing ↥(OL (X.Kx j w)))

theorem oc_adic (j w) : IsAdic (IsLocalRing.maximalIdeal (OcC X j w)) := Formalism.BasicNotions.Examples₂.LB.OL_adic (X.Kx j w)

theorem oc_complete (j w) : IsAdicComplete (IsLocalRing.maximalIdeal (OcC X j w)) (OcC X j w) :=
  Formalism.L2.G.IntCl.complete ℤ_[what₂.places.resChar w] ℚ_[what₂.places.resChar w] ↥(X.Kx j w).1 inferInstance

def ecC (j : ℕ) (w : what₂.places.Pl) : what₂.LL →+* FractionRing (OcC X j w) :=
  Formalism.BasicNotions.Examples₂.TwB.embF (X.Kx j w) (X.E.emb w) (X.hKx j w)

theorem ecC_w (j : ℕ) (w : what₂.places.Pl) (x : what₂.LL) :
    0 ≤ what₂.places.val w x ↔ ecC X j w x ∈ (algebraMap (OcC X j w) (FractionRing (OcC X j w))).range := by
  rw [X.E.emb_w]
  constructor
  · intro hx
    have hm : Formalism.BasicNotions.Examples₂.TwB.phiL (X.Kx j w) (X.E.emb w) (X.hKx j w) x ∈ OL (X.Kx j w) :=
      (Formalism.BasicNotions.Examples₂.LB.mem_OL (X.Kx j w) _).mpr hx
    exact ⟨⟨_, hm⟩, (Formalism.BasicNotions.Examples₂.LB.toFrac_eq_iff (X.Kx j w) _ ⟨_, hm⟩).mpr rfl⟩
  · rintro ⟨a, ha⟩
    have h1 := (Formalism.BasicNotions.Examples₂.LB.toFrac_eq_iff (X.Kx j w) _ a).mp ha
    have h2 := (Formalism.BasicNotions.Examples₂.LB.mem_OL (X.Kx j w) _).mp a.2
    rw [h1] at h2
    exact h2

instance algLL (j : ℕ) (w : what₂.places.Pl) : Algebra what₂.LL (FractionRing (OcC X j w)) := (ecC X j w).toAlgebra

def VC (j : ℕ) (w : what₂.places.Pl) : Type := FractionRing (OcC X j w) ⊗[what₂.LL] what₂.MtL (what₂.muTw w) j

instance (j w) : AddCommGroup (VC X j w) := inferInstanceAs (AddCommGroup (FractionRing (OcC X j w) ⊗[what₂.LL] what₂.MtL (what₂.muTw w) j))
instance modK (j w) : Module (FractionRing (OcC X j w)) (VC X j w) :=
  inferInstanceAs (Module (FractionRing (OcC X j w)) (FractionRing (OcC X j w) ⊗[what₂.LL] what₂.MtL (what₂.muTw w) j))
instance modO (j w) : Module (OcC X j w) (VC X j w) := Module.compHom (VC X j w) (algebraMap (OcC X j w) (FractionRing (OcC X j w)))
instance towO (j w) : IsScalarTower (OcC X j w) (FractionRing (OcC X j w)) (VC X j w) where
  smul_assoc a k v := by
    change (a • k) • v = algebraMap (OcC X j w) (FractionRing (OcC X j w)) a • (k • v)
    rw [Algebra.smul_def, mul_smul]

def iVC (j : ℕ) (w : what₂.places.Pl) : what₂.MtL (what₂.muTw w) j →ₛₗ[ecC X j w] VC X j w where
  toFun x := (1 : FractionRing (OcC X j w)) ⊗ₜ[what₂.LL] x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change (1 : FractionRing (OcC X j w)) ⊗ₜ[what₂.LL] (c • x) = ecC X j w c • ((1 : FractionRing (OcC X j w)) ⊗ₜ[what₂.LL] x)
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
    rfl

theorem iVC_basis (j : ℕ) (w : what₂.places.Pl)
    (b : Module.Basis (Module.Free.ChooseBasisIndex what₂.LL (what₂.MtL (what₂.muTw w) j)) what₂.LL (what₂.MtL (what₂.muTw w) j)) :
    LinearIndependent (FractionRing (OcC X j w)) (fun a => iVC X j w (b a)) ∧
      Submodule.span (FractionRing (OcC X j w)) (Set.range fun a => iVC X j w (b a)) = ⊤ := by
  have e : (fun a => iVC X j w (b a)) = fun a => b.baseChange (FractionRing (OcC X j w)) a := by
    funext a
    rw [Module.Basis.baseChange_apply]
    rfl
  rw [e]
  exact ⟨(b.baseChange _).linearIndependent, (b.baseChange _).span_eq⟩

end Formalism.L2.Fam.NPC.BaseC
