import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000 in

structure NChoice (D : D7) where

  twI : D.what₂.places.Pl → D.ntw.Tw
  twI_l : ∀ w, D.ntw.l (twI w) = D.what₂.places.resChar w
  sd : D.what₂.places.Pl → Bool

  Q : D.what₂.places.Pl → Finset (PlE D.host)
  k' : D.what₂.places.Pl → ℕ
  psi' : ∀ w, D.ntw.RCG (twI w) (Q w) →* (D.ntw.Ok (twI w) (k' w))ˣ

  Oe : D.what₂.places.Pl → Type
  [crOe : ∀ w, CommRing (Oe w)]
  [domOe : ∀ w, IsDomain (Oe w)]
  [dvrOe : ∀ w, IsDiscreteValuationRing (Oe w)]
  [algOe : ∀ w, Algebra (D.ntw.Ok (twI w) (k' w)) (Oe w)]
  [algOOe : ∀ w, Algebra (D.ntw.O (twI w)) (Oe w)]
  [towOe : ∀ w, IsScalarTower (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k' w)) (Oe w)]
  Oe_inj : ∀ w, Function.Injective (algebraMap (D.ntw.Ok (twI w) (k' w)) (Oe w))
  Oe_fin : ∀ w, Module.Finite (D.ntw.Ok (twI w) (k' w)) (Oe w)
  Oe_loc : ∀ w, IsLocalHom (algebraMap (D.ntw.Ok (twI w) (k' w)) (Oe w))

  embW : ∀ w, D.what₂.LL →+* FractionRing (Oe w)
  embW_w : ∀ w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    embW w x ∈ (algebraMap (Oe w) (FractionRing (Oe w))).range

  eMt : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[embW w]
    FractionRing (Oe w) ⊗[D.ntw.Ok (twI w) (k' w)]
      D.nexp.MtV (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w)))
  eMt_basis : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
    ∀ b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j),
    LinearIndependent (FractionRing (Oe w)) (fun i => eMt w j (b i)) ∧
      Submodule.span (FractionRing (Oe w)) (Set.range fun i => eMt w j (b i)) = ⊤
  eMt_lat : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → Submodule.span (Oe w)
      (eMt w j '' {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}) =
    Submodule.span (Oe w)
      ((TensorProduct.mk (D.ntw.Ok (twI w) (k' w)) (FractionRing (Oe w))
          (D.nexp.MtV (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w)))) 1) ''
        (D.nexp.MtLat (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w))) :
          Set (D.nexp.MtV (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w))))))

attribute [instance] NChoice.crOe NChoice.domOe NChoice.dvrOe NChoice.algOe NChoice.algOOe NChoice.towOe

set_option synthInstance.maxHeartbeats 400000 in

def NChoice.kMapE {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) :
    FractionRing (D.ntw.Ok (c.twI w) (c.k' w)) →+* FractionRing (c.Oe w) :=
  IsFractionRing.map (j := algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)) (c.Oe_inj w)

namespace NChoice

section OfOk

variable {K V : Type} [CommRing K] [IsDomain K] [AddCommGroup V] [Module (FractionRing K) V] [Module K V]
  [IsScalarTower K (FractionRing K) V]

def fracEquiv (K V : Type) [CommRing K] [IsDomain K] [AddCommGroup V] [Module (FractionRing K) V] [Module K V]
    [IsScalarTower K (FractionRing K) V] : FractionRing K ⊗[K] V ≃ₗ[FractionRing K] V :=
  haveI := isLocalizedModule_id (nonZeroDivisors K) V (FractionRing K)
  (IsLocalizedModule.isBaseChange (nonZeroDivisors K) (FractionRing K) (LinearMap.id : V →ₗ[K] V)).equiv

theorem fracEquiv_tmul (a : FractionRing K) (x : V) : fracEquiv K V (a ⊗ₜ x) = a • x := by
  simp [fracEquiv, IsBaseChange.equiv_tmul]

theorem fracEquiv_symm (x : V) : (fracEquiv K V).symm x = (1 : FractionRing K) ⊗ₜ x := by
  rw [LinearEquiv.symm_apply_eq, fracEquiv_tmul, one_smul]

def toFrac {L W : Type} [Field L] [AddCommGroup W] [Module L W] {σ : L →+* FractionRing K} (f : W →ₛₗ[σ] V) :
    W →ₛₗ[σ] FractionRing K ⊗[K] V :=
  (fracEquiv K V).symm.toLinearMap.comp f

theorem toFrac_apply {L W : Type} [Field L] [AddCommGroup W] [Module L W] {σ : L →+* FractionRing K}
    (f : W →ₛₗ[σ] V) (x : W) : toFrac f x = (fracEquiv K V).symm (f x) := rfl

theorem toFrac_basis {L W : Type} [Field L] [AddCommGroup W] [Module L W] {σ : L →+* FractionRing K}
    (f : W →ₛₗ[σ] V) {ι : Type} (v : ι → W)
    (h : LinearIndependent (FractionRing K) (fun i => f (v i)) ∧
      Submodule.span (FractionRing K) (Set.range fun i => f (v i)) = ⊤) :
    LinearIndependent (FractionRing K) (fun i => toFrac f (v i)) ∧
      Submodule.span (FractionRing K) (Set.range fun i => toFrac f (v i)) = ⊤ := by
  simp only [toFrac_apply]
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.map' (fracEquiv K V).symm.toLinearMap (fracEquiv K V).symm.ker, ?_⟩
  have h3 : (Set.range fun i => (fracEquiv K V).symm (f (v i))) =
      (fracEquiv K V).symm.toLinearMap '' Set.range fun i => f (v i) := by
    rw [← Set.range_comp]; rfl
  rw [h3, Submodule.span_image, h2, Submodule.map_top]
  exact LinearEquiv.range _

theorem toFrac_lat {L W : Type} [Field L] [AddCommGroup W] [Module L W] {σ : L →+* FractionRing K}
    (f : W →ₛₗ[σ] V) (S : Set W) (p : Submodule K V) (h : Submodule.span K (f '' S) = p) :
    Submodule.span K (toFrac f '' S) =
      Submodule.span K ((TensorProduct.mk K (FractionRing K) V 1) '' (p : Set V)) := by
  have h1 : toFrac f '' S = (TensorProduct.mk K (FractionRing K) V 1) '' (f '' S) := by
    rw [Set.image_image]
    exact Set.image_congr fun x _ => fracEquiv_symm (f x)
  rw [h1, Submodule.span_image, h, Submodule.span_image, Submodule.span_eq]

end OfOk

set_option synthInstance.maxHeartbeats 400000 in

def ofOk (D : D7) (twI : D.what₂.places.Pl → D.ntw.Tw) (twI_l : ∀ w, D.ntw.l (twI w) = D.what₂.places.resChar w)
    (sd : D.what₂.places.Pl → Bool) (Q : D.what₂.places.Pl → Finset (PlE D.host)) (k' : D.what₂.places.Pl → ℕ)
    (psi' : ∀ w, D.ntw.RCG (twI w) (Q w) →* (D.ntw.Ok (twI w) (k' w))ˣ)
    (embW : ∀ w, D.what₂.LL →+* FractionRing (D.ntw.Ok (twI w) (k' w)))
    (embW_w : ∀ w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
      embW w x ∈ (algebraMap (D.ntw.Ok (twI w) (k' w)) (FractionRing (D.ntw.Ok (twI w) (k' w)))).range)
    (eMt : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[embW w]
      D.nexp.MtV (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w))))
    (eMt_basis : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      ∀ b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
        D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j),
      LinearIndependent (FractionRing (D.ntw.Ok (twI w) (k' w))) (fun i => eMt w j (b i)) ∧
        Submodule.span (FractionRing (D.ntw.Ok (twI w) (k' w))) (Set.range fun i => eMt w j (b i)) = ⊤)
    (eMt_lat : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → Submodule.span (D.ntw.Ok (twI w) (k' w))
        (eMt w j '' {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}) =
      D.nexp.MtLat (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w)))) : NChoice D where
  twI := twI
  twI_l := twI_l
  sd := sd
  Q := Q
  k' := k'
  psi' := psi'
  Oe w := D.ntw.Ok (twI w) (k' w)
  Oe_inj _ := Function.injective_id
  Oe_fin _ := Module.Finite.self _
  Oe_loc _ := ⟨fun _ h => h⟩
  embW := embW
  embW_w := embW_w
  eMt w j := toFrac (eMt w j)
  eMt_basis w j h0 h1 h2 b := toFrac_basis (eMt w j) b (eMt_basis w j h0 h1 h2 b)
  eMt_lat w j h0 h1 h2 := toFrac_lat (eMt w j) _ _ (eMt_lat w j h0 h1 h2)

end NChoice

end Formalism.BasicNotions

end
