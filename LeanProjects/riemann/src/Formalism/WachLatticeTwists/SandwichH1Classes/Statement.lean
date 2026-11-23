import Formalism.WachLatticeTwists.HodgeTateChains.CorrectedHypothesisWConsequences

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

section H1

variable {ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module ℤ_[ℓ] M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul ℤ_[ℓ] M]
  {M' : Type} [AddCommGroup M'] [Module ℤ_[ℓ] M'] [TopologicalSpace M'] [ContinuousAdd M']
  [ContinuousConstSMul ℤ_[ℓ] M']

def Z1 (a : Representation ℤ_[ℓ] G M) : Submodule ℤ_[ℓ] (G → M) where
  carrier := {c | Continuous c ∧ ∀ g h, c (g * h) = c g + a g (c h)}
  add_mem' := by
    rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
    refine ⟨hc.add hd, fun g h => ?_⟩
    simp only [Pi.add_apply, hc', hd', map_add]
    abel
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  smul_mem' := by
    rintro t c ⟨hc, hc'⟩
    exact ⟨hc.const_smul t, fun g h => by simp only [Pi.smul_apply, hc', smul_add, map_smul]⟩

def B1 (a : Representation ℤ_[ℓ] G M) : Submodule ℤ_[ℓ] (G → M) :=
  LinearMap.range (LinearMap.pi fun g => a g - LinearMap.id : M →ₗ[ℤ_[ℓ]] (G → M))

abbrev H1 (a : Representation ℤ_[ℓ] G M) : Type := Z1 a ⧸ (B1 a).comap (Z1 a).subtype

def H1.mk (a : Representation ℤ_[ℓ] G M) : Z1 a →ₗ[ℤ_[ℓ]] H1 a := Submodule.mkQ _

structure EqMap (a : Representation ℤ_[ℓ] G M) (a' : Representation ℤ_[ℓ] G M') where
  f : M →ₗ[ℤ_[ℓ]] M'
  cont : Continuous f
  eqv : ∀ g m, f (a g m) = a' g (f m)

def EqMap.onZ {a : Representation ℤ_[ℓ] G M} {a' : Representation ℤ_[ℓ] G M'} (F : EqMap a a') :
    Z1 a →ₗ[ℤ_[ℓ]] Z1 a' :=
  (F.f.compLeft G).restrict (by
    rintro c ⟨hc, hc'⟩
    refine ⟨F.cont.comp hc, fun g h => ?_⟩
    simp only [LinearMap.compLeft_apply, Function.comp_apply, hc', map_add, F.eqv])

def EqMap.onH {a : Representation ℤ_[ℓ] G M} {a' : Representation ℤ_[ℓ] G M'} (F : EqMap a a') :
    H1 a →ₗ[ℤ_[ℓ]] H1 a' :=
  Submodule.mapQ _ _ F.onZ (by
    rintro c ⟨m, hm⟩
    refine ⟨F.f m, ?_⟩
    funext g
    have := congrFun hm g
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Submodule.subtype_apply]
      at this ⊢
    show a' g (F.f m) - F.f m = F.f (c.1 g)
    rw [← this, map_sub, F.eqv])

def H1.res {G' : Type} [Group G'] [TopologicalSpace G'] (a : Representation ℤ_[ℓ] G M) (p : G' →* G)
    (hp : Continuous p) : H1 a →ₗ[ℤ_[ℓ]] H1 (a.comp p) :=
  Submodule.mapQ _ _ ((LinearMap.funLeft ℤ_[ℓ] M p).restrict (by
    rintro c ⟨hc, hc'⟩
    refine ⟨hc.comp hp, fun g h => ?_⟩
    simp only [LinearMap.funLeft_apply, map_mul, hc', MonoidHom.comp_apply]) : Z1 a →ₗ[ℤ_[ℓ]] Z1 (a.comp p))
    (by
      rintro c ⟨m, hm⟩
      refine ⟨m, ?_⟩
      funext g
      exact congrFun hm (p g))

end H1

section SL

variable {ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] {OC : Type} [CommRing OC] [Algebra ℤ_[ℓ] OC]

structure SL (actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)) (r : ℕ) where
  Mx : G → Matrix (Fin r) (Fin r) OC
  one : Mx 1 = 1
  mul : ∀ g h, Mx (g * h) = (Mx h).map (actO g) * Mx g

variable {actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)} {r : ℕ}

lemma map_vecMul' (e : OC ≃ₐ[ℤ_[ℓ]] OC) (v : Fin r → OC) (A : Matrix (Fin r) (Fin r) OC) :
    (fun k => e ((v ᵥ* A) k)) = (fun k => e (v k)) ᵥ* A.map e := by
  funext k
  simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Matrix.map_apply]

def SL.rep (S : SL actO r) : Representation ℤ_[ℓ] G (Fin r → OC) where
  toFun g :=
    { toFun := fun v => (fun k => actO g (v k)) ᵥ* S.Mx g
      map_add' := by
        intro v w
        rw [← Matrix.add_vecMul]
        congr 1
        funext k
        simp
      map_smul' := by
        intro t v
        rw [RingHom.id_apply, ← Matrix.smul_vecMul]
        congr 1
        funext k
        simp }
  map_one' := by
    ext v k
    simp [S.one]
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro v
    show (fun k => actO (g * h) (v k)) ᵥ* S.Mx (g * h)
      = (fun k => actO g (((fun k => actO h (v k)) ᵥ* S.Mx h) k)) ᵥ* S.Mx g
    rw [map_vecMul', S.mul, Matrix.vecMul_vecMul]
    simp [map_mul]

def SL.twist (S : SL actO r) (χ : G →* ℤ_[ℓ]ˣ) (i : ℤ) : SL actO r where
  Mx g := (((χ g) ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • S.Mx g
  one := by simp [S.one]
  mul := by
    intro g h
    have : ((((χ h) ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • S.Mx h).map (actO g)
        = (((χ h) ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (S.Mx h).map (actO g) := by
      ext p q
      simp
    rw [this, S.mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_mul, mul_zpow, Units.val_mul,
      mul_comm]

def Inter (S S' : SL actO r) (Y : Matrix (Fin r) (Fin r) OC) : Prop :=
  ∀ g, Y.map (actO g) * S'.Mx g = S.Mx g * Y

variable [TopologicalSpace OC] [IsTopologicalRing OC] [ContinuousConstSMul ℤ_[ℓ] OC]

def Inter.eqMap {S S' : SL actO r} {Y : Matrix (Fin r) (Fin r) OC} (h : Inter S S' Y) :
    EqMap S.rep S'.rep where
  f :=
    { toFun := fun v => v ᵥ* Y
      map_add' := fun v w => Matrix.add_vecMul _ _ _
      map_smul' := fun t v => Matrix.smul_vecMul _ _ _ }
  cont := by
    show Continuous fun v : Fin r → OC => v ᵥ* Y
    exact Continuous.matrix_vecMul continuous_id continuous_const
  eqv := by
    intro g v
    show ((fun k => actO g (v k)) ᵥ* S.Mx g) ᵥ* Y = (fun k => actO g ((v ᵥ* Y) k)) ᵥ* S'.Mx g
    rw [map_vecMul', Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h g]

end SL

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
