import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjTor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

noncomputable section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg

namespace UpperTheory.V.UnitaryThreeInertia

structure Canon {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R) : Prop where
  hat : InHat h
  one : ∀ a, (h : Matrix (Fin 3) (Fin 3) R) a a = 1
  diag : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h).IsDiag

abbrev push {O A B Γ : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Group Γ]
    (f : A →ₐ[O] B) (r : Γ →* GG 3 A) : Γ →* GG 3 B := (GG.map (f : A →+* B)).comp r

section Weights

variable {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] (u : Γ →* GG 3 R)

variable (O) in

def wpart (j : ℤ) : Submodule O R where
  carrier := {x | ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : R →ₐ[O] R') (t : R'ˣ),
    push f' u = conjBy (tor R' t) (push f u) → f' x = ((t ^ j : R'ˣ) : R') * f x}
  add_mem' := fun hx hy R' _ _ _ f f' t h => by rw [map_add, map_add, hx R' f f' t h, hy R' f f' t h, mul_add]
  zero_mem' := fun R' _ _ _ f f' t _ => by simp
  smul_mem' := fun a x hx R' _ _ _ f f' t h => by rw [map_smul, map_smul, hx R' f f' t h, mul_smul_comm]

instance : SetLike.GradedMonoid (wpart O u) where
  one_mem := fun R' _ _ _ f f' t _ => by simp
  mul_mem := fun i j x y hx hy R' _ _ _ f f' t h => by
    rw [map_mul, map_mul, hx R' f f' t h, hy R' f f' t h, _root_.zpow_add, Units.val_mul]; ring

variable (O) in

def Sring : Subalgebra O R := gradedSub (wpart O u)

theorem mem_Sring {j : ℤ} {x : R} (hx : x ∈ wpart O u j) : x ∈ Sring O u := le_iSup (wpart O u) j hx

theorem entry_mem (g : Γ) (a b : Fin 3) : (u g).mat a b ∈ wpart O u (wt a b) := fun R' _ _ _ f f' t h => by
  have e := congrArg (fun r : Γ →* GG 3 R' => (r g).mat a b) h
  simp only [(conjBy_tor (push f u) t).1] at e
  exact e

def ptMat {K : Type} [CommRing K] [Algebra O K] (ξ : Sring O u →ₐ[O] K) (g : Γ) : Matrix (Fin 3) (Fin 3) K :=
  fun a b => ξ ⟨_, mem_Sring u (entry_mem u g a b)⟩

def IsPtHom {K : Type} [CommRing K] [Algebra O K] (ξ : Sring O u →ₐ[O] K) (r : Γ →* GG 3 K) : Prop :=
  ∀ g, (r g).right = (u g).right ∧ (r g).mat = ptMat u ξ g

def IsPush {K : Type} [CommRing K] [Algebra O K] {S : Subalgebra O R} (ξ : S →ₐ[O] K) (r : Γ →* GG 3 K) : Prop :=
  ∀ g, (r g).right = (u g).right ∧ ∀ a b, ∃ h : (u g).mat a b ∈ S, (r g).mat a b = ξ ⟨_, h⟩

end Weights

section Quot

variable {O : Type} [CommRing O]

def OQ (a : O) : Type := O ⧸ Ideal.span {a}

instance (a : O) : CommRing (OQ a) := inferInstanceAs (CommRing (O ⧸ Ideal.span {a}))
instance (a : O) : Algebra O (OQ a) := inferInstanceAs (Algebra O (O ⧸ Ideal.span {a}))
instance (a : O) : TopologicalSpace (OQ a) := ⊥
instance (a : O) : DiscreteTopology (OQ a) := ⟨rfl⟩
instance (a : O) : ContinuousConstSMul O (OQ a) := ⟨fun _ => continuous_of_discreteTopology⟩

def oqRep {D : Type} [Group D] (χ : D →* Oˣ) (a : O) : Representation O D (OQ a) where
  toFun g := ((χ g : Oˣ) : O) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [smul_smul, mul_comm]

end Quot

namespace Frame

variable {O : Type} [CommRing O] [IsLocalRing O] {G Γ : Type} [Group G] [Group Γ] {ι : Type} (F : Frame O G Γ ι)
  [TopologicalSpace G] [TopologicalSpace Γ]

structure IsUniv (g₁ : Γ) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R) : Prop where
  pt : F.IsPt g₁ u
  univ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (r : Γ →* GG 3 R'), F.IsPt g₁ r →
    ∃! f : R →ₐ[O] R', push f u = r

structure Adapted {R : Type} [CommRing R] [Algebra O R] (u : Γ →* GG 3 R) (W : WPres O ℤ R) : Prop where
  var : ∀ i, ∃ g a b, F.η g = 1 ∧ W.wt i = wt a b ∧ W.z i = (u g).mat a b - (F.rz R g).mat a b
  part : ∀ j, W.part j = wpart O u j

def Minimal {R : Type} [CommRing R] [Algebra O R] (W : WPres O ℤ R) : Prop :=
  ∀ f, W.π f = 0 → ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) f ∈ maximalIdeal O

def ShaO (a : O) : Submodule O (H1 (oqRep F.Ψ⁻¹ a)) :=
  Submodule.span O {x | ∃ z : Z1 (oqRep F.Ψ⁻¹ a), x = Submodule.Quotient.mk z ∧
    (∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, z.1 (F.loc v s) = 0) ∧
    ∀ v ∈ F.Tb, ∃ m, ∀ g : F.D v, z.1 (F.loc v g) = oqRep F.Ψ⁻¹ a (F.loc v g) m - m}

def VanE : Prop := ∀ j : ℤ, j ≤ 0 → ∀ γ : Γ → Matrix (Fin 3) (Fin 3) O, (∀ g, γ g ∈ gw O j) → IsCoc (r0 F.η F.Ψ) γ →
  (∀ a b, Alg.AdicCont (maximalIdeal O) fun g => γ g a b) →
  (∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, γ (F.loc v s) = 0) →
  (j = 0 → ∀ v ∈ F.Tb, ∀ s ∈ F.Iv v, γ (F.loc v s) = 0) →
  (j < 0 → ∃ Y ∈ gw O j, ∀ g : F.D F.vl, F.ηv F.vl g = 1 → γ (F.loc _ g) = cob (r0 F.η F.Ψ) Y (F.loc _ g)) →
  ∃ a : O, a ≠ 0 ∧ ∃ X, ∀ g, a • γ g = cob (r0 F.η F.Ψ) X g

def Cl1 : Prop := ∀ (A : Type) [CommGroup A] (χ : F.η.ker →* A), IsLocallyConstant χ →
  (∀ v (s : F.D v) (g : Γ) (h : g * F.loc v s * g⁻¹ ∈ F.η.ker), s ∈ F.Iv v → χ ⟨_, h⟩ = 1) → χ = 1

section Points

variable {K : Type} [Field K] [Algebra O K]

def IsCharZeroPt (g₁ : Γ) (r : Γ →* GG 3 K) : Prop :=
  ∃ (A : Subalgebra O K) (_ : IsDiscreteValuationRing A) (_ : Module.Finite O A) (t : Kˣ) (r' : Γ →* GG 3 A),
    F.IsPt g₁ r' ∧ push A.val r' = conjBy (tor K t) r

def Rigid [TopologicalSpace K] (r : Γ →* GG 3 K) : Prop :=
  ∀ (y : Γ → Matrix (Fin 3) (Fin 3) K) (r' : Γ →* GG 3 (DualNumber K)), Continuous y → IsCoc r y →
    IsDeform ((GG.map (algebraMap K (DualNumber K))).comp r)
      (fun g => (y g).map (TrivSqZeroExt.inr : K → DualNumber K)) r' →
    (∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, y (F.loc v s) = 0) →
    (∃ h, TriIn (F.ηv F.vl) (F.Ψv F.vl) (F.Iv F.vl) (r'.comp (F.loc F.vl)) h) →
    (∀ v ∈ F.Sb, ∃ h, DiagIn (F.ηv v) (F.Ψv v) (F.Iv v) (r'.comp (F.loc v)) h) →
    ∃ X, ∀ g, y g = cob r X g

end Points

end Frame

structure SmallExt (O : Type) [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (𝒜 : ℤ → Submodule O R) (I : Ideal R) (j : ℤ) : Prop where
  fin : Finite R
  kill : maximalIdeal R * I = ⊥
  le : I ≤ maximalIdeal R
  wt : ∀ x ∈ I, x ∈ 𝒜 j

end UpperTheory.V.UnitaryThreeInertia

end
