import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

noncomputable section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3

namespace UpperTheory.V.UnitaryThreeInertia

section Local

variable {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
  {D : Type} [Group D]

def psi (Ψ : D →* Oˣ) (a : Fin 3) (g : D) : O := ((Ψ g ^ wt1 a : Oˣ) : O)

abbrev InHat (h : GL (Fin 3) R) : Prop := CongOne (maximalIdeal R) h

structure Red (η : D →* ℤˣ) (Ψ : D →* Oˣ) (r : D →* GG 3 R) : Prop where
  mult : HasMult η r
  red : ∀ g, EntIn (maximalIdeal R) ((r g).mat - ((r0 η Ψ g).mat).map (algebraMap O R))

def kerBar (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) : Subgroup D :=
  I ⊓ η.ker ⊓ ((Units.map (residue O).toMonoidHom).comp Ψ).ker

def CondU (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 R) : Prop :=
  ∀ s ∈ kerBar η Ψ I, r s = 1

structure TriIn (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) {A : Type} [CommRing A] [Algebra O A]
    (r : D →* GG 3 A) (h : GL (Fin 3) A) : Prop where
  tri : Upper η (conjBy h⁻¹ r)
  ine : ∀ s ∈ I, η s = 1 → ∀ a, (conjBy h⁻¹ r s).mat a a = algebraMap O A (psi Ψ a s)

structure DiagIn (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) {A : Type} [CommRing A] [Algebra O A]
    (r : D →* GG 3 A) (h : GL (Fin 3) A) : Prop extends TriIn η Ψ I r h where
  low : Lower η (conjBy h⁻¹ r)

def CondT (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 R) : Prop :=
  ∃ h : GL (Fin 3) R, InHat h ∧ TriIn η Ψ I r h

def CondD (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 R) : Prop :=
  ∃ h : GL (Fin 3) R, InHat h ∧ DiagIn η Ψ I r h

def AdicCont [TopologicalSpace D] {A : Type} [CommRing A] (J : Ideal A) (r : D →* GG 3 A) : Prop :=
  ∀ n : ℕ, IsLocallyConstant fun g => (r g).mat.map (Ideal.Quotient.mk (J ^ n))

def GrMat {A : Type} [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) (X : Matrix (Fin 3) (Fin 3) A) : Prop :=
  ∀ a b, X a b ∈ 𝒜 (wt a b)

end Local

section Residual

variable {k : Type} [CommRing k] {D : Type} [Group D]

variable (k) in

def Gb (j : ℤ) : Type := gw k j

instance (j : ℤ) : AddCommGroup (Gb k j) := inferInstanceAs (AddCommGroup (gw k j))
instance (j : ℤ) : Module k (Gb k j) := inferInstanceAs (Module k (gw k j))
instance (j : ℤ) : TopologicalSpace (Gb k j) := ⊥
instance (j : ℤ) : DiscreteTopology (Gb k j) := ⟨rfl⟩
instance (j : ℤ) : ContinuousConstSMul k (Gb k j) := ⟨fun _ => continuous_of_discreteTopology⟩

def Gb.val {j : ℤ} (X : Gb k j) : Matrix (Fin 3) (Fin 3) k := Subtype.val (p := fun X => X ∈ gw k j) X

theorem adjoint_diagonal_rep_preserves_weight_piece (η : D →* ℤˣ) (Ψ : D →* kˣ) (j : ℤ) (g : D) :
    gw k j ≤ (gw k j).comap (adRep (r0 η Ψ) g) := by
  intro X hX a b hab
  have hJ : ∀ i j : Fin 3, (Jmat k 3 * Xᵀ * Jmat k 3) i j = X j.rev i.rev := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
  have hw : wt b.rev a.rev = wt a b := by
    fin_cases a <;> fin_cases b <;> simp [wt, wt1, Fin.rev]
  change ((r0 η Ψ g).mat * (if (r0 η Ψ g).right = 1 then X else thetaLie X) * (((r0 η Ψ g).left⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) a b = 0
  rw [GG.mat, unitaryThreeReflection_left, ← map_inv, tor_val, tor_val]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs
  · rw [hX a b hab]
    simp
  · unfold thetaLie
    rw [Matrix.neg_apply, hJ, hX b.rev a.rev (by rw [hw]; exact hab)]
    simp

def gRep (η : D →* ℤˣ) (Ψ : D →* kˣ) (j : ℤ) : Representation k D (Gb k j) :=
  (adRep (r0 η Ψ)).subrepresentation (gw k j) (adjoint_diagonal_rep_preserves_weight_piece η Ψ j)

theorem gRep_val (η : D →* ℤˣ) (Ψ : D →* kˣ) (j : ℤ) (g : D) (X : Gb k j) :
    (gRep η Ψ j g X).val = adRep (r0 η Ψ) g X.val := rfl

end Residual

structure Frame (O : Type) [CommRing O] (G Γ : Type) [Group G] [Group Γ] (ι : Type) where
  π : G →* Γ
  η : Γ →* ℤˣ
  Ψ : Γ →* Oˣ
  c : Γ
  D : ι → Subgroup G
  I : ι → Subgroup G
  vl : ι
  Sb : Set ι

namespace Frame

variable {O : Type} [CommRing O] [IsLocalRing O] {G Γ : Type} [Group G] [Group Γ] {ι : Type} (F : Frame O G Γ ι)

def loc (v : ι) : F.D v →* Γ := F.π.comp (F.D v).subtype

abbrev ηv (v : ι) : F.D v →* ℤˣ := F.η.comp (F.loc v)

abbrev Ψv (v : ι) : F.D v →* Oˣ := F.Ψ.comp (F.loc v)

abbrev Iv (v : ι) : Subgroup (F.D v) := (F.I v).subgroupOf (F.D v)

abbrev Nv (v : ι) : Subgroup (F.D v) := kerBar (F.ηv v) (F.Ψv v) (F.Iv v)

def Tb : Set ι := insert F.vl F.Sb

def Ψbar : Γ →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp F.Ψ

def rz (A : Type) [CommRing A] [Algebra O A] : Γ →* GG 3 A := (GG.map (algebraMap O A)).comp (r0 F.η F.Ψ)

section Cond

variable {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R]

def LocAt (v : ι) (r : F.D v →* GG 3 R) : Prop :=
  (v = F.vl → CondT (F.ηv v) (F.Ψv v) (F.Iv v) r) ∧ (v ∈ F.Sb → CondD (F.ηv v) (F.Ψv v) (F.Iv v) r) ∧
    (v ∉ F.Tb → CondU (F.ηv v) (F.Ψv v) (F.Iv v) r)

structure Cond (r : Γ →* GG 3 R) : Prop extends Red F.η F.Ψ r where
  loc : ∀ v, F.LocAt v (r.comp (F.loc v))

structure CondN (g₁ : Γ) (r : Γ →* GG 3 R) : Prop extends F.Cond r where
  norm : Normalised F.c g₁ r

structure IsPt [TopologicalSpace Γ] (g₁ : Γ) (r : Γ →* GG 3 R) : Prop extends F.CondN g₁ r where
  cont : AdicCont (maximalIdeal R) r

end Cond

def Marked (g₁ : Γ) : Prop := F.η g₁ = 1 ∧ IsUnit ((F.Ψ g₁ : O) ^ 2 - 1)

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Γ]

structure Ok : Prop where
  two : IsUnit (2 : O)
  π_cont : Continuous F.π
  η_cont : IsLocallyConstant F.η
  Ψ_cont : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ n) (F.Ψ g : O)
  csq : F.c * F.c = 1
  ηc : F.η F.c = -1
  Ψc : F.Ψ F.c = 1
  vl_notMem : F.vl ∉ F.Sb
  D_closed : ∀ v, IsClosed (F.D v : Set G)
  I_closed : ∀ v, IsClosed (F.I v : Set G)
  I_le : ∀ v, F.I v ≤ F.D v
  I_normal : ∀ v, (F.Iv v).Normal

  frob : ∀ v, ∃ φ : F.D v, (F.Iv v ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧
    ∀ n : ℕ, 0 < n → ∃ d : F.D v →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ F.Iv v, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1
  η_I : ∀ v ∈ F.Tb, ∀ s ∈ F.Iv v, F.ηv v s = 1
  x : ∀ v ∈ F.Tb, ∃ x : F.D v, F.ηv v x = 1 ∧ IsUnit ((F.Ψv v x : O) ^ 2 - 1)
  teich : ∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, F.Ψv v s = 1

abbrev gbar (j : ℤ) : Representation (ResidueField O) Γ (Gb (ResidueField O) j) := gRep F.η F.Ψbar j

abbrev gloc (j : ℤ) (v : ι) : Representation (ResidueField O) (F.D v) (Gb (ResidueField O) j) :=
  (F.gbar j).comp (F.loc v)

def ZL (j : ℤ) (v : ι) : Submodule (ResidueField O) (F.D v → Gb (ResidueField O) j) where
  carrier := {y | y ∈ Z1 (F.gloc j v) ∧ (v ≠ F.vl → ∀ s ∈ F.Nv v, y s = 0) ∧
    (v = F.vl → j < 0 → y ∈ B1 (F.gloc j v)) ∧ (v = F.vl → j = 0 → ∀ s ∈ F.Iv v, y s = 0)}
  add_mem' := fun {y y'} h h' => ⟨add_mem h.1 h'.1, fun e s hs => by simp [h.2.1 e s hs, h'.2.1 e s hs],
    fun e e' => add_mem (h.2.2.1 e e') (h'.2.2.1 e e'), fun e e' s hs => by simp [h.2.2.2 e e' s hs, h'.2.2.2 e e' s hs]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ => rfl, fun _ _ => zero_mem _, fun _ _ _ _ => rfl⟩
  smul_mem' := fun a y h => ⟨Submodule.smul_mem _ a h.1, fun e s hs => by simp [h.2.1 e s hs],
    fun e e' => Submodule.smul_mem _ a (h.2.2.1 e e'), fun e e' s hs => by simp [h.2.2.2 e e' s hs]⟩

def res1 (j : ℤ) (v : ι) : (Γ → Gb (ResidueField O) j) →ₗ[ResidueField O] (F.D v → Gb (ResidueField O) j) :=
  LinearMap.funLeft _ _ (F.loc v)

def res2 (j : ℤ) (v : ι) :
    (Γ × Γ → Gb (ResidueField O) j) →ₗ[ResidueField O] (F.D v × F.D v → Gb (ResidueField O) j) :=
  LinearMap.funLeft _ _ (Prod.map (F.loc v) (F.loc v))

def selmerCocycles (j : ℤ) : Submodule (ResidueField O) (Γ → Gb (ResidueField O) j) :=
  Z1 (F.gbar j) ⊓ ⨅ v, (F.ZL j v).comap (F.res1 j v)

abbrev selmerCohomologyQuotient (j : ℤ) : Type := F.selmerCocycles j ⧸ (B1 (F.gbar j)).comap (F.selmerCocycles j).subtype

def framedTwoCocycles (j : ℤ) : Submodule (ResidueField O)
    ((Γ × Γ → Gb (ResidueField O) j) × ∀ v, F.D v → Gb (ResidueField O) j) :=
  (Z2 (F.gbar j)).comap (LinearMap.fst _ _ _) ⊓
    ⨅ v, ((contMaps _ _ (F.D v)).comap ((LinearMap.proj v).comp (LinearMap.snd _ _ _)) ⊓
      LinearMap.eqLocus ((d1 (F.gloc j v)).comp ((LinearMap.proj v).comp (LinearMap.snd _ _ _)))
        ((F.res2 j v).comp (LinearMap.fst _ _ _)))

def framedTwoCoboundaries (j : ℤ) : Submodule (ResidueField O)
    ((Γ × Γ → Gb (ResidueField O) j) × ∀ v, F.D v → Gb (ResidueField O) j) :=
  (contMaps _ _ Γ).map ((d1 (F.gbar j)).prod (LinearMap.pi fun v => F.res1 j v)) ⊔
    (Submodule.pi Set.univ fun v => F.ZL j v).map (LinearMap.inr _ _ _)

abbrev Ob (j : ℤ) : Type := F.framedTwoCocycles j ⧸ (F.framedTwoCoboundaries j).comap (F.framedTwoCocycles j).subtype

def defect (j : ℤ) : ℤ := if j = -1 then -1 else if j = 1 ∨ j = 2 then 1 else 0

def Count : Prop := ∀ j : ℤ, Module.Finite (ResidueField O) (F.selmerCohomologyQuotient j) ∧ Module.Finite (ResidueField O) (F.Ob j) ∧
  (Module.finrank (ResidueField O) (F.selmerCohomologyQuotient j) : ℤ) - Module.finrank (ResidueField O) (F.Ob j) = defect j

structure LocVan : Prop where
  h2 : ∀ v ∈ F.Tb, ∀ j ≠ 0, Subsingleton (H2 (F.gloc j v))
  h1 : ∀ v ∈ F.Sb, ∀ j ≠ 0, Subsingleton (H1 (F.gloc j v))

def Xpp : Prop := Subsingleton (F.selmerCohomologyQuotient (-2))

end Frame

end UpperTheory.V.UnitaryThreeInertia

end
