import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.InstLocalRingSymplecticCoefficients

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TV

namespace Formalism.MainNotions.V

variable {D : D7} (V : VData D)

instance numberField_of_fd (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] : NumberField K := ⟨⟩

def scalarGL (R : Type) [CommRing R] (n : ℕ) : Rˣ →* GL (Fin n) R :=
  Units.map (Matrix.scalar (Fin n) : R →+* Matrix (Fin n) (Fin n) R).toMonoidHom

theorem scalarGL_commute (R : Type) [CommRing R] (n : ℕ) (u : Rˣ) (M : GL (Fin n) R) :
    Commute (scalarGL R n u) M := by
  apply Units.ext
  exact Matrix.scalar_commute (u : R) (fun r => Commute.all _ r) (M : Matrix (Fin n) (Fin n) R)

def twistRep {H R : Type} [Group H] [CommRing R] {n : ℕ} (ρ : H →* GL (Fin n) R) (χ : H →* Rˣ) :
    H →* GL (Fin n) R where
  toFun g := ρ g * scalarGL R n (χ g)
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_assoc]
    congr 1
    exact (scalarGL_commute R n (χ a) (ρ b)).symm.left_comm _

def IsDirSum {H R : Type} [Group H] [CommRing R] {m k : ℕ} (ρ : H →* GL (Fin (m + k)) R)
    (ρ₁ : H →* GL (Fin m) R) (ρ₂ : H →* GL (Fin k) R) : Prop :=
  ∃ P : GL (Fin (m + k)) R, ∀ g : H,
    ((P⁻¹ * ρ g * P : GL (Fin (m + k)) R) : Matrix (Fin (m + k)) (Fin (m + k)) R) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ g : Matrix (Fin m) (Fin m) R) 0 0 (ρ₂ g : Matrix (Fin k) (Fin k) R))

def charRep {H R : Type} [Group H] [CommRing R] (χ : H →* Rˣ) : H →* GL (Fin 1) R :=
  (scalarGL R 1).comp χ

def dualRep {H R : Type} [Group H] [CommRing R] {n : ℕ} (σ : H →* GL (Fin n) R) :
    H →* GL (Fin n) R where
  toFun g :=
    ⟨Matrix.transpose (((σ g)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R),
      Matrix.transpose ((σ g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R),
      by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]⟩
  map_one' := by ext1; simp
  map_mul' a b := by
    ext1
    simp only [map_mul, mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

def IsIsoRep {H R : Type} [Group H] [CommRing R] {n : ℕ} (ρ ρ' : H →* GL (Fin n) R) : Prop :=
  ∃ P : GL (Fin n) R, ∀ g : H, P⁻¹ * ρ g * P = ρ' g

def ChiConj (D : D7) (χ χ'' : Chi D) : Prop := ∃ k : ℕ, Nat.Coprime k (orderOf χ) ∧ χ'' = χ ^ k

def degQ (D : D7) (χ : Chi D) : ℕ := Nat.totient (orderOf χ)

open Classical in

def chiOrbit (D : D7) (χ : Chi D) : Finset (Chi D) := Finset.univ.filter (ChiConj D χ)

theorem ChiConj.refl (D : D7) (χ : Chi D) : ChiConj D χ χ := ⟨1, Nat.coprime_one_left _, (pow_one χ).symm⟩

theorem ChiConj.symm (D : D7) {χ χ'' : Chi D} (h : ChiConj D χ χ'') : ChiConj D χ'' χ := by
  obtain ⟨k, hk, rfl⟩ := h
  have ho : orderOf (χ ^ k) = orderOf χ := hk.symm.orderOf_pow
  rcases Nat.lt_or_ge 1 (orderOf χ) with hn | hn
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk hn
    refine ⟨m, ?_, ?_⟩
    · rw [ho]
      refine Nat.coprime_of_mul_modEq_one k ?_
      rw [Nat.ModEq, Nat.mul_comm, hm, Nat.mod_eq_of_lt hn]
    · rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]
  · have h1 : orderOf χ = 1 := le_antisymm hn (orderOf_pos χ)
    have hχ : χ = 1 := orderOf_eq_one_iff.mp h1
    exact ⟨1, Nat.coprime_one_left _, by rw [hχ]; simp⟩

def chiKC (K : IntermediateField ℚ QbarQ) (g : GQ) : ℂˣ :=
  haveI := Classical.dec (g ∈ K.fixingSubgroup); if g ∈ K.fixingSubgroup then 1 else -1

def IsQi (K : IntermediateField ℚ QbarQ) : Prop :=
  ∃ x : QbarQ, x ^ 2 = -1 ∧ K = IntermediateField.adjoin ℚ {x}

def UnitaryCaseGaussian (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) : Prop :=
  (∃ g ∈ V.Iq l, V.psiBar l e χ g ^ 2 ≠ 1) ∧ IsQi K

def UnitaryCaseInert (l : ℕ) [Fact l.Prime] (χ : Chi D) (K : IntermediateField ℚ QbarQ)
    [FiniteDimensional ℚ K] : Prop :=
  (Ideal.span {((l : ℕ) : 𝓞 K)}).IsPrime ∧ V.aOf l χ = 0 ∧ ¬ l ∣ condV D

structure UnitaryThreeData (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ)
    [FiniteDimensional ℚ K] : Prop where
  l_ne_two : l ≠ 2
  e_mem : e ∈ eRange D
  psi_even : V.PsiEven l e χ
  K_quad : Module.finrank ℚ K = 2
  K_imag : IsTotallyComplex K
  l_unram : ¬ ((l : ℤ) ∣ discr K)
  l_classNo : Nat.Coprime l (classNumber K)
  dK_coprime : IsCoprime (discr K) ((D.host.q : ℤ) * (D.host.d : ℤ))
  chiK_not : ¬ ∃ χ₀ : Chi D, ∀ g : GQ, V.chiGQ χ₀ g = chiKC K g
  sq_ne : ∃ g ∈ K.fixingSubgroup, V.psiBar l e χ g ^ 2 ≠ 1
  om_ne : ∃ g ∈ K.fixingSubgroup, V.omBar l g * V.psiBar l e χ g ≠ 1
  om_inv_ne : ∃ g ∈ K.fixingSubgroup, V.psiBar l e χ g ≠ V.omBar l g
  frame : UnitaryCaseGaussian V l e χ K ∨ UnitaryCaseInert V l χ K

def IsNormElt (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ)
    (g1 : GQ) : Prop :=
  g1 ∈ K.fixingSubgroup ∧ V.psiBar l e χ g1 ^ 2 ≠ 1

def IsRIota3 {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (π : (V.spec K 3).Rep) (ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l)) : Prop :=
  V.IsRi π (VData.toRecRep ρ)

def AttachedGL3 {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l)) : Prop :=
  ∃ π : (V.spec K 3).Rep, V.IsRACSDC K 3 π ∧ IsRIota3 V K π ρ

def UnitaryThreeFiniteness (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ) :
    Prop :=
  Module.Finite (V.Ol l) (V.S3zero l e χ K g1)

def UnitaryThreeIrreduciblePoints (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ)
    [FiniteDimensional ℚ K] (g1 : GQ) : Prop :=
  ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ)) →
    AttachedGL3 V K (twistRep (V.rho3 ξ) ((epsL l).comp K.fixingSubgroup.subtype)⁻¹)

def UnitaryThreeAutomorphy : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ)
    [FiniteDimensional ℚ K], UnitaryThreeData V l e χ K →
    ∃ g1 : GQ, IsNormElt V l e χ K g1 ∧ UnitaryThreeFiniteness V l e χ K g1 ∧ UnitaryThreeIrreduciblePoints V l e χ K g1

structure GSp4BaseConditions (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) : Prop where
  l_ne_two : l ≠ 2
  e_mem : e ∈ eRange D
  psi_even : V.PsiEven l e χ
  psibar_sq : ∀ g : GQ, V.psiBar l e χ g ^ 2 = 1
  psibar_ne : ∃ g : GQ, V.psiBar l e χ g ≠ 1
  chi_ne : χ ≠ 1
  two_le_e : 2 ≤ e
  l_coprime : Nat.Coprime l (condV D)
  two_l_lt : 2 * l < D.host.q ∧ 2 * l < D.host.d

structure GSp4Data (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (n' : ℕ)
    (ξ' : DirichletCharacter ℂ (2 ^ n')) : Prop where
  base : GSp4BaseConditions V l e χ
  n'_ge : 12 * l ^ 7 * (D.host.q * D.host.d) ≤ 2 ^ n'
  n'_least : ∀ m < n', 2 ^ m < 12 * l ^ 7 * (D.host.q * D.host.d)
  xi_odd : ξ'.Odd
  xi_cond : ξ'.conductor = 2 ^ n'

def AttachedGL4 {l : ℕ} [Fact l.Prime] (ρ : GQ →* GL (Fin 4) (QbarL l)) : Prop :=
  ∃ π : (V.spec ℚ 4).Rep, V.IsRA ℚ 4 π ∧ V.IsRi π ρ

def IsSigmaSum {l : ℕ} [Fact l.Prime] (ρ : GQ →* GL (Fin 4) (QbarL l)) (θ α : GQ →* (QbarL l)ˣ) :
    Prop :=
  ∃ σ : GQ →* GL (Fin 2) (QbarL l), Formalism.ConjugateSelfDual.Irred σ ∧
    (∀ g : GQ, ‖(σ g : Matrix (Fin 2) (Fin 2) (QbarL l)).trace - ((θ g : QbarL l) + (α g : QbarL l))‖ < 1 ∧
      ‖(σ g : Matrix (Fin 2) (Fin 2) (QbarL l)).det - (θ g : QbarL l) * (α g : QbarL l)‖ < 1) ∧
    IsDirSum (m := 2) (k := 2) ρ σ (twistRep (dualRep σ) θ)

def GSp4Automorphy : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')),
    GSp4Data V l e χ n' ξ' →
    Module.Finite (V.Ol l) (V.SS4inv l e χ n' ξ') ∧
    (∀ ξ : V.symplecticHeckeAlgebra l e χ n' ξ' →+* QbarL l, V.IsPt4 ξ → Formalism.ConjugateSelfDual.Irred (V.rho4 ξ) →
      AttachedGL4 V (V.rho4 ξ)) ∧
    (∀ ξ : V.symplecticHeckeAlgebra l e χ n' ξ' →+* QbarL l, V.IsPt4 ξ →
      ¬ IsSigmaSum (V.rho4 ξ) (V.thL l e χ n' ξ') (V.alL l n' ξ'))

def phiL (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter ℂ l) : GQ →* (QbarL l)ˣ :=
  (toLu (V.iotaC l)).comp
    ((φ.toUnitHom).comp ((Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom).comp (eps l)))

def onTop {n l : ℕ} [Fact l.Prime] (ρ : GQ →* GL (Fin n) (QbarL l)) : (⊤ : Subgroup GQ) →* GL (Fin n) (QbarL l) :=
  ρ.comp (⊤ : Subgroup GQ).subtype

def IsWeight2 (π : (V.spec ℚ 2).Rep) (k : ℕ) : Prop :=
  ∀ τ : ℚ →+* ℂ, (V.spec ℚ 2).wt π τ 0 - (V.spec ℚ 2).wt π τ 1 = (k : ℤ) - 1

def LevelPrimeTo (F : Type) [Field F] [NumberField F] (n : ℕ) (π : (V.spec F n).Rep) (l : ℕ) : Prop :=
  ∃ M : ℕ, (V.spec F n).level π M ∧ Nat.Coprime M l

def IsVg {l : ℕ} [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (ρ : GQ →* GL (Fin 2) (QbarL l)) : Prop :=
  V.IsRi π ρ

def OrdinaryAt (π : (V.spec ℚ 2).Rep) (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal →
    ∃ r : QbarL l, ‖r‖ = 1 ∧ ((V.spec ℚ 2).hecke π v).eval (V.iotaC l r) = 0

def LemmaK : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (e : ℕ), 1 ≤ e →
    ∀ π : (V.spec ℚ 2).Rep, IsWeight2 V π (2 * e + 1) → LevelPrimeTo V ℚ 2 π l →
    OrdinaryAt V π l →
    ∀ Vg : GQ →* GL (Fin 2) (QbarL l), Continuous Vg → Formalism.ConjugateSelfDual.AlmostUnram Vg → Formalism.ConjugateSelfDual.Irred Vg → IsVg V π Vg →
    (∀ τ, V.HT l 2 ⊤ (V.plc l) (onTop Vg) τ = {0, 2 * (e : ℤ)}) →
    ∀ φ : DirichletCharacter ℂ l,
      Subsingleton (V.finiteCohomology l 2 ⊤ (onTop (twistRep Vg ((epsL l) ^ e * phiL V l φ))))

def IsCorner {H R : Type} [Group H] [CommRing R] (ρ : H →* GL (Fin 3) R) (ρ₂ : H →* GL (Fin 2) R) : Prop :=
  ∀ g : H,
    (((ρ g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 1 = 0 ∧ ((ρ g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 1 0 = 0 ∧
      ((ρ g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 1 2 = 0 ∧ ((ρ g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 2 1 = 0) ∧
    ((ρ g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 1 1 = 1 ∧
    ((ρ₂ g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![((ρ g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 0, ((ρ g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 2;
         ((ρ g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 2 0, ((ρ g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 2 2]

def LemmaWAt (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ) : Prop :=
  ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ →
    ∀ ρ₂ : K.fixingSubgroup →* GL (Fin 2) (QbarL l), Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ₂) →
    IsCorner (V.rho3 ξ) ρ₂ →
    ∀ Wr : GQ →* GL (Fin 2) (QbarL l), (∀ g : K.fixingSubgroup, Wr g = ρ₂ g) →
      (((Wr V.cc : GL (Fin 2) (QbarL l)) : Matrix (Fin 2) (Fin 2) (QbarL l)) = !![-1, 0; 0, 1] ∨
        ((Wr V.cc : GL (Fin 2) (QbarL l)) : Matrix (Fin 2) (Fin 2) (QbarL l)) = !![1, 0; 0, -1]) →
    ∃ π : (V.spec ℚ 2).Rep, IsWeight2 V π (2 * e + 1) ∧ IsVg V π (twistRep Wr ((epsL l) ^ e)⁻¹)

def LemmaW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ)
    [FiniteDimensional ℚ K], UnitaryThreeData V l e χ K → ∀ g1 : GQ, IsNormElt V l e χ K g1 →
    LemmaWAt V l e χ K g1

def UnitaryThreeAutomorphyWeights : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ)
    [FiniteDimensional ℚ K], UnitaryThreeData V l e χ K →
    ∃ g1 : GQ, IsNormElt V l e χ K g1 ∧ UnitaryThreeFiniteness V l e χ K g1 ∧ UnitaryThreeIrreduciblePoints V l e χ K g1 ∧
      LemmaWAt V l e χ K g1

variable {V}

end Formalism.MainNotions.V
