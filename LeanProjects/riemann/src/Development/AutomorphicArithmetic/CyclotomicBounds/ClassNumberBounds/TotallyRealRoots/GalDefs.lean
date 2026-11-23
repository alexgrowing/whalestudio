import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc

namespace KStar.TotallyRealRoots

noncomputable def eps (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] :
    Gal(AlgebraicClosure E/E) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (AlgebraicClosure E) l).comp
    (MulSemiringAction.toRingAut Gal(AlgebraicClosure E/E) (AlgebraicClosure E))

noncomputable def galImage (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] : Subgroup ℤ_[l]ˣ :=
  (eps l E).range

noncomputable def nuGal (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] (tr : ℕ) : ℕ∞ :=
  ⨅ g : Gal(AlgebraicClosure E/E),
    emultiplicity (l : ℤ_[l]) (((eps l E g : ℤ_[l]ˣ) : ℤ_[l]) ^ tr - 1)

theorem nuGal_eq_nu (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] (tr : ℕ) :
    nuGal l E tr = nu l (galImage l E) tr := by
  unfold nuGal nu nuStar galImage
  rw [iInf, Set.image_image]
  congr 1
  ext x
  simp [MonoidHom.coe_range]

noncomputable def adjoinRoots (E : Type*) [Field E] (m : ℕ) :
    IntermediateField E (AlgebraicClosure E) :=
  IntermediateField.adjoin E {ζ : AlgebraicClosure E | ζ ^ m = 1}

noncomputable def fieldSubgroup (N : ℕ) [NeZero N] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (E : IntermediateField ℚ K) : Subgroup (ZMod N)ˣ :=
  E.fixingSubgroup.map (IsCyclotomicExtension.Rat.galEquivZMod N K).toMonoidHom

noncomputable def nuLevel (N : ℕ) (H : Subgroup (ZMod N)ˣ) (tr l : ℕ) : ℕ :=
  if h : l.Prime then (@nu l ⟨h⟩ (@levelGroup l ⟨h⟩ N H) tr).toNat else 0

noncomputable def nuField (E : Type*) [Field E] (tr l : ℕ) : ℕ :=
  if h : l.Prime then (@nuGal l ⟨h⟩ E _ tr).toNat else 0

end KStar.TotallyRealRoots
