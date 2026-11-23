import Development.AutomorphicArithmetic.QuadraticCharacters.MemRealCyclotomicSubgroup

open NumberField

namespace HostParam

namespace AbField

variable (E : AbField)

abbrev Cyc : Type := CyclotomicField E.N ℚ

instance : IsCyclotomicExtension {E.N} ℚ E.Cyc := CyclotomicField.isCyclotomicExtension E.N ℚ

noncomputable def cycGal : Gal(E.Cyc/ℚ) ≃* (ZMod E.N)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod E.N E.Cyc

noncomputable def field : IntermediateField ℚ E.Cyc :=
  IntermediateField.fixedField (E.H.comap E.cycGal.toMonoidHom)

instance : IsAbelianGalois ℚ E.Cyc := IsCyclotomicExtension.isAbelianGalois {E.N} ℚ E.Cyc

noncomputable instance : NumberField E.field := inferInstance

instance : IsAbelianGalois ℚ E.field := IsAbelianGalois.tower_bot ℚ E.field E.Cyc

noncomputable def galRes : (ZMod E.N)ˣ →* Gal(E.field/ℚ) :=
  (AlgEquiv.restrictNormalHom E.field).comp E.cycGal.symm.toMonoidHom

end AbField

end HostParam
