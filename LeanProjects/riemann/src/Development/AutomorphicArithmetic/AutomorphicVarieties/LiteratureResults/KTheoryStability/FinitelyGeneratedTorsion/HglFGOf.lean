import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.FinitelyGeneratedTorsion.TensTorsion
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly

noncomputable section

open CategoryTheory NumberField

namespace UpperTheory.FiniteGenerationAndTorsion

open UpperTheory.V UpperTheory.V.KH

theorem hglFG_of (h : FgShift) : HglFG := by
  intro L _ _ hL N m
  have := hL
  let C := faceCx (KT.Gm L N) (KT.Sx L N) (KT.Sx.face L N) KT.Sx.face_smul
  have hx := KT.sx_exact L N m
  exact h (KT.Gm L N) (KT.orbBound L N m) (3 ^ (KT.dd L N * N)) m (KT.Sx L N)
    (fun p => Rep.ofHom ⟨C.d p, fun g => LinearMap.ext fun f => C.d_equiv p g f⟩)
    (Rep.trivial ℤ (KT.Gm L N) ℤ)
    (Rep.ofHom ⟨C.ε, fun g => LinearMap.ext fun f => C.ε_equiv g f⟩)
    (Nat.one_le_pow _ _ (by norm_num)) hx.1 hx.2.1 hx.2.2
    (fun p hp => ⟨(KT.orb L N p).1, (KT.orb L N p).2.trans (KT.orbBound_mono L N hp)⟩)
    (fun p _ => KT.stab L N p)

end UpperTheory.FiniteGenerationAndTorsion

end
