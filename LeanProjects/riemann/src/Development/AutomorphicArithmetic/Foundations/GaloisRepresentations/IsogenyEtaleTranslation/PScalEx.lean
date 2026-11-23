import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (Integ)
open scoped TensorProduct

theorem UpperTheory.Gal.FixZ.scalEx_of :
    UpperTheory.Gal.G3.SysOf → UpperTheory.Gal.FixZ.ScalEx := by
  intro hS p _ D G L h hI
  obtain ⟨f, u, c, k, hsys, -, hk, -⟩ := hS p D G L h hI
  have hkp : k.Coprime p := hsys.2.1
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : p = 1 := by simpa using hkp
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hone : IsIntAf (1 : AfP p) := fun v => by rw [map_one]; exact one_mem _
  have hact : ∀ v, L.actG (GlobalTheory.W2.scalarAf G (GlobalTheory.W2.natUnit p k hk0)) v = k • v :=
    GlobalTheory.W2.actG_natScalar L k hk0
  refine ⟨k, GlobalTheory.W2.scalarAf G (GlobalTheory.W2.natUnit p k hk0), Nat.pos_of_ne_zero hk0, hkp,
    ⟨fun g => GlobalTheory.W2.scalarAf_comm _ g, hact, 1, 1, hone, hone, one_mul 1, ?_⟩, ?_, ?_⟩
  · show ((GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) : AfP p) * (GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) = ((k ^ 2 : ℕ) : AfP p) * 1
    have e : ((GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) : AfP p) = (k : AfP p) := by
      show algebraMap ℚ (AfP p) (k : ℚ) = _
      rw [map_natCast]
    rw [e, mul_one]; push_cast; ring
  · intro v hv
    rw [hact]
    exact nsmul_mem hv k
  · intro v hv
    rw [map_mul, Module.End.mul_apply, hact]
    exact hk v hv
