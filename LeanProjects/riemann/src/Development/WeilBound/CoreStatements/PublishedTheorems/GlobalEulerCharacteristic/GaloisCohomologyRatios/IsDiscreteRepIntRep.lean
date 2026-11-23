import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.Places
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.GEN.X

variable {G : Type} [Group G] {ℓ : ℕ}

noncomputable def intRep (M : Rep.{0} (ZMod ℓ) G) : Rep.{0} (ULift.{0} ℤ) G :=
  Rep.of (k := ULift.{0} ℤ) (X := M)
    { toFun := fun g =>
        { toFun := M.ρ g
          map_add' := map_add _
          map_smul' := fun r m => by
            obtain ⟨r⟩ := r
            exact map_zsmul (M.ρ g).toAddMonoidHom r m }
      map_one' := by ext m; simp
      map_mul' := fun g h => by ext m; simp [Module.End.mul_apply] }

theorem intRep_ρ_apply (M : Rep.{0} (ZMod ℓ) G) (g : G) (m : M) : (intRep M).ρ g m = M.ρ g m := rfl

def intRepEquiv (M : Rep.{0} (ZMod ℓ) G) : M ≃+ intRep M := AddEquiv.refl M

variable [TopologicalSpace G] [IsTopologicalGroup G]

instance isDiscreteRep_intRep (M : Rep.{0} (ZMod ℓ) G) [IsDiscreteRep M] : IsDiscreteRep (intRep M) :=
  ⟨fun a => isOpen_stabilizer M a⟩

instance finite_intRep (M : Rep.{0} (ZMod ℓ) G) [Finite M] : Finite (intRep M) := ‹Finite M›

theorem nsmul_intRep (M : Rep.{0} (ZMod ℓ) G) (m : intRep M) : ℓ • m = 0 := by
  have h : ℓ • (show M from m) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]
  exact h

noncomputable def cohomologyIntEquiv (M : Rep.{0} (ZMod ℓ) G) [IsDiscreteRep M] (n : ℕ) :
    cohomology M n ≃+ cohomology (intRep M) n :=
  cohomologyAddEquivOfEquiv (intRepEquiv M) (fun _ _ => rfl) n

end PositivityTheory.Lit1.GEN.X
