import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem lsq_eq (l p L : ℕ) (h : Nat.Coprime p l) : lsqInv l p L = inv1 p l ^ (2 * L) := by
  have h1 : IsUnit (l : ZMod p) := (ZMod.isUnit_iff_coprime l p).2 h.symm
  have h2 : IsUnit ((l : ZMod p) ^ (2 * L)) := h1.pow _
  unfold lsqInv inv1
  rw [dif_pos h1, dif_pos h2, inv_pow]
  congr 1
  ext
  simp

private theorem arg_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) [NeZero M]
    (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ) : (repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹) ∈ fixMu Ω M := by
  obtain ⟨-, -, -, -, -, -, -, hM⟩ := sSlD Ω ε X 1 one_pos
  have mul : ∀ a b : Ω ≃ₐ[ℚ] Ω, cycM M (a * b) = cycM M a * cycM M b := fun a b => (hM M a).2.1 b
  have rep : ∀ y : (ZMod M)ˣ, cycM M (repM (Ω := Ω) M y) = y := (hM M s).2.2.1
  let f : (Ω ≃ₐ[ℚ] Ω) →* (ZMod M)ˣ := MonoidHom.mk' (cycM M) mul
  rw [(hM M _).2.2.2.1]
  have e : f ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)) = 1 := by
    simp only [map_mul, map_inv]
    change (cycM M (repM (Ω := Ω) M y))⁻¹ * cycM M s * cycM M (repM (Ω := Ω) M (y * (cycM M s)⁻¹)) = 1
    rw [rep, rep, mul_comm y, ← mul_assoc, mul_inv_cancel_right, inv_mul_cancel]
  exact e

private theorem lift_push {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (N w n c M : ℕ) [NeZero N] [NeZero M] {T ι : Type} [DecidableEq T] [Fintype ι] (π : (ZMod M)ˣ → T)
    (z : ι → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (h : ∀ σ ∈ fixMu Ω M, LiftB X l N w n c (∑ i, z i σ) (bB σ)) (s : Ω ≃ₐ[ℚ] Ω) (t : T) :
    LiftB X l N w n c (∑ i, GlobalTheory.KA.push π (shB X l M (z i)) s t) (GlobalTheory.KA.push π (shB X l M bB) s t) := by
  obtain ⟨-, -, -, hSum, -, -, hGal, -⟩ := sApi Ω ε X l n
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have key : ∀ y : (ZMod M)ˣ, LiftB X l N w n c (∑ i, shB X l M (z i) s y) (shB X l M bB s y) := by
    intro y
    have hy := h _ (arg_mem X M s y)
    refine ⟨(sBStab Ω ε X l N w hN _ hy.1).1 _, ?_⟩
    have hc : CgF X l n (bB ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)))
        ((l : ℤ_[l]) ^ c • ∑ i, z i ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹))) := hy.2
    have hg := hGal (repM M y) _ _ hc
    have e : (l : ℤ_[l]) ^ c • ∑ i, shB X l M (z i) s y = X.galB l (repM M y)
        ((l : ℤ_[l]) ^ c • ∑ i, z i ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹))) := by
      simp only [shB, map_smul, map_sum]
    intro u
    have hu := hg u
    rw [← e] at hu
    exact hu
  have hpush : ∀ Y : (Ω ≃ₐ[ℚ] Ω) → (ZMod M)ˣ → X.Fn l,
      GlobalTheory.KA.push π Y s t = ∑ y ∈ Finset.univ.filter (fun y => π y = t), Y s y := fun Y => rfl
  simp only [hpush]
  rw [Finset.sum_comm]
  refine ⟨Submodule.sum_mem _ (fun y _ => (key y).1), ?_⟩
  have hs := hSum _ (Finset.univ.filter (fun y => π y = t)) (fun y => shB X l M bB s y)
    (fun y => (l : ℤ_[l]) ^ c • ∑ i, shB X l M (z i) s y) (fun y _ => (key y).2)
  rw [← Finset.smul_sum] at hs
  exact hs

theorem UpperTheory.V.Z.Kato.Nb.sRelT :
    UpperTheory.V.Z.Kato.Nb.SRelT := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he p _ hp c₀ Y hY r n
  obtain ⟨bB, hB, b, hb, hC⟩ := hY r n
  obtain ⟨-, -, -, -, hadd, -, -, hgal, -⟩ := hA
  have hw : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hB' : ∀ σ ∈ fixMu Ω (lvT l n r N p), LiftB X l N (2 * e - 1) n c₀ (∑ r₀, clsT X l n r N p x c d (2 * e - 1) (gm r₀) σ) (bB σ) := by
    intro σ hσ
    rw [← hw]
    exact hB σ hσ
  refine ⟨fun s y => GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) bB) s (y.1 * inv1 p l ^ (2 * (r + n)), y.2), b,
    fun s y => lift_push X l N _ n c₀ _ (rdT l n r N p) _ bB hB' s _, hb, fun s y => ?_⟩
  have key : ∀ t, pr (GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) bB) s t) = YfBT X l pr W e ψ n r N p bB s t := by
    intro t
    have hs := map_sum (AddMonoidHom.mk' pr hadd) (shB X l (lvT l n r N p) bB s)
      (Finset.univ.filter fun y' => rdT l n r N p y' = t)
    refine hs.trans (Finset.sum_congr rfl fun y' _ => ?_)
    exact hgal _ _ (hB' _ (arg_mem X _ s y')).1
  have := hC s y
  rw [lsq_eq l p _ hp, ← key] at this
  exact this
