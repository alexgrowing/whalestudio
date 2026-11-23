import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_adele {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (c : Kw w) :
    ∃ a : Af L, pLoc L w a = c ∧ ∀ u : Plc L, u ≠ w → pLoc L u a = 0 := by
  classical
  refine ⟨⟨Function.update (fun _ => 0) w c, ?_⟩, ?_, ?_⟩
  · filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with u hu
    have hu' : u ≠ w := hu
    simp [Function.update_of_ne hu']
  · show Function.update (fun _ => 0) w c w = c
    simp
  · intro u hu
    show Function.update (fun _ => 0) w c u = 0
    simp [Function.update_of_ne hu]

private theorem decomp {K : Type} [Field K] {D : K} (x : Lsq K D) :
    x = algebraMap K (Lsq K D) x.re + algebraMap K (Lsq K D) x.im * QuadraticAlgebra.omega := by
  ext <;> simp

private theorem omega_sq {K : Type} [Field K] {D : K} :
    (QuadraticAlgebra.omega : Lsq K D) * QuadraticAlgebra.omega = algebraMap K (Lsq K D) D := by
  ext <;> simp

private theorem ne_zero_of_equiv {K M : Type} [Field K] [Field M] {D : K} (e : Lsq K D ≃+* M) : D ≠ 0 := by
  rintro rfl
  have hz : e QuadraticAlgebra.omega * e QuadraticAlgebra.omega = 0 := by
    rw [← map_mul, omega_sq, map_zero, map_zero]
  have hz' : e QuadraticAlgebra.omega = 0 := mul_self_eq_zero.mp hz
  have hz'' : (QuadraticAlgebra.omega : Lsq K 0) = 0 := e.injective (by rw [hz', map_zero])
  have := congrArg QuadraticAlgebra.im hz''
  simp at this

theorem UpperTheory.V.Z.Sym.Dict.Br.splitCore :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (w : Plc L), IsSplitAt w → ∃ (s : Kv (un w)) (hs : s * s = cv (un w) R.Δ) (i : Kv (un w) ≃+* Kw w), s ≠ 0 ∧ ∀ x, R.ρ _ w rfl x = i (Sig.proj hs x) := by
  intro L _ _ _ R w hw
  obtain ⟨u, huw, hu⟩ := hw
  have hu' : un u = un w := hu
  let f : Kv (un w) →+* Kw w := (R.ρ _ w rfl).comp (algebraMap _ _)
  have hf : Function.Injective f := f.injective
  have hdec : ∀ x : Lsq (Kv (un w)) (cv (un w) R.Δ),
      R.ρ _ w rfl x = f x.re + f x.im * R.ρ _ w rfl QuadraticAlgebra.omega := by
    intro x
    conv_lhs => rw [decomp x]
    simp [f]
  obtain ⟨a₁, h₁u, h₁o⟩ := exists_adele u (1 : Kw u)
  obtain ⟨y, hy⟩ := R.ρ_surj (un w) a₁
  have hyw : R.ρ _ w rfl y = 0 := (hy w rfl).trans (h₁o w huw.symm)
  have hyu : R.ρ _ u hu' y = 1 := (hy u hu').trans h₁u
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hyu
  have him : y.im ≠ 0 := by
    intro h0
    apply hy0
    have h1 := hdec y
    rw [hyw, h0, map_zero, zero_mul, add_zero] at h1
    have h2 : y.re = 0 := hf (by rw [← h1, map_zero])
    exact QuadraticAlgebra.ext h2 h0
  have hfim : f y.im ≠ 0 := fun h => him (hf (by rw [h, map_zero]))
  set r := R.ρ _ w rfl QuadraticAlgebra.omega with hr
  let s : Kv (un w) := -y.re / y.im
  have hrs : r = f s := by
    have h1 := hdec y
    rw [hyw] at h1
    simp only [s, map_div₀, map_neg]
    field_simp
    linear_combination -h1
  have hs : s * s = cv (un w) R.Δ := by
    apply hf
    rw [map_mul, ← hrs, hr, ← map_mul, omega_sq]
    rfl
  have hsur : Function.Surjective f := by
    intro c
    obtain ⟨a, hac, -⟩ := exists_adele w c
    obtain ⟨x, hx⟩ := R.ρ_surj (un w) a
    refine ⟨Sig.proj hs x, ?_⟩
    have h1 := hdec x
    rw [hx w rfl, hac, hrs] at h1
    rw [h1]
    simp [Sig.proj, mul_comm]
  refine ⟨s, hs, RingEquiv.ofBijective f ⟨hf, hsur⟩, ?_, ?_⟩
  · intro h0
    apply ne_zero_of_equiv R.e
    have h1 : cv (un w) R.Δ = 0 := by rw [← hs, h0, zero_mul]
    exact (cv (un w)).injective (by rw [h1, map_zero])
  · intro x
    rw [hdec x, hrs]
    show _ = f (Sig.proj hs x)
    simp [Sig.proj, mul_comm]
