import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CRes

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private def locS {L : Type} (F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    (b : 𝓞 L) : Subring F where
  carrier := {x | ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → P.valuation F x ≤ 1}
  one_mem' := fun P _ => by simp
  zero_mem' := fun P _ => by simp
  mul_mem' := fun {x y} hx hy P hP => by
    rw [map_mul]; exact mul_le_one' (hx P hP) (hy P hP)
  add_mem' := fun {x y} hx hy P hP => Valuation.map_add_le _ (hx P hP) (hy P hP)
  neg_mem' := fun {x} hx P hP => by rw [Valuation.map_neg]; exact hx P hP

private theorem exists_res {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    {k : Type} [Field k] (r : 𝓞 F →+* k) (b : 𝓞 L) (hb : r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0) (σ : F ≃ₐ[L] F) :
    ∃ ρ : locS F b →+* k, ∀ x : locS F b, ResF r (σ x) (ρ x) := by
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.V.ZK.Cl.cRes L F k r
  obtain ⟨a1, a2, a3, a4, -⟩ := UpperTheory.V.ZK.Cl.cAct L F
  have hex : ∀ x : locS F b, ∃ u, ResF r (σ x) u := by
    intro x
    refine ((h4 b hb).1 (σ x) fun P hP => ?_).2
    have e : P = actP σ (actP σ⁻¹ P) := by rw [← a2, mul_inv_cancel, a3]
    rw [e, a1]
    exact x.2 _ (by rwa [a4])
  choose f hf using hex
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · refine h1 _ _ _ (hf 1) ?_
    simpa using h2 1
  · intro x y
    refine h1 _ _ _ (hf (x * y)) ?_
    simpa using (h3 _ _ _ _ (hf x) (hf y)).2
  · refine h1 _ _ _ (hf 0) ?_
    simpa using h2 0
  · intro x y
    refine h1 _ _ _ (hf (x + y)) ?_
    simpa using (h3 _ _ _ _ (hf x) (hf y)).1

private theorem exists_mat {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    {I : Type} [Fintype I] [DecidableEq I] (b : 𝓞 L) (g : (I → F) →ₗ[F] (I → F))
    (hg : ∀ x, InLoc b x → InLoc b (g x)) :
    ∃ A : Matrix I I (locS F b), (locS F b).subtype.mapMatrix A = LinearMap.toMatrix' g := by
  refine ⟨fun i j => ⟨g (Pi.single j 1) i, hg _ (fun i' P _ => ?_) i⟩, ?_⟩
  · by_cases h : i' = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl

theorem UpperTheory.V.ZK.Cl.cMat :
    UpperTheory.V.ZK.Cl.CMat := by
  intro L F _ _ _ _ _ I _ k _ r b hb g hg
  classical
  obtain ⟨A, hA⟩ := exists_mat b (g : (I → F) →ₗ[F] (I → F)) fun x hx => (hg x).1 hx
  obtain ⟨B, hB⟩ := exists_mat b (g.symm : (I → F) →ₗ[F] (I → F)) fun x hx =>
    (hg _).2 (by simpa using hx)
  have hinj : Function.Injective ((locS F b).subtype.mapMatrix : Matrix I I (locS F b) → Matrix I I F) := by
    intro X Y h
    ext i j
    exact congrFun (congrFun h i) j
  have hAB : A * B = 1 := by
    apply hinj
    rw [map_mul, hA, hB, ← LinearMap.toMatrix'_comp, map_one]
    simp
  have hBA : B * A = 1 := by
    apply hinj
    rw [map_mul, hA, hB, ← LinearMap.toMatrix'_comp, map_one]
    simp
  have hdet : ((LinearEquiv.det g : Fˣ) : F) = (A.det : locS F b) := by
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix', ← hA, ← RingHom.map_det]
    rfl
  refine ⟨fun P hP => ?_, fun σ => ?_⟩
  · have h1 : ((A.det : locS F b) : F) * (B.det : locS F b) = 1 := by
      rw [← Subring.coe_mul, ← Matrix.det_mul, hAB]; simp
    have h2 := congrArg (P.valuation F) h1
    rw [map_mul, map_one] at h2
    have h3 : P.valuation F ((A.det : locS F b) : F) = 1 :=
      le_antisymm (A.det.2 P hP) (h2.symm.le.trans (mul_le_of_le_one_right' (B.det.2 P hP)))
    rw [ordP, hdet, h3]; simp
  · obtain ⟨ρ, hρ⟩ := exists_res r b hb σ
    obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.V.ZK.Cl.cRes L F k r
    refine ⟨Matrix.toLin'OfInv (M := ρ.mapMatrix B) (M' := ρ.mapMatrix A)
      (by rw [← map_mul, hBA, map_one]) (by rw [← map_mul, hAB, map_one]), ?_, fun w u hw hu i => ?_⟩
    · have := hρ A.det
      rw [← hdet, RingHom.map_det, ← LinearMap.det_toLin'] at this
      unfold Res
      rw [LinearEquiv.coe_det]
      exact this
    · let w' : I → locS F b := fun i => ⟨w i, hw i⟩
      have e1 : u = fun i => ρ (w' i) := funext fun i => h1 _ _ _ (hu i) (hρ (w' i))
      have e2 : g w i = (A.mulVec w' i : locS F b) := by
        have : g w = Matrix.mulVec (LinearMap.toMatrix' (g : (I → F) →ₗ[F] (I → F))) w := by
          simp
        rw [this, ← hA]
        exact (RingHom.map_mulVec (locS F b).subtype A w' i).symm
      have := hρ (A.mulVec w' i)
      rw [← e2, RingHom.map_mulVec] at this
      rw [e1]
      exact this
