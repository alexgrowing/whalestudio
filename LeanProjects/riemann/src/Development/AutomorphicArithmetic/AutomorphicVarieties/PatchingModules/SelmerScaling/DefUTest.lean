import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TestEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TrBndDen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.ClosureIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TestVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrVr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.defUTest_smul {F : Type} [CommRing F] {e : ℕ} (c : F) (x : DD F e) :
    c • x = DD.C c * x := rfl

private def UpperTheory.V.Pa.defUTest_a (F : Type) [CommRing F] (e : ℕ) : DD F e →ₗ[F] F where
  toFun x := x.a
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

private def UpperTheory.V.Pa.defUTest_ep (F : Type) [CommRing F] {e : ℕ} (k : Fin e) : DD F e →ₗ[F] F where
  toFun x := x.ep k
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

private def UpperTheory.V.Pa.defUTest_ep' (F : Type) [CommRing F] {e : ℕ} (k : Fin e) : DD F e →ₗ[F] F where
  toFun x := x.ep' k
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

private def UpperTheory.V.Pa.defUTest_eta (F : Type) [CommRing F] (e : ℕ) : DD F e →ₗ[F] F where
  toFun x := x.eta
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

theorem UpperTheory.V.Pa.defUTest :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (e : ℕ) (α : Fin e → S.Bh →+ S.F) (μ : Fin e → S.U.N →+ S.F) (Φ : S.U.N →+ S.F), (∀ k, α k ∈ S.Tp) → (∀ k, μ k ∈ S.La) → (∀ (b : S.Bh) y, Φ (b • y) = S.rF b * Φ y + ∑ k, α k b * μ k y) → ∃ (u : S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.F e)) (ψ : ∀ v, Fin S.n → S.L.Gv v →* (DD S.F e)ˣ), DefU S.h S.x u ψ ∧ (∀ k, epC S.h S.x u k = S.laC (μ k)) ∧ ∀ k, epC' S.h S.x u k = S.alC (α k) := by
  intro l _ S e α μ Φ hα hμ hΦ
  obtain ⟨θ, hT, hθ⟩ := testEx l S e α μ Φ hα hμ hΦ
  obtain ⟨_, hE, _, hψ, hm⟩ := testVal l S (DD S.F e) (DD.aug S.F e) θ hT
  obtain ⟨hord, hine, _, _, _⟩ := vrRel l S
  have hp := prAdd l S
  have hB : ∀ b : S.B, S.pr1 (algebraMap S.B S.U.AA b) = 0 := by
    intro b
    have h1 := (hp.2.1 (algebraMap S.B S.Bh b) 0).2
    simpa [← IsScalarTower.algebraMap_apply] using h1
  let u : S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.F e) := fun g => (S.U.vr g).map θ
  let ψ : ∀ v, Fin S.n → S.L.Gv v →* (DD S.F e)ˣ := fun v i =>
    (Units.map (θ.comp (algebraMap S.B S.U.AA)).toMonoidHom).comp (S.u.ψ v i)
  refine ⟨u, ψ, ?_, ?_, ?_⟩
  · refine
      { one := by simp [u]
        mul := by intro g g'; simp [u, Matrix.map_mul]
        red := ?_
        even := ?_
        form := ?_
        ine := ?_
        ψ_red := ?_
        ψ_even := ?_
        ψ_mu := ?_
        ord := ?_
        bnd := ?_ }
    · intro g
      ext i j
      simp only [u, Matrix.map_apply, hθ]
      exact (prVr l S g i j).1
    · intro g i j
      obtain ⟨_, h1, h2⟩ := prVr l S g i j
      constructor
      · intro hij
        simp only [u, Matrix.map_apply, hθ]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          first
          | (intro h; exact absurd h (by decide))
          | (intro _; funext k; simp [h1 hij])
          | (intro _; simp [h1 hij])
      · intro hij
        simp only [u, Matrix.map_apply, hθ]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          first
          | (intro h; exact absurd h (by decide))
          | (intro _; funext k; simp [h2 hij])
          | (intro _; simp [h2 hij])
    · intro g
      have h := congrArg θ.mapMatrix (S.U.form g)
      simp only [map_mul, RingHom.mapMatrix_apply, Matrix.transpose_map] at h
      rw [show ((S.U.vr g).map θ)ᵀ = ((S.U.vr g)ᵀ).map θ from (Matrix.transpose_map).symm]
      refine h.trans (Matrix.ext fun i j => ?_)
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.one_apply_eq, map_one, mul_one]
        exact (hE g _).trans rfl
      · simp only [Matrix.one_apply_ne hij, map_zero, mul_zero]
    · intro w g hg
      simp [u, hine w g hg]
    · intro v i g
      exact hψ v i g
    · intro v i g
      simp only [ψ, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        RingHom.coe_comp, Function.comp_apply, hθ, hB]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
        | (intro h; exact absurd h (by decide))
        | (intro _; funext k; simp)
        | (intro _; simp)
    · intro v i g hg
      exact Units.ext (hm v i g hg)
    · intro v g
      have h := congrArg θ.mapMatrix (hord v g)
      rw [map_list_prod, map_zero, List.map_ofFn] at h
      refine Eq.trans ?_ h
      refine congrArg List.prod (congrArg List.ofFn (funext fun i => Matrix.ext fun a b => ?_))
      by_cases hab : a = b
      · subst hab
        simp [u, ψ, Matrix.algebraMap_matrix_apply, Matrix.sub_apply]
      · simp [u, ψ, Matrix.algebraMap_matrix_apply, Matrix.sub_apply, hab]
    · intro i j
      exact ⟨trBnd l S _ _ θ hT (defUTest_a S.F e) i j,
        fun k => trBnd l S _ _ θ hT (defUTest_ep S.F k) i j,
        fun k => trBnd l S _ _ θ hT (defUTest_ep' S.F k) i j,
        trBnd l S _ _ θ hT (defUTest_eta S.F e) i j⟩
  · intro k
    funext γ
    simp only [epC, Ctx.laC, u, Matrix.map_map]
    congr 1
    ext i j
    simp [hθ]
  · intro k
    funext γ
    simp only [epC', Ctx.alC, u, Matrix.map_map]
    congr 1
    ext i j
    simp [hθ]
