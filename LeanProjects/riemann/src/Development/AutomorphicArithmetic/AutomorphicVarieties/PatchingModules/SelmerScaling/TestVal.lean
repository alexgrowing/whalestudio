import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem padicInt_ringHom_finite_field_eq {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (φ ψ : ℤ_[p] →+* K) (z : ℤ_[p]) : φ z = ψ z := by
  have key : ∀ χ : ℤ_[p] →+* K, IsLocalRing.maximalIdeal ℤ_[p] ≤ RingHom.ker χ := by
    intro χ
    have hne : RingHom.ker χ ≠ ⊥ := by
      intro h
      have hinj : Function.Injective χ := (RingHom.injective_iff_ker_eq_bot χ).mpr h
      haveI : Finite ℤ_[p] := Finite.of_injective χ hinj
      haveI : Infinite ℤ_[p] := Infinite.of_injective (Nat.cast : ℕ → ℤ_[p]) Nat.cast_injective
      exact not_finite ℤ_[p]
    have hmax : (RingHom.ker χ).IsMaximal := (RingHom.ker_isPrime χ).isMaximal hne
    exact (IsLocalRing.eq_maximalIdeal hmax).ge
  have h1 := key φ (PadicInt.sub_zmodRepr_mem z)
  have h2 := key ψ (PadicInt.sub_zmodRepr_mem z)
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, map_natCast, map_natCast]

theorem UpperTheory.V.Pa.testVal :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (R : Type) [CommRing R] [Algebra S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R), S.Test R e θ → (∀ c : S.O, θ (algebraMap S.B S.U.AA (algebraMap S.O S.B c)) = algebraMap S.F R (algebraMap S.x.A S.F (algebraMap S.O S.x.A c))) ∧ (∀ (g : S.G.G₀) (m : ℤ), θ (algebraMap S.B S.U.AA ((S.G.frame.eps S.O S.B g ^ m : S.Bˣ) : S.B)) = algebraMap S.F R (algebraMap S.x.A S.F ((S.G.frame.eps ℤ_[l] S.x.A g ^ m : S.x.Aˣ) : S.x.A))) ∧ θ (algebraMap S.B S.U.AA S.P.s) = algebraMap S.F R (algebraMap S.x.A S.F S.x.t) ∧ (∀ v i g, e (θ (algebraMap S.B S.U.AA (S.u.ψ v i g))) = algebraMap S.x.A S.F (S.x.ψ v i g)) ∧ ∀ v i, ∀ g ∈ S.G.frame.mu v, θ (algebraMap S.B S.U.AA (S.u.ψ v i g)) = 1 := by
  intro l _ S R _ _ e θ hT
  have hB : ∀ b : S.B, algebraMap S.B S.U.AA b = algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b) :=
    fun b => IsScalarTower.algebraMap_apply S.B S.Bh S.U.AA b
  have hO : ∀ c : S.O, θ (algebraMap S.B S.U.AA (algebraMap S.O S.B c)) =
      algebraMap S.F R (algebraMap S.x.A S.F (algebraMap S.O S.x.A c)) := by
    intro c
    obtain ⟨o, ho⟩ := S.oo_O c
    rw [hB, ← ho, hT.oo o, ho, S.rF_f, S.P.f.commutes]
  have hpr : ∀ b : S.Bh, S.pr0 (algebraMap S.Bh S.U.AA b) = b := by
    intro b
    have h1 := (Ctx.exists_pr S (algebraMap S.Bh S.U.AA b)).choose_spec
    have h2 : algebraMap S.Bh S.U.AA b - algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b))
        ∈ (1 : Submodule S.Bh S.U.AA) := by
      rw [← map_sub]
      exact Submodule.mem_one.mpr ⟨_, rfl⟩
    have h4 := (Submodule.disjoint_def.mp S.U.compl.disjoint) _ h2 h1
    rw [← map_sub] at h4
    have h5 := S.U.inj (h4.trans (map_zero _).symm)
    exact (sub_eq_zero.mp h5).symm
  refine ⟨hO, ?_, ?_, ?_, ?_⟩
  · intro g m
    rw [← map_zpow, ← map_zpow]
    show θ (algebraMap S.B S.U.AA (algebraMap S.O S.B (algebraMap ℤ_[l] S.O _))) = _
    rw [hO]
    congr 2
    change algebraMap S.O S.x.A (algebraMap ℤ_[l] S.O _) = algebraMap ℤ_[l] S.x.A (algebraMap ℤ_[l] ℤ_[l] _)
    rw [Algebra.algebraMap_self, RingHom.id_apply,
      IsScalarTower.algebraMap_apply ℤ_[l] S.x.K (PowerSeries S.x.K),
      IsScalarTower.algebraMap_apply S.O S.x.K (PowerSeries S.x.K)]
    congr 1
    exact padicInt_ringHom_finite_field_eq ((algebraMap S.O S.x.K).comp (algebraMap ℤ_[l] S.O)) (algebraMap ℤ_[l] S.x.K) _
  · obtain ⟨o, ho⟩ := S.ordinaryPointSection
    rw [hB, ← ho, hT.oo o, ho, S.rF_f, S.P.f_s]
  · intro v i g
    rw [hT.res, hB, hpr, S.rF_f]
    have h := congrArg (fun χ => ((χ g : S.x.Aˣ) : S.x.A)) (S.P.maps.2 v i)
    exact congrArg _ h
  · intro v i g hg
    have hψ : ((S.u.ψ v i g : S.Bˣ) : S.B) = algebraMap S.O S.B ((S.r.th v i ⟨g, hg⟩ : S.Oˣ) : S.O) :=
      (S.u.psi v i).mu ⟨g, hg⟩
    have h := congrArg (fun χ => ((χ g : S.x.Aˣ) : S.x.A)) (S.P.maps.2 v i)
    have h' : S.P.f ((S.u.ψ v i g : S.Bˣ) : S.B) = ((S.x.ψ v i g : S.x.Aˣ) : S.x.A) := h
    rw [hψ, hO, ← S.P.f.commutes, ← hψ, h', S.x.ψ_mu v i g hg]
    simp
