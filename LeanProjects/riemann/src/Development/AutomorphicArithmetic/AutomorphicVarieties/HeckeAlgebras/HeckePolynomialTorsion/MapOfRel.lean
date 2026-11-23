import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

theorem UpperTheory.V.Hi.JEx.map_of_rel {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) {T : Type} [CommRing T] [Algebra O T]
    [IsCO O T] (φ : Λ.Λ →ₐ[O] T) (D : GDet n T F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Tˣ) (hc : D.IsCont (maximalIdeal T))
    (hred : D.map (res O T : T →+* ResidueField O) = r.Dbar)
    (hpsi : ∀ v i, r.IsPsi v i (ψ v i) ∧ pushCh (φ : Λ.Λ →+* T) (Λ.κ v i) = (ψ v i).comp (F.Iv v).subtype)
    (hrel : (∀ i g, D.lam i (F.star O T n (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1)) ∧
      (∀ v (g : Fin n → F.Gv v) (h : F.G₀), D.tr (MonoidAlgebra.single h 1 * F.oEl v (ψ v) g) = 0) ∧
      ∀ u, ∀ g ∈ r.Ip u, ∀ h : F.G₀, D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) = 0) :
    ∃ f : B.B →ₐ[O] T, B.u.D.map f.toRingHom = D ∧ (∀ v i, pushCh f.toRingHom (B.u.ψ v i) = ψ v i) ∧
      ∀ b, f (Λ.toPair B.u b) = φ b := by
  let p : Pair r T := ⟨D, ψ, hc, hred, fun v i => (hpsi v i).1, hrel.1, hrel.2.1, hrel.2.2⟩
  obtain ⟨f, hf, -⟩ := B.univ T p
  refine ⟨f, hf.1, hf.2, ?_⟩
  let κ' : ∀ v, Fin n → F.Iv v →* Tˣ := fun v i => (ψ v i).comp (F.Iv v).subtype
  have hin : IsInert r κ' := fun v i => ⟨ψ v i, (hpsi v i).1, rfl⟩
  obtain ⟨g, -, hu⟩ := Λ.univ T κ' hin
  have h1 : ∀ v i, pushCh ((f.comp (Λ.toPair B.u) : Λ.Λ →ₐ[O] T) : Λ.Λ →+* T) (Λ.κ v i) = κ' v i := by
    intro v i
    have e1 := LamObj.toPair_spec r Λ B.u v i
    have e2 := hf.2 v i
    calc pushCh ((f.comp (Λ.toPair B.u) : Λ.Λ →ₐ[O] T) : Λ.Λ →+* T) (Λ.κ v i)
        = pushCh (f : B.B →+* T) (pushCh ((Λ.toPair B.u : Λ.Λ →ₐ[O] B.B) : Λ.Λ →+* B.B) (Λ.κ v i)) := by
          ext s
          rfl
      _ = pushCh (f : B.B →+* T) ((B.u.ψ v i).comp (F.Iv v).subtype) := by rw [e1]
      _ = (pushCh (f : B.B →+* T) (B.u.ψ v i)).comp (F.Iv v).subtype := by
          ext s
          rfl
      _ = κ' v i := by rw [e2]
  have h2 : ∀ v i, pushCh (φ : Λ.Λ →+* T) (Λ.κ v i) = κ' v i := fun v i => (hpsi v i).2
  have heq := (hu _ h1).trans (hu _ h2).symm
  intro b
  exact DFunLike.congr_fun heq b
