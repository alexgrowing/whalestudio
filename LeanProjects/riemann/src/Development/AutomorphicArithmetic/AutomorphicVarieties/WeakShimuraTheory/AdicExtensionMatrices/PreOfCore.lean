import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ChConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PairNear

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isGSp_map' {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {ν : R} {X : M4 R}
    (h : IsGSp ν X) : IsGSp (f ν) (X.map f) := by
  unfold IsGSp at *
  ext i j
  have := congrArg f (congrFun (congrFun h i) j)
  simpa [Matrix.mul_apply, adj_apply, Matrix.one_apply, map_sum, apply_ite f] using this

open Classical in
theorem UpperTheory.V.Ws.sxPreOfCore :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ}, (∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v) → Core Φ a → Nonempty (Pre Φ a) := by
  intro O Γ _ _ _ Φ Λ _ _ a hMu X
  obtain ⟨A, cA, aA, n, hft, hgen, hfl, huniv⟩ := sxChart X.D
  letI aBA : Algebra X.B A := ((algebraMap X.A A).comp (algebraMap X.B X.A)).toAlgebra
  letI aLA : Algebra Λ A := ((algebraMap X.A A).comp (algebraMap Λ X.A)).toAlgebra
  have hB : ∀ b, algebraMap X.B A b = algebraMap X.A A (algebraMap X.B X.A b) := fun _ => rfl
  have hL : ∀ b, algebraMap Λ A b = algebraMap X.A A (algebraMap Λ X.A b) := fun _ => rfl
  haveI t1 : IsScalarTower X.B X.A A := IsScalarTower.of_algebraMap_eq hB
  haveI t2 : IsScalarTower Λ X.B A := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hB, hL, ← IsScalarTower.algebraMap_apply Λ X.B X.A]
  let P : PD Φ.ι Γ A := ⟨mapRep (algebraMap X.A A) X.D.r, n⟩
  have hr : ∀ g, P.r g = (X.D.r g).map (algebraMap X.A A) := fun _ => rfl
  have hψ : ∀ v i (s : Φ.Gv v), P.ψ v i s = algebraMap X.A A (X.D.ψ v i s) := fun v i s => hfl.char v i s
  refine ⟨{ A := A, B := X.B, ft := X.ft.trans hft, P := P, pair := ?_, cont := ?_, gen := ?_, cp := X.cp,
            cp_map := ?_, cp_cont := X.cp_cont, cp_red := X.cp_red,
            ψ := fun v i s => if h : s ∈ Φ.Gv v then X.ψ v i ⟨s, h⟩ else 0,
            ψ_map := ?_, ψ_cont := ?_, ψ_red := ?_, genB := ?_, univ := ?_ }⟩
  · refine ⟨fun g => isGSp_map' (algebraMap X.A A) (X.rep.mult g), fun g hg => ?_, ?_, hfl.low, hfl.flag,
      fun v s hs i => ?_⟩
    · rw [hr, X.rep.kill g hg, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [hr]
      exact X.rep.nrm.map (map_zero _)
    · exact (hfl.char v i ⟨s, hMu v s hs⟩).trans (hfl.mu v i ⟨s, hMu v s hs⟩ hs)
  · intro i j
    refine adicCont_map (algebraMap X.A A) ?_ (X.cont i j)
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact Ideal.mem_map_of_mem (algebraMap X.B A) hb
  · rw [eq_top_iff]
    set S := Algebra.adjoin X.B ((Set.range fun x : Γ × Fin 4 × Fin 4 => P.r x.1 x.2.1 x.2.2) ∪
      Set.range fun x : Φ.ι × Fin 4 × Fin 4 => P.n x.1 x.2.1 x.2.2) with hS
    have h0 : ∀ x : X.A, algebraMap X.A A x ∈ S := by
      intro x
      have hx : x ∈ Algebra.adjoin X.B (Set.range fun x : Γ × Fin 4 × Fin 4 => X.D.r x.1 x.2.1 x.2.2) := by
        rw [X.gen]; trivial
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        exact Algebra.subset_adjoin (Or.inl ⟨y, rfl⟩)
      | algebraMap b => exact S.algebraMap_mem b
      | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact S.mul_mem hx hy
    rintro x -
    have hx : x ∈ Algebra.adjoin X.A (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) := by
      rw [hgen]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Or.inr hx)
    | algebraMap b => exact h0 b
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | mul x y _ _ hx hy => exact S.mul_mem hx hy
  · intro g
    rw [hr, Matrix.charpoly_map, ← X.cp_map, Polynomial.map_map]
    rfl
  · intro v i s hs
    rw [dif_pos hs, hB, X.ψ_map]
    exact (hψ v i ⟨s, hs⟩).symm
  · intro v i
    simpa using X.ψ_cont v i
  · intro v i s hs
    rw [dif_pos hs]
    exact X.ψ_red v i ⟨s, hs⟩
  · intro R _ _ _ f f' h1 h2
    refine X.genB R f f' h1 fun v i s => ?_
    simpa using h2 v i s s.2
  · intro R _ _ _ c Q hc hQ
    obtain ⟨τ, D', hN, hDr, hF⟩ := sxPairNear c Q hc hQ
    obtain ⟨f, hf⟩ := X.univ R τ D' hN
    obtain ⟨F, hF1, hF2⟩ := huniv R (f : X.A →+* R) Q.n (hf ▸ hF)
    have hF3 : ∀ x, F (algebraMap X.A A x) = f x := fun x => RingHom.congr_fun hF1 x
    refine ⟨{ F with commutes' := fun x => ?_ }, ?_⟩
    · exact (hF3 _).trans (f.commutes x)
    · refine PD.ext ?_ (funext hF2)
      rw [← hDr, ← hf]
      ext g i j
      exact hF3 _
