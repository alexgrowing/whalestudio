import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

section
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]
  {A' : Over (Sp (DualNumber k))} [GrpObj A'] {i : A₀.left ⟶ A'.left}

private theorem resMor (h : IsGrpPullback A₀ A' (epsRed k) i) :
    GrpMor (dp0 (DualNumber k)) (𝟙 _) A' (dp0 k) (𝟙 _) A₀ (TrivSqZeroExt.fstHom k k k).toRingHom (epsRed k) i :=
  GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) (by simp; rfl) h

private theorem frob_sq (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0) :
    GlobalTheory.VB.frob A₀.left p (cast_left p k hk A₀) ≫ i = i ≫ GlobalTheory.VB.frob A'.left p (cast_left p _ hT A') :=
  GlobalTheory.VB.frob_naturality p (cast_left p _ hT A') i (cast_left p k hk A₀)

private theorem pow_dual (hk : (p : k) = 0) (r : DualNumber k) :
    r ^ p = algebraMap k (DualNumber k) (TrivSqZeroExt.fst r ^ p) := by
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_pow]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_pow, nsmul_eq_mul, hk]

private theorem res_frob (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (c : primDR A') :
    (resMor h).pull (frobDR p _ hT A' c) = frobDR p k hk A₀ ((resMor h).pull c) := by
  have F' := frobMor p _ hT A' (cast_left p _ hT A')
  have F₀ := frobMor p k hk A₀ (cast_left p k hk A₀)
  have M := F'.comp (resMor h)
  refine (GrpMor.pull_pull F' (resMor h) M (fun _ ↦ rfl) rfl c).trans
    (GrpMor.pull_pull (resMor h) F₀ M (fun r ↦ ?_) (frob_sq hk hT) c).symm
  simp [frobR_apply, TrivSqZeroExt.fst_pow]

private theorem lift_frob (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (c : primDR A') :
    (liftMor (epsDP k) h).pull (frobDR p _ hT A' c) =
      (constMor A₀).pull (frobDR p k hk A₀ ((resMor h).pull c)) := by
  have F' := frobMor p _ hT A' (cast_left p _ hT A')
  have F₀ := frobMor p k hk A₀ (cast_left p k hk A₀)
  have M := F'.comp (liftMor (epsDP k) h)
  have N := (resMor h).comp F₀
  have e₁ := GrpMor.pull_pull F' (liftMor (epsDP k) h) M (fun _ ↦ rfl) rfl c
  have e₂ := GrpMor.pull_pull (resMor h) F₀ N (fun _ ↦ rfl) rfl c
  have e₃ := GrpMor.pull_pull N (constMor A₀) M (fun r ↦ by
    simp [frobR_apply, pow_dual hk r]) (by simpa using frob_sq hk hT) c
  exact e₁.trans (e₃.symm.trans (congrArg _ e₂.symm))

private theorem res_iter (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (n : ℕ) (c : primDR A') :
    (resMor h).pull ((frobDR p _ hT A')^[n] c) = (frobDR p k hk A₀)^[n] ((resMor h).pull c) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', res_frob hk hT h, ih]

private theorem corr_push {x : HdR A₀} {d : Crys (epsDP k) (epsRed k) A₀}
    (hd : (constMor A₀).Corr x d) (u : A₀ ⟶ A₀) [IsMonHom u] (c : primDR A₀) :
    push (epsDP k) (epsRed k) u d ((constMor A₀).pull c) =
      algebraMap k (DualNumber k) (push (dp0 k) (𝟙 _) u x c) :=
  GrpMor.Corr.push (m := constMor A₀) (constMor A₀) u u (by simp) hd c

private theorem vanish (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (hBC : (constMor A₀).IsBC)
    (g₀ : A₀ ⟶ A₀) (g' : A' ⟶ A') [IsMonHom g₀] [IsMonHom g']
    (hg : i ≫ g'.left = g₀.left ≫ i) (n : ℕ) (x : HdR A₀) (d : Crys (epsDP k) (epsRed k) A₀)
    (hd : (constMor A₀).Corr x d)
    (hx : ∀ z, x (primPull (dp0 k) (𝟙 _) g₀ ((frobDR p k hk A₀)^[n + 1] z)) = 0) (c : primDR A') :
    crysToDR (epsDP k) h d (primPull (dp0 (DualNumber k)) (𝟙 _) g' ((frobDR p _ hT A')^[n + 1] c)) = 0 := by
  have e₁ : crysToDR (epsDP k) h d (primPull (dp0 (DualNumber k)) (𝟙 _) g' ((frobDR p _ hT A')^[n + 1] c)) =
      push (epsDP k) (epsRed k) g₀ d ((liftMor (epsDP k) h).pull ((frobDR p _ hT A')^[n + 1] c)) :=
    (LinearMap.congr_fun (crysToDR_push (epsDP k) h h g₀ g' hg d) _).symm
  have e₂ : (liftMor (epsDP k) h).pull ((frobDR p _ hT A')^[n + 1] c) =
      (constMor A₀).pull ((frobDR p k hk A₀)^[n + 1] ((resMor h).pull c)) := by
    rw [Function.iterate_succ_apply', lift_frob hk hT h, res_iter hk hT h,
      Function.iterate_succ_apply']
  rw [e₁, e₂, corr_push hd g₀, push_apply, hx, map_zero]

private theorem dual_zero_of_span {T M : Type*} [CommRing T] [AddCommGroup M] [Module T M] (L : M →ₗ[T] T)
    {S : Set M} (hS : ∀ s ∈ S, L s = 0) {y : M} (hy : y ∈ Submodule.span T S) : L y = 0 :=
  LinearMap.mem_ker.1 ((Submodule.span_le (p := LinearMap.ker L)).2 (fun s hs ↦ LinearMap.mem_ker.2 (hS s hs)) hy)

private theorem alg_eq (a : k) :
    algebraMap k (DualNumber k) a = TrivSqZeroExt.inl a + TrivSqZeroExt.inr 0 := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

set_option maxHeartbeats 1600000 in
private theorem core (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (hBC : (constMor A₀).IsBC)
    (e₀ g₀ : A₀ ⟶ A₀) (e' g' : A' ⟶ A') [IsMonHom e₀] [IsMonHom g₀] [IsMonHom e'] [IsMonHom g']
    (he : i ≫ e'.left = e₀.left ≫ i) (hg : i ≫ g'.left = g₀.left ≫ i) (f : ℕ) (hf : 0 < f)
    (hNO : NO p (DualNumber k) hT A' e' g' f) (x : HdR A₀)
    (hx : ∀ z, x (primPull (dp0 k) (𝟙 _) g₀ ((frobDR p k hk A₀)^[f] z)) = 0) :
    IsFilLift h (push (dp0 k) (𝟙 _) e₀ x) 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  obtain ⟨d, hd⟩ := hBC.exists x
  refine ⟨push (epsDP k) (epsRed k) e₀ d, ?_, fun c ↦ ?_⟩
  · have hpush := crysToDR_push (epsDP k) h h e₀ e' he d
    change crysToDR (epsDP k) h (push (epsDP k) (epsRed k) e₀ d) ∈ Fil A'
    rw [hpush]
    refine (Submodule.mem_dualAnnihilator _).2 fun y hy ↦ ?_
    have hmem : primPull (dp0 (DualNumber k)) (𝟙 _) e' y ∈ Submodule.span (DualNumber k)
        (Set.range fun c => primPull (dp0 (DualNumber k)) (𝟙 _) g' ((frobDR p (DualNumber k) hT A')^[n + 1] c)) :=
      hNO y hy
    have h0 : crysToDR (epsDP k) h d (primPull (dp0 (DualNumber k)) (𝟙 _) e' y) = 0 :=
      dual_zero_of_span _ (Set.forall_mem_range.2 (vanish hk hT h hBC g₀ g' hg n x d hd hx)) hmem
    exact h0
  · have e₁ := corr_push (x := x) (d := d) hd e₀ c
    exact e₁.trans (alg_eq _)

end

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.estep :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (f : ℕ), 0 < f → ∀ (π : Par p w f)
      (k : Type) [Field k] (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0) (s₀ : Sp k ⟶ Sp R) (s' : Sp (DualNumber k) ⟶ Sp R) (o₀ : Obj b N s₀) (o' : Obj b N s')
      (m : ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), NOo hT o' π →
      ∀ x : HdR o₀.A, (∀ z, x (coh o₀ π.g ((frobDR p k hk o₀.A)^[f] z)) = 0) → IsFilLift m.cart (hom o₀ π.ε x) 0 := by
  intro p _ D R _ b N w f hf π k _ hk hT s₀ s' o₀ o' m hNO x hx
  haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O π.ε)
  haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O π.g)
  haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O π.ε)
  haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O π.g)
  exact core hk hT m.cart (GlobalTheory.HTRealise.isBC_constMor o₀.ab) _ _ _ _ (m.act _).symm (m.act _).symm f hf hNO x hx
