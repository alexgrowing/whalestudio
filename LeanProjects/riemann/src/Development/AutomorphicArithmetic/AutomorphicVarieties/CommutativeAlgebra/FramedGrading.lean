import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TactVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private def tc {R ι X : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X)
    (t : Multiplicative X →* Rˣ) : Matrix ι ι R →* Matrix ι ι R where
  toFun h := Matrix.of fun a b => (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b
  map_one' := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  map_mul' h h' := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : w a - w b = (w a - w c) + (w c - w b) := by abel
    rw [this, ofAdd_add, map_mul, Units.val_mul]
    ring

private theorem tc_apply {R ι X : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X)
    (t : Multiplicative X →* Rˣ) (h : Matrix ι ι R) (a b : ι) :
    tc w t h a b = (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b := rfl

private theorem tc_fix {R ι X : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X)
    (t : Multiplicative X →* Rˣ) (h : Matrix ι ι R) (hh : ∀ a b, w a ≠ w b → h a b = 0) : tc w t h = h := by
  ext a b
  rw [tc_apply]
  by_cases hab : w a = w b
  · simp [hab]
  · simp [hh a b hab]

private theorem map_mul_alg {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] [DecidableEq ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

section

variable {O : Type} [CommRing O] [IsLocalRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X]
  {w : ι → X} {Φ : FormData O w} {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {rbar : Γ →* Matrix ι ι (ResidueField O)} {r0 : Γ →* Matrix ι ι O}
  {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

private def tl (w : ι → X) (t : Multiplicative X →* Rˣ) (ht : ∀ j, res O R (t j) = 1) (r : Lift O rbar R) :
    Lift O rbar R where
  hom := (tc w t).comp r.hom
  cont a b N := by
    have := (r.cont a b N).comp
      (fun x => Ideal.Quotient.mk (maximalIdeal R ^ N) (t (Multiplicative.ofAdd (w a - w b)) : R) * x)
    exact this
  red g a b := by
    show res O R ((t (Multiplicative.ofAdd (w a - w b)) : R) * r.hom g a b) = _
    rw [map_mul, ht, one_mul, r.red]

private theorem inH_comap {r : Lift O rbar R} (h : Φ.InH r0 R r) {H : Type} [Group H] [TopologicalSpace H]
    (φ : H →* Γ) (hφ : Continuous φ) : Φ.InH (r0.comp φ) R (r.comap φ hφ) := fun s => by
  have := h (φ s)
  rw [← map_inv] at this
  exact this

variable {F : Frame Γ} {L : ∀ q, Cond O (rbar.comp (F.ψ q))}
  {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B}

private theorem framed_map (hL : ∀ q, Φ.IsLocCond (r0.comp (F.ψ q)) (F.N q) (L q)) {i : B →ₐ[O] R}
    {r : Lift O rbar R} {α : F.T → Matrix ι ι R} (h : IsFramed Φ r0 F L ρ i r α)
    {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') :
    IsFramed Φ r0 F L ρ (f.comp i) (r.map f) (fun v => (α v).map f) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hm := (hh_group O ι X w Φ R).2.2.2.1 R' f
  refine ⟨fun s => ?_, fun q => ?_, fun v => hm _ (h3 v), ?_, fun v s => ?_⟩
  · have := hm _ (h1 s)
    have e : ((r0 s⁻¹).map (algebraMap O R)).map f = (r0 s⁻¹).map (algebraMap O R') := by
      ext a b
      simp
    rw [map_mul_alg, e] at this
    exact this
  · obtain ⟨I, hI⟩ := (hL q).closed R _ (inH_comap h1 (F.ψ q) (F.hψ q))
    have h0 := (hI R (AlgHom.id O R)).1 (h2 q)
    exact (hI R' f).2 fun x hx => by rw [show x = 0 from h0 x hx, map_zero]
  · simp [h4]
  · have := congrArg (fun A : Matrix ι ι R => A.map f) (h5 v s)
    simp only [map_mul_alg] at this
    exact this

private theorem framed_torus (hL : ∀ q, Φ.IsLocCond (r0.comp (F.ψ q)) (F.N q) (L q))
    (h0 : ∀ g a b, w a ≠ w b → r0 g a b = 0) {i i' : B →ₐ[O] R}
    {r : Lift O rbar R} {α : F.T → Matrix ι ι R} (h : IsFramed Φ r0 F L ρ i r α)
    (t : Multiplicative X →* Rˣ) (ht : ∀ j, res O R (t j) = 1)
    (hi : ∀ v s a b, i' ((ρ v).hom s a b) = t (Multiplicative.ofAdd (w a - w b)) * i ((ρ v).hom s a b)) :
    IsFramed Φ r0 F L ρ i' (tl w t ht r) (fun v => tc w t (α v)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hm : ∀ h, Φ.HH h → Φ.HH (tc w t h) := (hh_group O ι X w Φ R).2.2.2.2.2 t
  refine ⟨fun s => ?_, fun q => ?_, fun v => hm _ (h3 v), ?_, fun v s => ?_⟩
  · have := hm _ (h1 s)
    rw [map_mul, tc_fix w t ((r0 s⁻¹).map _) fun a b hab => by simp [h0 _ a b hab]] at this
    exact this
  · exact (hL q).torus R _ _ t (inH_comap h1 (F.ψ q) (F.hψ q)) ht (fun g a b => rfl) (h2 q)
  · simp [h4]
  · have := congrArg (tc w t) (h5 v s)
    simp only [map_mul] at this
    have e : ((ρ v).hom s).map i' = tc w t (((ρ v).hom s).map i) := by
      ext a b
      exact hi v s a b
    rw [e]
    exact this

end

private theorem algHom_ext_on_generators {O X : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] {B : Type} [CommRing B] [Algebra O B] [IsCO O B]
    (W : WPres O X B) (hz : ∀ s, W.z s ∈ maximalIdeal B) {R' : Type} [CommRing R'] [Algebra O R']
    [IsCO O R'] (f g : B →ₐ[O] R') (h : ∀ s, f (W.z s) = g (W.z s)) : f = g := by
  have hC : ∀ (H : MvPowerSeries W.σ O →ₐ[O] R') (x : O), H (C x) = Algebra.ofId O R' x := fun H x => by
    have := H.commutes x
    rw [MvPowerSeries.algebraMap_apply] at this
    exact this
  have hm : ∀ s, f (W.z s) ∈ maximalIdeal R' := fun s => by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hz s
  have key : f.comp W.π = g.comp W.π :=
    (co_ev O O R' W.σ (Algebra.ofId O R') (fun s => f (W.z s)) hm).unique ⟨hC _, fun _ => rfl⟩
      ⟨hC _, fun s => (h s).symm⟩
  ext x
  obtain ⟨y, rfl⟩ := W.surj x
  exact DFunLike.congr_fun key y

private theorem const_mem {O X R ι : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    (W : WPres O X R) (w : ι → X) {a b : ι} {c : O} (hc : w a ≠ w b → c = 0) {x : R}
    (hx : x - algebraMap O R c ∈ W.part (w a - w b)) : x ∈ W.part (w a - w b) := by
  have h2 : algebraMap O R c ∈ W.part (w a - w b) := by
    by_cases hab : w a = w b
    · rw [hab, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
    · rw [hc hab, map_zero]
      exact zero_mem _
  simpa using add_mem hx h2

private theorem const_eig {O X R R' ι : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] (f f' : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ)
    (w : ι → X) {a b : ι} {c : O} (hc : w a ≠ w b → c = 0) {x : R}
    (hx : f' x = t (Multiplicative.ofAdd (w a - w b)) * f x) :
    f' (x - algebraMap O R c) = t (Multiplicative.ofAdd (w a - w b)) * f (x - algebraMap O R c) := by
  rw [map_sub f', map_sub f, AlgHom.commutes, AlgHom.commutes, hx, mul_sub]
  by_cases hab : w a = w b
  · simp [hab]
  · simp [hc hab]

theorem UpperTheory.V.Alg.framed_grading :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (WB : WPres O X B), (∀ s, WB.z s ∈ maximalIdeal B) → (∀ v s a b, (ρ v).hom s a b ∈ WB.part (w a - w b)) →
      ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (i : B →ₐ[O] R) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α →
      ∃ W : WPres O X R, (∀ s, W.z s ∈ maximalIdeal R) ∧ (∀ s, i (WB.z s) ∈ W.part (WB.wt s)) ∧ (∀ s a b, r.hom s a b ∈ W.part (w a - w b)) ∧ ∀ v a b, α v a b ∈ W.part (w a - w b) := by
  intro O _ _ _ _ ι X _ _ _ _ _ w Φ _ Γ _ _ _ rbar r0 _ hn0 F L _ hL _ B _ _ _ ρ _ WB hzB hρ R _ _ _ i r α ⟨hfr, hu⟩
  have h0 := hn0.2.2
  have h1 : ∀ a b, w a ≠ w b → (1 : Matrix ι ι O) a b = 0 := fun a b hab =>
    Matrix.one_apply_ne fun e => hab (by rw [e])
  let e : WB.σ ⊕ (Γ × ι × ι) ⊕ (F.T × ι × ι) → R := Sum.elim (fun s => i (WB.z s))
    (Sum.elim (fun s => r.hom s.1 s.2.1 s.2.2 - algebraMap O R (r0.hom s.1 s.2.1 s.2.2))
      fun s => α s.1 s.2.1 s.2.2 - algebraMap O R ((1 : Matrix ι ι O) s.2.1 s.2.2))
  have hem : ∀ s, e s ∈ maximalIdeal R := by
    rintro (s | ⟨g, a, b⟩ | ⟨v, a, b⟩)
    · show i (WB.z s) ∈ _
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hzB s
    · show r.hom g a b - algebraMap O R (r0.hom g a b) ∈ _
      rw [← res_eq_zero_iff O, map_sub, r.red, AlgHom.commutes, ← r0.red g a b, sub_eq_zero]
      exact (res O O).commutes _
    · show α v a b - algebraMap O R ((1 : Matrix ι ι O) a b) ∈ _
      have k : res O R (α v a b) = (1 : Matrix ι ι (ResidueField O)) a b :=
        congrFun (congrFun (hfr.2.2.1 v).2.2 a) b
      rw [← res_eq_zero_iff O, map_sub, k, AlgHom.commutes, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
  obtain ⟨W, u, hW, he⟩ := coord_grading O X R _ e
    (Sum.elim WB.wt (Sum.elim (fun s => w s.2.1 - w s.2.2) fun s => w s.2.1 - w s.2.2)) hem
    (fun R' _ _ _ f f' h => by
      refine (hu R' _ _ _ (framed_map hL hfr f)).unique ⟨rfl, rfl, fun _ => rfl⟩ ⟨?_, ?_, fun v => ?_⟩
      · exact algHom_ext_on_generators WB hzB _ _ fun s => (h (.inl s)).symm
      · ext g a b
        have : f (r.hom g a b - algebraMap O R _) = f' (r.hom g a b - algebraMap O R _) :=
          h (.inr (.inl (g, a, b)))
        simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
        exact this.symm
      · ext a b
        have : f (α v a b - algebraMap O R _) = f' (α v a b - algebraMap O R _) :=
          h (.inr (.inr (v, a, b)))
        simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
        exact this.symm)
    (fun R' _ _ _ f t ht => by
      obtain ⟨i', hi', -⟩ := tact O X B WB hzB R' (f.comp i) t
      obtain ⟨f', ⟨k1, k2, k3⟩, -⟩ := hu R' _ _ _
        (framed_torus hL h0 (framed_map hL hfr f) t ht fun v s a b => hi' _ _ (hρ v s a b))
      refine ⟨f', ?_⟩
      rintro (s | ⟨g, a, b⟩ | ⟨v, a, b⟩)
      · exact (DFunLike.congr_fun k1 _).trans (hi' _ _ (WB.z_mem s))
      · exact const_eig f f' t w (h0 g a b) (congrArg (fun x => x.hom g a b) k2)
      · exact const_eig f f' t w (h1 a b) (congrFun (congrFun (k3 v) a) b))
  exact ⟨W, fun s => by rw [(hW s).1]; exact hem _, fun s => he (.inl s),
    fun g a b => const_mem W w (h0 g a b) (he (.inr (.inl (g, a, b)))),
    fun v a b => const_mem W w (h1 a b) (he (.inr (.inr (v, a, b))))⟩
