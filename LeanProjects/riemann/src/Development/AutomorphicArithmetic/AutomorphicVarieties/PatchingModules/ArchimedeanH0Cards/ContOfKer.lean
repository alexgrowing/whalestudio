import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdExExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.EvIff

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem cont_of_ker {A Γ M : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module A M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation A Γ M)
    (hk : ∀ᶠ g in nhds (1 : Γ), ∀ m, ρ g m = m) : ContAction ρ := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [ContinuousAt, nhds_discrete M, Filter.tendsto_pure]
  have hg : ∀ᶠ g in nhds p.1, ∀ m, ρ g m = ρ p.1 m := by
    have ht : Filter.Tendsto (fun g => p.1⁻¹ * g) (nhds p.1) (nhds 1) := by
      simpa using (continuous_mul_left p.1⁻¹).tendsto p.1
    filter_upwards [ht.eventually hk] with g hg m
    calc ρ g m = ρ p.1 (ρ (p.1⁻¹ * g) m) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ p.1 m := by rw [hg m]
  have hm : ∀ᶠ q : Γ × M in nhds p, q.2 = p.2 := by
    have h0 : ∀ᶠ m in nhds p.2, m = p.2 := by
      rw [nhds_discrete, Filter.eventually_pure]
    exact (continuous_snd.tendsto p).eventually h0
  filter_upwards [(continuous_fst.tendsto p).eventually hg, hm] with q h1 h2
  rw [h1, h2]

private theorem ev_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (m : ℕ) (hm : algebraMap x.A X (x.t ^ m) = 0) :
    ∀ᶠ g in nhds (1 : F.G₀), x.ρX X g = 1 := by
  have key : ∀ a b : x.A, Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries x.K) ^ m) a =
      Ideal.Quotient.mk _ b → algebraMap x.A X a = algebraMap x.A X b := by
    intro a b hab
    rw [Ideal.Quotient.eq, PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hab
    obtain ⟨c, hc⟩ := hab
    rw [← sub_eq_zero, ← map_sub, hc, map_mul, hm, zero_mul]
  have hij : ∀ i j : Fin n, ∀ᶠ g in nhds (1 : F.G₀), x.ρX X g i j = (1 : Matrix (Fin n) (Fin n) X) i j := by
    intro i j
    have hl := x.cont i j m
    filter_upwards [(hl.isOpen_fiber _).mem_nhds (Set.mem_singleton _)] with g hg
    have hg' := key _ _ hg
    simp only [NP.ρX, Matrix.map_apply]
    rw [hg']
    simp [mat, Matrix.one_apply]
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 (hij i)] with g hg
  exact Matrix.ext hg

private theorem tri_X {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) (g : F.Gv v) :
    (x.wiX X v * x.ρX X (F.φ v g) * x.wX X v).BlockTriangular id := by
  intro i j hij
  have h := (x.tri v g).1 i j hij
  simp only [NP.wiX, NP.ρX, NP.wX, mat, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply]
  rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, ← Units.val_mul, ← Units.val_mul, h, map_zero]

private theorem w_wi {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) : x.wX X v * x.wiX X v = 1 := by
  simp only [NP.wX, NP.wiX]
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

private def triSub {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n : ℕ}
    (V : Submodule A (Matrix (Fin n) (Fin n) X)) (a b : Matrix (Fin n) (Fin n) X) : Submodule A V where
  carrier := {Z | (a * (Z : Matrix (Fin n) (Fin n) X) * b).BlockTriangular id}
  zero_mem' := by
    intro i j _
    simp
  add_mem' := by
    intro Z Z' h h' i j hij
    have e1 := h hij
    have e2 := h' hij
    simp only [Submodule.coe_add, mul_add, add_mul, Matrix.add_apply, e1, e2, add_zero]
  smul_mem' := by
    intro c Z h i j hij
    have e1 := h hij
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, e1, smul_zero]

theorem UpperTheory.V.Pa.B2.odEx :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] [Finite X], (∃ m : ℕ, algebraMap x.A X (x.t ^ m) = 0) → ∃ D : Dat x.A (plOf G), Nonempty (IsOd h x X D) := by
  intro l _ L G G0 h n x X _ _ _ hX
  obtain ⟨m, hm⟩ := hX
  obtain ⟨-, hok⟩ := okX l L G G0 h n x X 1
  obtain ⟨rep, hrep⟩ := adEx l G.frame x.A X n (fun g => x.ρX X (h.p₀ g))
    (fun g => algebraMap x.A X ((1 : G.Γ →* x.A) g)) (Od x.A X n x.a) hok
  have hact : ∀ (g : G.G₀) (Z : Od x.A X n x.a),
      ((rep g Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) =
        x.ρX X (h.p₀ g) * Z * x.ρX X (h.p₀ g⁻¹) := by
    intro g Z
    rw [hrep.1 g Z]
    simp
  have hc : ∀ Z : Od x.A X n x.a, ((rep G.c Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) = -(Z : Matrix (Fin n) (Fin n) X)ᵀ := by
    intro Z
    rw [hrep.2 Z]
    simp
  letI : TopologicalSpace (Od x.A X n x.a) := ⊥
  haveI : DiscreteTopology (Od x.A X n x.a) := ⟨rfl⟩
  haveI : Finite (Od x.A X n x.a) := inferInstance
  have hp : Continuous h.p₀ := continuous_induced_rng.2 (h.cont.comp continuous_subtype_val)
  have hcont : ContAction rep := by
    apply cont_of_ker
    have E := ev_one x X m hm
    have E1 : ∀ᶠ g in nhds (1 : G.G₀), x.ρX X (h.p₀ g) = 1 := by
      have := (hp.tendsto 1).eventually (by simpa using E)
      exact this
    have E2 : ∀ᶠ g in nhds (1 : G.G₀), x.ρX X (h.p₀ g⁻¹) = 1 := by
      have ht : Filter.Tendsto (fun g : G.G₀ => g⁻¹) (nhds 1) (nhds 1) := by
        simpa using (continuous_inv.tendsto (1 : G.G₀))
      exact ht.eventually E1
    have E3 := E1.and E2
    rw [show (1 : G.G₀) = ⟨1, G.η.ker.one_mem⟩ from rfl, nhds_subtype_eq_comap, Filter.eventually_comap] at E3
    filter_upwards [E3, G.η_open.mem_nhds G.η.ker.one_mem] with g hg hker Z
    obtain ⟨h1, h2⟩ := hg ⟨g, hker⟩ rfl
    apply Subtype.ext
    have := hact ⟨g, hker⟩ Z
    rw [h1, h2, Matrix.one_mul, Matrix.mul_one] at this
    exact this
  let M : FRep x.A G.Γ := ⟨Od x.A X n x.a, rep, hcont⟩
  let N : (plOf G).ι → Submodule x.A M.X :=
    Sum.elim (fun v => triSub (Od x.A X n x.a) (x.wiX X v) (x.wX X v)) (fun _ => ⊥)
  have hN : ∀ (w : (plOf G).ι) (g : (plOf G).G w), N w ≤ Submodule.comap (M.ρ ((plOf G).φ w g)) (N w) := by
    intro w g
    cases w with
    | inl v =>
      change L.Gv v at g
      intro Z hZ
      have hZ' : (x.wiX X v * (Z : Matrix (Fin n) (Fin n) X) * x.wX X v).BlockTriangular id := hZ
      show (x.wiX X v * ((rep ((G.φ v g : G.G₀) : G.Γ) Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) * x.wX X v).BlockTriangular id
      have e1 : h.p₀ (G.φ v g) = G0.frame.φ v g := Subtype.ext (h.φ v g)
      have e2 : h.p₀ (G.φ v g)⁻¹ = G0.frame.φ v g⁻¹ := by
        rw [map_inv h.p₀, e1]
        exact (map_inv (G0.frame.φ v) g).symm
      rw [hact, e1, e2]
      have hww := w_wi x X v
      have heq : x.wiX X v * (x.ρX X (G0.frame.φ v g) * (Z : Matrix (Fin n) (Fin n) X) * x.ρX X (G0.frame.φ v g⁻¹)) * x.wX X v =
          (x.wiX X v * x.ρX X (G0.frame.φ v g) * x.wX X v) * (x.wiX X v * (Z : Matrix (Fin n) (Fin n) X) * x.wX X v) *
            (x.wiX X v * x.ρX X (G0.frame.φ v g⁻¹) * x.wX X v) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (x.wX X v) (x.wiX X v), hww, Matrix.one_mul,
          ← Matrix.mul_assoc (x.wX X v) (x.wiX X v), hww, Matrix.one_mul]
      rw [heq]
      exact ((tri_X x X v g).mul hZ').mul (tri_X x X v g⁻¹)
    | inr u =>
      intro Z hZ
      have hZ0 : Z = 0 := (Submodule.mem_bot _).1 hZ
      simp [N, hZ0]
  refine ⟨Dat.ofSub (plOf G) M N hN, ⟨⟨LinearEquiv.refl _ _, fun g m => hact g m, fun m => hc m, ?_, ?_⟩⟩⟩
  · intro v m
    exact (Submodule.Quotient.mk_eq_zero (N (Sum.inl v)) (x := (m : M.X))).trans
      ⟨fun hb i j hij => hb hij, fun hb i j hij => hb i j hij⟩
  · intro u a b hab
    have hab' := (Submodule.Quotient.eq (N (Sum.inr u)) (x := (a : M.X)) (y := b)).1 hab
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 hab')
